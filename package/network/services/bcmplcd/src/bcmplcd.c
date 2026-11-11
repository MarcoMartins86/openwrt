// SPDX-License-Identifier: GPL-2.0-or-later
/*
 * Host daemon for Broadcom BCM60xxx HomePlug AV2 chips without flash
 *
 * Such a chip keeps nothing of its own: after a reset its boot ROM asks the
 * host for the firmware over Ethernet, and the running firmware reads and
 * writes its parameter block (keys, names, tone maps) through the host.
 * Until the firmware runs, the chip does not forward frames either, so on
 * boards that have the Ethernet port behind the chip this daemon also brings
 * up the wired network.
 */

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <net/ethernet.h>
#include <net/if.h>
#include <netpacket/packet.h>
#include <poll.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <syslog.h>
#include <time.h>
#include <unistd.h>

#include <linux/filter.h>

#define ETH_P_BCMPLC		0x8912

#define FRAME_MAX		1514
#define FRAME_MIN		60

/* partition wrapper used by TP-Link: be32 length, be32 zero */
#define TPLINK_PTN_HDR_LEN	8

/* header in front of the firmware, loader and parameter blobs */
#define BLOB_HDR_LEN		32
#define BLOB_VERSION		1

#define IMAGE_MAX		0x140000
#define IMAGE_PARAM_LEN		4096
#define IMAGE_LOAD_ADDR		0x80000

/*
 * firmware download, Ethernet II frames:
 * version, type (le16), zero, sequence number, operation, payload
 */
#define BOOT_HDR_LEN		20
#define BOOT_VERSION		2
#define BOOT_TYPE		0xaff0
#define BOOT_CHUNK		1494
#define BOOT_ACK_TIMEOUT	30	/* ms */
#define BOOT_RETRIES		5
#define BOOT_DEMAND_HOLDOFF	600	/* ms */

enum {
	BOOT_OP_DEMAND = 1,
	BOOT_OP_START = 2,
	BOOT_OP_DATA = 3,
	BOOT_OP_ACK = 4,
	BOOT_OP_DATA_LAST = 6,
};

enum {
	BOOT_IDLE,
	BOOT_START,
	BOOT_DATA,
};

/*
 * parameter storage, 802.3 frames with LLC/SNAP:
 * zero length, aa aa 03, OUI, protocol, version, operation, payload
 */
#define NVM_HDR_LEN		24
#define NVM_VERSION		1
#define NVM_REQ_LEN		10	/* handle, offset, length */
#define NVM_DATA_MAX		1480

enum {
	NVM_OPEN_REQ = 0x00,
	NVM_OPEN_CNF = 0x01,
	NVM_CLOSE_REQ = 0x04,
	NVM_CLOSE_CNF = 0x05,
	NVM_READ_REQ = 0x08,
	NVM_READ_CNF = 0x09,
	NVM_READ_FAIL = 0x0a,
	NVM_WRITE_REQ = 0x0c,
	NVM_WRITE_CNF = 0x0d,
	NVM_WRITE_FAIL = 0x0e,
	NVM_RESET_REQ = 0x10,
	NVM_RESET_CNF = 0x11,
	NVM_ALIVE_REQ = 0x14,
	NVM_ALIVE_CNF = 0x15,
};

enum {
	NVM_INIT,
	NVM_OPENED,
	NVM_CLOSED,
};

struct blob {
	uint8_t *data;
	size_t len;
};

static const uint8_t boot_rom_addr[ETH_ALEN] = { 0x00, 0x1f, 0x84, 0x00, 0x00, 0x00 };
static const uint8_t bcast_addr[ETH_ALEN] = { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff };
static const uint8_t nvm_llc[] = { 0x00, 0x00, 0xaa, 0xaa, 0x03, 0x00, 0x1f, 0x84, 0x89, 0x12 };

static const char *ifname = "eth0";
static const char *fw_src = "plc-fw";
static const char *loader_src = "plc-bin";
static const char *param_src = "plc-param";
static const char *param_default_src;
static const char *param_file;
static int verbose;

static int sock = -1;
static int ifindex;
static uint8_t if_mac[ETH_ALEN];
static uint8_t soc_mac[ETH_ALEN];
static bool soc_mac_set;

static struct blob param;

static struct {
	int state;
	uint8_t seq;
	size_t offset;
	size_t chunk;
	int retries;
	struct blob image;
	int64_t deadline;
	int64_t last_demand;
} boot = { .last_demand = -BOOT_DEMAND_HOLDOFF };

static struct {
	int state;
	uint16_t handle;
} nvm;

static void msg(int prio, const char *fmt, ...)
{
	va_list ap;

	if (prio == LOG_DEBUG && !verbose)
		return;

	va_start(ap, fmt);
	vsyslog(prio, fmt, ap);
	va_end(ap);
}

#define err(...)	msg(LOG_ERR, __VA_ARGS__)
#define info(...)	msg(LOG_INFO, __VA_ARGS__)
#define dbg(...)	msg(LOG_DEBUG, __VA_ARGS__)

static int64_t now_ms(void)
{
	struct timespec ts;

	clock_gettime(CLOCK_MONOTONIC, &ts);

	return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static uint32_t get_be32(const uint8_t *p)
{
	return (uint32_t)p[0] << 24 | p[1] << 16 | p[2] << 8 | p[3];
}

static uint32_t get_le32(const uint8_t *p)
{
	return (uint32_t)p[3] << 24 | p[2] << 16 | p[1] << 8 | p[0];
}

static void put_be32(uint8_t *p, uint32_t val)
{
	p[0] = val >> 24;
	p[1] = val >> 16;
	p[2] = val >> 8;
	p[3] = val;
}

static void put_le32(uint8_t *p, uint32_t val)
{
	p[0] = val;
	p[1] = val >> 8;
	p[2] = val >> 16;
	p[3] = val >> 24;
}

/* the boot ROM wants a CRC-32 that starts from zero */
static uint32_t image_crc(const uint8_t *data, size_t len)
{
	uint32_t crc = 0;
	int i;

	while (len--) {
		crc ^= *data++;
		for (i = 0; i < 8; i++)
			crc = (crc >> 1) ^ (crc & 1 ? 0xedb88320 : 0);
	}

	return ~crc;
}

static void blob_free(struct blob *b)
{
	free(b->data);
	b->data = NULL;
	b->len = 0;
}

static int mtd_find(const char *name, char *dev, size_t len)
{
	char line[128], label[65];
	unsigned int idx;
	int ret = -1;
	FILE *f;

	f = fopen("/proc/mtd", "r");
	if (!f)
		return -1;

	while (fgets(line, sizeof(line), f)) {
		if (sscanf(line, "mtd%u: %*x %*x \"%64[^\"]\"", &idx, label) != 2)
			continue;

		if (strcmp(label, name))
			continue;

		snprintf(dev, len, "/dev/mtd%uro", idx);
		ret = 0;
		break;
	}

	fclose(f);

	return ret;
}

static int file_read(const char *path, struct blob *b)
{
	struct stat st;
	ssize_t n;
	size_t len = 0;
	size_t size = 65536;
	uint8_t *data = NULL;
	int fd;

	fd = open(path, O_RDONLY);
	if (fd < 0)
		return -1;

	if (!fstat(fd, &st) && S_ISREG(st.st_mode) && st.st_size > 0)
		size = st.st_size;

	while (1) {
		uint8_t *tmp = realloc(data, size);

		if (!tmp)
			goto error;

		data = tmp;

		while (len < size) {
			n = read(fd, data + len, size - len);
			if (n < 0 && errno == EINTR)
				continue;
			if (n < 0)
				goto error;
			if (!n)
				goto done;

			len += n;
		}

		if (size >= 2 * IMAGE_MAX)
			goto error;

		size *= 2;
	}

done:
	close(fd);
	b->data = data;
	b->len = len;

	return 0;

error:
	close(fd);
	free(data);

	return -1;
}

/* a path names a file with the bare blob, anything else a flash partition */
static int blob_read(const char *src, struct blob *b)
{
	char dev[32];
	uint32_t len;

	if (strchr(src, '/')) {
		if (file_read(src, b)) {
			err("cannot read %s: %s", src, strerror(errno));
			return -1;
		}
	} else {
		if (mtd_find(src, dev, sizeof(dev))) {
			err("flash partition %s not found", src);
			return -1;
		}

		if (file_read(dev, b)) {
			err("cannot read %s: %s", dev, strerror(errno));
			return -1;
		}

		len = b->len >= TPLINK_PTN_HDR_LEN ? get_be32(b->data) : 0;
		if (!len || len > b->len - TPLINK_PTN_HDR_LEN) {
			err("flash partition %s is empty", src);
			goto error;
		}

		memmove(b->data, b->data + TPLINK_PTN_HDR_LEN, len);
		b->len = len;
	}

	if (b->len < BLOB_HDR_LEN || get_le32(b->data) != BLOB_VERSION ||
	    get_le32(b->data + 4) != b->len - BLOB_HDR_LEN) {
		err("%s is not what this chip takes", src);
		goto error;
	}

	return 0;

error:
	blob_free(b);

	return -1;
}

static int param_save(void)
{
	char tmp[256];
	ssize_t n;
	int fd;

	if (!param_file)
		return 0;

	snprintf(tmp, sizeof(tmp), "%s.tmp", param_file);

	fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0600);
	if (fd < 0)
		goto error;

	n = write(fd, param.data, param.len);
	if (n != (ssize_t)param.len || fsync(fd)) {
		close(fd);
		goto error;
	}

	close(fd);

	if (rename(tmp, param_file))
		goto error;

	return 0;

error:
	err("cannot write %s: %s", param_file, strerror(errno));
	unlink(tmp);

	return -1;
}

static int param_load(void)
{
	struct blob flash = {};

	if (blob_read(param_src, &flash))
		return -1;

	if (flash.len > IMAGE_PARAM_LEN) {
		err("%s is too large", param_src);
		blob_free(&flash);
		return -1;
	}

	/* the kept copy has to describe the same parameters as the flash */
	if (param_file && !access(param_file, R_OK) &&
	    !blob_read(param_file, &param)) {
		if (param.len == flash.len) {
			blob_free(&flash);
			return 0;
		}

		err("%s does not match %s, starting over", param_file, param_src);
		blob_free(&param);
	}

	param = flash;

	return 0;
}

static int param_reset(void)
{
	struct blob def = {};

	if (!param_default_src)
		return -1;

	if (blob_read(param_default_src, &def))
		return -1;

	if (def.len != param.len) {
		blob_free(&def);
		return -1;
	}

	blob_free(&param);
	param = def;

	return param_save();
}

/*
 * What the boot ROM loads: the firmware without its header, a page with the
 * parameters, the addresses of both ends of the link and the second stage
 * loader, closed with a checksum.
 */
static int image_build(struct blob *image)
{
	struct blob fw = {}, loader = {};
	size_t fw_len, len;
	uint8_t *p;
	int ret = -1;

	if (blob_read(fw_src, &fw) || blob_read(loader_src, &loader))
		goto out;

	if (fw.len < 2 * BLOB_HDR_LEN)
		goto out;

	fw_len = fw.len - 2 * BLOB_HDR_LEN;
	len = fw_len + IMAGE_PARAM_LEN + 16 + loader.len;
	len = (len + 3) & ~3;
	len += 4;

	if (len >= IMAGE_MAX) {
		err("firmware is too large");
		goto out;
	}

	p = calloc(1, len);
	if (!p)
		goto out;

	image->data = p;
	image->len = len;

	memcpy(p, fw.data + BLOB_HDR_LEN, fw_len);
	p += fw_len;

	memcpy(p, param.data, param.len);
	p += IMAGE_PARAM_LEN;

	put_be32(p, 16);
	memcpy(p + 4, if_mac, ETH_ALEN);
	memcpy(p + 10, soc_mac, ETH_ALEN);
	p += 16;

	memcpy(p, loader.data, loader.len);

	put_le32(image->data + len - 4, image_crc(image->data, len - 4));
	ret = 0;

out:
	blob_free(&fw);
	blob_free(&loader);

	return ret;
}

static int frame_send(uint8_t *frame, size_t len)
{
	struct sockaddr_ll sll = {
		.sll_family = AF_PACKET,
		.sll_ifindex = ifindex,
		.sll_halen = ETH_ALEN,
	};

	if (len < FRAME_MIN)
		len = FRAME_MIN;

	memcpy(sll.sll_addr, frame, ETH_ALEN);

	if (sendto(sock, frame, len, 0, (struct sockaddr *)&sll, sizeof(sll)) < 0) {
		err("send failed: %s", strerror(errno));
		return -1;
	}

	return 0;
}

static void boot_send(void)
{
	uint8_t frame[FRAME_MAX] = {};
	uint8_t *p = frame + BOOT_HDR_LEN;
	size_t len = 0;

	memcpy(frame + ETH_ALEN, if_mac, ETH_ALEN);
	frame[12] = ETH_P_BCMPLC >> 8;
	frame[13] = ETH_P_BCMPLC & 0xff;
	frame[14] = BOOT_VERSION;
	frame[15] = BOOT_TYPE & 0xff;
	frame[16] = BOOT_TYPE >> 8;
	frame[18] = boot.seq;

	switch (boot.state) {
	case BOOT_START:
		/* the ROM listens on a fixed address and takes over the given one */
		memcpy(frame, boot_rom_addr, ETH_ALEN);
		frame[19] = BOOT_OP_START;
		memcpy(p, soc_mac, ETH_ALEN);
		put_be32(p + 8, 0);
		put_be32(p + 12, IMAGE_LOAD_ADDR);
		put_be32(p + 16, boot.image.len);
		len = 20;
		break;
	case BOOT_DATA:
		memcpy(frame, soc_mac, ETH_ALEN);
		len = boot.chunk;
		frame[19] = len < BOOT_CHUNK ? BOOT_OP_DATA_LAST : BOOT_OP_DATA;
		memcpy(p, boot.image.data + boot.offset, len);
		break;
	default:
		return;
	}

	frame_send(frame, BOOT_HDR_LEN + len);
	boot.deadline = now_ms() + BOOT_ACK_TIMEOUT;
}

static void boot_stop(void)
{
	blob_free(&boot.image);
	boot.state = BOOT_IDLE;
}

static void boot_set_chunk(void)
{
	boot.chunk = boot.image.len - boot.offset;
	if (boot.chunk > BOOT_CHUNK)
		boot.chunk = BOOT_CHUNK;
}

static void boot_demand(void)
{
	/* the ROM repeats the request while the first one is being served */
	if (now_ms() - boot.last_demand < BOOT_DEMAND_HOLDOFF)
		return;

	if (!boot.image.data && image_build(&boot.image))
		return;

	info("chip asks for firmware, sending %zu bytes", boot.image.len);

	/* reading the flash takes longer than the ROM waits to ask again */
	boot.last_demand = now_ms();

	/* the parameter storage starts closed after every boot */
	nvm.state = NVM_INIT;

	boot.state = BOOT_START;
	boot.seq = 1;
	boot.retries = 0;
	boot_send();
}

static void boot_ack(uint8_t seq)
{
	switch (boot.state) {
	case BOOT_START:
		boot.state = BOOT_DATA;
		boot.offset = 0;
		break;
	case BOOT_DATA:
		if (seq != boot.seq)
			return;

		boot.offset += boot.chunk;
		break;
	default:
		return;
	}

	boot.retries = 0;

	if (boot.offset >= boot.image.len) {
		info("firmware sent");
		boot_stop();
		return;
	}

	boot.seq++;
	boot_set_chunk();
	boot_send();
}

static void boot_timeout(void)
{
	if (boot.state == BOOT_IDLE)
		return;

	if (boot.retries++ >= BOOT_RETRIES) {
		err("chip stopped answering at %zu of %zu bytes",
		    boot.offset, boot.image.len);
		boot_stop();
		return;
	}

	boot_send();
}

static void boot_recv(const uint8_t *frame, size_t len)
{
	if (len < BOOT_HDR_LEN || frame[14] != BOOT_VERSION ||
	    frame[15] != (BOOT_TYPE & 0xff) || frame[16] != BOOT_TYPE >> 8)
		return;

	switch (frame[19]) {
	case BOOT_OP_DEMAND:
		boot_demand();
		break;
	case BOOT_OP_ACK:
		boot_ack(frame[18]);
		break;
	}
}

static void nvm_send(uint8_t op, const uint8_t *data, size_t len)
{
	uint8_t frame[FRAME_MAX] = {};

	memcpy(frame, soc_mac, ETH_ALEN);
	memcpy(frame + ETH_ALEN, if_mac, ETH_ALEN);
	memcpy(frame + 12, nvm_llc, sizeof(nvm_llc));
	frame[22] = NVM_VERSION;
	frame[23] = op;

	if (len)
		memcpy(frame + NVM_HDR_LEN, data, len);

	frame_send(frame, NVM_HDR_LEN + len);
}

/* the chip counts from the end of the header that the parameters carry */
static uint8_t *nvm_range(const uint8_t *req, size_t req_len, uint32_t *len)
{
	uint32_t offset;

	if (req_len < NVM_REQ_LEN)
		return NULL;

	offset = get_be32(req + 2);
	*len = get_be32(req + 6);

	if (*len > NVM_DATA_MAX || offset > param.len ||
	    offset + BLOB_HDR_LEN + *len > param.len)
		return NULL;

	return param.data + BLOB_HDR_LEN + offset;
}

static void nvm_read(const uint8_t *req, size_t req_len)
{
	uint8_t resp[NVM_REQ_LEN + NVM_DATA_MAX];
	uint32_t len;
	uint8_t *p;

	p = nvm_range(req, req_len, &len);
	if (!p) {
		err("chip reads outside of its parameters");
		nvm_send(NVM_READ_FAIL, req, 2);
		return;
	}

	dbg("parameters: read %u at %u", len, get_be32(req + 2));

	memcpy(resp, req, NVM_REQ_LEN);
	memcpy(resp + NVM_REQ_LEN, p, len);
	nvm_send(NVM_READ_CNF, resp, NVM_REQ_LEN + len);
}

static void nvm_write(const uint8_t *req, size_t req_len)
{
	uint32_t len;
	uint8_t *p;

	p = nvm_range(req, req_len, &len);
	if (!p || req_len < NVM_REQ_LEN + len) {
		err("chip writes outside of its parameters");
		nvm_send(NVM_WRITE_FAIL, req, 2);
		return;
	}

	dbg("parameters: write %u at %u", len, get_be32(req + 2));

	if (memcmp(p, req + NVM_REQ_LEN, len)) {
		memcpy(p, req + NVM_REQ_LEN, len);

		if (param_save()) {
			nvm_send(NVM_WRITE_FAIL, req, 2);
			return;
		}
	}

	nvm_send(NVM_WRITE_CNF, req, 2);
}

static void nvm_recv(const uint8_t *frame, size_t len)
{
	const uint8_t *req = frame + NVM_HDR_LEN;
	size_t req_len;
	uint16_t handle;
	uint8_t op;

	if (len < NVM_HDR_LEN + 2 || memcmp(frame + 14, nvm_llc + 2, sizeof(nvm_llc) - 2))
		return;

	if (memcmp(frame, if_mac, ETH_ALEN) && memcmp(frame, bcast_addr, ETH_ALEN))
		return;

	if (memcmp(frame + ETH_ALEN, soc_mac, ETH_ALEN))
		return;

	op = frame[23];
	req_len = len - NVM_HDR_LEN;
	handle = req[0] << 8 | req[1];

	switch (op) {
	case NVM_RESET_REQ:
		info("chip asks for its default parameters");
		param_reset();
		nvm_send(NVM_RESET_CNF, NULL, 0);
		return;
	case NVM_ALIVE_REQ:
		nvm_send(NVM_ALIVE_CNF, NULL, 0);
		return;
	}

	switch (nvm.state) {
	case NVM_INIT:
		if (op != NVM_OPEN_REQ)
			return;
		break;
	case NVM_OPENED:
		switch (op) {
		case NVM_OPEN_REQ:
			if (handle != nvm.handle)
				nvm.state = NVM_CLOSED;
			return;
		case NVM_READ_REQ:
			nvm_read(req, req_len);
			break;
		case NVM_WRITE_REQ:
			nvm_write(req, req_len);
			break;
		case NVM_CLOSE_REQ:
			nvm_send(NVM_CLOSE_CNF, req, 2);
			nvm.state = NVM_CLOSED;
			break;
		default:
			dbg("parameters: operation %#x while open", op);
			return;
		}

		nvm.handle = handle;
		return;
	case NVM_CLOSED:
		switch (op) {
		case NVM_OPEN_REQ:
			break;
		case NVM_READ_REQ:
			nvm_send(NVM_READ_FAIL, req, 2);
			nvm.handle = handle;
			return;
		case NVM_CLOSE_REQ:
			nvm_send(NVM_CLOSE_CNF, req, 2);
			nvm.handle = handle;
			return;
		default:
			dbg("parameters: operation %#x while closed", op);
			return;
		}
		break;
	}

	dbg("parameters: opened");
	nvm_send(NVM_OPEN_CNF, req, 2);
	nvm.state = NVM_OPENED;
	nvm.handle = handle;
}

static int if_lookup(void)
{
	struct ifreq ifr = {};
	int fd, ret = -1;

	fd = socket(AF_INET, SOCK_DGRAM, 0);
	if (fd < 0)
		return -1;

	strncpy(ifr.ifr_name, ifname, sizeof(ifr.ifr_name) - 1);

	if (ioctl(fd, SIOCGIFINDEX, &ifr))
		goto out;

	ifindex = ifr.ifr_ifindex;

	if (ioctl(fd, SIOCGIFHWADDR, &ifr))
		goto out;

	memcpy(if_mac, ifr.ifr_hwaddr.sa_data, ETH_ALEN);
	ret = 0;

out:
	close(fd);

	return ret;
}

static int sock_open(void)
{
	/* the boot protocol by its type, the storage protocol by its SNAP header */
	struct sock_filter insns[] = {
		BPF_STMT(BPF_LD | BPF_H | BPF_ABS, 12),
		BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, ETH_P_BCMPLC, 3, 0),
		BPF_JUMP(BPF_JMP | BPF_JGE | BPF_K, 0x600, 3, 0),
		BPF_STMT(BPF_LD | BPF_H | BPF_ABS, 20),
		BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, ETH_P_BCMPLC, 0, 1),
		BPF_STMT(BPF_RET | BPF_K, 0xffff),
		BPF_STMT(BPF_RET | BPF_K, 0),
	};
	struct sock_fprog prog = {
		.len = sizeof(insns) / sizeof(insns[0]),
		.filter = insns,
	};
	struct sockaddr_ll sll = {
		.sll_family = AF_PACKET,
		.sll_protocol = htons(ETH_P_ALL),
		.sll_ifindex = ifindex,
	};

	sock = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ALL));
	if (sock < 0) {
		err("cannot open a socket: %s", strerror(errno));
		return -1;
	}

	if (setsockopt(sock, SOL_SOCKET, SO_ATTACH_FILTER, &prog, sizeof(prog))) {
		err("cannot set the socket filter: %s", strerror(errno));
		return -1;
	}

	if (bind(sock, (struct sockaddr *)&sll, sizeof(sll))) {
		err("cannot bind to %s: %s", ifname, strerror(errno));
		return -1;
	}

	return 0;
}

static void sock_recv(void)
{
	uint8_t frame[FRAME_MAX];
	struct sockaddr_ll sll;
	socklen_t sll_len = sizeof(sll);
	ssize_t len;

	len = recvfrom(sock, frame, sizeof(frame), MSG_DONTWAIT,
		       (struct sockaddr *)&sll, &sll_len);
	if (len < 0 && errno == ENODEV) {
		err("interface %s is gone", ifname);
		exit(1);
	}

	/* an interface that goes down is reported here once, wait for it */
	if (len < ETH_HLEN || sll.sll_pkttype == PACKET_OUTGOING)
		return;

	if ((frame[12] << 8 | frame[13]) == ETH_P_BCMPLC)
		boot_recv(frame, len);
	else
		nvm_recv(frame, len);
}

static int mac_parse(const char *str, uint8_t *mac)
{
	unsigned int b[ETH_ALEN];
	int i;

	if (sscanf(str, "%x:%x:%x:%x:%x:%x", &b[0], &b[1], &b[2], &b[3], &b[4], &b[5]) != ETH_ALEN)
		return -1;

	for (i = 0; i < ETH_ALEN; i++)
		mac[i] = b[i];

	return 0;
}

static void mac_add(uint8_t *mac, unsigned int val)
{
	int i;

	for (i = ETH_ALEN - 1; i >= 0 && val; i--) {
		val += mac[i];
		mac[i] = val;
		val >>= 8;
	}
}

static int usage(const char *prog)
{
	fprintf(stderr,
		"Usage: %s [options]\n"
		"\n"
		"Options:\n"
		"  -i <ifname>   interface that leads to the chip (default: eth0)\n"
		"  -m <mac>      address the chip takes (default: interface address + 2)\n"
		"  -f <source>   firmware (default: plc-fw)\n"
		"  -l <source>   second stage loader (default: plc-bin)\n"
		"  -p <source>   parameters (default: plc-param)\n"
		"  -d <source>   default parameters, for a reset asked by the chip\n"
		"  -s <file>     file that keeps the parameters the chip changes\n"
		"  -w <file>     write the boot image to a file and exit\n"
		"  -v            log every request\n"
		"\n"
		"A source is the name of a flash partition, or the path of a file.\n",
		prog);

	return 1;
}

int main(int argc, char **argv)
{
	const char *image_file = NULL;
	struct pollfd pfd;
	int ch;

	while ((ch = getopt(argc, argv, "i:m:f:l:p:d:s:w:v")) != -1) {
		switch (ch) {
		case 'i':
			ifname = optarg;
			break;
		case 'm':
			if (mac_parse(optarg, soc_mac))
				return usage(argv[0]);
			soc_mac_set = true;
			break;
		case 'f':
			fw_src = optarg;
			break;
		case 'l':
			loader_src = optarg;
			break;
		case 'p':
			param_src = optarg;
			break;
		case 'd':
			param_default_src = optarg;
			break;
		case 's':
			param_file = optarg;
			break;
		case 'w':
			image_file = optarg;
			break;
		case 'v':
			verbose++;
			break;
		default:
			return usage(argv[0]);
		}
	}

	openlog("bcmplcd", LOG_PERROR, LOG_DAEMON);

	if (if_lookup()) {
		err("interface %s not found", ifname);
		return 1;
	}

	if (!soc_mac_set) {
		memcpy(soc_mac, if_mac, ETH_ALEN);
		mac_add(soc_mac, 2);
	}

	if (param_load())
		return 1;

	if (image_file) {
		struct blob image = {};
		FILE *f;

		if (image_build(&image))
			return 1;

		f = fopen(image_file, "w");
		if (!f || fwrite(image.data, image.len, 1, f) != 1 || fclose(f)) {
			err("cannot write %s: %s", image_file, strerror(errno));
			return 1;
		}

		return 0;
	}

	if (sock_open())
		return 1;

	info("serving the chip at %02x:%02x:%02x:%02x:%02x:%02x on %s",
	     soc_mac[0], soc_mac[1], soc_mac[2], soc_mac[3], soc_mac[4], soc_mac[5], ifname);

	pfd.fd = sock;
	pfd.events = POLLIN;

	while (1) {
		int timeout = -1;

		if (boot.state != BOOT_IDLE) {
			int64_t left = boot.deadline - now_ms();

			timeout = left > 0 ? left : 0;
		}

		ch = poll(&pfd, 1, timeout);
		if (ch < 0 && errno != EINTR) {
			err("poll failed: %s", strerror(errno));
			return 1;
		}

		if (ch > 0)
			sock_recv();

		if (boot.state != BOOT_IDLE && now_ms() >= boot.deadline)
			boot_timeout();
	}

	return 0;
}
