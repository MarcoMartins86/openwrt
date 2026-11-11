// SPDX-License-Identifier: GPL-2.0-or-later
/*
 * Control tool for Broadcom BCM60xxx HomePlug AV2 chips
 *
 * Talks to the running firmware of the chip with its management frames:
 * push-button pairing, the stations of the powerline network, a restart.
 */

#include <arpa/inet.h>
#include <errno.h>
#include <net/ethernet.h>
#include <net/if.h>
#include <netpacket/packet.h>
#include <poll.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#include <linux/filter.h>

#define ETH_P_BCMPLC		0x8912

#define FRAME_MAX		1514
#define FRAME_MIN		60

/* version, type (le16), two zero bytes, OUI, request number, payload */
#define MME_HDR_LEN		23
#define MME_TIMEOUT		500	/* ms */
#define MME_RETRIES		3

enum {
	MME_KEY_SET = 0xa018,
	MME_RESTART = 0xa020,
	MME_STATIONS = 0xa02c,
	MME_PARAM_GET = 0xa05c,
	MME_IDENTIFY = 0xa070,
	MME_PAIR = 0xa08c,
};

enum {
	PAIR_START = 0,
	PAIR_STATUS = 2,
	PAIR_STOP = 3,
};

enum {
	PAIR_DONE,
	PAIR_FAILED,
	PAIR_TIMEOUT,
	PAIR_ONGOING,
	PAIR_UNCHANGED,
	PAIR_IDLE,
};

/* index of the network identifier and key in the parameters of the chip */
#define PARAM_NID		35
#define PARAM_NMK		36
#define NID_LEN			7
#define NMK_LEN			16

#define PAIR_WAIT		130	/* s */

static const uint8_t oui[] = { 0x00, 0x1f, 0x84 };
static const uint8_t identify_key[] = {
	0xa3, 0x97, 0xa2, 0x55, 0x53, 0xbe, 0xf1, 0xfc,
	0xf9, 0x79, 0x6b, 0x52, 0x14, 0x13, 0xe9, 0xe2,
};

static const char *ifname = "eth0";
static int sock = -1;
static int ifindex;
static uint8_t if_mac[ETH_ALEN];
static uint8_t soc_mac[ETH_ALEN];
static uint8_t req_num;

static int64_t now_ms(void)
{
	struct timespec ts;

	clock_gettime(CLOCK_MONOTONIC, &ts);

	return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static int sock_open(void)
{
	struct sock_filter insns[] = {
		BPF_STMT(BPF_LD | BPF_H | BPF_ABS, 12),
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
	};
	struct ifreq ifr = {};

	sock = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ALL));
	if (sock < 0) {
		perror("socket");
		return -1;
	}

	strncpy(ifr.ifr_name, ifname, sizeof(ifr.ifr_name) - 1);

	if (ioctl(sock, SIOCGIFINDEX, &ifr)) {
		fprintf(stderr, "interface %s not found\n", ifname);
		return -1;
	}

	ifindex = ifr.ifr_ifindex;

	if (ioctl(sock, SIOCGIFHWADDR, &ifr)) {
		perror("SIOCGIFHWADDR");
		return -1;
	}

	memcpy(if_mac, ifr.ifr_hwaddr.sa_data, ETH_ALEN);

	if (setsockopt(sock, SOL_SOCKET, SO_ATTACH_FILTER, &prog, sizeof(prog))) {
		perror("SO_ATTACH_FILTER");
		return -1;
	}

	sll.sll_ifindex = ifindex;

	if (bind(sock, (struct sockaddr *)&sll, sizeof(sll))) {
		perror("bind");
		return -1;
	}

	return 0;
}

/*
 * Send a request and wait for its answer: the type is one above the one of
 * the request, and it carries the request number.
 */
static int mme(const uint8_t *dst, uint16_t type, const void *req, size_t req_len,
	       uint8_t *resp, size_t resp_len)
{
	struct sockaddr_ll sll = {
		.sll_family = AF_PACKET,
		.sll_ifindex = ifindex,
		.sll_halen = ETH_ALEN,
	};
	uint8_t frame[FRAME_MAX] = {};
	size_t len = MME_HDR_LEN + req_len;
	uint8_t num = ++req_num;
	int try;

	memcpy(frame, dst, ETH_ALEN);
	memcpy(frame + ETH_ALEN, if_mac, ETH_ALEN);
	frame[12] = ETH_P_BCMPLC >> 8;
	frame[13] = ETH_P_BCMPLC & 0xff;
	frame[14] = type == MME_IDENTIFY ? 1 : 2;
	frame[15] = type & 0xff;
	frame[16] = type >> 8;
	memcpy(frame + 19, oui, sizeof(oui));
	frame[22] = num;
	memcpy(frame + MME_HDR_LEN, req, req_len);

	if (len < FRAME_MIN)
		len = FRAME_MIN;

	memcpy(sll.sll_addr, dst, ETH_ALEN);

	for (try = 0; try < MME_RETRIES; try++) {
		int64_t end = now_ms() + MME_TIMEOUT;

		if (sendto(sock, frame, len, 0, (struct sockaddr *)&sll, sizeof(sll)) < 0) {
			perror("send");
			return -1;
		}

		while (1) {
			struct pollfd pfd = { .fd = sock, .events = POLLIN };
			uint8_t buf[FRAME_MAX];
			int64_t left = end - now_ms();
			ssize_t n;

			if (left <= 0 || poll(&pfd, 1, left) <= 0)
				break;

			n = recv(sock, buf, sizeof(buf), MSG_DONTWAIT);
			if (n < MME_HDR_LEN || memcmp(buf + ETH_ALEN, dst, ETH_ALEN) ||
			    (buf[15] | buf[16] << 8) != type + 1 ||
			    memcmp(buf + 19, oui, sizeof(oui)) || buf[22] != num)
				continue;

			n -= MME_HDR_LEN;
			if ((size_t)n > resp_len)
				n = resp_len;

			memcpy(resp, buf + MME_HDR_LEN, n);

			return n;
		}
	}

	fprintf(stderr, "the chip does not answer\n");

	return -1;
}

static int pair_cmd(uint8_t cmd)
{
	uint8_t resp[1];

	if (mme(soc_mac, MME_PAIR, &cmd, 1, resp, sizeof(resp)) < 1)
		return -1;

	if (resp[0] & 0x0f)
		return -1;

	return resp[0] >> 4;
}

static int cmd_pair(void)
{
	int64_t end = now_ms() + PAIR_WAIT * 1000;
	int state;

	if (pair_cmd(PAIR_START)) {
		fprintf(stderr, "pairing did not start\n");
		return 1;
	}

	printf("pairing started, press the pair button of the other adapter\n");
	fflush(stdout);

	do {
		sleep(1);
		state = pair_cmd(PAIR_STATUS);
	} while (state == PAIR_ONGOING && now_ms() < end);

	switch (state) {
	case PAIR_DONE:
		printf("paired\n");
		return 0;
	case PAIR_FAILED:
		printf("pairing failed\n");
		break;
	case PAIR_TIMEOUT:
	case PAIR_ONGOING:
		printf("no other adapter answered\n");
		break;
	case PAIR_UNCHANGED:
		printf("pairing ended, the network is unchanged\n");
		break;
	case PAIR_IDLE:
		printf("pairing cancelled\n");
		break;
	default:
		return 1;
	}

	return 2;
}

static int cmd_cancel(void)
{
	return pair_cmd(PAIR_STOP) ? 1 : 0;
}

static int cmd_status(void)
{
	static const char * const names[] = {
		[PAIR_DONE] = "paired",
		[PAIR_FAILED] = "failed",
		[PAIR_TIMEOUT] = "timeout",
		[PAIR_ONGOING] = "pairing",
		[PAIR_UNCHANGED] = "unchanged",
		[PAIR_IDLE] = "idle",
	};
	int state = pair_cmd(PAIR_STATUS);

	if (state < 0 || state > PAIR_IDLE)
		return 1;

	printf("%s\n", names[state]);

	return 0;
}

static int identify(const uint8_t *mac, char *str, size_t len)
{
	uint8_t resp[2 + 64];
	int n;

	n = mme(mac, MME_IDENTIFY, identify_key, sizeof(identify_key), resp, sizeof(resp));
	if (n < 2 || resp[1] > n - 2 || resp[1] >= len)
		return -1;

	memcpy(str, resp + 2, resp[1]);
	str[resp[1]] = 0;

	return 0;
}

static void print_mac(const uint8_t *mac)
{
	printf("%02x:%02x:%02x:%02x:%02x:%02x", mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
}

/* answer: size of an element, number of elements (le16), elements */
static int param_get(uint8_t index, uint8_t *val, size_t len)
{
	uint8_t req[2] = { index };
	uint8_t resp[3 + 64];
	int n;

	n = mme(soc_mac, MME_PARAM_GET, req, sizeof(req), resp, sizeof(resp));
	if (n < 0 || (size_t)n < 3 + len || resp[0] != 1 || resp[1] != len)
		return -1;

	memcpy(val, resp + 3, len);

	return 0;
}

static int cmd_info(void)
{
	uint8_t req[1 + NID_LEN] = { 1 };
	uint8_t resp[1 + 64 * 10];
	char str[65];
	int n, i;

	if (identify(soc_mac, str, sizeof(str)))
		return 1;

	printf("chip ");
	print_mac(soc_mac);
	printf(" %s\n", str);

	if (param_get(PARAM_NID, req + 1, NID_LEN))
		return 1;

	/* answer: number of stations, then address and two rates for each */
	n = mme(soc_mac, MME_STATIONS, req, sizeof(req), resp, sizeof(resp));
	if (n < 1 || n < 1 + resp[0] * 10)
		return 1;

	for (i = 0; i < resp[0]; i++) {
		const uint8_t *sta = resp + 1 + i * 10;

		printf("station ");
		print_mac(sta);
		printf(" tx %u rx %u Mbit/s", (sta[6] | sta[7] << 8) & 0x7ff,
		       (sta[8] | sta[9] << 8) & 0x7ff);

		if (!identify(sta, str, sizeof(str)))
			printf(" %s", str);

		printf("\n");
	}

	return 0;
}

static int cmd_key(const char *str)
{
	uint8_t req[NMK_LEN + 2] = {};
	uint8_t resp[1];
	unsigned int b;
	int i;

	if (!str) {
		if (param_get(PARAM_NMK, req, NMK_LEN))
			return 1;

		for (i = 0; i < NMK_LEN; i++)
			printf("%02x", req[i]);
		printf("\n");

		return 0;
	}

	if (strlen(str) != 2 * NMK_LEN)
		return -1;

	for (i = 0; i < NMK_LEN; i++) {
		if (sscanf(str + 2 * i, "%2x", &b) != 1)
			return -1;

		req[i] = b;
	}

	if (mme(soc_mac, MME_KEY_SET, req, sizeof(req), resp, sizeof(resp)) < 1 || resp[0])
		return 1;

	return 0;
}

static int cmd_restart(void)
{
	uint8_t resp[1];

	return mme(soc_mac, MME_RESTART, NULL, 0, resp, sizeof(resp)) < 0;
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
		"Usage: %s [options] <command>\n"
		"\n"
		"Options:\n"
		"  -i <ifname>   interface that leads to the chip (default: eth0)\n"
		"  -m <mac>      address of the chip (default: interface address + 2)\n"
		"\n"
		"Commands:\n"
		"  pair          start push-button pairing and wait for its end\n"
		"  cancel        end a pairing that is under way\n"
		"  status        state of the pairing\n"
		"  info          the chip and the stations of its network\n"
		"  key [<hex>]   show the network key, or set it (32 hex digits)\n"
		"  restart       restart the chip, it loads its firmware again\n",
		prog);

	return 1;
}

int main(int argc, char **argv)
{
	bool soc_mac_set = false;
	const char *cmd;
	int ch;

	while ((ch = getopt(argc, argv, "i:m:")) != -1) {
		switch (ch) {
		case 'i':
			ifname = optarg;
			break;
		case 'm':
			if (mac_parse(optarg, soc_mac))
				return usage(argv[0]);
			soc_mac_set = true;
			break;
		default:
			return usage(argv[0]);
		}
	}

	if (optind >= argc)
		return usage(argv[0]);

	cmd = argv[optind++];

	if (optind < argc - !strcmp(cmd, "key"))
		return usage(argv[0]);

	if (sock_open())
		return 1;

	if (!soc_mac_set) {
		memcpy(soc_mac, if_mac, ETH_ALEN);
		mac_add(soc_mac, 2);
	}

	/* requests of other programs on this host count on in the same byte */
	req_num = getpid();

	if (!strcmp(cmd, "pair"))
		return cmd_pair();
	if (!strcmp(cmd, "cancel"))
		return cmd_cancel();
	if (!strcmp(cmd, "status"))
		return cmd_status();
	if (!strcmp(cmd, "info"))
		return cmd_info();
	if (!strcmp(cmd, "restart"))
		return cmd_restart();

	if (!strcmp(cmd, "key")) {
		ch = cmd_key(argv[optind]);
		if (ch >= 0)
			return ch;
	}

	return usage(argv[0]);
}
