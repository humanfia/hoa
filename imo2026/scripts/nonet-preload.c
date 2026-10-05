#define _GNU_SOURCE
#include <errno.h>
#include <sys/socket.h>

int socket(int domain, int type, int protocol) {
  (void)domain; (void)type; (void)protocol;
  errno = EACCES;
  return -1;
}

int socketpair(int domain, int type, int protocol, int sv[2]) {
  (void)domain; (void)type; (void)protocol; (void)sv;
  errno = EACCES;
  return -1;
}

int connect(int fd, const struct sockaddr *addr, socklen_t len) {
  (void)fd; (void)addr; (void)len;
  errno = EACCES;
  return -1;
}

int bind(int fd, const struct sockaddr *addr, socklen_t len) {
  (void)fd; (void)addr; (void)len;
  errno = EACCES;
  return -1;
}
