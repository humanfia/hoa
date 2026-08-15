#define _GNU_SOURCE

#include <errno.h>
#include <fcntl.h>
#include <linux/landlock.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

struct path_rule {
    const char *path;
    int writable;
};

static int landlock_create_ruleset(
    const struct landlock_ruleset_attr *attributes,
    size_t size,
    uint32_t flags
) {
    return (int)syscall(SYS_landlock_create_ruleset, attributes, size, flags);
}

static int landlock_add_rule(
    int ruleset,
    enum landlock_rule_type type,
    const void *attributes,
    uint32_t flags
) {
    return (int)syscall(SYS_landlock_add_rule, ruleset, type, attributes, flags);
}

static int landlock_restrict_self(int ruleset, uint32_t flags) {
    return (int)syscall(SYS_landlock_restrict_self, ruleset, flags);
}

static uint64_t handled_rights(int abi) {
    uint64_t rights =
        LANDLOCK_ACCESS_FS_EXECUTE |
        LANDLOCK_ACCESS_FS_WRITE_FILE |
        LANDLOCK_ACCESS_FS_READ_FILE |
        LANDLOCK_ACCESS_FS_READ_DIR |
        LANDLOCK_ACCESS_FS_REMOVE_DIR |
        LANDLOCK_ACCESS_FS_REMOVE_FILE |
        LANDLOCK_ACCESS_FS_MAKE_CHAR |
        LANDLOCK_ACCESS_FS_MAKE_DIR |
        LANDLOCK_ACCESS_FS_MAKE_REG |
        LANDLOCK_ACCESS_FS_MAKE_SOCK |
        LANDLOCK_ACCESS_FS_MAKE_FIFO |
        LANDLOCK_ACCESS_FS_MAKE_BLOCK |
        LANDLOCK_ACCESS_FS_MAKE_SYM;

    if (abi >= 2) {
        rights |= LANDLOCK_ACCESS_FS_REFER;
    }
    if (abi >= 3) {
        rights |= LANDLOCK_ACCESS_FS_TRUNCATE;
    }
    return rights;
}

static uint64_t read_rights(void) {
    return LANDLOCK_ACCESS_FS_EXECUTE |
           LANDLOCK_ACCESS_FS_READ_FILE |
           LANDLOCK_ACCESS_FS_READ_DIR;
}

static int add_path_rule(
    int ruleset,
    uint64_t handled,
    const struct path_rule *rule
) {
    struct stat metadata;
    struct landlock_path_beneath_attr attributes;
    uint64_t allowed = rule->writable ? handled : read_rights();
    int descriptor = open(rule->path, O_PATH | O_CLOEXEC);

    if (descriptor < 0) {
        fprintf(stderr, "landlock: cannot open %s: %s\n", rule->path, strerror(errno));
        return -1;
    }
    if (fstat(descriptor, &metadata) != 0) {
        fprintf(stderr, "landlock: cannot stat %s: %s\n", rule->path, strerror(errno));
        close(descriptor);
        return -1;
    }
    if (!S_ISDIR(metadata.st_mode)) {
        allowed &= LANDLOCK_ACCESS_FS_EXECUTE |
                   LANDLOCK_ACCESS_FS_WRITE_FILE |
                   LANDLOCK_ACCESS_FS_READ_FILE |
                   LANDLOCK_ACCESS_FS_TRUNCATE;
    }

    memset(&attributes, 0, sizeof(attributes));
    attributes.allowed_access = allowed;
    attributes.parent_fd = descriptor;
    if (landlock_add_rule(
            ruleset,
            LANDLOCK_RULE_PATH_BENEATH,
            &attributes,
            0
        ) != 0) {
        fprintf(stderr, "landlock: cannot allow %s: %s\n", rule->path, strerror(errno));
        close(descriptor);
        return -1;
    }
    close(descriptor);
    return 0;
}

static void usage(const char *program) {
    fprintf(
        stderr,
        "usage: %s [--ro PATH | --rw PATH]... -- PROGRAM [ARG ...]\n",
        program
    );
}

int main(int argc, char **argv) {
    struct path_rule *rules;
    struct landlock_ruleset_attr ruleset_attributes;
    uint64_t handled;
    int abi;
    int command_index = -1;
    int rule_count = 0;
    int ruleset;

    if (argc < 4) {
        usage(argv[0]);
        return 125;
    }
    rules = calloc((size_t)argc, sizeof(*rules));
    if (rules == NULL) {
        perror("calloc");
        return 125;
    }

    for (int index = 1; index < argc; ++index) {
        if (strcmp(argv[index], "--") == 0) {
            command_index = index + 1;
            break;
        }
        if ((strcmp(argv[index], "--ro") != 0 && strcmp(argv[index], "--rw") != 0)
            || index + 1 >= argc) {
            usage(argv[0]);
            free(rules);
            return 125;
        }
        rules[rule_count].writable = strcmp(argv[index], "--rw") == 0;
        rules[rule_count].path = argv[++index];
        ++rule_count;
    }
    if (command_index < 0 || command_index >= argc || rule_count == 0) {
        usage(argv[0]);
        free(rules);
        return 125;
    }

    abi = landlock_create_ruleset(NULL, 0, LANDLOCK_CREATE_RULESET_VERSION);
    if (abi < 1) {
        fprintf(stderr, "landlock: unsupported kernel ABI: %s\n", strerror(errno));
        free(rules);
        return 125;
    }
    handled = handled_rights(abi);
    memset(&ruleset_attributes, 0, sizeof(ruleset_attributes));
    ruleset_attributes.handled_access_fs = handled;
    ruleset = landlock_create_ruleset(
        &ruleset_attributes,
        sizeof(ruleset_attributes),
        0
    );
    if (ruleset < 0) {
        perror("landlock_create_ruleset");
        free(rules);
        return 125;
    }

    for (int index = 0; index < rule_count; ++index) {
        if (add_path_rule(ruleset, handled, &rules[index]) != 0) {
            close(ruleset);
            free(rules);
            return 125;
        }
    }
    if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) {
        perror("PR_SET_NO_NEW_PRIVS");
        close(ruleset);
        free(rules);
        return 125;
    }
    if (landlock_restrict_self(ruleset, 0) != 0) {
        perror("landlock_restrict_self");
        close(ruleset);
        free(rules);
        return 125;
    }
    close(ruleset);
    free(rules);

    if (setenv("IOI_LANDLOCK_ACTIVE", "1", 1) != 0) {
        perror("setenv");
        return 125;
    }

    execvp(argv[command_index], &argv[command_index]);
    perror("execvp");
    return 127;
}
