module core.sys.linux.unistd;

public import core.sys.posix.unistd;

version (linux):
extern(C):
nothrow:
@nogc:

import core.stdc.config : c_long;

// Additional seek constants for sparse file handling
// from Linux's unistd.h, stdio.h, and linux/fs.h
// (see http://man7.org/linux/man-pages/man2/lseek.2.html)
enum {
    /// Offset is relative to the next location containing data
    SEEK_DATA = 3,
    /// Offset is relative to the next hole (or EOF if file is not sparse)
    SEEK_HOLE = 4
}

/// Prompt for a password without echoing it.
char* getpass(const(char)* prompt);

// Exit all threads in a process
void exit_group(int status);

/// Close all open file descriptors greater or equal to `lowfd`
void closefrom(int lowfd);

/// Invoke system call number `sysno`, passing it the remaining arguments.
c_long syscall(c_long sysno, ...);
