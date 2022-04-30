#!/bin/sh
# e.g. ./trace.sh o//blc <<<00101
# you need to enable trace in blc.S or blc8.S
make &&
strace "$@" 2>&1 |
  sed '
      s/^getppid.*/Iop/
      s/^getuid.*/Var/
      s/^getgid.*/App/
      s/^getpid.*/Abs/
    '
