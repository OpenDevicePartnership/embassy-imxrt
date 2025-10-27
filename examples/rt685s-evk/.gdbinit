set pagination off
target remote :2331
set print demangle
set print asm-demangle
mon reset
load
b main
c
d
layout split

