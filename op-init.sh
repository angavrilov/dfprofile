#!/bin/bash

opcontrol --deinit
echo 0 > /proc/sys/kernel/nmi_watchdog
opcontrol --start-daemon --no-vmlinux
opcontrol --reset
