#!/bin/bash

set -e

SUDOERS_FILE=/etc/sudoers.d/ubuntu-nopasswd
echo -e 'ubuntu\tALL=(ALL) NOPASSWD:ALL' > "$SUDOERS_FILE"

chmod 400 "$SUDOERS_FILE"

passwd -d ubuntu
