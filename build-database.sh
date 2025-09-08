#!/bin/bash

codeql database create \
    --overwrite \
    --source-root="/home/user/repo/buildroot-x86_64/output/build/linux-6.12.9" \
    --threads=31 \
    --command="make clean && make -j31" \
    --language=c \
    --ram=200000 \
    ./linux-database
