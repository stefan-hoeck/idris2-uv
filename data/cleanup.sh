#!/usr/bin/env bash

if [ "$(
    git status >/dev/null 2>&1
    echo $?
)" -eq 0 ]; then
    git restore src/System/UV/Data/Error.idr
    git restore src/System/UV/Data/Pointer.idr
    git restore src/System/UV/Data/RunMode.idr
fi
