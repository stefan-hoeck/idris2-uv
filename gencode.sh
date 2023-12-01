#!/usr/bin/env bash

make -C codegen all
codegen/error_gen > src/System/UV/Data/Error.idr
codegen/run_mode_gen >> src/System/UV/Data/RunMode.idr
