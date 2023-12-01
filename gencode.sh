#!/bin/bash

make -C codegen error_gen
codegen/error_gen > src/System/UV/Data/Error.idr
