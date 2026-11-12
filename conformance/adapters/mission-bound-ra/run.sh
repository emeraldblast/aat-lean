#!/bin/sh
# no network; type stripping plus transforms (parameter properties)
exec sandbox-exec -p '(version 1)(allow default)(deny network*)' node --no-warnings "$(dirname "$0")/adapter.ts"
