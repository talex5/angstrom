#!/bin/sh
for benchmark in json endian http numbers characters loops short-strings http-version; do
	dune exec -- ./benchmarks/pure_benchmark.exe $benchmark
done
