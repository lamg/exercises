#!/bin/sh

time cat data.txt | dotnet fsi -O prime_generator.fsx > primes.txt