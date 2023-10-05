#!/bin/sh

echo 'running for spoj_example.txt …'
time cat spoj_example.txt | dotnet fsi -O prime_generator.fsx > spoj_example.output.txt
echo ''
echo 'running for data.txt …'
time cat data.txt | dotnet fsi -O prime_generator.fsx > data.output.txt