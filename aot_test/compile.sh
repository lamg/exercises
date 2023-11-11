#!/bin/bash

mkdir -p test_dir
cd cs_aot
dotnet publish -c Release -r linux-x64
mv bin/Release/net8.0/linux-x64/publish/cs_aot ../test_dir
cd ../fs_aot
dotnet publish -c Release -r linux-x64
mv bin/Release/net8.0/linux-x64/publish/fs_aot ../test_dir
