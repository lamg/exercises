# `convff`

`convff` is a command line program for encapsulating several patterns for converting videos using `ffmpeg`:

# Setup and usage

``` sh
cd convff
nix-shell
dune build
cp _build/default/bin/main.exe directory-with-video-files
cd directory-with-video-files
mkdir conv
./main.exe
# wait for ffmpeg to finish
# now converted videos are in conv
```
