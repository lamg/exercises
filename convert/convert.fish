#!/usr/bin/env fish

# create output directory if it doesn't exist
mkdir -p output

# loop through all webm files in directory
for file in *.webm
    # extract audio from webm file and save as opus file
    ffmpeg -i "$file" -vn -acodec copy "output/$file:r.opus"
end