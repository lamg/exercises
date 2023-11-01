#!/usr/bin/env fish

# loop through all webm files in directory
for file in *.webm
    # extract audio from webm file and save as opus file
    ffmpeg -i "$file" -vn -acodec copy "$file.opus"
end