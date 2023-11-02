open! Core

let list_dir (dir : string) =
  let hnd = UnixLabels.opendir dir in
  let rec rd (ls : string list) =
    (try UnixLabels.readdir hnd |> Option.return with
     | End_of_file -> None)
    |> Option.value_map ~default:ls ~f:(fun n -> rd (n :: ls))
  in
  rd []
;;

let list_videos (dir : string) =
  let extensions = [ ".mp4"; ".mkv"; ".webm" ] in
  let is_video n =
    extensions |> List.exists ~f:(fun ext -> String.is_suffix n ~suffix:ext)
  in
  dir |> list_dir |> List.filter ~f:is_video
;;

type stream =
  { codec_name : string
  ; codec_type : string
  ; r_frame_rate : string
  }
[@@deriving yojson] [@@yojson.allow_extra_fields]

type stream_info = { streams : stream list }
[@@deriving yojson] [@@yojson.allow_extra_fields]

let parse_info (info : string) : stream_info option =
  try
    info |> Yojson.Safe.from_string |> stream_info_of_yojson |> Option.return
  with
  | _ -> None
;;

let command_output (cmd : string) (args : string list) =
  let arr_args = Array.of_list (cmd :: args) in
  let ch = UnixLabels.open_process_args_in cmd arr_args in
  let s = In_channel.input_all ch in
  let _ = UnixLabels.close_process_in ch in
  s
;;

let ( $ ) = Fn.compose

let get_stream_info (file : string) =
  command_output
    "ffprobe"
    [ "-loglevel"
    ; "8"
    ; "-hide_banner"
    ; "-print_format"
    ; "json"
    ; "-show_streams"
    ; file
    ]
  |> parse_info
  |> Option.map ~f:(fun i -> file, i)
;;

type video_info =
  { audio_codec : string
  ; video_codec : string
  ; fps : int
  ; file : string
  }
[@@deriving show]

let get_video_info ((file, v) : string * stream_info) =
  let audio_codec =
    v.streams |> List.find ~f:(fun s -> String.equal s.codec_type "audio")
  in
  let video_codec =
    v.streams |> List.find ~f:(fun s -> String.equal s.codec_type "video")
  in
  let parse_fps r_frame_rate =
    r_frame_rate
    |> String.split ~on:'/'
    |> function
    | [ snum; sden ] -> Some (Int.of_string snum / Int.of_string sden)
    | _ -> None
  in
  (match audio_codec, video_codec with
   | Some a, Some v -> Some (a, v)
   | _, _ -> None)
  |> Option.value_map ~default:None ~f:(fun (a, v) ->
       parse_fps v.r_frame_rate
       |> Option.map ~f:(fun fps ->
            { audio_codec = a.codec_name
            ; video_codec = v.codec_name
            ; fps
            ; file
            }))
;;

let mkv_args (output_dir : string) (v : video_info) =
  let output_audio =
    match v.audio_codec with
    | "aac"
    | "mp3"
    | "vorbis" ->
      "copy"
    | _ -> "libvorbis"
  in
  let output_video =
    match v.video_codec with
    | "h264" -> "copy"
    | _ -> "h264"
  in
  [ "-i"
  ; v.file
  ; "-vcodec"
  ; output_video
  ; "-acodec"
  ; output_audio
  ; Printf.sprintf "%s/%s.mkv" output_dir v.file
  ]
;;

let convert (args : string list) = command_output "ffmpeg" args

let main () =
  let ( >>= ) = Option.( >>= ) in
  let r = Option.return in
  list_videos "."
  |> List.filter_map ~f:(fun file ->
       get_stream_info file
       >>= get_video_info
       >>= (r $ mkv_args "conv")
       >>= (r $ convert))
  |> List.iter ~f:print_endline
;;
