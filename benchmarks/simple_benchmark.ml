let read file =
  let open Unix in
  let size = (stat file).st_size in
  let buf  = Bytes.create size in
  let rec loop pos len fd =
    let n = read fd buf pos len in
    if n > 0 then loop (pos + n) (len - n) fd
  in
  let fd = Unix.openfile file Unix.[O_RDONLY] 0 in
  loop 0 size fd;
  Unix.close fd;
  Bigstringaf.of_string (Bytes.to_string buf) ~off:0 ~len:size

let () =
  let http_get = read "benchmarks/data/http-requests.txt.100" in
  let t0 = Unix.gettimeofday () in
  let n_iters = 100 in
  let p = Angstrom.skip_many RFC2616.request in
  for _ = 1 to n_iters do
    match Angstrom.(parse_bigstring ~consume:All) p http_get with
    | Ok _ -> ()
    | Error err -> failwith err
  done;
  let t1 = Unix.gettimeofday () in
  let time = t1 -. t0 in
  Printf.printf "Took %.2fms per iteration\n" (1000. *. time /. float n_iters)
