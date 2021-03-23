(*----------------------------------------------------------------------------
    Copyright (c) 2016 Inhabited Type LLC.

    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in the
       documentation and/or other materials provided with the distribution.

    3. Neither the name of the author nor the names of his contributors
       may be used to endorse or promote products derived from this software
       without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE CONTRIBUTORS ``AS IS'' AND ANY EXPRESS
    OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
    WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
    DISCLAIMED.  IN NO EVENT SHALL THE AUTHORS OR CONTRIBUTORS BE LIABLE FOR
    ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
    DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
    OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
    HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
    STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
  ----------------------------------------------------------------------------*)

module Bigarray = struct
  (* Do not access Bigarray operations directly. If anything's needed, refer to
   * the internal Bigstring module. *)
end

type bigstring = Bigstringaf.t

module Unbuffered = struct
  include Parser

  include Exported_state

  type more = More.t =
    | Complete
    | Incomplete

  effect Read : int -> (bigstring * int * int * More.t)
end

include Unbuffered
include Parser.Monad
include Parser.Choice

module Buffered = struct
  type unconsumed = Buffering.unconsumed =
    { buf : bigstring
    ; off : int
    ; len : int }

  type input =
    [ `Bigstring of bigstring
    | `String    of string ]

  type 'a state =
    | Partial of ([ input | `Eof ] -> 'a state)
    | Done    of unconsumed * 'a
    | Fail    of unconsumed * string list * string

  let from_unbuffered_state buffering = function
    | Unbuffered.Done(consumed, v) ->
      let unconsumed = Buffering.unconsumed ~shift:consumed buffering in
      Done(unconsumed, v)
    | Unbuffered.Fail(consumed, marks, msg) ->
      let unconsumed = Buffering.unconsumed ~shift:consumed buffering in
      Fail(unconsumed, marks, msg)

  let parse ?(initial_buffer_size=0x1000) p =
    if initial_buffer_size < 1 then
      failwith "parse: invalid argument, initial_buffer_size < 1";
    let buffering = Buffering.create initial_buffer_size in
    match Unbuffered.parse p with
    | x -> from_unbuffered_state buffering x
    | effect (Read committed) k ->
      Buffering.shift buffering committed;
      let cb input =
        let more : More.t =
          match input with
          | `Eof            -> Complete
          | #input as input ->
            Buffering.feed_input buffering input;
            Incomplete
        in
        let for_reading = Buffering.for_reading buffering in
        continue k (for_reading, 0, Bigstringaf.length for_reading, more)
      in
      Partial cb

  let feed state input =
    match state with
    | Partial k -> k input
    | Fail(unconsumed, marks, msg) ->
      begin match input with
      | `Eof   -> state
      | #input as input ->
        let buffering = Buffering.of_unconsumed unconsumed in
        Buffering.feed_input buffering input;
        Fail(Buffering.unconsumed buffering, marks, msg)
      end
    | Done(unconsumed, v) ->
      begin match input with
      | `Eof   -> state
      | #input as input ->
        let buffering = Buffering.of_unconsumed unconsumed in
        Buffering.feed_input buffering input;
        Done(Buffering.unconsumed buffering, v)
      end

  let state_to_option = function
    | Done(_, v) -> Some v
    | Partial _  -> None
    | Fail _     -> None

  let state_to_result = function
    | Partial _           -> Error "incomplete input"
    | Done(_, v)          -> Ok v
    | Fail(_, marks, msg) -> Error (Unbuffered.fail_to_string marks msg)

  let state_to_unconsumed = function
    | Done(unconsumed, _)
    | Fail(unconsumed, _, _) -> Some unconsumed
    | Partial _              -> None

end

let failf fmt =
  Printf.ksprintf (fun msg -> raise (Fail([], msg))) fmt

(** BEGIN: getting input *)

let rec prompt state =
  (* [prompt] returns [true] if it has received more input and
   * [false] if there is no chance that the input will grow, i.e., [more = Complete].
   * Otherwise (in the case where the input hasn't grown but [more = Incomplete] just prompt again. *)
  let input = state.Parser.input in
  let parser_uncommitted_bytes = Input.parser_uncommitted_bytes input in
  let parser_committed_bytes   = Input.parser_committed_bytes   input in
  let committed = Input.bytes_for_client_to_commit input in
  let input, off, len, more = perform (Read committed) in
  if len < parser_uncommitted_bytes then
    failwith "prompt: input shrunk!";
  state.input <- Input.create input ~off ~len ~committed_bytes:parser_committed_bytes;
  state.more <- more;
  if len = parser_uncommitted_bytes then
    match (state.more : More.t) with
    | Complete   -> false
    | Incomplete -> prompt state
  else
    true

let demand_input =
  { run = fun state ->
    match (state.more : More.t) with
    | Complete   ->
      failf "not enough input"
    | Incomplete ->
      if not (prompt state) then
        failf "not enough input"
  }

let ensure_suspended n state =
  let rec go =
    { run = fun state ->
      if state.pos + n <= Input.length state.input then
        ()
      else
        (demand_input *> go).run state
    }
  in
  (demand_input *> go).run state

let unsafe_apply len ~f =
  { run = fun state ->
    let r = Input.apply state.input state.pos len ~f in
    state.pos <- state.pos + len;
    r
  }

let unsafe_apply_opt len ~f =
  { run = fun state ->
    match Input.apply state.input state.pos len ~f with
    | Error e -> raise (Fail ([], e))
    | Ok    x ->
      state.pos <- state.pos + len;
      x
  }

let ensure n p =
  { run = fun state ->
    if state.pos + n <= Input.length state.input
    then p.run state
    else (
      ensure_suspended n state;
      p.run state
    )
  }

(** END: getting input *)

let at_end_of_input =
  { run = fun state ->
    if state.pos < Input.length state.input then
      false
    else match state.more with
    | Complete -> true
    | Incomplete -> not (prompt state)
  }

let end_of_input =
  at_end_of_input
  >>= function
    | true  -> return ()
    | false -> fail "end_of_input"

let advance n =
  if n < 0
  then fail "advance"
  else
    let p = { run = fun state -> state.pos <- state.pos + n } in
    ensure n p

let pos =
  { run = fun state -> state.pos }

let available =
  { run = fun state ->
    Input.length state.input - state.pos
  }

let commit =
  { run = fun state ->
    Input.commit state.input state.pos }

(* Do not use this if [p] contains a [commit]. *)
let unsafe_lookahead p =
  { run = fun state ->
    let old_pos = state.pos in
    let v = p.run state in
    state.pos <- old_pos;
    v
  }

let peek_char =
  { run = fun state ->
    if state.pos < Input.length state.input then
      Some (Input.unsafe_get_char state.input state.pos)
    else if state.more = Complete then
      None
    else
      if prompt state then
        Some (Input.unsafe_get_char state.input state.pos)
      else
        None
  }

(* This parser is too important to not be optimized. Do a custom job. *)
let rec peek_char_fail =
  { run = fun state ->
    if state.pos < Input.length state.input
    then Input.unsafe_get_char state.input state.pos
    else (
      ensure_suspended 1 state;
      peek_char_fail.run state
    )
  }

let satisfy f =
  { run = fun state ->
    if state.pos = Input.length state.input then
      ensure_suspended 1 state;
    let c = Input.unsafe_get_char state.input state.pos in
    if f c
    then (
      state.pos <- state.pos + 1;
      c
    ) else (
      failf "satisfy: %C" c
    )
  }

let char c =
  let p =
    { run = fun state ->
      if Input.unsafe_get_char state.input state.pos = c
      then (
        state.pos <- state.pos + 1;
        c
      ) else (
        failf "char %C" c
      )
    }
  in
  ensure 1 p

let not_char c =
  let p =
    { run = fun state ->
      let c' = Input.unsafe_get_char state.input state.pos in
      if c <> c'
      then (
        state.pos <- state.pos + 1;
        c'
      ) else (
        failf "not char %C" c
      )
    }
  in
  ensure 1 p

let any_char =
  let p =
    { run = fun state ->
      let c = Input.unsafe_get_char state.input state.pos in
      state.pos <- state.pos + 1;
      c
    }
  in
  ensure 1 p

let int8 i =
  let p =
    { run = fun state ->
      let c = Char.code (Input.unsafe_get_char state.input state.pos) in
      if c = i land 0xff
      then (
        state.pos <- state.pos + 1;
        c
      ) else (
        failf "int8 %d" i
      )
    }
  in
  ensure 1 p

let any_uint8 =
  let p =
    { run = fun state ->
      let c = Input.unsafe_get_char state.input state.pos in
      state.pos <- state.pos + 1;
      Char.code c
    }
  in
  ensure 1 p

let any_int8 =
  (* https://graphics.stanford.edu/~seander/bithacks.html#VariableSignExtendRisky *)
  let s = Sys.int_size - 8 in
  let p =
    { run = fun state ->
      let c = Input.unsafe_get_char state.input state.pos in
      state.pos <- state.pos + 1;
      (Char.code c lsl s) asr s
    }
  in
  ensure 1 p

let skip f =
  let p =
    { run = fun state ->
      if f (Input.unsafe_get_char state.input state.pos)
      then state.pos <- state.pos + 1
      else failf "skip" }
  in
  ensure 1 p

let rec count_while ~init ~f ~with_buffer =
  { run = fun state ->
    let pos         = state.pos in
    let len         = Input.count_while state.input (pos + init) ~f in
    let input_len   = Input.length state.input in
    let init'       = init + len in
    (* Check if the loop terminated because it reached the end of the input
     * buffer. If so, then prompt for additional input and continue. *)
    if pos + init' < input_len || state.more = Complete
    then (
      let r = Input.apply state.input pos init' ~f:with_buffer in
      state.pos <- pos + init';
      r
    ) else (
      if prompt state then
        (count_while ~init:init' ~f ~with_buffer).run state
      else (
        let r = Input.apply state.input pos init' ~f:with_buffer in
        state.pos <- pos + init';
        r
      )
    )
  }

let rec count_while1 ~f ~with_buffer =
  { run = fun state ->
    let pos         = state.pos in
    let len         = Input.count_while state.input pos ~f in
    let input_len   = Input.length state.input in
    (* Check if the loop terminated because it reached the end of the input
     * buffer. If so, then prompt for additional input and continue. *)
    if len < 1
    then
      if pos < input_len || state.more = Complete
      then failf "count_while1"
      else if prompt state then
        (count_while1 ~f ~with_buffer).run state
      else
        failf "count_while1"
    else if pos + len < input_len || state.more = Complete
    then (
      let r = Input.apply state.input pos len ~f:with_buffer in
      state.pos <- state.pos + len;
      r
    ) else (
      if prompt state then (
        (count_while ~init:len ~f ~with_buffer).run state
      ) else (
        let r = Input.apply state.input pos len ~f:with_buffer in
        state.pos <- state.pos + len;
        r
      )
    )
  }

let string_ f s =
  (* XXX(seliopou): Inefficient. Could check prefix equality to short-circuit
   * the io. *)
  let len = String.length s in
  ensure  len (unsafe_apply_opt len ~f:(fun buffer ~off ~len ->
    let i = ref 0 in
    while !i < len && Char.equal (f (Bigstringaf.unsafe_get buffer (off + !i)))
                                 (f (String.unsafe_get s !i))
    do
      incr i
    done;
    if len = !i
    then Ok (Bigstringaf.substring buffer ~off ~len)
    else Error "string"))

let string s    = string_ (fun x -> x) s
let string_ci s = string_ Char.lowercase_ascii s

let skip_while f =
  count_while ~init:0 ~f ~with_buffer:(fun _ ~off:_ ~len:_ -> ())

let take n =
  if n < 0
  then fail "take: n < 0"
  else
    let n = max n 0 in
    ensure n (unsafe_apply n ~f:Bigstringaf.substring)

let take_bigstring n =
  if n < 0
  then fail "take_bigstring: n < 0"
  else
    let n = max n 0 in
    ensure n (unsafe_apply n ~f:Bigstringaf.copy)

let take_bigstring_while f =
  count_while ~init:0 ~f ~with_buffer:Bigstringaf.copy

let take_bigstring_while1 f =
  count_while1 ~f ~with_buffer:Bigstringaf.copy

let take_bigstring_till f =
  take_bigstring_while (fun c -> not (f c))

let peek_string n =
  unsafe_lookahead (take n)

let take_while f =
  count_while ~init:0 ~f ~with_buffer:Bigstringaf.substring

let take_while1 f =
  count_while1 ~f ~with_buffer:Bigstringaf.substring

let take_till f =
  take_while (fun c -> not (f c))

let choice ?(failure_msg="no more choices") ps =
  List.fold_right (<|>) ps (fail failure_msg)

let fix f =
  let rec p = lazy (f r)
  and r = { run = fun state ->
    (Lazy.force p).run state }
  in
  r

let option x p =
  p <|> return x

let cons x xs = x :: xs

let rec list ps =
  match ps with
  | []    -> return []
  | p::ps -> lift2 cons p (list ps)

let count n p =
  if n < 0 
  then fail "count: n < 0"
  else 
    let rec loop = function
      | 0 -> return []
      | n -> lift2 cons p (loop (n - 1))
    in
    loop n

let many p =
  fix (fun m ->
    (lift2 cons p m) <|> return [])

let many1 p =
  lift2 cons p (many p)

let many_till p t =
  fix (fun m ->
    (t *> return []) <|> (lift2 cons p m))

let sep_by1 s p =
  fix (fun m ->
    lift2 cons p ((s *> m) <|> return []))

let sep_by s p =
  (lift2 cons p ((s *> sep_by1 s p) <|> return [])) <|> return []

let skip_many p =
  fix (fun m ->
    (p *> m) <|> return ())

let skip_many1 p =
  p *> skip_many p

let end_of_line =
  (char '\n' *> return ()) <|> (string "\r\n" *> return ()) <?> "end_of_line"

let scan_ state f ~with_buffer =
  { run = fun parser_state ->
    let state = ref state in
    let parser =
      count_while ~init:0 ~f:(fun c ->
        match f !state c with
        | None -> false
        | Some state' -> state := state'; true)
      ~with_buffer
      >>| fun x -> x, !state
    in
    parser.run parser_state }

let scan state f =
  scan_ state f ~with_buffer:Bigstringaf.substring

let scan_state state f =
  scan_ state f ~with_buffer:(fun _ ~off:_ ~len:_ -> ())
  >>| fun ((), state) -> state

let scan_string state f =
  scan state f >>| fst

let consume_with p f =
  { run = fun state ->
    let start = state.pos in
    let parser_committed_bytes = Input.parser_committed_bytes state.input  in
    let _ = p.run state in
    if parser_committed_bytes <> Input.parser_committed_bytes state.input
    then failf "consumed: parser committed"
    else (
      let len = state.pos - start in
      Input.apply state.input start len ~f
    )
  }

let consumed           p = consume_with p Bigstringaf.substring
let consumed_bigstring p = consume_with p Bigstringaf.copy

let both a b = lift2 (fun a b -> a, b) a b
let map t ~f = t >>| f
let bind t ~f = t >>= f
let map2 a b ~f = lift2 f a b
let map3 a b c ~f = lift3 f a b c
let map4 a b c d ~f = lift4 f a b c d

module Let_syntax = struct
  let return = return
  let ( >>| ) = ( >>| )
  let ( >>= ) = ( >>= )

  module Let_syntax = struct
    let return = return
    let map = map
    let bind = bind
    let both = both
    let map2 = map2
    let map3 = map3
    let map4 = map4
  end
end

let ( let+ ) = ( >>| )
let ( let* ) = ( >>= )
let ( and+ ) = both

module BE = struct
  (* XXX(seliopou): The pattern in both this module and [LE] are a compromise
   * between efficiency and code reuse. By inlining [ensure] you can recover
   * about 2 nanoseconds on average. That may add up in certain applications.
   *
   * This pattern does not allocate in the fast (success) path.
   * *)
  let int16 n =
    let bytes = 2 in
    let p =
      { run = fun state ->
        if Input.unsafe_get_int16_be state.input state.pos = (n land 0xffff)
        then state.pos <- state.pos + bytes
        else failf "BE.int16" }
    in
    ensure bytes p

  let int32 n =
    let bytes = 4 in
    let p =
      { run = fun state ->
        if Int32.equal (Input.unsafe_get_int32_be state.input state.pos) n
        then state.pos <- state.pos + bytes
        else failf "BE.int32" }
    in
    ensure bytes p

  let int64 n =
    let bytes = 8 in
    let p =
      { run = fun state ->
        if Int64.equal (Input.unsafe_get_int64_be state.input state.pos) n
        then state.pos <- state.pos + bytes
        else failf "BE.int64" }
    in
    ensure bytes p

  let any_uint16 =
    ensure 2 (unsafe_apply 2 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int16_be bs off))

  let any_int16  =
    ensure 2 (unsafe_apply 2 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int16_sign_extended_be  bs off))

  let any_int32  =
    ensure 4 (unsafe_apply 4 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int32_be bs off))

  let any_int64 =
    ensure 8 (unsafe_apply 8 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int64_be bs off))

  let any_float =
    ensure 4 (unsafe_apply 4 ~f:(fun bs ~off ~len:_ -> Int32.float_of_bits (Bigstringaf.unsafe_get_int32_be bs off)))

  let any_double =
    ensure 8 (unsafe_apply 8 ~f:(fun bs ~off ~len:_ -> Int64.float_of_bits (Bigstringaf.unsafe_get_int64_be bs off)))
end

module LE = struct
  let int16 n =
    let bytes = 2 in
    let p =
      { run = fun state ->
        if Input.unsafe_get_int16_le state.input state.pos = (n land 0xffff)
        then state.pos <- state.pos + bytes
        else failf "LE.int16" }
    in
    ensure bytes p

  let int32 n =
    let bytes = 4 in
    let p =
      { run = fun state ->
        if Int32.equal (Input.unsafe_get_int32_le state.input state.pos) n
        then state.pos <- state.pos + bytes
        else failf "LE.int32" }
    in
    ensure bytes p

  let int64 n =
    let bytes = 8 in
    let p =
      { run = fun state ->
        if Int64.equal (Input.unsafe_get_int64_le state.input state.pos) n
        then state.pos <- state.pos + bytes
        else failf "LE.int64" }
    in
    ensure bytes p


  let any_uint16 =
    ensure 2 (unsafe_apply 2 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int16_le bs off))

  let any_int16  =
    ensure 2 (unsafe_apply 2 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int16_sign_extended_le  bs off))

  let any_int32  =
    ensure 4 (unsafe_apply 4 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int32_le bs off))

  let any_int64 =
    ensure 8 (unsafe_apply 8 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int64_le bs off))

  let any_float =
    ensure 4 (unsafe_apply 4 ~f:(fun bs ~off ~len:_ -> Int32.float_of_bits (Bigstringaf.unsafe_get_int32_le bs off)))

  let any_double =
    ensure 8 (unsafe_apply 8 ~f:(fun bs ~off ~len:_ -> Int64.float_of_bits (Bigstringaf.unsafe_get_int64_le bs off)))
end

module Unsafe = struct
  let take n f =
    let n = max n 0 in
    ensure n (unsafe_apply n ~f)

  let peek n f =
    unsafe_lookahead (take n f)

  let take_while check f =
    count_while ~init:0 ~f:check ~with_buffer:f

  let take_while1 check f =
    count_while1 ~f:check ~with_buffer:f

  let take_till check f =
    take_while (fun c -> not (check c)) f
end

module Consume = struct
  type t =
    | Prefix
    | All
end

let parse_bigstring ~consume p bs =
  let p =
    match (consume : Consume.t) with
    | Prefix -> p
    | All -> p <* end_of_input
  in
  Unbuffered.parse_bigstring p bs

let parse_string ~consume p s =
  let len = String.length s in
  let bs  = Bigstringaf.create len in
  Bigstringaf.unsafe_blit_from_string s ~src_off:0 bs ~dst_off:0 ~len;
  parse_bigstring ~consume p bs
