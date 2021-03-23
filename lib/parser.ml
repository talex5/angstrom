exception Fail of Input.t * int * More.t * string list * string

type 'a with_state = Input.t ->  int -> More.t -> 'a

type 'a t =
  { run : (Input.t * int * More.t * 'a) with_state }

let parse p =
  let input = Input.create Bigstringaf.empty ~committed_bytes:0 ~off:0 ~len:0 in
  match p.run input 0 Incomplete with
  | (input, i, _more, x) ->
    Exported_state.Done (i - Input.client_committed_bytes input,x)
  | exception Fail (input, i, _more, sl, s) -> Exported_state.Fail (i - Input.client_committed_bytes input, sl, s)

let parse_bigstring p input =
  let input = Input.create input ~committed_bytes:0 ~off:0 ~len:(Bigstringaf.length input) in
  Exported_state.state_to_result (
    match p.run input 0 Complete with
    | (input, i, _more, x) -> Exported_state.Done (i - Input.client_committed_bytes input,x)
    | exception Fail (input, i, _more, sl, s) -> Exported_state.Fail (i - Input.client_committed_bytes input, sl, s)
  )

module Monad = struct
  let return v =
    { run = fun input pos more -> input, pos, more, v }

  let fail msg =
    { run = fun input pos more -> raise_notrace (Fail (input, pos, more, [], msg)) }

  let (>>=) p f =
    { run = fun input pos more ->
      let input', pos', more', v = p.run input pos more in
      (f v).run input' pos' more'
    }

  let (>>|) p f =
    { run = fun input pos more ->
      let input', pos', more', v = p.run input pos more in
      input', pos', more', f v
    }

  let (<$>) f m =
    m >>| f

  let (<*>) f m =
    (* f >>= fun f -> m >>| f *)
    { run = fun input pos more ->
      let input, pos, more, f = f.run input pos more in
      let input, pos, more, m = m.run input pos more in
      input, pos, more, f m
    }

  let lift f m =
    f <$> m

  let lift2 f m1 m2 =
    { run = fun input pos more ->
      let input, pos, more, m1 = m1.run input pos more in
      let input, pos, more, m2 = m2.run input pos more in
      input, pos, more, f m1 m2
    }

  let lift3 f m1 m2 m3 =
    { run = fun input pos more ->
      let input, pos, more, m1 = m1.run input pos more in
      let input, pos, more, m2 = m2.run input pos more in
      let input, pos, more, m3 = m3.run input pos more in
      input, pos, more, f m1 m2 m3
    }

  let lift4 f m1 m2 m3 m4 =
    { run = fun input pos more ->
      let input, pos, more, m1 = m1.run input pos more in
      let input, pos, more, m2 = m2.run input pos more in
      let input, pos, more, m3 = m3.run input pos more in
      let input, pos, more, m4 = m4.run input pos more in
      input, pos, more, f m1 m2 m3 m4
    }

  let ( *>) a b =
    (* a >>= fun _ -> b *)
    { run = fun input pos more ->
      let input, pos, more, _ = a.run input pos more in
      b.run input pos more
    }

  let (<* ) a b =
    (* a >>= fun x -> b >>| fun _ -> x *)
    { run = fun input pos more ->
      let input, pos, more, x = a.run input pos more in
      let input, pos, more, _ = b.run input pos more in
      input, pos, more, x
    }
end

module Choice = struct
  let (<?>) p mark =
    { run = fun input pos more ->
      try p.run input pos more
      with Fail (input', pos', more', marks, msg) ->
        raise_notrace (Fail (input', pos', more', (mark::marks), msg))
    }

  let (<|>) p q =
    { run = fun input pos more ->
      try p.run input pos more
      with Fail (input', pos', more', marks, msg) ->
        (* The only two constructors that introduce new failure continuations are
         * [<?>] and [<|>]. If the initial input position is less than the length
         * of the committed input, then calling the failure continuation will
         * have the effect of unwinding all choices and collecting marks along
         * the way. *)
        if pos < Input.parser_committed_bytes input' then
          (* Not sure why we re-raise with the original [more] here. Maybe it doesn't matter. *)
          raise_notrace (Fail (input', pos', more, marks, msg))
        else
          q.run input' pos more'
    }
end

module Monad_use_for_debugging = struct
  let return = Monad.return
  let fail   = Monad.fail
  let (>>=)  = Monad.(>>=)

  let (>>|) m f = m >>= fun x -> return (f x)

  let (<$>) f m = m >>| f
  let (<*>) f m = f >>= fun f -> m >>| f

  let lift  = (>>|)
  let lift2 f m1 m2       = f <$> m1 <*> m2
  let lift3 f m1 m2 m3    = f <$> m1 <*> m2 <*> m3
  let lift4 f m1 m2 m3 m4 = f <$> m1 <*> m2 <*> m3 <*> m4

  let ( *>) a b = a >>= fun _ -> b
  let (<* ) a b = a >>= fun x -> b >>| fun _ -> x
end
