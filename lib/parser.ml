exception Fail of string list * string

type state = {
  mutable input : Input.t;
  mutable pos : int;
  mutable more : More.t;
}

type 'a t =
  { run : state -> 'a }

let parse p =
  let state = {
    input = Input.create Bigstringaf.empty ~committed_bytes:0 ~off:0 ~len:0;
    pos = 0;
    more = Incomplete;
  } in
  match p.run state with
  | x ->
    Exported_state.Done (state.pos - Input.client_committed_bytes state.input, x)
  | exception Fail (sl, s) -> Exported_state.Fail (state.pos - Input.client_committed_bytes state.input, sl, s)

let parse_bigstring p input =
  let state = {
    input = Input.create input ~committed_bytes:0 ~off:0 ~len:(Bigstringaf.length input);
    pos = 0;
    more = Complete;
  } in
  Exported_state.state_to_result (
    match p.run state with
    | x -> Exported_state.Done (state.pos - Input.client_committed_bytes state.input, x)
    | exception Fail (sl, s) -> Exported_state.Fail (state.pos - Input.client_committed_bytes state.input, sl, s)
  )

module Monad = struct
  let return v = { run = fun _state -> v }

  let fail msg =
    { run = fun _state -> raise_notrace (Fail ([], msg)) }

  let (>>=) p f =
    { run = fun state ->
      let v = p.run state in
      (f v).run state
    }

  let (>>|) p f =
    { run = fun state ->
      let v = p.run state in
      f v
    }

  let (<$>) f m =
    m >>| f

  let (<*>) f m =
    (* f >>= fun f -> m >>| f *)
    { run = fun state ->
      let f = f.run state in
      let m = m.run state in
      f m
    }

  let lift f m =
    f <$> m

  let lift2 f m1 m2 =
    { run = fun state ->
      let m1 = m1.run state in
      let m2 = m2.run state in
      f m1 m2
    }

  let lift3 f m1 m2 m3 =
    { run = fun state ->
      let m1 = m1.run state in
      let m2 = m2.run state in
      let m3 = m3.run state in
      f m1 m2 m3
    }

  let lift4 f m1 m2 m3 m4 =
    { run = fun state ->
      let m1 = m1.run state in
      let m2 = m2.run state in
      let m3 = m3.run state in
      let m4 = m4.run state in
      f m1 m2 m3 m4
    }

  let ( *>) a b =
    (* a >>= fun _ -> b *)
    { run = fun state ->
      let _ = a.run state in
      b.run state
    }

  let (<* ) a b =
    (* a >>= fun x -> b >>| fun _ -> x *)
    { run = fun state ->
      let x = a.run state in
      let _ = b.run state in
      x
    }
end

module Choice = struct
  let (<?>) p mark =
    { run = fun state ->
      try p.run state
      with Fail (marks, msg) ->
        raise_notrace (Fail ((mark::marks), msg))
    }

  let (<|>) p q =
    { run = fun state ->
      let old_pos = state.pos in
      try p.run state
      with Fail (marks, msg) ->
        (* The only two constructors that introduce new failure continuations are
         * [<?>] and [<|>]. If the initial input position is less than the length
         * of the committed input, then calling the failure continuation will
         * have the effect of unwinding all choices and collecting marks along
         * the way. *)
        if old_pos < Input.parser_committed_bytes state.input then
          raise_notrace (Fail (marks, msg))
        else (
          state.pos <- old_pos;
          q.run state
        )
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
