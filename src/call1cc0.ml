(* call1cc0.ml *)

(* Compiles wih ocaml.5.3.0
   Compile & run:
     ocamlopt -o call1cc0.exe call1cc0.ml && ./call1cc0.exe
*)

open Effect
open Effect.Shallow

(* ------------------------------------------------------------------------- *)
(* Extension of OCaml's [Effect.Shallow] module with [continue] and
   [match_with], similar to the operations from [Effect.Deep]. *)

module Shallow : sig
  include (module type of Effect.Shallow)

  val continue : ('a, 'b) continuation -> 'a -> 'b

  val match_with : ('c -> 'a) -> 'c -> ('a, 'b) handler -> 'b

end = struct
  include Effect.Shallow

  let continue k x =
    continue_with k x
      { retc = Fun.id;
        exnc = raise;
        effc = fun _ -> None;
      }

  let match_with f x h =
    continue_with (fiber f) x h
end

(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Call1cc0. *)

module type CALL1CC0 = sig
  type 'a cont
  val call1cc0 : ('a cont -> 'b) -> 'a
  val throw : 'a cont -> 'a -> 'b
  val run : (unit -> unit) -> unit
  val fork : (unit -> unit) -> unit Domain.t
  val par : (unit -> unit) -> (unit -> unit) -> unit
end

module Call1cc0 : CALL1CC0 = struct

  type 'a cont = ('a, unit) Shallow.continuation

  type _ Effect.t += Call1cc0 : ('a cont -> 'b) -> 'a t
  type _ Effect.t += Throw : 'a cont * 'a -> 'b t

  let call1cc0 f = perform (Call1cc0 f)
  let throw k x = perform (Throw (k, x))

  let rec run (e : unit -> unit) : unit =
    Shallow.match_with e () {
      retc = Fun.id;
      exnc = raise;
      effc = fun (type c) (effc : c Effect.t) ->
        match effc with
        | (Call1cc0 f) -> Some (fun (k : (c, _) continuation) ->
            run (fun () -> let _ = f k in assert false))
        | (Throw (k, x)) -> Some (fun (_ : (c, _) continuation) ->
            run (fun () -> Shallow.continue k x))
        | _ ->
            None;
    }

  let fork e = Domain.spawn (fun () -> run e)
  let par f g =
    let df, dg = fork f, fork g in Domain.(join df; join dg)
end

(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Call1cc. *)

let call1cc f = Call1cc0.(call1cc0 (fun k -> throw k (f k)))

(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Cooperative multithreading using [call1cc0]. *)

let with_fork main = Call1cc0.(call1cc0 (fun return ->
  let q = Queue.create () in
  let next () =
    if Queue.is_empty q then throw return () else throw (Queue.take q) ()
  in
  let fork' task = call1cc0 (fun k -> Queue.add k q; task (); next ()) in
  let yield () = call1cc0 (fun k -> Queue.add k q; next ()) in
  main fork' yield;
  next ()
))

(* Example. *)
let () = Call1cc0.run (fun () ->
  let r = ref 0 in
  let () = with_fork (fun fork yield ->
    yield ();
    fork (fun () -> yield (); incr r);
    fork (fun () -> incr r; yield (); fork (fun () -> incr r));
  )
  in
  assert (!r = 3)
)

(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Control inversion using [call1cc0]. *)

let invertcc (type a) (iter : (a -> unit) -> unit) : a Seq.t =
  let open Call1cc0 in
  fun () -> call1cc0 (fun kc ->
    let r = ref kc in
    let yield x = call1cc0 (fun kp ->
      throw !r (Seq.Cons (x, fun () ->
        call1cc0 (fun kc -> r := kc; throw kp ())
      ))
    )
    in
    iter yield; throw !r Seq.Nil
  )

(* Example: same-fringe problem. *)
type 'a tree = Leaf of 'a | Branch of 'a tree * 'a tree

let rec iter t f = match t with Leaf x -> f x | Branch (l, r) -> iter l f; iter r f

let same_fringe t1 t2 =
  Seq.equal (=) (invertcc (iter t1)) (invertcc (iter t2))

let () = Call1cc0.run (fun () ->
  let t1 = Branch (Leaf 0, Branch (Leaf 1, Leaf 2)) in
  let t2 = Branch (Branch (Leaf 0, Leaf 1), Leaf 2) in
  let t3 = Branch (Branch (Leaf 0, Leaf 1), Leaf 3) in
  assert (same_fringe t1 t2);
  assert (not (same_fringe t1 t3));
  assert (same_fringe t2 t1);
  assert (not (same_fringe t3 t2))
)

(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Effect handlers using [call1cc0]. *)

type val_t = ..

module type HANDLER = functor (E : sig type 'x t end) -> sig
  type 'r t = {
    effc : 'x. 'x E.t -> ('x -> 'r) -> 'r;
    retc : val_t -> 'r;
  }

  val perform : 'x E.t -> 'x

  val handle :
    'r t ->            (* handler *)
    (unit -> val_t) -> (* computation *)
    'r
end

module Handler : HANDLER = functor (E : sig type 'x t end) -> struct

  type 'r t = {
    effc : 'x. 'x E.t -> ('x -> 'r) -> 'r;
    retc : val_t -> 'r;
  }

  type result =
   | Return : val_t -> result
   | Effect : 'x. 'x E.t * 'x Call1cc0.cont -> result

  let hs = Stack.create ()

  let abort res = let k = Stack.pop hs in Call1cc0.throw k res

  let perform (type x) (x : x E.t) = Call1cc0.call1cc0 (fun k ->
    abort (Effect (x, k)))

  let rec handle { effc; retc } (main : unit -> val_t) =
    let open Call1cc0 in
    match call1cc0 (fun k ->
      Stack.push k hs;
      let y = main () in
      abort (Return y))
    with
    | Return y -> retc y
    | Effect (x, k) ->
        effc x (fun y -> handle { effc; retc } (fun () -> throw k y))
end

(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Context-independent effects and handlers. *)

module type CIHANDLER = functor (E : sig type 'x t end) -> sig
  type ('a, 'r) t = {
    effc : 'x. 'x E.t -> ('x -> 'r) -> 'r;
    retc : 'a -> 'r;
  }

  type perform = { perform : 'x. 'x E.t -> 'x }

  val with_perform :
    ('a, 'r) t ->      (* handler *)
    (perform -> 'a) -> (* computation *)
    'r
end

module CIHandler : CIHANDLER = functor (E : sig type 'x t end) -> struct

  type ('a, 'r) t = {
    effc : 'x. 'x E.t -> ('x -> 'r) -> 'r;
    retc : 'a -> 'r;
  }

  type perform = { perform : 'x. 'x E.t -> 'x }

  let with_perform { effc; retc } main =
    let open struct
      type 'a result =
      | Return : 'a. 'a -> 'a result
      | Effect : 'a 'x. 'x E.t * 'x Call1cc0.cont -> 'a result
    end in
    let r = ref None in
    let rec run comp =
      match
        Call1cc0.call1cc0 (fun k ->
          r := Some k;
          let y = comp () in
          Call1cc0.throw (Option.get !r) (Return y)
        )
      with
      | Return y -> retc y
      | Effect (x, k) -> effc x (fun y -> run (fun () -> Call1cc0.throw k y))
    in
    let perform (type x) (x : x E.t) : x = Call1cc0.call1cc0 (fun k ->
      Call1cc0.throw (Option.get !r) (Effect (x, k)))
    in
    run (fun () -> main { perform })
end


(* Examples. *)

(* Concurrent counter. *)
let () = Call1cc0.(run (fun () ->
  let module Incr = struct type 'x t = Incr : unit t end in
  let module IncrHandler = CIHandler(Incr) in

  let with_incr ~init main =
    let open Incr in
    let effc (type x) (e : x Incr.t) (k : x -> (int -> int)) =
      match e with Incr -> (fun (s : int) -> k () (s + 1))
    in
    let retc () s = s in
    begin IncrHandler.with_perform { effc; retc } (fun { perform } ->
      main (fun () -> perform Incr))
    end init
  in

  let y = with_incr ~init:0 (fun incr ->
    let lock = Mutex.create () in
    let update () = Mutex.protect lock incr in
    par update update
  )
  in
  assert (y = 2)
))

(* g and f. *)
let () = Call1cc0.run (fun () ->
  let module F = struct type 'x t = F : 'y. 'y * ('y -> 'y) -> 'y t end in
  let module G = struct type 'x t = G : unit t end in

  let module HF = CIHandler(F) in
  let module HG = CIHandler(G) in

  let effc (type x) (x : x F.t) (k : x -> unit) = match x with F (y, g) -> k (g y) in
  HF.with_perform { effc; retc = (fun () -> ()) } (fun f ->
    let effc (type x) (x : x G.t) (k : x -> unit) = match x with G -> k () in
    HG.with_perform { effc; retc = (fun () -> ()) } (fun g ->
      f.perform (F ((), fun () -> g.perform G))
    )
  )
)

(* Generators. *)
module Generators : sig
  type 'a t
  val create : (('a -> unit) -> unit) -> 'a t
  val next   : 'a t -> 'a option
end = struct
  type 'a t = 'a Seq.t option ref

  let with_yield (type a) (g : (a -> unit) -> unit) : a Seq.t = fun () ->
    let module E = struct type 'x t = Yield : a -> unit t end in
    let module H = CIHandler(E) in
    let effc (type x) (e : x E.t) (k : x -> a Seq.node) =
      match e with E.Yield x -> Seq.Cons (x, k)
    in
    let retc () = Seq.Nil in
    H.with_perform { effc; retc } (fun { perform } ->
      g (fun x -> perform (E.Yield x))
    )

  let create g = ref (Some (with_yield g))

  let next c =
    match let g = Option.get !c in c := None; g () with
    | Seq.Cons (x, g') -> c := Some g'; Some x
    | Seq.Nil -> None
end

let () = Call1cc0.run (fun () ->
  let rec g n yield = yield n; g (n + 1) yield in
  let c = Generators.create (g 0) in

  for i = 0 to 10 do
    assert (Generators.next c = Some i)
  done
)

(* Get/Set effects. *)
let () = Call1cc0.(run (fun () ->
  let module State = struct type 'x t = Get : int t | Set : int -> unit t end in
  let module StateCIHandler = CIHandler(State) in

  let open struct type 'a cell = { get : unit -> 'a; set : 'a -> unit } end in
  let with_state ~init main =
    let open State in
    let effc (type x) (e : x State.t) (k : x -> (int -> int)) =
      match e with Get -> (fun (s : int) -> k s s) | Set y -> (fun _ -> k () y)
    in
    let retc () s = s in
    begin StateCIHandler.with_perform { effc; retc } (fun { perform } ->
       main { get = (fun () -> perform Get); set = (fun y -> perform (Set y)) }
    ) end init
  in

  let _ = with_state ~init:0 (fun res ->
    let open State in

    let fact n =
      res.set 1;
      let rec loop k =
        if k <= 1 then
          res.get ()
        else begin
          res.set (res.get () * k);
          loop (k - 1)
        end
      in
      loop n
    in

    assert (fact 2 = 2);
    assert (fact 3 = 6);
    assert (fact 4 = 24);
    assert (fact 5 = 120);
    assert (fact 6 = 720);
    assert (fact 7 = 5040)
  )
  in

  ()
))

(* Performing an effect after [main]'s lifetime. *)
let () =
  try Call1cc0.run (fun () ->
    let module Escape = struct type 'x t = Escape : unit t end in
    let module EscapeHandler = CIHandler(Escape) in

    let effc (type x) (e : x Escape.t) (k : x -> unit) =
      match e with Escape -> k ()
    in
    let retc f = f () in

    let main ({ perform } : EscapeHandler.perform) = (fun () -> perform Escape) in

    EscapeHandler.with_perform { effc; retc } main);

    (* This line cannot be reached: *)
    assert false
  with Continuation_already_resumed ->
    () (* Exception is raised (and caught) as expected. *)

(* ------------------------------------------------------------------------- *)
