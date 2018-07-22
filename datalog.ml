open Core

module Elem = struct
  type ('a, 's) t =
    | Here : ('a, 'a -> 'b) t
    | There : ('a, 's) t -> ('a, 'b -> 's) t
end

module Hlist = struct
  module Make (T : sig
    type 'a t
  end) = struct
    type _ t =
      | [] : unit t
      | (::) : 'a T.t * 'b t -> ('a -> 'b) t

    let rec get : type a x. a t -> (x, a) Elem.t -> x T.t =
      fun l elem ->
        match (l, elem) with
        | x :: _, Elem.Here -> x
        | _ :: xs, Elem.There e -> get xs e
        | _ -> .
  end

  include Make(struct type 'a t = 'a end)
end

module Prim = struct
  type _ t =
    | Int : int64 t
    | Symbol : string t

  module List = Hlist.Make(struct type nonrec 'a t = 'a t end)
end

module Relation = struct
  type 'a t = string * 'a Prim.List.t

  module List = Hlist.Make(struct type nonrec 'a t = 'a t end)
end

module Fact = struct
  type 'a t =
    | Fact of 'a Relation.t * 'a Hlist.t
end

module Free_bool_algebra = struct
  type 'a t =
    | And of 'a t * 'a t
    | Or of 'a t * 'a t
    | Not of 'a t
    | Pure of 'a

  let pure a = Pure a

  let (&&) a b = And (a, b)

  let (||) a b = Or (a, b)

  let (!~) a = Not a

  let (=>) a b = (!~ a) || b

  let xor a b = (a || b) && (!~ (a && b))

  let (=) a b = !~ (xor a b)
end

module Rule = struct
  module Self = struct
    type 'a t = Self
  end
  module Rule_term = struct
    type 'a t =
      | Self : 'a Hlist.t -> 'a t
      | Rel : 'a Relation.List.t * ('b, 'a) Elem.t * 'b Hlist.t -> 'b t
  end
  type 'a t =
    | T : string * 'a Relation.List.t * 'b Prim.List.t * 'c Rule_term.t Free_bool_algebra.t -> 'c t
end

module Db = struct
  module T = struct
    type 'a t =
      | Intro_rel :
        'r Relation.t * ('r Relation.t -> 'a t) -> 'a t
      | Intro_fact :
        'r Fact.t * (unit -> 'a t) -> 'a t
      | Intro_rule :
        'r Rule.t * (unit -> 'a t) -> 'a t
      | Pure : 'a -> 'a t

    let return a = Pure a
    let map = `Define_using_bind
    let rec bind t ~f = match t with
      | Intro_rel (relation, k) ->
          Intro_rel (relation, fun rel -> bind ~f (k rel))
      | Intro_fact (fact, k) ->
          Intro_fact (fact, fun () -> bind ~f (k ()))
      | Intro_rule (rule, k) ->
          Intro_rule (rule, fun () -> bind ~f (k ()))
      | Pure x -> f x
  end

  include T
  include Monad.Make(T)

  let intro_rel relation = Intro_rel (relation, return)

  let intro_fact fact = Intro_fact (fact, return)

  let intro_rule rule = Intro_rule (rule, return)
end

open Db
open Relation
open Fact
let sample =
  let open Db.Let_syntax in
  let sxs = Prim.List.[Symbol;Symbol] in
  let%bind node = intro_rel ("node", Prim.List.[Symbol]) in
  let%bind edge = intro_rel ("edge", sxs) in
  let%bind () = intro_fact (Fact (node, Hlist.["x"])) in
  let%bind () = intro_fact (Fact (edge, Hlist.["x";"y"])) in
  let%bind () = intro_fact (Fact (edge, Hlist.["y";"z"])) in
  let%bind () = intro_fact (Fact (edge, Hlist.["z";"w"])) in
  let rels = Relation.List.[edge;node] in
  let%map () = intro_rule
    (Rule.T ("path", rels, sxs,
      let open Free_bool_algebra in
      let open Rule.Rule_term in
      let path args = pure (Self args) in
      let edge args = pure (Rel (rels, Elem.Here, args)) in
      (edge (Hlist.["x"; "y"])) || (
        (path Hlist.["x";"z"]) && (path Hlist.["z";"y"])
      )
    ))
  in
  ()
;;
printf "Hello world\n"
