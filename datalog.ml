open Core

module Elem = struct
  type ('a, 's) t =
    | Here : ('a, 'a -> 'b) t
    | There : ('a, 's) t -> ('a, 'b -> 's) t
end

module V = struct
  type 'a t =
    { pprint : 'a -> string ; value : 'a }

  let sym value : string t =
    { pprint = Fn.id
    ; value }
  let num value : int64 t =
    { pprint = (fun v -> Int64.to_string v)
    ; value }
end

module Hlist = struct
  module Make (T : sig
    type 'a t
  end) = struct
    type _ t =
      | [] : unit t
      | (::) : 'a T.t * 'b t -> ('a -> 'b) t

    module Mapper = struct
      type 'b t = {f: 'a. 'a T.t -> 'b}
    end

    let rec map : type a. a t -> 'b Mapper.t -> 'b List.t =
      fun ls mapper ->
        match ls with
        | [] -> []
        | h :: t -> List.cons (mapper.f h) (map t mapper)

    let rec get : type a x. a t -> (x, a) Elem.t -> x T.t =
      fun l elem ->
        match (l, elem) with
        | x :: _, Elem.Here -> x
        | _ :: xs, Elem.There e -> get xs e
        | _ -> .

    let pprint : 'a t -> string Mapper.t -> string =
      fun t mapper ->
        let xs = map t mapper in
        List.fold xs ~init:None ~f:(fun acc x ->
          match acc with
          | None -> Some x
          | Some acc -> Some (acc ^ ", " ^ x)
        ) |> Option.value ~default:""
  end

  include Make(struct
    type 'a t = 'a V.t
  end)

  let pprint : 'a t -> string =
    fun t ->
    let m : string Mapper.t =
      let f : type a. a V.t -> string =
        fun {pprint;value} -> pprint value
      in
      { Mapper.f }
    in
    pprint t m
end

module Prim = struct
  module T = struct
    type _ t =
      | Int : int64 t
      | Symbol : string t

    let pprint : type a. a t -> string = function
      | Int -> "Int"
      | Symbol -> "Symbol"
  end

  include T
  module List = struct
    include Hlist.Make(T)
    let pprint prims =
      let m : string Mapper.t =
        let f = T.pprint in
        {Mapper.f}
      in
      pprint prims m
  end
end

module Relation = struct
  type 'a t = string * 'a Prim.List.t

  let pprint (name, prims) =
    Printf.sprintf "rel %s(%s)" name
      (Prim.List.pprint prims)

  module List = Hlist.Make(struct type nonrec 'a t = 'a t end)
end

module Fact = struct
  type 'a t =
    | Fact of 'a Relation.t * 'a Hlist.t

  let pprint (Fact (rel, args)) =
    Printf.sprintf "%s(%s)" (fst rel) (Hlist.pprint args)
end

module Free_bool_algebra = struct
  type 'a t =
    | And of 'a t * 'a t
    | Or of 'a t * 'a t
    | Not of 'a t
    | Pure of 'a

  let rec pprint pprint_a t =
    let f = pprint pprint_a in
    match t with
    | And (x, y) ->
        "(" ^ (f x) ^ " && " ^ (f y) ^ ")"
    | Or (x, y) ->
        "(" ^ (f x) ^ " || " ^ (f y) ^ ")"
    | Not x -> "(~" ^ f x ^ ")"
    | Pure a -> pprint_a a

  let pure a = Pure a

  let (&&) a b = And (a, b)

  let (||) a b = Or (a, b)

  let (!~) a = Not a

  let (=>) a b = (!~ a) || b

  let xor a b = (a || b) && (!~ (a && b))

  let (=) a b = !~ (xor a b)
end

module Rule = struct
  module Rule_term = struct
    type 'a t =
      | Self : 'a Hlist.t -> 'a t
      | Rel : 'a Relation.List.t * ('b, 'a) Elem.t * 'b Hlist.t -> 'b t

    let pprint self_name t =
      match t with
      | Self args ->
        Printf.sprintf "%s(%s)" self_name (Hlist.pprint args)
      | Rel (rels, elem, args) ->
        let rel = Relation.List.get rels elem in
        Printf.sprintf "%s(%s)" (fst rel) (Hlist.pprint args)
  end
  type 'a t =
    | T : string * 'b Prim.List.t * 'b Hlist.t * 'c Rule_term.t Free_bool_algebra.t -> 'c t

  let self args = Free_bool_algebra.pure (Rule_term.Self args)

  let rel rels elem args =
    Free_bool_algebra.pure (Rule_term.Rel (rels, elem, args))

  let pprint = function
    | T (name, prims, args, terms) ->
      let open Rule_term in
      Printf.sprintf "%s(%s):(%s) :- %s"
        name
        (Hlist.pprint args)
        (Prim.List.pprint prims)
        (Free_bool_algebra.pprint (Rule_term.pprint name) terms)
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

  let intro_rel name typ = Intro_rel ((name, typ), return)

  let intro_fact rel args = Intro_fact (Fact (rel, args), return)

  let (-:) f x = f x

  let intro_rule name typ args alg = Intro_rule (Rule.T (name, typ, args, alg), return)

  let rec pprint t =
    let f = pprint in
    match t with
    | Intro_rel (relation, k) ->
        Relation.pprint relation ^ ".\n" ^ (f (k relation))
    | Intro_fact (fact, k) ->
        Fact.pprint fact ^ ".\n" ^ (f (k ()))
    | Intro_rule (rule, k) ->
        Rule.pprint rule ^ ".\n" ^ (f (k ()))
    | Pure x -> ""
end

open Db
open Relation
open Fact
open V

let sample =
  let open Db.Let_syntax in
  let sxs = Prim.List.[Symbol;Symbol] in
  let%bind node = intro_rel "node" Prim.List.[Symbol] in
  let%bind edge = intro_rel "edge" sxs in
  let%bind () = intro_fact node Hlist.[sym "x"] in
  let%bind () = intro_fact edge Hlist.[sym "x"; sym "y"] in
  let%bind () = intro_fact edge Hlist.[sym "y"; sym "z"] in
  let%bind () = intro_fact edge Hlist.[sym "z"; sym "w"] in
  let rels = Relation.List.[edge;node] in
  let%map () =
    intro_rule "path" sxs Hlist.[sym "x";sym "y"] -: (
        let open Rule in
        let path = self in
        let edge = rel rels Elem.Here in

        let open Free_bool_algebra in
        (edge (Hlist.[sym "x"; sym "y"])) || (
          (path Hlist.[sym "x";sym "z"]) && (path Hlist.[sym "z"; sym "y"])
        )
      )
  in
  ()
;;

printf "\n\n%s" (Db.pprint sample)
