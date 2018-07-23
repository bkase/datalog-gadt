open Core

module Elem = struct
  type ('a, 's) t =
    | Here : ('a, 'a -> 'b) t
    | There : ('a, 's) t -> ('a, 'b -> 's) t

  let rec equal : type a s. (a, s) t -> (a, s) t -> bool =
    fun t t' ->
      match (t, t') with
      | Here, Here -> true
      | There xs, There xs' -> equal xs xs'
      | Here, There _ -> false
      | There _, Here -> false
end

module V = struct
  type 'a t =
    { eq : 'a -> 'a -> bool
    ; pprint : 'a -> string
    ; value : 'a }

  let sym value : string t =
    { eq = String.equal
    ; pprint = Fn.id
    ; value }
  let num value : int64 t =
    { eq = Int64.equal
    ; pprint = (fun v -> Int64.to_string v)
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

    let pprint : string Mapper.t -> 'a t -> string =
      fun mapper t ->
        let xs = map t mapper in
        List.fold xs ~init:None ~f:(fun acc x ->
          match acc with
          | None -> Some x
          | Some acc -> Some (acc ^ ", " ^ x)
        ) |> Option.value ~default:""

    module Pred = struct
      type t = {p: 'a. 'a T.t -> 'a T.t -> bool}
    end

    let rec equal : type a. Pred.t -> a t -> a t -> bool =
      fun p t t' ->
        match (t, t') with
        | [], [] -> true
        | x :: xs, y:: ys ->
          p.p x y && equal p xs ys
        | _ -> .
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
    pprint m t

  let equal : 'a t -> 'a t -> bool =
    fun t t' ->
    let p : Pred.t =
      let p : type a. a V.t -> a V.t -> bool =
        fun {eq; value} {value=value'} -> eq value value'
      in
      { Pred.p }
    in
    equal p t t'
end

module V_with_holes = struct
  include Hlist.Make(struct
    type 'a t = 'a V.t option
  end)

  let pprint : 'a t -> string =
    fun t ->
    let m : string Mapper.t =
      let f : type a. a V.t option -> string =
        fun t ->
          match t with
          | None -> "?"
          | Some {pprint; value} -> pprint value
      in
      { Mapper.f }
    in
    pprint m t
end


module Prim = struct
  module T = struct
    type _ t =
      | Int : int64 t
      | Symbol : string t

    let pprint : type a. a t -> string = function
      | Int -> "Int"
      | Symbol -> "Symbol"

    let equal : type a. a t -> a t -> bool =
      fun t t' ->
        match (t, t') with
        | Int, Int -> true
        | Symbol, Symbol -> true
  end

  include T
  module List = struct
    include Hlist.Make(T)
    let pprint prims =
      let m : string Mapper.t =
        let f = T.pprint in
        {Mapper.f}
      in
      pprint m prims

    let equal prims =
      let p : Pred.t =
        let p = T.equal in
        {Pred.p}
      in
      equal p prims
  end
end

module Relation = struct
  module T = struct
    type 'a t = string * 'a Prim.List.t

    let equal : type a. a t -> a t -> bool =
      fun (n1, prims1) (n2, prims2) ->
        String.equal n1 n2 && Prim.List.equal prims1 prims2
  end

  include T
  module List = struct
    include Hlist.Make(T)

    let equal rels =
      let p : Pred.t =
        let p = T.equal in
        {Pred.p}
      in
      equal p rels
  end

  let pprint (name, prims) =
    Printf.sprintf "rel %s(%s)" name
      (Prim.List.pprint prims)
end

module Fact = struct
  type 'a t =
    | Fact of 'a Relation.t * 'a Hlist.t

  let pprint (Fact (rel, args)) =
    Printf.sprintf "%s(%s)" (fst rel) (Hlist.pprint args)

  let equal : type a. a t -> a t -> bool =
    fun (Fact (r1, args1)) (Fact (r2, args2)) ->
      Relation.equal r1 r2 && Hlist.equal args1 args2
end

module Free_bool_algebra = struct
  type 'a t =
    | True
    | False
    | And of 'a t * 'a t
    | Or of 'a t * 'a t
    | Not of 'a t
    | Pure of 'a
  [@@deriving eq]

  let rec pprint pprint_a t =
    let f = pprint pprint_a in
    match t with
    | True -> "true"
    | False -> "false"
    | And (x, y) ->
        "(" ^ (f x) ^ " && " ^ (f y) ^ ")"
    | Or (x, y) ->
        "(" ^ (f x) ^ " || " ^ (f y) ^ ")"
    | Not x -> "(~" ^ f x ^ ")"
    | Pure a -> pprint_a a

  let simplify eq_a =
    let eq = equal eq_a in
    function
    (* Not-not *)
    | Not (Not x) -> x
    (* Identity *)
    | And (True, x) | And (x, True) -> x
    | Or (False, x) | Or (x, False) -> x
    (* Annihlation *)
    | And (False, _) | And (_, False) -> False
    | Or (True, _) | Or (_, True) -> True
    (* Idempotence *)
    | And (x1, x2) when eq x1 x2 -> x1
    | Or (x1, x2) when eq x1 x2 -> x1
    (* Absorption *)
    | And (x1, (Or (x2, _))) when eq x1 x2 -> x1
    | And (x1, (Or (_, x2))) when eq x1 x2 -> x1
    | And ((Or (x2, _)), x1) when eq x1 x2 -> x1
    | And ((Or (_, x2)), x1) when eq x1 x2 -> x1
    | And (x1, (Or (x2, _))) when eq x1 x2 -> x1
    | And (x1, (Or (_, x2))) when eq x1 x2 -> x1
    | And ((Or (x2, _)), x1) when eq x1 x2 -> x1
    | And ((Or (_, x2)), x1) when eq x1 x2 -> x1
    (* Distributive *)
    | Or (And (y, x1), And (z, x2)) when eq x1 x2 ->
        And (Or (y, z), x1)
    | And (Or (y, x1), Or (z, x2)) when eq x1 x2 ->
        Or (And (y, z), x1)
    | Or (And (x1, y), And (x2, z)) when eq x1 x2 ->
        And (x1, Or (y, z))
    | And (Or (x1, y), Or (x2, z)) when eq x1 x2 ->
        Or (x1, And (y, z))
    (* Nothing *)
    | x -> x

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
      | Rel : 'a Relation.t * 'a Hlist.t -> 'a t

    let pprint self_name t =
      match t with
      | Self args ->
        Printf.sprintf "%s(%s)" self_name (Hlist.pprint args)
      | Rel (rel, args) ->
        Printf.sprintf "%s(%s)" (fst rel) (Hlist.pprint args)

    let equal : type a. a t -> a t -> bool =
      fun t t' ->
        match (t, t') with
        | (Self args, Self args2) -> Hlist.equal args args2
        | (Rel (rel, args), Rel (rel2, args2)) ->
            Relation.equal rel rel2 &&
              Hlist.equal args args2
        | (Self _, Rel _) -> false
        | (Rel _, Self _) -> false

  end
  type ('a, 'b) t =
    | T : 'a Relation.t * 'a Hlist.t * 'b Rule_term.t Free_bool_algebra.t -> ('a, 'b) t

  let self args = Free_bool_algebra.pure (Rule_term.Self args)

  let rel rel args =
    Free_bool_algebra.pure (Rule_term.Rel (rel, args))

  let to_rel (T (rel, _, _)) = rel

  let pprint = function
    | T ((name, prims), args, terms) ->
      let open Rule_term in
      Printf.sprintf "%s(%s):(%s) :- %s"
        name
        (Hlist.pprint args)
        (Prim.List.pprint prims)
        (Free_bool_algebra.pprint (Rule_term.pprint name) terms)
end

module Query = struct
  type 'a t = 'a Relation.t * 'a V_with_holes.t

  let pprint (rel, vs) =
    Printf.sprintf "%s(%s)" (fst rel) (V_with_holes.pprint vs)
end

module Db = struct
  module T = struct
    type 'a t =
      | Intro_rel :
        'r Relation.t * ('r Relation.t -> 'a t) -> 'a t
      | Intro_fact :
        'r Fact.t * (unit -> 'a t) -> 'a t
      | Intro_rule :
        ('r1, 'r2) Rule.t * (('r1, 'r2) Rule.t -> 'a t) -> 'a t
      | Perform_query :
        'r Query.t * (unit -> 'a t) -> 'a t
      | Pure : 'a -> 'a t

    let return a = Pure a
    let map = `Define_using_bind
    let rec bind t ~f = match t with
      | Intro_rel (relation, k) ->
          Intro_rel (relation, fun rel -> bind ~f (k rel))
      | Intro_fact (fact, k) ->
          Intro_fact (fact, fun () -> bind ~f (k ()))
      | Intro_rule (rule, k) ->
          Intro_rule (rule, fun rule -> bind ~f (k rule))
      | Perform_query (query, k) ->
          Perform_query (query, fun () -> bind ~f (k ()))
      | Pure x -> f x
  end

  include T
  include Monad.Make(T)

  let intro_rel name typ = Intro_rel ((name, typ), return)

  let intro_fact rel args = Intro_fact (Fact (rel, args), return)

  let (-:) f x = f x

  let intro_rule name typ args alg = Intro_rule (Rule.T ((name, typ), args, Free_bool_algebra.simplify Rule.Rule_term.equal alg), fun rule -> return (Rule.to_rel rule))

  let perform_query name args = Perform_query ((name, args), return)

  let rec pprint t =
    let f = pprint in
    match t with
    | Intro_rel (relation, k) ->
        Relation.pprint relation ^ ".\n" ^ (f (k relation))
    | Intro_fact (fact, k) ->
        Fact.pprint fact ^ ".\n" ^ (f (k ()))
    | Intro_rule (rule, k) ->
        Rule.pprint rule ^ ".\n" ^ (f (k rule))
    | Perform_query (query, k) ->
        "\n?- " ^ Query.pprint query ^ ".\n" ^ (f (k ()))
    | Pure x -> ""

  let eval (t : unit t) : 'a V.t list =
    failwith "TODO"
end

open Db
open Relation
open Fact
open V

let sample : unit Db.t =
  let open Db.Let_syntax in
  let sxs = Prim.List.[Symbol;Symbol] in
  let%bind node = intro_rel "node" Prim.List.[Symbol] in
  let%bind edge = intro_rel "edge" sxs in
  let%bind () = intro_fact node Hlist.[sym "x"] in
  let%bind () = intro_fact edge Hlist.[sym "x"; sym "y"] in
  let%bind () = intro_fact edge Hlist.[sym "y"; sym "z"] in
  let%bind () = intro_fact edge Hlist.[sym "z"; sym "w"] in
  let%bind path =
    intro_rule "path" sxs Hlist.[sym "x";sym "y"] -: (
        let open Rule in
        let path = self in
        let edge = rel edge in

        let open Free_bool_algebra in
        (edge (Hlist.[sym "x"; sym "y"])) || (
          (path Hlist.[sym "x";sym "z"]) && (path Hlist.[sym "z"; sym "y"])
        )
      )
  in
  let%bind reachable =
    intro_rule "reachable" sxs Hlist.[sym "x"; sym "y"] -: (
      let open Rule in
      let path = rel path in

      (* The Free-boolean-algebra simplifies the `&& True` away *)
      let open Free_bool_algebra in
      path Hlist.[sym "x"; sym "y"] && True
    )
  in
  perform_query reachable Hlist.[Some (sym "y"); None]
;;

printf "\n\n%s" (Db.pprint sample)
