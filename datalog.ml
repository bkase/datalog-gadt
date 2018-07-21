open Core

module Hlist = struct
  type _ t =
    | [] : unit t
    | (::) : 'a * 'b t -> ('a -> 'b) t
end

module Prim = struct
  type _ t =
    | Int : int64 t
    | Symbol : string t

  type 'a t0 = 'a t
  module List = struct
    type _ t =
      | [] : unit t
      | (::) : 'a t0 * 'b t -> ('a -> 'b) t
  end
end

module Relation = struct
  type 'a t = string * 'a Prim.List.t
end

module Fact : sig type t end = struct
  type t = ()
end

module Db = struct
  (* rel_env, facts, value *)
  type (_, _, _) t =
    | Intro_rel :
      'a Relation.t * ('a Relation.t -> 'e, 'f, 'b) t -> ('e, 'f, 'b) t
    | Intro_fact :
      ('e, 'a Relation.t * 'a Hlist.t -> 'f, Fact.t) t * ('e, 'a Relation.t * 'a Hlist.t -> 'f, 'b) t -> ('e, 'f, 'a Relation.t * 'a Hlist.t -> 'b) t
    | Fact_here :
      'a Hlist.t -> ('a Relation.t -> 'e, 'a Relation.t * 'a Hlist.t -> 'f, Fact.t) t
    | Fact_there :
      ('e, 'f, 'a) t -> ('b Relation.t -> 'e, 'f, 'a) t
    | Done : ('e, 'f, unit) t
end

open Relation
open Prim.List
let x = Db.(
  Intro_rel (("node", [Symbol]),
    Intro_rel (("edge", [Symbol;Symbol]),
      Intro_fact (
        Fact_there (Fact_here (Hlist.["x"])),
          Intro_fact (
            Fact_here (Hlist.["x";"y"]),
          Done)))))

;;
printf "Hello world\n"
