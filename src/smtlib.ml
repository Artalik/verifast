(* This module implements an SMTLib interface for the fragment of the
   SMTlib language used by Verifast.

   Pretty-printing is done using the standard Format module.

   We use modules and functors to enforce abstraction barriers. *)

let print_string o = Format.fprintf o "%s"

(* Very general pretty-printing function for lists *)
let rec print_list
          (print : Format.formatter -> 'a -> unit)
          (sep : 'b)
          (print_sep : Format.formatter -> 'b -> unit)
          (o : Format.formatter) : 'a list -> unit = function
  | [] -> ()
  | [a] -> print o a
  | a :: l ->
     Format.fprintf o "%a%a%a"
        print a
        print_sep sep
        (print_list print sep print_sep) l

(* Print a list with a string separator *)
let print_list_ssep print sep =
  print_list print sep print_string

(* Print a list of items separated by breakable spaces *)
let print_list_space print =
  print_list print ("@ " : (unit, Format.formatter, unit) format) Format.fprintf

(* Print a list of items separated by newlines *)
let print_list_newline print =
  print_list print ("@\n" : (unit, Format.formatter, unit) format) Format.fprintf

module type PRINTABLE = sig
  type t
  val print : Format.formatter -> t -> unit
  val to_string : t -> string
end

module type SORT = sig
  include PRINTABLE

  val bool : t
  val int : t
  val real : t
  val inductive : t
end

module Sort : SORT = struct
  type t =
    | Bool
    | Int
    | Real
    | Inductive

  let bool = Bool
  let int = Int
  let real = Real
  let inductive = Inductive
  let to_string = function
    | Bool -> "Bool"
    | Int -> "Int"
    | Real -> "Real"
    | Inductive -> "Inductive"

  let print o sort = print_string o (to_string sort)
end

type sort = Sort.t
let bool = Sort.bool
let int = Sort.int
let real = Sort.real
let inductive = Sort.inductive

module type SYMBOL = sig
  include PRINTABLE
  type sort
  (* [fresh name domain range] returns a symbol of domain [domain] and
     of range [range]. The name of the symbol is [name] if this name
     is free; otherwise, freshness is ensured by appending an integer
     at the end of [name]. *)
  val fresh : string -> sort list -> sort -> t
  (* We treat equality and conditional specially because they use
     implicit polymorphism: for each sort [s], [eq s] is a symbol
     named "=" of domain [[s; s]] and range [bool] and [ite s] is a
     symbol named "ite" of domain [[bool; s; s]] and range [s]. *)
  val eq : sort -> t
  val ite : sort -> t
  val get_domain : t -> sort list
  val get_range : t -> sort
end

module Symbol (S : SORT) : SYMBOL with type sort = S.t = struct
  type sort = S.t
  type t = string * sort list * sort

  (* This list of reserved names comes from the SMTlib documentation
     to which all names occurring in Verifast standard lib (especially
     the list libraries) conflicting with CVC4 theory of sets have
     been added. It is highly probable that some other CVC4 builtins
     are missing. *)
  let all_names =
    ref
      [
        "Bool"; "Int"; "Real"; "Inductive";
        "par"; "NUMERAL"; "DECIMAL"; "STRING"; "_"; "!"; "as"; "let";
        "forall"; "exists"; "assert"; "assert-not"; "check-sat";
        "declare-const"; "declare-fun"; "declare-sort"; "define-const";
        "define-fun"; "define-fun-rec"; "define-sort"; "exit"; "get-assertions";
        "get-assignment"; "get-info"; "get-option"; "get-proof"; "get-unsat-core";
        "get-value"; "pop"; "push"; "set-info"; "set-logic"; "set-option";
        "distinct"; "map"; "abs"; "Set"; "union"; "intersection"; "setminus";
        "member"; "subset"; "emptyset"; "singleton"; "card"; "insert"; "complement";
        "univset"; "extract";
      ]

  (* We escape "@" using "_" as escape symbol. In SMTLib, names
     starting with "@" are reserved and should not appear in the input
     problems. *)
  let escape_char = function
    | '@' -> "_@"
    | c -> String.make 1 c

  let escape_string s =
    let b = Buffer.create (2 * String.length s) in
    String.iter (fun c -> Buffer.add_string b (escape_char c)) s;
    Buffer.contents b

  (* This implementation of freshness is very inefficient with respect
     to both memory and time.  If efficiency is a problem, we sould
     probably switch to a better datatype such as an hashtable mapping
     each symbol name s to the smallest index i such that s followed
     by i is still a free name. *)
  let fresh_name s =
    let s = escape_string s in
    let suffix = ref 0 in
    let new_name =
      if List.mem s !all_names then
        begin
          while List.mem (s ^ string_of_int !suffix) !all_names do
            incr suffix;
          done;
          (s ^ string_of_int !suffix)
        end
          else s
    in
    all_names := new_name :: !all_names;
    new_name

  let fresh s domain range = (fresh_name s, domain, range)

  let eq =
    let name = fresh_name "=" in
    fun sort -> (name, [sort; sort], S.bool)
  let ite =
    let name = fresh_name "ite" in
    fun sort -> (name, [S.bool; sort; sort], sort)

  let to_string (name, _, _) = name
  let get_domain (_, domain, _) = domain
  let get_range (_, _, range) = range

  let print o f = print_string o (to_string f)
end

module Sym : SYMBOL with type sort = Sort.t = Symbol(Sort)

type symbol = Sym.t
let fresh_symbol = Sym.fresh
let get_domain = Sym.get_domain
let get_range = Sym.get_range

module type VAR = sig
  include PRINTABLE
  type sort

  val mk : int -> sort -> t
  val get_type : t -> sort
  val to_string_with_type : t -> string
  val print_with_type : Format.formatter -> t -> unit
end

module Variable (S : SORT) (Sy : SYMBOL with type sort = S.t)
       : VAR with type sort = S.t = struct
  type sort = S.t
  type t = string * sort

  let all_vars : string list ref = ref []
  let mk i sort =
    try (List.nth !all_vars i, sort)
    with
    | Failure _ ->
       let f = Sy.fresh "var" [] sort in
       let name = Sy.to_string f in
       all_vars := !all_vars @ [name];
       (name, sort)

  let get_type (_, sort) = sort

  let to_string (name, _) = name
  let to_string_with_type (name, sort) =
    Printf.sprintf "(%s %s)" name (S.to_string sort)
  let print o var = print_string o (to_string var)
  let print_with_type o (name, sort) =
    Format.fprintf o "@[<3>(%a@ %a)@]"
       print_string name
       S.print sort
end

module Var = Variable(Sort)(Sym)

type variable = Var.t
let mk_var = Var.mk
let var_get_sort = Var.get_type

module type TERM = sig
  include PRINTABLE
  type var
  type sort
  type symbol

  val int : Big_int.big_int -> t
  val real : Num.num -> t
  val var : var -> t
  (* /!\ We do no sort nor arity checking! *)
  val app : symbol -> t list -> t
  val forall : var list -> t list -> t -> t

  val get_type : t -> sort
end

module Term (S : SORT)
            (Sy : SYMBOL with type sort = S.t)
            (V : VAR with type sort = S.t)
       : TERM with
         type sort = S.t and
         type symbol = Sy.t and
         type var = V.t = struct
  type sort = S.t
  type symbol = Sy.t
  type var = V.t
  type t =
    | Int of Big_int.big_int
    | Real of Num.num
    | Var of var
    | App of symbol * t list
    | Forall of var list * t list * t

  let get_type = function
    | Int _ -> S.int
    | Real _ -> S.real
    | Var v -> V.get_type v
    | App (f, _) -> Sy.get_range f
    | Forall _ -> S.bool

  let int i = Int i
  let real r = Real r
  let var v = Var v
  let app f l = App (f, l)
  let forall vars patterns t = Forall (vars, patterns, t)

  let rec print o = function
    | Int i ->
       if Big_int.sign_big_int i >= 0 then
         Format.fprintf o "%s" (Big_int.string_of_big_int i)
       else
         Format.fprintf o "@[<3>(-@ %s)@]"
          (Big_int.string_of_big_int (Big_int.abs_big_int i))
    | Real r ->
       Format.fprintf o "%s" (Num.string_of_num r)
    | Var v -> V.print o v
    | App (head, []) -> Sy.print o head
    | App (head, l) ->
       Format.fprintf o "@[<3>(%a@ %a)@]"
          Sy.print head
          (print_list_space print) l
    | Forall (vars, [], t) ->
       Format.fprintf o "@[<3>(@[forall@ @[<3>(%a)@]@]@ %a)@]"
          (print_list_space V.print_with_type) vars
          print t
    | Forall (vars, patterns, t) ->
       Format.fprintf o "@[<3>(@[forall@ @[<3>(%a)@]@]@ @[<3>(!@ %a@ @[:pattern@ @[<3>(%a)@]@])@])@]"
          (print_list_space V.print_with_type) vars
          print t
          (print_list_space print) patterns

  let rec to_string = function
    | Int i ->
       if Big_int.sign_big_int i >= 0 then
         Printf.sprintf "%s" (Big_int.string_of_big_int i)
       else
         Printf.sprintf "(- %s)"
          (Big_int.string_of_big_int (Big_int.abs_big_int i))
    | Real r -> Num.string_of_num r
    | Var v -> V.to_string v
    | App (head, []) -> Sy.to_string head
    | App (head, l) ->
       Printf.sprintf "(%s %s)"
          (Sy.to_string head)
          (String.concat " " (List.map to_string l))
    | Forall (vars, [], t) ->
       Printf.sprintf "(forall (%s) %s)"
          (String.concat " " (List.map V.to_string_with_type vars))
          (to_string t)
    | Forall (vars, patterns, t) ->
       Printf.sprintf "(forall (%s) (! %s :pattern (%s)))"
           (String.concat " " (List.map V.to_string_with_type vars))
           (to_string t)
           (String.concat " " (List.map to_string patterns))
end

module T = Term(Sort)(Sym)(Var)

type term = T.t
let app = T.app
(* Constant application *)
let capp f = app f []
(* Unary application *)
let uapp f t = app f [t]
(* Binary application *)
let bapp f t1 t2 = app f [t1; t2]
(* Ternary application *)
let tapp f t1 t2 t3 = app f [t1; t2; t3]
let var v = T.var v

let ttrue = capp (Sym.fresh "true" [] Sort.bool)
let tfalse = capp (Sym.fresh "false" [] Sort.bool)
let tnot = uapp (Sym.fresh "not" [Sort.bool] Sort.bool)
let tand = bapp (Sym.fresh "and" [Sort.bool; Sort.bool] Sort.bool)
let tor = bapp (Sym.fresh "or" [Sort.bool; Sort.bool] Sort.bool)
let tite t1 t2 t3 = tapp (Sym.ite (T.get_type t2)) t1 t2 t3
let timp = bapp (Sym.fresh "=>" [Sort.bool; Sort.bool] Sort.bool)
let eq t1 t2 = bapp (Sym.eq (T.get_type t1)) t1 t2
let iff = eq
let forall = T.forall
let add = bapp (Sym.fresh "+" [Sort.int; Sort.int] Sort.int)
let sub = bapp (Sym.fresh "-" [Sort.int; Sort.int] Sort.int)
let mul = bapp (Sym.fresh "*" [Sort.int; Sort.int] Sort.int)
let div = bapp (Sym.fresh "/" [Sort.int; Sort.int] Sort.int)
let tmod = bapp (Sym.fresh "mod" [Sort.int; Sort.int] Sort.int)
let lt = bapp (Sym.fresh "<" [Sort.int; Sort.int] Sort.bool)
let le = bapp (Sym.fresh "<=" [Sort.int; Sort.int] Sort.bool)
let radd = bapp (Sym.fresh "+." [Sort.int; Sort.int] Sort.int)
let rsub = bapp (Sym.fresh "-." [Sort.int; Sort.int] Sort.int)
let rmul = bapp (Sym.fresh "*." [Sort.int; Sort.int] Sort.int)
let rlt = bapp (Sym.fresh "<." [Sort.int; Sort.int] Sort.bool)
let rle = bapp (Sym.fresh "<=." [Sort.int; Sort.int] Sort.bool)

let get_type = T.get_type
let print_term = T.print

module type STATEMENT = sig
  include PRINTABLE
  type symbol
  type sort
  type term

  val set_logic : string -> t
  val declare_fun : symbol -> t
  val declare_sort : sort -> t
  val sassert : term -> t
  val push : t
  val pop : int -> t
  val comment : string -> t
  val check_sat : t
end

module Statement
         (S : SORT)
         (Sy : SYMBOL with type sort = S.t)
         (V : VAR with type sort = S.t)
         (T : TERM with type sort = S.t and type symbol = Sy.t and type var = V.t)
       : STATEMENT with type sort = S.t and type symbol = Sy.t and type term = T.t
  = struct

  type sort = S.t
  type symbol = Sy.t
  type var = V.t
  type term = T.t

  type t =
    | SetLogic of string
    | SortDecl of sort
    | FunDecl of symbol
    | Assert of term
    | Push
    | Pop of int
    | Comment of string
    | CheckSat

  let set_logic s = SetLogic s
  let declare_sort s = SortDecl s
  let declare_fun f = FunDecl f
  let sassert t = Assert t
  let push = Push
  let pop i =
    if i <= 0 then raise (Invalid_argument "Smtlib.Statement.pop")
    else Pop i
  let comment s = Comment s
  let check_sat = CheckSat

  let print o : t -> unit = function
    | SetLogic s ->
       Format.fprintf o "@[<3>(set-logic %s)@]" s
    | SortDecl s ->
       Format.fprintf o "@[<3>(declare-sort@ %a@ 0)@]" S.print s
    | FunDecl f ->
       Format.fprintf o "@[<3>(declare-fun@ %a@ @[<3>(%a)@]@ %a)@]"
          Sy.print f
          (print_list_space S.print) (Sy.get_domain f)
          S.print (Sy.get_range f)
    | Assert t ->
       Format.fprintf o "@[<3>(assert@ %a)@]"
          T.print t
    | Push ->
       print_string o "(push)"
    | Pop i ->
       Format.fprintf o "@[<3>(pop@ %d)@]" i
    | Comment s ->
       Format.fprintf o "; %s" s
    | CheckSat -> print_string o "(check-sat)"

  let to_string = function
    | SetLogic s ->
       Printf.sprintf "(set-logic %s)" s
    | SortDecl s ->
       Printf.sprintf "(declare-sort %s)" (S.to_string s)
    | FunDecl f ->
       Printf.sprintf "(declare-fun %s (%s) %s)"
          (Sy.to_string f)
          (String.concat " " (List.map S.to_string (Sy.get_domain f)))
          (S.to_string (Sy.get_range f))
    | Assert t ->
       Printf.sprintf "(assert %s)"
          (T.to_string t)
    | Push -> "(push)"
    | Pop i ->
       Printf.sprintf "(pop %d)" i
    | Comment s ->
       Printf.sprintf "; %s\n" s
    | CheckSat -> "(check-sat)"
end

module St = Statement(Sort)(Sym)(Var)(T)

type statement = St.t
let print_statement = St.print
let set_logic s = St.set_logic s
let declare_fun = St.declare_fun
let declare_sort = St.declare_sort
let sassert t = St.sassert t
let push = St.push
let pop = St.pop
let comment = St.comment
let check_sat = St.check_sat