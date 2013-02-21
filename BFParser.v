(**
  In this article I take the first steps in writing a BrainFuck interpreter: 
*)

Require Import List Ascii String.
Require Import Language Combinators Utils. 

Import List.ListNotations. 
Import Utils.Notations. 

Definition bracket {T U V: Type} (open: Parser U) (p: Parser T) (close: Parser V): Parser T :=
  open >> 
  p >>= fun t => 
  close >> 
  result t.

(** * Parsing BrainFuck *)

Definition basic_parser :=
     (char "+" >> result Inc)
  or (char "-" >> result Dec)
  or (char "<" >> result Left)
  or (char ">" >> result Right)
  or (char "," >> result Input)
  or (char "." >> result Output). 

Fixpoint bf_parser (maxDepth: nat): Parser (list command) := 
match maxDepth with
| O => fail
| S n' =>  many (  
             basic_parser
             or (bracket (char "[") (bf_parser n') (char "]") >>= fun t => 
                 result (Loop t))
           )
end.

Definition bf_parse (s: string): option (list command) :=
match bf_parser (String.length s) [[ s ]] with
| None => None
| Some (t, remainder) => if remainder then Some t else None
end.

Eval compute in (bf_parse ">+++++++[<+++++>-]"). 
Eval compute in (bf_parse "[[]]]"). 

Example ex_bf_parse_1: bf_parse ">+++++++[<+++++>-]" = Some
         [Right; Inc; Inc; Inc; Inc; Inc; Inc; Inc;
         Loop [Left; Inc; Inc; Inc; Inc; Inc; Right; Dec] ].
Proof. reflexivity. Qed. 

Example ex_bf_parse_2: bf_parse "[[]]]" = None. 
Proof. reflexivity. Qed.  
