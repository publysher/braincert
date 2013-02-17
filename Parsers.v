(**
  In this article I take the first steps in writing a BrainFuck interpreter: 
*)

Require Import List Ascii String.
Require Import Language. 

Module Parser. 


(** * Utilities

*)
Module Parser_Support.

Fixpoint str_list (s: string): list ascii :=
match s with
| EmptyString => nil
| String c s' => c :: str_list s'
end.

End Parser_Support. 
Import Parser_Support. 


(** * Basic Parsers

*)

Definition Parser (T: Type) := list ascii -> option (T * list ascii).

Definition fail {T: Type}: Parser T := fun _ => None.

Definition result {T: Type} (t: T): Parser T := fun inp => Some (t, inp).

Definition item: Parser ascii := fun inp => match inp with
| nil => None
| x :: inp' => Some (x, inp')
end.



(** * Turning the Parser into a Monad *)

Definition bind {T U: Type} (p: Parser T) (f: T -> Parser U): Parser U := 
fun inp => 
  match p inp with
  | None => None
  | Some (t, inp') => f t inp'
  end.

Notation "p >>= f" := (bind p f) (at level 60, right associativity). 

Notation "p >> q" := (p >>= (fun _ => q)) (at level 60, right associativity).

(** * Basic Parser Combinators *)

Definition sat (p: ascii -> bool): Parser ascii := 
  item >>= fun x => 
           if p x then result x else fail. 

Definition char (c: ascii) : Parser ascii := 
  sat (fun c' => 
       if ascii_dec c c' then true else false). 

Definition choice {T: Type} (p q: Parser T): Parser T := 
fun inp => 
  match p inp with
  | None => q inp
  | something => something
  end. 

Notation "p 'or' q" := (choice p q) (at level 60). 

Fixpoint many {T: Type} (maxDepth: nat) (p: Parser T): Parser (list T) := 
  match maxDepth with
  | 0 => fail
  | S maxDepth' =>  (p >>= fun x =>
                       many maxDepth' p >>= fun xs =>
                       result (x :: xs))
                    or result nil 
  end. 

Definition bracket {T U V: Type} (open: Parser U) (p: Parser T) (close: Parser V): Parser T :=
  open >> 
  p >>= fun t => 
  close >> 
  result t.

(** * Parsing BrainFuck *)

Import Language. 
Definition basicParser :=
     (char "+" >> result Inc)
  or (char "-" >> result Dec)
  or (char "<" >> result Left)
  or (char ">" >> result Right)
  or (char "," >> result Input)
  or (char "." >> result Output). 

Fixpoint bfParser (maxDepth: nat): Parser (list command) := 
match maxDepth with
| O => fail
| S n' =>  many n' (  
             basicParser
             or (bracket (char "[") (bfParser n') (char "]") >>= fun t => 
                 result (Loop t))
           )
end.

Definition bf_parse (s: string): option (list command) :=
match bfParser (String.length s) (str_list s) with
| None => None
| Some (t, remainder) => if remainder then Some t else None
end. 

Eval compute in (bf_parse ">+++++++[<+++++>-]"). 
Eval compute in (bf_parse "[[]]]"). 

End Parser. 