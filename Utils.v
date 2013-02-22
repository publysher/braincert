(**
A number of small utility functions and proofs. 
*)

(* begin hide *)
Require Import List String Ascii Arith.
Import List.ListNotations. 
(* end hide *)

(** 
[str_list] converts a string to a list of ascii characters. 
*)

Fixpoint str_list (s: string): list ascii :=
match s with
| EmptyString => nil
| String c s' => c :: str_list s'
end.

Example ex_str_list_1: str_list "hello" = ["h"; "e"; "l"; "l"; "o"]%char.
Proof. reflexivity. Qed.  


(**
 Some useful notations to import.
*)
Module Notations.

(** Less than or equal on ascii *)
Notation "c1 <= c2" := (leb (nat_of_ascii c1) (nat_of_ascii c2)). 

(** Converting a string to a list of characters *)
Notation "[[ s ]]" := (str_list s). 

End Notations.