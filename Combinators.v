(**

Parser combinators are a powerful tool to create full-fledged parsers by combining small
combinators. This module gives a minimal implementation of parser combinators for Coq. 

Parser combinators in Coq can be found all over the internet; this module is different by
providing a large number of examples. 

The library is heavily based on the article "Monadic Parser Combinators" by Hutton and Meijer. 
It is also inspired by the parser implementation in "Software Foundations" by Pierce et al. 
*)

(* begin hide *)
Require Import Ascii String List Arith.
Require Import Utils. 

Import List.ListNotations. 
Import Utils.Notations.

(* end hide *)

(**
In general, a parser is a function that converts a list of tokens, called the input, 
into a different representation, called the output. 
The idea behind parser combinators is that a parser combinator consumes only part of
the input, and returns a part of the output together with the remaining input. 

There are different ways of implementing parser combinators. The combinators in 
"Monadic Parser Combinators" are meant to provide all possible parsing results. The combinators
in this module are more deterministic: at most one parse result is returned. 
*)

(** * The Basic Combinators
Combinators are parameterized over the input and output. The input should be repsresented by 
an abstract type [token], but for now the combinators only work on tokens of type [ascii]; 
the output is represented as the abstract type [T], as in "Monadic Parser Combinators". 

A parser combinator is now defined as something that tries to convert a list of tokens
into a (partial) result and the remaining list of tokens. 
*)

Definition Parser (T: Type) := list ascii -> option (T * list ascii).

(** 
Based on this definition, let's start by defining the basic building blocks. The first
building block is the [fail] combinator, which always fails. 
*)

Definition fail {T: Type}: Parser T := fun _ => None.

Example ex_fail_1: (fail: Parser nat) [["hello"]] = None. 
Proof. reflexivity. Qed. 

(** 
The second building block always has a specific result, without consuming any
input. 
*)

Definition result {T: Type} (t: T): Parser T := fun inp => Some (t, inp).

Example ex_result_1: (result 42) [["The final answer"]]
                     = Some (42, [["The final answer"]]). 
Proof. reflexivity. Qed. 

(**
The final building block consumes a single token from the input and 
returns that token. 
*)

Definition item: Parser ascii := fun inp => match inp with
| nil => None
| x :: inp' => Some (x, inp')
end.

Example ex_item_1: item [["hello"]] = Some("h"%char, [["ello"]]).
Proof. reflexivity. Qed.  

(** * Combining Combinators
These three building blocks are not enough to result in a useful parser. The most important
next step is to define a way to _combine_ those building blocks into bigger blocks. The following
function turns out to be the only function we need. 
*)

Definition bind {T U: Type} (p: Parser T) (f: T -> Parser U): Parser U := 
fun inp => 
  match p inp with
  | None => None
  | Some (t, inp') => f t inp'
  end.

(** 
The intuitive definition of [bind] is that it feeds the output of parser [p] into parser 
[q]. For example, it is now possible to combine the [item] combinator with the [result] combinator
into a simple parser that consumes one item and returns that item. *)

Example ex_bind_1: let combined := bind item (fun x => result x) in
  combined [["hello"]] = Some ("h"%char, [["ello"]]). 
Proof. reflexivity. Qed. 

(** 
This example might be a bit trivial, because it is identical to the [item] combinator itself.
*)

Lemma ex_bind_1_trivial: forall input, item input = (bind item (fun x => result x)) input. 
Proof.
  destruct input; reflexivity. 
Qed.

(** 
But luckily, the bind operator can do more. For example, the following combinator
consumes from the input and outputs 42. 
*)

Example ex_bind_2: let combined := bind item (fun _ => result 42) in
  combined [["hello"]] = Some (42, [["ello"]]). 
Proof. reflexivity. Qed. 

(**
If you know monads, the [bind] function should look familiar; its name is actually derived
from the typical monad definition. Similarly, the [result] function is identical to the
monadic [return] function. However, Coq already has a [return]. 

Given this familiarity, it's time to introduce some well-known notations. 
*)

Notation "p >>= f" := (bind p f) (at level 60, right associativity). 

Notation "p >> q" := (p >>= (fun _ => q)) (at level 60, right associativity).

Example ex_notation_1: let combined := item >> result 42 in
  combined [["hello"]] = Some (42, [["ello"]]). 
Proof. reflexivity. Qed. 

Example ex_notation_2: let combined := item >> (fail: Parser ascii) >> item in 
  combined [["hello"]] = None.
Proof. reflexivity. Qed. 

(**
And of course, the proof that the combination of [Parser T], [bind] and [result] 
forms a Monad. 
*)

Lemma parser_monad_left_id: forall (T U: Type) (t: T) (f: T -> Parser U), 
  (result t >>= f) = f t.
Proof. reflexivity.  Qed.

Lemma parser_monad_right_id: forall (T: Type) (m: Parser T) (inp: list ascii), 
  (m >>= result) inp = m inp.
Proof. 
  intros T m inp. 
  compute. 
  destruct (m inp) as [p | None]. 
  + destruct p; reflexivity. 
  + reflexivity.
Qed.

Lemma parser_monad_assoc: forall (T U V: Type) p (f: T -> Parser U) (g: U -> Parser V) (inp: list ascii), 
  ((p >>= f) >>= g) inp  = (p >>= (fun x => f x >>= g)) inp.
Proof.
  intros T U V p f g inp. 
  compute.
  destruct (p inp) as [s | None]. 
  + destruct s; destruct (f t l) as [s' | None]. 
    * destruct s'; reflexivity.
    * reflexivity.   
  + reflexivity. 
Qed. 

(** 
Note that [parser_monad_right_id] and [parser_monad_assoc] are not completely right; they only prove
that the functions behave the same on any input. In order to proof equality of the functions, I would
have to add the extensional equality axiom ([forall f g x, f x = g x -> f = g]), effectively resulting
in the same proof. 
*)


(** * Advanced Combinators 
Armed with the bind operator, it is now possible to create more interesting
parsers. The first one is the [sat] parser, which consumes a token from
the input if it satisfies a certain predicate.
*)

Definition sat (p: ascii -> bool): Parser ascii := 
  item >>= fun x => 
           if p x then result x else fail. 

(**
A simple example is the [char] parser, which consumes a specific character from
the input.
*)

Definition char (c: ascii) : Parser ascii := 
  sat (fun c' => 
       if ascii_dec c c' then true else false). 

Example ex_char_1: char "h" [["hello"]] = Some("h"%char, [["ello"]]).
Proof. reflexivity. Qed. 

Example ex_char_2: char "x" [["hello"]] = None. 
Proof. reflexivity. Qed. 


(** 
Other useful examples are [digit], [lower] and [upper].
*)
Definition digit: Parser ascii :=
  sat (fun c =>
       andb ("0" <= c) (c <= "9")). 

Example ex_digit_1: digit [["1234"]] = Some ("1"%char, [["234"]]).
Proof. reflexivity. Qed.  


(**
A more complex example is the [choice] parser, which works over two parser [p] and [q]. 
It first tries to parse using [p]. If that fails, it will try to use the 
parser [q]. 
*)

Definition choice {T: Type} (p q: Parser T): Parser T := 
fun inp => 
  match p inp with
  | None => q inp
  | something => something
  end. 


Example ex_choice_1: choice (char "h") (char "b") (str_list "hello") = 
                     Some ("h"%char, str_list "ello").
Proof. reflexivity. Qed. 

Example ex_choice_2: choice (char "h") (char "b") (str_list "bye") =
                     Some ("b"%char, str_list "ye").
Proof. reflexivity. Qed. 

(** 
In fact, the choice parser is so common that it deserves its own notation.
*)

Notation "p 'or' q" := (choice p q) (at level 60). 

(**
Note that [or] always tries to match the first
possible parser, which can have surprising results. 
*)

Example ex_choice_3: let parser := (char "q") or (char "q" >> char "q") in  
  parser (str_list "qq") = Some ("q"%char, str_list "q").
Proof. reflexivity. Qed.

(** **The [many] combinator

The most useful combinator of all is the [many] combinator. This combinator
repeats another parser for as long as possible. In most functional languages, 
the [many] combinator can easily be defined; in Coq we'd like to do something like this:

<<<
Definition many {T: Type} (p: Parser T): Parser (list T) := 
  (p >>= fun x =>
   many p >>= fun xs =>
   result (x :: xs))
  or
   result nil.
>>>

This definition is not accepted by Coq, because [Definition]s cannot refer to themselves. 
[Fixpoint] does not help us either:

<<<
Fixpoint many {T: Type} (p: Parser T): Parser (list T) := 
  (p >>= fun x =>
   many p >>= fun xs =>
   result (x :: xs))
  or
   result nil.
>>>

This fails because [Fixpoint] requires a decreasing argument. But rewriting the [Fixpoint]
by introducing a decreasing argument doesn't work either:

<<<
Fixpoint many {T: Type} (p: Parser T) (inp: list ascii): option(T, list ascii) :=
match inp with
| []  => None
| lst => ((p >>= fun x =>
           many p >>= fun xs ==>
           result (x :: xs))
          or
           result nil) inp 
end.
>>>

The problem is that in this definition, [inp] is not decreasing at all.

This problem should not be too surprising. After all, Coq can only work because it requires
every function to terminate. And if the previous solution was allowed, it would become possible
to create parsers like [many (result 42)] \u2013\u00a0a parser which produces an endless stream of 42s without
ever consuming the input.

The usual way to fix this in Coq is to introduce an artificial guard condition: 
*)

Fixpoint many_guarded {T: Type} (maxDepth: nat) (p: Parser T): Parser (list T) := 
  match maxDepth with
  | 0 => result nil
  | S maxDepth' =>  (p >>= fun x =>
                       many_guarded maxDepth' p >>= fun xs =>
                       result (x :: xs))
                    or result nil 
  end. 

Example ex_many_1: (many_guarded 3 (result 42))[["hello"]] = Some([42; 42; 42], [["hello"]]).
Proof. reflexivity. Qed. 

(** This actually works, because the guard guarantees that even infinite recursive [many] constructs
eventually terminate. But it leaves a bitter taste \u2013\u00a0using the guard to define a new parser feels 
unnatural. It also begs the question: what guard is good enough? 

As it turns out, there is an easy answer which is related to the idea of _input consumption_. When we write
a parser like [many p], we have the implicit expectation that this parser consumes input until [p] fails. In
other words, parser like [many (result 42)] don't have a practical use. 

But if the expression [many p] is only useful as long as [p] consumes input, than the number of steps can 
never be larger than the length of the input. 

[length input] turns out to be the perfect guard. 
*)

Definition many {T: Type} (p: Parser T): Parser (list T) := fun input =>
  many_guarded (length input) p input. 

