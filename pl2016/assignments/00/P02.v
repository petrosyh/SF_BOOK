Require Export P01.

(** **** Problem #2: 1 star (factorial) *)
(** Recall the standard factorial function:
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Translate this into Coq. 

    Note that plus and multiplication are already defined in Coq.
    use "+" for plus and "*" for multiplication.
*)

Eval compute in 3 * 5.
Eval compute in 3+5*6.

Fixpoint factorial (n:nat) : nat := 
  GIVEUP.

Example test_factorial1:          (factorial 3) = 6.
exact GIVEUP. Qed.
Example test_factorial2:          (factorial 5) = 10 * 12.
exact GIVEUP. Qed.
(** [] *)
