Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

Notation var := string.

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Print arith.


Lemma syntax_is_not_semantics:
    Plus (Const 1) (Const 1) <> Const 2.
Proof.
    Locate "<>".
    Print not.
    unfold not.
    (*No way to prove False means the thing on the left shouldn't be provable*)
    intro Heq.
    (*Now need to call Coq's bluff i.e. for every way it would prove Heq, we would prove False*)
    (*Another flavor of destruct called inversion*)
    inversion Heq.
Qed.