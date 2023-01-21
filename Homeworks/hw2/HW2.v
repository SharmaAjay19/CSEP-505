(*

  _   _    ___    __  __   _____  __        __   ___    ____    _  __    ____
 | | | |  / _ \  |  \/  | | ____| \ \      / /  / _ \  |  _ \  | |/ /   |___ \
 | |_| | | | | | | |\/| | |  _|    \ \ /\ / /  | | | | | |_) | | ' /      __) |
 |  _  | | |_| | | |  | | | |___    \ V  V /   | |_| | |  _ <  | . \     / __/
 |_| |_|  \___/  |_|  |_| |_____|    \_/\_/     \___/  |_| \_\ |_|\_\   |_____|


Howdy folks! In this homework assignment we'll explore more Coq programming
and proving and get some practice with interpreters.

There are 21 problems worth a total of 120 core points and
30 challenge points.

*)


Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

(*
               ____                  _     _                     _
              / ___|    ___    ___  | |_  (_)   ___    _ __     / |
              \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    | |
               ___) | |  __/ | (__  | |_  | | | (_) | | | | |   | |
              |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_|

                          SECTION 1 : More Coq Practice
*)

(*
 * In this part of the homework, we get some practice with lists and other
 * data structures.
 *
 * Step through this file with VSCode (or another IDE for Coq), and complete the
 * problems. Search for "PROBLEM" to be sure you find them all---not all
 * problems correspond to Coq code!
 *
 * Throughout, we include the approximate lines of code (LOC) or number of
 * tactics for each of our solutions to these problems.  These are rough
 * guidelines to help you figure out if you are getting off track.
 *
 * There is no penalty for writing a shorter or longer solution! However, if
 * you find yourself writing a much longer solution, you might save yourself
 * some time by taking a step back and seeing if you can find a simpler way.
 *
 *)

(* --- More arithmetic --- *)

(* This module creates a namespace where we can travel back in time to
 * Homework 1. Later in this homework we will be using the Coq standard library
 * version of nat, so we hide our own definitions in this namespace so we can
 * close it later.
 *)
Module Homework1_TimeTravel. (* get in the DeLorean *)
Set Implicit Arguments.

(*
 * Here are some definitions again from Homework 1.
 *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint add (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => S (add m1 n2)
  end.

(*
 * PROBLEM 1 [0 points, ~4 tactics]
 *
 * You'll need this, which you proved in Homework 1. Feel free to copy/paste
 * your solution.
 *)
Lemma add_n_S :
  forall n1 n2,
    add n1 (S n2) = S (add n1 n2).
Proof.
induction n1 as [| p IHp]; intros; simpl.
- reflexivity.
- rewrite IHp. reflexivity.
Qed. (* Change to Qed when done *)

(* We can define multiplication recursively as repeated addition. *)

Fixpoint mult (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => O
  | S m1 => add n2 (mult m1 n2)
  end.

(*
 * PROBLEM 2 [8 points, ~35 tactics]
 *
 * Prove that multiplication is commutative, as stated by the lemma below.
 *
 * Hint: Proceed by induction.
 *
 * Hint: Don't use more than one induction inside a single proof.  Instead,
 * figure out lemmas that might be useful, and then prove those separately
 * (by induction, probably). See the style guide for more information.
 *
 * Hint: It might be useful to review all the lemmas about `add` in Homework 1.
 * Feel free to copy them over if you need to use them. You might need to
 * state and prove some analogous lemmas about `mult`.
 *
 * Hint: In order to prove your helpers about `mult`, you might need 1 or 2
 * additional facts about `add`.  Try to keep these simple, based on facts
 * you know from math, and prove them by induction.
 *)

 Lemma add_n_O :
  forall n,
  add n O = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
  Qed.

Lemma mult_n_O :
 forall n,
   mult n O = O.
Proof.
 induction n; auto.
Qed.

Lemma add_comm :
  forall n1 n2,
    add n1 n2 = add n2 n1.
Proof.
  induction n1.
  intros.
  - simpl. rewrite -> add_n_O. reflexivity.
  - simpl. intro n2. symmetry. rewrite add_n_S.
    rewrite IHn1. auto.
Qed.

Lemma add_assoc :
  forall n1 n2 n3,
    add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
  intros.
  induction n1.
  - simpl. reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma mult_n_Sm : 
  forall n m : nat,
    mult n (S m) =  add n (mult n m).
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. f_equal.
    rewrite -> add_assoc.
    replace (add m n) with (add n m) by apply add_comm.
    rewrite <- add_assoc.
    reflexivity.
Qed.


Lemma mult_comm :
  forall n m : nat,
    mult n m = mult m n.
Proof.
  induction n; simpl; intros.
  - symmetry. apply mult_n_O.
  - rewrite IHn. rewrite mult_n_Sm. reflexivity. 
Qed. 


Lemma add_swap:
  forall n1 n2 n3,
    add n1 (add n2 n3) = add n2 (add n1 n3).
Proof.
  intros.
  induction n1 as [| p IHp].
  - simpl. reflexivity.
  - simpl. rewrite IHp. rewrite <- add_n_S. reflexivity.
Qed.

Lemma mult_distributive:
  forall n1 n2 n3,
    mult (add n1 n2) n3 = add (mult n1 n3) (mult n2 n3).
Proof.
  intros.
  induction n1 as [| m1 IHm1].
  - simpl. reflexivity.
  - simpl. rewrite <- add_assoc. rewrite IHm1. reflexivity.
Qed.
(*
 * PROBLEM 3 [10 points, ~25 tactics]
 *
 * State and prove that the `mult` function is associative.
 *
 * Hint: You'll probably need ~2 more lemmas about mult and/or add.
 *)
(* YOUR LEMMA STATEMENT AND PROOF HERE *)
Lemma mult_assoc : 
  forall n1 n2 n3,
    mult n1 (mult n2 n3) = mult (mult n1 n2) n3.
Proof.
  intros.
  induction n1 as [| p IHp].
  - simpl. reflexivity.
  - simpl. rewrite IHp. rewrite <- mult_distributive. reflexivity.
Qed.

(* Here's the definition of `le` from lecture (and the standard library). *)
Inductive le (n : nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m, le n m -> le n (S m).

(*
 * PROBLEM 4 [10 points, ~9 tactics]
 *
 * State and prove the following:
 * If a <= b then a + c <= b + c
 *
 * Hint: Proceed by induction.
 *)
Lemma a_le_b_add_c_le_b_add_c : 
  forall a b c: nat,
    le a b -> le (add a c) (add b c).
  Proof.
    intros.
    induction H.
    - simpl. apply le_n.
    - simpl. apply le_S. assumption.
Qed.

End Homework1_TimeTravel. (* return to the present *)

(*
 * Now that you've seen how nat, add, and mult are defined under the hood,
 * from now on we'll use the versions in Coq's standard library. These come
 * with nice notations like `1 + 3 * 4`, and with lots of free lemmas.
 *
 * There are also some useful tactics for working with arithmetic.
 *
 * Here are some automated proofs that the Coq standard library versions
 * of add and mult are commutative. (These lemmas are also in the standard
 * library, but we prove them from scratch just to demonstrate the tactics.)
 *)

Lemma add_comm_again :
  forall a b, a + b = b + a.
Proof.
  intros.
  lia.
Qed.

Lemma mult_comm_again :
  forall a b, a * b = b * a.
Proof.
  intros.
  ring.
Qed.

(*
 * PROBLEM 5 [4 points, ~5 tactics]
 *
 * Prove this simple fact about and.
 *
 * Hint: Review tactics that are useful for taking apart hypotheses.
 *
 * Hint: Review tactics that are useful for decomposing goals.
 *
 * Hint: Our solution uses little automation. If you feel like it, you can solve
 * it with ~1 tactic as well, using automation.
 *)
Lemma and_comm :
  forall (A B : Prop),
    A /\ B ->
    B /\ A.
Proof.
  intros.
  destruct H as [Ha Hb].
  split. (* works because we're proving a conjunction.*)
  - assumption. 
  - assumption. 
Qed. 

(*
 * PROBLEM 6 [4 points, ~7 tactics]
 *
 * Prove this simple fact about or.
 *
 * Hint: Review tactics that are useful for taking apart hypotheses.
 *
 * Hint: Review tactics that are useful for decomposing goals.
 *
 * Hint: Our solution uses little automation. If you feel like it, you can solve
 * it with ~1 tactic as well, using automation.
 *)
Lemma or_comm :
  forall (A B : Prop),
    A \/ B ->
    B \/ A.
Proof.
  intros.
  destruct H as [Ha | Hb].
  - right. exact Ha. (* can't split here because not a conjunction - have to extract each side *)
  - left. exact Hb.
Qed.

(* Here is an inductive definition of evenness for natural numbers. *)
Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).

(*
 * There are two constructors that can prove even. 0 is even. And a number of
 * the form S (S n) is even if n is even.
 *)

(*
 * PROBLEM 7 [9 points, ~3 sentences]
 *
 * Write a comment answering the following questions.
 *
 * (a) If n is a nat in Coq, how many constructors of the type nat (O or S) is
 *     it built with? How many of those are S constructors and how many are O?
 *
 * (b) If n is a nat in Coq, and pf is a proof of even n, how many constructors
 *     of the proposition even is pf built with? How many are even_O and how
 *     many are even_SS?
 *
 * (c) If n is a nat in Coq, and n is odd, explain intuitively why your answer
 *     to part (b) implies that there is no proof of "even n".
 *
 * Hint: Your answer to part (a) should be three quantities: how many
 * constructors total, how many are O, and how many are S? Each quantity should
 * be expressed in terms of n. For example, one (wrong) answer would be "There
 * are n / 3 + 7 constructors total, n / 3 are O, and 7 are S."
 *
 * Hint: Your answer to part (b) should be of a similar "shape" to part (a):
 * three quantities expressed in terms of n.
 *)
(*
 * (a) Each nat is built with n + 1 constructors, where n is the number of S () and + 1 O constuctor.
 * (b) Each even n is built with n/2 even_SS constructors and one even_O constructor.
 * (c) There's isn't one! The construcors described in #2 are predicated on the recursive nature of even numbers.
       As there isn't a constructor for False in Coq, so there is no proof of even n if n is odd.
 *)

(* Here is a function that returns twice its argument. *)
Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S m => S (S (double m))
  end.

(*
 * PROBLEM 8 [4 points, ~5 tactics]
 *
 * Prove that double always returns an even number.
 *
 * Hint: Proceed by induction.
 *)
Lemma double_even :
  forall n,
    even (double n).
Proof.
  intros.
  induction n.
  simpl.
  - exact even_O.
  - simpl. apply even_SS. assumption. 
Qed.

(*
 * PROBLEM 9 [4 points, ~2 sentences]
 *
 * Consider the following lemma, which says that every even number is the output
 * of double on some input.
 *
 * Attempt to prove this lemma by induction on n. No need to turn in your
 * partial proof.
 *
 * Explain in a comment where you get stuck.
 *)

Lemma even_double :
  forall n,
    even n ->
    exists k,
      n = double k.
Proof.
  induction n.
  - intros. exists 0. reflexivity.
  - intros. destruct IHn as [k Hk]. 
    contradict H. exfalso. (* I could have stopped before the destruct, but going this deep proves that the approach truly is broken,
                              because the first goal is "False" and the only element above the line is "n: nat" *) 
Abort.
(* We don't know enough about the computation of even n, or double k so the proof breaks down almost immediately. Immediately after
proving the base case, n = 0, the proof assistant poses us with even S( n ) which is, of course, false. But we don't have enough
information to demonstrate that. Instead, if we were to induct on the derivation of even n we can prove that, for all cases
where n is even, the implication holds. *)

(*
 * PROBLEM 10 [5 points, ~9 tactics]
 *
 * Now prove the lemma by induction on the derivation of even n.
 *)
Lemma even_double :
  forall n,
    even n ->
    exists k,
      n = double k.
Proof.
  intros.
  induction H.
  - exists O. reflexivity.
  - destruct IHeven as [d1 d2].
    + exists (S d1). simpl in *. lia. 
Qed.

(*
 * PROBLEM 11 [5 points, ~6 tactics]
 *
 * Prove that the sum of two even numbers is even.
 *
 * Hint: What should you induct on?
 *)
Lemma plus_even :
  forall x y,
    even x ->
    even y ->
    even (x + y).
Proof.
  intros. induction H.
  - simpl. assumption.
  - simpl. constructor. assumption.  
Qed.

(*
 * PROBLEM 12 [5 points, ~4 tactics]
 *
 * Prove that 3 is not even.
 *
 * Hint: No need for induction. "Call Coq's bluff".
 *)
Lemma three_not_even :
  even 3 -> False.
Proof.
  intro Ht.
  inversion Ht. (* "I'll prove false for all cases which could have proved this true"*)
  inversion H0. (* even 1 is totally impossible to prove, so we're done *)
Qed. 

Module Data_Structures.
Set Implicit Arguments.

(* --- List practice --- *)

(* Here are some definitions copied from the Coq standard library. *)
Inductive list (A : Type) : Type :=
| nil
| cons (hd : A) (tl : list A).

Arguments nil {A}.
Infix "::" := cons.
Notation "[ ]" := nil.
Notation "[ x1 ; .. ; xN ]" := (cons x1 (.. (cons xN nil) ..)).

Fixpoint length {A} (ls : list A) : nat :=
  match ls with
  | nil => 0
  | _ :: ls' => 1 + length ls'
  end.

Fixpoint app {A} (ls1 ls2 : list A) : list A :=
  match ls1 with
  | nil => ls2
  | x :: ls1' => x :: app ls1' ls2
  end.
Infix "++" := app.

Fixpoint rev {A} (ls : list A) : list A :=
  match ls with
  | nil => nil
  | x :: ls' => rev ls' ++ [x]
  end.

(*
 * PROBLEM 13 [12 points, ~15 tactics]
 *
 * Prove the following theorem about the length of a reversed list.
 *
 * Hint: Proceed by induction on l.
 *
 * Hint: You'll need a helper lemma!
 *)

 Lemma len_1_S : 
  forall A (l: list A),
    length l + 1 = S (length l).
 Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
 Qed.

 Lemma length_comp:
  forall A (l1 l2 : list A),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1; auto.
  - simpl. intros. rewrite IHl1. reflexivity.
Qed.

Lemma length_rev :
  forall A (l : list A),
    length (rev l) = length l.
Proof.
  induction l.
  - auto.
  - simpl. rewrite length_comp. simpl. rewrite IHl. apply len_1_S. 
Qed.

(*
 * Here is a function that adds up all the elements of a list of nats.
 *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

(*
 * And here are two functions that computes the same result with tail recursion.
 *)
Fixpoint sum_list_tr (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => sum_list_tr xs (x + acc)
  end.

Definition sum_list_tailrec (l : list nat) : nat :=
  sum_list_tr l 0.

(*
 * PROBLEM 14 [5 points, ~1 sentences]
 *
 * Consider the following theorem about the two ways of summing a list. You will
 * be asked to prove it in the next problem. For now, make a proof attempt that
 * proceeds directly by induction on `l`, without any nested inductions or
 * extra lemmas. At some point, you should get stuck.
 *
 * Write a sentence or two explaining why your proof attempt fails. Focus on the
 * induction hypothesis and whether it gives you enough information to complete
 * the proof.
 *
 * There is no need to turn in your proof attempt. Just turn in your
 * explanation.
 *
 * Hint: The base case should be provable.
 *
 * Hint: You might be able to make slightly more progress if you use the
 * `unfold` tactic to see inside the definition of `sum_list_tailrec`.
 *)
Theorem sum_list_tailrec_ok : forall l,
  sum_list_tailrec l = sum_list l.
Proof.
  induction l.
  - auto.
  - simpl. rewrite <- IHl. unfold sum_list_tailrec. simpl. 
Abort.
  (* The remaining goal of the proof when we left off above is: "sum_list_tr l (hd + 0) = hd + sum_list_tr l 0" and the inductive
  hypothesis is "sum_list_tailrec l = sum_list l". The inductive hypothesis here is helpful if we
  have a reference to sum_list_tailrec or sum_list in our remaining goal, but that's not the case *)

(*
 * PROBLEM 15 [8 points, ~15 tactics]
 *
 * Now fix your broken proof by backing up and stating and proving a more
 * general helper lemma. Then use your helper lemma to finish the proof.
 *
 * Hint: Since `sum_list_tailrec` is defined in terms of the recursive function
 * `sum_list_tr`, it makes sense for your lemma to be about `sum_list_tr`.
 *
 * Hint: Your lemma should be proved by induction.
 *
 * Hint: Your fixed proof of `sum_list_tailrec_ok` should *not* use induction.
 *)

 Lemma sum_list_tr_sum_list_pl_acc : forall l acc,
 sum_list_tr l acc = sum_list l + acc.
Proof.
 induction l.
 - auto.
 - simpl. intros. rewrite -> IHl. lia.
Qed.

Theorem sum_list_tailrec_ok : forall l,
  sum_list_tailrec l = sum_list l.
Proof.
  intros. unfold sum_list_tailrec.
  replace (sum_list l) with (sum_list l + 0) by lia. apply sum_list_tr_sum_list_pl_acc.
Qed.

(* --- Binary Tree practice --- *)

Inductive tree (A : Type) : Type :=
| Leaf
| Node : tree A -> A -> tree A -> tree A.
Arguments Leaf {A}.

Fixpoint reverse {A} (t : tree A) : tree A :=
  match t with
  | Leaf => Leaf
  | Node l n r => Node (reverse r) n (reverse l)
  end.

(*
 * PROBLEM 16 [5 points, ~5 LOC]
 *
 * Define a function that adds up all the elements of a tree of nats.
 *)
Fixpoint sum_tree (t : tree nat) : nat :=
  match t with
  | Leaf => 0
  | Node l d r => d + sum_tree l + sum_tree r
  end.

(*
 * PROBLEM 17 [5 points, ~5 tactics]
 *
 * Prove that `reverse` has no effect on the sum of the elements in a tree.
 *)
Lemma sum_tree_reverse :
  forall t,
    sum_tree (reverse t) = sum_tree t.
Proof.
  induction t.
  - auto.
  - simpl. rewrite IHt1. rewrite IHt2. lia. 
Qed.

(*
 * PROBLEM 18 [12 points, ~20 tactics]
 *
 * Prove the following similar lemma about `sum_list` and `rev`.
 *
 * Hint: Proceed by induction on l.
 *
 * Hint: You'll need a helper lemma about sum_list.
 *)

Lemma sum_list_app_eq_sum_list_split :
  forall l1 l2,
    sum_list (l1 ++ l2) = sum_list l1 + sum_list l2. 
Proof.
  induction l1.
  - auto.
  - simpl. intros. rewrite IHl1. lia.
Qed.

(* sum_list_nat is mostly just for reorganizing a goal and I couldn't
   figure out another way to do that *)
Lemma sum_list_nat :
  forall (hd : nat) (l1: list nat),
     hd = sum_list [hd].
  Proof.
    intros. simpl. lia. 
Qed.

Lemma sum_list_rev :
  forall l,
    sum_list (rev l) = sum_list l.
Proof.
  induction l.
  - auto.
  - simpl. rewrite <- IHl. simpl. rewrite (sum_list_nat hd) at 2.
    rewrite sum_list_app_eq_sum_list_split. lia. auto.
Qed.

End Data_Structures.

(*
 * PROBLEM 19 [5 points, ~3 sentences]
 *
 * Please take a moment to let us know how the homework went for you by
 * answering the following three questions:
 *    1. How long did the homework take you?
 *    2. Which parts were most interesting or helpful for you?
 *    3. Which parts were especially frustrating, confusing, or tedious?
 *       What should we do better next time?
 *
 * It's fine if your answers are short if you don't have much to say!
 *)

(* 
* answers to the questions above:
 *    1. probably 15 or so hours, but I got stuck for a long time on the
  *       first few. Office hours with Zach was really helpful!
 *    2. Everything was interesting, but I enjoyed the data structures
  *       section the most. It's cool that there is a (truly challenging)
  *       challenges section.
 *    3. Everything made sense eventually. I would definitely benefit from 
         seeing the instructors work through more proofs with more tactics.
         Office hours was a game-changer for me mostly because I was able to 
        see how Zach thought through a few lemmas. 
 *)



(* --- End of Core Points --- *)

(*
 * This is the end of the core points available for Homework 2. See below for
 * challenge points.
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this
 * homework assignment.
 *)

(*
             ____                  _     _                     ____
            / ___|    ___    ___  | |_  (_)   ___    _ __     |___ \
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \      __) |
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    / __/
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_____|

                          SECTION 2 : Challenge Problem
*)

(*
 * CHALLENGE 20 [10 points, ~20 tactics]
 *
 * Give an alternative characterization of evenness as follows.
 *)


 Lemma even_double_nat :
 forall n, n + n = double n .
Proof.
  intros.
  induction n.
  - auto.
  - simpl. lia.
Qed.

Lemma even_n_add_n :
 forall n, even (n + n).
Proof.
  intros.
  induction n.
  - simpl. constructor.
  - rewrite even_double_nat. apply double_even.
Qed.

Lemma even_iff_exists_half :
  forall n,
    even n <-> exists k, n = 2 * k.
Proof.
  split.
  intros.
  induction H.
  - exists 0. auto.
  - destruct IHeven.
    + exists (S x). lia.
  - simpl in *. (* exists k, n = 2 * k. is NOT recursive so we shouldn't need induction. *)
    intros.
    destruct H.
    rewrite H.
    replace (x + (x + 0)) with (x + x) by lia.
    apply even_n_add_n.
Qed.

(* CHALLENGE 21 [20 points, ~8 tactics]
 *
 * In class we saw a proof that Peirce's law implies the law of excluded middle.
 * Now prove the reverse direction
 *
 * Hint: This way should be easier than the proof from lecture.
 *)
Lemma lem_implies_peirce :
  (forall P : Prop, P \/ ~P) -> forall P Q : Prop, ((P -> Q) -> P) -> P.
Proof.
   simpl. intros.
    destruct (H P) as [P1 | P2]. (* P1 = P, P2 = ~P - comment in here because I became *very* confused*)
    - apply P1.
    - apply H0. intros. contradict H1. apply P2.
  Qed.
