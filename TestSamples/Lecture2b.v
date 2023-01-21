Require Import List.
Import ListNotations.

Check [1; 2; 3].

Print nat.

(* These are well formed propositions *)
Check (True /\ True).
Check (True /\ False).
(* To figure out how /\ is defined, Locate can be used to see how a notation is defined *)
Locate "/\".
(* Here we see that this /\ is actually and function *)


(* True is a Proposition and true is a boolean *)


Print and.

(* We can see that and is not built in, we can define it however we want *)

(*
Inductive and (A B : Prop) : Prop :=
  | conj : A -> B -> and A B.
*)

Lemma foo :
 1 <= 2 /\ negb true = false.
Proof.
    (* conj constructor is the one that builds and *)
    apply conj.
    - Locate "<=".
      Print le.
      apply le_S.
      apply le_n.
      Show Proof.
    - Print negb.
      simpl. reflexivity. (* Used simpl because negb is a function *)
      Show Proof.
Qed.


Lemma foo1 :
 1 <= 2 /\ negb true = false.
Proof.
    (* split also does apply conj *)
    split.
    - Locate "<=".
      Print le.
      apply le_S.
      apply le_n.
      Show Proof.
    - Print negb.
      simpl. reflexivity. (* Used simpl because negb is a function *)
      Show Proof.
Qed.

Lemma foo2:
    1 <= 2 /\ negb true = false.
Proof.
    (* constructor - if your goal is some inductively defined proposition like and, 
        constructor says go look for all possible constructors for that type
        and the first one that'd work, use it! *)
    constructor.
    - constructor. (* since le is also inductively defined *)
      constructor.
    - constructor. (* since equality is also inductively defined *) 
Qed.

(* Constructor is extremely useful. Do not use constructor for le, use Import Psatz and then use lia from it. *)

Require Import Psatz.

Lemma foo3:
    1 <= 2 /\ negb true = false.
Proof.
    constructor.
    - lia.
    - constructor.
Qed.

Lemma bar :
    forall (A B: Prop),
    A /\ B -> A.
Proof.
    intros.
    (* if you use construct to introduce something, you can use destruct to use it ! *)
    destruct H.
    (* basically saying that the goal is in the context *)
    assumption. (* or could use exact H *)
    Show Proof.
Qed.


(* Disjunction *)

Check (True \/ True).

Locate "\/".
Print or.

(*
Inductive or (A B : Prop) : Prop :=
	or_introl : A -> A \/ B | or_intror : B -> A \/ B.
*)

Check (True \/ False).


Lemma foobar:
    2 <= 1 \/ negb true = false.
Proof.
    (* constructor picks the first item by default coz for or only left subgoal needs to be proved, but reality is it can't be proven so we specifically apply right side *)
    apply or_intror. auto.
Qed.

Lemma foobar1:
    2 <= 1 \/ negb true = false.
Proof.
    (* can also use right tactic to select the right subgoal *)
    right. auto.
Qed.

(* Use of Restart to reset the proof *)

Lemma foobar2:
    2 <= 1 \/ negb true = false.
Proof.
    right. auto.
    Restart.
    apply or_intror. auto.
Qed.


Lemma foobar3:
    (* -> False basically means that the thing on the left cannot be proven/ doesn't exist / is not a valid proposition *)
    2 <= 1 \/ negb true = true -> False.
Proof.
    intros.
    destruct H.  (* For every way H is built, we will prove the lemma *)
    - lia.
    - simpl in H.
      congruence.
Qed.


Print True.  (* The one constructor I is a proof of True *)
Print False. (* False is a type but There is no constructor of False. There is no way to build False. *)



Check (exists x, 1 <= x).
(* Print exists. will fail exists is not a type, its a notation *)

Locate "exists".
Print ex.


Lemma googa:
    exists x, 1 <= x.
Proof.
    (* use constructor when we need to pass something to it but don't know what *)
    econstructor.
    constructor.
    Show Proof.
Qed.

Lemma blorp:
    (* This exists is a notation for a type *)
    exists x, 1 <= x.
Proof.
    (* This exists is a tactic *)
    exists 1. lia.
Qed.


Lemma blorp1:
    (exists x, 1 <= x) -> True.
Proof.
    intros.
    destruct H.
    exact I.
    Show Proof.
    
    Restart.
    
    exact (fun _ => I).
    Show Proof.
Qed.


Inductive tree (A: Set) : Set :=
| leaf : tree A
| branch: A -> tree A -> tree A -> tree A.


Inductive list (A: Set) : Set :=
| nil: list A
| cons: A -> list A -> list A.





