(** PROJETO E ANÁLISE DE ALGORITMOS - 2025/2 *)
(** Link do site do coq se vocês prefirirem: https://jscoq.github.io/scratchpad.html

Nome e username dos participantes:
1. 
2. Geilson - Geilsondss 
3. 
*)

Require Import Arith List Recdef.
Require Import Coq.Program.Wf.
Require Import Permutation.

Inductive sorted :list nat -> Prop :=
  | nil_sorted : sorted nil
  | one_sorted: forall n:nat, sorted (n :: nil)
  | all_sorted : forall (x y: nat) (l:list nat), sorted (y :: l) -> x <= y -> sorted (x :: y :: l).

Definition le_all x l := forall y, In y l -> x <= y.

Infix "<=*" := le_all (at level 70, no associativity).

Lemma tail_sorted: forall l a, sorted (a :: l) -> sorted l.
Proof.
  intro l.
  case l.
  - intros a H.  
    apply nil_sorted.  
  - intros n l' a H.  
    inversion H; subst.
    assumption.  
Qed.

Lemma le_all_sorted: forall l a, a <=* l -> sorted l -> sorted (a :: l).
Proof.
  intros l a H H0.
  induction l.
  - apply one_sorted.
  - apply all_sorted.
    + exact H0.
    + destruct H with (y := a0).
      * simpl.
        left.
        apply eq_refl.
      * apply Nat.le_refl.
      * apply le_S.
        exact l0.
Qed.

Lemma remove_sorted: forall l a1 a2, sorted (a1 :: a2 :: l) -> sorted (a1 :: l).
Proof.
  intro l; case l.
  - intros a1 a2 H.
    apply one_sorted.
  - intros n l' a1 a2 H.
    inversion H; subst.
    inversion H2; subst.
    apply all_sorted.
    + assumption.
    + apply Nat.le_trans with a2; assumption.
Qed.
    

Lemma sorted_le_all: forall l a, sorted(a :: l) -> a <=* l.
Proof.
  induction l.
  - intros a H y H0.
    destruct H0.
  - intros a0 H y H0.
    destruct H0.
  Admitted.

Fixpoint num_oc n l  :=
  match l with
    | nil => 0
    | h :: tl =>
      if n =? h then S(num_oc n tl) else  num_oc n tl
  end.

Definition perm l l' := forall n:nat, num_oc n l = num_oc n l'.

Lemma perm_refl: forall l, perm l l.
Proof.
Admitted.

Lemma num_oc_append: forall n l1 l2, num_oc n l1 + num_oc n l2 = num_oc n (l1 ++ l2).
Proof.
  Admitted.

Definition sorted_pair_lst (p: list nat * list nat) :=
sorted (fst p) /\ sorted (snd p).


Definition len (p: list nat * list nat) :=
   length (fst p) + length (snd p).

Function merge (p: list nat * list nat) {measure len p} :=
match p with
  | (nil, l2) => l2
  | (l1, nil) => l1
  | ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
if hd1 <=? hd2 then hd1 :: merge (tl1, l2)
      else hd2 :: merge (l1, tl2)
   end.

Proof.
  Admitted.

Lemma merge_in: forall y p, In y (merge p) -> In y (fst p) \/ In y (snd p).
Proof.
Admitted.


Theorem merge_sorts: forall p, sorted_pair_lst p -> sorted (merge p).
Proof.
  Admitted.

Function mergesort (l: list nat) {measure length l}:=
  match l with
  | nil => nil
  | hd :: nil => l
  | hd :: tail =>
     let n := length(l) / 2 in
     let l1 := firstn n l in
     let l2 := skipn n l in
     let sorted_l1 := mergesort(l1) in
     let sorted_l2 := mergesort(l2) in
     merge (sorted_l1, sorted_l2)
  end.

Proof.
Admitted.

Theorem mergesort_sorts: forall l, sorted (mergesort l).
Proof.
  Admitted.

Lemma merge_num_oc: forall n p, num_oc n (merge p) = num_oc n (fst p) + num_oc n (snd p).
Proof.
Admitted.


Theorem mergesort_is_perm: forall l, perm l (mergesort l).
Proof.
  Admitted.

Theorem mergesort_is_correct: forall l, perm l (mergesort l) /\ sorted (mergesort l).
Proof.
  Admitted.
