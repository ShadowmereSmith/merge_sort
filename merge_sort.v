(** PROJETO E ANÁLISE DE ALGORITMOS - 2025/2 *)
(** Link do site do coq se vocês prefirirem: https://jscoq.github.io/scratchpad.html*)
(** CORREÇÃO DO ALGORITMO MERGESORT
  
Nome e username dos participantes:
1. Ayrla Costa - AyrlaCosta
2. Geilson - Geilsondss 
3. Wesley - ShadowmereSmith
*)

Require Import Arith List Recdef.
Require Import Coq.Program.Wf.
Require Import Permutation.

(** Primeira Etapa*)
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
    + inversion H; subst.
          exact H5.
        + apply remove_sorted in H.
          apply IHl in H.
          unfold "<=*" in H.
          apply H in H0.
          exact H0.
Qed.

(** Segunda Etapa *)
Fixpoint num_oc n l  :=
  match l with
    | nil => 0
    | h :: tl =>
      if n =? h then S(num_oc n tl) else  num_oc n tl
  end.

Definition perm l l' := forall n:nat, num_oc n l = num_oc n l'.

Lemma perm_refl: forall l, perm l l.
Proof.
  intro l. unfold perm. intro. reflexivity.
Qed.

Lemma num_oc_append: forall n l1 l2, num_oc n l1 + num_oc n l2 = num_oc n (l1 ++ l2).
Proof.
  intros. induction l1.
  - simpl num_oc. trivial.
  - simpl. destruct (n =? a).
    + rewrite <- IHl1. apply Peano.plus_Sn_m.
    + assumption.
Qed.

(** Terceira Etapa *)
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
  - intros. unfold len. unfold fst. unfold snd. simpl length.
    apply plus_lt_compat_r. auto.
  - intros. unfold len. unfold fst. unfold snd. simpl length.
    apply plus_lt_compat_l. auto.  
Qed.

Lemma merge_in: forall y p, In y (merge p) -> In y (fst p) \/ In y (snd p).
Proof.
intros. functional induction (merge p).
  - right. unfold snd. assumption.
    - left. unfold fst. assumption.
    - simpl in H. destruct H as [H1 | H2].
    + left. unfold fst. unfold In. left. assumption.
        + destruct IHl.
        * assumption.
          * left. unfold fst. unfold fst in H. simpl In. right. assumption.
          * right. simpl. simpl in H. assumption.
    - simpl in H. destruct H as [H1 | H2].
    + right. simpl snd. simpl In. left. assumption.
        + destruct IHl.
        * assumption.
          * left. unfold fst. unfold fst in H. assumption.
          * right. simpl. simpl in H. right. assumption.
Qed.


Theorem merge_sorts: forall p, sorted_pair_lst p -> sorted (merge p).
Proof.
  intro p. functional induction (merge p).
  - unfold sorted_pair_lst. intro. destruct H.
    unfold snd in H0. assumption.
  - unfold sorted_pair_lst. intro. destruct H.
    unfold fst in H. assumption.
  - intro. apply le_all_sorted.
    + unfold le_all. intro. intro. apply merge_in in H0.
      destruct H0 as [H1 | H2].
      * simpl fst in H1. unfold sorted_pair_lst in H. destruct H as [H2 H3].
        simpl fst in H2. apply sorted_le_all in H2. unfold le_all in H2.
        apply H2. assumption.    
      * simpl snd in H2. apply Nat.le_trans with hd2.
        -- apply Nat.leb_le. assumption.
        -- unfold sorted_pair_lst in H. destruct H as [H3 H4]. simpl snd in H4.
           apply sorted_le_all in H4. simpl In in H2. destruct H2 as [H5 | H6].
           ** rewrite H5. trivial.
           ** unfold le_all in H4. apply H4. assumption.
    + apply IHl. unfold sorted_pair_lst. split.
      * simpl fst. unfold sorted_pair_lst in H. destruct H as [H1 H2].
        simpl fst in H1. apply tail_sorted in H1. assumption.
      * simpl snd. unfold sorted_pair_lst in H. destruct H as [H1 H2].
        simpl snd in H2. assumption.  
  - intro. apply le_all_sorted.
    + unfold le_all. intro. intro. apply merge_in in H0.
      destruct H0 as [H1 | H2].
      * simpl fst in H1. unfold sorted_pair_lst in H. destruct H as [H2 H3].
        simpl fst in H2. apply sorted_le_all in H2. unfold le_all in H2.
        simpl in H1. destruct H1 as [H4 | H5].
        ** rewrite <- H4. apply leb_complete_conv in e0. apply Nat.lt_le_incl in e0. assumption.
        ** apply H2 in H5. apply leb_complete_conv in e0. apply Nat.lt_le_incl in e0. rewrite <- H5. assumption.
      * simpl snd in H2. apply Nat.le_trans with hd2.
        -- trivial.
        -- unfold sorted_pair_lst in H. destruct H as [H3 H4]. simpl snd in H4.
           apply sorted_le_all in H4. unfold le_all in H4. apply H4 in H2. assumption.
    + apply IHl. unfold sorted_pair_lst. split.
      * simpl fst. unfold sorted_pair_lst in H. destruct H as [H1 H2].
        simpl fst in H1. assumption.
      * simpl snd. unfold sorted_pair_lst in H. destruct H as [H1 H2].
        simpl snd in H2. apply tail_sorted in H2. assumption.  
Qed.

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
- intros. rewrite skipn_length. apply Nat.sub_lt.
  + apply Nat.lt_le_incl. apply Nat.div_lt.
    * simpl. apply Nat.lt_0_succ.
      * apply Nat.lt_1_2.
    + apply Nat.div_str_pos. simpl. split.
    * apply Nat.lt_0_2.
      * apply Peano.le_n_S. apply Peano.le_n_S. apply Peano.le_0_n.  
  - intros. rewrite firstn_length. rewrite min_l.
  + apply Nat.div_lt.
    * simpl. apply Nat.lt_0_succ.
      * apply Nat.lt_1_2.
    + apply Nat.lt_le_incl. apply Nat.div_lt.
    * simpl. apply Nat.lt_0_succ.
      * apply Nat.lt_1_2.
Defined.
        

Theorem mergesort_sorts: forall l, sorted (mergesort l).
Proof.
induction l.
  - apply nil_sorted.
  - functional induction (mergesort (a :: l)).
    + apply nil_sorted.
    + apply one_sorted.
    + apply merge_sorts.
      unfold sorted_pair_lst.
      split.
      * unfold fst.
        assumption.
      * unfold snd.
        assumption.
Qed.

Lemma merge_num_oc: forall n p, num_oc n (merge p) = num_oc n (fst p) + num_oc n (snd p).
Proof.
intros. functional induction (merge p).
  - simpl fst. simpl snd. simpl num_oc. trivial.
  - simpl fst. simpl snd. simpl num_oc. trivial.
  - simpl fst. simpl snd. simpl num_oc at 1 2. destruct (n =? hd1).
    + rewrite IHl. apply Peano.plus_Sn_m.
    + rewrite IHl. simpl fst. simpl snd. trivial.
  - simpl fst. simpl snd. simpl num_oc at 1 3. (destruct (n =? hd2)).
      + rewrite IHl. simpl fst. simpl snd. apply Peano.plus_n_Sm.
      + rewrite IHl. simpl fst. simpl snd. trivial.
Qed.


Theorem mergesort_is_perm: forall l, perm l (mergesort l).
Proof.
  intros. functional induction (mergesort l).
  - apply perm_refl.
  - apply perm_refl.
  - unfold perm. intros. rewrite merge_num_oc.
    unfold fst. unfold snd.
    replace (num_oc n (mergesort (firstn (length (hd :: tail) / 2) (hd :: tail)))) with (num_oc n (firstn (length (hd :: tail) / 2) (hd :: tail))).
    replace (num_oc n (mergesort (skipn (length (hd :: tail) / 2) (hd :: tail)))) with (num_oc n (skipn (length (hd :: tail) / 2) (hd :: tail))).
    + rewrite num_oc_append. rewrite firstn_skipn. reflexivity.
    + destruct mergesort.
      * unfold perm in *. rewrite -> IHl1. reflexivity.
      * unfold perm in *. rewrite -> IHl1. reflexivity.
    + unfold perm in *. rewrite -> IHl0. reflexivity.
Qed.


Theorem mergesort_is_correct: forall l, perm l (mergesort l) /\ sorted (mergesort l).
Proof.
  split.
  - apply mergesort_is_perm.
  - apply mergesort_sorts.
Qed.
