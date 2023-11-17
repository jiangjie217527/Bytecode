Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sets.Multiset.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Definition_and_soundness.  Import Definition_and_soundness.

Local Open Scope string.
Local Open Scope sets.
Local Open Scope list.

Import Int256.
Import Lang.
Import program_state.
Import CPU_state.
Import pc_state.
Import act_state.

(* This is a template Lemma for you to test the environment, 
  if you can complie this lemma correctly, 
  then you can just delete this lemma and write your own code *)
Lemma POP_sem_trivial: forall (pc: nat)(y: act_state)(x z: pc_state), 
  POP_sem pc x (cons y nil) z ->
  (exists v: int256, x.(state) = y.(state) /\ y.(action).(mem_ins) = non /\
  x.(pc) = pc /\ y.(pc) = pc /\ z.(pc) = pc + 1 /\
  x.(state).(stack) = cons v z.(state).(stack) /\
  y.(state).(memory) = z.(state).(memory)).
Proof.
  intros.
  inversion H.
  exists v.
  subst.
  repeat split; try tauto.
Qed.
