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



Lemma completeness_of_protocol: 
 forall (program: list ins)(CPU_trace rm_first_CPU_trace rm_last_CPU_trace: list CPU_state)
  (first_CPU_state last_CPU_state: CPU_state)
  (action_trace: list action_type)(memory_trace: list action_type),
  CPU_trace = cons first_CPU_state rm_first_CPU_trace ->
  CPU_trace = rm_last_CPU_trace ++ [last_CPU_state] ->
  (exists (mem_list: list (int256 -> int256))(first_mem last_mem: int256 -> int256),
  length mem_list = length action_trace /\
  eval_ins_list program
  (combine_to_pc_state first_CPU_state first_mem)
  (combine_to_act_state_list rm_last_CPU_trace mem_list action_trace)
  (combine_to_pc_state last_CPU_state last_mem))
-> constraints program CPU_trace action_trace memory_trace.
Proof.
  intros.
  destruct H1 as [mem_list [first_mem [last_mem [H1 H2]]]].
  split.
  remember (combine_to_pc_state first_CPU_state first_mem) as x.
  remember (combine_to_act_state_list rm_last_CPU_trace mem_list action_trace) as y.
  remember (combine_to_pc_state last_CPU_state last_mem) as z.
  destruct H2 as [program].
   + apply trace_CPU with (rm_first_CPU_trace:=rm_first_CPU_trace) (first_CPU_state:=first_CPU_state).
    - tauto.
    - unfold combine_to_pc_state in *.
      unfold Definition_and_soundness.Build_pc_state  in *.
      unfold Definition_and_soundness.Build_program_state in *.
      rewrite Heqx in H2.
      simpl in H2.
      tauto.
   -  unfold combine_to_pc_state in *.
      unfold Definition_and_soundness.Build_pc_state  in *.
      unfold Definition_and_soundness.Build_program_state in *.
      rewrite Heqx in H4.
      simpl in H4.
      tauto.
    - destruct H6 as[n ?].
       rewrite H.
        revert H CPU_trace  rm_first_CPU_trace rm_last_CPU_trace.

       apply rev_ind with (l:=rm_first_CPU_trace).
       * pose proof adjacent_CPU_state_nil.
          specialize (H7 eval_constraint first_CPU_state).
          tauto.
       * intros.
          pose proof adjacent_CPU_state_cons.
          pose proof cons_app_eq first_CPU_state.
          specialize(H9 l).
          destruct H9 as [last_two_CPU_state [rm_last_two_CPU_trace]].
          specialize (H8 eval_constraint last_two_CPU_state x0 (rm_last_two_CPU_trace)).
          rewrite H9 in H7.
          assert (eval_constraint last_two_CPU_state x0).
          {
             destruct last_two_CPU_state.
             unfold eval_constraint.
              simpl in *.
              destruct inst0.
              +  pose proof jumpi_constraint.
                  specialize (H10 ({| CPU_state.pc := pc0; stack := stack0; inst := JUMPI |}) x0 )
}.
Admitted.

(*      induction n.
      * simpl in H6.
        destruct H6.
        inversion H6.
        rewrite H8 in H5.
        rewrite Heqx in H7.
        rewrite Heqz in H7.
        inversion H7.*)
(*
      rewrite H.
      induction rm_first_CPU_trace.
      * simpl.
        pose proof adjacent_CPU_state_nil.
        pose proof adjacent_CPU_state_cons.
        specialize (H0 eval_constraint last_CPU_state).
        tauto.
      * pose proof adjacent_CPU_state_nil.
        pose proof adjacent_CPU_state_cons.
        pose proof cons_app_eq a rm_last_CPU_trace.
        destruct H9 as [last_two_CPU_trace [rm_last_two_CPU_trace ?]].
        rewrite H9.
        specialize (H8 eval_constraint last_two_CPU_trace last_CPU_state rm_last_two_CPU_trace).
        apply H8.
subst.
*)