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

Definition Build_program_state (memory: int256 -> int256) (stack: list int256): program_state :=
  {| program_state.memory := memory; program_state.stack := stack |}.

Definition Build_pc_state (pc: nat) (state: program_state): pc_state :=
  {| pc_state.pc := pc; pc_state.state := state |}.

Theorem soundness:
  (* CPU_trace_list is without first and last CPU_state *)
  forall (program: list ins)(CPU_trace rm_first_CPU_trace rm_last_CPU_trace: list CPU_state)
  (first_CPU_state last_CPU_state: CPU_state)
  (action_trace: list action_type)(memory_trace: list action_type),
  constraints program CPU_trace action_trace memory_trace ->
  CPU_trace = cons first_CPU_state rm_first_CPU_trace ->
  CPU_trace = rm_last_CPU_trace ++ [last_CPU_state] ->
  exists (mem_list: list (int256 -> int256))(first_mem last_mem: int256 -> int256),
  length mem_list = length action_trace /\
  eval_ins_list program
  (combine_to_pc_state first_CPU_state first_mem)
  (combine_to_act_state_list rm_last_CPU_trace mem_list action_trace)
  (combine_to_pc_state last_CPU_state last_mem) /\
  (forall address: int256, last_mem_prop last_mem memory_trace address)
  .
Proof.
  intros program CPU_trace rm_first_CPU_trace rm_last_CPU_trace first_CPU_state last_CPU_state action_trace memory_trace.
  revert program CPU_trace rm_first_CPU_trace rm_last_CPU_trace first_CPU_state last_CPU_state memory_trace.
  apply rev_ind with (l := action_trace).
  - intros. subst. inversion H. subst.
    inversion H0. subst.
    inversion H8. symmetry in H13, H14. subst. clear H8.
    (* CPU_trace should be a single value list; adjacent_CPU_state_for_action_trace has two constructors *)
    inversion H4. subst. inversion H8; subst.
    + symmetry in H1. apply app_eq_unit in H1. inversion H1. clear H1.
      { inversion H12. clear H12. subst. inversion H13. subst. clear H13.
        unfold combine_to_act_state_list. exists nil. simpl. (* mem_list = [] *)
        exists (fun _ => Int256.zero). exists (fun _ => Int256.zero). (* first_mem = last_mem = fun (n: int256) => Int256.zero *)
        destruct program.
        - inversion H2. subst. simpl in H1. inversion H1. contradiction. (* program = [] *)
        - intros.
          split.
          + tauto.
          + split.
            * apply sigma; try auto; try apply ActionListNil.
              unfold combine_to_pc_state, Build_pc_state, Build_program_state; simpl; exists 0; simpl.
              sets_unfold.
              tauto.
            * intros.
              assert (memory_trace = []).
              {
                inversion H5; subst.
                simpl in H1.
                apply Permutation_nil.
                tauto.
              }
              rewrite H1.
              apply not_in_memory_trace.
              simpl.
              intros.
              contradiction.
              tauto.
      }
      { inversion H12. discriminate. }
    + apply app_eq_nil in H13. inversion H13. discriminate.
    (*soundness从这里开始证明复杂情况*)
  - intros. subst. inversion H0. subst. rewrite H2 in H0, H1, H3, H5, H8.
    (*由完整的程序满足约束，推出部分程序满足约束*)
    assert (action_trace_constraint rm_last_CPU_trace l).
    {
      apply trace_action.
      inversion H5. subst.
      inversion H9.
      - symmetry in H12.
        apply app_eq_nil in H12.
        inversion H12.
        discriminate.
      - apply app_inj_tail in H10.
        destruct H10.
        apply app_inj_tail in H11.
        destruct H11.
        rewrite H10 in H13.
        rewrite H11 in H13.
        apply H13.
    }
    assert (CPU_trace_constraint rm_last_CPU_trace).
    {
      inversion H1. subst.
      rewrite <- H2 in H10.
      inversion H10.
      clear H10.
      rewrite <- H15 in H11.
      rewrite <- H15 in H12.
      clear rm_first_CPU_trace0 first_CPU_state0 H15 H16.
      inversion H13; subst.
      - symmetry in H14.
        apply app_eq_unit in H14.
        inversion H14.
        + inversion H10.
          apply action_CPU_trace_len_cons in H9.
          rewrite H15 in H9.
          discriminate.
        + inversion H10.
          discriminate.
      - assert (l0 ++ [x0; y]= (l0 ++ [x0]) ++ [y]). { rewrite <- app_assoc. tauto. }
        rewrite H16 in H10.
        apply app_inj_tail in H10.
        inversion H10.
        destruct rm_last_CPU_trace.
        + apply app_eq_nil in H17.
          inversion H17.
          discriminate.
        + rewrite H17 in H15.
          rewrite <- app_comm_cons in H2.
          inversion H2.
          rewrite <- H20.
          pose proof (trace_CPU (first_CPU_state :: rm_last_CPU_trace) rm_last_CPU_trace first_CPU_state).
          apply H19.
          tauto.
          tauto.
          tauto.
          rewrite <- H20 in H15.
          tauto.
    }
    assert (multiset_constraint rm_last_CPU_trace program).
    { 
      inversion H3.
      rewrite map_app in H11.
      apply Forall_app in H11.
      inversion H11.
      apply trace_multiset.
      tauto.
    }
    assert (action_trace_timestamp_constraint l).
    {
      inversion H4.
      - symmetry in H13.
        apply app_eq_nil in H13.
        inversion H13.
        discriminate.
      - symmetry in H12.
        apply app_eq_unit in H12.
        inversion H12.
        + inversion H14.
          rewrite H15.
          apply ActionListTraceNil.
        + inversion H14.
          discriminate.
      - apply app_inj_tail in H12.
        inversion H12.
        rewrite <- H15.
        apply H14.
    }
    assert (exists memory_trace', memory_trace_legal l memory_trace' /\
    (x.(mem_ins) <> non /\ (exists l1' l2', (memory_trace' = l1' ++ l2' /\ memory_trace = l1' ++ [x] ++ l2')) \/
    (x.(mem_ins) = non /\ memory_trace = memory_trace'))).
    {
      apply (exists_memory_trace' l memory_trace x); try tauto;
      apply (last_action_trace_timestamp_biggest (l ++ [x]) l x); tauto.
    }
    inversion H13 as [memory_trace' H14]. clear H13.
    destruct H14 as [H14 H_for_last_mem].
    assert (constraints program rm_last_CPU_trace l memory_trace').
    {
      apply all_constraints.
      apply H10.
      apply H11.
      apply H12.
      apply H9.
      inversion H14. subst.
      apply H13.
      inversion H14. subst.
      apply H15.
      apply public.
    }
    (*----到这里完成对除去最后一步的程序满足约束---------------*)
    assert (exists (rm_first_CPU_trace'
    rm_last_CPU_trace' : list CPU_state)
    (first_CPU_state' last_CPU_state' : CPU_state),
    rm_last_CPU_trace = first_CPU_state' :: rm_first_CPU_trace' /\
    rm_last_CPU_trace = rm_last_CPU_trace' ++ [last_CPU_state']).
    {
      apply action_CPU_trace_len_cons in H9.
      destruct rm_last_CPU_trace.
      - discriminate.
      - exists rm_last_CPU_trace.
        specialize (cons_app_eq c rm_last_CPU_trace).
        intros.
        destruct H15. destruct H15.
        exists x1, c, x0.
        split.
        + tauto.
        + apply H15.
    }
    inversion H15 as [rm_first_CPU_trace' H16]. clear H15.
    inversion H16 as [rm_last_CPU_trace' H17]. clear H16.
    inversion H17 as [first_CPU_state' H18]. clear H17.
    inversion H18 as [last_CPU_state' H19]. clear H18.
    inversion H19 as [H20 H21]. clear H19.
    apply (H program rm_last_CPU_trace rm_first_CPU_trace' rm_last_CPU_trace'
    first_CPU_state' last_CPU_state' memory_trace') in H13; try tauto.
    inversion H13 as [mem_list' H15]. clear H13.
    inversion H15 as [first_mem' H13]. clear H15.
    inversion H13 as [last_mem' H15]. clear H13.
    exists (mem_list' ++ [last_mem']). exists first_mem'.
    assert (exists last_mem, last_mem = (fun address0 =>
      match x.(mem_ins) with
      | write address value => if (Int256.eq address address0) then value else (last_mem' address0)
      | _ => last_mem' address0
      end
    ) /\ (forall address : int256,
    last_mem_prop last_mem memory_trace
      address)).
    { 
      destruct H15; destruct H15.
      exists (fun address0 =>
        match x.(mem_ins) with
        | write address value => if (Int256.eq address address0) then value else (last_mem' address0)
        | _ => last_mem' address0
        end
      ).
      intros.
      inversion H14. clear H19 H22 action_trace0 memory_trace0.
      pose proof (last_action_trace_timestamp_biggest (l ++ [x]) l x).
      assert (Forall
      (fun a : action_type =>
       a.(timestamp) < x.(timestamp)) l).
      {
        assert (l ++ [x] = l ++ [x]). { tauto. }
        apply (H19 H22 H4).
      }
      clear H19.
      split; try tauto.
      intro.
      apply (construct_last_mem
      memory_trace memory_trace' l 
      x address last_mem' H7 H6 H18 H17 H22 H_for_last_mem).
      tauto.
    }
    destruct H13 as [last_mem H13]. 
    assert (eval_ins_list_single program
    (combine_to_pc_state last_CPU_state' last_mem')
    (combine_to_act_state_list [last_CPU_state']
      [last_mem'] 
      [x])
    (combine_to_pc_state last_CPU_state last_mem)).
    {
      rewrite H21 in H5.
      inversion H5.
      inversion H16.
      - symmetry in H23.
        apply app_eq_nil in H23.
        inversion H23.
        discriminate.
      - apply app_inj_tail in H19.
        inversion H19. clear H19.
        apply app_inj_tail in H25.
        inversion H25. clear H25.
        apply app_inj_tail in H22.
        inversion H22. clear H22.
        rewrite H27 in H23.
        rewrite H26 in H23.
        rewrite H28 in H23.
        destruct H15.
        destruct H22.
        inversion H1. clear H30 H31 H32 H34 CPU_trace0 rm_first_CPU_trace0 first_CPU_state0.
        rewrite H21 in H33.
        inversion H33.
        + symmetry in H31.
          apply app_eq_unit in H31.
          destruct H31.
          {
            destruct H30.
            apply app_eq_nil in H30.
            destruct H30.
            discriminate.
          }
          {
            destruct H30.
            discriminate.
          }
        + assert (l1 ++ [x1; y0] = (l1 ++ [x1]) ++ [y0]). { rewrite <- app_assoc; tauto. }
          rewrite H34 in H30.
          apply app_inj_tail in H30.
          destruct H30.
          apply app_inj_tail in H30.
          destruct H30.
          rewrite H36, H35 in H31.
          clear H32 H30 H36 H34 H35 H33 x1 y0 l1.
          clear H26 H19 H25 H28 H24 H27 H18 l0 x0 y action0 l_action H17 H16 action_trace0 CPU_trace action_trace0.
          inversion H23.
          {
            clear H24 H25 H26 state0 next_state action0.
            unfold eval_constraint in H31.
            rewrite H16 in H31.
            assert (MLOAD_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
            last_mem') (combine_to_act_state_list
            [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
            last_mem)).
            {
              inversion H31. clear H26 H27 x0.
              inversion H25. clear H27 H25 offset value0.
              assert (last_mem' address = value).
              {
                specialize (H29 address).
                destruct H_for_last_mem; destruct H25.
                - destruct H26 as [l1 [l2 H26]].
                  destruct H26 as [H_pre H_now].
                  inversion H14.
                  apply (additional_property_to_for_new_read address value x memory_trace memory_trace' l1 l2 l last_mem' H7 H27 H26 H6 H4 H_pre H_now H17 H29).
                - rewrite H25 in H17.
                  discriminate.
              }
              apply mload_sem with (offset := address) (l := remaining_stack); try tauto.
              {
                assert (((combine_to_pc_state last_CPU_state' last_mem').(state)).(memory) address = value).
                {
                  unfold combine_to_pc_state.
                  tauto.
                }
                rewrite H26.
                unfold combine_to_pc_state.
                tauto.
              }
              {
                simpl.
                destruct H13.
                rewrite H13.
                rewrite H17.
                reflexivity.
              }
              {
                simpl.
                rewrite H25.
                tauto.
              }
            }
            assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
            (seq 0 (Datatypes.length program)))).
            {
              inversion H11.
              clear H27 program0.
              rewrite Forall_forall in H25.
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
              (fun cpu_state : CPU_state =>
               (cpu_state.(inst), cpu_state.(pc)))
              rm_last_CPU_trace)).
              {
                rewrite H21.
                rewrite map_app.
                apply in_or_app.
                right.
                simpl.
                left.
                tauto.
              }
              apply (H25 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H27).
            }
            constructor.
            unfold fold_ins_sem.
            assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
            last_mem') (combine_to_act_state_list
            [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
            last_mem)).
            {
              unfold eval_ins.
              rewrite H16.
              tauto.
            }
            apply (in_property (ins * nat) 
            pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
            (combine program (seq 0 (Datatypes.length program)))
            eval_ins
            (combine_to_pc_state last_CPU_state' last_mem')
            (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
            (combine_to_pc_state last_CPU_state last_mem)
            ); tauto.
          }
          {
            clear H24 H25 H19 state0 next_state action0.
            unfold eval_constraint in H31.
            rewrite H16 in H31.
            assert (MSTORE_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
            last_mem') (combine_to_act_state_list
            [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
            last_mem)).
            {
              inversion H31. clear H25 H26 x0 y.
              rewrite H18 in H24.
              inversion H24.
              rewrite H28 in H18.
              clear H24 H26 H27 H28 offset value0.
              apply mstore_sem with (offset := address) (v := value); try tauto.
              destruct H13.
              rewrite H13.
              rewrite H17.
              simpl.
              unfold update_memory.
              apply functional_extensionality.
              intros address0.
              destruct (Int256.eq_dec address address0).
              - rewrite e. reflexivity.
              - pose proof n as n'.
                apply not_eq_sym in n'.
                apply Int256.eq_false in n.
                apply Int256.eq_false in n'.
                rewrite n, n'.
                reflexivity.
            }
            assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
            (seq 0 (Datatypes.length program)))).
            {
              inversion H11.
              clear H26 program0.
              rewrite Forall_forall in H24.
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
              (fun cpu_state : CPU_state =>
               (cpu_state.(inst), cpu_state.(pc)))
              rm_last_CPU_trace)).
              {
                rewrite H21.
                rewrite map_app.
                apply in_or_app.
                right.
                simpl.
                left.
                tauto.
              }
              apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
            }
            constructor.
            unfold fold_ins_sem.
            assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
            last_mem') (combine_to_act_state_list
            [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
            last_mem)).
            {
              unfold eval_ins.
              rewrite H16.
              tauto.
            }
            apply (in_property (ins * nat) 
            pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
            (combine program (seq 0 (Datatypes.length program)))
            eval_ins
            (combine_to_pc_state last_CPU_state' last_mem')
            (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
            (combine_to_pc_state last_CPU_state last_mem)
            ); tauto.
          }
          {
            clear H24 H25 H19 state0 next_state action0.
            unfold eval_constraint in H31.
            destruct last_CPU_state'.(inst) eqn: H_ins.
            - assert (JUMPI_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply jumpi_sem with (dest := dest) (cond := cond); try tauto.
                simpl.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - assert (JUMP_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply jump_sem with (v := v); try tauto.
                simpl.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - assert (POP_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply pop_sem with (v := v); try tauto.
                simpl.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - assert (ADD_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply add_sem with (v1 := v1) (v2 := v2) (l := l0); try simpl; try tauto.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - assert (MUL_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply mul_sem with (v1 := v1) (v2 := v2) (l := l0); try simpl; try tauto.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - assert (SUB_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply sub_sem with (v1 := v1) (v2 := v2) (l := l0); try simpl; try tauto.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - congruence.
            - congruence.
            - assert (PUSH32_sem v last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply push32_sem; try simpl; try tauto.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
          }
    }
    destruct H15.
    destruct H17.
    exists last_mem.
    assert (first_CPU_state' = first_CPU_state).
    {
      rewrite H20 in H2. Search app.
      rewrite <- app_comm_cons in H2.
      inversion H2.
      tauto.
    }
    rewrite H19 in H17.
    inversion H17.
    split.
    {
      rewrite ! last_length.
      lia.
    }
    clear H19 H27 H28 H29 H30 l0 x0 y z.
    apply and_comm.
    split; try tauto.
    clear H18 H13.
    apply sigma; try auto.
    {
      clear H22 H23 H24 H26.
      inversion H4.
      - symmetry in H18; apply app_eq_nil in H18; inversion H18; discriminate.
      - symmetry in H13; apply app_eq_unit in H13.
        inversion H13.
        + inversion H19.
          apply length_zero_iff_nil in H22.
          rewrite H22 in H15.
          apply action_CPU_trace_len_cons in H9.
          rewrite H22 in H9.
          apply length_one_iff_single in H9.
          inversion H9.
          rewrite H24.
          apply length_zero_iff_nil in H15.
          rewrite H15.
          simpl.
          apply ActionListSingle.
          simpl.
          apply H18.
        + inversion H19.
          discriminate.
      - rewrite H21.
        apply app_inj_tail in H13.
        inversion H13.
        rewrite <- H22 in H25.
        apply action_CPU_trace_len_cons in H9.
        rewrite H21 in H9.
        rewrite last_length in H9.
        apply eq_add_S in H9.
        rewrite <- H22 in H9.
        destruct rm_last_CPU_trace'.
        + simpl in H9.
          symmetry in H9.
          apply length_zero_iff_nil in H9.
          apply app_eq_nil in H9.
          inversion H9.
          discriminate.
        + destruct mem_list'.
          * rewrite <- H22 in H15.
            symmetry in H15.
            simpl in H15.
            apply length_zero_iff_nil in H15.
            apply app_eq_nil in H15.
            inversion H15.
            discriminate.
          * specialize (cons_app_eq c rm_last_CPU_trace').
            intros. destruct H24. destruct H24.
            specialize (cons_app_eq i mem_list').
            intros. destruct H26. destruct H26.
            rewrite H24, H26 in H25.
            rewrite H24, H26.
            assert (Datatypes.length (x2 ++ [x1]) =
                Datatypes.length (x4 ++ [x3])).
            {
              rewrite H22 in H9.
              rewrite <- H9 in H15.
              rewrite <- H24. rewrite <- H26.
              rewrite H15.
              tauto.
            }
            assert (Datatypes.length
            (combine (x2 ++ [x1]) (x4 ++ [x3])) =
            Datatypes.length (l0 ++ [x0])).
            {
              apply len_combine in H27.
              rewrite <- H27.
              rewrite <- H26.
              rewrite H22.
              apply H15.
            }
            assert (Datatypes.length
            (combine [last_CPU_state'] [last_mem']) =
            Datatypes.length [y]).
            {
              assert (length [last_CPU_state'] = length [last_mem']).
              { tauto. }
              apply len_combine in H29.
              rewrite <- H29.
              tauto.
            }
            assert (Datatypes.length x2 = Datatypes.length x4).
            {
              rewrite ! app_length in H27.
              simpl in H27.
              lia.
            }
            assert (Datatypes.length [x1] = Datatypes.length [x3]).
            {
              tauto.
            }
            assert (Datatypes.length (combine x2 x4) =
            Datatypes.length l0).
            {
              rewrite combine_app in H28; try tauto.
              rewrite ! app_length in H28.
              apply len_combine in H31.
              rewrite <- H31 in H28.
              simpl in H28.
              lia.
            }
            assert (Datatypes.length (combine [x1] [x3]) =
            Datatypes.length [x3]).
            {
              apply len_combine in H31.
              rewrite <- H31.
              tauto.
            }
            unfold combine_to_act_state_list.
            rewrite combine_app; try tauto.
            rewrite combine_app; try tauto.
            rewrite map_app; try tauto.
            rewrite combine_app; try tauto.
            rewrite combine_app; try tauto.
            rewrite map_app.
            apply ActionListCons; try tauto.
            rewrite <- H22 in H17.
            rewrite H24 in H17.
            rewrite H26 in H17.
            unfold combine_to_act_state_list in H17.
            rewrite combine_app in H17; try tauto.
            rewrite combine_app in H17; try tauto.
            rewrite map_app in H17.
            simpl in H17.
            inversion H17. subst.
            apply H37.
      (* Increasing_timestamp *)
    }
    {
      clear H22 H23 H24 H25.
      (* eval_ins_list_single *)
      rewrite H21.
      pose proof (rt_trans_n1 (eval_ins_list_single program)).
      assert ((combine_to_pc_state first_CPU_state first_mem',
      combine_to_act_state_list (rm_last_CPU_trace' ++ [last_CPU_state'])
      (mem_list' ++ [last_mem']) (l ++ [x]),
      combine_to_pc_state last_CPU_state last_mem)
      ∈ clos_refl_trans (eval_ins_list_single program)
      ∘ eval_ins_list_single program).
      {
        simpl.
        exists (combine_to_pc_state last_CPU_state' last_mem').
        exists (combine_to_act_state_list rm_last_CPU_trace' mem_list' l).
        exists (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x]).
        split.
        - assert (combine_to_act_state_list rm_last_CPU_trace' mem_list' l ++
          combine_to_act_state_list [last_CPU_state'] [last_mem'] [x] =
          combine_to_act_state_list (rm_last_CPU_trace' ++ [last_CPU_state'])
          (mem_list' ++ [last_mem']) (l ++ [x])).
          {
            unfold combine_to_act_state_list.
            unfold combine_to_act_state.
            rewrite <- map_app.
            assert (combine (combine rm_last_CPU_trace' mem_list') l ++
            combine (combine [last_CPU_state'] [last_mem']) [x] =
            combine (combine (rm_last_CPU_trace' ++ [last_CPU_state']) (mem_list' ++ [last_mem'])) (l ++ [x])).
            {
              (* combine property, correct only when
              rm_last_CPU_trace, mem_list and action_trace have the same length,
              which need a lemma to prove it *)
              assert (length rm_last_CPU_trace' = length mem_list').
              { 
                assert (length rm_last_CPU_trace' = length l).
                {
                  assert (length rm_last_CPU_trace = S (length l)).
                  {
                    apply action_CPU_trace_len_cons.
                    apply H9.
                  }
                  rewrite H21 in H18.
                  simpl in H18.
                  rewrite last_length in H18.
                  injection H18.
                  intros. apply H19.
                }
                rewrite H15.  apply H18.
              }
              rewrite ! combine_app; try tauto.
              apply len_combine in H18.
              rewrite <- H18.
              tauto.
            }
            rewrite H18.
            reflexivity.
          }
          apply H18.
        - split.
          + simpl.
            inversion H17. apply H24.
          + apply H16.
      }
      apply H13 in H18. apply H18.
    }
Qed.
