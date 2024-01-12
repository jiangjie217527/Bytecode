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
Require Import Lemma. Import Lemma.

Local Open Scope string.
Local Open Scope sets.
Local Open Scope list.

Import Int256.
Import Lang.
Import program_state.
Import CPU_state.
Import pc_state.
Import act_state.

(*
Lemma fold_right_sem_right:
  forall (p:list ins) (last_two_CPU last_CPU:CPU_state) (rm_last_two_CPU:list CPU_state)(last_two_mem last_mem:int256->int256)(y:act_state),
  fold_right (fun (x y : pc_state -> list act_state -> pc_state -> Prop) (a : pc_state) (a0 : list act_state) (a1 : pc_state) => x a a0 a1 \/ y a a0 a1)
        (fun (_ : pc_state) (_ : list act_state) (_ : pc_state) => False) (map eval_ins (combine p (seq 0 (Datatypes.length (p))))) (combine_to_pc_state last_two_CPU last_two_mem) [y] (combine_to_pc_state last_CPU last_mem)->
        multiset_constraint (rm_last_two_CPU++[last_two_CPU;last_CPU]) p->
         (exists (id:nat)(i:ins),id= last_two_CPU.(pc)/\i = nth id p POP/\eval_ins (i,id) (combine_to_pc_state last_two_CPU last_two_mem) [y] (combine_to_pc_state last_CPU last_mem)).
Proof.
  intros p.
  (*apply rev_ind with (l:= p).*)
  induction p.
  + intros.
      inversion H.
   + intros.
   Print fold_left_rev_right.
   (*
   pose proof fold_left_rev_right (fun
          (x y : pc_state -> list act_state -> pc_state -> Prop)
          (a : pc_state) (a0 : list act_state) 
          (a1 : pc_state) => x a a0 a1 \/ y a a0 a1) (rev(map eval_ins (combine (l ++ [x]) (seq 0 (Datatypes.length (l ++ [x])))))) (fun (_ : pc_state) (_ : list act_state) (_ : pc_state)
        => False).
   Search (rev(rev ?l)).
   pose proof rev_involutive (map eval_ins (combine (l ++ [x]) (seq 0 (Datatypes.length (l ++ [x]))))).
   rewrite H3 in H2;clear H3.
   rewrite H2 in H0;clear H2.
   pose proof rev_ind_ins l x.
         
   rewrite H2 in H0.
         pose proof fold_right_sem (a :: p) (combine_to_pc_state last_two_CPU last_two_mem) (combine_to_pc_state last_CPU last_mem) y 0 H.
   *)
   simpl in H.
   destruct H.
      inversion H0;clear H0.
   simpl in H0.
   destruct a.
       destruct H0.
      - admit.
      (*
      symmetry in H2.
      pose proof map_eq_nil (fun cpu_state : CPU_state =>
        (cpu_state.(inst), cpu_state.(pc))) (rm_last_two_CPU ++ [last_two_CPU; last_CPU]) H2;clear H2.
      pose proof app_eq_nil rm_last_two_CPU [last_two_CPU; last_CPU] H0.
      destruct H3;inversion H6.
      *)
      - destruct H.
      * exists 0, a.
       destruct a;
        inversion H;clear H;simpl in *;subst.
        **
           rewrite H11 in H1;
           split.
           symmetry in H1.
           tauto.
           split.
           tauto.
           apply jumpi_sem with (dest:=dest)(cond:=cond) ;tauto.
      ** 
           rewrite H11 in H1;
           split.
           symmetry in H1.
           tauto.
           split.
           tauto.
           apply jump_sem with (v:=v) ;tauto.
    ** 
       rewrite H11 in H1;
       split.
       symmetry in H1.
       tauto.
       split.
       tauto.
       apply pop_sem with (v:=v);tauto.
   **
       rewrite H11 in H1;
       split.
       symmetry in H1.
       tauto.
       split.
       tauto.
       apply add_sem with (v1:=v1)(v2:=v2)(l:=l0);tauto.
   **
       rewrite H11 in H1;
       split.
       symmetry in H1.
       tauto.
       split.
       tauto.
       apply mul_sem with (v1:=v1)(v2:=v2)(l:=l0);tauto.
       **
       rewrite H11 in H1;
       split.
       symmetry in H1.
       tauto.
       split.
       tauto.
       apply sub_sem with (v1:=v1)(v2:=v2)(l:=l0);tauto.
       **
       rewrite H10 in H1;
       split.
       symmetry in H1.
       tauto.
       split.
       tauto.
       apply mload_sem with (offset:=offset)(l:=l0);tauto.
       **
       rewrite H10 in H1;
       split.
       symmetry in H1.
       tauto.
       split.
       tauto.
       apply mstore_sem with (offset:=offset)(v:=v);tauto.
       **
       rewrite H11 in H1;
       split.
       symmetry in H1.
       tauto.
       split.
       tauto.
       apply push32_sem with (v:=v);tauto.
     * specialize (IHp last_two_CPU last_CPU rm_last_two_CPU last_two_mem last_mem y) .
       
      destruct a ;destruct x; inversion H;simpl in H;subst;simpl in *;subst;try tauto.
      - specialize ( IHp x z y (S n)).
       pose proof IHp H.
       tauto.
*)

Lemma eval_ins_list_first:
  forall (p:list ins)(x z:pc_state)(first_CPU last_CPU:CPU_state)(rm_first_last_CPU:list CPU_state) (first_aciton:action_type )(rm_first_action:list action_type)(first_mem:(int256->int256))(rm_first_mem:list(int256->int256)),
  eval_ins_list p x (combine_to_act_state_list (first_CPU::rm_first_last_CPU) (first_mem::rm_first_mem)(first_aciton::rm_first_action)) z ->
  (exists (y:pc_state),eval_ins_list p y (combine_to_act_state_list rm_first_last_CPU rm_first_mem rm_first_action) z).
Proof.
  intros.
  inversion H;clear H;simpl in *;subst.
  destruct H4.
  destruct x0;simpl in H;sets_unfold in H;destruct H.
  
  unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H.
  inversion H;clear H;simpl in *;subst.
  rename x1 into y0.
  destruct H as [a1 [a2 [? [? ?]]]].
  exists y0.
  Admitted.


Lemma mem_is_zero:
  forall (p:list ins) (action_trace :list action_type)
( last_CPU_state:CPU_state)(rm_last_CPU_trace:list CPU_state)(last_mem : int256 -> int256) ,
(exists
              (mem_list : list (int256 -> int256)) ,
              Datatypes.length mem_list =
              Datatypes.length action_trace /\
              eval_ins_list p {|
          pc_state.pc := 0;
          pc_state.state :=
            {|
              memory := fun _ : int256 => zero;
              program_state.stack := []
            |}
        |}
                (combine_to_act_state_list
                   rm_last_CPU_trace mem_list
                   action_trace)
                (combine_to_pc_state last_CPU_state
                   last_mem))->
     filter mem_ins_type_is_not_non action_trace = [] -> 
     action_trace_constraint (rm_last_CPU_trace++[last_CPU_state]) action_trace ->
     length rm_last_CPU_trace = length action_trace ->
     last_mem = fun _ : int256 => zero.
     
Proof.
  intros p action_trace.
  revert p.
  apply rev_ind with (l:= action_trace).
  + intros.
      (*后补条件*)
      rename H2 into G.
      (*后补条件结束*)
      destruct H as [? [? ?]].
                  unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H2.
                  unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H1.
      simpl in H2.
      pose proof length_zero_iff_nil x.
      simpl in H.
      destruct H3.
      clear H4;pose proof H3 H.
      subst;clear H3 H H0 H1.
      assert (
      
      @Logic.eq
    (list (prod (prod CPU_state (forall _ : int, int))action_type))
    (@combine (prod CPU_state (forall _ : int, int))
       action_type
       (@combine CPU_state (forall _ : int, int) rm_last_CPU_trace
          (@Datatypes.nil (forall _ : int, int)))
       (@Datatypes.nil action_type))
    (@Datatypes.nil
       (prod (prod CPU_state (forall _ : int, int))
          action_type))
      ).
      {
          pose proof combine_nil (A:=CPU_state * (int256 -> int256)). 
          specialize (H (action_type) (@combine CPU_state (forall _ : int, int) rm_last_CPU_trace
          (@Datatypes.nil (forall _ : int, int)))).
          tauto.
      }
      rewrite H in H2.
      simpl in H2.
      inversion H2;clear H2;simpl in *;subst.
      clear H0 H1 H3 H4 H.
      destruct H5.
      destruct x.
      simpl in H;sets_unfold in H;destruct H;clear H.
      inversion H0;clear H0.
      symmetry in H2;tauto.
      simpl in H;sets_unfold in H.
      destruct H as[? [? [? [? [? ?]]]]].
      pose proof app_eq_nil x1 x2 H.
      destruct H2;subst. clear H H1.
      pose proof one_step_generate_one_action {|
           pc_state.pc := 0;
           pc_state.state :=
             {|
               memory := fun _ : int256 => zero;
               program_state.stack := []
             |}
         |} x0 (@nil act_state) p 0.
     inversion H0;clear H0;subst.
     unfold fold_ins_sem in H1.
     sets_unfold in H1.
     pose proof H H1.
     inversion H0.
   + intros.
       rename l into rm_last_action.
       rename x into last_action.
       destruct H0 as [mem_list [? ?]].
       pose proof last_length rm_last_action last_action.
       rewrite H5 in H0.
       pose proof len_succ mem_list (Datatypes.length rm_last_action) (ltac:(symmetry in H0;tauto)).
       destruct H6 as [first_mem [rm_first_mem ?]].
       rewrite H6 in H4.
       rewrite H5 in H3;clear H5.
       pose proof len_succ rm_last_CPU_trace (Datatypes.length rm_last_action) (ltac:(symmetry in H3;tauto)).
       destruct H5 as [first_CPU_trace [rm_first_last_CPU_trace ?]].
       rewrite H5 in H4.
       rewrite H5 in H3;simpl in H3.
       inversion H3;clear H3.
       rewrite H6 in H0;simpl in H0;inversion H0;clear H0.
       
       pose proof cons_app_eq first_CPU_trace rm_first_last_CPU_trace.
       destruct H0 as [last_two_2_CPU_state [rm_last_two_CPU_trace ?]].
       pose proof cons_app_eq first_mem rm_first_mem.
       destruct H3 as [last_two_mem [rm_last_two_mem ?]].
       Search (filter ?P (?l++[?x])).
       pose proof filter_cons_app_single mem_ins_type_is_not_non rm_last_action last_action.
       rewrite H9 in H1;clear H9.
       Search (?l++?l'=[]).
       pose proof app_eq_nil (filter mem_ins_type_is_not_non rm_last_action) (filter mem_ins_type_is_not_non [last_action]) H1;clear H1.
       destruct H9.
       simpl in H9.
       assert (last_action.(mem_ins)=non).
       {
        destruct last_action.
        destruct mem_ins0;simpl in H9.
        + discriminate.
        + discriminate.
        + tauto.
       }
       clear H9.
       specialize (H p last_two_2_CPU_state rm_last_two_CPU_trace last_two_mem).
       
       assert (
       (exists mem_list : list (int256 -> int256),
       Datatypes.length mem_list =
       Datatypes.length rm_last_action /\
       eval_ins_list p
         {|
           pc_state.pc := 0;
           pc_state.state :=
             {|
               memory := fun _ : int256 => zero;
               program_state.stack := []
             |}
         |}
         (combine_to_act_state_list rm_last_two_CPU_trace
            mem_list rm_last_action)
         (combine_to_pc_state last_two_2_CPU_state
            last_two_mem))
       ).
       {
        exists rm_last_two_mem.
        split.
        + pose proof cons_app_length (rm_first_mem) (rm_last_two_mem) first_mem last_two_mem H3.
        lia.
        + rewrite H3 in H4.
            rewrite H0 in H4.
            (*eval_ins_list*)
            inversion H4;clear H4;simpl in *;subst.
            clear H9 H11 H12.
            destruct H14.
            
            Check nsteps_nsteps'.
            pose proof nsteps_nsteps' (eval_ins_list_single p) x.
            sets_unfold in H5.
            remember {|
         pc_state.pc := 0;
         pc_state.state :=
           {|
             memory := fun _ : int256 => zero;
             program_state.stack := []
           |}
       |} as pc1.
            specialize (H5 pc1        (combine_to_act_state_list
          (rm_last_two_CPU_trace ++ [last_two_2_CPU_state])
          (rm_last_two_mem ++ [last_two_mem])
          (rm_last_action ++ [last_action]))
       (combine_to_pc_state last_CPU_state last_mem)).
       destruct H5.
       clear H6; pose proof H5 H4;clear H5 H4.
       destruct x.
       simpl in H6;sets_unfold in H6;destruct H6.
          pose proof cons_app_length (rm_first_mem) (rm_last_two_mem) first_mem last_two_mem H3.
          pose proof cons_app_length rm_first_last_CPU_trace rm_last_two_CPU_trace first_CPU_trace last_two_2_CPU_state H0.
      pose proof combine_act_app last_two_2_CPU_state rm_last_two_CPU_trace last_two_mem rm_last_two_mem last_action rm_last_action (ltac:(lia))(ltac:(lia)).
       rewrite H11 in H4. 
       pose proof app_eq_nil (combine_to_act_state_list rm_last_two_CPU_trace rm_last_two_mem
       rm_last_action) (combine_to_act_state_list [last_two_2_CPU_state] [ last_two_mem] [ last_action]) H4.
       destruct H12.
       discriminate.
       (*one bad situation*)
       simpl in H6;sets_unfold in H6;destruct H6 as [? [? [? [? [? ?]]]]].
       pose proof nsteps_nsteps' (eval_ins_list_single p) x.
       sets_unfold in H9.
       specialize (H9 pc1 x1 x0).
       destruct H9.
       clear H9.
       pose proof H11 H5;clear H5 H11.
       Search Increasing_timestamp.
       inversion H4;clear H4;simpl in *;subst.
                 pose proof cons_app_length (rm_first_mem) (rm_last_two_mem) first_mem last_two_mem H3.
          pose proof cons_app_length rm_first_last_CPU_trace rm_last_two_CPU_trace first_CPU_trace last_two_2_CPU_state H0.
             pose proof combine_act_app last_two_2_CPU_state rm_last_two_CPU_trace last_two_mem rm_last_two_mem last_action rm_last_action (ltac:(lia))(ltac:(lia)).
             rewrite H12 in H11.
     apply sigma with (l:=p)(x:=  {|
    pc_state.pc := 0;
    pc_state.state :=
      {|
        memory := fun _ : int256 => zero;
        program_state.stack := []
      |}
  |})(y:=  (combine_to_act_state_list rm_last_two_CPU_trace
     rm_last_two_mem rm_last_action))(z:=  (combine_to_pc_state last_two_2_CPU_state last_two_mem)).
     - tauto.
     - tauto.
     - tauto.
     - rewrite H12 in H13.
       pose proof single_act_state last_two_2_CPU_state
           last_two_mem last_action (      combine_to_act_state_list [last_two_2_CPU_state] [last_two_mem] [last_action])(ltac:(tauto)).
      pose proof length_one_iff_single (combine_to_act_state_list [last_two_2_CPU_state] [last_two_mem] [last_action]).
      destruct H15.
      clear H16;pose proof H15 H14;clear H15 H14.
      destruct H16.
      rewrite H14 in H13.
       pose proof Increasing_timestamp_subst
        (combine_to_act_state_list rm_last_two_CPU_trace
     rm_last_two_mem rm_last_action) x3 H13.
     tauto.
    - simpl.
      exists x.
      inversion H6;clear H6;simpl in *;subst.
      unfold fold_ins_sem in H14;sets_unfold in H14.
      pose proof one_step_generate_one_action x0 (combine_to_pc_state last_CPU_state last_mem) x2 p 0 H14.
      pose proof length_one_iff_single x2.
      destruct H15;clear H16.
      pose proof H15 H6;clear H6 H15.
      destruct H16;subst.
             pose proof single_act_state last_two_2_CPU_state
           last_two_mem last_action (      combine_to_act_state_list [last_two_2_CPU_state] [last_two_mem] [last_action])(ltac:(tauto)).
                 pose proof length_one_iff_single (combine_to_act_state_list [last_two_2_CPU_state] [last_two_mem] [last_action]).
       destruct H15;clear H16.
       pose proof H15 H6;clear H15 H6.
       destruct H16.
       rewrite H6 in H11.
      pose proof app_inj_tail x1 (combine_to_act_state_list rm_last_two_CPU_trace
        rm_last_two_mem rm_last_action) x3 x2 H11.
        destruct H15;subst.
      pose proof fold_right_sem p x0 (combine_to_pc_state last_CPU_state last_mem) x2 0 H14.
      destruct H15;subst.
                  unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H6.
      simpl in H6.
      inversion H6;clear H6.
                        unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state.
    assert (x0={|
    pc_state.pc := last_two_2_CPU_state.(pc);
    pc_state.state :=
      {|
        memory := last_two_mem;
        program_state.stack :=
          last_two_2_CPU_state.(stack)
      |}
  |}).
  {
    destruct x0.
    simpl in *.
    rewrite H15.
        rewrite H16.
    destruct x2.
    inversion H18;clear H18;simpl in *;subst.
    tauto.
  }
  rewrite H6 in H9.
                    unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H9.
      tauto.
 }
  pose proof action_trace_constraint_app rm_last_CPU_trace last_CPU_state rm_last_action last_action H2.
  rewrite H5 in H11.
  rewrite H0 in H11.
          pose proof cons_app_length (rm_first_mem) (rm_last_two_mem) first_mem last_two_mem H3.
          pose proof cons_app_length rm_first_last_CPU_trace rm_last_two_CPU_trace first_CPU_trace last_two_2_CPU_state H0.
 pose proof H H9 H1 H11 (ltac:(lia)).
 clear H.
 
   inversion H4;clear H4;simpl in *;subst.
  clear H H15 H16.
  destruct H18.
  destruct x.
simpl in H;sets_unfold in H;destruct H.
rewrite H0 in H.
rewrite H3 in H.

      pose proof combine_act_app last_two_2_CPU_state rm_last_two_CPU_trace (fun _ : int256 => zero) rm_last_two_mem last_action rm_last_action (ltac:(lia))(ltac:(lia)).
       rewrite H5 in H. 
       pose proof app_eq_nil (combine_to_act_state_list rm_last_two_CPU_trace rm_last_two_mem
       rm_last_action) (combine_to_act_state_list [last_two_2_CPU_state] [ (fun _ : int256 => zero)] [ last_action]) H.
       destruct H6.
       discriminate.
       pose proof nsteps_nsteps' (eval_ins_list_single p) (S x).
       rename H4 into H6.
       sets_unfold in H6.
       specialize (H6 {|
        pc_state.pc := 0;
        pc_state.state :=
          {|
            memory := fun _ : int256 => zero;
            program_state.stack := []
          |}
      |} (combine_to_act_state_list
         (first_CPU_trace :: rm_first_last_CPU_trace)
         (first_mem :: rm_first_mem)
         (rm_last_action ++ [last_action])) (combine_to_pc_state last_CPU_state last_mem)).
       destruct H6.
       clear H5.
       pose proof H4 H;clear H4 H.
        simpl in H5;sets_unfold in H5;destruct H5 as [? [? [? [? [? ?]]]]].
  rewrite H3 in H.
    rewrite H0 in H.
   pose proof combine_to_act_state_list_app rm_last_two_CPU_trace rm_last_two_mem rm_last_action last_two_2_CPU_state (fun _ : int256 => zero) last_action (ltac:(lia))(ltac:(lia)).
   rewrite H6 in H.
   inversion H5;clear H5;simpl in *;subst.
   unfold fold_ins_sem in H14; sets_unfold in H14.
   pose proof one_step_generate_one_action x0 (combine_to_pc_state last_CPU_state last_mem) x2 p 0 H14.
   pose proof length_one_iff_single x2.
   destruct H15.
   clear H16;pose proof H15 H5;clear H15 H5.
   destruct H16;subst.
   Search (combine_to_act_state_list).
   pose proof single_act_state last_two_2_CPU_state (fun _ : int256 => zero) last_action (combine_to_act_state_list [last_two_2_CPU_state]
      [fun _ : int256 => zero] [last_action]) (ltac:(tauto)).
      pose proof length_one_iff_single (combine_to_act_state_list [last_two_2_CPU_state]
          [fun _ : int256 => zero] [last_action]).
   destruct H15.
   clear H16;pose proof H15 H5;clear H15 H5.
   destruct H16;subst.
   rewrite H5 in H.
   pose proof app_inj_tail x1 (combine_to_act_state_list rm_last_two_CPU_trace rm_last_two_mem rm_last_action) x3 (x2) H.
   destruct H15;subst.
   clear H.
   Print fold_right.
   Search fold_right.
   inversion H2;clear H2;simpl in *.
   inversion H.
   symmetry in H20.
   pose proof app_eq_nil rm_last_action [last_action] H20.
   destruct H2.
   inversion H21.
   pose proof app_inj_tail (l ++ [x1]) (first_CPU_trace :: rm_first_last_CPU_trace) y last_CPU_state H2.
      pose proof app_inj_tail l_action rm_last_action action0 last_action H18.
      destruct H21. destruct H22. subst.
      inversion H19;clear H19.
      rewrite H10 in H16.
      inversion H16.
            rewrite H10 in H16.
      inversion H16.
      subst.
      clear H18.
      rewrite H0 in H21.
      inversion H21;clear H21.
      Search (?l++[?x]).
      pose proof app_inj_tail l rm_last_two_CPU_trace x1 last_two_2_CPU_state H19.
      destruct H18;subst. clear H19 H2.
      destruct H9 as [mem_list [? ?]].
      destruct last_two_2_CPU_state.(inst).
      - Search x0.
Admitted.

Lemma exists_memory_trace:
  forall (mem_trace0 action_trace0:list action_type)(last_action last_two_action:action_type)(CPU_trace0:list CPU_state) (last_two_CPU_state last_CPU_state first_CPU_state:CPU_state) (p:list ins) (last_two_mem last_mem:int256->int256), 
  (exists
              (mem_list : list (int256 -> int256)) 
            (first_mem last_mem : int256 -> int256),
              Datatypes.length mem_list =
              Datatypes.length action_trace0 /\
              eval_ins_list p (combine_to_pc_state first_CPU_state
                   first_mem)
                (combine_to_act_state_list
                   CPU_trace0 mem_list
                   action_trace0)
                (combine_to_pc_state last_two_CPU_state
                   last_mem))->
  memory_constraint mem_trace0 -> 
action_trace_constraint (CPU_trace0++[last_two_CPU_state]) (action_trace0++[last_two_action]) ->
Permutation (filter mem_ins_type_is_not_non (action_trace0++[last_two_action])) mem_trace0 ->
CPU_trace_constraint (CPU_trace0++[last_two_CPU_state]) ->
List.fold_right Sets.union ∅
      (map eval_ins
         (combine p  (seq 0 (Datatypes.length p))))      {|
        pc_state.pc := last_two_CPU_state.(pc);
        pc_state.state :=
          {|
            memory := last_two_mem;
            program_state.stack :=
              last_two_CPU_state.(stack)
          |}
      |}
      (map
         (fun
            x : CPU_state * (int256 -> int256) *
                action_type =>
          {|
            pc := (fst (fst x)).(pc);
            state :=
              {|
                memory := snd (fst x);
                program_state.stack :=
                  (fst (fst x)).(stack)
              |};
            action := snd x
          |})
         [(last_two_CPU_state, last_two_mem,
          last_action)])
      {|
        pc_state.pc := last_CPU_state.(pc);
        pc_state.state :=
          {|
            memory := last_mem;
            program_state.stack := last_CPU_state.(stack)
          |}
      |} ->
  (last_action.(mem_ins)=non -> exists (mem_trace1:list action_type),mem_trace1 = mem_trace0)\/(
  forall (add val:int256),(last_action.(mem_ins) = read add val)\/((last_action.(mem_ins) = write add val)) -> (exists (mem_trace1:list action_type), mem_trace1 = last_action::mem_trace0/\memory_constraint mem_trace1)\/ (exists (a:action_type) (l1 l2:list action_type),mem_trace0 = l1 ++[a] ++l2 ->exists (mem_trace1:list action_type), mem_trace1 = l1 ++[a]++[last_action]++l2/\ memory_constraint mem_trace1)).
Proof.
  intros mem_trace0.
  induction mem_trace0.
  + intros.
      destruct last_action.
      destruct mem_ins0.
      - right.
        intros.
        subst.
        inversion H5;inversion H6;subst;clear H5 H6.
        pose proof Permutation_sym H2.
        pose proof Permutation_nil H5;clear H5 H2.
        left.
        exists [{|
     timestamp := timestamp0;
     mem_ins := read add0 val
   |}] .
        split. tauto.
        destruct H as [mem_list [first_mem [rm_last_mem [? ?]]]].
        inversion H2;clear H2;subst.
        simpl in *;subst.
        inversion H1;clear H1;subst.
        inversion H2. 
        destruct action_trace0;simpl in H11; inversion H11.
        pose proof app_last_corr l_action action_trace0 action0 last_two_action H7. clear H7.
        destruct H13;subst.
        pose proof app_last_corr (l++[x]) CPU_trace0 y last_two_CPU_state H1. clear H1.
        destruct H7;subst.
           pose proof filter_cons_app_single mem_ins_type_is_not_non action_trace0 last_two_action.
           rewrite H1 in H6;clear H1.
        inversion H11;clear H11;subst;destruct last_two_action;    simpl in H7;subst;simpl in H6.
        * (*--MLOAD---*)
         destruct (filter mem_ins_type_is_not_non action_trace0);simpl in H6;discriminate.
        *  (*---MSTORE---*)
         destruct (filter mem_ins_type_is_not_non action_trace0);simpl in H6;discriminate.
         * simpl in H13.
            subst.
            inversion H12;clear H12.
            ++ symmetry in H13.
                  pose proof app_after_nil_1 l x x0 H13.
                  subst.
                  simpl in H13.
                  inversion H13;clear H13;subst.
                  unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H10.
                  unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H10.
                  simpl in *.
                  pose proof length_zero_iff_nil mem_list.
                  destruct H11. clear H12.
                  pose proof H11 H. clear H.
                  subst.
                  simpl in H10.
                  destruct H10 as[n ?].
                  destruct n.
                  -- simpl in H;sets_unfold in H.
                      destruct H.
                      inversion H10;clear H10.
                      subst.
                      rewrite H5 in H13.
                      rewrite H8 in H15.
                      symmetry in H13,H15.
                      subst;clear H H6.
                      rewrite H13 in H4.
                      rewrite H15 in H4.
                      unfold List.fold_right in H4;sets_unfold in H4.
                      destruct p.
                      ** simpl in H4.
                           contradiction.
                      ** simpl in H4.
                          destruct H4.
                          {
                            destruct i.
                            + inversion H;clear H;simpl in *;subst.
                                inversion H10.
                            + inversion H;clear H;simpl in *;subst.
                                inversion H10.
                             + inversion H;clear H;simpl in *;subst.
                                inversion H10.
                              + inversion H;clear H;simpl in *;subst.
                                inversion H10.
                           + inversion H;clear H;simpl in *;subst.
                                inversion H10.
                            + inversion H;clear H;simpl in *;subst.
                                inversion H10.
                            + inversion H;clear H;simpl in *;subst.
                                inversion H16.   
                            + inversion H;clear H;simpl in *;subst.
                                inversion H16.
                            + inversion H;clear H;simpl in *;subst.
                                inversion H10.        
                          }
                          pose proof out_is_false p 
{|
        pc_state.pc := last_CPU_state.(pc);
        pc_state.state :=
          {|
            memory := last_mem;
            program_state.stack := last_CPU_state.(stack)
          |}
      |} {|
         pc := 0;
         state :=
           {|
             memory := last_two_mem; program_state.stack := []
           |};
         action :=
           {|
             timestamp := timestamp0; mem_ins := read add0 val
           |}
       |} last_two_mem H.
       contradiction.
                  -- simpl in H;sets_unfold in H.
                      destruct H as [?[?[?[? [? ?]]]]].
                      pose proof one_step_generate_one_action {|
          pc_state.pc := first_CPU_state.(pc);
          pc_state.state :=
            {|
              memory := fun _ : int256 => zero;
              program_state.stack := first_CPU_state.(stack)
            |}
        |} x x1 p 0.
        inversion H10;clear H10;subst.
        unfold fold_ins_sem in H14.
        sets_unfold in H14;simpl in H14.
        pose proof H13 H14.
        pose proof H.
        {
          destruct x1.
          + inversion H10.
          + simpl in H15;inversion H15.
        }
        ++ simpl in H6.
Admitted.

(*below are failed*)

Lemma nsteps_last:
  forall (p:list ins)(n:nat) (s1 s3:pc_state) (rm_last_CPU_trace:list CPU_state)(last_C:CPU_state) (rm_last_m:list (int256->int256))(last_m:(int256->int256))(rm_last_a:list action_type) (last_a:action_type), nsteps (eval_ins_list_single p) (S n) s1 (map
          (fun x : CPU_state * (int256 -> int256) * action_type =>
           {|
             pc := (fst (fst x)).(pc);
             state :=
               {|
                 memory := snd (fst x);
                 program_state.stack := (fst (fst x)).(stack)
               |};
             action := snd x
           |}) (combine (combine (rm_last_CPU_trace++[last_C])(rm_last_m++[last_m]) ) (rm_last_a++[last_a]))) s3 -> 
           length rm_last_a = length rm_last_m->
           length rm_last_CPU_trace = length rm_last_m->
           nsteps (eval_ins_list_single p) n s1 (map
          (fun x : CPU_state * (int256 -> int256) * action_type =>
           {|
             pc := (fst (fst x)).(pc);
             state :=
               {|
                 memory := snd (fst x);
                 program_state.stack := (fst (fst x)).(stack)
               |};
             action := snd x
           |}) (combine (combine (rm_last_CPU_trace)(rm_last_m))  (rm_last_a)))
           (combine_to_pc_state last_C last_m)
           .
Proof.
    intros.
    destruct rm_last_CPU_trace.
   + simpl in H1.
      pose proof length_zero_iff_nil rm_last_m.
      destruct H2.
      clear H3.
      pose proof H2 (ltac:(symmetry in H1;tauto)).
      clear H2.
      rewrite <- H1 in H0.
      pose proof length_zero_iff_nil rm_last_a.
      destruct H2.
      clear H4.
      pose proof H2 H0.
      subst.
      simpl in H.
      sets_unfold in H.
      clear H1 H2 H0.
      destruct H as [? [? [? [? [? ?]]]]].
      inversion H0;clear H0;subst.
      unfold fold_ins_sem in H2.
      Check one_step_generate_one_action.
      pose proof one_step_generate_one_action s1 x x0 p 0 H2.
       assert (length (x0 ++ x1) = length ([{|
       pc := last_C.(pc);
       state := {| memory := last_m; program_state.stack := last_C.(stack) |};
       action := last_a
     |}])).
     {
          rewrite H.
          tauto.
      }
         simpl in H3.
         Search (length (?l ++?l')).
         pose proof app_length x0 x1.
         rewrite H4 in H3.
         rewrite H0 in H3.
         inversion H3;clear H3.
         Search (length ?l=0).
         pose proof length_zero_iff_nil x1.
         destruct H3;clear H5.
         pose proof H3 H6;clear H3 H6.
         subst.
         assert (n=0).
         {
            destruct n.
            + tauto.
            + simpl in H1.
                sets_unfold in H1.
               destruct H1 as [? [? [? [? [? ?]]]]].
               inversion H3;clear H3;subst.
               unfold fold_ins_sem in H6.
                pose proof one_step_generate_one_action x x1 x2 p 0 H6.
                assert(length (x2++x3)=0).
                {
                  rewrite H1.
                  tauto.
                }
                pose proof app_length x2 x3.
                rewrite H8 in H7.
                rewrite H3 in H7.
                discriminate.
         }
         subst.
        simpl.
        sets_unfold.
        split.
        - tauto.
        - pose proof app_nil_r x0 .
          rewrite H3 in H.
          subst.
          pose proof fold_right_s1
          p s1 x last_C  last_m last_a 0 H2.
          unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state.
          tauto.
     + pose proof cons_app_eq c rm_last_CPU_trace. 
        destruct H2 as [last_two_CPU [rm_first_last_CPU_trace ?]].
        assert (exists (last_two_m:(int256->int256))(last_two_a:action_type)(rm_first_last_m:list (int256->int256))(rm_first_last_a:list action_type), rm_last_m = rm_first_last_m++[last_two_m]/\rm_last_a = rm_first_last_a++[last_two_a]).
        { 
        admit.
        }
        destruct H3 as [? [? [? [? [? ?]]]]].
        subst.
        rewrite H2 in H.
        assert(nsteps (eval_ins_list_single p) 1 (combine_to_pc_state last_two_CPU x)  (map
         (fun x : CPU_state * (int256 -> int256) * action_type =>
          {|
            pc := (fst (fst x)).(pc);
            state :=
              {|
                memory := snd (fst x);
                program_state.stack := (fst (fst x)).(stack)
              |};
            action := snd x
          |}) (combine
            (combine ([last_C])
               ( [last_m])) ( [last_a]))) s3).
        {
           simpl.
           sets_unfold.
           Search nsteps.
           inversion H;clear H.
           simpl in H3;sets_unfold in H3.
          destruct H3 as [? [? [? [? ?]]]].
          exists s3,[{|
     pc := last_C.(pc);
     state := {| memory := last_m; program_state.stack := last_C.(stack) |};
     action := last_a
   |}],[].
          split.
          + tauto.
          + split.
             - inversion H3;clear H3;subst.
                unfold fold_ins_sem in H5.
                Check one_step_generate_one_action.
             pose proof one_step_generate_one_action s1 x3 x4 p 0 H5.
             Abort.
        }
        
        Lemma nsteps_3:
  forall (n:nat) (p:list ins) (s1 s3:pc_state) (rm_last_CPU_trace:list CPU_state)(last_C:CPU_state) (rm_last_m:list (int256->int256))(last_m:(int256->int256))(rm_last_a:list action_type) (last_a:action_type), nsteps (eval_ins_list_single p) (S n) s1 (map
          (fun x : CPU_state * (int256 -> int256) * action_type =>
           {|
             pc := (fst (fst x)).(pc);
             state :=
               {|
                 memory := snd (fst x);
                 program_state.stack := (fst (fst x)).(stack)
               |};
             action := snd x
           |}) (combine (combine (rm_last_CPU_trace++[last_C])(rm_last_m++[last_m]) ) (rm_last_a++[last_a]))) s3 -> 
           length rm_last_a = length rm_last_m->
           length rm_last_CPU_trace = length rm_last_m->
           nsteps (eval_ins_list_single p) n s1 (map
          (fun x : CPU_state * (int256 -> int256) * action_type =>
           {|
             pc := (fst (fst x)).(pc);
             state :=
               {|
                 memory := snd (fst x);
                 program_state.stack := (fst (fst x)).(stack)
               |};
             action := snd x
           |}) (combine (combine (rm_last_CPU_trace)(rm_last_m))  (rm_last_a)))
           (combine_to_pc_state last_C last_m)
           .
Proof.
  intros n.
  induction n.
  + intros.
     pose proof nsteps_one p s1 s3 rm_last_CPU_trace last_C 
rm_last_m last_m rm_last_a last_a H H0 H1;tauto.
  + intros.
     inversion H;clear H.
     simpl in H2;sets_unfold in H2.
     destruct H2 as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
     subst.
     remember (fun x : CPU_state * (int256 -> int256) * action_type =>
       {|
         pc := (fst (fst x)).(pc);
         state :=
           {|
             memory := snd (fst x);
             program_state.stack := (fst (fst x)).(stack)
           |};
         action := snd x
       |}) as f.
Abort.

Lemma soudnness_subst:
  forall (program : list ins) (inst0:ins)(first_CPU_state last_CPU_state last_two_2_CPU_state: CPU_state) ( rm_last_action_trace rm_first_action_trace: list action_type) (rm_last_two_CPU_trace rm_first_last_CPU_trace : list CPU_state) (first_action last_action:action_type),
           (exists
       (mem_list : list (int256 -> int256)) (first_mem
                                             last_mem : 
                                             int256 -> int256),
       Datatypes.length mem_list = Datatypes.length (first_action :: rm_first_action_trace) /\
       eval_ins_list (inst0 :: program)
         (combine_to_pc_state first_CPU_state first_mem)
         (combine_to_act_state_list (rm_last_two_CPU_trace++ [last_two_2_CPU_state]) mem_list (first_action :: rm_first_action_trace))
         (combine_to_pc_state last_CPU_state last_mem))->
  first_action :: rm_first_action_trace =
     rm_last_action_trace ++ [last_action]->
  first_CPU_state.(pc) = 0->
 first_CPU_state.(stack) = []
         -> 
         rm_last_two_CPU_trace ++ [last_two_2_CPU_state] =
     first_CPU_state :: rm_first_last_CPU_trace ->
     exists
       (mem_list : list (int256 -> int256)) (first_mem
                                             last_mem : 
                                             int256 -> int256),
       Datatypes.length mem_list = Datatypes.length rm_last_action_trace /\
       eval_ins_list (inst0 :: program)
         (combine_to_pc_state first_CPU_state first_mem)
         (combine_to_act_state_list    (rm_last_two_CPU_trace )  mem_list rm_last_action_trace)
         (combine_to_pc_state last_two_2_CPU_state last_mem)
     
.
Proof.
  intros.
  destruct H as [mem_list[in_list_first_mem [last_mem_list [? ?]]]].
  inversion H2;clear H2;subst.
    Search (eval_ins_list).
    Abort.