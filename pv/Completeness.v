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

Lemma app_after_nil_1: forall {A: Type}(l : list A) (x y:A),(l ++ [x]) = [y] -> l = [] .
Proof.
  intros.
   Search length (?l ++ ?[x]).
     pose proof app_length.
      specialize (H0 A l [x]).
      rewrite H in H0.
      simpl in H0.
      assert (length l = 0).
    {
        lia.
}
      Search (length ?l = 0).
      pose proof length_zero_iff_nil.
      specialize(H2 A l).
      destruct H2.
      clear H3.
      tauto.
Qed.

Lemma app_after_nil_2:forall {A: Type}(l : list A) (x y:A),(l ++ [x]) = [y] -> x=y.
Proof.
  intros.
  pose proof app_after_nil_1 l x y H.
  rewrite H0 in H.
  simpl in H.
  inversion H.
  tauto.
Qed.

Lemma app_last_corr:
  forall [A : Type] (l l' : list A) (y y' : A),
  l ++ [y] = l' ++ [y'] -> l = l' /\ y = y'.
Proof.
  intros.
  inversion H.
  split.
    + apply app_inj_tail in H. tauto.
    + apply app_inj_tail in H. tauto.
Qed.

Lemma cons_eq: forall {A : Type} (x : A) (l : list A), exists y l',  l ++ [x] = y:: l'.
Proof.
  intros.
  revert x.
  induction l. intros.
  - exists x, []. reflexivity.
  - intros. exists a, (l++[x]). reflexivity.
Qed.

Lemma filter_cons_app_single:
  forall [A: Type] (P : A -> bool) (l: list A) (x:A),
  filter P (l++[x]) = (filter P l) ++ (filter P [x]).
Proof.
  Print filter.
  induction l.
  + simpl.
   tauto.
  + simpl.
   intros.
   assert(a :: filter P (l ++ [x]) = a :: filter P l ++ (if P x then [x] else [])).
   { 
    specialize (IHl x).
    rewrite IHl.
    simpl.
    tauto.
  }
    assert(filter P (l ++ [x]) =filter P l ++ (if P x then [x] else [])).
   { 
    specialize (IHl x).
    rewrite IHl.
    simpl.
    tauto.
  }
  rewrite H.
  rewrite H0.
  destruct (P a).
  - tauto.
  - tauto.
Qed.

Lemma filter_cons_app:
  forall [A: Type] (P : A -> bool) (l l': list A) ,
  filter P (l++l') = (filter P l) ++ (filter P l').
Proof.
  intros.
  apply rev_ind with (l:= l').
  + simpl. 
     pose proof app_nil_r l.
     pose proof app_nil_r (filter P l).
     rewrite H.
     rewrite H0.
     tauto.
  + intros.
      pose proof  filter_cons_app_single P l0 x.
      rewrite H0.
      pose proof app_assoc (filter P l) (filter P l0)(filter P [x]).
      rewrite H1.
      rewrite <- H.
      pose proof app_assoc (l) (l0)([x]).
      rewrite H2.
      pose proof filter_cons_app_single P (l ++ l0) x.
      rewrite H3.
      tauto.
Qed.

Print Permutation.

Definition f :=
  fix f (l : list action_type):list action_type:=
  match l with
  | [] => []
  | x::l0 => f l0
  end.
Print f.

Inductive increase_mem_trace:list action_type-> Prop:=
| nil_increase: increase_mem_trace nil
| single_increase: forall (m:list action_type), length m = 1 -> increase_mem_trace m
| multi_increase_read_to_read: forall (m:list action_type) (m0 m1: action_type) (m': list action_type)
( add0  add1  val0  val1:int256),
  m0::(m1::m') = m -> m0.(mem_ins) = read add0  val0 -> m1.(mem_ins) = read  add1 val1
  -> (Int256.unsigned add0 <= Int256.unsigned add1)%Z -> ((Int256.unsigned add0 = Int256.unsigned add1)%Z -> m0.(timestamp) < m1.(timestamp))
  -> increase_mem_trace m
| multi_increase_read_to_write: forall (m:list action_type) (m0 m1: action_type) (m': list action_type)
( add0  add1  val0  val1:int256),
  m0::(m1::m') = m -> m0.(mem_ins) = write add0  val0 -> m1.(mem_ins) = read  add1 val1
  -> (Int256.unsigned add0 <= Int256.unsigned add1)%Z -> ((Int256.unsigned add0 = Int256.unsigned add1)%Z-> m0.(timestamp) < m1.(timestamp))
  -> increase_mem_trace m
| multi_increase_write_to_read: forall (m:list action_type) (m0 m1: action_type) (m': list action_type)
( add0  add1  val0  val1:int256),
  m0::(m1::m') = m -> m0.(mem_ins) = read add0  val0 -> m1.(mem_ins) = write add1 val1
  -> (Int256.unsigned add0 <= Int256.unsigned add1)%Z -> ((Int256.unsigned add0 = Int256.unsigned add1)%Z -> m0.(timestamp) < m1.(timestamp))
  -> increase_mem_trace m
| multi_increase_write_to_write: forall (m:list action_type) (m0 m1: action_type) (m': list action_type)
( add0  add1  val0  val1:int256),
  m0::(m1::m') = m -> m0.(mem_ins) = write add0  val0 -> m1.(mem_ins) = write  add1 val1
  -> (Int256.unsigned add0 <= Int256.unsigned add1)%Z -> ((Int256.unsigned add0 = Int256.unsigned add1)%Z -> m0.(timestamp) < m1.(timestamp))
  -> increase_mem_trace m
.

Inductive multiset:list ins-> list CPU_state -> Prop:=
| halt: forall (CPU_trace:list CPU_state) (program:list ins), length CPU_trace = 1 -> program = []->multiset program CPU_trace
| run: forall (CPU_trace rm_2_CPU_trace:list CPU_state) (program rm_program:list ins) (C1 C2:CPU_state), 
C1::C2::rm_2_CPU_trace=CPU_trace -> C1.(inst)::rm_program = program -> multiset program CPU_trace
.

Theorem completeness_of_protocol:
forall (program: list ins)(CPU_trace rm_first_CPU_trace rm_last_CPU_trace:
list CPU_state)
(first_CPU_state last_CPU_state: CPU_state)
(action_trace: list action_type),
CPU_trace = cons first_CPU_state rm_first_CPU_trace ->
CPU_trace = rm_last_CPU_trace ++ [last_CPU_state] ->
length rm_last_CPU_trace = length action_trace -> (* 新增条件 *)
program <> [] -> (* 新增条件 *)
In (last_CPU_state.(inst), last_CPU_state.(pc)) (combine program (seq 0
(length program))) -> (* 新增条件 *)
(exists (mem_list: list (int256 -> int256))(first_mem last_mem: int256 ->
int256),
length mem_list = length action_trace /\
eval_ins_list program
(combine_to_pc_state first_CPU_state first_mem)
(combine_to_act_state_list rm_last_CPU_trace mem_list action_trace) (* 注
意这里 combine_to_act_state_list 是用 combine 实现的，不要求 rm_last_CPU_trace
和 mem_list 以及 action_trace 长度相等 *)
(combine_to_pc_state last_CPU_state last_mem))
-> exists (memory_trace: list action_type), constraints program CPU_trace
action_trace memory_trace. (* 需要用条件和归纳假设自行构造 memory_trace *)
Proof.
  intros program CPU_trace rm_first_CPU_trace rm_last_CPU_trace first_CPU_state last_CPU_state action_trace.
  revert program CPU_trace rm_first_CPU_trace first_CPU_state last_CPU_state action_trace.
(*反向归纳*)
  apply rev_ind with (l:=rm_last_CPU_trace).
  + intros;simpl in *.
      subst.
      exists [].
      inversion H1;clear H1.
      destruct H4 as [mem_list [first_mem [last_mem [H1 ?]]]].
      inversion H0;clear H0.
      inversion H;clear H.
      subst.
      unfold combine_to_pc_state,Definition_and_soundness.Build_pc_state,Definition_and_soundness.Build_program_state in H10.
      simpl in H10.
      pose proof length_zero_iff_nil action_trace.
      destruct H.
      symmetry in H5.
      pose proof H H5.
      clear H H6 H5.
      unfold combine_to_pc_state in H8.
      unfold Definition_and_soundness.Build_program_state,Definition_and_soundness.Build_pc_state in H8.
      simpl in H8.
      unfold Definition_and_soundness.combine_to_pc_state in H4.
      simpl in H4.
      subst.
      (*通过化简得到很多都是空的*)
      split.
      - apply trace_CPU with (rm_first_CPU_trace:=[]) (first_CPU_state:=last_CPU_state).
        * tauto.
        * tauto.
        * tauto.
        * apply adjacent_CPU_state_nil.
      - apply trace_multiset with (program:= program) (CPU_trace:= [last_CPU_state]).
        destruct program.
        * contradiction.
        * simpl in *.
          right.
          ++ tauto.
          ++ apply Forall_nil.
      - apply ActionListTraceNil.
      - apply trace_action with (CPU_trace:=[last_CPU_state]) (action_trace:=[]).
        apply adjacent_CPU_state_for_action_trace_nil with (x:= last_CPU_state).
      - apply permutation with (action_trace:=[])(memory_trace:=[]).
        simpl.
        apply perm_nil.
      - apply trace_momory_nil.
      - apply public with (program:= program)(CPU_trace:= [last_CPU_state])(action_trace:=[])(memory_trace:=[]).
  + intros.
     subst.
     pose proof cons_eq x l.
     destruct H0 as [? [rm_first_last_CPU_trace ?]].
     rewrite H0 in H1.
     inversion H1;clear H1.
     symmetry in H7.
     subst.
     rename x into rm_last_two_2_CPU_state.
     specialize (H program (l ++ [rm_last_two_2_CPU_state]) rm_first_last_CPU_trace first_CPU_state rm_last_two_2_CPU_state).
     pose proof last_length l  rm_last_two_2_CPU_state .
     rewrite H1 in H2;clear H1.
     assert (exists (rm_last_action_trace:list action_type)(a:action_type), rm_last_action_trace++[a]=action_trace
/\Datatypes.length l = Datatypes.length rm_last_action_trace).
{
     destruct action_trace.
     simpl in H2.
     + inversion H2.
     + pose proof cons_app_eq a action_trace.
        destruct H1 as [ls [rm_ls ?]].
        exists rm_ls,ls.
        symmetry in H1.
        split.
        - tauto.
        - rewrite <- H1 in H2.
          Search (length (?l ++ ?x)).
          pose proof last_length rm_ls ls.
          rewrite H6 in H2;clear H6.
          lia.
}
     destruct H1 as[rm_last_action_trace [last_action_trace [? ?]]].
     specialize (H rm_last_action_trace).
     pose proof H H0 (ltac:(tauto)).
     pose proof H7 H6 H3.
     clear H H7.
     destruct H5 as  [mem_list [first_mem [last_mem [H9 H10]]]].
     inversion H10;clear H10.
     subst.
     inversion H11;clear H11.
     inversion H12;clear H12.
     unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H10.
     unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H1.
     pose proof cons_eq rm_last_two_2_CPU_state l .
     pose proof cons_eq last_action_trace rm_last_action_trace.
     destruct H11 as [first [last_two ?]].
     destruct H12 as [firsxt_ [rm_first ?]].
     - destruct mem_list.
       * inversion H9. 
          rewrite H12 in H14.
          inversion H14.
      * rewrite H11 in H10.
         rewrite H12 in H10.
         inversion H10.
    - unfold combine_to_act_state_list in H1.
      pose proof cons_eq rm_last_two_2_CPU_state l .
      pose proof cons_eq last_action_trace rm_last_action_trace.
      destruct H11 as [first [last_two ?]].
      destruct H13 as [first_ [rm_first ?]].
      rewrite H11 in H1.
      rewrite H13 in H1.
      simpl in H1.
      destruct mem_list.
      * inversion H1.
      * inversion H1;clear H1.
         rewrite  H0 in H11.
         inversion H11;clear H11.
         subst.
         destruct mem_list.
         ++ inversion H9;clear H9.
               pose proof length_one_iff_single (rm_last_action_trace ++ [last_action_trace]).
               destruct H1.
               clear H9.
               symmetry in H11.
               pose proof H1 H11;clear H1.
               destruct H9.
               pose proof app_after_nil_1 rm_last_action_trace.
               specialize (H9 last_action_trace x).
               pose proof H9 H1;clear H1 H9.
               rewrite H11 in H2.
               destruct l.
               -- subst.
                  simpl in H12.
                  inversion H12.
                  destruct x0.
                  ** simpl in H1;sets_unfold in H1;destruct H1.
                      unfold combine_to_act_state_list in H1.
                      inversion H1.
                  ** simpl in H1;sets_unfold in H1.
                      destruct H1 as [i0 [i1[i2 [? [? ?]]]]].
                      pose proof Definition_and_soundness.one program i1  (combine_to_pc_state first first_mem)  i0.
                      destruct H15.
                      +++ 
                  admit.
               -- inversion H2. (*q.e.d*)
               destruct last_action_trace.
               destruct mem_ins0.
               -- exists [{| timestamp := timestamp0; mem_ins := read address value |}].
                  split.
               
               pose proof cons_eq last_action_trace rm_last_action_trace .
               destruct H9 as [y [l' ?]].
               rewrite H9 in H1.
               inversion H1;clear H1.
               subst.
 unfold combine in H10.
          simpl in H10.
     simpl in H12.
     rename H12 into H1.
     destruct H1 as [n ?].
     destruct n.
     - simpl in H1.
       sets_unfold in H1.
       destruct H1.
       unfold combine_to_act_state_list,combine_to_act_state in H1.
       simpl in H1.
     assert (In (rm_last_two_2_CPU_state.(inst), rm_last_two_2_CPU_state.(pc))
       (combine program (seq 0 (Datatypes.length program)))).
{
     
}
 (*接下来已知最后一个可达，证明倒数第二个也可达*)
     pose proof H8 
     inversion H6.
     assert(exists m:list action_type, filter mem_ins_type_is_not_non m = m /\ Permutation m action_trace /\ increase_mem_trace m).
{
  exists (filter mem_ins_type_is_not_non action_trace).
  apply rev_ind with (l := action_trace).
  + simpl;tauto.
  + intros.
      pose proof filter_cons_app mem_ins_type_is_not_non l [x].
      rewrite H0.
      pose proof filter_cons_app mem_ins_type_is_not_non (filter mem_ins_type_is_not_non l) (filter mem_ins_type_is_not_non [x]).
      rewrite H1.
      rewrite H.
     destruct x.
     destruct mem_ins0.
      - tauto.
      - tauto.
      - tauto.
}
          tauto.
        simpl.
        unfold In.
        simpl.
        tauto.
        * unfold combine_to_act_state_list in H0.
           simpl in H0.
           unfold combine_to_pc_state in H0.
           unfold Definition_and_soundness.Build_program_state,Definition_and_soundness.Build_pc_state in H0.
           sets_unfold in H0.
           inversion H0;clear H0.
           inversion H4;clear H4.


        destruct program.
        ++ contradiction.
        ++ destruct i.
              -- simpl.
                 right.
                 ** left.

unfold combine_to_act_state_list in H0.
           simpl in H0.
           unfold combine_to_pc_state in H0.
           unfold Definition_and_soundness.Build_program_state,Definition_and_soundness.Build_pc_state in H0.
           destruct x0.
           ++
            admit.
           ++ simpl in H0. 
                 sets_unfold in H0.
                 destruct H0 as[x [y [z []]]].
                  Search (?l = []).
                 pose proof app_eq_nil y z H0;clear H0 H.
                 destruct H4; subst.
                 destruct H3.
                 inversion H;clear H;subst.
                 unfold fold_ins_sem in H3.
                 simpl in H3.
                 sets_unfold in H3.
                 inversion H3;clear H3.
                 -- destruct i;inversion H.
                 -- unfold fold_right in H.
                     rewrite H2,H13 in H.
                     unfold eval_ins in H.
                     destruct program;inversion H.
                     ** destruct i0;inversion H3.
                     **
                        
                    simpl in H.
                     
                  Print nsteps.
(*
                 pose proof Definition_and_soundness.one (i :: program) [] ({|
        pc_state.pc := last_CPU_state.(pc);
        pc_state.state :=
          {|
            memory := fun _ : int256 => zero;
            program_state.stack := last_CPU_state.(stack)
          |}
      |}) x.
*)
                  H0.
            inversion H3;clear H3.

            subst.
            
            






  +
  intros program CPU_trace rm_first_CPU_trace rm_last_CPU_trace first_CPU_state last_CPU_state action_trace.
  revert program CPU_trace rm_first_CPU_trace rm_last_CPU_trace first_CPU_state last_CPU_state.
  destruct H as [memory_trace ?].





 intros program CPU_trace rm_last_CPU_trace first_CPU_state last_CPU_state action_trace H H0.
        exists  (filter mem_ins_type_is_not_non action_trace).
       subst.
      symmetry in H0.
      pose proof app_after_nil_1 rm_last_CPU_trace last_CPU_state first_CPU_state H0.
      pose proof app_after_nil_2 rm_last_CPU_trace last_CPU_state first_CPU_state H0.
      clear H0.
      intros.
(*
在这里得到H : rm_last_CPU_trace = []
H2 : last_CPU_state = first_CPU_state
*)
      destruct H1 as [mem_list [first_mem [last_mem [H1 H3]]]].
      inversion H3.
      clear H3.
      simpl in *.
      Search combine.
      Print combine.
      split.
      - apply trace_CPU with (rm_first_CPU_trace:=[]) (first_CPU_state:=first_CPU_state).
        * tauto.
        * tauto.
        * tauto.
        * pose proof adjacent_CPU_state_nil eval_constraint first_CPU_state.
          tauto.
      - apply trace_multiset with (program := program) (CPU_trace:= [first_CPU_state]).
        simpl.
        rewrite H0.
        Print In.
        destruct first_CPU_state as [? ? ?].
        subst.
         destruct inst0.
          ++
              simpl in *.
              Print Rels.RELS_ID.
              unfold combine_to_act_state_list in *.
              simpl in *.
              clear H6.
              (pose proof Definition_and_soundness.one program [] 
(combine_to_pc_state {| CPU_state.pc := pc0; stack := stack0; inst := JUMPI |} (fun _ : int256 => zero)) 
(combine_to_pc_state {| CPU_state.pc := pc0; stack := stack0; inst := JUMPI |} last_mem) ).
              unfold nsteps in H7.
              destruct H7 as [n ?].
              destruct n.
              Print nsteps.
              simpl in H2.



              unfold fold_ins_sem,fold_right in H.
              simpl in H.
              inversion H7.
              unfold combine_to_pc_state in H7.
              simpl in H7.
              inversion H7.
              discriminate.
              
            
          assert (length program = 1).
          {

          }
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
  + intros x l H Program CPU_trace rm_last_CPU_trace first_CPU_state last_CPU_state  action_trace memory_trace.
     pose proof cons_app_eq first_CPU_state l.
    destruct H0 as [last_two_2_CPU_state [rm_last_two_2_CPU_trace ?]].
      
      split.
      - rewrite H1.
        
  















      pose proof cons_app_eq first_CPU_state l.
      destruct H0 as [last_two_2_CPU_state [rm_last_two_2_CPU_trace ?]].
     specialize (H Program rm_last_CPU_trace rm_last_two_2_CPU_trace first_CPU_state last_two_2_CPU_state).
      intros H1 H2 H3.
      destruct H3 as[mem_list [first_mem [last_mem []]]].
      inversion H4.
      inversion H9.
      rename x1 into n.
      clear H9.
      subst.
      assert (exists (x:action_type) (l:list action_type),l ++ [x]=action_trace).
      {
          admit.
      }
      assert (exists (x:action_type) (l:list action_type),l ++ [x]=memory_trace).
      {
          admit.
      }
      destruct H1 as [last_action [rm_last_action_trace ?]].
      destruct H9 as [last_memory [rm_last_memory_trace ?]].
      specialize (H rm_last_action_trace rm_last_memory_trace).
      pose proof app_last_corr (first_CPU_state :: l) rm_last_CPU_trace x last_CPU_state H2.
      destruct H10.
      symmetry in H10.
      pose proof H10.
      rewrite H0 in H12.
      pose proof H H10 H12.
      clear H.
      destruct H13.
      assert (exists (x:int256->int256)(l:list (int256->int256)),l++[x]=mem_list).
      {
          admit.
      }
      destruct H as [last_two_2_mem [rm_last_mem_list ?]].
      - exists rm_last_mem_list,first_mem,last_two_2_mem.
        split.
        * admit.
        *  apply sigma.
          ++ tauto.
          ++ tauto.
          ++ tauto.
          ++ pose proof ActionListCons.
                admit.
          ++ simpl.
                assert (exists (n0:nat),S n0 = n).
                {
                  admit.
                }
                destruct H13 as [n0 ?].
                exists n0.
                Print one.
                admit.
      -

(* ∀x∀l(()->())->∀P...(()->()) *)







  pose proof all_constraints.
  inversion H.
  split.
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
