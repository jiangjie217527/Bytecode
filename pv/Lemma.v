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

Lemma cons_eq: forall {A : Type} (x : A) (l : list A), exists y l',  l ++ [x] = y:: l'.
Proof.
  intros.
  revert x.
  induction l. intros.
  - exists x, []. reflexivity.
  - intros. exists a, (l++[x]). reflexivity.
Qed.
(*not in:由pc越界推出矛盾*)
Lemma zero_not_in_seq_one:
  forall (x:nat),In 0 (seq 1 x) -> False.
Proof.
  intros.
  pose proof in_seq x 1 0.
  destruct H0;clear H1.
  pose proof H0 H;clear H0.
  destruct H1.
  inversion H0.
Qed.

Lemma Forall_rev_tail:
  forall [A : Type] [P : A -> Prop] [a : A] [l : list A],
  Forall P (l++[a]) -> Forall P l.
Proof.
  intros.
  induction l.
  + apply Forall_nil.
  + simpl in H.
      pose proof Forall_inv_tail.
      specialize (H0 A P a0 (l ++[a])).
      pose proof H0 H.
      pose proof IHl H1.
      pose proof Forall_inv.
      specialize (H3 A P a0 (l++[a])).
      pose proof H3 H.
      apply Forall_cons;tauto.
Qed.

Lemma multiset_subst:
  forall (l:list CPU_state) (p:list ins) (a x:CPU_state),
   multiset_constraint (a::l ++[x]) (p) -> multiset_constraint (a::l) (p).
Proof.
  intros.
  inversion H;clear H;subst.
  apply trace_multiset with(program:=p) (CPU_trace:=(a::l)).
  pose proof Forall_rev_tail.
   pose proof Forall_map (fun cpu_state : CPU_state => (cpu_state.(inst),cpu_state.(pc)))  (fun x : ins * nat =>
        In x (combine ( p) (seq 0 (Datatypes.length (p)))))  (a :: l ++ [x]).
    destruct H1 ;clear H2.
    pose proof H1 H0. clear H1 H0.
    
  specialize (H CPU_state).
  specialize (H (fun x : CPU_state => In (x.(inst), x.(pc)) (combine p (seq 0 (Datatypes.length p))))).
  specialize (H x (a::l)).
  pose proof H H2. clear H H2.
     pose proof Forall_map (fun cpu_state : CPU_state => (cpu_state.(inst),cpu_state.(pc)))  (fun x : ins * nat =>
        In x (combine ( p) (seq 0 (Datatypes.length (p)))))  (a :: l).
   destruct H. clear H.
   pose proof H1 H0.
   tauto.
Qed.
(*
   pose proof 

  remember a.(inst) as inst0.
  Check in_app_or.
  
 
   destruct H0. clear H2.
   pose proof H0 H1;clear H0 H1.
   pose proof Forall_rev.
   specialize (H0 CPU_state (fun x : CPU_state => In (x.(inst), x.(pc)) (combine (inst0 :: p) (seq 0 (Datatypes.length (inst0 :: p)))))  (a :: l ++ [x])).
   pose proof H0 H2;clear H0 H2.
   simpl in H1.
   inversion H1;clear H1;subst.
  +
     pose proof cons_eq a (rev (l ++ [x])).
     destruct H0 as [? [? ?]].
     symmetry in H2.
     rewrite H0 in H2.
     discriminate.
   + pose proof rev_unit l x.
      rewrite H1 in H0.
      inversion H0;clear H0 H1.
      subst.
      
      destruct l.
      - simpl in H3.
        discriminate.
      - simpl in H2.
   inversion H2.
      simpl in H1.
  Check Forall_forall.
  
  intros l.
  
  induction l.
  + intros.
      apply trace_multiset with(program:=(inst0::p)) (CPU_trace:=[a]).
      simpl.
      inversion H0;clear H0;subst.
      simpl in H1.
      inversion H1;clear H1;subst.
      inversion H3;clear H3.
      - right.
        * left;tauto.
        * left.
      - rewrite H in H0.
      Check in_combine_r.
        pose proof in_combine_r p (seq 1 (Datatypes.length p)) a.(inst) 0 H0;clear H0.
        pose proof zero_not_in_seq_one (Datatypes.length p) H1.
        contradiction.
  + intros.
     
  specialize (IHl p a x inst0).
    pose proof IHl H;clear IHl.
     simpl in H.
     inversion H;subst;clear H.
     simpl in H0.
     inversion H0;clear H0;subst.
     
 *)
     (*
     Lemma subset:
  forall [A:Type] (a x:A)(l:list A),
  In (a::l) (a::l++[x]).
     
     *)

Lemma cong:
  forall [A:Type](a:A),
  [a]<>[] -> [] <> [a].
Proof.
  congruence.
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

Lemma cons_before_nil:
  forall [A:Type](x y:A)(l:list A),
  [x] = y::l
  -> y = x /\ l = [].
Proof.
  intros.
  pose proof cons_app_eq y l.
  destruct H0 as [? [? ?]].
  rewrite H0 in H.
  pose proof app_after_nil_1 x1 x0 x.
  symmetry in H.
  pose proof H1 H.
  clear H1.
  subst.
  split.
  + destruct l.
    - inversion H0.
       symmetry in H2.
       inversion H.
       subst.
       simpl in H.
       tauto.
     - inversion H0.
  + destruct l.
      - tauto.
      - inversion H0.
Qed.


Lemma one_step_generate_one_action_2:
  forall (first_pc_state run_one_step_pc_state:pc_state)(act_trace:list act_state)(program:list ins)(n:nat),
fold_right
        (fun (x y : pc_state -> list act_state -> pc_state -> Prop)
           (a : pc_state) (a0 : list act_state) 
           (a1 : pc_state) => x a a0 a1 \/ y a a0 a1)
        (fun (_ : pc_state) (_ : list act_state) (_ : pc_state) => False)
        (map eval_ins
           (combine (program)
              (seq n
                 (Datatypes.length (program)))))
        first_pc_state act_trace run_one_step_pc_state
        -> act_trace <> [].
Proof.
  intros first_pc_state run_one_step_pc_state act_trace program n.
  revert first_pc_state run_one_step_pc_state act_trace n.
  (*assert (remain_program = []).*)
  induction program.
  + intros. 
     simpl in H;contradiction.
  + intros.
     simpl in H.
     destruct H.
     - destruct a;inversion H;discriminate.
     - specialize (IHprogram first_pc_state run_one_step_pc_state act_trace (S n)).
     pose proof IHprogram H.
     tauto.
Qed.

Lemma one_step_generate_one_action:
  forall (first_pc_state run_one_step_pc_state:pc_state)(act_trace:list act_state)(program:list ins)(n:nat),
fold_right
        (fun (x y : pc_state -> list act_state -> pc_state -> Prop)
           (a : pc_state) (a0 : list act_state) 
           (a1 : pc_state) => x a a0 a1 \/ y a a0 a1)
        (fun (_ : pc_state) (_ : list act_state) (_ : pc_state) => False)
        (map eval_ins
           (combine (program)
              (seq n
                 (Datatypes.length (program)))))
        first_pc_state act_trace run_one_step_pc_state
        -> length act_trace =1.
Proof.
   intros.
   pose proof one_step_generate_one_action_2 first_pc_state run_one_step_pc_state act_trace program n H.
   destruct act_trace.
   + contradiction.
   + clear H0.
      revert H.
      revert first_pc_state run_one_step_pc_state act_trace n.
      induction program.
      - intros.
        simpl in H;contradiction.
      - intros.
        simpl.
        destruct act_trace.
        * simpl;tauto.
        * inversion H;clear H.
          ++ unfold eval_ins in H0.
                destruct a0;inversion H0.
          ++ specialize (IHprogram first_pc_state run_one_step_pc_state (a1 :: act_trace) (S n)).
           pose proof IHprogram H0.
           tauto.
Qed.
        
(*
  induction act_trace.
  + simpl in H.
     destruct H.
     - destruct inst0;inversion H.
     - 
  inversion H;clear H;destruct first_pc_state;simpl in H0;rewrite H0 in H1.
  +
    unfold eval_ins in H1.
    destruct inst0;inversion H1;discriminate.
  +
      Print fold_right.
      unfold fold_right in H1.
      apply rev_ind with (l:= remain_program).
      - simpl in H1.
        contradiction.
      - simpl in H1.
        destruct H1.
        * destruct a; inversion H; simpl in H3;discriminate.
        * 
          destruct  IHremain_program.
          ++ unfold seq in H.
                simpl in H.
                unfold eval_ins in H.
                unfold map in H.
                unfold fold_right in H.
                simpl in H.
      pose proof IHremain_program H1.
    - inversion H1.
  + 
  destruct inst0.
  +
  inversion H;clear H. 
    -  unfold eval_ins in H1.
       inversion H1.
       subst.
        discriminate.
    - destruct first_pc_state.
       simpl in H0.
       rewrite H0 in H1.
       induction remain_program.
       * simpl in H1. contradiction.
       * simpl in H1. 

*)
      
Lemma map_nil:
  forall [A B:Type] (f:A->B) (l:list A),
  [] = map f l
  -> l = [].
Proof.
  intros.
  destruct l.
  + tauto.
  + simpl in H.
      discriminate.
      Check Datatypes.length.
Qed.


(*不一定成立，可能f不是单射，导致可能l的第一个元素并不是x.*)
(*所以在证明中需要证明eval_ins中(ins*pc)可以由后面三个参数唯一确定*)
(*为什么不是只有第一个就可以确定。按道理某个pc_state固定了，后面的也确定了
因为pc_state 包含了pc,memory stack，但是我们并不知道这个inst它和pc的关系
举个例子，如果f x s1 s2 s3中x为(add 0) f y s1 t2 t3 中y为(sub 0)，那么其实s1看上去也是
一样的（ins貌似并不存储在memory和stack里面而是在program里面）
但是这两个的结果是s3,t3不同
同理，如果一个读一个写，那就是s2,t2不同*)
(*唯一确定的理由可能是eval_ins由后面三个参数可以得到确定的ins*nat *)
(*但是单射这个条件太强了，其实pop 和jump就不是单射，可以inst不一样但是行为完全一样*)
(*所以只能确定nat,所以这个定理确实不一定成立*)
(*--------------x可能不在l里，但是x2一定在l的第二个里面 ---------------*)

Lemma out_property:
  forall [A B C D:Type]  (l: list (A*nat)) (f: (A*nat) -> B -> C -> D -> Prop)  (s1: B)(s2: C)(s3: D) (l1:list A)(l2:list nat),
  (forall (x y:A*nat) (s1:B) (s2:C) (s3:D) (x1 x2:A)(y1 y2:nat), x = (x1,y1)-> y=(x2,y2)-> f x s1 s2 s3 /\ f y s1 s2 s3 -> y1 = y2 ) -> fold_right Sets.union ∅ (map f l) s1 s2 s3 -> l = (combine l1 l2) ->length l1 = length l2->(exists (x:A*nat),f x s1 s2 s3 /\ In x l).
Proof.
  intros A B C D l f s1 s2 s3 l1 l2.
  revert f s1 s2 s3 l1 l2.
  induction l.
  + intros.
       destruct l2.
     - contradiction.
     - simpl in H2.
       symmetry in H2.
       pose proof len_succ l1 (Datatypes.length l2) H2.
       destruct H3 as [? [? ?]].
       rewrite H3 in H1.
       inversion H1.
  + intros.
    assert (exists (ins0:A) (l':list A),l1 = ins0::l').
    {
      destruct l1.
      inversion H1.
      exists a0,l1.
      tauto.
    }
    destruct H3 as [ins0 [l12 ?]].
    subst.
     destruct l2.
     - inversion H2.
      (*
       pose proof length_zero_iff_nil l1.
       destruct H6;clear H8.
       pose proof H6 H7.
       contradiction.*)
     - inversion H0;clear H0.
       * exists a.
          split.
          ++ tauto.
          ++ simpl.
                left.
                tauto.
      (*
        destruct a;subst.
         specialize (H (x1,x2) (a,n0) s1 s2 s3 x1 a x2 n0).
         pose proof H (ltac:(tauto)) (ltac:(tauto));clear H.
         destruct H0.
         split;tauto.
         inversion H3.
         unfold In.
         left.
         tauto.*)
       * inversion H1;clear H1. 
       inversion H2;clear H2.
         specialize (IHl f s1 s2 s3 l12 l2).
         pose proof IHl H H3 H5 H1 ;clear IHl.
          (*(ltac:(tauto)) (ltac:(tauto));clear H*)
         destruct H0 as [x [? ?]].
         exists x.
         split.
         ++ tauto.
         ++ simpl.
                right.
                rewrite <- H5.
                tauto.
         
         (*
         unfold In.
         right.
         tauto.*)
Qed.

Lemma stack_difference_2:
  forall [A:Type] (l l':list A)(a:A),
  l = l' -> l = a::l' -> False.
Proof.
  intros.
  rewrite H in H0.
  assert (length (a :: l') <>length l' ).
   {
    simpl.
    pose proof Nat.neq_succ_diag_l (Datatypes.length l').
    tauto.
   }
   rewrite <- H0 in H1.
   contradiction.
Qed.
Lemma stack_difference:
  forall [A:Type] (l l':list A)(a b c:A),
  l = a:: l' -> l = b :: c :: l'->False.
Proof.
  intros.
  rewrite H in H0.
   inversion H0.
   pose proof stack_difference_2 l' l' c (ltac:(tauto)) H3.
   tauto.
Qed.

Lemma  stack_difference_3:
  forall  [A:Type] (l l':list A),
  l' <> [] -> l = l' ++ l -> False.
Proof.
  intros.
  assert (length l = length (l' ++ l)).
  {
    rewrite <- H0.
    tauto.
  }
  pose proof app_length l' l.
  rewrite H2 in H1.
  assert (length l' <> 0).
  {
     destruct l'.
     + contradiction.
     + simpl.
        lia.
  }
  lia.
Qed.


(*----------------------又是一个发现没法证明的命题，，，，，-------------------*)
Lemma eval_ins_mono:
  forall (x y:(ins*nat)) (s1:pc_state) (s2:list act_state) (s3:pc_state), eval_ins x s1 s2 s3 /\ eval_ins y s1 s2 s3 -> x = y.
Proof.
  intros.
  destruct H.
  unfold eval_ins in H.
  unfold eval_ins in H0.
  destruct x.
  destruct y.
  destruct i;inversion H;clear H;     subst.
  + destruct i0;inversion H0;clear H0;subst;simpl in *.
     - tauto.
     - pose proof stack_difference (program_state.stack (pc_state.state s1)) (program_state.stack (pc_state.state s3)) v dest cond H12 H5.
        contradiction.
    -  pose proof stack_difference (program_state.stack (pc_state.state s1)) (program_state.stack (pc_state.state s3)) v dest cond H13 H5.
        contradiction.
    - rewrite H5 in H13.
    inversion H13.
    pose proof stack_difference_2 (program_state.stack (pc_state.state s3)) (l) (add v1 v2) H15 H14.
    contradiction.
    - rewrite H5 in H13.
    inversion H13.
    pose proof stack_difference_2 (program_state.stack (pc_state.state s3)) (l) (mul v1 v2) H15 H14.
    contradiction.
    - rewrite H5 in H13.
    inversion H13.
    pose proof stack_difference_2 (program_state.stack (pc_state.state s3)) (l) (sub v1 v2) H15 H14.
    contradiction.
    - rewrite H5 in H12.
      inversion H12.
      rewrite <- H9 in H13.
      assert ((pc_state.state s1).(memory) offset :: cond :: program_state.stack (pc_state.state s3) = [(pc_state.state s1).(memory) offset ; cond]++program_state.stack (pc_state.state s3)).
      {
        simpl.
        tauto.
      }
      rewrite H in H13.
      pose proof stack_difference_3 (program_state.stack (pc_state.state s3)) ([(pc_state.state s1).(memory) offset; cond]) (ltac:(discriminate)) H13.
      contradiction.
    - rewrite H2 in H16.
      discriminate.
    - rewrite H5 in H13.
      assert (v :: dest :: cond :: program_state.stack (pc_state.state s3) = [v;dest;cond]++program_state.stack (pc_state.state s3)).
      {
        simpl.
        tauto.
      }
      rewrite H in H13.
      pose proof stack_difference_3 (program_state.stack (pc_state.state s3)) ([v; dest; cond]) (ltac:(discriminate)) H13.
      contradiction.
  + destruct i0;inversion H0;clear H0;subst;simpl in *.
      - pose proof stack_difference (program_state.stack (pc_state.state s1)) (program_state.stack (pc_state.state s3)) v dest cond H5 H11.
        contradiction.
      - tauto.
      -  (*这种情况没法证明*)
Abort.
(*-------------改成证明只有pc相同----------------------*)

Lemma eval_ins_same_pc:
  forall (x y:(ins*nat)) (s1:pc_state) (s2:list act_state) (s3:pc_state) (ins0 ins1:ins) (pc0 pc1:nat), x =(ins0,pc0)->y=(ins1,pc1)->eval_ins x s1 s2 s3 /\ eval_ins y s1 s2 s3 -> pc0=pc1.
Proof.
  intros.
  destruct H1.
  subst.
  unfold eval_ins in H1.
  unfold eval_ins in H2.
  destruct ins0;destruct ins1;inversion H1;clear H1;inversion H2;clear H2;subst;tauto.
Qed.

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

Lemma combine_to_act_state_list_app:
    forall (l1:list CPU_state)( l2:list (int256 -> int256))( l3:list action_type) (x1:CPU_state)(x2:(int256 -> int256))(x3:action_type),length l1 = length l2 -> length l2 = length l3 ->combine_to_act_state_list (l1++[x1])(l2++[x2])(l3++[x3])=
    combine_to_act_state_list l1 l2 l3 ++ combine_to_act_state_list [x1] [x2] [x3].
Proof.
  intros.
  unfold combine_to_act_state_list.
  pose proof map_app (fun x : CPU_state * (int256 -> int256) * action_type =>
   combine_to_act_state (fst (fst x)) (snd (fst x)) (snd x)) (combine (combine l1 l2) l3) (combine (combine [x1] [x2]) [x3]).
   simpl.
   Search (combine (?l1) (?l2 ) ++ ?l).
   pose proof combine_app l1 [x1] l2 [x2] H (ltac:(simpl;tauto)).
      Search (length (combine ?l1 ?l2)).
   pose proof len_combine l1 l2 H.
  rewrite H0 in H3.
  symmetry in H3.
  simpl in *.
  pose proof combine_app (combine l1 l2) [(x1,x2)] l3 [x3] H3 (ltac:(simpl;tauto)).
  rewrite H2.
  simpl in H4.
  rewrite <- H4 in H1.
  tauto.
Qed.

Lemma Increasing_timestamp_subst:
  forall (l:list act_state)(x:act_state),Increasing_timestamp (l++[x])-> Increasing_timestamp l.
Proof.
  intros.
  inversion H.
  + destruct l.
    - simpl in H1.
      discriminate.
    - simpl in H1.
      discriminate.
  + destruct l.
    - apply ActionListNil.
    - simpl in H0.
      inversion H0.
      destruct l; simpl in H4;discriminate.
  + pose proof app_inj_tail (l0 ++ [x0]) l y x H0.
     destruct H3.
     subst.
     tauto.
Qed.
  