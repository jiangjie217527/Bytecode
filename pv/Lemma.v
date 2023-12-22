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
  forall [A B C D:Type] (x:A*nat) (l: list (A*nat)) (f: (A*nat) -> B -> C -> D -> Prop)  (s1: B)(s2: C)(s3: D) (x1:A)(x2:nat)(l1:list A)(l2:list nat),
  (forall (x y:A*nat) (s1:B) (s2:C) (s3:D) (x1 x2:A)(y1 y2:nat), x = (x1,y1)-> y=(x2,y2)-> f x s1 s2 s3 /\ f y s1 s2 s3 -> y1 = y2 ) -> fold_right Sets.union ∅ (map f l) s1 s2 s3 -> f x s1 s2 s3 -> x = (x1,x2) -> l = (combine l1 l2) ->length l1 = length l2->In x2 l2.
Proof.
  intros A B C D x l f s1 s2 s3 x1 x2 l1 l2.
  revert x  f s1 s2 s3 x1 x2 l1 l2.
  induction l.
  + intros.
       destruct l2.
     - contradiction.
     - simpl in H4.
       symmetry in H4.
       pose proof len_succ l1 (Datatypes.length l2) H4.
       destruct H5 as [? [? ?]].
       rewrite H5 in H3.
       inversion H3.
  + intros.
    assert (exists (ins0:A) (l':list A),l1 = ins0::l').
    {
      destruct l1.
      inversion H3.
      exists a0,l1.
      tauto.
    }
    destruct H5 as [ins0 [l12 ?]].
    subst.
     destruct l2.
     - inversion H4.
      (*
       pose proof length_zero_iff_nil l1.
       destruct H6;clear H8.
       pose proof H6 H7.
       contradiction.*)
     - inversion H0;clear H0.
       * destruct a;subst.
         specialize (H (x1,x2) (a,n0) s1 s2 s3 x1 a x2 n0).
         pose proof H (ltac:(tauto)) (ltac:(tauto));clear H.
         destruct H0.
         split;tauto.
         inversion H3.
         unfold In.
         left.
         tauto.
       * inversion H3;clear H3. 
       inversion H4;clear H4.
         specialize (IHl (x1,x2) f s1 s2 s3 x1 x2 l12 l2).
         pose proof IHl H H2 H1 (ltac:(tauto)) H6 H3;clear IHl. (*(ltac:(tauto)) (ltac:(tauto));clear H*)
         unfold In.
         right.
         tauto.
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
