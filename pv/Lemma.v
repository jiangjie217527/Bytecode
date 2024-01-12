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
(*filter之后的list一定比之前的短*)
Lemma filter_short:
  forall [A:Type](P:A->bool)(l:list A),
length (filter P l) <= length l.
Proof.
  intros.
  induction l.
  + simpl.
      lia.
  + simpl.
     destruct (P a).
     - simpl in *.
       lia.
     - lia.
Qed.
(*如果把一个list去除一部分内容之后和它自己是排列关系，那么它自己其实不包含这种东西(也就是filter P l = l)*)
Lemma per_ins_non:
  forall (l:list action_type), Permutation   (filter mem_ins_type_is_not_non l) l -> (filter mem_ins_type_is_not_non
           l) = l.
Proof.
  intros.
  pose proof Permutation_length H.
  induction l.
  + simpl.
  tauto.
  + destruct a.
     destruct mem_ins0.
     - simpl in *.
        inversion H;clear H.
        inversion H0;clear H0.
        pose proof IHl H2 H5.
        * rewrite H.
        tauto.
        * tauto.
        * simpl in *;subst.
          pose proof Permutation_trans H1 H2.
          Search (Permutation).
          pose proof Permutation_cons_inv H.
          inversion H0.
          pose proof IHl H3 H5.
          rewrite H4.
          tauto.
    - simpl in *.
        inversion H;clear H.
        inversion H0;clear H0.
        pose proof IHl H2 H5.
        * rewrite H.
        tauto.
        * tauto.
        * simpl in *;subst.
          pose proof Permutation_trans H1 H2.
          Search (Permutation).
          pose proof Permutation_cons_inv H.
          inversion H0.
          pose proof IHl H3 H5.
          rewrite H4.
          tauto.
      - simpl in *.
        pose proof filter_short mem_ins_type_is_not_non l.
        rewrite H0 in H1.
        lia.
Qed.
(*l前面加一个元素就长度+1*)
Lemma cons_length_add_one:
  forall [A:Type] (l:list A)(a:A),
  length (a::l) = S(length l).
Proof.
  intros A l.
  induction l;intros.
  + simpl;tauto.
  + simpl;tauto.
Qed.
Print filter.
Lemma filiter_self:
  forall [A:Type] (l:list A)(a:A)(P:A->bool),
  filter P l = l -> 
  In a l ->
  P a=true.
Proof.
  intros A l.
  induction l.
  (*对l反向归纳，如果l为空，那么验证哪一个就可以，如果l不止一个，那么就是第一个满足，并且归纳条件需要得到第二个到最后一个满足*)
  + intros.
     simpl in H0.
     contradiction.
  + intros.
      simpl in H,H0.
      (*a要么是l的第一个元素要么是l里面的元素*)
      destruct H0.
      - subst.
        destruct (P a0).
        * tauto.
        * pose proof filter_short P l.
           rewrite H in H0.
           simpl in H0.
           lia.
    - specialize (IHl a0 P).
      destruct (P a).
        * inversion H.
           pose proof IHl H2 H0;tauto.
        * pose proof filter_short P l.
           rewrite H in H1.
           simpl in H1.
           lia.
Qed.

(*满足permutation关系的两个list应该里面元素有一样的*)
Lemma per_in:
  forall [A:Type] (a:A)(l1 l2:list A),
  Permutation (a::l1) l2 -> In a l2.
Proof.
  intros.
  remember (a::l1) as l'.
  Check Permutation_in.
  pose proof Permutation_in.
  specialize (H0 A).
    specialize (H0 l' l2 a H).
    assert (In a l').
    {
      rewrite Heql'.
      unfold In.
      simpl;tauto.
    }
    tauto.
Qed.
(*一个list里面有一个元素就可以通过这个元素把list分隔开*)
Lemma find_in:
  forall (A:Type)(l:list A)(a:A),
  In a l-> exists (l1 l2:list A), l = l1 ++[a]++l2.
Proof.
  intros A l.
  induction l.
  + intros. inversion H.
  + intros. inversion H.
      - subst.
        exists [],l.
        simpl.
        tauto.
      - specialize (IHl a0).
        pose proof IHl H0.
        destruct H1 as [? [? ?]].
        exists (a::x),x0.
        simpl.
        rewrite H1.
        tauto.
Qed. 
(*filter self的加强版，l'经过filter之后还要随机排列之后才和l相同*)
Lemma Per_t:
  forall [A:Type] (P:A->bool )(l:list A)(l':list A)(x:A), Permutation (filter P l') l
           ->In x l -> P x = true.
Proof.
intros.
pose proof Permutation_sym H.
  pose proof Permutation_in.
  specialize (H2 A l (filter P l') x).
  pose proof H2 H1 H0.
  pose proof filter_In.
  specialize (H4 A P x l').
  destruct H4;clear H5.
  pose proof H4 H3;destruct H5.
  tauto.
Qed.
(*map得到的一样，原本的不一定一样*)
Lemma map_same:
  forall [A B:Type] (f:A->B) (l l':list A),
  map f l = map f l' -> l = l'.
Proof.
  intros.
  induction l.
  + pose proof map_eq_nil f l'.
      simpl in H.
      pose proof H0 (ltac:(symmetry in H;tauto)).
      symmetry in H1.
      tauto.
   + simpl in H.
      destruct l'.
      - simpl in H.
        discriminate.
      - simpl in H.
      inversion H.
      simpl in H1.
  Search (map ?f ?l).
Abort.

Lemma cons_app_length:
  forall [A:Type] (l l':list A)(x y :A),
  x::l = l'++[y] -> length l = length l'.
Proof.
  intros.
  assert (length (x :: l ) = length (l' ++ [y])).
  { 
    rewrite H.
    tauto.
  }
  simpl in H0.
    pose proof last_length l' y.
    rewrite H1 in H0.
    inversion H0.
    tauto.
Qed.

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
(*多重集现在应该用不到了*)
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
(*filter具有连接性*)
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
     - inversion H0;clear H0.
       * exists a.
          split.
          ++ tauto.
          ++ simpl.
                left.
                tauto.
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

Lemma fold_ins_sem_nil:
  forall (l:list (ins*nat))(s1 s3:pc_state),
  fold_ins_sem l s1 [] s3 -> False.
Proof.
  intros l.
  induction l.
  + intros.
      inversion H;clear H.
   + intros.
      inversion H;clear H.
      - unfold eval_ins in H0.
      destruct a.
        destruct i;inversion H0.
      - specialize (IHl s1 s3).
        pose proof IHl H0.
        tauto.
Qed.

Lemma fold_right_s1:
   forall (p:list ins) (s1 s3:pc_state) (c:CPU_state) (m: (int256 -> int256)) (a:action_type)(n:nat), fold_right Sets.union ∅ (map eval_ins (combine p (seq n (Datatypes.length p))))s1 [{|
          pc := c.(pc);
          state :=
            {| memory := m; program_state.stack := c.(stack) |};
          action := a
        |}] s3 ->s1 =
{|
  pc_state.pc := c.(pc);
  pc_state.state :=
    {| memory := m; program_state.stack := c.(stack) |}
|}.
Proof.
   intros p.
   induction p.
   + intros.
       unfold  fold_right in H.
       simpl in H.
       sets_unfold in H.
       contradiction.
    + intros.
       unfold  fold_right in H.
       simpl in H.
       sets_unfold in H.
      destruct a.
      - destruct H.
        * inversion H;clear H;subst; simpl in *.
           destruct s1;simpl in *.
           rewrite H4.
           rewrite H1.
           tauto.
        * specialize (IHp s1 s3 c m a0 (S n)). 
           unfold  fold_right in IHp.
           pose proof IHp H.
           tauto.
      - destruct H.
        * inversion H;clear H;subst; simpl in *.
           destruct s1;simpl in *.
           rewrite H4.
           rewrite H1.
           tauto.
        * specialize (IHp s1 s3 c m a0 (S n)). 
           unfold  fold_right in IHp.
           pose proof IHp H.
           tauto.
      - destruct H.
        * inversion H;clear H;subst; simpl in *.
           destruct s1;simpl in *.
           rewrite H4.
           rewrite H1.
           tauto.
        * specialize (IHp s1 s3 c m a0 (S n)). 
           unfold  fold_right in IHp.
           pose proof IHp H.
           tauto.
      - destruct H.
        * inversion H;clear H;subst; simpl in *.
           destruct s1;simpl in *.
           rewrite H4.
           rewrite H1.
           tauto.
        * specialize (IHp s1 s3 c m a0 (S n)). 
           unfold  fold_right in IHp.
           pose proof IHp H.
           tauto.
      - destruct H.
        * inversion H;clear H;subst; simpl in *.
           destruct s1;simpl in *.
           rewrite H4.
           rewrite H1.
           tauto.
        * specialize (IHp s1 s3 c m a0 (S n)). 
           unfold  fold_right in IHp.
           pose proof IHp H.
           tauto.
      - destruct H.
        * inversion H;clear H;subst; simpl in *.
           destruct s1;simpl in *.
           rewrite H4.
           rewrite H1.
           tauto.
        * specialize (IHp s1 s3 c m a0 (S n)). 
           unfold  fold_right in IHp.
           pose proof IHp H.
           tauto.
      - destruct H.
        * inversion H;clear H;subst; simpl in *.
           destruct s1;simpl in *.
           rewrite H3.
           rewrite H1.
           tauto.
        * specialize (IHp s1 s3 c m a0 (S n)). 
           unfold  fold_right in IHp.
           pose proof IHp H.
           tauto.
      - destruct H.
        * inversion H;clear H;subst; simpl in *.
           destruct s1;simpl in *.
           rewrite H3.
           rewrite H1.
           tauto.
        * specialize (IHp s1 s3 c m a0 (S n)). 
           unfold  fold_right in IHp.
           pose proof IHp H.
           tauto.
      - destruct H.
        * inversion H;clear H;subst; simpl in *.
           destruct s1;simpl in *.
           rewrite H4.
           rewrite H1.
           tauto.
        * specialize (IHp s1 s3 c m a0 (S n)). 
           unfold  fold_right in IHp.
           pose proof IHp H.
           tauto.
Qed.

Lemma nsteps_one:
  forall (p:list ins) (s1 s3:pc_state) (rm_last_CPU_trace:list CPU_state)(last_C:CPU_state) (rm_last_m:list (int256->int256))(last_m:(int256->int256))(rm_last_a:list action_type) (last_a:action_type), nsteps (eval_ins_list_single p) 1 s1 (map
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
           nsteps (eval_ins_list_single p) 0 s1 (map
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
  (*intros p n.
  revert p.
  destruct n.
  +*) intros.
      inversion H;clear H.
      simpl in H2.
      sets_unfold in H2.
      simpl.
      sets_unfold.
      destruct H2 as [? [? [? [? [? ?]]]]].
      subst.
      inversion H2;clear H2.
      subst.
      unfold fold_ins_sem in H3.
      Check one_step_generate_one_action.
      pose proof one_step_generate_one_action s1 s3 x0 p 0 H3.
      pose proof app_nil_r x0.
      rewrite H4 in H.
      rewrite H in H2.
      pose proof map_length   (fun x : CPU_state * (int256 -> int256) * action_type =>
           {|
             pc := (fst (fst x)).(pc);
             state :=
               {|
                 memory := snd (fst x);
                 program_state.stack := (fst (fst x)).(stack)
               |};
             action := snd x
           |})  (combine
             (combine (rm_last_CPU_trace ++ [last_C]) (rm_last_m ++ [last_m]))
             (rm_last_a ++ [last_a])).
       rewrite H2 in H5.
       Check combine_app.
       pose proof combine_app rm_last_CPU_trace [last_C] rm_last_m [last_m] H1 (ltac:(tauto)).
       pose proof len_combine rm_last_CPU_trace rm_last_m H1.
       rewrite H6 in H2.
       simpl in H2.
       pose proof combine_app (combine rm_last_CPU_trace rm_last_m) [(last_C, last_m)] rm_last_a [last_a].
        rewrite <- H0 in H7.
       symmetry in H7.
       pose proof H8 H7 (ltac:(tauto)).
       rewrite H9 in H2.
       simpl in *.
      Search (length ?l = 1).
      pose proof length_one_iff_single (map
          (fun x : CPU_state * (int256 -> int256) * action_type =>
           {|
             pc := (fst (fst x)).(pc);
             state :=
               {|
                 memory := snd (fst x);
                 program_state.stack := (fst (fst x)).(stack)
               |};
             action := snd x
           |})
          (combine (combine rm_last_CPU_trace rm_last_m) rm_last_a ++
           [(last_C, last_m, last_a)])).
      destruct H10.
      clear H11.
      pose proof H10 H2.
      destruct H11.
      Search (map ?f (?x++?y)).
      pose proof map_app (fun x : CPU_state * (int256 -> int256) * action_type =>
         {|
           pc := (fst (fst x)).(pc);
           state :=
             {|
               memory := snd (fst x);
               program_state.stack := (fst (fst x)).(stack)
             |};
           action := snd x
         |}) (combine (combine rm_last_CPU_trace rm_last_m) rm_last_a) [(last_C, last_m, last_a)].
         rewrite H12 in H11.
         simpl in H11.
      pose proof app_after_nil_1 (map (fun x : CPU_state * (int256 -> int256) * action_type =>
         {|
           pc := (fst (fst x)).(pc);
           state :=
             {|
               memory := snd (fst x);
               program_state.stack := (fst (fst x)).(stack)
             |};
           action := snd x
         |})
        (combine (combine rm_last_CPU_trace rm_last_m) rm_last_a)) 
        {|
         pc := last_C.(pc);
         state :=
           {| memory := last_m; program_state.stack := last_C.(stack) |};
         action := last_a
       |} x H11.
       clear H4 H5.
       rewrite H13 in H11.
       inversion H11;clear H11 H10 H8.
       Search (map ?f ?l = []).
       pose proof map_eq_nil  (fun x : CPU_state * (int256 -> int256) * action_type =>
         {|
           pc := (fst (fst x)).(pc);
           state :=
             {|
               memory := snd (fst x);
               program_state.stack := (fst (fst x)).(stack)
             |};
           action := snd x
         |}) (combine (combine rm_last_CPU_trace rm_last_m) rm_last_a) H13.
       clear H2.
       rewrite H6 in H.
       rewrite H9 in H.
       rewrite H12 in H.
       rewrite H13 in H.
       simpl in H.
       subst.
       split.
       - tauto.
       - unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state.
       unfold fold_right in H3.
       pose proof fold_right_s1 p s1 s3 last_C last_m last_a 0.
       unfold fold_right in H.
       pose proof H H3.
       tauto.
Qed.

Lemma combine_3:
  forall (rm_last_CPU_trace:list CPU_state)(last_C:CPU_state) (rm_last_m:list (int256->int256))(last_m:(int256->int256))(rm_last_a:list action_type) (last_a:action_type),
   length rm_last_a = length rm_last_m->
           length rm_last_CPU_trace = length rm_last_m->
  combine
       (combine (rm_last_CPU_trace ++ [last_C])( rm_last_m ++[ last_m])) (rm_last_a ++ [last_a]) =
     combine (combine rm_last_CPU_trace rm_last_m) rm_last_a ++
     [(last_C, last_m, last_a)].
Proof.
  intros.
  pose proof combine_app rm_last_CPU_trace [last_C] rm_last_m [last_m] H0 (ltac:(tauto)).
  simpl in *.
  pose proof len_combine rm_last_CPU_trace rm_last_m H0.
  rewrite H2 in H.
  pose proof combine_app (combine rm_last_CPU_trace rm_last_m) [(last_C, last_m)] rm_last_a [last_a] (ltac:(symmetry in H;tauto)) (ltac:(tauto)).
  simpl in *.
  rewrite H1.
  tauto.
Qed.


(*
Lemma rev_ind_ins:
  forall (l:list ins)(x:ins),
(
(rev  (map eval_ins  (combine (l ++ [x])
                (seq 0 (Datatypes.length (l ++ [x]))))))=
(map eval_ins (combine [x] [(Datatypes.length (l))])) ++ rev (map eval_ins (combine l (seq 0 (length l))))).
Proof.
  Search rev.
  intros l.
  induction l.
  + intros.
      simpl.
      tauto.
  + intros.
      simpl.
      destruct a.
      destruct x.
      - Search rev.
        assert (  rev (map eval_ins (combine (l ++ [JUMPI]) (seq 1 (Datatypes.length (l ++ [JUMPI])))))  = JUMPI_sem (S (Datatypes.length l))
:: rev (map eval_ins (combine l (seq 1 (Datatypes.length l))))).
{
admit.
}
       rewrite H.
       tauto.
Admitted.
*)

(*
Lemma last_step:
forall (p:list ins)(x z:pc_state)(rm_last_two_CPU_trace:list CPU_state)(rm_last_two_mem:int256->int256)(rm_last_action:action_type)(n:nat),
nsteps (eval_ins_list_single p) n
       x  (combine_to_act_state_list rm_last_two_CPU_trace
          rm_last_two_mem rm_last_action) z ->
        z=(combine_to_pc_state rm_last_two_CPU_trace rm_last_two_mem).
        *)

Lemma fold_right_sem:
  forall (p:list ins) (x z:pc_state) (y:act_state) (n:nat),
  fold_right (fun (x y : pc_state -> list act_state -> pc_state -> Prop) (a : pc_state) (a0 : list act_state) (a1 : pc_state) => x a a0 a1 \/ y a a0 a1)
        (fun (_ : pc_state) (_ : list act_state) (_ : pc_state) => False) (map eval_ins (combine p (seq n (Datatypes.length (p))))) x [y] z-> x.(pc) = y.(pc)/\x.(state) = y.(state).
Proof.
  intros p.
  induction p.
  + intros.
   inversion H.
  + intros.
   simpl in H.
      destruct H.
      - destruct a ;destruct x; inversion H;simpl in H;subst;simpl in *;subst;try tauto.
      - specialize ( IHp x z y (S n)).
       pose proof IHp H.
       tauto.
Qed.

       
Lemma cons_cons:
  forall [A:Type] (l:list A)(x y:A),
  l++[x]++[y]=l++[x;y].
Proof.
  intros.
  simpl.
  tauto.
Qed.

Lemma same_list:
  forall [A:Type] (l:list A)(x y:A),
  l++[x]++[y]=(l++[x])++[y].
Proof.
  intros A l.
  induction l.
  + simpl;tauto.
  + intros.
     simpl.
     specialize (IHl x y).
     simpl in IHl.
     rewrite IHl.
     tauto.
Qed. 
    
Lemma out_is_false:
  forall(p:list ins) (s3:pc_state)(s2:act_state)(mem:int256->int256),
  List.fold_right Sets.union ∅
        (map eval_ins
           (combine p
              (seq 1 (Datatypes.length p))))
        {|
          pc_state.pc := 0;
          pc_state.state :=
            {|
              memory := mem;
              program_state.stack := []
            |}
        |}
        [s2] s3 -> False.
Proof.
  intros.
  sets_unfold in H.
        pose proof eval_ins_same_pc.
        pose proof out_property.
        specialize (H1 ins pc_state (list act_state) pc_state).
        specialize(H1 (combine p (seq 1 (Datatypes.length p)))).
        specialize (H1 eval_ins).
        specialize(H1  ({|          pc_state.pc := 0;          pc_state.state :=            {|              memory := mem; program_state.stack := []            |}        |})  [s2] s3).
       specialize (H1 p (seq 1 (Datatypes.length p))).
       pose proof H1 H0 H (ltac:(tauto));clear H1.
       pose proof seq_length (Datatypes.length p) 1.
       symmetry in H1.
       pose proof H2 H1;clear H2.
       destruct H3 as [x [? ?]].
       destruct x.
       unfold eval_ins in H2.
       destruct i;inversion H2;subst. inversion H8;simpl in *.
       ++  pose proof in_combine_r p (seq 1 (Datatypes.length p)) JUMPI 0 H3.
            pose proof zero_not_in_seq_one (Datatypes.length p) H4;contradiction.
             ++  pose proof in_combine_r p (seq 1 (Datatypes.length p)) JUMP 0 H3.
            pose proof zero_not_in_seq_one (Datatypes.length p) H4;contradiction.
              ++  pose proof in_combine_r p (seq 1 (Datatypes.length p)) POP 0 H3.
            pose proof zero_not_in_seq_one (Datatypes.length p) H4;contradiction.
            ++  pose proof in_combine_r p (seq 1 (Datatypes.length p)) ADD 0 H3.
            pose proof zero_not_in_seq_one (Datatypes.length p) H4;contradiction.
            ++  pose proof in_combine_r p (seq 1 (Datatypes.length p)) MUL 0 H3.
            pose proof zero_not_in_seq_one (Datatypes.length p) H4;contradiction.
            ++  pose proof in_combine_r p (seq 1 (Datatypes.length p)) SUB 0 H3.
            pose proof zero_not_in_seq_one (Datatypes.length p) H4;contradiction.
            ++  pose proof in_combine_r p (seq 1 (Datatypes.length p)) MLOAD 0 H3.
            pose proof zero_not_in_seq_one (Datatypes.length p) H4;contradiction.
            ++  pose proof in_combine_r p (seq 1 (Datatypes.length p)) MSTORE 0 H3.
            pose proof zero_not_in_seq_one (Datatypes.length p) H4;contradiction.
            ++  pose proof in_combine_r p (seq 1 (Datatypes.length p)) (PUSH32 v) 0 H3.
            pose proof zero_not_in_seq_one (Datatypes.length p) H4;contradiction.
Qed.
  
Lemma fu_k_ing_lemma:
  forall (C:list CPU_state) (M:list (int256->int256))(A:list action_type),
  M = [] -> combine (combine C M) A = [].
Proof.
  intros.
  rewrite H;clear H;revert A.
  induction C.
  + simpl;tauto.
  + intros.
     pose proof combine_nil.
     simpl. tauto.
Qed.


Lemma combine_act_app:
  forall 
( last_CPU:CPU_state)(rm_last_CPU:list CPU_state)(last_mem : int256 -> int256) (rm_last_mem:list (int256->int256))(last_action:action_type)(rm_last_action:list action_type),
   length rm_last_CPU = length rm_last_mem ->
      length rm_last_action = length rm_last_mem ->
      combine_to_act_state_list   (rm_last_CPU ++ [last_CPU])
       (rm_last_mem ++ [last_mem])  (rm_last_action ++ [last_action])=
      combine_to_act_state_list  (rm_last_CPU ) (rm_last_mem ) (rm_last_action)++ combine_to_act_state_list ( [last_CPU])  ([last_mem])  ([last_action]).
Proof.
    intros.
    unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state ;sets_unfold .
    pose proof combine_3 rm_last_CPU last_CPU rm_last_mem last_mem rm_last_action last_action H0 H.
    rewrite H1.
    pose proof map_app   (fun x : CPU_state * (int256 -> int256) * action_type =>
   {|
     pc := (fst (fst x)).(pc);
     state :=
       {|
         memory := snd (fst x);
         program_state.stack := (fst (fst x)).(stack)
       |};
     action := snd x
   |})      (combine (combine rm_last_CPU rm_last_mem)
       rm_last_action)      [(last_CPU, last_mem, last_action)].
       tauto.
Qed.
(*
      pose proof map_eq_nil (fun
          x : CPU_state * (int256 -> int256) * action_type
        =>
        {|
          pc := (fst (fst x)).(pc);
          state :=
            {|
              memory := snd (fst x);
              program_state.stack := (fst (fst x)).(stack)
            |};
          action := snd x
        |})        (combine
          (combine
             (rm_last_CPU ++
              [last_CPU])
             (rm_last_mem ++ [last_mem]))
          (rm_last_action ++ [last_action])) .

*)

Lemma single_act_state:
  forall(x:CPU_state)(y:int256->int256)(z:action_type)(l:list act_state),combine_to_act_state_list [x][y] [z]=l->
    length l = 1.
Proof.
  intros.
  unfold combine_to_act_state_list in H.
  simpl in H.
  rewrite <- H.
  tauto.
Qed.
  
Lemma action_trace_constraint_app:
  forall (rm_last_CPU:list CPU_state)(last_CPU:CPU_state)(rm_last_action:list action_type)(last_action:action_type),
  action_trace_constraint (rm_last_CPU++[last_CPU])(rm_last_action++[last_action])->
  action_trace_constraint rm_last_CPU rm_last_action.
Proof.
  intros.
  inversion H;clear H.
  apply trace_action with (CPU_trace:=rm_last_CPU)(action_trace:=rm_last_action).
  inversion H0;clear H0.
  + symmetry in H.
      pose proof app_eq_nil rm_last_action  [last_action] H.
     destruct H0;discriminate.
  + pose proof app_inj_tail l_action rm_last_action action0 last_action H3.
      destruct H0;subst;clear H3.
      pose proof app_inj_tail (l ++ [x]) rm_last_CPU y last_CPU H.
      destruct H0;subst.
      tauto.
Qed.
(*
Lemma last_eval:
  forall (p:list ins)(x z:pc_state)(y:action_type),
  length ((map eval_ins (combine p (seq 0 (length p) ))) x [y] z) =1.
*)

        
  
           (*------------要找到last_action插入的位置，
         就要找到last_action前一个元素
         1. 如果这个元素不存在，那就是last_action比所有的地址都小
         2. 如果这个元素存在，那就是，首先这个元素的地址要小于等于last_action,如果等于，那么时间戳小于last_action(满足下界)
         3. 存在则还要满足是下界的上确界，也就是要么任意一个满足下界的都比它小，要么就是任意一个比它大的元素都不满足下界*)
  
  
  
