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


Lemma one_step_generate_one_action:
  forall (first_pc_state run_one_step_pc_state:pc_state)(act_trace:list act_state)(inst:ins)(remain_program:list ins),
fold_right
        (fun (x y : pc_state -> list act_state -> pc_state -> Prop)
           (a : pc_state) (a0 : list act_state) 
           (a1 : pc_state) => x a a0 a1 \/ y a a0 a1)
        (fun (_ : pc_state) (_ : list act_state) (_ : pc_state) => False)
        (map eval_ins
           (combine (inst :: remain_program)
              (seq 0
                 (Datatypes.length (inst::remain_program)))))
        first_pc_state act_trace run_one_step_pc_state
        -> first_pc_state.(pc) = 0
        -> act_trace <> [].
Proof.
  intros.
  assert (remain_program = []).
  {admit. }
  subst.
  simpl in H.
  destruct H.
  + destruct inst0;inversion H;discriminate.
  + contradiction.
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
 Admitted.
      
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
      exists []. (*显然在程序没有运行的时候，memory_trace=[]*)
      inversion H1;clear H1. (*只是把这个前提拿到下面来方便处理*)
      (*对于H4,即程序能正常运行，将其中的mem_list拆解出来，mem_list只在该条件中有约束,其他地方无法看出mem_list跟acition_trace中memory的关系*)
      destruct H4 as [mem_list [first_mem [last_mem [H1 ?]]]].
      (*得到第一个等于最后一个的前提*)
      inversion H0;clear H0.
      (*化简程序正常运行的条件，必须用inversion*)
      inversion H;clear H ; subst.
      (*=======================================*)
      (*--------------这一段由action_trace长度为0导出action_trace为空----------------*)
      pose proof length_zero_iff_nil action_trace.
      destruct H.
      symmetry in H5.
      pose proof H H5.
      clear H H6 H5.
      (*-----------------------action_trace为空证明结束------------------------------------------*)
      (*--------------------------------以下化简得到last_CPU_state.(stack) = [] ----------*)
      unfold combine_to_pc_state in H8.
      unfold Definition_and_soundness.Build_program_state,Definition_and_soundness.Build_pc_state in H8.
      simpl in H8.
      (*------------------------------化简完成-------------------------------------------*)
      (*--------------------------------以下化简得到first_mem = (fun _ : int256 => zero) ----------*)
      unfold Definition_and_soundness.combine_to_pc_state in H4.
      simpl in H4.
      subst.
      (*化简完成，通过化简得到很多都是空的。这几个初始条件的化简在后面也会经常用到*)
      (*================以下对于约束分开讨论==============*)
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
      (*============由于是初始情况，都挺简单的===============*)
  + intros.
     subst.
     (*------改个名字，符合实际--------*)
     rename l into rm_last_two_CPU_trace.
     rename x into last_two_2_CPU_state.
     (*--------改完了------*)
     (*----------------------------------把CPU_trace细分-----------------*)
     pose proof cons_eq last_two_2_CPU_state rm_last_two_CPU_trace.
     destruct H0 as [? [rm_first_last_CPU_trace ?]].
     rewrite H0 in H1.
     inversion H1;clear H1.
     symmetry in H7.
     subst.
     clear rm_last_CPU_trace.
    (*完整程序的CPU_trace表达方式现在有：
    1. first_CPU_state :: rm_first_last_CPU_trace ++[last_CPU_state]
    2. rm_last_two_CPU_trace ++ [last_two_2_CPU_state] ++ [last_CPU_state]
    3. 按道理还可以用rm_last_CPU_trace,但是现在rm_last_CPU_trace可以用rm_first_last_CPU_trace ++[last_CPU_state]表示，所以这个变量已经没有用了*)
    (*------------------------细分完毕----------------------*)
    (*--------------------------------把action_trace细分----------------------*)
     (*-----------以下根据action_trace的长度是等于rm_last_CPU_trace的长度，得出action_trace一定可以拆出一个action*)
     pose proof last_length rm_last_two_CPU_trace  last_two_2_CPU_state .
     rewrite H1 in H2;clear H1.
     pose proof len_succ action_trace (Datatypes.length rm_last_two_CPU_trace) H2.
                    (*这个assert证明确实能拆,但其实有lemma可以直接用,太神奇辣（气）*)
                    (*
     assert (exists (rm_last_action_trace:list action_type)(a:action_type), rm_last_action_trace++[a]=action_trace
/\Datatypes.length rm_last_two_CPU_trace = Datatypes.length rm_last_action_trace).
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
*)
     destruct H1 as[first_action [rm_first_action_trace ?]];subst.
     pose proof cons_app_eq first_action rm_first_action_trace.
     destruct H1 as [last_action [rm_last_action_trace ?]].
     simpl in H2.
     inversion H2;clear H2.
     
     (*--------------------------------化简替换完毕------------------------------*)
     (*这里化简完后，不存在action_trace,表示方式是
     1. rm_last_action_trace ++ [last_action]
     2. first_action :: rm_first_action_trace*)
     
     (*-----------------------化简前提假设------------------------*)
     (*对归纳得到的前提假设稍微化简，把需要的变量和前提填进去（按照已经有的）*)
     specialize (H program (rm_last_two_CPU_trace ++ [last_two_2_CPU_state]) rm_first_last_CPU_trace first_CPU_state last_two_2_CPU_state rm_last_action_trace).
     assert (Datatypes.length rm_first_action_trace = Datatypes.length rm_last_action_trace).
     {
        assert (length (first_action :: rm_first_action_trace) =
   length (rm_last_action_trace ++ [last_action])).
          {
            rewrite H1.
            tauto.
          }
          simpl in H2.
          pose proof last_length rm_last_action_trace last_action.
          rewrite H6 in H2.
          inversion H2.
          tauto.
     }
     pose proof H2.
     rewrite <- H7 in H2.
     pose proof H H0 (ltac:(tauto)) H2 H3;clear H.
(*------------------完成对归纳条件的初步化简,下一步-----------------------*)
(*下一步期望得到倒数第二个CPU_state确实是合法的*)
    (*-----------------------首先还是把程序满足soundness给化简一下------------------*)
     pose proof H5;clear H5. (*这一步给它拿到下面来看*)
     destruct H as  [mem_list[first_mem [last_mem [H9 H10]]]].
     (*拆出两个条件：
     1. mem_list长度和action_trace长度一样
     2. 第一步到最后一步满足语意*)
     inversion H9;clear H9.
     inversion H10;clear H10;     subst.
     (*-=-==-=-=-=-=-=-=化简初始条件*)
     inversion H;clear H.
     unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H9.
     inversion H9;clear H9.
     simpl in H.
     unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H11.
     inversion H11;clear H11.
     subst.
     (*-=-=-=-=-=-=-=-=初始条件化简完成*)
     (*处理mem_list的长度问题,因为比较简单，由mem_list长度不为1,则mem_list也可以拆出两种表示方式*)
     (*----------------------------由于这里代码复用了，所以考虑Lemma-----------------------*)
     symmetry in H5.
     pose proof len_succ mem_list (Datatypes.length rm_first_action_trace) H5.
     destruct H as [in_list_first_mem [rm_first_mem_list ?]].
(*以下代码展出action_trace的另一种表述形式，但上面已经表示好了
     pose proof cons_eq last_action rm_last_action_trace .
     destruct H10 as [first_action [rm_first_action_trace]].
     rewrite H10 in H9.
     simpl in H9.
     
     *)
     
     (* 非常好引理，使我的assert消失
     assert(exists (m:int256->int256)(rm_last_m:list (int256->int256) ),rm_last_m++[m]=mem_list).
{ 
     destruct mem_list.
     + inversion H9.
     + pose proof cons_app_eq i mem_list.
         destruct H11 as[m [rm_last ?]].
         exists m,rm_last.
         symmetry in H11.
         tauto.
}
     destruct H11 as [last_mem_in_list [rm_last_mem_list ?]].
     Print cons_eq.
     *)
     pose proof cons_app_eq in_list_first_mem rm_first_mem_list.
     destruct H9 as [in_list_last_mem [rm_last_mem_list ?]].
     subst.
     simpl in H5.
     inversion H5;clear H5.
    (*-------------------------由此，mem_list消失，由两种方式表述----------------
    1. in_list_first_mem :: rm_first_mem_list
    2. rm_last_mem_list ++ [in_list_last_mem]*)
    (*-----------由program不为空，则可以找到第一个(最后一个)inst------------*)
     assert (exists (inst0:ins)(rm_first_program:list ins),inst0::rm_first_program = program).
     {
        destruct program.
        + contradiction.
        + exists i,program.
            tauto.
     }
     destruct H as [inst0[rm_first_prgram ?]].
     subst;clear H3.
     (*----------------------program成功拆封------------------------------*)
     (*现在就剩两个条件，一个是满足自反传递闭包，一个是满足时间戳可以用，需要推出倒数第二个在program里面，之前尝试化简时间戳不太成功，这次事实化简第一个条件*)
     (*-==============化简自反传递闭包==============*)
     inversion H13;clear H13.
     rewrite H0 in H.  (*将CPU_state由++形式转化为::形式方便化简*)
      unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H.
      unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H.
      simpl in H.
      rename x into n.
      (*可以肯定现在n不为0*)
      assert (exists (n0:nat),n = S n0).
      {
        destruct n.
        + simpl in H.
            sets_unfold in H.
            inversion H;clear H.
            inversion H3.
         + exists n.
             tauto. 
      }
      destruct H3 as [n0 ?].
      subst.
      simpl in H;sets_unfold in H.
      destruct H as [second_pc_state [first_act_state [remain_act_state ? ]]].
      destruct H as [? [? ?]].
      
      
      
      
      (*以下为处理时间戳的废弃代码*)
       rewrite H8 in H1.
       rewrite H5 in H1.
       unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H9.
       rewrite H10 in H9.
       rewrite H0 in H9.
       rewrite H12 in H9.
       simpl in H9.
     inversion H9;clear H9. (*该步对时间戳分类讨论*)
     - (*以下为时间戳只有一个，即只运行一步的情况*)
        pose proof map_nil (fun x : CPU_state * (int256 -> int256) * action_type =>
         {|
           pc := (fst (fst x)).(pc);
           state :=
             {|
               memory := snd (fst x);
               program_state.stack := (fst (fst x)).(stack)
             |};
           action := snd x
         |}) (combine (combine rm_first_last_CPU_trace rm_first_mem_list)
           rm_first_action_trace).
       pose proof H9 H11.
       clear H9 H11.
       rename x0 into first_pc_state.
       (*
      pose proof cons_before_nil x0 ({| pc := 0 ; state := {| memory := first_mem_in_list; program_state.stack := [] |}; action := first_action |}) (map (fun x : CPU_state * (int256 -> int256) * action_type => {| pc := (fst (fst x)).(pc); state := {| memory := snd (fst x); program_state.stack := (fst (fst x)).(stack) |}; action := snd x |})
          (combine (combine rm_first_last_CPU_trace rm_first_mem_list) rm_first_action_trace)).
       pose proof H9 H8;clear H8 H9.*)
       simpl in H7.
       
       destruct H13.
       pose proof H1;clear H1.
       rename x into n.
       inversion H;clear H.
       rewrite H14 in H8.
       rewrite H5 in H8.
       subst.
      pose proof H6.
      pose proof H0.
      pose proof H12.
      pose proof H10.
      clear H6 H0 H12 H10.
      rewrite H1 in H13.
            rewrite H7 in H13.
                  rewrite H8 in H13.
          unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H13.
                unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H13.
        rewrite H14 in H13.
                rewrite H5 in H13.
        simpl in H13.
        rewrite H9 in H13.
        assert (n=1).
        {
            destruct n.
            + simpl in H13;sets_unfold in H13;inversion H13;inversion H0.
            + destruct n.
                - tauto.
                - simpl in H13;sets_unfold in H13;pose proof H13;clear H13.
                  simpl in H0.
                  destruct H0 as [unknow_pc_state [act_trace_1 [act_trace_2 ?] ]].
                  destruct H0 as [? [? [? [? [? [? [? ?]]]] ]]]. 
                  rename unknow_pc_state into run_one_step_pc_state.
                  rename x into run_two_step_pc_state.
                  inversion H6;clear H6.
                  subst.
                  unfold fold_ins_sem in H15.
                  sets_unfold in H15.
                  assert (exists (inst0 inst1:ins)(remain_program:list ins) ,inst0::inst1::remain_program = program).
                  {
                    destruct program.
                    + contradiction.
                    + destruct program.
                       - inversion H12;clear H12;subst.
                         unfold fold_ins_sem in H6.
                         sets_unfold in H6.
                         destruct i.
                         * (*jimpi*)
                         inversion H15;clear H15.
                         unfold eval_ins in H10.
                         inversion H10;clear H10.
                         inversion H6;clear H6.
                         unfold eval_ins in H10.
                         inversion H10.
                         subst.
                         simpl in *.
                         inversion H18.
                          ++ simpl in *. contradiction.
                          ++ simpl in *. contradiction.
                          * (*jump*)
                                                   inversion H15;clear H15.
                         unfold eval_ins in H10.
                         inversion H10;clear H10.
                         inversion H6;clear H6.
                         unfold eval_ins in H10.
                         inversion H10.
                         subst.
                         simpl in *.
                         inversion H18.
                          ++ simpl in *. contradiction.
                          ++ simpl in *. contradiction.
                          * (*pop*)
                                                   inversion H15;clear H15.
                         unfold eval_ins in H10.
                         inversion H10;clear H10.
                         inversion H6;clear H6.
                         unfold eval_ins in H10.
                         inversion H10.
                         subst.
                         simpl in *.
                         inversion H18.
                          ++ simpl in *. inversion H19.
                          ++ simpl in *. inversion H19.
                          ++ simpl in *. contradiction.
                          * (*add*)
                                                   inversion H15;clear H15.
                         unfold eval_ins in H10.
                         inversion H10;clear H10.
                         inversion H6;clear H6.
                         unfold eval_ins in H10.
                         inversion H10.
                         subst.
                         simpl in *.
                         inversion H18.
                          ++ simpl in *. inversion H19.
                          ++ simpl in *. inversion H19.
                          ++ simpl in *. contradiction.
                          * (*mul*)
                                                   inversion H15;clear H15.
                         unfold eval_ins in H10.
                         inversion H10;clear H10.
                         inversion H6;clear H6.
                         unfold eval_ins in H10.
                         inversion H10.
                         subst.
                         simpl in *.
                         inversion H18.
                          ++ simpl in *. inversion H19.
                          ++ simpl in *. inversion H19.
                          ++ simpl in *. contradiction.
                          * (*sub*)
                                                   inversion H15;clear H15.
                         unfold eval_ins in H10.
                         inversion H10;clear H10.
                         inversion H6;clear H6.
                         unfold eval_ins in H10.
                         inversion H10.
                         subst.
                         simpl in *.
                         inversion H18.
                          ++ simpl in *. inversion H19.
                          ++ simpl in *. inversion H19.
                          ++ simpl in *. contradiction.
                          * (*mload*)
                                                   inversion H15;clear H15.
                         unfold eval_ins in H10.
                         inversion H10;clear H10.
                         inversion H6;clear H6.
                         unfold eval_ins in H10.
                         inversion H10.
                         subst.
                         simpl in *.
                         inversion H18.
                          ++ simpl in *. contradiction.
                          ++ simpl in *. contradiction.
                          * (*mstore*)
                                                   inversion H15;clear H15.
                         unfold eval_ins in H10.
                         inversion H10;clear H10.
                         inversion H6;clear H6.
                         unfold eval_ins in H10.
                         inversion H10.
                         subst.
                         simpl in *.
                         inversion H18.
                          ++ simpl in *. contradiction.
                          ++ simpl in *. contradiction.
                          * (*push*)
                                                   inversion H15;clear H15.
                         unfold eval_ins in H10.
                         inversion H10;clear H10.
                         inversion H6;clear H6.
                         unfold eval_ins in H10.
                         inversion H10.
                         subst.
                         inversion H10.
                         simpl in *.
                          ++ simpl in *. subst. inversion H0.
                          ++ simpl in *. contradiction.
                          ++ simpl in *. contradiction.
                      - exists i,i0,program.
                        tauto.
                  }
                  destruct H6 as [inst0 [inst1 [remain_program]]].
                  subst.
                  inversion H12;clear H12;subst.
                  unfold fold_ins_sem in H6;sets_unfold in H6.
                  assert (exists (a:act_state), act_trace_1 = [a]).
                  {
                    
                  }
        }
        assert (In (last_two_2_CPU_state.(inst), last_two_2_CPU_state.(pc))
       (combine program (seq 0 (Datatypes.length program)))).
       {
        + destruct last_two_2_CPU_state.
       }
       destruct n.
       * inversion H13;clear H13.
          sets_unfold in H1.
          simpl in H14,H1.
          unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H1.
          rewrite H10 in H1.
          rewrite H0 in H1.
          rewrite H12 in H1.
          inversion H1.
       * (*当n不等于0的情况，其实就是要找n=1的情况，所以还要对S n的n归纳*)
          destruct n.
          ++ inversion H13;clear H13.
                simpl in H1.
                sets_unfold in H1.
                destruct H1 as [act_1 [act_2 [H1 [? [? ?]]]]].
                subst.
                inversion H13;clear H13;subst.
                unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H8.
                unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H1.
                rewrite H10 in H1.
                rewrite H0 in H1.
                rewrite H12 in H1.
                simpl in H1.
                assert (exists (a:act_state)(rm_a_action:list act_state), a::rm_a_action=act_1).
                {
                   destruct act_1.
                  +inversion H1.
                  + exists a,act_1.
                      tauto.
                }
                destruct H13 as [first_act [rm_first_act ?] ].
                subst.
                inversion H1;clear H1.
                destruct first_action.
                simpl in H11.

                unfold fold_ins_sem in H8.
                sets_unfold in H8.
                inversion H;clear H.
                unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H5.
                inversion H5;clear H5.
                simpl in H.
                unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H7.
                inversion H7;clear H7.
                subst.
                rewrite H6 in H8.
                rewrite H5 in H8.
                assert (rm_first_act = []).
                {
                  destruct rm_first_act.
                  + tauto.
                  + Print fold_right.
                      destruct program.
                      - contradiction.
                      - simpl in H8.
                        destruct H8.
                        * destruct i;inversion H.
                        * destruct program.
                          ++ simpl in H. contradiction.
                          ++ simpl in H.
                                destruct H.
                                -- destruct i0;inversion H.
                                -- inversion H4.
                                    ** inversion H0.
                                        subst.
                                        rewrite <- H10 in H.
                                        destruct program.
                                        +++ simpl in H;contradiction.
                                        +++ simpl in H.
                                                 destruct H.
                                                 --- destruct i;inversion H.
                                                 ---
                }   
                subst.
                simpl in H8.
                assert(rm_first_last_CPU_trace = [] /\ rm_first_mem_list = [] /\ rm_first_action_trace).
                destruct mem_ins0.
                -- exists [({| timestamp := timestamp0; mem_ins := read address value |})].
                
                   inversion H8.
                destruct program. (*对program归纳，找到运行的第一步*)
                -- contradiction.
                -- inversion H8.
                   ** destruct i.
                       +++ inversion H13.
                

       
       
       
       
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
