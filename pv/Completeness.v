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

Search int256.
Definition my_constant:int256 :=Int256.repr 1.

Lemma a_or_false:
  forall [A:Prop],A\/False->A.
Proof.
  intros.
  destruct H.
  + tauto.
  + contradiction.
Qed.

Theorem completeness_of_example:
forall (program: list ins)(CPU_trace rm_first_CPU_trace rm_last_CPU_trace:
list CPU_state)
  (first_CPU_state last_CPU_state: CPU_state)
  (action_trace: list action_type),
  program = [(PUSH32 (Int256.repr 1))] -> (*program取特殊值*)
  CPU_trace = cons first_CPU_state rm_first_CPU_trace ->
  CPU_trace = rm_last_CPU_trace ++ [last_CPU_state] ->
  length rm_last_CPU_trace = length action_trace -> (* 新增条件 *)
  program <> [] -> (* 新增条件 *)
  multiset_constraint CPU_trace program -> (* 新增条件 *)(*Used to be like last version,now no difference*)
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
  apply rev_ind with (l:=rm_last_CPU_trace).
  +
  intros.
  subst.
  clear H3.
  inversion H4;rename H4 into G.
  simpl in H.
  inversion H;clear H.
  pose proof a_or_false H7. 
  clear H7.
  inversion H;clear H.
  symmetry in H9,H10.
  rewrite H9 in H4.
  rewrite H10 in H4.
  destruct H5 as [mem_list [first_mem[last_mem[? ?]]]].
  inversion H5;clear H5.
  simpl in *;subst.
  destruct H14.
    assert(rm_first_CPU_trace=[]).
  {admit. }
  subst.
  assert (action_trace=[]).
  {admit. }
  inversion H1.
  subst.
   assert (mem_list=[]).
  {admit. }
  inversion H1.
  subst.
  exists [].
  destruct x.
  - simpl in H0;sets_unfold in H0.
    destruct H0;subst.
    split.
    ++
           apply trace_CPU with (CPU_trace:=[last_CPU_state])(rm_first_CPU_trace:=[])(first_CPU_state:=last_CPU_state).
          -- tauto.
          -- tauto.
          -- tauto.
          -- pose proof adjacent_CPU_state_nil eval_constraint last_CPU_state.
              tauto.
      ++ tauto.
      ++   apply ActionListTraceNil.
      ++ apply trace_action with (CPU_trace:=[last_CPU_state]) (action_trace:=[]).
        apply adjacent_CPU_state_for_action_trace_nil with (x:= last_CPU_state).
      ++ apply permutation with (action_trace:=[])(memory_trace:=[]).
        simpl.
        apply perm_nil.
      ++ apply trace_momory_nil.
      ++ apply public with (program:= [PUSH32 (repr 1)])(CPU_trace:= [last_CPU_state])(action_trace:=[])(memory_trace:=[]).
    -simpl in H0;sets_unfold in H0.
     destruct H0 as [? [? [? [? [? ?]]]]].
     unfold combine_to_act_state_list in H0.
     simpl in H0.
     inversion H3;clear H3;simpl in *;subst.
     unfold fold_ins_sem in H5; sets_unfold in H5.
     pose proof one_step_generate_one_action (combine_to_pc_state last_CPU_state
          (fun _ : int256 => zero)) x0 x1 [(PUSH32 (repr 1))]  0 H5.
     admit.
     + intros.
     destruct H6 as [mem_list [first_mem [last_mem [? ?]]]].
         inversion H7;clear H7;simpl in *;subst.
         destruct H12.
         destruct x0.
         -
         simpl in H0;sets_unfold in H0;destruct H0.
      unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H0.
          simpl in H0.
          pose proof map_eq_nil(fun x : CPU_state * (int256 -> int256) * action_type =>
        {|
          pc := (fst (fst x)).(pc);
          state :=
            {|
              memory := snd (fst x);
              program_state.stack := (fst (fst x)).(stack)
            |};
          action := snd x
        |}) (combine (combine (l ++ [x]) mem_list) action_trace) H0.
        admit.
        -simpl in H0;sets_unfold in H0.
         destruct H0 as [? [? [? [? [? ?]]]]].
         assert(x0 = 0).
         {admit. }
         subst.
         simpl in H7;sets_unfold in H7.
         destruct H7;subst.
         inversion H1;clear H1;subst;simpl in *.
         inversion H7;clear H7.
         simpl in H1.
         inversion H1; clear H1;simpl in *;subst.
         ++ unfold Definition_and_soundness.Build_program_state in H7.
                exists [].
                Admitted.
         
     
     

      


Theorem completeness_of_protocol:
forall (program: list ins)(CPU_trace rm_first_CPU_trace rm_last_CPU_trace:
list CPU_state)
  (first_CPU_state last_CPU_state: CPU_state)
  (action_trace: list action_type),
  CPU_trace = cons first_CPU_state rm_first_CPU_trace ->
  CPU_trace = rm_last_CPU_trace ++ [last_CPU_state] ->
  length rm_last_CPU_trace = length action_trace -> (* 新增条件 *)
  program <> [] -> (* 新增条件 *)
  multiset_constraint CPU_trace program -> (* 新增条件 *)(*Used to be like last version,now no difference*)
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
      - tauto.
       (*apply trace_multiset with (program:= program) (CPU_trace:= [last_CPU_state]).
        destruct program.
        * contradiction.
        * simpl in *.
          right.
          ++ tauto.
          ++ apply Forall_nil.
          fu*k multiset    ******** ****** ,**** !@#$%^&*( *&^%$ zaku zaku
          *)
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
     pose proof H5.
     pose proof H4.
     rename H6 into B.
     rename H0 into G. (*增援未来*)
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
     destruct H as [inst0[rm_first_program ?]].
     subst;clear H3.
     
     (*----------------------program成功拆封------------------------------*)
     (*现在就剩两个条件，一个是满足自反传递闭包，一个是满足时间戳可以用，需要推出倒数第二个在program里面，之前尝试化简时间戳不太成功，这次事实化简第一个条件*)
     (*-==============化简自反传递闭包==============*)
     inversion H13;clear H13.
     rewrite H0 in H.  (*将CPU_state由++形式转化为::形式方便化简*)
      unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H.
      unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state in H.
      simpl in H.
      (*--------------可以肯定现在n不为0---------------------*)
      rename x into n.
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
      pose proof H.
      rename H3 into F.
      (*----------------完成对n的归纳,此时可以继续化简------------------*)
      simpl in H;sets_unfold in H.
      destruct H as [second_pc_state [first_act_trace [remain_act_trace ? ]]].
      destruct H as [? [? ?]].
      inversion H3;clear H3;subst.
      pose proof one_step_generate_one_action ({|
          pc_state.pc := first_CPU_state.(pc);
          pc_state.state :=
            {|
              memory := fun _ : int256 => zero;
              program_state.stack := first_CPU_state.(stack)
            |}
        |}) second_pc_state first_act_trace (inst0 :: rm_first_program) 0 H13.
      rewrite H14 in H13.
      rewrite H10 in H13.
      simpl in H13.
      pose proof length_one_iff_single first_act_trace .
      destruct H15.
      clear H16.
      pose proof H15 H3;clear H3 H15.
      destruct H16 as [first_act ?].
      subst.
      inversion H;clear H.
      Check fold_ins_sem.
      (*----------化简得到3个条件-----------
      1. 已知了action_trace的第一个
      2. 已知第一步的单步
      3. 已知第二步可以走到最后一步
      接下来证明思路的问题是：已知的都是前几步，如何证明倒数第二步能到最后一步*)
      (*或者说，接下来需要思考，
      什么条件能证明出来某一个CPU_state的inst和pc In program*)
      (*给条件的是最后一个不方便证明，前面按道理都可以证明，所以有没有可能*)
      (*是归纳地证明，第一个可以，然后前一个可以则后一个可以*)
      (*-------------对这第一步的单步化简---------------*)
      (*----由整个程序满足multiset推出除去最后一个也满足multiset---------------------*)
      pose proof multiset_subst.
      specialize (H rm_first_last_CPU_trace (inst0 :: rm_first_program) first_CPU_state  last_CPU_state).
      pose proof H H4. clear H.
      rewrite <- H0 in H3.
      pose proof H8 H3. clear H8.
      (*-------------------证明完毕----------------*)
      (*接下来尝试证明第一步能运行到倒数第二步*)
      (*------------------首先要找到第一步到倒数第二步的mem_list和last_mem,也就是原本的倒数第二个mem-----------*)
      assert (length rm_first_mem_list = length rm_last_mem_list).
      {
        assert (length (in_list_first_mem :: rm_first_mem_list ) = length ( rm_last_mem_list ++ [in_list_last_mem])).
        {
          rewrite H9;tauto.
          }
          simpl in H8.
          pose proof last_length rm_last_mem_list in_list_last_mem.
          rewrite H17 in H8.
          inversion H8.
          tauto.
       }
       (*-------以上补证了mem_list 除去第一个和除去最后一个长度相同*)
       inversion H4;clear H4;subst.
       inversion H17;clear H17;subst.
       rewrite H14 in H16.
       assert (first_CPU_state.(inst)  = inst0).
       {
           inversion H16;clear H16.
           + inversion H4.
              symmetry in H16.
              tauto.
            + pose proof zero_not_in_seq_one (Datatypes.length rm_first_program).
              pose proof in_combine_r rm_first_program (seq 1 (Datatypes.length rm_first_program)) first_CPU_state.(inst) 0 H4.
              pose proof H15 H16;contradiction.
       }
      Print fold_right.
      
      (*通过H13得到第一步确实符合语意（反面情况已经证好）*)
      inversion H13;clear H13.
      - subst.
        clear H16.
        (*-------------进入子证明--------------*)
              assert (
        (exists
       (mem_list : list (int256 -> int256)) (first_mem
                                             last_mem : 
                                             int256 -> int256),
       Datatypes.length mem_list = Datatypes.length rm_last_action_trace /\
       eval_ins_list (first_CPU_state.(inst) :: rm_first_program)
         (combine_to_pc_state first_CPU_state first_mem)
         (combine_to_act_state_list rm_last_two_CPU_trace mem_list
            rm_last_action_trace)
         (combine_to_pc_state last_two_2_CPU_state last_mem))
      ).
            {
            (*------------确认从第一步到倒数第二步的mem_list和last mem-------*)
            (*现在mem_list的表达方式有
            1. in_list_first_mem :: rm_first_mem_list
            2.  rm_last_mem_list ++ [in_list_last_mem]
            其中in_list_first_mem应该就是f(x)=0
           有一个last_mem,特指最后一步的mem状态*)
        exists (rm_last_mem_list),in_list_first_mem,in_list_last_mem.
        split.
        + rewrite H6 in H11.
           rewrite H8 in H11.
           rewrite H11.
           tauto.
        + (*下面证明最后一个能从第一个运行到倒数第二个所需要的条件*)
        (*----------这里应该是想确认first_mem是f(x)=0但是有点多余------------*)
        assert (     (pc_state.state (combine_to_pc_state first_CPU_state in_list_first_mem)).(memory) =
(fun _ : int256 => zero)/\program_state.stack
  (pc_state.state (combine_to_pc_state first_CPU_state in_list_first_mem)) =
[]).
          {
          unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state.
                      simpl in H15.
            split;simpl;            destruct first_CPU_state.(inst);inversion H15;clear H15;simpl in *;subst;inversion H13;symmetry in H15;tauto.
          }
          destruct H4.
        apply sigma with (l:= (first_CPU_state.(inst) :: rm_first_program)) (x:=   (combine_to_pc_state first_CPU_state in_list_first_mem)) (y:=   (combine_to_act_state_list rm_last_two_CPU_trace rm_last_mem_list
     rm_last_action_trace)) (z:=   (combine_to_pc_state last_two_2_CPU_state in_list_last_mem)). (*分开我们要证的内容*)
          - tauto.
          - tauto.
          - tauto.
          - (*这里证明时间戳确实是递增*)
            rewrite H1 in H12.
            rewrite H9 in H12.
            pose proof combine_to_act_state_list_app (rm_last_two_CPU_trace)(rm_last_mem_list)  rm_last_action_trace last_two_2_CPU_state in_list_last_mem last_action.
            assert (length rm_last_two_CPU_trace = length rm_last_mem_list).
            {
              rewrite <- H7 in H11.
              rewrite <- H11 in H8.
              tauto.
            }
            assert (Datatypes.length rm_last_mem_list = Datatypes.length rm_last_action_trace).
            {
              rewrite H8 in H11.
              rewrite H11 in H6.
              tauto.
            }
            pose proof H16 H17 H19;clear H16.
            rewrite H20 in H12.
            assert (exists (last:act_state), combine_to_act_state_list [last_two_2_CPU_state]
           [in_list_last_mem] [last_action] = [last]).
           {
            unfold combine_to_act_state_list .
            simpl.
            exists (combine_to_act_state last_two_2_CPU_state in_list_last_mem last_action).
            tauto.
           }
            destruct H16.
            rewrite H16 in H12.
            pose proof Increasing_timestamp_subst  (combine_to_act_state_list rm_last_two_CPU_trace rm_last_mem_list rm_last_action_trace) x H12.
            tauto.
         - (*这里证明通过有限步可以从第一步到倒数第二步*)
            
            simpl.
            exists n0.
            assert (in_list_first_mem = (fun _ : int256 => zero)).
            {
              unfold eval_ins in H15.
              destruct first_CPU_state.(inst);simpl in H4;tauto.
            }
            (*----首先证明第一个mm确实是f(x)=0-------------*)
            remember (eval_ins_list_single (first_CPU_state.(inst) :: rm_first_program)) as f.
             pose proof nsteps_nsteps' f (S n0).
             (*-----------把从前往后S n0步转化为从后往前S n0步*)
             sets_unfold in H17.
             specialize (H17 {| pc_state.pc := first_CPU_state.(pc); pc_state.state := {| memory := fun _ : int256 => zero; program_state.stack := first_CPU_state.(stack) |} |} ({| pc := first_CPU_state.(pc); state := {| memory := in_list_first_mem; program_state.stack := first_CPU_state.(stack) |}; action := first_action |}
       :: map
            (fun x : CPU_state * (int256 -> int256) * action_type =>
             {| pc := (fst (fst x)).(pc); state := {| memory := snd (fst x); program_state.stack := (fst (fst x)).(stack) |}; action := snd x |})
            (combine (combine rm_first_last_CPU_trace rm_first_mem_list) rm_first_action_trace)) {| pc_state.pc := last_CPU_state.(pc); pc_state.state := {| memory := last_mem; program_state.stack := last_CPU_state.(stack) |} |}).
            destruct H17;clear H18.
            pose proof H17 F.
            simpl in H18;sets_unfold in H18.
            destruct H18 as [? [? [? [? [? ?]]]]].
            pose proof nsteps_nsteps' f n0.
            sets_unfold in H22.
            specialize (H22 {| pc_state.pc := first_CPU_state.(pc); pc_state.state := {| memory := fun _ : int256 => zero; program_state.stack := first_CPU_state.(stack) |} |} x0 x).
            destruct H22;clear H22.
            pose proof H23 H20.
           unfold combine_to_pc_state,combine_to_act_state_list,Definition_and_soundness.Build_pc_state, Definition_and_soundness.Build_program_state.
          unfold         combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state .
          pose proof one_step_generate_one_action x {| pc_state.pc := last_CPU_state.(pc); pc_state.state := {| memory := last_mem; program_state.stack := last_CPU_state.(stack) |} |} x1(first_CPU_state.(inst) :: rm_first_program) 0.
        rewrite Heqf in H21.
        simpl in H21.
       inversion H21;clear H21;subst.
       unfold fold_ins_sem in H25.
       pose proof H24 H25.
       rename H25 into A.
       clear H24 H23 H20 H19 H17.
       clear H15 H13 H4 F G H5 H3 H12.
       assert ([{| pc := first_CPU_state.(pc); state := {| memory := fun _ : int256 => zero; program_state.stack := first_CPU_state.(stack) |}; action := first_action |}] = map
           (fun x : CPU_state * (int256 -> int256) * action_type =>
            {| pc := (fst (fst x)).(pc); state := {| memory := snd (fst x); program_state.stack := (fst (fst x)).(stack) |}; action := snd x |}) [(first_CPU_state,(fun _ : int256 => zero),first_action)]).
            {
              simpl;tauto.
            }
            remember (fun x : CPU_state * (int256 -> int256) * action_type =>
            {| pc := (fst (fst x)).(pc); state := {| memory := snd (fst x); program_state.stack := (fst (fst x)).(stack) |}; action := snd x |}) as g.
         (*---这个assert把所有元素都放到map g里面---*)
            assert ({| pc := first_CPU_state.(pc); state := {| memory := fun _ : int256 => zero; program_state.stack := first_CPU_state.(stack) |}; action := first_action |}
      :: map g (combine (combine rm_first_last_CPU_trace rm_first_mem_list) rm_first_action_trace) = map g ([(first_CPU_state, fun _ : int256 => zero, first_action)] ++ (combine (combine rm_first_last_CPU_trace rm_first_mem_list) rm_first_action_trace))).
      {
        simpl. 
        simpl in H3.
        inversion H3.
        tauto.
      }
      rewrite H4 in H18.
      pose proof H0.
      pose proof H1.
      pose proof H9.
      symmetry in H5.
      (*----这个assert把map g里面的东西重新排列-----*)
      assert ([(first_CPU_state, fun _ : int256 => zero, first_action)] ++ combine (combine rm_first_last_CPU_trace rm_first_mem_list) rm_first_action_trace = (combine (combine rm_last_two_CPU_trace rm_last_mem_list) rm_last_action_trace ) ++ [(last_two_2_CPU_state ,in_list_last_mem,last_action)]).
      {
      pose proof combine_3 rm_last_two_CPU_trace last_two_2_CPU_state rm_last_mem_list in_list_last_mem rm_last_action_trace last_action.
      pose proof H1.
      pose proof H7.
      pose proof H2.
      pose proof H11.
      pose proof H8.
      rewrite <- H19 in H21.
      rewrite <- H21 in H23.
      rewrite H23 in H20.
      pose proof H15 (ltac:(symmetry in H20;tauto)) H23.
      rewrite <- H24.
      rewrite <- H5.
      rewrite <- H12.
      rewrite <- H13.
      simpl.
      tauto.
      }
      rewrite H15 in H18.
      Search (map ?f (?l ++[?x])).
      pose proof map_last g (combine (combine rm_last_two_CPU_trace rm_last_mem_list) rm_last_action_trace)  (last_two_2_CPU_state, in_list_last_mem, last_action).
      rewrite H17 in H18.
      Search (length ?l =1).
      pose proof length_one_iff_single x1.
      destruct H19.
      clear H20.
      pose proof H19 H16.
      destruct H20.
      subst. clear H19.
      inversion H18.
      Search (?l ++[?x]=(?l' ++[?y])).
      pose proof app_inj_tail x0  (map
        (fun x : CPU_state * (int256 -> int256) * action_type =>
         {| pc := (fst (fst x)).(pc); state := {| memory := snd (fst x); program_state.stack := (fst (fst x)).(stack) |}; action := snd x |})
        (combine (combine rm_last_two_CPU_trace rm_last_mem_list) rm_last_action_trace)) x2 {| pc := last_two_2_CPU_state.(pc); state := {| memory := in_list_last_mem; program_state.stack := last_two_2_CPU_state.(stack) |}; action := last_action |} H18.
        destruct H19.
        rewrite H19 in H22.
        Check fold_right_sem.
        pose proof fold_right_sem (first_CPU_state.(inst) :: rm_first_program)  x {| pc_state.pc := last_CPU_state.(pc); pc_state.state := {| memory := last_mem; program_state.stack := last_CPU_state.(stack) |} |} x2 0 A.
        destruct x2.
        destruct H23.
        inversion H21.
        subst.
        destruct x.
        simpl in H24.
        simpl in H23.
        rewrite H23 in H22.
        rewrite H24 in H22.
        tauto.
      }
      pose proof H H4.
      destruct H13.
      rename x into rm_last_mem_trace.
      clear G.
      rewrite H0 in H13.
      Print Permutation.
      inversion H13;clear H13.
      inversion H21;clear H21.
      clear H23.
      subst.
      clear H H17 H18.
      rename H4 into soundness.
      remember (eval_ins_list_single (first_CPU_state.(inst) :: rm_first_program)) as f.
      remember (fun x : CPU_state * (int256 -> int256) * action_type => {| pc := (fst (fst x)).(pc); state := {| memory := snd (fst x); program_state.stack := (fst (fst x)).(stack) |}; action := snd x |}) as g.
      remember {|
        pc_state.pc := last_CPU_state.(pc);
        pc_state.state :=
          {|
            memory := last_mem;
            program_state.stack := last_CPU_state.(stack)
          |}
      |} as last_pc_state.
      pose proof nsteps_nsteps' f (S n0).
             (*-----------把从前往后S n0步转化为从后往前S n0步*)
      sets_unfold in H.
      specialize (H {| pc_state.pc := first_CPU_state.(pc); pc_state.state := {| memory := fun _ : int256 => zero; program_state.stack := first_CPU_state.(stack) |} |} ({| pc := first_CPU_state.(pc); state := {| memory := in_list_first_mem; program_state.stack := first_CPU_state.(stack) |}; action := first_action |}
       :: map
            g
            (combine (combine rm_first_last_CPU_trace rm_first_mem_list) rm_first_action_trace)) last_pc_state).
            destruct H; clear H4.
            pose proof H F;clear H.
            simpl in H4;sets_unfold in H4.
            destruct H4 as [? [? [? [? [? ?]]]]].
            clear H4.
            pose proof one_step_generate_one_action x last_pc_state x1  (first_CPU_state.(inst) :: rm_first_program) 0.
            rewrite Heqf in H17.
            inversion H17;clear H17;subst.
            unfold fold_ins_sem in H18.
            pose proof H4 H18.
            clear H4.
            rename H18 into I.
            (*-=-----------------以下代码希望确定x1是最后一个action_trace*)
            remember (fun
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
          |}) as g.
            assert ({| pc := first_CPU_state.(pc); state := {| memory := fun _ : int256 => zero; program_state.stack := first_CPU_state.(stack) |}; action := first_action |}
      :: map g (combine (combine rm_first_last_CPU_trace rm_first_mem_list) rm_first_action_trace) = map g ([(first_CPU_state, fun _ : int256 => zero, first_action)] ++ (combine (combine rm_first_last_CPU_trace rm_first_mem_list) rm_first_action_trace))).
      {
        rewrite Heqg. 
        simpl.
        tauto.
      }
      assert ([(first_CPU_state, fun _ : int256 => zero, first_action)] ++ combine (combine rm_first_last_CPU_trace rm_first_mem_list) rm_first_action_trace = (combine (combine rm_last_two_CPU_trace rm_last_mem_list) rm_last_action_trace ) ++ [(last_two_2_CPU_state ,in_list_last_mem,last_action)]).
      {
      pose proof combine_3 rm_last_two_CPU_trace last_two_2_CPU_state rm_last_mem_list in_list_last_mem rm_last_action_trace last_action.
      pose proof H1.
      pose proof H7.
      pose proof H2.
      pose proof H11.
      pose proof H8.
      rewrite <- H23 in H25.
      rewrite <- H25 in H26.
      rewrite H26 in H24.
      pose proof H18 (ltac:(symmetry in H24;tauto)) H26.
      rewrite <- H27.
      rewrite H0.
      rewrite <- H1.
      rewrite <- H9.
      simpl.
                  assert (in_list_first_mem = (fun _ : int256 => zero)).
            {
              unfold eval_ins in H15.
              destruct first_CPU_state.(inst);inversion H15;subst;simpl in H29;
              inversion H29;tauto.
            }
      subst.
      tauto.
      }
      (*-----第三遍证明第一个mem是f(x)=0----*)
      assert (in_list_first_mem = (fun _ : int256 => zero)).
      {
        unfold eval_ins in H15.
        destruct first_CPU_state.(inst);inversion H15;subst.
        + simpl in H32; inversion H23;tauto.
        + simpl in H31; inversion H23;tauto.
        + simpl in H31; inversion H23;tauto.
        + simpl in H32; inversion H23;tauto.
        + simpl in H32; inversion H23;tauto.
        + simpl in H32; inversion H23;tauto.
        + simpl in H32; inversion H23;tauto.
        + simpl in H31; inversion H23;tauto.
        + simpl in H32; inversion H23;tauto.
      }
      subst. 
      rewrite H4 in H.
      clear H4.
      rewrite H18 in H.
      clear H18.
      assert ( x1 = map
      (fun
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
       |}) [(last_two_2_CPU_state, in_list_last_mem,
        last_action)]).
      {
        destruct x1.
        + simpl in H17;lia.
        + simpl in H17.
            inversion H17;clear H17.
            pose proof length_zero_iff_nil x1.
            destruct H4.
            clear H17. pose proof H4 H18;subst.
            pose proof map_last  (fun
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
       |}) (combine
         (combine rm_last_two_CPU_trace rm_last_mem_list)
         rm_last_action_trace) (last_two_2_CPU_state, in_list_last_mem,
        last_action).
        rewrite H17 in H;clear H17.
        pose proof app_inj_tail x0 (map
      (fun
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
       |})
      (combine
         (combine rm_last_two_CPU_trace rm_last_mem_list)
         rm_last_action_trace)) a ({|
       pc :=
         (fst
            (fst
               (last_two_2_CPU_state, in_list_last_mem,
               last_action))).(pc);
       state :=
         {|
           memory :=
             snd
               (fst
                  (last_two_2_CPU_state, in_list_last_mem,
                  last_action));
           program_state.stack :=
             (fst
                (fst
                   (last_two_2_CPU_state,
                   in_list_last_mem, last_action))).(stack)
         |};
       action :=
         snd
           (last_two_2_CPU_state, in_list_last_mem,
           last_action)
     |}) H.
     destruct H17.
     rewrite H21;tauto.
      }
      clear H17.
      subst.
      pose proof fold_right_sem (first_CPU_state.(inst) :: rm_first_program) x {|
        pc_state.pc := last_CPU_state.(pc);
        pc_state.state :=
          {|
            memory := last_mem;
            program_state.stack := last_CPU_state.(stack)
          |}
      |} ((fun
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
         (last_two_2_CPU_state, in_list_last_mem,
          last_action)) 0 I.
      destruct H4.
      destruct x.
      simpl in H4,H17;subst.
      Search (in_list_last_mem).
      remember (List.fold_right Sets.union ∅
      (map eval_ins
         (combine
            (first_CPU_state.(inst) :: rm_first_program)
            (seq 0
               (Datatypes.length
                  (first_CPU_state.(inst)
                   :: rm_first_program)))))) as h.
          
      (*check point*)
      assert ((last_action.(mem_ins)=non /\ exists (mem_trace1:list action_type),mem_trace1 = rm_last_mem_trace)\/(
  exists (add val:int256),(last_action.(mem_ins)=non ->False)/\( ((last_action.(mem_ins) = read add val)\/((last_action.(mem_ins) = write add val))) /\ ((exists (mem_trace1:list action_type), mem_trace1 = last_action::rm_last_mem_trace/\memory_constraint mem_trace1)\/ (exists (a:action_type) (l1 l2:list action_type),rm_last_mem_trace = l1 ++[a] ++l2 ->exists (mem_trace1:list action_type), mem_trace1 = l1 ++[a]++[last_action]++l2/\ memory_constraint mem_trace1))))).
      {
      admit.
      }
      destruct H4.
    * destruct H4.
      clear H17;exists rm_last_mem_trace.
      split.
      ++ apply trace_CPU with (CPU_trace:=first_CPU_state :: rm_first_last_CPU_trace ++ [last_CPU_state]) (rm_first_CPU_trace:=rm_first_last_CPU_trace ++ [last_CPU_state])(first_CPU_state:=first_CPU_state).
        -- tauto.
        -- tauto.
        -- tauto.
        -- inversion H16;clear H16.
        Search (first_CPU_state :: rm_first_last_CPU_trace).
        rewrite <- H0 in H23.
            assert (eval_constraint last_two_2_CPU_state last_CPU_state).
            {admit. }
            pose proof adjacent_CPU_state_cons eval_constraint last_two_2_CPU_state last_CPU_state  rm_last_two_CPU_trace H16 H23.
      assert (rm_last_two_CPU_trace ++
         [last_two_2_CPU_state] ++ [last_CPU_state]= (first_CPU_state :: rm_first_last_CPU_trace ++ [last_CPU_state])).
         {
         admit.  (*这个很简单，帮我做一下。FLAG*)
         }
         rewrite <- H26;tauto.
       ++ tauto.
       ++ rewrite H1.
       Search rm_first_action_trace.
       destruct rm_last_action_trace.
       -- 
       pose proof ActionListTraceSingle last_action.
       Search (first_action :: rm_first_action_trace).
       rewrite H1 in H12.
       assert(rm_last_two_CPU_trace=[]).
       {admit. }(*这个很简单，帮我做一下。FLAG*)
       assert(rm_first_mem_list=[]).
              {admit. }(*这个很简单，帮我做一下。FLAG*)
       subst.
       simpl in H12.
       inversion H12.
       ** inversion H21;clear H21.
            subst.
            pose proof H17 H24;simpl.
            tauto.
       **       unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H18.
            simpl in H18. 
            pose proof app_inj_tail (l++[x]) [] y {|
         pc := last_two_2_CPU_state.(pc);
         state :=
           {|
             memory := fun _ : int256 => zero;
             program_state.stack := last_two_2_CPU_state.(stack)
           |};
         action := last_action
       |} H18.
       destruct H24.
       pose proof app_eq_nil l [x] H24.
       destruct H26.
       discriminate.
      -- pose proof cons_app_eq a rm_last_action_trace.
          destruct H17 as [last_two_action [rm_last_two_action ?]].
          rewrite H17.
          Search ((first_action :: rm_first_action_trace)).
          rewrite H1 in H12.
          assert (((a :: rm_last_action_trace) ++ [last_action]) = ((rm_last_two_action ++ [last_two_action]) ++ [last_action])).
          {admit. }(*这个很简单，帮我做一下。FLAG*)
          rewrite H18 in H12.
          inversion H12.
          ** admit. (*这个是证明矛盾，比较长，不想做还是我做。FLAG*)
          ** admit. (*这个一样是矛盾，帮我做一下。FLAG*)
          ** Search (rm_first_mem_list).
          rewrite H9 in H21.
          Search (rm_last_two_action ++ [last_two_action]).
          rename rm_last_action_trace into rm_first_last_action_trace.
          assert (exists (a:CPU_state)(b:list CPU_state),rm_last_two_CPU_trace = (b++[a])).
          {admit. }(*这个很简单，帮我做一下。FLAG*)
          assert (exists (a:(int256->int256))(b:list (int256->int256)),rm_last_mem_list = (b++[a])).
          {admit. }(*这个很简单，帮我做一下。FLAG*)
          destruct H25 as [last_3_CPU_state [rm_last_3_CPU_trace ?]].
                    destruct H26 as [last_2_mem [rm_last_2_mem_list ?]].
         rewrite H26 in H21.
         rewrite H25 in H21.
         assert ([x]=(combine_to_act_state_list [last_3_CPU_state] [last_2_mem] [last_two_action])).
         {admit. }(*这个有点复杂，有空可以做一下。FLAG*)
         assert ([y]=(combine_to_act_state_list [last_two_2_CPU_state] [in_list_last_mem][last_action] )).
                  {admit. }(*这个一样复杂，。FLAG*)
unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state in H27,H28.
    simpl in H27,H28.
    inversion H27;clear H27.
        inversion H28;clear H28.
     inversion H23.
     rewrite H29 in H28.
          rewrite H30 in H28.
     simpl in H28.
     Search (a :: rm_first_last_action_trace).
     rewrite H17 in H19.
     pose proof ActionListTraceCons last_two_action last_action rm_last_two_action H28 H19.
     tauto.
    ++ apply trace_action with (CPU_trace:=first_CPU_state :: rm_first_last_CPU_trace ++ [last_CPU_state]) (action_trace:=first_action :: rm_first_action_trace).
        inversion H20;clear H20;simpl in *;subst.
        inversion H17.
        ** clear H17;simpl in *;subst.
        assert (Check_action first_CPU_state last_CPU_state first_action).
        {admit. }
        pose proof adjacent_CPU_state_for_action_trace_nil Check_action  first_CPU_state.
        assert(rm_first_action_trace = []).
        {admit. }(*这个很简单，帮我做一下。FLAG*)
        rewrite H20.
        simpl in *.
        pose proof adjacent_CPU_state_for_action_trace_cons Check_action first_CPU_state last_CPU_state first_action [] [] H17 H18.
        tauto.
        ** 
            pose proof adjacent_CPU_state_for_action_trace_cons Check_action x y action0 (l) l_action H20 H21.
        Search (map ?p (?l++[?x])).
        assert (y=last_two_2_CPU_state).
        {admit. }(*这个很简单，帮我做一下。FLAG*)
        assert ((l ++ [x])=rm_last_two_CPU_trace).
        {admit. }(*这个很简单，帮我做一下。FLAG*)
        assert (  (first_CPU_state
   :: rm_first_last_CPU_trace ++ [last_CPU_state])=rm_last_two_CPU_trace ++ [last_two_2_CPU_state;last_CPU_state]).
   {admit. }(*这个很简单，帮我做一下。FLAG*)
        rewrite H27.
rewrite H1.
        assert (Check_action last_two_2_CPU_state last_CPU_state last_action).
        {admit. }
        rewrite H25 in H24.
                rewrite H26 in H24.
        Search (l_action ++ [action0]).
        rewrite H23 in H24.
        pose proof adjacent_CPU_state_for_action_trace_cons Check_action last_two_2_CPU_state last_CPU_state last_action (rm_last_two_CPU_trace) rm_last_action_trace H28 H24.
        Search ((?l++[?x])++[?y]).
        pose proof same_list rm_last_two_CPU_trace last_two_2_CPU_state last_CPU_state.
        rewrite <- H30 in H29.
        tauto.
      ++
          apply permutation with (action_trace:=  (first_action :: rm_first_action_trace))(memory_trace:=rm_last_mem_trace).
        rewrite H1.
        assert (filter mem_ins_type_is_not_non
     (rm_last_action_trace ++ [last_action])=(filter mem_ins_type_is_not_non
           rm_last_action_trace)).
           {admit. }(*这个有点复杂但是Search filter就行，帮我做一下。FLAG*)
       rewrite H17;tauto.
      ++ tauto.
      ++ apply public with (program:=  (first_CPU_state.(inst) :: rm_first_program))(CPU_trace:= (first_CPU_state
   :: rm_first_last_CPU_trace ++ [last_CPU_state]))(action_trace:=(first_action :: rm_first_action_trace))(memory_trace:=rm_last_mem_trace).
   *  (*读或写的情况*)
      destruct H4 as [add[val [? ?]]].
      destruct last_action.(mem_ins).
       ++ clear H4. 
       destruct H17.
       destruct H4.
       --   inversion H4;clear H4.
           admit.
       --  discriminate.
       ++ clear H4. 
       destruct H17.
       destruct H4.
       --   discriminate.
       --  admit.
       ++ pose proof H4 (ltac:(tauto)).
            contradiction.
      - sets_unfold in H15.
        pose proof eval_ins_same_pc.
        pose proof out_property.
        specialize (H17 ins pc_state (list act_state) pc_state).
        specialize(H17 (combine rm_first_program (seq 1 (Datatypes.length rm_first_program)))).
        specialize (H17 eval_ins).
        specialize(H17  ({|          pc_state.pc := 0;          pc_state.state :=            {|              memory := fun _ : int256 => zero; program_state.stack := []            |}        |})  [{|           pc := first_CPU_state.(pc);           state :=             {|               memory := in_list_first_mem;               program_state.stack := first_CPU_state.(stack)             |};           action := first_action         |}] second_pc_state).
       specialize (H17 rm_first_program (seq 1 (Datatypes.length rm_first_program))).
       pose proof H17 H13 H15 (ltac:(tauto));clear H17.
       pose proof seq_length (Datatypes.length rm_first_program) 1.
       symmetry in H17.
       pose proof H19 H17;clear H19.
       destruct H20 as [x [? ?]].
       destruct x.
       unfold eval_ins in H19.
       destruct i;inversion H19;subst;inversion H25;simpl in *.
       ++  pose proof in_combine_r rm_first_program (seq 1 (Datatypes.length rm_first_program)) JUMPI 0 H20.
            pose proof zero_not_in_seq_one (Datatypes.length rm_first_program) H4;contradiction.
             ++  pose proof in_combine_r rm_first_program (seq 1 (Datatypes.length rm_first_program)) JUMP 0 H20.
            pose proof zero_not_in_seq_one (Datatypes.length rm_first_program) H4;contradiction.
              ++  pose proof in_combine_r rm_first_program (seq 1 (Datatypes.length rm_first_program)) POP 0 H20.
            pose proof zero_not_in_seq_one (Datatypes.length rm_first_program) H4;contradiction.
            ++  pose proof in_combine_r rm_first_program (seq 1 (Datatypes.length rm_first_program)) ADD 0 H20.
            pose proof zero_not_in_seq_one (Datatypes.length rm_first_program) H4;contradiction.
            ++  pose proof in_combine_r rm_first_program (seq 1 (Datatypes.length rm_first_program)) MUL 0 H20.
            pose proof zero_not_in_seq_one (Datatypes.length rm_first_program) H4;contradiction.
            ++  pose proof in_combine_r rm_first_program (seq 1 (Datatypes.length rm_first_program)) SUB 0 H20.
            pose proof zero_not_in_seq_one (Datatypes.length rm_first_program) H4;contradiction.
            ++  pose proof in_combine_r rm_first_program (seq 1 (Datatypes.length rm_first_program)) MLOAD 0 H20.
            pose proof zero_not_in_seq_one (Datatypes.length rm_first_program) H4;contradiction.
            ++  pose proof in_combine_r rm_first_program (seq 1 (Datatypes.length rm_first_program)) MSTORE 0 H20.
            pose proof zero_not_in_seq_one (Datatypes.length rm_first_program) H4;contradiction.
            ++  pose proof in_combine_r rm_first_program (seq 1 (Datatypes.length rm_first_program)) (PUSH32 v) 0 H20.
            pose proof zero_not_in_seq_one (Datatypes.length rm_first_program) H4;contradiction.
Admitted.
           
