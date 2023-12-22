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
      (*-----------------unfold H4------------------------------*)
      Admitted.
      (*
      inversion H13;clear H13.
      - admit.
     - sets_unfold in H.
       try contradiction.
       Check eval_ins_same_pc.
       pose proof eval_ins_same_pc.
       Check out_property.
      assert(exists (inst0':ins),eval_ins (inst0', 0)
        {|
          pc_state.pc := 0;
          pc_state.state :=
            {|
              memory := fun _ : int256 => zero; program_state.stack := []
            |}
        |} [first_act] second_pc_state).
        {admit.
        (*
           revert 
           
           + simpl in H3;contradiction.
           + simpl in H3;destruct H3.
              - destruct a;inversion H3;simpl in H17;discriminate.
              - 
           inversion H12;clear H12.
           + rewrite H0 in H16.
              inversion H16.
           + rewrite H0 in H15.
              inversion H15;clear H15.
              unfold combine_to_act_state,Definition_and_soundness.Build_program_state in H17.
              inversion H17;clear H17;subst. 
              simpl in H16.
              pose proof map_nil (fun x : CPU_state * (int256 -> int256) * action_type =>
         combine_to_act_state (fst (fst x)) (snd (fst x)) (snd x))
        (combine (combine rm_first_last_CPU_trace rm_first_mem_list)
           rm_first_action_trace) H18;clear H18.
              rewrite H12 in H.
              simpl in H.
              destruct first_act_trace.
              - simpl in H3.
              admit.*)
        }
      
      
      pose proof out_property (inst0,0) (combine rm_first_program(seq 1 (Datatypes.length rm_first_program))) eval_ins ({|
         pc_state.pc := 0;
         pc_state.state :=
           {|
             memory := fun _ : int256 => zero; program_state.stack := []
           |}
       |}) [first_act] second_pc_state inst0 0 rm_first_program (seq 1 (Datatypes.length rm_first_program)) H3 H.
       
    assert (eval_ins (inst0, 0)
        {|
          pc_state.pc := 0;
          pc_state.state :=
            {|
              memory := fun _ : int256 => zero; program_state.stack := []
            |}
        |} first_act_trace second_pc_state).
        {
          unfold eval_ins.
          destruct inst0.
          + tauto.
          }
           Check  
             (seq 1 (Datatypes.length rm_first_prgram)).
             Check fold_right.
             Print In.
      (*要想使用H13，就需要证明eval_ins是单射（见Out_property）*)
      (*要证明单射，就要用到时间戳，所以下面是处理时间戳来证明单射的代码*)
      (*------------------------证明单射(由于太长已经移到Lemma里面了)-----------------------------*)
      
Admitted.
*)