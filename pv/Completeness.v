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
     pose proof H5.
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
            subst.
            (*分类n是不是0，n为0则倒数第二个就是第一个*)
            destruct rm_first_last_CPU_trace. 
            * assert (n0 = 0).
               {
                  destruct n0.
                  + tauto.
                  + inversion H5;clear H5;subst;simpl in *.
                     sets_unfold in H16.
                     destruct H16 as [? [? [? [? ?]]]].
                     pose proof app_eq_nil x0 x1 H5;clear H5.
                     destruct H19;subst.
                     inversion H16;clear H16;subst.
                     pose proof fold_ins_sem_nil  (combine (first_CPU_state.(inst) :: rm_first_program)
          (seq 0
             (Datatypes.length
                (first_CPU_state.(inst) :: rm_first_program)))) second_pc_state x H5;contradiction.
                }
                subst.
                pose proof app_last_corr rm_last_two_CPU_trace [] last_two_2_CPU_state first_CPU_state H0.
                destruct H16;subst.
                simpl.
                sets_unfold.
                split.
                ++       unfold combine_to_act_state_list,combine_to_act_state,Definition_and_soundness.Build_program_state.
                    simpl.
                    tauto.
                ++ inversion H7.
                      rewrite <- H17 in H11.
                      pose proof length_zero_iff_nil.
                      specialize (H16 (int256 -> int256) rm_first_mem_list).
                      destruct H16.
                      symmetry in H11.
                      pose proof H16 H11.
                      subst.
                      symmetry in H9.
                      pose proof app_after_nil_2 rm_last_mem_list in_list_last_mem (fun _ : int256 => zero) H9.
                      rewrite H20.
                      tauto.
            * (*下面处理n不为0，由于实际使用的条件是，first_CPU_state后面接了一个c*)
               (*所以要分，一个是倒数第二个是c,一个是倒数第二个在rm_first_CPU_trace里面*)
              assert (exists (rm_first_last_two_CPU_trace:list CPU_state),first_CPU_state ::rm_first_last_two_CPU_trace = rm_last_two_CPU_trace).
              {
                destruct rm_first_last_CPU_trace.
                + exists [].
                Print two_ele_app.
                    pose proof two_ele_app first_CPU_state c.
                    rewrite H16 in H0.
                    Search (?l ++[?x] = ?l' ++[?y]).
                    pose proof app_inj_tail rm_last_two_CPU_trace [first_CPU_state]  last_two_2_CPU_state c H0.
                    destruct H17.
                    symmetry in H17;tauto.
                  + pose proof cons_app_eq c0 rm_first_last_CPU_trace.
                     destruct H16 as [? [? ?]].
                     exists (c::x0).
                     rewrite H16 in H0.
                    pose proof app_inj_tail rm_last_two_CPU_trace (first_CPU_state :: c :: x0)  last_two_2_CPU_state x H0.
                    destruct H17.
                    symmetry in H17;tauto.
              }
              destruct H16 as [? ?].
              subst.
              rename x into rm_first_last_two_CPU_trace.
              (*-------------以上说明了现在至少有3个，除去最后两个，还能在前面找到c
              现在CPU_trace的表示方式有
              1. first_CPU_state :: rm_first_last_two_CPU_trace++
     [last_two_2_CPU_state] ++[last_CPU_state] 
              2. first_CPU_state :: c :: rm_first_last_CPU_trace ++[last_CPU_state] 
              由于分类讨论，rm_first_last_CPU_trace 现在其实是rm_first_two_last_CPU_trace*)
              simpl in H7.
              pose proof H11.
              rewrite <- H7 in H16.
              pose proof len_succ rm_first_mem_list (Datatypes.length rm_first_last_two_CPU_trace) H16.
              destruct H17 as [second_m [rm_first_two_memo ?]].
              pose proof len_succ rm_first_action_trace (Datatypes.length rm_first_last_two_CPU_trace) H7.
              destruct H19 as [second_action [rm_first_two_action ?]].
              subst.
              (*---现在action也有两种不一样的表示方式
              1. first_action :: second_action :: rm_first_two_action
              2. rm_last_action_trace ++ [last_action]*)
              assert (exists (n1:nat), S n1 = n0).
              {
                destruct n0.
                + inversion H5.
                   sets_unfold in H17;simpl in H17.
                   inversion H17.
                + exists n0;tauto.
              }
              destruct H17 as [n1 ?];subst.
              inversion H0.
              (*以上验证了n不为0*)
              rewrite <- H19 in H5.
              pose proof cons_app_eq second_m rm_first_two_memo.
              pose proof cons_app_eq second_action rm_first_two_action.
              destruct H17 as [last_two_m [rm_last_two_m ?] ].
              destruct H20 as [last_two_a [rm_first_last_two_a ?] ].
              rewrite H17 in H5.
              rewrite H20 in H5.
              subst.
              clear H4 H13 H18.
              assert (nsteps (eval_ins_list_single (first_CPU_state.(inst) :: rm_first_program)) 1 {|
          pc_state.pc := 0;
          pc_state.state :=
            {|
              memory := fun _ : int256 => zero; program_state.stack := []
            |}
        |} [{|
           pc := first_CPU_state.(pc);
           state :=
             {|
               memory := fun _ : int256 => zero;
               program_state.stack := first_CPU_state.(stack)
             |};
           action := first_action
         |}]  second_pc_state).
         {
            simpl.
            sets_unfold.
            exists second_pc_state,[{|
     pc := first_CPU_state.(pc);
     state :=
       {|
         memory := fun _ : int256 => zero;
         program_state.stack := first_CPU_state.(stack)
       |};
     action := first_action
   |}],[] .
              split.
              + tauto.
              + split.
                 - apply Definition_and_soundness.one with (l:= ( (first_CPU_state.(inst) :: rm_first_program))) (y:= [{|
     pc := first_CPU_state.(pc);
     state :=
       {|
         memory := fun _ : int256 => zero;
         program_state.stack := first_CPU_state.(stack)
       |};
     action := first_action
   |}]) (x:= {|
    pc_state.pc := 0;
    pc_state.state :=
      {| memory := fun _ : int256 => zero; program_state.stack := [] |}
  |}) (z:= second_pc_state).
  unfold fold_ins_sem.
     simpl.
     simpl in H15.
     sets_unfold.
     left.
     tauto.
     - split;tauto.
         }
        Check nsteps_n_m.
        pose proof nsteps_n_m (eval_ins_list_single (first_CPU_state.(inst) :: rm_first_program)) 1 (S n1).
        simpl in H13.
        sets_unfold in H13.
        simpl in H13.
        remember (eval_ins_list_single
                 (first_CPU_state.(inst) :: rm_first_program)) as f.
              
                 (*------这里特化了一个nsteps的性质*)
        specialize (H13 {|
          pc_state.pc := 0;
          pc_state.state :=
            {|
              memory := fun _ : int256 => zero; program_state.stack := []
            |}
        |} ([{|
          pc := first_CPU_state.(pc);
          state := 
            {|
              memory := fun _ : int256 => zero;
              program_state.stack := first_CPU_state.(stack)
            |};
          action := first_action
        |}]++(map
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
          (combine
             (combine
                (rm_first_last_two_CPU_trace ++ [last_two_2_CPU_state])
                (rm_last_two_m ++ [last_two_m]))
             (rm_first_last_two_a ++ [last_two_a])))) {|
         pc_state.pc := last_CPU_state.(pc);
         pc_state.state :=
           {|
             memory := last_mem;
             program_state.stack := last_CPU_state.(stack)
           |}
       |} ).
       destruct H13.
       clear H13.
       assert ((exists (i : pc_state) (i0 i1 : list act_state),
         i0 ++ i1 =
         [{|
            pc := first_CPU_state.(pc);
            state :=
              {|
                memory := fun _ : int256 => zero;
                program_state.stack := first_CPU_state.(stack)
              |};
            action := first_action
          |}] ++
         map
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
           (combine
              (combine
                 (rm_first_last_two_CPU_trace ++ [last_two_2_CPU_state])
                 (rm_last_two_m ++ [last_two_m]))
              (rm_first_last_two_a ++ [last_two_a])) /\
         f
           {|
             pc_state.pc := 0;
             pc_state.state :=
               {|
                 memory := fun _ : int256 => zero;
                 program_state.stack := []
               |}
           |} i0 i /\
         (exists (i2 : pc_state) (i3 i4 : list act_state),
            i3 ++ i4 = i1 /\
            f i i3 i2 /\
            nsteps f n1 i2 i4
              {|
                pc_state.pc := last_CPU_state.(pc);
                pc_state.state :=
                  {|
                    memory := last_mem;
                    program_state.stack := last_CPU_state.(stack)
                  |}
              |}))).
           {
              exists second_pc_state.
              exists  [{|
     pc := first_CPU_state.(pc);
     state :=
       {|
         memory := fun _ : int256 => zero;
         program_state.stack := first_CPU_state.(stack)
       |};
     action := first_action
   |}].     exists (map
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
    (combine
       (combine (rm_first_last_two_CPU_trace ++ [last_two_2_CPU_state])
          (rm_last_two_m ++ [last_two_m]))
       (rm_first_last_two_a ++ [last_two_a]))).
       split.
       + tauto.
       + split.
          - rewrite Heqf.
            simpl.
            apply Definition_and_soundness.one with (l:= ( (first_CPU_state.(inst) :: rm_first_program))) (y:= [{|
     pc := first_CPU_state.(pc);
     state :=
       {|
         memory := fun _ : int256 => zero;
         program_state.stack := first_CPU_state.(stack)
       |};
     action := first_action
   |}]) (x:= {|
    pc_state.pc := 0;
    pc_state.state :=
      {| memory := fun _ : int256 => zero; program_state.stack := [] |}
  |}) (z:= second_pc_state).
  unfold fold_ins_sem.
  simpl .
  sets_unfold.
       simpl in H15.
       left.
       tauto.
       - 
       Admitted.
       (*
           }
              (*这里更改了mem和action的表达方式
              现在是
              mem:
               1. (fun _ : int256 => zero) :: second_m :: rm_first_two_memo
               2. rm_last_mem_list ++ [in_list_last_mem]
               3. (fun _ : int256 => zero) ++ rm_last_two_m ++ [last_two_m]
             action:
              1.  first_action :: second_action :: rm_first_two_action
              2.  rm_last_action_trace ++ [last_action]
              3. first_action :: rm_first_last_two_a ++ [last_two_a]
              *)
              assert (nsteps (eval_ins_list_single (first_CPU_state.(inst) :: rm_first_program)) 1 (combine_to_pc_state last_two_2_CPU_state rm_last_two_m )
              (combine_to_act_state_list [last_CPU_state] [last_mem] [last_two_a]) )
                     (*
               }
            assert (nsteps
       (eval_ins_list_single (first_CPU_state.(inst) :: rm_first_program)) 1 first_CPU_state [{|
           pc := first_CPU_state.(pc);
           state :=
             {|
               memory := fun _ : int256 => zero;
               program_state.stack := first_CPU_state.(stack)
             |};
           action := first_action
         |}] )
            Search (nsteps).
            
      }
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
            
            
            
            
            
            
            
            

Admitted.*)*)
