# 用 Coq 基于指称语义证明简单字节码程序的 trace 满足 Plonk 协议规定的一系列约束

在这个问题中，我们将给出一个简单字节码程序的指称语义，并给出了 Plonk 协议规定的一系列约束的定义。我们还会给出满足这些约束的简单字节码程序的 trace 符合指称语义的 soundness 证明，以及一系列已证明的引理作为参考。具体而言，学生需参考 `soundness_of_protocol` 的定义并给出 `completeness_of_protocol` 的定义并完成证明，关键证明代码处必须提供注释，学生还需在 `doc` 文件夹中提供一份类似 `4. soundness 证明思路` 的数学证明以说明你的证明的整体思路。

以下是说明文档，包含了一些基本的定义和引理，以及一些有用的参考资料，所有参考的代码均在文件 `pv/Definition_and_soundness.v` 中，请在 `Completeness.v` 中定义并证明 completeness_of_protocol，你可以参考 `Completeness.v` 文件开头的环境配置将引理写在多个文件中。对本大作业如有任何疑问，请及时联系助教寻求帮助。

关于环境配置的说明：本代码库使用的 coq 版本为
```
The Coq Proof Assistant, version 8.14.1
compiled with OCaml 4.11.2
```
你可以使用 `coqc -v` 命令来查看你的本地 coq 版本。如果你的本地 coq 版本不同，可以 `opam switch create` 命令来新建一个 coq 版本环境，详情见 `opam switch --help`。

在下载解压完本代码库，并安装好对应的 coq 环境后，你需要运行 `make depend` 并运行 `make all` 来编译已有的代码（如果出现报错，请检查你的 coq 版本是否正确，并在重新配好环境后先执行 `make clean`），然后你就可以和往常一样在单个文件里逐个语句执行了。

## 1. 简单字节码虚拟机与简单字节码程序的语法
- 简单字节码虚拟机是一个由不超过 1024 个 `int256` 空间的栈和一块 `int256 -> int256` 的内存组成的栈机。
- 语法的定义在 `Module Lang` 中，由如下 9 种指令组成，其中 `PUSH32` 指令有一个参数，参数是一个 256 位的无符号整数（可以认为是上课用到的 `int64` 的 256 位版）。
  ```
  Module Lang.

  Inductive ins : Type :=
  | JUMPI 
  | JUMP
  | POP
  | ADD
  | MUL
  | SUB
  | MLOAD
  | MSTORE
  | PUSH32 (v: int256)
  .

  End Lang.
  ```

## 2. 指称语义

- 单个指令的指称语义的类型如下 
  $[\![c]\!] : \text{pc} \rightarrow \text{pc} * \text{state} \rightarrow ( \text{pc} * \text{state} * \text{action} ) \rightarrow \text{pc} * \text{state} \rightarrow \text{Prop}$
  注意这里三元组中的 pc 和 state 和前面一组 pc 和 state 是相同的，这样设计是为了方便定义多个指令构成的程序的指称语义，注意在代码中我们是用 `Record pc_state` 和 `Record act_state` 实现的，而不是二元组和三元组。
  action 的定义如下，其记录了该指令执行的时间戳、内存操作类型（分别对应 `MLOAD`，`MSTORE` 和其他指令）、内存操作地址和内存操作值。
  ```
  Inductive mem_ins_type: Type := 
  | read(address: int256)(value: int256)
  | write(address: int256)(value: int256)
  | non.

  (* action is a record of timestamp, memory instruction type,
    operation address and operation value *)
  Record action_type: Type := {
    timestamp: nat;
    mem_ins: mem_ins_type;
  }.
  ```
  例：以下程序定义了 `POP` 指令的指称语义
  ```
  Inductive POP_sem: nat -> pc_state -> list act_state -> pc_state -> Prop :=
  | pop_sem:
      forall (pc: nat)(y: act_state)(x z: pc_state)(v: int256),
        x.(state) = y.(state) -> y.(action).(mem_ins) = non ->
        x.(pc) = pc -> y.(pc) = pc -> z.(pc) = pc + 1 ->
        x.(state).(stack) = cons v z.(state).(stack) ->
        y.(state).(memory) = z.(state).(memory) ->
        POP_sem pc x (cons y nil) z.
  ```

- 定义三元关系的结合如下：
  对任意集合 $R, S$， 列表 $l, l_1, l_2$，
  $(a, l, c) \in (R \circ S) \text{ iff } \exists b, l_1, l_2, (a, l_1, b) \in R, (b, l_2, c) \in S, l_1 || l_2 = l$
  定义集合上的运算 $\Omega$ 如下：
  $R^\Omega := I \cup R \cup (R \circ R) \cup (R \circ R \circ R) \cup \ldots $

- 多个指令构成的程序的指称语义的辅助定义如下 $[\![c_0; c_2; ...; c_{n-1}]\!] := ( [\![c_0]\!] (0) \cup [\![c_1]\!] (1) \cup \ldots \cup [\![c_{n-1}]\!] (n-1) )^\Omega$
  代码中的定义如下：
  ```
  Definition fold_ins_sem (l: list (ins * nat)): pc_state -> list act_state -> pc_state -> Prop :=
    fold_right Sets.union ∅ (map eval_ins l).
  
  Inductive eval_ins_list_single: list ins -> pc_state -> list act_state -> pc_state -> Prop :=
  | one: forall (l: list ins)(y: list act_state)(x z: pc_state),
    fold_ins_sem (combine l (seq 0 (length l))) x y z ->
    eval_ins_list_single l x y z.
  ```
  注意这个定义中包含了运行了任意有限条（包括 0 条） $c_0, \ldots, c_{n-1}$ 语句的情况，且程序的开始指令不一定是 $c_0$，也可以是 $c_1, \ldots, c_{n-1}$ 中的任意一个，这是为了定义与证明的方便。
  这不是我们想要的结果，因此我们实际在证明时需要加上一些限制条件，比如程序的初始 pc 必须是 1 等。

- 简单字节码程序规定程序的初始 pc 是 0，栈和内存都是空的（initial_stack 为 `nil`；initial_memory 为 `int256 -> 0`），初始时间戳为 1，且时间戳每运行一条指令加一，完整的多个指令构成的程序的指称语义代码如下：
  ```
  Inductive Increasing_timestamp: list act_state -> Prop :=
  | ActionListNil : Increasing_timestamp nil
  | ActionListSingle : forall x : act_state,
      x.(action).(timestamp) = 1 -> Increasing_timestamp (cons x nil)
  | ActionListCons : forall (x y : act_state) (l : list act_state),
      y.(action).(timestamp) = x.(action).(timestamp) + 1 ->
      Increasing_timestamp (app l (cons x nil)) -> 
      Increasing_timestamp (app (app l (cons x nil)) (cons y nil)).
  
  Inductive eval_ins_list: list ins -> pc_state -> list act_state -> pc_state -> Prop :=
  | sigma: forall (l: list ins)(x z: pc_state)(y: list act_state),
    x.(pc) = 0 ->
    x.(state).(memory) = (fun (n: int256) => Int256.zero) ->
    x.(state).(stack) = nil ->
    Increasing_timestamp y ->
    clos_refl_trans (eval_ins_list_single l) x y z ->
    eval_ins_list l x y z.
  ```

## 3. Plonk 协议规定的一系列约束

Coq 中定义的完整约束条件如下：
```
Inductive constraints: list ins -> list CPU_state -> list action_type -> list action_type -> Prop :=
| all_constraints: forall (program: list ins)(CPU_trace: list CPU_state)
  (action_trace: list action_type)(memory_trace: list action_type),
  CPU_trace_constraint CPU_trace ->
  multiset_constraint CPU_trace program ->
  action_trace_timestamp_constraint action_trace ->
  action_trace_constraint CPU_trace action_trace ->
  permutation_constraint action_trace memory_trace ->
  memory_constraint memory_trace ->
  public_constraint program CPU_trace action_trace memory_trace ->
  constraints program CPU_trace action_trace memory_trace.
```

- CPU constraints（`CPU_trace_constraint`）
  CPU state 定义如下：
  ```
  Record CPU_state: Type := {
    pc: nat;
    stack: list int256;
    inst: ins;
  }.
  ```
  CPU_trace_constraint 定义如下：
  ```
  Definition eval_constraint(x y: CPU_state): Prop :=
  match x.(inst) with
  | JUMP => JUMP_constraint x y
  | MUL => MUL_constraint x y
  | SUB => SUB_constraint x y
  | ADD => ADD_constraint x y
  | POP => POP_constraint x y
  | JUMPI => JUMPI_constraint x y
  | MLOAD => MLOAD_constraint x y
  | MSTORE => MSTORE_constraint x y
  | PUSH32 v => PUSH32_constraint v x y
  end.

  (* CPU_state列表中每相邻两个元素都满足某个性质 *)
  Inductive adjacent_CPU_state (P : CPU_state -> CPU_state -> Prop) : list CPU_state -> Prop :=
  | adjacent_CPU_state_nil : forall (x: CPU_state), adjacent_CPU_state P [x]
  | adjacent_CPU_state_cons : forall (x y : CPU_state)(l : list CPU_state),
      P x y -> adjacent_CPU_state P (l ++ [x]) -> adjacent_CPU_state P (l ++ [x] ++ [y]).

  Inductive CPU_trace_constraint: list CPU_state -> Prop :=
  | trace_CPU: forall (CPU_trace rm_first_CPU_trace: list CPU_state)
    (first_CPU_state: CPU_state),
    CPU_trace = cons first_CPU_state rm_first_CPU_trace ->
    first_CPU_state.(pc) = 0 ->
    first_CPU_state.(stack) = nil ->
    adjacent_CPU_state eval_constraint CPU_trace ->
    CPU_trace_constraint CPU_trace.
  ```
  CPU_trace 为所有 CPU_state 按时间顺序构成的列表，初始 CPU_state 需满足一定条件，相邻两个 CPU_state 需满足单个指令的指称语义
- multiset constraint
  ```
  Inductive multiset_constraint: list CPU_state -> list ins -> Prop :=
  | trace_multiset: forall (program: list ins)(CPU_trace: list CPU_state),
    Forall (fun x => In x (combine program (seq 0 (length program)))) 
    (map (fun cpu_state => (cpu_state.(inst), cpu_state.(pc))) CPU_trace) ->
    multiset_constraint CPU_trace program
  ```
  CPU_trace 中的指令和相应的 pc 与程序（即指令序列 list ins）相对应，构成所谓的多重集（由于可能有循环，所以一条指令在 CPU_trace 中可能出现不止出现一次）
- action trace check
  - `action_trace_timestamp_constraint`：相邻两个 action 需满足时间戳从一开始每次加一的约束
  - `action_trace_constraint`：action 需对应相应的指令（如果是 read，不用检验 value，如果是 write，只需验证与栈中的 value 相等）
- permutation constraint
  - action trace (删去其中的 non 指令) 和 memory trace 构成 permutation
- memory constraints
  涉及地址操作的 action trace 按照地址大小和时间戳排序，得到 memory_trace，相邻的两个 action 需满足一定性质，具体见代码
- public constraint
  这个约束其实什么都没干，可以忽略

## 4. soundness 证明思路

这里是对 soundness 证明思路的简介，由于 completeness 和 soundness 的证明方向是相反的，并不直接相关，所以不一定能照搬这里的证明思路，还需学生自己思考

```
Theorem soundness_of_protocol:
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
```

证明的整体思路是对 `action_trace` 使用反向归纳法 `apply rev_ind with (l := action_trace).` 即不用 `action_trace` 的归纳假设证明 `soundness_of_protocol` 对 `new_action :: action_trace` 成立，而是用 `action_trace` 的归纳假设证明 `soundness_of_protocol` 对 `action_trace ++ [last_action]` 成立，这样可以更好地利用 `memory_constraint` 的条件来构造新的 `last_mem`。

遇到证不出来的时候需要加强归纳条件，如要求 `length mem_list = length action_trace`，以及要求 `last_mem` 满足 `last_mem_prop` 的条件，这样就可以在归纳证明时候用 `last_mem_prop` 的条件来构造新的 `last_mem`。

具体证明思路如下（仅为数学证明，与真实代码并不一定一致）：

- 归纳基础：action trace 为 `nil`: 易证

- 假设 action trace 为 `action_trace'` 时 `soundness_of_protocol` 为真

- 下证明 action trace 为 `action_trace` 即 `action_trace' ++ [last_action]` 时`soundness_of_protocol` 也为真，注意到我们需要假定所有约束都满足，然后利用归纳假设并构造一个新的 `last_mem` 来证明 `soundness_of_protocol`。

  假设倒数第二步指令是 $c_i$ ($0 \leq i \leq n-1$)，最后一步指令是 $c_m$ ($0 \leq m \leq n-1$)，$c_m$ 之后 CPU state 中 pc 为 m'

  1. 1. 如果 `last_action` 是非读写（`non`）操作，过滤非读写操作后的 `action_trace` 和过滤非读写操作后的 `action_trace'` 相同，因此 `action_trace'` 与 `memory_constraint` 满足 permutation constraint
     1. 如果 `last_action` 是读写操作，其对应 `memory_trace` 中相应 address 的 action 中最后一次读写操作，因为根据 `last_mem_prop` 其 `timestamp` 最大，可以证明非读写操作后过滤后的 `action_trace'` 与 `memory_trace` 删掉对应 `last_action` 的那一项后满足 permutation constraint
  2. $\exist$ `mem_list`, `first_mem`, `last_mem`, s.t. `initial_pc(0) * initial_state(0) -> list (pc * state * action) -> pc(m) * state(m)` $\in ( [\![c_0]\!] (0) \cup [\![c_1]\!] (1) \cup \ldots \cup [\![c_{n-1}]\!] (n-1) )^\Omega$ （归纳假设）
  3. $\exist$ `mem_list`, `first_mem`, `last_mem`, `j`, s.t. `initial_pc(0) * initial_state(0) -> list (pc * state * action) -> pc(m) * state(m)` $\in ( [\![c_0]\!] (0) \cup [\![c_1]\!] (1) \cup \ldots \cup [\![c_{n-1}]\!] (n-1) )^j$
     1. 根据 `last_action` 和 `last_mem` 可以构造 state(m') 中的 memory，记为 `new_last_memory` ，因此可以构造出 state(m') 使得 `pc(m) * state(m) -> [pc(m) * state(m) * last_action] -> pc(m') * state(m')` $\in [\![c_m]\!] (m)$
     2. `pc(m) * state(m) -> [pc(m) * state(m) * last_action] -> pc(m') * state(m')` $\in ( [\![c_0]\!] (0) \cup [\![c_1]\!] (1) \cup \ldots \cup [\![c_{n-1}]\!] (n-1) )^\Omega$
  4. $\exist$ `mem_list`, `first_mem`, `last_mem`, `new_last_memory`, `j`, s.t. `initial_pc(0) * initial_state -> list (pc * state * action) -> pc(m) * state(m)` $\circ$ `pc(m) * state(m) -> [pc(m) * state(m) * action] -> pc(m') * state(m')` $\in ( [\![c_0]\!] (0) \cup [\![c_1]\!] (1) \cup \ldots \cup [\![c_{n-1}]\!] (n-1) )^j  \circ ( [\![c_0]\!] (0) \cup [\![c_1]\!] (1) \cup \ldots \cup [\![c_{n-1}]\!] (n-1) )$
  5. $\exist$ `mem_list`, `first_mem`, `last_mem`, `new_last_memory`, `j`, s.t. `initial_pc(0) * initial_state -> list (pc * state * action) -> pc(m) * state(m)` $\circ$ `pc(m) * state(m) -> [pc(m) * state(m) * action] -> pc(m') * state(m')` $\in ( [\![c_0]\!] (0) \cup [\![c_1]\!] (1) \cup \ldots \cup [\![c_{n-1}]\!] (n-1) )^{j+1}$
  6. $\exist$ `mem_list`, `first_mem`, `last_mem`, `new_last_memory`, `j`, s.t. `initial_pc(0) * initial_state -> list (pc * state * action) ++ [pc(m) * state(m) * action] -> pc(m') * state(m')` $\in ( [\![c_0]\!] (0) \cup [\![c_1]\!] (1) \cup \ldots \cup [\![c_{n-1}]\!] (n-1) )^{j+1}$
  7. $\exist$ `mem_list`, `first_mem`, `last_mem`, `new_last_memory`, `j`, s.t. `initial_pc(0) * initial_state -> list (pc * state * action) ++ [pc(m) * state(m) * action] -> pc(m') * state(m')` $\in ( [\![c_0]\!] (0) \cup [\![c_1]\!] (1) \cup \ldots \cup [\![c_{n-1}]\!] (n-1) )^\Omega$
