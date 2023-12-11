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

Local Open Scope string.
Local Open Scope sets.
Local Open Scope list.

Module Definition_and_soundness.

(* Define int256 *)
Module Wordsize_256.
  Definition wordsize := 256%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize. congruence. Qed.
End Wordsize_256.


Strategy opaque [Wordsize_256.wordsize].
Module Int256 := Make(Wordsize_256).
Strategy 0 [Wordsize_256.wordsize].
Notation int256 := Int256.int.

(* Define syntax *)
Module Lang.
(*instructure 指令*)
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

Import Lang.

Module program_state.
(* state is a record of memory, mem_size and stack *)
Record program_state: Type := {
  memory: int256 -> int256;
  stack: list int256;
}.
End program_state.

Import program_state.
Notation "s '.(memory)'" := (memory s) (at level 1).
Notation "s '.(stack)'" := (stack s) (at level 1).
Ltac any_stack x := exact (program_state.stack x).
Notation "x '.(stack)'" := (ltac:(any_stack x)) (at level 1, only parsing).

Module CPU_state.
Record CPU_state: Type := {
  pc: nat;
  stack: list int256;
  inst: ins;
}.
End CPU_state.

Import CPU_state.
Notation "s '.(pc)'" := (CPU_state.pc s) (at level 1, only printing).
Ltac any_pc x := exact (CPU_state.pc x).
Notation "x '.(pc)'" := (ltac:(any_pc x)) (at level 1, only parsing).

Notation "s '.(stack)'" := (CPU_state.stack s) (at level 1, only printing).
Ltac any_stack x ::=
  match type of x with
  | program_state => exact (program_state.stack x)
  | CPU_state => exact (CPU_state.stack x)
  end.
Notation "x '.(stack)'" := (ltac:(any_stack x)) (at level 1, only parsing).
Notation "s '.(inst)'" := (CPU_state.inst s) (at level 1, only printing).


(* 加一下参数 *)
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

Notation "a '.(timestamp)'" := (timestamp a) (at level 1).
Notation "a '.(mem_ins)'" := (mem_ins a) (at level 1).

Module pc_state.

Record pc_state: Type := {
  pc: nat;
  state: program_state;
}.
Print program_state.

End pc_state.

Import pc_state.

Notation "s '.(pc)'" := (pc_state.pc s) (at level 1).
Notation "s '.(state)'" := (pc_state.state s) (at level 1).

Ltac any_pc x ::=
  match type of x with
  | CPU_state => exact (CPU_state.pc x)
  | pc_state => exact (pc_state.pc x)
  end.
Ltac any_state x := exact (pc_state.state x).

Notation "x '.(pc)'" := (ltac:(any_pc x)) (at level 1, only parsing).
Notation "x '.(state)'" := (ltac:(any_state x)) (at level 1, only parsing).

Module act_state.

(* act_state is the type of the elements of the list of memory actions 
内存操作的列表 的 元素 的类型*)
Record act_state: Type := {
  pc: nat;
  state: program_state;
  action: action_type;
}.

End act_state.

Import act_state.

Notation "s '.(pc)'" := (act_state.pc s) (at level 1, only printing).
Notation "s '.(state)'" := (act_state.state s) (at level 1, only printing).
Notation "s '.(action)'" := (act_state.action s) (at level 1).

Ltac any_pc x ::=
  match type of x with
  | CPU_state => exact (CPU_state.pc x)
  | pc_state => exact (pc_state.pc x)
  | act_state => exact (act_state.pc x)
  end.
Ltac any_state x ::=
  match type of x with
  | pc_state => exact (pc_state.state x)
  | act_state => exact (act_state.state x)
  end.

(*指令语意*)
Definition ins_sem_triple: Type := 
  pc_state -> list act_state -> pc_state -> Prop.

(* 用 Inductive 定义 Permutation 的类似办法定义单个和多个程序语句的语义 *)
Inductive POP_sem: nat -> pc_state -> list act_state -> pc_state -> Prop :=
| pop_sem:
    forall (pc: nat)(y: act_state)(x z: pc_state)(v: int256),
      x.(state) = y.(state) -> y.(action).(mem_ins) = non ->
      x.(pc) = pc -> y.(pc) = pc -> z.(pc) = pc + 1 ->
      x.(state).(stack) = cons v z.(state).(stack) ->
      y.(state).(memory) = z.(state).(memory) ->
      POP_sem pc x (cons y nil) z.

Print Datatypes.cons.

(* ADD

     input          output 
     ----------     ----------
     | a | b |   -> | a + b |
     ----------     ----------
*)

Inductive ADD_sem: nat -> pc_state -> list act_state -> pc_state -> Prop :=
| add_sem:
    forall (pc: nat)(y: act_state)(x z: pc_state)(v1 v2: int256)(l: list int256),
      x.(state) = y.(state) -> y.(action).(mem_ins) = non ->
      x.(pc) = pc -> y.(pc) = pc -> z.(pc) = pc + 1 ->
      (* integer result of the addition modulo 2^256 *)
      x.(state).(stack) = cons v1 (cons v2 l) ->
      z.(state).(stack) = cons (Int256.add v1 v2) l ->
      y.(state).(memory) = z.(state).(memory) ->
      ADD_sem pc x (cons y nil) z.

(* SUB

     input          output 
     ----------     ----------
     | a | b |   -> | a - b |
     ----------     ----------
*)

Inductive SUB_sem: nat -> pc_state -> list act_state -> pc_state -> Prop :=
| sub_sem:
    forall (pc: nat)(y: act_state)(x z: pc_state)(v1 v2: int256)(l: list int256),
    x.(state) = y.(state) -> y.(action).(mem_ins) = non ->
    x.(pc) = pc -> y.(pc) = pc -> z.(pc) = pc + 1 ->
    (* integer result of the addition modulo 2^256 *)
    x.(state).(stack) = cons v1 (cons v2 l) ->
    z.(state).(stack) = cons (Int256.sub v1 v2) l ->
    y.(state).(memory) = z.(state).(memory) ->
    SUB_sem pc x (cons y nil) z.

(* MUL

     input          output 
     ----------     ----------
     | a | b |   -> | a * b |
     ----------     ----------
*)

Inductive MUL_sem: nat -> pc_state -> list act_state -> pc_state -> Prop :=
| mul_sem:
    forall (pc: nat)(y: act_state)(x z: pc_state)(v1 v2: int256)(l: list int256),
    x.(state) = y.(state) -> y.(action).(mem_ins) = non ->
    x.(pc) = pc -> y.(pc) = pc -> z.(pc) = pc + 1 ->
    (* integer result of the addition modulo 2^256 *)
    x.(state).(stack) = cons v1 (cons v2 l) ->
    z.(state).(stack) = cons (Int256.mul v1 v2) l ->
    y.(state).(memory) = z.(state).(memory) ->
    MUL_sem pc x (cons y nil) z.

(* JUMP

     input                output 
     ----------------
     | destination |   -> $pc = destination
     ----------------
*)

Inductive JUMP_sem: nat -> pc_state -> list act_state -> pc_state -> Prop :=
| jump_sem:
    forall (pc: nat)(y: act_state)(x z: pc_state)(v: int256),
      x.(state) = y.(state) -> y.(action).(mem_ins) = non ->
      x.(pc) = pc -> y.(pc) = pc ->
      x.(state).(stack) = cons v z.(state).(stack) ->
      z.(pc) = Z.to_nat (Int256.unsigned v) ->
      y.(state).(memory) = z.(state).(memory) ->
      JUMP_sem pc x (cons y nil) z.

(* JUMPI (In that case, 0 means condition false, not 0 means condition true)

     input                            output 
     ----------------------------
     | destination | condition |   -> $pc = cond ? destination : $pc + 1
     ----------------------------
*)

Inductive JUMPI_sem: nat -> pc_state -> list act_state -> pc_state -> Prop :=
| jumpi_sem:
    forall (pc: nat)(y: act_state)(x z: pc_state)(dest cond: int256),
      x.(state) = y.(state) -> y.(action).(mem_ins) = non ->
      x.(pc) = pc -> y.(pc) = pc ->
      x.(state).(stack) = cons dest (cons cond z.(state).(stack)) ->
      (cond = Int256.repr 0 -> z.(pc) = pc + 1) (* no jump *) ->
      (cond <> Int256.repr 0 ->
      z.(pc) = Z.to_nat (Int256.unsigned dest)) (* jump *) ->
      y.(state).(memory) = z.(state).(memory) ->
      JUMPI_sem pc x (cons y nil) z.

(* PUSH

     input               output 
     ----                -----------
     |                   | int256 |
     ----                -----------
*)

Inductive PUSH32_sem (v: int256): nat -> pc_state -> list act_state -> pc_state -> Prop :=
| push32_sem:
    forall (pc: nat)(y: act_state)(x z: pc_state),
      x.(state) = y.(state) -> y.(action).(mem_ins) = non ->
      x.(pc) = pc -> y.(pc) = pc -> z.(pc) = pc + 1 ->
      (* stack size limit: 1024 *)
      z.(state).(stack) = cons v x.(state).(stack) ->
      length z.(state).(stack) <= 1024 ->
      y.(state).(memory) = z.(state).(memory) ->
      PUSH32_sem v pc x (cons y nil) z.

(* 	MLOAD (	memory[offset:offset+32] = value, uint256 )

     input                  output 
     -----------            ----------
     | offset |             | value |
     -----------            ----------
*)

Inductive MLOAD_sem : nat -> pc_state -> list act_state -> pc_state -> Prop :=
| mload_sem:
    forall (pc: nat)(y: act_state)(x z: pc_state)(offset: int256)(l: list int256),
      x.(state) = y.(state) ->
      x.(pc) = pc -> y.(pc) = pc -> z.(pc) = pc + 1 ->
      x.(state).(stack) = cons offset l ->
      z.(state).(stack) = cons (x.(state).(memory) offset) l ->
      y.(state).(memory) = z.(state).(memory) ->
      y.(action).(mem_ins) = read offset (x.(state).(memory) offset) ->
      MLOAD_sem pc x (cons y nil) z.

(* 		MSTORE (	memory[offset:offset+32] = value )

     input                          output 
     -------------------            ----------
     | offset | value |             |
     -------------------            ----------

*)

Definition update_memory (memory: int256->int256) (offset: int256) (value: int256): int256->int256 :=
  fun (address: int256) =>
  if Int256.eq address offset then value
  else memory address.

Inductive MSTORE_sem : nat -> pc_state -> list act_state -> pc_state -> Prop :=
| mstore_sem:
    forall (pc: nat)(y: act_state)(x z: pc_state)(offset v: int256)(l: list int256),
      x.(state) = y.(state) ->  
      x.(pc) = pc -> y.(pc) = pc -> z.(pc) = pc + 1 ->
      x.(state).(stack) = cons v (cons offset z.(state).(stack)) ->
      (* update memory check*)
      z.(state).(memory) = update_memory x.(state).(memory) offset v ->
      y.(action).(mem_ins) = write offset v ->
      MSTORE_sem pc x (cons y nil) z.

(* ==================================================================================== *)

Definition eval_ins (ins_pc:ins * nat): pc_state -> list act_state -> pc_state -> Prop :=
  match ins_pc with
  | (JUMP, index) => JUMP_sem index
  | (MUL, index) => MUL_sem index
  | (SUB, index) => SUB_sem index
  | (ADD, index) => ADD_sem index
  | (POP, index) => POP_sem index
  | (JUMPI, index) => JUMPI_sem index
  | (MLOAD, index) => MLOAD_sem index
  | (MSTORE, index) => MSTORE_sem index
  | (PUSH32 v, index) => PUSH32_sem v index
  end.

Print seq.
Definition fold_ins_sem (l: list (ins * nat)): pc_state -> list act_state -> pc_state -> Prop :=
  fold_right
  Sets.union ∅ (map eval_ins l).

(* [[c_0]] (0) U [[c_1]] (1) U ... U [[c_{n-1}]] (n-1) *)
Inductive eval_ins_list_single: list ins -> pc_state -> list act_state -> pc_state -> Prop :=
| one: forall (l: list ins)(y: list act_state)(x z: pc_state),
  fold_ins_sem (combine l (seq 0 (length l))) x y z ->
  eval_ins_list_single l x y z.

(* 加上对初始 pc_state 和 action list 全部 timestamp 的限制才能完成对语句列表的定义 *)
Inductive Increasing_timestamp: list act_state -> Prop :=
| ActionListNil : Increasing_timestamp nil
| ActionListSingle : forall x : act_state,
    x.(action).(timestamp) = 1 -> Increasing_timestamp (cons x nil)
| ActionListCons : forall (x y : act_state) (l : list act_state),
    y.(action).(timestamp) = x.(action).(timestamp) + 1 ->
    Increasing_timestamp (app l (cons x nil)) -> Increasing_timestamp (app (app l (cons x nil)) (cons y nil)).


Inductive eval_ins_list: list ins -> pc_state -> list act_state -> pc_state -> Prop :=
| sigma: forall (l: list ins)(x z: pc_state)(y: list act_state),
  x.(pc) = 0 ->
  x.(state).(memory) = (fun (n: int256) => Int256.zero) ->
  x.(state).(stack) = nil ->
  Increasing_timestamp y ->
  clos_refl_trans (eval_ins_list_single l) x y z ->
  eval_ins_list l x y z.

Print clos_refl_trans.

Inductive POP_constraint: CPU_state -> CPU_state -> Prop :=
| pop_constraint:
    forall (x y: CPU_state)(v: int256),
      y.(pc) = x.(pc) + 1 ->
      x.(stack) = cons v y.(stack) ->
      POP_constraint x y.

Inductive JUMP_constraint: CPU_state -> CPU_state -> Prop :=
| jump_constraint:
    forall (x y: CPU_state)(v: int256),
      y.(pc) = Z.to_nat (Int256.unsigned v) ->
      x.(stack) = cons v y.(stack) ->
      JUMP_constraint x y.

Inductive MUL_constraint: CPU_state -> CPU_state -> Prop :=
| mul_constraint:
    forall (x y: CPU_state)(v1 v2: int256)(l: list int256),
      y.(pc) = x.(pc) + 1 ->
      x.(stack) = cons v1 (cons v2 l) ->
      y.(stack) = cons (Int256.mul v1 v2) l ->
      MUL_constraint x y.

Inductive SUB_constraint: CPU_state -> CPU_state -> Prop :=
| sub_constraint:
    forall (x y: CPU_state)(v1 v2: int256)(l: list int256),
      y.(pc) = x.(pc) + 1 ->
      x.(stack) = cons v1 (cons v2 l) ->
      y.(stack) = cons (Int256.sub v1 v2) l ->
      SUB_constraint x y.

Inductive ADD_constraint: CPU_state -> CPU_state -> Prop :=
| add_constraint:
    forall (x y: CPU_state)(v1 v2: int256)(l: list int256),
      y.(pc) = x.(pc) + 1 ->
      x.(stack) = cons v1 (cons v2 l) ->
      y.(stack) = cons (Int256.add v1 v2) l ->
      ADD_constraint x y.

Inductive JUMPI_constraint: CPU_state -> CPU_state -> Prop :=
| jumpi_constraint:
    forall (x y: CPU_state)(dest cond: int256),
      y.(pc) = x.(pc) + 1 ->
      x.(stack) = cons dest (cons cond y.(stack)) ->
      (cond = Int256.zero -> y.(pc) = x.(pc) + 1) ->
      (cond <> Int256.zero -> y.(pc) = Z.to_nat (Int256.unsigned dest)) ->
      JUMPI_constraint x y.

Inductive MLOAD_constraint: CPU_state -> CPU_state -> Prop :=
| mload_constraint:
    forall (x y: CPU_state)(offset value: int256),
      y.(pc) = x.(pc) + 1 ->
      cons value x.(stack) = cons offset y.(stack) ->
      MLOAD_constraint x y.

Inductive MSTORE_constraint: CPU_state -> CPU_state -> Prop :=
| mstore_constraint:
    forall (x y: CPU_state)(offset value: int256),
      y.(pc) = x.(pc) + 1 ->
      x.(stack) = cons value (cons offset y.(stack)) ->
      MSTORE_constraint x y.

Inductive PUSH32_constraint: int256 -> CPU_state -> CPU_state -> Prop :=
| push32_constraint:
    forall (v: int256) (x y: CPU_state),
      y.(pc) = x.(pc) + 1 ->
      y.(stack) = cons v x.(stack) ->
      length y.(stack) <= 1024 ->
      PUSH32_constraint v x y.

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

Inductive multiset_constraint: list CPU_state -> list ins -> Prop :=
| trace_multiset: forall (program: list ins)(CPU_trace: list CPU_state),
  Forall (fun x => In x (combine program (seq 0 (length program)))) 
  (map (fun cpu_state => (cpu_state.(inst), cpu_state.(pc))) CPU_trace) ->
  multiset_constraint CPU_trace program
.

Definition mem_ins_type_is_not_non (action : action_type) : bool :=
  match action.(mem_ins) with
  | non => false
  | _ => true
  end.

Inductive permutation_constraint: list action_type -> list action_type -> Prop :=
| permutation: forall (action_trace memory_trace: list action_type),
  Permutation (filter mem_ins_type_is_not_non action_trace) memory_trace ->
  permutation_constraint action_trace memory_trace.

Print filter.

Inductive adjacent_CPU_state_for_action_trace (P : CPU_state -> CPU_state -> action_type -> Prop) : list CPU_state -> list action_type -> Prop :=
| adjacent_CPU_state_for_action_trace_nil : forall(x: CPU_state), adjacent_CPU_state_for_action_trace P [x] nil
| adjacent_CPU_state_for_action_trace_cons : forall (x y : CPU_state)(action : action_type)(l : list CPU_state)(l_action: list action_type),
    P x y action -> adjacent_CPU_state_for_action_trace P (l ++ [x]) l_action ->
    adjacent_CPU_state_for_action_trace P ((l ++ [x]) ++ [y]) (l_action ++ [action]).

Inductive action_trace_timestamp_constraint: list action_type -> Prop :=
| ActionListTraceNil : action_trace_timestamp_constraint nil
| ActionListTraceSingle : forall x : action_type,
    x.(timestamp) = 1 -> action_trace_timestamp_constraint (cons x nil)
| ActionListTraceCons : forall (x y : action_type) (l : list action_type),
    y.(timestamp) = x.(timestamp) + 1 ->
    action_trace_timestamp_constraint (app l [x]) -> action_trace_timestamp_constraint (app (app l [x]) [y]).

(*flag*)
Inductive Check_action: CPU_state -> CPU_state -> action_type -> Prop :=
| check_read_action: forall (state next_state: CPU_state)(action: action_type)(address value: int256)(remaining_stack: list int256),
  state.(inst) = MLOAD -> action.(mem_ins) = read address value ->
  state.(stack) = cons address remaining_stack -> next_state.(stack) = cons value remaining_stack ->
  Check_action state next_state action
| check_write_action: forall (state next_state: CPU_state)(action: action_type)(address value: int256)(new_stack: list int256),
  state.(inst) = MSTORE -> action.(mem_ins) = write address value ->
  state.(stack) = cons value (cons address new_stack) ->
  Check_action state next_state action
| check_non_action: forall (state next_state: CPU_state)(action: action_type),
  state.(inst) <> MLOAD -> state.(inst) <> MSTORE -> action.(mem_ins) = non -> Check_action state next_state action.

Inductive action_trace_constraint: list CPU_state -> list action_type -> Prop :=
| trace_action: forall (CPU_trace: list CPU_state)(action_trace: list action_type),
  adjacent_CPU_state_for_action_trace Check_action CPU_trace action_trace ->
  action_trace_constraint CPU_trace action_trace
.

Inductive memory_constraint: list action_type -> Prop :=
| trace_momory_nil: memory_constraint nil
| trace_memory_single_write: forall (action: action_type)(address value: int256),
  action.(mem_ins) = write address value -> memory_constraint [action]
| trace_memory_single_read: forall (action: action_type)(address value: int256),
  action.(mem_ins) = read address value -> value = Int256.repr 0 -> memory_constraint [action]
| trace_memory_multiple_write_to_read: forall (action next_action: action_type)(memory_trace: list action_type)(address value next_address next_value: int256),
  memory_constraint (app memory_trace [action]) ->
  action.(mem_ins) = write address value ->
  next_action.(mem_ins) = read next_address next_value ->
  (((Int256.unsigned address = Int256.unsigned next_address)%Z /\ next_action.(timestamp) > action.(timestamp) /\ value = next_value)
  \/ ((Int256.unsigned address < Int256.unsigned next_address)%Z /\ next_value = Int256.repr 0)) ->
  memory_constraint (app memory_trace [action; next_action])
| trace_memory_multiple_read_to_read: forall (action next_action: action_type)(memory_trace: list action_type)(address value next_address next_value: int256),
  memory_constraint (app memory_trace [action]) ->
  action.(mem_ins) = read address value ->
  next_action.(mem_ins) = read next_address next_value ->
  (((Int256.unsigned address = Int256.unsigned next_address)%Z /\ next_action.(timestamp) > action.(timestamp) /\ value = next_value)
  \/ ((Int256.unsigned address < Int256.unsigned next_address)%Z /\ next_value = Int256.repr 0)) ->
  memory_constraint (app memory_trace [action; next_action])
| trace_memory_multiple_write_to_write: forall (action next_action: action_type)(memory_trace: list action_type)(address value next_address next_value: int256),
  memory_constraint (app memory_trace [action]) ->
  action.(mem_ins) = write address value ->
  next_action.(mem_ins) = write next_address next_value ->
  (Int256.unsigned address <= Int256.unsigned next_address)%Z ->
  ((Int256.unsigned address = Int256.unsigned next_address)%Z -> next_action.(timestamp) > action.(timestamp)) ->
  memory_constraint (app memory_trace [action; next_action])
| trace_memory_multiple_read_to_write: forall (action next_action: action_type)(memory_trace: list action_type)(address value next_address next_value: int256),
  memory_constraint (app memory_trace [action]) ->
  action.(mem_ins) = read address value ->
  next_action.(mem_ins) = write next_address next_value ->
  (Int256.unsigned address <= Int256.unsigned next_address)%Z ->
  ((Int256.unsigned address = Int256.unsigned next_address)%Z -> next_action.(timestamp) > action.(timestamp)) ->
  memory_constraint (app memory_trace [action; next_action])
.

(* This constraint does nothing, just ignore it *)
Inductive public_constraint: list ins -> list CPU_state -> list action_type -> list action_type -> Prop :=
| public: forall (program: list ins)(CPU_trace: list CPU_state)
  (action_trace: list action_type)(memory_trace: list action_type),
  public_constraint program CPU_trace action_trace memory_trace.


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

(* =============================================================================== *)

Definition Build_program_state (memory: int256 -> int256) (stack: list int256): program_state :=
  {| program_state.memory := memory; program_state.stack := stack |}.

Definition Build_pc_state (pc: nat) (state: program_state): pc_state :=
  {| pc_state.pc := pc; pc_state.state := state |}.

(* combine CPU_state and a memory to a pc_state *)
Definition combine_to_pc_state (cpu_state: CPU_state) (memory: int256 -> int256): pc_state :=
  Build_pc_state cpu_state.(pc) (Build_program_state memory cpu_state.(stack)).

Definition combine_to_act_state (cpu_state: CPU_state) (memory: int256 -> int256) (action: action_type): act_state :=
  {| act_state.pc := cpu_state.(pc); act_state.state := Build_program_state memory cpu_state.(stack); act_state.action := action |}.

(* combine list CPU_state, list (int256 -> int256), list action_type to list act_state *)
Definition combine_to_act_state_list (CPU_trace: list CPU_state) (memory_list: list (int256 -> int256)) (action_trace: list action_type): list act_state :=
  map (fun x => (combine_to_act_state (fst (fst x)) (snd (fst x)) (snd x))) (combine (combine CPU_trace memory_list) action_trace).

Lemma app_cat : forall [A : Type] (l l' : list A) (x y x' y' : A),
  l ++ [x; y] = l' ++ [x'; y'] -> l ++ [x] = l' ++ [x'].
Proof.
  intros.
  assert (l ++ [x; y] = l ++ [x] ++ [y]).
  {
    reflexivity.
  }
  assert (l' ++ [x'; y'] = l' ++ [x'] ++ [y']).
  {
    reflexivity.
  }
  revert H.
  rewrite H0, H1.
  intros.
  rewrite ! app_assoc in H.
  apply app_inj_tail in H.
  tauto.
Qed.

Lemma app_first_last_corr:
  forall [A : Type] (l l' : list A) (x y x' y' : A),
  [x] ++ l ++ [y] = [x'] ++ l' ++ [y'] -> x = x' /\ l = l' /\ y = y'.
Proof.
  intros.
  inversion H.
  split.
  - tauto.
  - split.
    + apply app_inj_tail in H2. tauto.
    + apply app_inj_tail in H2. tauto.
Qed.

Lemma CPU_state_extract:
  forall [A : Type] (x y x' y' : A)(l: list A),
  [x; y] = [x'] ++ l ++ [y'] -> x = x' /\ l = [] /\ y = y'.
Proof.
  intros.
  assert ([x; y] = [x] ++ [] ++ [y]). { reflexivity. }
  rewrite H0 in H.
  apply app_first_last_corr in H.
  destruct H. destruct H1.
  split.
  - tauto.
  - split.
    + rewrite H1. reflexivity.
    + tauto.
Qed.

Lemma len_succ: forall {T : Type} (l : list T) x, S x = length l -> exists a l', l = a :: l'.
Proof.
  intros.
  destruct l; simpl in H; [discriminate|].
  exists t, l.
  tauto.
Qed.

Lemma combine_app: forall {A B : Type} (l1 l2 : list A) (l1' l2' : list B),
  length l1 = length l1' ->
  length l2 = length l2' ->
  (combine (l1 ++ l2) (l1' ++ l2')) = (combine l1 l1') ++ (combine l2 l2').
Proof.
  intros.
  remember (length l1) as ll1.
  revert ll1 l1 l1' l2 l2' Heqll1 H H0.
  induction ll1; intros.
  - symmetry in H; apply length_zero_iff_nil in H; subst.
    symmetry in Heqll1; apply length_zero_iff_nil in Heqll1; subst.
    simpl.
    tauto.
  - pose proof H; pose proof Heqll1.
    apply len_succ in H; apply len_succ in Heqll1.
    destruct H as [ ? [?] ].
    destruct Heqll1 as [ ? [?] ].
    subst l1 l1'.
    simpl.
    simpl in H1, H2. injection H1. injection H2. intros.
    specialize (IHll1 x2 x0 l2 l2' H H3 H0).
    rewrite IHll1.
    tauto.
Qed.

(*如果两个list长度相同，那么b把他们combine起来之后长度和原来一样*)
Lemma len_combine: forall {A B : Type} (l1 : list A) (l1' : list B),
length l1 = length l1' -> length l1' = length (combine l1 l1').
Proof.
  intros.
  remember (length l1') as ll1'.
  revert H. revert ll1' l1 l1'  Heqll1'.
  induction ll1'; intros.
  - apply length_zero_iff_nil in H. subst.
    symmetry in Heqll1'. apply length_zero_iff_nil in Heqll1'; subst.
    tauto.
  - symmetry in H.
    pose proof Heqll1'. pose proof H.
    apply len_succ in Heqll1'. apply len_succ in H.
    destruct Heqll1' as [? [?]].
    destruct H as [? [?]].
    subst l1 l1'.
    simpl.
    injection H0. injection H1. intros.
    symmetry in H.
    specialize (IHll1' x2 x0 H2 H).
    rewrite IHll1'.
    tauto.
Qed.
(*rev_ind是list相关的定理*)
Print list.
Print eq_ind.
Print rev_ind.
(*rev_ind貌似是对某一个list分类归纳*)

(*list前面加内容则可以找到一个list后面加内容*)
Lemma cons_app_eq: forall {A : Type} (x : A) (l : list A), exists y l', x :: l = l' ++ [y].
Proof.
  intros.
  revert x.
  apply rev_ind with (l := l). intros.
  - exists x, []. reflexivity.
  - intros. exists x, (x0 :: l0). reflexivity.
Qed.

(*flag*)
(*rm_last_CUP_trace比l长1*)
Lemma action_CPU_trace_len_cons: forall (rm_last_CPU_trace: list CPU_state)(l: list action_type),
  action_trace_constraint rm_last_CPU_trace l -> length rm_last_CPU_trace = S (length l).
Proof.
  intros. revert H. revert rm_last_CPU_trace.
  apply rev_ind with (l := l).
  - intros.
    simpl.
    inversion H. subst.
    inversion H0.
    + tauto.
    + apply app_eq_nil in H1.
      inversion H1.
      Print Check_action.
      discriminate.
(*why*)
  - intros.
    destruct rm_last_CPU_trace as [|y l'] eqn:H1.
    + inversion H0.
      inversion H2.
      apply app_eq_nil in H5.
      inversion H5.
      discriminate.
    + assert (exists z l'', y :: l' = l'' ++ [z]).
      {
        apply cons_app_eq.
      }
      destruct H2. destruct H2.
      assert (length x1 = length l').
      {
        assert (length (y :: l') = length (x1 ++ [x0])).
        {
          rewrite H2.
          reflexivity.
        }
        rewrite app_length in H3.
        simpl in H3.
        rewrite Nat.add_1_r in H3.
        symmetry in H3.
        injection H3.
        tauto.
      }
      rewrite H2.
      rewrite app_length.
      simpl.
      rewrite Nat.add_1_r.
      rewrite H2 in H0.
      assert (action_trace_constraint x1 l0).
      {
        apply trace_action.
        inversion H0.
        inversion H4.
        - symmetry in H9.
          apply app_eq_nil in H9.
          destruct H9.
          discriminate.
        - apply app_inj_tail in H7.
          destruct H7.
          apply app_inj_tail in H8.
          destruct H8.
          rewrite H7 in H10. rewrite H8 in H10.
          apply H10.
      }
      apply H in H4.
      rewrite H4.
      rewrite app_length.
      simpl.
      rewrite Nat.add_1_r.
      tauto.
Qed.

Lemma length_one_iff_single: forall {A: Type}(l : list A), length l = 1 <-> exists x, l = [x].
Proof.
  split.
  - destruct l.
    + discriminate.
    + simpl.
      intros.
      apply eq_add_S in H.
      apply length_zero_iff_nil in H.
      rewrite H.
      exists a. tauto.
  - intros.
    inversion H.
    assert (length l = length [x]). { rewrite H0. reflexivity. }
    simpl in H1.
    apply H1.
Qed.

Inductive memory_trace_legal: list action_type -> list action_type -> Prop :=
| legal: forall (action_trace memory_trace: list action_type),
  permutation_constraint action_trace memory_trace -> memory_constraint memory_trace ->
  memory_trace_legal action_trace memory_trace.

Lemma filter_preserves_Forall : forall {A: Type} (l : list A) (P: A -> Prop) (f: A -> bool),
  Forall P l -> Forall P (filter f l).
Proof.
  intros A l P f H.
  induction l as [| x xs IH].
  - (* l 是空列表的情况 *)
    simpl. constructor.
  - (* l 不为空列表的情况 *)
    simpl. destruct (f x) eqn:Hfx.
    + (* f x 返回 true 的情况 *)
      inversion H; subst. constructor.
      * (* P x 成立 *)
        apply H2.
      * (* 对 xs 应用归纳假设 *)
        apply IH. apply H3.
    + (* f x 返回 false 的情况 *)
      inversion H; subst.
      (* 对 xs 应用归纳假设 *)
      apply IH. apply H3.
Qed.

Lemma memory_constraint_keep: forall (l: list action_type)(x: action_type),
  memory_constraint (l ++ [x]) -> memory_constraint l.
Proof.
  intros.
  destruct l.
  - constructor.
  - pose proof (cons_app_eq a l).
    destruct H0 as [y [l' H0]].
    rewrite H0.
    rewrite H0 in H.
    inversion H.
    + symmetry in H2.
      apply app_eq_nil in H2.
      destruct H2.
      discriminate.
    + symmetry in H1.
      apply app_eq_unit in H1.
      destruct H1.
      * destruct H1.
        apply app_eq_nil in H1.
        destruct H1.
        discriminate.
      * destruct H1.
        discriminate.
    + symmetry in H1.
      apply app_eq_unit in H1.
      destruct H1.
      * destruct H1.
        apply app_eq_nil in H1.
        destruct H1.
        discriminate.
      * destruct H1.
        discriminate.
    + assert (memory_trace ++ [action0; next_action] = (memory_trace ++ [action0]) ++ [next_action]).
      {
        rewrite <- app_assoc.
        simpl.
        reflexivity.
      }
      rewrite H6 in H1.
      apply app_inj_tail in H1.
      destruct H1.
      rewrite H1 in H2.
      tauto.
    + assert (memory_trace ++ [action0; next_action] = (memory_trace ++ [action0]) ++ [next_action]).
      {
        rewrite <- app_assoc.
        simpl.
        reflexivity.
      }
      rewrite H6 in H1.
      apply app_inj_tail in H1.
      destruct H1.
      rewrite H1 in H2.
      tauto.
    + assert (memory_trace ++ [action0; next_action] = (memory_trace ++ [action0]) ++ [next_action]).
      {
        rewrite <- app_assoc.
        simpl.
        reflexivity.
      }
      rewrite H7 in H1.
      apply app_inj_tail in H1.
      destruct H1.
      rewrite H1 in H2.
      tauto.
    + assert (memory_trace ++ [action0; next_action] = (memory_trace ++ [action0]) ++ [next_action]).
      {
        rewrite <- app_assoc.
        simpl.
        reflexivity.
      }
      rewrite H7 in H1.
      apply app_inj_tail in H1.
      destruct H1.
      rewrite H1 in H2.
      tauto.
Qed.

Lemma memory_constraint_keep_without_list: forall (l l': list action_type),
  memory_constraint (l ++ l') -> memory_constraint l.
Proof.
  intros.
  revert l H.
  apply rev_ind with (l := l').
  - intros.
    rewrite app_nil_r in H.
    tauto.
  - intros.
    assert (memory_constraint (l0 ++ l)).
    {
      rewrite app_assoc in H0.
      apply (memory_constraint_keep (l0 ++ l) x H0).
    }
    apply (H l0 H1).
Qed.

Lemma memory_trace_is_read_or_write: forall (l l': list action_type)(x: action_type),
  l = l' ++ [x] ->
  memory_constraint (l' ++ [x]) ->
  exists address value,
  x.(mem_ins) = read address value \/ x.(mem_ins) = write address value.
Proof.
  intros.
  remember (length l) as ll.
  revert Heqll H H0. revert x l' l.
  induction ll.
  - intros.
    symmetry in Heqll.
    rewrite length_zero_iff_nil in Heqll.
    rewrite Heqll in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H.
    discriminate.
  - intros.
    destruct l'.
    + rewrite app_nil_l in H0.
      inversion H0.
      * exists address, value.
        apply or_intror.
        apply H2.
      * exists address, value.
        apply or_introl.
        apply H2.
      * apply app_eq_unit in H1.
        destruct H1; destruct H1; discriminate.
      * apply app_eq_unit in H1.
        destruct H1; destruct H1; discriminate.
      * apply app_eq_unit in H1.
        destruct H1; destruct H1; discriminate.
      * apply app_eq_unit in H1.
        destruct H1; destruct H1; discriminate.
    + pose proof (cons_app_eq a l').
      destruct H1; destruct H1.
      rewrite H1 in H.
      rewrite H in Heqll.
      rewrite app_length in Heqll.
      simpl in Heqll.
      assert (ll = Datatypes.length (x1 ++ [x0])). { lia. }
      rewrite H1 in H0.
      inversion H0.
      * symmetry in H4.
        apply app_eq_nil in H4.
        destruct H4; discriminate.
      * symmetry in H3.
        apply app_eq_unit in H3.
        destruct H3; destruct H3.
        apply app_eq_nil in H3.
        destruct H3; discriminate.
        discriminate.
      * symmetry in H3.
        apply app_eq_unit in H3.
        destruct H3; destruct H3.
        apply app_eq_nil in H3.
        destruct H3; discriminate.
        discriminate.
      * assert (memory_trace ++
        [action0; next_action] = (memory_trace ++
        [action0]) ++ [next_action]).
        {
          rewrite <- app_assoc.
          tauto.
        }
        rewrite H8 in H3.
        apply app_inj_tail in H3.
        destruct H3.
        rewrite H9 in H6.
        exists next_address, next_value.
        apply or_introl.
        tauto.
      * assert (memory_trace ++
        [action0; next_action] = (memory_trace ++
        [action0]) ++ [next_action]).
        {
          rewrite <- app_assoc.
          tauto.
        }
        rewrite H8 in H3.
        apply app_inj_tail in H3.
        destruct H3.
        rewrite H9 in H6.
        exists next_address, next_value.
        apply or_introl.
        tauto.
      * assert (memory_trace ++
        [action0; next_action] = (memory_trace ++
        [action0]) ++ [next_action]).
        {
          rewrite <- app_assoc.
          tauto.
        }
        rewrite H9 in H3.
        apply app_inj_tail in H3.
        destruct H3.
        rewrite H10 in H6.
        exists next_address, next_value.
        apply or_intror.
        tauto.
      * assert (memory_trace ++
        [action0; next_action] = (memory_trace ++
        [action0]) ++ [next_action]).
        {
          rewrite <- app_assoc.
          tauto.
        }
        rewrite H9 in H3.
        apply app_inj_tail in H3.
        destruct H3.
        rewrite H10 in H6.
        exists next_address, next_value.
        apply or_intror.
        tauto.
Qed.

Lemma memory_trace_is_read_or_write_in: forall (l: list action_type)(x: action_type),
  In x l ->
  memory_constraint l ->
  exists address value,
  x.(mem_ins) = read address value \/ x.(mem_ins) = write address value.
Proof.
  intros.
  revert H H0.
  apply rev_ind with (l := l).
  - simpl.
    intros.
    contradiction.
  - intros.
    apply in_app_or in H0.
    destruct H0.
    + specialize (memory_constraint_keep l0 x0 H1).
      intro.
      apply (H H0 H2).
    + simpl in H0; destruct H0; try tauto.
      rewrite H0 in H1.
      pose proof (memory_trace_is_read_or_write (l0 ++ [x]) l0 x).
      destruct H2; try tauto.
      destruct H2 as [value H2].
      exists x1, value.
      tauto.
Qed.

Lemma list_element_2_vs_1: forall (l l': list action_type)(x y z: action_type),
  l ++ x :: y :: l' <> [z].
Proof.
  intros.
  unfold not.
  intro.
  pose proof (cons_app_eq y (l')).
  destruct H0 as [y0 [l0 H0]].
  rewrite H0 in H.
  pose proof (cons_app_eq x l0).
  destruct H1 as [y0' [l0' H1]].
  rewrite app_comm_cons in H.
  rewrite H1 in H.
  apply app_eq_unit in H.
  destruct H.
  - destruct H.
    apply app_eq_unit in H2.
    destruct H2.
    + destruct H2.
      apply app_eq_nil in H2.
      destruct H2.
      discriminate.
    + destruct H2.
      discriminate.
  - destruct H.
    apply app_eq_nil in H2.
    destruct H2.
    discriminate.
Qed.

Lemma two_ele_app: forall {A: Type} (x y: A),
  [x; y] = [x] ++ [y].
Proof.
  simpl; tauto.
Qed.

Lemma memory_trace_read_value_eq: forall (l l': list action_type)(x y: action_type)(address value_x value_y: int256),
  memory_constraint (l ++ [x] ++ [y] ++ l') ->
  ((x.(mem_ins) = read address value_x /\ y.(mem_ins) = read address value_y) \/
  (x.(mem_ins) = write address value_x /\ y.(mem_ins) = read address value_y)) ->
  (Int256.unsigned value_x = Int256.unsigned value_y)%Z.
Proof.
  intros.
  rewrite ! app_assoc in H.
  rewrite <- (app_assoc l [x] [y]) in H.
  pose proof (memory_constraint_keep_without_list (l ++ [x] ++ [y]) l' H).
  inversion H1.
  + symmetry in H3.
    apply app_eq_nil in H3.
    destruct H3.
    discriminate.
  + symmetry in H2.
    rewrite (two_ele_app x y) in H2.
    apply app_eq_unit in H2.
    destruct H2; destruct H2; discriminate.
  + symmetry in H2.
    rewrite (two_ele_app x y) in H2.
    apply app_eq_unit in H2.
    destruct H2; destruct H2; discriminate.
  + rewrite (two_ele_app x y) in H2.
    rewrite (two_ele_app action0 next_action) in H2.
    rewrite ! app_assoc in H2.
    apply app_inj_tail in H2.
    destruct H2.
    apply app_inj_tail in H2.
    destruct H2.
    rewrite H8 in H4.
    rewrite H7 in H5.
    destruct H0.
    - destruct H0.
      congruence.
    - destruct H0.
      rewrite H0 in H4.
      rewrite H9 in H5.
      inversion H4.
      inversion H5.
      destruct H6.
      * destruct H6.
        destruct H10.
        f_equal.
        tauto.
      * destruct H6.
        rewrite <- H11 in H6.
        rewrite <- H13 in H6.
        lia.
  + rewrite (two_ele_app x y) in H2.
    rewrite (two_ele_app action0 next_action) in H2.
    rewrite ! app_assoc in H2.
    apply app_inj_tail in H2.
    destruct H2.
    apply app_inj_tail in H2.
    destruct H2.
    rewrite H8 in H4.
    rewrite H7 in H5.
    destruct H0.
    - destruct H0.
      rewrite H0 in H4.
      rewrite H9 in H5.
      inversion H4.
      inversion H5.
      destruct H6.
      * destruct H6.
        destruct H10.
        f_equal.
        tauto.
      * destruct H6.
        rewrite <- H11 in H6.
        rewrite <- H13 in H6.
        lia.
    - destruct H0.
      congruence.
  + rewrite (two_ele_app x y) in H2.
    rewrite (two_ele_app action0 next_action) in H2.
    rewrite ! app_assoc in H2.
    apply app_inj_tail in H2.
    destruct H2.
    apply app_inj_tail in H2.
    destruct H2.
    rewrite H9 in H4.
    rewrite H8 in H5.
    destruct H0; destruct H0; congruence.
  + rewrite (two_ele_app x y) in H2.
    rewrite (two_ele_app action0 next_action) in H2.
    rewrite ! app_assoc in H2.
    apply app_inj_tail in H2.
    destruct H2.
    apply app_inj_tail in H2.
    destruct H2.
    rewrite H9 in H4.
    rewrite H8 in H5.
    destruct H0; destruct H0; congruence.
Qed.

Lemma memory_trace_address_less_than: forall (l: list action_type)(x y: action_type)(address_x value_x address_y value_y: int256),
  memory_constraint ((l ++ [x]) ++ [y]) ->
  ((x.(mem_ins) = read address_x value_x /\ y.(mem_ins) = read address_y value_y) \/
  (x.(mem_ins) = read address_x value_x /\ y.(mem_ins) = write address_y value_y) \/
  (x.(mem_ins) = write address_x value_x /\ y.(mem_ins) = read address_y value_y) \/
  (x.(mem_ins) = write address_x value_x /\ y.(mem_ins) = write address_y value_y)) ->
  (Int256.unsigned address_x <= Int256.unsigned address_y)%Z.
Proof.
  intros.
  inversion H.
  - symmetry in H2.
    apply app_eq_nil in H2.
    destruct H2; discriminate.
  - symmetry in H1.
    apply app_eq_unit in H1.
    destruct H1; destruct H1.
    + apply app_eq_nil in H1.
      destruct H1.
      discriminate.
    + discriminate.
  - symmetry in H1.
    apply app_eq_unit in H1.
    destruct H1; destruct H1.
    + apply app_eq_nil in H1.
      destruct H1.
      discriminate.
    + discriminate.
  - assert (memory_trace ++
    [action0; next_action] = (memory_trace ++
    [action0]) ++ [next_action]).
    {
      rewrite <- app_assoc.
      tauto.
    }
    rewrite H6 in H1.
    apply app_inj_tail in H1.
    destruct H1.
    apply app_inj_tail in H1.
    destruct H1.
    subst.
    rewrite H3 in H0.
    rewrite H4 in H0.
    destruct H0.
    + destruct H0; discriminate.
    + destruct H0.
      { destruct H0; discriminate. }
      destruct H0.
      {
        destruct H0.
        inversion H0.
        inversion H1.
        rewrite <- H8.
        rewrite <- H10.
        lia.
      }
      { destruct H0; discriminate. }
  - assert (memory_trace ++
    [action0; next_action] = (memory_trace ++
    [action0]) ++ [next_action]).
    {
      rewrite <- app_assoc.
      tauto.
    }
    rewrite H6 in H1.
    apply app_inj_tail in H1.
    destruct H1.
    apply app_inj_tail in H1.
    destruct H1.
    subst.
    rewrite H3 in H0.
    rewrite H4 in H0.
    destruct H0.
    + destruct H0.
      {
        inversion H0.
        inversion H1.
        rewrite <- H8.
        rewrite <- H10.
        lia.
      }
    + destruct H0.
      { destruct H0; discriminate. }
      destruct H0; destruct H0; discriminate.
  - assert (memory_trace ++
    [action0; next_action] = (memory_trace ++
    [action0]) ++ [next_action]).
    {
      rewrite <- app_assoc.
      tauto.
    }
    rewrite H7 in H1.
    apply app_inj_tail in H1.
    destruct H1.
    apply app_inj_tail in H1.
    destruct H1.
    subst.
    rewrite H3 in H0.
    rewrite H4 in H0.
    destruct H0.
    + destruct H0; discriminate.
    + destruct H0.
      { destruct H0; discriminate. }
      destruct H0.
      { destruct H0; discriminate. }
      {
        destruct H0.
        inversion H0.
        inversion H1.
        rewrite <- H9.
        rewrite <- H11.
        lia.
      }
  - assert (memory_trace ++
    [action0; next_action] = (memory_trace ++
    [action0]) ++ [next_action]).
    {
      rewrite <- app_assoc.
      tauto.
    }
    rewrite H7 in H1.
    apply app_inj_tail in H1.
    destruct H1.
    apply app_inj_tail in H1.
    destruct H1.
    subst.
    rewrite H3 in H0.
    rewrite H4 in H0.
    destruct H0.
    + destruct H0; discriminate.
    + destruct H0.
      {
        destruct H0.
        inversion H0.
        inversion H1.
        rewrite <- H9.
        rewrite <- H11.
        lia.
      }
      destruct H0; destruct H0; discriminate.
Qed.

Lemma memory_trace_address_less_than_next: forall (l l': list action_type)(x y: action_type)(address_x value_x address_y value_y: int256),
  memory_constraint (l ++ [x] ++ [y] ++ l') ->
  ((x.(mem_ins) = read address_x value_x /\ y.(mem_ins) = read address_y value_y) \/
  (x.(mem_ins) = read address_x value_x /\ y.(mem_ins) = write address_y value_y) \/
  (x.(mem_ins) = write address_x value_x /\ y.(mem_ins) = read address_y value_y) \/
  (x.(mem_ins) = write address_x value_x /\ y.(mem_ins) = write address_y value_y)) ->
  (Int256.unsigned address_x <= Int256.unsigned address_y)%Z.
Proof.
  intros l l'.
  revert l.
  apply rev_ind with (l := l').
  - intros.
    rewrite app_nil_r in H.
    rewrite app_assoc in H.
    apply (memory_trace_address_less_than l x y address_x value_x address_y value_y H H0).
  - intros.
    rewrite ! app_assoc in H0.
    rewrite <- (app_assoc (l0 ++ [x0]) [y] l) in H0.
    rewrite <- (app_assoc l0 [x0] ([y] ++ l)) in H0.
    pose proof (memory_constraint_keep (l0 ++ [x0] ++ [y] ++ l) x H0).
    apply (H l0 x0 y address_x value_x address_y value_y H2 H1).
Qed.

Lemma memory_trace_address_less_than_forall: forall (l l' l0: list action_type)(x y: action_type)(address_x value_x address_y value_y: int256),
  memory_constraint (l ++ [x] ++ l0 ++ [y] ++ l') ->
  ((x.(mem_ins) = read address_x value_x /\ y.(mem_ins) = read address_y value_y) \/
  (x.(mem_ins) = read address_x value_x /\ y.(mem_ins) = write address_y value_y) \/
  (x.(mem_ins) = write address_x value_x /\ y.(mem_ins) = read address_y value_y) \/
  (x.(mem_ins) = write address_x value_x /\ y.(mem_ins) = write address_y value_y)) ->
  (Int256.unsigned address_x <= Int256.unsigned address_y)%Z.
Proof.
  intros l l' l0.
  revert l l'.
  apply rev_ind with (l := l0).
  - intros.
    rewrite app_nil_l in H.
    apply (memory_trace_address_less_than_next l l' x y address_x value_x address_y value_y H H0).
  - intros.
    rewrite <- app_assoc in H0.
    assert (exists address value : int256,
    x.(mem_ins) = read address value \/ x.(mem_ins) = write address value).
    {
      assert (In x (l1 ++
      [x0] ++ l ++ [x] ++ [y] ++ l')).
      {
        apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
        simpl; tauto.
      }
      apply (memory_trace_is_read_or_write_in (l1 ++
      [x0] ++ l ++ [x] ++ [y] ++ l') x H2 H0).
    }
    destruct H2 as [address [value H2]].
    assert (x0.(mem_ins) =
    read address_x value_x /\
    x.(mem_ins) =
    read address value \/
    x0.(mem_ins) =
    read address_x value_x /\
    x.(mem_ins) =
    write address value \/
    x0.(mem_ins) =
    write address_x value_x /\
    x.(mem_ins) =
    read address value \/
    x0.(mem_ins) =
    write address_x value_x /\
    x.(mem_ins) =
    write address value). { tauto. }
    pose proof (H l1 ([y] ++ l') x0 x address_x value_x address value H0 H3).
    clear H3.
    assert (l1 ++
    [x0] ++ l ++ [x] ++ [y] ++ l' = (l1 ++
    [x0] ++ l) ++ [x] ++ [y] ++ l').
    {
      rewrite ! app_assoc.
      tauto.
    }
    rewrite H3 in H0; clear H3.
    assert (x.(mem_ins) = read address value /\ y.(mem_ins) = read address_y value_y \/
    x.(mem_ins) = read address value /\ y.(mem_ins) = write address_y value_y \/
    x.(mem_ins) = write address value /\ y.(mem_ins) = read address_y value_y \/
    x.(mem_ins) = write address value /\
    y.(mem_ins) = write address_y value_y). { tauto. }
    pose proof (memory_trace_address_less_than_next (l1 ++ [x0] ++ l) l' x y address value address_y value_y H0 H3).
    lia.
Qed.

Lemma memory_trace_address_less_than_in: forall (l l': list action_type)(x y: action_type)(address_x value_x address_y value_y: int256),
  In x l ->
  memory_constraint (l ++ [y] ++ l') ->
  ((x.(mem_ins) = read address_x value_x /\ y.(mem_ins) = read address_y value_y) \/
  (x.(mem_ins) = read address_x value_x /\ y.(mem_ins) = write address_y value_y) \/
  (x.(mem_ins) = write address_x value_x /\ y.(mem_ins) = read address_y value_y) \/
  (x.(mem_ins) = write address_x value_x /\ y.(mem_ins) = write address_y value_y)) ->
  (Int256.unsigned address_x <= Int256.unsigned address_y)%Z.
Proof.
  intros.
  apply in_split in H.
  destruct H as [l1 [l2 H]].
  assert (l1 ++ x :: l2 = l1 ++ [x] ++ l2). { simpl; tauto. }
  rewrite H2 in H; clear H2.
  rewrite H in H0.
  rewrite ! app_assoc in H0.
  rewrite <- ! app_assoc in H0.
  apply (memory_trace_address_less_than_forall l1 l' l2 x y address_x value_x address_y value_y H0 H1).
Qed.

Lemma memory_trace_address_less_than_in_behind: forall (l l': list action_type)(x y: action_type)(address_x value_x address_y value_y: int256),
  In y l' ->
  memory_constraint (l ++ [x] ++ l') ->
  ((x.(mem_ins) = read address_x value_x /\ y.(mem_ins) = read address_y value_y) \/
  (x.(mem_ins) = read address_x value_x /\ y.(mem_ins) = write address_y value_y) \/
  (x.(mem_ins) = write address_x value_x /\ y.(mem_ins) = read address_y value_y) \/
  (x.(mem_ins) = write address_x value_x /\ y.(mem_ins) = write address_y value_y)) ->
  (Int256.unsigned address_x <= Int256.unsigned address_y)%Z.
Proof.
  intros.
  apply in_split in H.
  destruct H as [l1 [l2 H]].
  assert (l1 ++ y :: l2 = l1 ++ [y] ++ l2). { simpl; tauto. }
  rewrite H2 in H; clear H2.
  rewrite H in H0.
  rewrite ! app_assoc in H0.
  rewrite <- ! app_assoc in H0.
  apply (memory_trace_address_less_than_forall l l2 l1 x y address_x value_x address_y value_y H0 H1).
Qed.

Lemma memory_trace_timestamp_less_than_next: forall (l l': list action_type)(x y: action_type)(address value_x value_y: int256),
  memory_constraint (l ++ [x] ++ [y] ++ l') ->
  ((x.(mem_ins) = read address value_x /\ y.(mem_ins) = read address value_y) \/
  (x.(mem_ins) = read address value_x /\ y.(mem_ins) = write address value_y) \/
  (x.(mem_ins) = write address value_x /\ y.(mem_ins) = read address value_y) \/
  (x.(mem_ins) = write address value_x /\ y.(mem_ins) = write address value_y)) ->
  x.(timestamp) < y.(timestamp).
Proof.
  intros.
  assert (l ++ [x] ++ [y] ++ l' = (l ++ [x] ++ [y]) ++ l').
  {
    rewrite ! app_assoc.
    rewrite <- ! app_assoc.
    reflexivity.
  }
  rewrite H1 in H; clear H1.
  pose proof (memory_constraint_keep_without_list (l ++ [x] ++ [y]) l' H).
  inversion H1.
  - symmetry in H3.
    apply app_eq_nil in H3.
    destruct H3; discriminate.
  - symmetry in H2.
    apply app_eq_unit in H2.
    destruct H2; destruct H2; discriminate.
  - symmetry in H2.
    apply app_eq_unit in H2.
    destruct H2; destruct H2; discriminate.
  - rewrite (two_ele_app x y) in H2.
    rewrite (two_ele_app action0 next_action) in H2.
    rewrite ! app_assoc in H2.
    apply app_inj_tail in H2.
    destruct H2.
    apply app_inj_tail in H2.
    destruct H2.
    subst.
    destruct H6.
    + destruct H2.
      destruct H6.
      lia.
    + destruct H2.
      destruct H0.
      * destruct H0.
        congruence.
      * destruct H0; try destruct H0; try congruence.
        {
          destruct H0.
          rewrite H0 in H4.
          rewrite H7 in H5.
          inversion H4.
          inversion H5.
          rewrite <- H9 in H2.
          rewrite <- H11 in H2.
          lia.
        }
        {
          destruct H0; try congruence.
        }
  - rewrite (two_ele_app x y) in H2.
    rewrite (two_ele_app action0 next_action) in H2.
    rewrite ! app_assoc in H2.
    apply app_inj_tail in H2.
    destruct H2.
    apply app_inj_tail in H2.
    destruct H2.
    subst.
    destruct H6.
    + destruct H2.
      destruct H6.
      lia.
    + destruct H2.
      destruct H0.
      * destruct H0.
        rewrite H0 in H4.
        rewrite H7 in H5.
        inversion H4.
        inversion H5.
        rewrite <- H9 in H2.
        rewrite <- H11 in H2.
        lia.
      * destruct H0; try destruct H0; try destruct H0; try congruence.
    - rewrite (two_ele_app x y) in H2.
      rewrite (two_ele_app action0 next_action) in H2.
      rewrite ! app_assoc in H2.
      apply app_inj_tail in H2.
      destruct H2.
      apply app_inj_tail in H2.
      destruct H2.
      subst.
      destruct H0.
      * destruct H0; try congruence.
      * destruct H0; destruct H0; try congruence.
        {
          destruct H0.
          rewrite H2 in H5.
          rewrite H0 in H4.
          congruence.
        }
        {
          destruct H0.
          rewrite H2 in H5.
          rewrite H0 in H4.
          inversion H4.
          inversion H5.
          rewrite <- H9, H11 in H7.
          lia.
        }
    - rewrite (two_ele_app x y) in H2.
      rewrite (two_ele_app action0 next_action) in H2.
      rewrite ! app_assoc in H2.
      apply app_inj_tail in H2.
      destruct H2.
      apply app_inj_tail in H2.
      destruct H2.
      subst.
      destruct H0.
      * destruct H0; try congruence.
      * destruct H0; destruct H0; try congruence.
        {
          rewrite H2 in H5.
          rewrite H0 in H4.
          inversion H4.
          inversion H5.
          rewrite <- H9, H11 in H7.
          lia.
        }
        {
          destruct H0.
          rewrite H2 in H5.
          rewrite H0 in H4.
          congruence.
        }
        destruct H0; try congruence.
Qed.

Lemma memory_trace_timestamp_less_than: forall (l l' l0: list action_type)(x y: action_type)(address value_x value_y: int256),
  memory_constraint (l ++ [x] ++ l0 ++ [y] ++ l') ->
  ((x.(mem_ins) = read address value_x /\ y.(mem_ins) = read address value_y) \/
  (x.(mem_ins) = read address value_x /\ y.(mem_ins) = write address value_y) \/
  (x.(mem_ins) = write address value_x /\ y.(mem_ins) = read address value_y) \/
  (x.(mem_ins) = write address value_x /\ y.(mem_ins) = write address value_y)) ->
  x.(timestamp) < y.(timestamp).
Proof.
  intros l l' l0.
  revert l l'.
  apply rev_ind with (l := l0).
  - intros.
    rewrite app_nil_l in H.
    apply (memory_trace_timestamp_less_than_next l l' x y address value_x value_y H H0).
  - intros.
    assert (l1 ++
    [x0] ++
    (l ++ [x]) ++ [y] ++ l' = l1 ++
    [x0] ++
    l ++ [x] ++ ([y] ++ l')).
    {
      rewrite ! app_assoc; tauto.
    }
    rewrite H2 in H0; clear H2.
    assert (In x (l1 ++
    [x0] ++ l ++ [x] ++ [y] ++ l')).
    {
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
      simpl; tauto.
    }
    pose proof (memory_trace_is_read_or_write_in (l1 ++
    [x0] ++ l ++ [x] ++ [y] ++ l') x H2 H0).
    destruct H3 as [address' [value' H3]].
    assert (x0.(mem_ins) =
    read address value_x /\
    x.(mem_ins) =
    read address' value' \/
    x0.(mem_ins) =
    read address value_x /\
    x.(mem_ins) =
    write address' value' \/
    x0.(mem_ins) =
    write address value_x /\
    x.(mem_ins) =
    read address' value' \/
    x0.(mem_ins) =
    write address value_x /\
    x.(mem_ins) =
    write address' value'). { tauto. }
    pose proof (memory_trace_address_less_than_forall l1 ([y] ++ l') l x0 x address value_x address' value' H0 H4).
    clear H4.
    assert ( x.(mem_ins) =
    read address' value' /\
    y.(mem_ins) =
    read address value_y \/
    x.(mem_ins) =
    read address' value' /\
    y.(mem_ins) =
    write address value_y \/
    x.(mem_ins) =
    write address' value' /\
    y.(mem_ins) =
    read address value_y \/
    x.(mem_ins) =
    write address' value' /\
    y.(mem_ins) =
    write address value_y). { tauto. }
    assert ((l1 ++
    [x0] ++ l ++ [x] ++ [y] ++ l') = ((l1 ++
    [x0] ++ l) ++ [x] ++ [y] ++ l')).
    {
      rewrite ! app_assoc; tauto.
    }
    rewrite H6 in H0; clear H6.
    pose proof (memory_trace_address_less_than_next (l1 ++ [x0] ++ l) l' x y address' value' address value_y H0 H4).
    assert (address = address').
    {
      rewrite <- (Int256.repr_unsigned address).
      rewrite <- (Int256.repr_unsigned address').
      f_equal.
      lia.
    }
    rewrite <- H7 in H3.
    assert (((l1 ++ [x0] ++ l) ++
    [x] ++ [y] ++ l') = (l1 ++ [x0] ++ l ++
    [x] ++ ([y] ++ l'))).
    {
      rewrite ! app_assoc; tauto.
    }
    rewrite H8 in H0.
    assert (x0.(mem_ins) =
    read address value_x /\
    x.(mem_ins) =
    read address value' \/
    x0.(mem_ins) =
    read address value_x /\
    x.(mem_ins) =
    write address value' \/
    x0.(mem_ins) =
    write address value_x /\
    x.(mem_ins) =
    read address value' \/
    x0.(mem_ins) =
    write address value_x /\
    x.(mem_ins) =
    write address value'). { tauto. }
    pose proof (H l1 ([y] ++ l') x0 x address value_x value' H0 H9).
    assert ((l1 ++
    [x0] ++ l ++ [x] ++ [y] ++ l') = ((l1 ++
    [x0] ++ l) ++ [x] ++ [y] ++ l')).
    {
      rewrite ! app_assoc; tauto.
    }
    rewrite H11 in H0.
    assert (x.(mem_ins) =
    read address value' /\
    y.(mem_ins) =
    read address value_y \/
    x.(mem_ins) =
    read address value' /\
    y.(mem_ins) =
    write address value_y \/
    x.(mem_ins) =
    write address value' /\
    y.(mem_ins) =
    read address value_y \/
    x.(mem_ins) =
    write address value' /\
    y.(mem_ins) =
    write address value_y). { tauto. }
    pose proof (memory_trace_timestamp_less_than_next (l1 ++ [x0] ++ l) l' x y address value' value_y H0 H12).
    lia.
Qed.

Lemma memory_trace_timestamp_less_than_in_front: forall (l l': list action_type)(x y: action_type)(address value_x value_y: int256),
  memory_constraint (l ++ [x] ++ l') ->
  In y l ->
  ((x.(mem_ins) = read address value_x /\ y.(mem_ins) = read address value_y) \/
  (x.(mem_ins) = read address value_x /\ y.(mem_ins) = write address value_y) \/
  (x.(mem_ins) = write address value_x /\ y.(mem_ins) = read address value_y) \/
  (x.(mem_ins) = write address value_x /\ y.(mem_ins) = write address value_y)) ->
  y.(timestamp) < x.(timestamp).
Proof.
  intros.
  apply in_split in H0.
  destruct H0 as [l1 [l2 H0]].
  assert (l1 ++ y :: l2 = l1 ++ [y] ++ l2). { simpl; tauto. }
  rewrite H2 in H0; clear H2.
  rewrite H0 in H.
  rewrite ! app_assoc in H.
  rewrite <- ! app_assoc in H.
  assert (y.(mem_ins) =
  read address value_y /\
  x.(mem_ins) =
  read address value_x \/
  y.(mem_ins) =
  read address value_y /\
  x.(mem_ins) =
  write address value_x \/
  y.(mem_ins) =
  write address value_y /\
  x.(mem_ins) =
  read address value_x \/
  y.(mem_ins) =
  write address value_y /\
  x.(mem_ins) =
  write address value_x). { tauto. }
  apply (memory_trace_timestamp_less_than l1 l' l2 y x address value_y value_x H H2).
Qed.

Lemma memory_trace_timestamp_less_than_in_behind: forall (l l': list action_type)(x y: action_type)(address value_x value_y: int256),
  memory_constraint (l ++ [x] ++ l') ->
  In y l' ->
  ((x.(mem_ins) = read address value_x /\ y.(mem_ins) = read address value_y) \/
  (x.(mem_ins) = read address value_x /\ y.(mem_ins) = write address value_y) \/
  (x.(mem_ins) = write address value_x /\ y.(mem_ins) = read address value_y) \/
  (x.(mem_ins) = write address value_x /\ y.(mem_ins) = write address value_y)) ->
  x.(timestamp) < y.(timestamp).
Proof.
    intros.
    apply in_split in H0.
    destruct H0 as [l1 [l2 H0]].
    assert (l1 ++ y :: l2 = l1 ++ [y] ++ l2). { simpl; tauto. }
    rewrite H2 in H0; clear H2.
    rewrite H0 in H.
    rewrite ! app_assoc in H.
    rewrite <- ! app_assoc in H.
    apply (memory_trace_timestamp_less_than l l2 l1 x y address value_x value_y H H1).
Qed.

Lemma memory_trace_fisrt_read_value_zero: forall (l: list action_type)(x: action_type)(address value: int256),
  memory_constraint (x :: l) ->
  x.(mem_ins) = read address value ->
  value = Int256.repr 0.
Proof.
  intros.
  assert (x :: l = [x] ++ l). { simpl; tauto. }
  rewrite H1 in H; clear H1.
  pose proof (memory_constraint_keep_without_list [x] l H).
  inversion H1.
  - congruence.
  - rewrite H0 in H3.
    inversion H3.
    tauto.
  - apply app_eq_unit in H2.
    destruct H2; try destruct H2; try discriminate.
  - apply app_eq_unit in H2.
    destruct H2; try destruct H2; try discriminate.
  - apply app_eq_unit in H2.
    destruct H2; try destruct H2; try discriminate.
  - apply app_eq_unit in H2.
    destruct H2; try destruct H2; try discriminate.
Qed.

Lemma memory_trace_fisrt_address_value_zero: forall (l l': list action_type)(x: action_type)(address value: int256),
  (forall (action : action_type) (address0 value0 : int256),
  In action l ->
  action.(mem_ins) = read address0 value0 \/ action.(mem_ins) = write address0 value0 -> address <> address0) ->
  memory_constraint (l ++ [x] ++ l') ->
  x.(mem_ins) = read address value ->
  value = Int256.repr 0.
Proof.
  intro.
  destruct l.
  - intros.
    rewrite app_nil_l in H0.
    simpl in H0.
    apply (memory_trace_fisrt_read_value_zero l' x address value H0).
    tauto.
  - intros.
    pose proof (cons_app_eq a l).
    destruct H2 as [y [l0 H2]].
    rewrite H2 in H0, H.
    clear H2.
    assert (((l0 ++ [y]) ++
    [x] ++ l') = ((l0 ++ [y] ++
    [x]) ++ l')).
    {
      rewrite ! app_assoc; tauto.
    }
    rewrite H2 in H0.
    pose proof (memory_constraint_keep_without_list (l0 ++ [y] ++ [x]) l' H0).
    inversion H3.
    + symmetry in H5.
      rewrite (two_ele_app y x) in H5.
      apply app_eq_nil in H5.
      destruct H5.
      discriminate.
    + symmetry in H4.
      rewrite (two_ele_app y x) in H4.
      apply app_eq_unit in H4.
      destruct H4; destruct H4; discriminate.
    + symmetry in H4.
      rewrite (two_ele_app y x) in H4.
      apply app_eq_unit in H4.
      destruct H4; destruct H4; discriminate.
    + rewrite (two_ele_app y x) in H4.
      rewrite (two_ele_app action0 next_action) in H4.
      rewrite ! app_assoc in H4.
      apply app_inj_tail in H4.
      destruct H4.
      apply app_inj_tail in H4.
      destruct H4.
      rewrite H9 in H7.
      rewrite H1 in H7.
      inversion H7.
      destruct H8.
      * destruct H8; destruct H11.
        subst.
        assert (In y (l0 ++ [y])).
        {
          apply in_or_app.
          right.
          simpl; tauto.
        }
        assert (y.(mem_ins) =
        read address0 next_value \/
        y.(mem_ins) =
        write address0 next_value). { tauto. }
        pose proof (H y address0
        next_value H4 H9).
        assert (address0 = next_address).
        {
          rewrite <- (Int256.repr_unsigned address0).
          rewrite <- (Int256.repr_unsigned next_address).
          f_equal.
          tauto.
        }
        congruence.
      * destruct H8.
        tauto.
    + rewrite (two_ele_app y x) in H4.
      rewrite (two_ele_app action0 next_action) in H4.
      rewrite ! app_assoc in H4.
      apply app_inj_tail in H4.
      destruct H4.
      apply app_inj_tail in H4.
      destruct H4.
      rewrite H9 in H7.
      rewrite H1 in H7.
      inversion H7.
      destruct H8.
      * destruct H8; destruct H11.
        subst.
        assert (In y (l0 ++ [y])).
        {
          apply in_or_app.
          right.
          simpl; tauto.
        }
        assert (y.(mem_ins) =
        read address0 next_value \/
        y.(mem_ins) =
        write address0 next_value). { tauto. }
        pose proof (H y address0
        next_value H4 H9).
        assert (address0 = next_address).
        {
          rewrite <- (Int256.repr_unsigned address0).
          rewrite <- (Int256.repr_unsigned next_address).
          f_equal.
          tauto.
        }
        congruence.
      * destruct H8.
        tauto.
    + rewrite (two_ele_app y x) in H4.
      rewrite (two_ele_app action0 next_action) in H4.
      rewrite ! app_assoc in H4.
      apply app_inj_tail in H4.
      destruct H4.
      apply app_inj_tail in H4.
      destruct H4.
      rewrite H10 in H7.
      congruence.
    + rewrite (two_ele_app y x) in H4.
      rewrite (two_ele_app action0 next_action) in H4.
      rewrite ! app_assoc in H4.
      apply app_inj_tail in H4.
      destruct H4.
      apply app_inj_tail in H4.
      destruct H4.
      rewrite H10 in H7.
      congruence.
Qed.

Lemma exists_memory_trace': forall (l memory_trace: list action_type)(x: action_type),
  permutation_constraint (l ++ [x]) memory_trace ->
  memory_constraint memory_trace ->
  Forall (fun a => a.(timestamp) < x.(timestamp)) l ->
  exists memory_trace', memory_trace_legal l memory_trace' /\
  (x.(mem_ins) <> non /\ (exists l1' l2', (memory_trace' = l1' ++ l2' /\ memory_trace = l1' ++ [x] ++ l2')) \/
  (x.(mem_ins) = non /\ memory_trace = memory_trace'))
  .
Proof.
  intros.
  destruct x.(mem_ins) eqn:Heq.
  - inversion H. subst.
    assert (filter mem_ins_type_is_not_non (l ++ [x]) = (filter mem_ins_type_is_not_non l) ++ [x]).
    {
      rewrite filter_app.
      simpl.
      unfold mem_ins_type_is_not_non.
      rewrite Heq.
      tauto.
    }
    rewrite H3 in H2.
    pose proof (Permutation_cons_append (filter mem_ins_type_is_not_non l) x).
    apply (Permutation_trans H4) in H2.
    pose proof H2.
    apply Permutation_sym in H2.
    apply Permutation_vs_cons_inv in H2.
    destruct H2 as [l1 H2].
    destruct H2 as [l2 H2].
    rewrite H2 in H5.
    apply Permutation_cons_app_inv in H5.
    exists (l1 ++ l2).
    split.
    {
      constructor.
      + constructor. apply H5.
      + apply (filter_preserves_Forall l (fun a : action_type =>
        a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H1.
        apply (Permutation_Forall H5) in H1.
        rewrite H2 in H0.
        revert H0 H1.
        apply rev_ind with (l := l2).
        {
          intros.
          destruct l1.
          + constructor.
          + pose proof (cons_app_eq a l1).
            destruct H6 as [action H6].
            destruct H6 as [l' H6].
            rewrite H6 in H0.
            rewrite H6.
            rewrite app_nil_r.
            inversion H0.
            - symmetry in H8.
              apply app_eq_nil in H8.
              destruct H8.
              discriminate.
            - symmetry in H7.
              apply app_eq_unit in H7.
              destruct H7.
              * destruct H7.
                apply app_eq_nil in H7.
                destruct H7.
                discriminate.
              * destruct H7.
                discriminate.
            - symmetry in H7.
              apply app_eq_unit in H7.
              destruct H7.
              * destruct H7.
                apply app_eq_nil in H7.
                destruct H7.
                discriminate.
              * destruct H7.
                discriminate.
            - assert (memory_trace0 ++
              [action0; next_action] = (memory_trace0 ++
              [action0]) ++ [next_action]).
              {
                rewrite <- app_assoc.
                tauto.
              }
              rewrite H12 in H7.
              apply app_inj_tail in H7.
              destruct H7.
              rewrite H7 in H8.
              apply H8.
            - assert (memory_trace0 ++
              [action0; next_action] = (memory_trace0 ++
              [action0]) ++ [next_action]).
              {
                rewrite <- app_assoc.
                tauto.
              }
              rewrite H12 in H7.
              apply app_inj_tail in H7.
              destruct H7.
              rewrite H7 in H8.
              apply H8.
            - assert (memory_trace0 ++
              [action0; next_action] = (memory_trace0 ++
              [action0]) ++ [next_action]).
              {
                rewrite <- app_assoc.
                tauto.
              }
              rewrite H13 in H7.
              apply app_inj_tail in H7.
              destruct H7.
              rewrite H7 in H8.
              apply H8.
            - assert (memory_trace0 ++
              [action0; next_action] = (memory_trace0 ++
              [action0]) ++ [next_action]).
              {
                rewrite <- app_assoc.
                tauto.
              }
              rewrite H13 in H7.
              apply app_inj_tail in H7.
              destruct H7.
              rewrite H7 in H8.
              apply H8. 
        }
        {
          intros.
          rewrite app_assoc in H6.
          apply Forall_app in H6.
          destruct H6.
          inversion H1.
          - symmetry in H9.
          apply app_eq_nil in H9.
          destruct H9.
          discriminate.
          - symmetry in H8.
            apply app_eq_unit in H8.
            destruct H8.
            * destruct H8.
              rewrite app_comm_cons in H10.
              apply app_eq_unit in H10.
              destruct H10; destruct H10; discriminate.
            * destruct H8.
              rewrite app_comm_cons in H10.
              apply app_eq_nil in H10.
              destruct H10; discriminate.
          - symmetry in H8.
            apply app_eq_unit in H8.
            destruct H8.
            * destruct H8.
              rewrite app_comm_cons in H11.
              apply app_eq_unit in H11.
              destruct H11; destruct H11; discriminate.
            * destruct H8.
              rewrite app_comm_cons in H11.
              apply app_eq_nil in H11.
              destruct H11; discriminate.
          - assert (memory_trace0 ++
            [action0; next_action] = (memory_trace0 ++
            [action0]) ++ [next_action]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H13 in H8.
            assert (l1 ++ x :: l0 ++ [x0] = (l1 ++ (x :: l0)) ++ [x0]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H14 in H8.
            apply app_inj_tail in H8.
            destruct H8.
            rewrite H8 in H9.
            apply (H0 H9) in H6.
            subst.
            destruct l0.
            * apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              inversion H12.
              + destruct H2.
                destruct H8.
                lia.
              + destruct l1.
                {
                  simpl.
                  destruct H2.
                  apply trace_memory_single_read in H11.
                  apply H11.
                  apply H8.
                }
                {
                  (* if l0 = nil, action0 = x, 
                  possible_address_above <= address0 < next_address,
                  next_value = Int256.repr 0, thus memory_constraint l1 ++ [x0]
                  o.w. l0 = l0' ++ [action0], action0 and x0 satisfy all these prop,
                  thus memory_constraint (l1 ++ l0 ++ [x0]) *)
                  pose proof (cons_app_eq a l1).
                  destruct H8.
                  destruct H8 as [l' H8].
                  rewrite H8 in H6.
                  rewrite app_nil_r in H6.
                  rewrite H8 in H9.
                  rewrite H8.
                  simpl.
                  assert (exists address1 value1, x1.(mem_ins) = read address1 value1 \/ x1.(mem_ins) = write address1 value1).
                  {
                    pose proof (memory_trace_is_read_or_write (l' ++ [x1]) l' x1).
                    destruct H15.
                    - tauto.
                    - tauto.
                    - destruct H15.
                      exists x2, x3.
                      tauto.
                  }
                  destruct x1.(mem_ins) eqn:Hx1.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H16 address1 value1 address0 value0).
                      specialize (H16 H9).
                      apply H16.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H16.
                    + destruct H2.
                      apply (trace_memory_multiple_read_to_read x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      apply or_intror.
                      split; tauto.
                    + tauto.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H16 address1 value1 address0 value0).
                      specialize (H16 H9).
                      apply H16.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H16.
                    + destruct H2.
                      apply (trace_memory_multiple_write_to_read x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      apply or_intror.
                      split; tauto.
                    + tauto.
                  - destruct H15.
                    destruct H15.
                    destruct H15; discriminate.
                }
            * pose proof (cons_app_eq a l0).
              destruct H2; destruct H2.
              rewrite H2 in H8.
              clear H14.
              assert (l1 ++ x :: x2 ++ [x1] = (l1 ++ x :: x2) ++ [x1]).
              {
                rewrite app_comm_cons.
                rewrite app_assoc.
                tauto. 
              }
              rewrite H14 in H8.
              apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              clear H13 H14.
              rewrite H2.
              rewrite H2 in H0.
              rewrite H2 in H1.
              rewrite H2 in H6.
              rewrite H2 in H9.
              rewrite <- app_assoc.
              simpl.
              rewrite app_assoc.
              apply (trace_memory_multiple_write_to_read x1 x0 (l1 ++ x2) address0 value0 next_address next_value).
              rewrite <- app_assoc.
              tauto. tauto. tauto. tauto.
          - assert (memory_trace0 ++
            [action0; next_action] = (memory_trace0 ++
            [action0]) ++ [next_action]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H13 in H8.
            assert (l1 ++ x :: l0 ++ [x0] = (l1 ++ (x :: l0)) ++ [x0]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H14 in H8.
            apply app_inj_tail in H8.
            destruct H8.
            rewrite H8 in H9.
            apply (H0 H9) in H6.
            subst.
            destruct l0.
            * apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              inversion H12.
              + destruct H2.
                destruct H8.
                lia.
              + destruct l1.
                {
                  simpl.
                  destruct H2.
                  apply trace_memory_single_read in H11.
                  apply H11.
                  apply H8.
                }
                {
                  (* if l0 = nil, action0 = x, 
                  possible_address_above <= address0 < next_address,
                  next_value = Int256.repr 0, thus memory_constraint l1 ++ [x0]
                  o.w. l0 = l0' ++ [action0], action0 and x0 satisfy all these prop,
                  thus memory_constraint (l1 ++ l0 ++ [x0]) *)
                  pose proof (cons_app_eq a l1).
                  destruct H8.
                  destruct H8 as [l' H8].
                  rewrite H8 in H6.
                  rewrite app_nil_r in H6.
                  rewrite H8 in H9.
                  rewrite H8.
                  simpl.
                  assert (exists address1 value1, x1.(mem_ins) = read address1 value1 \/ x1.(mem_ins) = write address1 value1).
                  {
                    pose proof (memory_trace_is_read_or_write (l' ++ [x1]) l' x1).
                    destruct H15.
                    - tauto.
                    - tauto.
                    - destruct H15.
                      exists x2, x3.
                      tauto.
                  }
                  destruct x1.(mem_ins) eqn:Hx1.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H16 address1 value1 address0 value0).
                      specialize (H16 H9).
                      apply H16.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H16.
                    + destruct H2.
                      apply (trace_memory_multiple_read_to_read x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      apply or_intror.
                      split; tauto.
                    + tauto.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H16 address1 value1 address0 value0).
                      specialize (H16 H9).
                      apply H16.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H16.
                    + destruct H2.
                      apply (trace_memory_multiple_write_to_read x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      apply or_intror.
                      split; tauto.
                    + tauto.
                  - destruct H15.
                    destruct H15.
                    destruct H15; discriminate.
                }
            * pose proof (cons_app_eq a l0).
              destruct H2; destruct H2.
              rewrite H2 in H8.
              clear H14.
              assert (l1 ++ x :: x2 ++ [x1] = (l1 ++ x :: x2) ++ [x1]).
              {
                rewrite app_comm_cons.
                rewrite app_assoc.
                tauto. 
              }
              rewrite H14 in H8.
              apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              clear H13 H14.
              rewrite H2.
              rewrite H2 in H0.
              rewrite H2 in H1.
              rewrite H2 in H6.
              rewrite H2 in H9.
              rewrite <- app_assoc.
              simpl.
              rewrite app_assoc.
              apply (trace_memory_multiple_read_to_read x1 x0 (l1 ++ x2) address0 value0 next_address next_value).
              rewrite <- app_assoc.
              tauto. tauto. tauto. tauto.
          - assert (memory_trace0 ++
            [action0; next_action] = (memory_trace0 ++
            [action0]) ++ [next_action]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H14 in H8.
            assert (l1 ++ x :: l0 ++ [x0] = (l1 ++ (x :: l0)) ++ [x0]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H15 in H8.
            apply app_inj_tail in H8.
            destruct H8.
            rewrite H8 in H9.
            apply (H0 H9) in H6.
            subst.
            destruct l0.
            * apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              apply Zle_lt_or_eq in H12.
              apply or_comm in H12.
              inversion H12.
              + apply H13 in H2.
                lia.
              + destruct l1.
                {
                  simpl.
                  apply (trace_memory_single_write x0 next_address next_value).
                  apply H11.
                }
                {
                  (* if l0 = nil, action0 = x, 
                  possible_address_above <= address0 < next_address,
                  next_value = Int256.repr 0, thus memory_constraint l1 ++ [x0]
                  o.w. l0 = l0' ++ [action0], action0 and x0 satisfy all these prop,
                  thus memory_constraint (l1 ++ l0 ++ [x0]) *)
                  pose proof (cons_app_eq a l1).
                  destruct H8.
                  destruct H8 as [l' H8].
                  rewrite H8 in H6.
                  rewrite app_nil_r in H6.
                  rewrite H8 in H9.
                  rewrite H8.
                  simpl.
                  assert (exists address1 value1, x1.(mem_ins) = read address1 value1 \/ x1.(mem_ins) = write address1 value1).
                  {
                    pose proof (memory_trace_is_read_or_write (l' ++ [x1]) l' x1).
                    destruct H16.
                    - tauto.
                    - tauto.
                    - destruct H16.
                      exists x2, x3.
                      tauto.
                  }
                  destruct x1.(mem_ins) eqn:Hx1.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H17 address1 value1 address0 value0).
                      specialize (H17 H9).
                      apply H17.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H17.
                    + destruct H2.
                      apply (trace_memory_multiple_read_to_write x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      lia.
                      lia.
                    + tauto.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H17 address1 value1 address0 value0).
                      specialize (H17 H9).
                      apply H17.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H17.
                    + destruct H2.
                      apply (trace_memory_multiple_write_to_write x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      lia.
                      lia.
                    + tauto.
                  - destruct H16.
                    destruct H16.
                    destruct H16; discriminate.
                }
            * pose proof (cons_app_eq a l0).
              destruct H2; destruct H2.
              rewrite H2 in H8.
              clear H14.
              assert (l1 ++ x :: x2 ++ [x1] = (l1 ++ x :: x2) ++ [x1]).
              {
                rewrite app_comm_cons.
                rewrite app_assoc.
                tauto. 
              }
              rewrite H14 in H8.
              apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              clear H13 H14.
              rewrite H2.
              rewrite H2 in H0.
              rewrite H2 in H1.
              rewrite H2 in H6.
              rewrite H2 in H9.
              rewrite <- app_assoc.
              simpl.
              rewrite app_assoc.
              apply (trace_memory_multiple_write_to_write x1 x0 (l1 ++ x2) address0 value0 next_address next_value).
              rewrite <- app_assoc.
              tauto. tauto. tauto. tauto.
              rewrite <- app_assoc in H1.
              simpl in H1.
              rewrite app_comm_cons in H1.
              rewrite app_assoc in H1.
              inversion H1.
              + symmetry in H13.
                apply app_eq_nil in H13.
                destruct H13.
                discriminate.
              + symmetry in H8.
                apply app_eq_unit in H8.
                destruct H8; destruct H8; discriminate.
              + symmetry in H8.
                apply app_eq_unit in H8.
                destruct H8; destruct H8; discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H18 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H16 in H11.
                discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H18 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H16 in H11.
                discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H19 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H14 in H10.
                inversion H10.
                rewrite H16 in H11.
                inversion H11.
                subst.
                tauto.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H19 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H14 in H10.
                discriminate.
          - assert (memory_trace0 ++
            [action0; next_action] = (memory_trace0 ++
            [action0]) ++ [next_action]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H14 in H8.
            assert (l1 ++ x :: l0 ++ [x0] = (l1 ++ (x :: l0)) ++ [x0]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H15 in H8.
            apply app_inj_tail in H8.
            destruct H8.
            rewrite H8 in H9.
            apply (H0 H9) in H6.
            subst.
            destruct l0.
            * apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              apply Zle_lt_or_eq in H12.
              apply or_comm in H12.
              inversion H12.
              + apply H13 in H2.
                lia.
              + destruct l1.
                {
                  simpl.
                  apply (trace_memory_single_write x0 next_address next_value).
                  apply H11.
                }
                {
                  (* if l0 = nil, action0 = x, 
                  possible_address_above <= address0 < next_address,
                  next_value = Int256.repr 0, thus memory_constraint l1 ++ [x0]
                  o.w. l0 = l0' ++ [action0], action0 and x0 satisfy all these prop,
                  thus memory_constraint (l1 ++ l0 ++ [x0]) *)
                  pose proof (cons_app_eq a l1).
                  destruct H8.
                  destruct H8 as [l' H8].
                  rewrite H8 in H6.
                  rewrite app_nil_r in H6.
                  rewrite H8 in H9.
                  rewrite H8.
                  simpl.
                  assert (exists address1 value1, x1.(mem_ins) = read address1 value1 \/ x1.(mem_ins) = write address1 value1).
                  {
                    pose proof (memory_trace_is_read_or_write (l' ++ [x1]) l' x1).
                    destruct H16.
                    - tauto.
                    - tauto.
                    - destruct H16.
                      exists x2, x3.
                      tauto.
                  }
                  destruct x1.(mem_ins) eqn:Hx1.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H17 address1 value1 address0 value0).
                      specialize (H17 H9).
                      apply H17.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H17.
                    + destruct H2.
                      apply (trace_memory_multiple_read_to_write x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      lia.
                      lia.
                    + tauto.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H17 address1 value1 address0 value0).
                      specialize (H17 H9).
                      apply H17.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H17.
                    + destruct H2.
                      apply (trace_memory_multiple_write_to_write x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      lia.
                      lia.
                    + tauto.
                  - destruct H16.
                    destruct H16.
                    destruct H16; discriminate.
                }
            * pose proof (cons_app_eq a l0).
              destruct H2; destruct H2.
              rewrite H2 in H8.
              clear H14.
              assert (l1 ++ x :: x2 ++ [x1] = (l1 ++ x :: x2) ++ [x1]).
              {
                rewrite app_comm_cons.
                rewrite app_assoc.
                tauto. 
              }
              rewrite H14 in H8.
              apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              clear H13 H14.
              rewrite H2.
              rewrite H2 in H0.
              rewrite H2 in H1.
              rewrite H2 in H6.
              rewrite H2 in H9.
              rewrite <- app_assoc.
              simpl.
              rewrite app_assoc.
              apply (trace_memory_multiple_read_to_write x1 x0 (l1 ++ x2) address0 value0 next_address next_value).
              rewrite <- app_assoc.
              tauto. tauto. tauto. tauto.
              rewrite <- app_assoc in H1.
              simpl in H1.
              rewrite app_comm_cons in H1.
              rewrite app_assoc in H1.
              inversion H1.
              + symmetry in H13.
                apply app_eq_nil in H13.
                destruct H13.
                discriminate.
              + symmetry in H8.
                apply app_eq_unit in H8.
                destruct H8; destruct H8; discriminate.
              + symmetry in H8.
                apply app_eq_unit in H8.
                destruct H8; destruct H8; discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H18 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H16 in H11.
                discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H18 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H16 in H11.
                discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H19 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H14 in H10.
                discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H19 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H14 in H10.
                inversion H10.
                rewrite H16 in H11.
                inversion H11.
                subst.
                tauto.
        }
    }
    left.
    split; try congruence.
    exists l1, l2.
    split; try tauto.
  - inversion H. subst.
    assert (filter mem_ins_type_is_not_non (l ++ [x]) = (filter mem_ins_type_is_not_non l) ++ [x]).
    {
      rewrite filter_app.
      simpl.
      unfold mem_ins_type_is_not_non.
      rewrite Heq.
      tauto.
    }
    rewrite H3 in H2.
    pose proof (Permutation_cons_append (filter mem_ins_type_is_not_non l) x).
    apply (Permutation_trans H4) in H2.
    pose proof H2.
    apply Permutation_sym in H2.
    apply Permutation_vs_cons_inv in H2.
    destruct H2 as [l1 H2].
    destruct H2 as [l2 H2].
    rewrite H2 in H5.
    apply Permutation_cons_app_inv in H5.
    exists (l1 ++ l2).
    split.
    {
      constructor.
      + constructor. apply H5.
      + apply (filter_preserves_Forall l (fun a : action_type =>
        a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H1.
        apply (Permutation_Forall H5) in H1.
        rewrite H2 in H0.
        revert H0 H1.
        apply rev_ind with (l := l2).
        {
          intros.
          destruct l1.
          + constructor.
          + pose proof (cons_app_eq a l1).
            destruct H6 as [action H6].
            destruct H6 as [l' H6].
            rewrite H6 in H0.
            rewrite H6.
            rewrite app_nil_r.
            inversion H0.
            - symmetry in H8.
              apply app_eq_nil in H8.
              destruct H8.
              discriminate.
            - symmetry in H7.
              apply app_eq_unit in H7.
              destruct H7.
              * destruct H7.
                apply app_eq_nil in H7.
                destruct H7.
                discriminate.
              * destruct H7.
                discriminate.
            - symmetry in H7.
              apply app_eq_unit in H7.
              destruct H7.
              * destruct H7.
                apply app_eq_nil in H7.
                destruct H7.
                discriminate.
              * destruct H7.
                discriminate.
            - assert (memory_trace0 ++
              [action0; next_action] = (memory_trace0 ++
              [action0]) ++ [next_action]).
              {
                rewrite <- app_assoc.
                tauto.
              }
              rewrite H12 in H7.
              apply app_inj_tail in H7.
              destruct H7.
              rewrite H7 in H8.
              apply H8.
            - assert (memory_trace0 ++
              [action0; next_action] = (memory_trace0 ++
              [action0]) ++ [next_action]).
              {
                rewrite <- app_assoc.
                tauto.
              }
              rewrite H12 in H7.
              apply app_inj_tail in H7.
              destruct H7.
              rewrite H7 in H8.
              apply H8.
            - assert (memory_trace0 ++
              [action0; next_action] = (memory_trace0 ++
              [action0]) ++ [next_action]).
              {
                rewrite <- app_assoc.
                tauto.
              }
              rewrite H13 in H7.
              apply app_inj_tail in H7.
              destruct H7.
              rewrite H7 in H8.
              apply H8.
            - assert (memory_trace0 ++
              [action0; next_action] = (memory_trace0 ++
              [action0]) ++ [next_action]).
              {
                rewrite <- app_assoc.
                tauto.
              }
              rewrite H13 in H7.
              apply app_inj_tail in H7.
              destruct H7.
              rewrite H7 in H8.
              apply H8. 
        }
        {
          intros.
          rewrite app_assoc in H6.
          apply Forall_app in H6.
          destruct H6.
          inversion H1.
          - symmetry in H9.
          apply app_eq_nil in H9.
          destruct H9.
          discriminate.
          - symmetry in H8.
            apply app_eq_unit in H8.
            destruct H8.
            * destruct H8.
              rewrite app_comm_cons in H10.
              apply app_eq_unit in H10.
              destruct H10; destruct H10; discriminate.
            * destruct H8.
              rewrite app_comm_cons in H10.
              apply app_eq_nil in H10.
              destruct H10; discriminate.
          - symmetry in H8.
            apply app_eq_unit in H8.
            destruct H8.
            * destruct H8.
              rewrite app_comm_cons in H11.
              apply app_eq_unit in H11.
              destruct H11; destruct H11; discriminate.
            * destruct H8.
              rewrite app_comm_cons in H11.
              apply app_eq_nil in H11.
              destruct H11; discriminate.
          - assert (memory_trace0 ++
            [action0; next_action] = (memory_trace0 ++
            [action0]) ++ [next_action]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H13 in H8.
            assert (l1 ++ x :: l0 ++ [x0] = (l1 ++ (x :: l0)) ++ [x0]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H14 in H8.
            apply app_inj_tail in H8.
            destruct H8.
            rewrite H8 in H9.
            apply (H0 H9) in H6.
            subst.
            destruct l0.
            * apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              inversion H12.
              + destruct H2.
                destruct H8.
                lia.
              + destruct l1.
                {
                  simpl.
                  destruct H2.
                  apply trace_memory_single_read in H11.
                  apply H11.
                  apply H8.
                }
                {
                  (* if l0 = nil, action0 = x, 
                  possible_address_above <= address0 < next_address,
                  next_value = Int256.repr 0, thus memory_constraint l1 ++ [x0]
                  o.w. l0 = l0' ++ [action0], action0 and x0 satisfy all these prop,
                  thus memory_constraint (l1 ++ l0 ++ [x0]) *)
                  pose proof (cons_app_eq a l1).
                  destruct H8.
                  destruct H8 as [l' H8].
                  rewrite H8 in H6.
                  rewrite app_nil_r in H6.
                  rewrite H8 in H9.
                  rewrite H8.
                  simpl.
                  assert (exists address1 value1, x1.(mem_ins) = read address1 value1 \/ x1.(mem_ins) = write address1 value1).
                  {
                    pose proof (memory_trace_is_read_or_write (l' ++ [x1]) l' x1).
                    destruct H15.
                    - tauto.
                    - tauto.
                    - destruct H15.
                      exists x2, x3.
                      tauto.
                  }
                  destruct x1.(mem_ins) eqn:Hx1.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H16 address1 value1 address0 value0).
                      specialize (H16 H9).
                      apply H16.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H16.
                    + destruct H2.
                      apply (trace_memory_multiple_read_to_read x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      apply or_intror.
                      split; tauto.
                    + tauto.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H16 address1 value1 address0 value0).
                      specialize (H16 H9).
                      apply H16.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H16.
                    + destruct H2.
                      apply (trace_memory_multiple_write_to_read x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      apply or_intror.
                      split; tauto.
                    + tauto.
                  - destruct H15.
                    destruct H15.
                    destruct H15; discriminate.
                }
            * pose proof (cons_app_eq a l0).
              destruct H2; destruct H2.
              rewrite H2 in H8.
              clear H14.
              assert (l1 ++ x :: x2 ++ [x1] = (l1 ++ x :: x2) ++ [x1]).
              {
                rewrite app_comm_cons.
                rewrite app_assoc.
                tauto. 
              }
              rewrite H14 in H8.
              apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              clear H13 H14.
              rewrite H2.
              rewrite H2 in H0.
              rewrite H2 in H1.
              rewrite H2 in H6.
              rewrite H2 in H9.
              rewrite <- app_assoc.
              simpl.
              rewrite app_assoc.
              apply (trace_memory_multiple_write_to_read x1 x0 (l1 ++ x2) address0 value0 next_address next_value).
              rewrite <- app_assoc.
              tauto. tauto. tauto. tauto.
          - assert (memory_trace0 ++
            [action0; next_action] = (memory_trace0 ++
            [action0]) ++ [next_action]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H13 in H8.
            assert (l1 ++ x :: l0 ++ [x0] = (l1 ++ (x :: l0)) ++ [x0]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H14 in H8.
            apply app_inj_tail in H8.
            destruct H8.
            rewrite H8 in H9.
            apply (H0 H9) in H6.
            subst.
            destruct l0.
            * apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              inversion H12.
              + destruct H2.
                destruct H8.
                lia.
              + destruct l1.
                {
                  simpl.
                  destruct H2.
                  apply trace_memory_single_read in H11.
                  apply H11.
                  apply H8.
                }
                {
                  (* if l0 = nil, action0 = x, 
                  possible_address_above <= address0 < next_address,
                  next_value = Int256.repr 0, thus memory_constraint l1 ++ [x0]
                  o.w. l0 = l0' ++ [action0], action0 and x0 satisfy all these prop,
                  thus memory_constraint (l1 ++ l0 ++ [x0]) *)
                  pose proof (cons_app_eq a l1).
                  destruct H8.
                  destruct H8 as [l' H8].
                  rewrite H8 in H6.
                  rewrite app_nil_r in H6.
                  rewrite H8 in H9.
                  rewrite H8.
                  simpl.
                  assert (exists address1 value1, x1.(mem_ins) = read address1 value1 \/ x1.(mem_ins) = write address1 value1).
                  {
                    pose proof (memory_trace_is_read_or_write (l' ++ [x1]) l' x1).
                    destruct H15.
                    - tauto.
                    - tauto.
                    - destruct H15.
                      exists x2, x3.
                      tauto.
                  }
                  destruct x1.(mem_ins) eqn:Hx1.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H16 address1 value1 address0 value0).
                      specialize (H16 H9).
                      apply H16.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H16.
                    + destruct H2.
                      apply (trace_memory_multiple_read_to_read x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      apply or_intror.
                      split; tauto.
                    + tauto.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H16 address1 value1 address0 value0).
                      specialize (H16 H9).
                      apply H16.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H16.
                    + destruct H2.
                      apply (trace_memory_multiple_write_to_read x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      apply or_intror.
                      split; tauto.
                    + tauto.
                  - destruct H15.
                    destruct H15.
                    destruct H15; discriminate.
                }
            * pose proof (cons_app_eq a l0).
              destruct H2; destruct H2.
              rewrite H2 in H8.
              clear H14.
              assert (l1 ++ x :: x2 ++ [x1] = (l1 ++ x :: x2) ++ [x1]).
              {
                rewrite app_comm_cons.
                rewrite app_assoc.
                tauto. 
              }
              rewrite H14 in H8.
              apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              clear H13 H14.
              rewrite H2.
              rewrite H2 in H0.
              rewrite H2 in H1.
              rewrite H2 in H6.
              rewrite H2 in H9.
              rewrite <- app_assoc.
              simpl.
              rewrite app_assoc.
              apply (trace_memory_multiple_read_to_read x1 x0 (l1 ++ x2) address0 value0 next_address next_value).
              rewrite <- app_assoc.
              tauto. tauto. tauto. tauto.
          - assert (memory_trace0 ++
            [action0; next_action] = (memory_trace0 ++
            [action0]) ++ [next_action]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H14 in H8.
            assert (l1 ++ x :: l0 ++ [x0] = (l1 ++ (x :: l0)) ++ [x0]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H15 in H8.
            apply app_inj_tail in H8.
            destruct H8.
            rewrite H8 in H9.
            apply (H0 H9) in H6.
            subst.
            destruct l0.
            * apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              apply Zle_lt_or_eq in H12.
              apply or_comm in H12.
              inversion H12.
              + apply H13 in H2.
                lia.
              + destruct l1.
                {
                  simpl.
                  apply (trace_memory_single_write x0 next_address next_value).
                  apply H11.
                }
                {
                  (* if l0 = nil, action0 = x, 
                  possible_address_above <= address0 < next_address,
                  next_value = Int256.repr 0, thus memory_constraint l1 ++ [x0]
                  o.w. l0 = l0' ++ [action0], action0 and x0 satisfy all these prop,
                  thus memory_constraint (l1 ++ l0 ++ [x0]) *)
                  pose proof (cons_app_eq a l1).
                  destruct H8.
                  destruct H8 as [l' H8].
                  rewrite H8 in H6.
                  rewrite app_nil_r in H6.
                  rewrite H8 in H9.
                  rewrite H8.
                  simpl.
                  assert (exists address1 value1, x1.(mem_ins) = read address1 value1 \/ x1.(mem_ins) = write address1 value1).
                  {
                    pose proof (memory_trace_is_read_or_write (l' ++ [x1]) l' x1).
                    destruct H16.
                    - tauto.
                    - tauto.
                    - destruct H16.
                      exists x2, x3.
                      tauto.
                  }
                  destruct x1.(mem_ins) eqn:Hx1.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H17 address1 value1 address0 value0).
                      specialize (H17 H9).
                      apply H17.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H17.
                    + destruct H2.
                      apply (trace_memory_multiple_read_to_write x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      lia.
                      lia.
                    + tauto.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H17 address1 value1 address0 value0).
                      specialize (H17 H9).
                      apply H17.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H17.
                    + destruct H2.
                      apply (trace_memory_multiple_write_to_write x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      lia.
                      lia.
                    + tauto.
                  - destruct H16.
                    destruct H16.
                    destruct H16; discriminate.
                }
            * pose proof (cons_app_eq a l0).
              destruct H2; destruct H2.
              rewrite H2 in H8.
              clear H14.
              assert (l1 ++ x :: x2 ++ [x1] = (l1 ++ x :: x2) ++ [x1]).
              {
                rewrite app_comm_cons.
                rewrite app_assoc.
                tauto. 
              }
              rewrite H14 in H8.
              apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              clear H13 H14.
              rewrite H2.
              rewrite H2 in H0.
              rewrite H2 in H1.
              rewrite H2 in H6.
              rewrite H2 in H9.
              rewrite <- app_assoc.
              simpl.
              rewrite app_assoc.
              apply (trace_memory_multiple_write_to_write x1 x0 (l1 ++ x2) address0 value0 next_address next_value).
              rewrite <- app_assoc.
              tauto. tauto. tauto. tauto.
              rewrite <- app_assoc in H1.
              simpl in H1.
              rewrite app_comm_cons in H1.
              rewrite app_assoc in H1.
              inversion H1.
              + symmetry in H13.
                apply app_eq_nil in H13.
                destruct H13.
                discriminate.
              + symmetry in H8.
                apply app_eq_unit in H8.
                destruct H8; destruct H8; discriminate.
              + symmetry in H8.
                apply app_eq_unit in H8.
                destruct H8; destruct H8; discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H18 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H16 in H11.
                discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H18 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H16 in H11.
                discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H19 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H14 in H10.
                inversion H10.
                rewrite H16 in H11.
                inversion H11.
                subst.
                tauto.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H19 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H14 in H10.
                discriminate.
          - assert (memory_trace0 ++
            [action0; next_action] = (memory_trace0 ++
            [action0]) ++ [next_action]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H14 in H8.
            assert (l1 ++ x :: l0 ++ [x0] = (l1 ++ (x :: l0)) ++ [x0]).
            {
              rewrite <- app_assoc.
              tauto.
            }
            rewrite H15 in H8.
            apply app_inj_tail in H8.
            destruct H8.
            rewrite H8 in H9.
            apply (H0 H9) in H6.
            subst.
            destruct l0.
            * apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              apply Zle_lt_or_eq in H12.
              apply or_comm in H12.
              inversion H12.
              + apply H13 in H2.
                lia.
              + destruct l1.
                {
                  simpl.
                  apply (trace_memory_single_write x0 next_address next_value).
                  apply H11.
                }
                {
                  (* if l0 = nil, action0 = x, 
                  possible_address_above <= address0 < next_address,
                  next_value = Int256.repr 0, thus memory_constraint l1 ++ [x0]
                  o.w. l0 = l0' ++ [action0], action0 and x0 satisfy all these prop,
                  thus memory_constraint (l1 ++ l0 ++ [x0]) *)
                  pose proof (cons_app_eq a l1).
                  destruct H8.
                  destruct H8 as [l' H8].
                  rewrite H8 in H6.
                  rewrite app_nil_r in H6.
                  rewrite H8 in H9.
                  rewrite H8.
                  simpl.
                  assert (exists address1 value1, x1.(mem_ins) = read address1 value1 \/ x1.(mem_ins) = write address1 value1).
                  {
                    pose proof (memory_trace_is_read_or_write (l' ++ [x1]) l' x1).
                    destruct H16.
                    - tauto.
                    - tauto.
                    - destruct H16.
                      exists x2, x3.
                      tauto.
                  }
                  destruct x1.(mem_ins) eqn:Hx1.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H17 address1 value1 address0 value0).
                      specialize (H17 H9).
                      apply H17.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H17.
                    + destruct H2.
                      apply (trace_memory_multiple_read_to_write x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      lia.
                      lia.
                    + tauto.
                  - assert (Int256.unsigned address1 <= Int256.unsigned address0)%Z.
                    {
                      pose proof (memory_trace_address_less_than l' x1 x).
                      specialize (H17 address1 value1 address0 value0).
                      specialize (H17 H9).
                      apply H17.
                      tauto.
                    }
                    apply (Z.le_lt_trans (Int256.unsigned address1) (Int256.unsigned address0) (Int256.unsigned next_address)) in H17.
                    + destruct H2.
                      apply (trace_memory_multiple_write_to_write x1 x0 l' address1 value1 next_address next_value) in H6.
                      rewrite <- app_assoc.
                      tauto.
                      tauto.
                      tauto.
                      lia.
                      lia.
                    + tauto.
                  - destruct H16.
                    destruct H16.
                    destruct H16; discriminate.
                }
            * pose proof (cons_app_eq a l0).
              destruct H2; destruct H2.
              rewrite H2 in H8.
              clear H14.
              assert (l1 ++ x :: x2 ++ [x1] = (l1 ++ x :: x2) ++ [x1]).
              {
                rewrite app_comm_cons.
                rewrite app_assoc.
                tauto. 
              }
              rewrite H14 in H8.
              apply app_inj_tail in H8.
              destruct H8.
              subst.
              apply Forall_inv in H7.
              clear H13 H14.
              rewrite H2.
              rewrite H2 in H0.
              rewrite H2 in H1.
              rewrite H2 in H6.
              rewrite H2 in H9.
              rewrite <- app_assoc.
              simpl.
              rewrite app_assoc.
              apply (trace_memory_multiple_read_to_write x1 x0 (l1 ++ x2) address0 value0 next_address next_value).
              rewrite <- app_assoc.
              tauto. tauto. tauto. tauto.
              rewrite <- app_assoc in H1.
              simpl in H1.
              rewrite app_comm_cons in H1.
              rewrite app_assoc in H1.
              inversion H1.
              + symmetry in H13.
                apply app_eq_nil in H13.
                destruct H13.
                discriminate.
              + symmetry in H8.
                apply app_eq_unit in H8.
                destruct H8; destruct H8; discriminate.
              + symmetry in H8.
                apply app_eq_unit in H8.
                destruct H8; destruct H8; discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H18 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H16 in H11.
                discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H18 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H16 in H11.
                discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H19 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H14 in H10.
                discriminate.
              + assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
                rewrite ! H19 in H8.
                rewrite ! app_assoc in H8.
                apply app_inj_tail in H8.
                destruct H8.
                apply app_inj_tail in H8.
                destruct H8.
                subst.
                rewrite H14 in H10.
                inversion H10.
                rewrite H16 in H11.
                inversion H11.
                subst.
                tauto.
        }
    }
    left.
    split; try congruence.
    exists l1, l2.
    split; try tauto.
  - exists memory_trace.
    split.
    {
      constructor.
      + inversion H. subst.
        assert (filter mem_ins_type_is_not_non (l ++ [x]) = filter mem_ins_type_is_not_non l).
        {
          rewrite filter_app.
          simpl.
          unfold mem_ins_type_is_not_non.
          rewrite Heq.
          rewrite app_nil_r.
          tauto.
        }
        rewrite H3 in H2.
        constructor.
        apply H2.
      + tauto.
    }
    right.
    split; try tauto.
Qed.

Lemma last_action_trace_timestamp_biggest: forall (l l': list action_type)(x: action_type),
  l = l' ++ [x] ->
  action_trace_timestamp_constraint (l' ++ [x]) ->
  Forall (fun a : action_type => a.(timestamp) < x.(timestamp)) l'.
Proof.
  intros.
  remember (length l) as ll.
  revert Heqll H H0. revert x l' l.
  induction ll.
  - intros.
    symmetry in Heqll.
    rewrite length_zero_iff_nil in Heqll.
    rewrite Heqll in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H.
    discriminate.
  - intros.
    destruct l'.
    + auto.
    + pose proof (cons_app_eq a l').
      destruct H1 as [y [l0 H1]].
      rewrite H1 in H0.
      rewrite H1.
      rewrite H1 in H.
      rewrite H in Heqll.
      rewrite app_length in Heqll.
      simpl in Heqll.
      assert (ll = Datatypes.length (l0 ++ [y])). { lia. }
      inversion H0.
      * symmetry in H4.
        apply app_eq_nil in H4.
        destruct H4.
        discriminate.
      * symmetry in H3.
        apply app_eq_unit in H3.
        destruct H3; destruct H3.
        apply app_eq_nil in H3.
        destruct H3.
        discriminate.
        discriminate.
      * apply app_inj_tail in H3.
        destruct H3.
        apply app_inj_tail in H3.
        destruct H3.
        subst.
        specialize (IHll y l0 (l0 ++ [y])).
        destruct IHll.
        tauto. tauto. tauto.
        simpl in H0.
        inversion H0.
        assert (forall {A: Type}(x y: A), [x; y] = [x] ++ [y]). { tauto. }
        rewrite H6 in H.
        apply app_inj_tail in H.
        destruct H.
        apply app_eq_unit in H.
        destruct H; destruct H.
        {
          subst.
          simpl.
          assert (y.(timestamp) < x.(timestamp)). { lia. }
          auto.
        }
        discriminate.
        assert (y.(timestamp) < x.(timestamp)). { lia. }
        apply Forall_app.
        split.
        {
          assert (x0.(timestamp) < x.(timestamp)). { lia. }
          apply Forall_cons.
          - tauto.
          - pose proof (Forall_forall (fun a : action_type => a.(timestamp) < y.(timestamp)) l).
            rewrite H6 in f.
            pose proof (Forall_forall (fun a0 : action_type => a0.(timestamp) < x.(timestamp)) l).
            rewrite H7.
            intros.
            apply (f x1) in H8.
            lia.
        }
        {
          apply Forall_cons.
          tauto.
          apply Forall_nil.
        }
Qed.

Inductive last_mem_prop(last_mem: int256 -> int256)(memory_trace: list action_type)(address: int256): Prop :=
| in_memory_trace:
    (exists action value, In action memory_trace /\
    (action.(mem_ins) = read address value \/ action.(mem_ins) = write address value) /\
    last_mem address = value /\
    (forall action' value', In action' memory_trace ->
    (action'.(mem_ins) = read address value' \/ action'.(mem_ins) = write address value') ->
    action' <> action ->
    action'.(timestamp) < action.(timestamp))) ->
    last_mem_prop last_mem memory_trace address
| not_in_memory_trace:
    (forall action address0 value0,
    In action memory_trace ->  (action.(mem_ins) = read address0 value0 \/ action.(mem_ins) = write address0 value0) ->
    address <> address0) ->
    last_mem address = Int256.repr 0 ->
    last_mem_prop last_mem memory_trace address.

Lemma construct_last_mem: forall (memory_trace memory_trace' l: list action_type)(x: action_type)(address: int256)(last_mem': int256 -> int256),
  memory_constraint memory_trace ->
  permutation_constraint (l ++ [x]) memory_trace ->
  memory_constraint memory_trace' ->
  permutation_constraint l memory_trace' ->
  Forall (fun a : action_type => a.(timestamp) < x.(timestamp)) l ->
  (x.(mem_ins) <> non /\ (exists l1' l2', (memory_trace' = l1' ++ l2' /\ memory_trace = l1' ++ [x] ++ l2')) \/
  (x.(mem_ins) = non /\ memory_trace = memory_trace')) ->
  (forall address : int256,
  last_mem_prop last_mem' memory_trace' address) ->
  last_mem_prop
  (fun address0 : int256 =>
   match x.(mem_ins) with
   | write address1 value =>
       if
        Int256.eq address1
          address0
       then value
       else last_mem' address0
   | _ => last_mem' address0
   end) memory_trace address.
Proof.
  intros.
  destruct x.(mem_ins) eqn:ins_type; destruct H4; destruct H4; try congruence.
  - destruct H6 as [l1 [l2 H6]].
    destruct H6.
    destruct l1.
    * simpl in H6, H7.
      specialize (H5 address).
      inversion H5.
      + pose proof (Int256.eq_dec address0 address).
        destruct H9.
        revert e. intro H9.
        {
          (* address0 = address -> False *)
          rewrite H9 in ins_type.
          destruct H8 as [action [value1 H8]].
          destruct H8; destruct H10; destruct H11.
          rewrite <- H6 in H7.
          rewrite H7 in H.
          pose proof (memory_trace_timestamp_less_than_in_behind [] memory_trace' x).
          specialize (H13 action address value value1).
          simpl in H13.
          assert (x.(mem_ins) = read address value /\
          action.(mem_ins) = read address value1 \/
          x.(mem_ins) = read address value /\
          action.(mem_ins) = write address value1 \/
          x.(mem_ins) = write address value /\
          action.(mem_ins) = read address value1 \/
          x.(mem_ins) = write address value /\
          action.(mem_ins) = write address value1). { tauto. }
          apply (H13 H H8) in H14.
          inversion H2. clear H17 memory_trace0.
          apply (filter_preserves_Forall l (fun a : action_type => a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H3.
          apply (Permutation_Forall H15) in H3.
          rewrite Forall_forall in H3.
          specialize (H3 action).
          apply H3 in H8.
          lia.
        }
        revert n. intro H9.
        {
          (* address0 <> address *)
          apply in_memory_trace.
          rewrite <- H6 in H7.
          rewrite H7 in H.
          rewrite H7.
          destruct H8 as [action [value1 H8]].
          destruct H8; destruct H10; destruct H11.
          exists action, value1.
          split; try split; try split; try tauto.
          apply (in_cons x action memory_trace').
          tauto.
          intros.
          destruct H13.
          - rewrite <- H13 in H14.
            rewrite ins_type in H14.
            destruct H14; congruence.
          - apply (H12 action' value' H13 H14 H15).
        }
      + pose proof (Int256.eq_dec address0 address).
        destruct H10.
        revert e. intro H10.
        {
          apply in_memory_trace.
          assert (value = Int256.repr 0).
          {
            pose proof (memory_trace_fisrt_read_value_zero l2 x address0 value).
            rewrite <- H7 in H11.
            apply H11 in H; try tauto.
          }
          rewrite H11 in ins_type.
          exists x, (Int256.repr 0).
          rewrite ! H7, <- H10.
          split; try split; try split; try tauto.
          simpl; left; tauto.
          rewrite H10; tauto.
          intros.
          destruct H12; try congruence.
          rewrite <- H6 in H12.
          apply (H8 action' address0 value' H12) in H13.
          congruence.
        }
        revert n. intro H10.
        {
          apply not_in_memory_trace; try tauto.
          rewrite H7.
          intros.
          destruct H11.
          - rewrite <- H11 in H12.
            destruct H12; try rewrite ins_type in H12.
            + inversion H12.
              rewrite H14 in H10; auto.
            + discriminate.
          - rewrite <- H6 in H11.
            apply (H8 action0 address1 value0); try tauto.
        }
    * pose proof (cons_app_eq a l1).
      destruct H8 as [y [l' H8]].
      rewrite H8 in H6, H7; clear H8.
      specialize (H5 address).
      inversion H5.
      + pose proof (Int256.eq_dec address0 address).
        destruct H9.
        revert e. intro H9.
        {
          (* address0 = address -> False *)
          rewrite H9 in ins_type.
          destruct H8 as [action [value1 H8]].
          destruct H8; destruct H10; destruct H11.
          rewrite H6 in H8.
          apply in_app_or in H8.
          inversion H8.
          - apply in_app_or in H13.
            inversion H13.
            + pose proof (memory_trace_is_read_or_write_in memory_trace' y).
              assert (In y memory_trace').
              {
                rewrite H6.
                apply in_or_app.
                left.
                apply in_or_app.
                right.
                simpl; tauto.
              }
              specialize (H15 H16 H1).
              destruct H15 as [address_y [value_y H15]].
              pose proof (memory_trace_address_less_than_in l' l2 action y address value1 address_y value_y).
              assert (action.(mem_ins) = read address value1 /\
              y.(mem_ins) = read address_y value_y \/
              action.(mem_ins) = read address value1 /\
              y.(mem_ins) = write address_y value_y \/
              action.(mem_ins) = write address value1 /\
              y.(mem_ins) = read address_y value_y \/
              action.(mem_ins) = write address value1 /\
              y.(mem_ins) = write address_y value_y). { tauto. }
              rewrite <- app_assoc in H6.
              rewrite <- H6 in H17.
              apply (H17 H14 H1) in H18. clear H17.
              pose proof (memory_trace_address_less_than_next l' l2 y x address_y value_y address value).
              assert (y.(mem_ins) = read address_y value_y /\
              x.(mem_ins) = read address value \/
              y.(mem_ins) = read address_y value_y /\
              x.(mem_ins) = write address value \/
              y.(mem_ins) = write address_y value_y /\
              x.(mem_ins) = read address value \/
              y.(mem_ins) = write address_y value_y /\
              x.(mem_ins) = write address value). { tauto. }
              rewrite app_assoc in H17.
              rewrite <- H7 in H17.
              apply (H17 H) in H19.
              clear H17.
              assert (Int256.unsigned address = Int256.unsigned address_y). { lia. }
              clear H18 H19 H16.
              assert (address = address_y).
              {
                assert (Int256.repr (Int256.unsigned address) = Int256.repr (Int256.unsigned address_y)).
                {
                  rewrite H17; tauto.
                }
                rewrite (Int256.repr_unsigned address) in H16.
                rewrite ((Int256.repr_unsigned address_y)) in H16.
                tauto.
              }
              rewrite <- ! H16 in H15.
              pose proof (memory_trace_timestamp_less_than_in_front l' l2 y action address value_y value1).
              rewrite <- H6 in H18.
              assert (y.(mem_ins) = read address value_y /\
              action.(mem_ins) = read address value1 \/
              y.(mem_ins) = read address value_y /\
              action.(mem_ins) = write address value1 \/
              y.(mem_ins) = write address value_y /\
              action.(mem_ins) = read address value1 \/
              y.(mem_ins) = write address value_y /\
              action.(mem_ins) = write address value1). { tauto. }
              specialize (H18 H1 H14 H19). clear H19.
              specialize (H12 y value_y).
              assert (In y memory_trace').
              {
                rewrite H6.
                apply in_or_app.
                right.
                apply in_or_app.
                left.
                simpl; tauto.
              }
              specialize (H12 H19 H15).
              assert (y <> action).
              {
                intro.
                rewrite H20 in H18.
                lia.
              }
              apply H12 in H20.
              clear H12.
              lia.
            + simpl in H14.
              destruct H14; try tauto.
              pose proof (memory_trace_timestamp_less_than l' l2 [] y x address value1 value).
              rewrite <- ! app_assoc in H7.
              rewrite <- H14 in H10.
              assert (y.(mem_ins) = read address value1 /\
              x.(mem_ins) = read address value \/
              y.(mem_ins) = read address value1 /\
              x.(mem_ins) = write address value \/
              y.(mem_ins) = write address value1 /\
              x.(mem_ins) = read address value \/
              y.(mem_ins) = write address value1 /\
              x.(mem_ins) = write address value). { tauto. }
              rewrite app_nil_l in H15.
              rewrite <- H7 in H15.
              specialize (H15 H H16). clear H16.
              rewrite <- H14 in H12.
              pose proof (memory_trace_read_value_eq l' l2 y x address value1 value).
              assert (y.(mem_ins) = read address value1 /\
              x.(mem_ins) = read address value \/
              y.(mem_ins) = write address value1 /\
              x.(mem_ins) = read address value). { tauto. }
              rewrite <- H7 in H16.
              specialize (H16 H H17). clear H17.
              assert (value1 = value).
              {
                rewrite <- (Int256.repr_unsigned value1).
                rewrite <- (Int256.repr_unsigned value).
                rewrite H16; tauto.
              }
              rewrite H17 in H11.
              apply in_memory_trace.
              exists x, value.
              split; try split; try split; try tauto.
              {
                rewrite H7.
                apply in_or_app.
                right.
                apply in_or_app.
                right.
                apply in_or_app.
                left.
                simpl; tauto.
              }
              rewrite H7.
              intros.
              apply in_app_or in H18.
              destruct H18.
              {
                assert (In action' memory_trace').
                {
                  rewrite H6.
                  apply in_or_app.
                  left.
                  apply in_or_app.
                  left.
                  tauto.
                }
                specialize (H12 action' value' H21 H19).
                assert (action' <> y).
                {
                  intro.
                  pose proof (memory_trace_timestamp_less_than_in_front l' l2 y action' address value1 value').
                  rewrite <- app_assoc in H6.
                  rewrite <- H6 in H23.
                  assert (y.(mem_ins) = read address value1 /\
                  action'.(mem_ins) = read address value' \/
                  y.(mem_ins) = read address value1 /\
                  action'.(mem_ins) = write address value' \/
                  y.(mem_ins) = write address value1 /\
                  action'.(mem_ins) = read address value' \/
                  y.(mem_ins) = write address value1 /\
                  action'.(mem_ins) = write address value'). { tauto. }
                  specialize (H23 H1 H18 H24).
                  rewrite H22 in H23.
                  lia.
                }
                apply H12 in H22.
                lia.
              }
              apply in_app_or in H18.
              destruct H18.
              {
                simpl in H18; destruct H18; try tauto.
                rewrite H18 in H15.
                assumption.
              }
              apply in_app_or in H18.
              destruct H18.
              {
                simpl in H18; destruct H18; try tauto.
                congruence.
              }
              {
                assert (In action' memory_trace').
                {
                  rewrite H6.
                  apply in_or_app.
                  right.
                  tauto.
                }
                specialize (H12 action' value' H21 H19).
                assert (action' <> y).
                {
                  intro.
                  pose proof (memory_trace_timestamp_less_than_in_behind l' l2 y action' address value1 value').
                  rewrite <- app_assoc in H6.
                  rewrite <- H6 in H23.
                  assert (y.(mem_ins) = read address value1 /\
                  action'.(mem_ins) = read address value' \/
                  y.(mem_ins) = read address value1 /\
                  action'.(mem_ins) = write address value' \/
                  y.(mem_ins) = write address value1 /\
                  action'.(mem_ins) = read address value' \/
                  y.(mem_ins) = write address value1 /\
                  action'.(mem_ins) = write address value'). { tauto. }
                  specialize (H23 H1 H18 H24).
                  rewrite H22 in H23.
                  lia.
                }
                apply H12 in H22.
                lia.
                (* also a contradiction *)
              }
          - rewrite H6 in H2.
            inversion H2.
            apply (filter_preserves_Forall l (fun a : action_type =>
            a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H3.
            apply (Permutation_Forall H14) in H3.
            apply Forall_app in H3.
            destruct H3.
            rewrite (Forall_forall (fun a : action_type =>
            a.(timestamp) < x.(timestamp)) l2) in H17.
            specialize (H17 action H13).
            pose proof (memory_trace_timestamp_less_than_in_behind (l' ++ [y]) l2 x action address value value1).
            assert (x.(mem_ins) = read address value /\
            action.(mem_ins) = read address value1 \/
            x.(mem_ins) = read address value /\
            action.(mem_ins) = write address value1 \/
            x.(mem_ins) = write address value /\
            action.(mem_ins) = read address value1 \/
            x.(mem_ins) = write address value /\
            action.(mem_ins) = write address value1). { tauto. }
            rewrite <- H7 in H18.
            specialize (H18 H H13 H19).
            lia.
        }
        revert n. intro H9.
        {
          (* address0 <> address *)
          apply in_memory_trace.
          destruct H8 as [action' [value' H8]].
          destruct H8. destruct H10. destruct H11.
          exists action', value'.
          split; try split; try split; try tauto.
          - rewrite H6 in H8.
            rewrite H7.
            apply in_app_or in H8.
            destruct H8.
            + apply in_or_app; left; tauto.
            + apply in_or_app; right; apply in_or_app; right; tauto.
          - intros.
            rewrite H7 in H13.
            apply in_app_or in H13.
            destruct H13.
            + assert (In action'0 memory_trace').
              {
                rewrite H6; apply in_or_app; left; tauto.
              }
              exact (H12 action'0 value'0 H16 H14 H15).
            + apply in_app_or in H13.
              destruct H13.
              * simpl in H13; destruct H13; try tauto.
                rewrite H13 in ins_type.
                destruct H14; congruence.
              * assert (In action'0 memory_trace').
                {
                  rewrite H6; apply in_or_app; right; tauto.
                }
                exact (H12 action'0 value'0 H16 H14 H15).
        }
      + destruct (Int256.eq_dec address0 address).
        revert e. intro H10.
        {
          (* address0 = address *)
          apply in_memory_trace.
          exists x, value.
          split; try split; try split.
          - rewrite H7.
            apply in_or_app; right; apply in_or_app; left; simpl; left; tauto.
          - rewrite H10 in ins_type.
            tauto.
          - assert (value = Int256.repr 0).
            {
              apply (memory_trace_fisrt_address_value_zero (l' ++ [y]) l2 x address0 value); try tauto.
              intros.
              assert (In action0 memory_trace').
              {
                rewrite H6.
                apply in_or_app.
                left.
                tauto.
              }
              rewrite H10.
              apply (H8 action0 address1 value0 H13 H12).
              rewrite <- H7.
              tauto.
            }
            rewrite H11; tauto.
          - intros.
            rewrite H7 in H11.
            apply in_app_or in H11.
            destruct H11.
            + assert (In action' memory_trace').
              {
                rewrite H6.
                apply in_or_app.
                left.
                tauto.
              }
              apply (filter_preserves_Forall l (fun a : action_type => a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H3.
              inversion H2.
              apply (Permutation_Forall H15) in H3.
              rewrite Forall_forall in H3.
              apply (H3 action' H14).
            + apply in_app_or in H11.
              destruct H11.
              * simpl in H11; destruct H11; try tauto.
                congruence.
              * assert (In action' memory_trace').
                {
                  rewrite H6.
                  apply in_or_app.
                  right.
                  tauto.
                }
                apply (filter_preserves_Forall l (fun a : action_type => a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H3.
                inversion H2.
                apply (Permutation_Forall H15) in H3.
                rewrite Forall_forall in H3.
                apply (H3 action' H14).
        }
        revert n. intro H10.
        {
          (* address0 <> address *)
          apply not_in_memory_trace; try tauto.
          rewrite H7.
          intros.
          apply in_app_or in H11.
          destruct H11.
          - assert (In action0 memory_trace').
            {
              rewrite H6.
              apply in_or_app.
              left; tauto.
            }
            apply (H8 action0 address1 value0 H13 H12).
          - apply in_app_or in H11.
            destruct H11.
            + simpl in H11; destruct H11; try tauto.
              rewrite <- H11 in H12.
              rewrite ins_type in H12.
              assert (address0 = address1).
              {
                destruct H12; inversion H12; tauto.
              }
              rewrite <- H13.
              congruence.
            + assert (In action0 memory_trace').
              {
                rewrite H6.
                apply in_or_app.
                right; tauto.
              }
              apply (H8 action0 address1 value0 H13 H12).
        }
  - destruct H6 as [l1 [l2 H6]].
    destruct H6.
    destruct l1.
    * simpl in H6, H7.
      specialize (H5 address).
      inversion H5.
      + pose proof (Int256.eq_dec address0 address).
        destruct H9.
        revert e. intro H9.
        {
          (* address0 = address -> False *)
          rewrite H9 in ins_type.
          destruct H8 as [action [value1 H8]].
          destruct H8; destruct H10; destruct H11.
          rewrite <- H6 in H7.
          rewrite H7 in H.
          pose proof (memory_trace_timestamp_less_than_in_behind [] memory_trace' x).
          specialize (H13 action address value value1).
          simpl in H13.
          assert (x.(mem_ins) = read address value /\
          action.(mem_ins) = read address value1 \/
          x.(mem_ins) = read address value /\
          action.(mem_ins) = write address value1 \/
          x.(mem_ins) = write address value /\
          action.(mem_ins) = read address value1 \/
          x.(mem_ins) = write address value /\
          action.(mem_ins) = write address value1). { tauto. }
          apply (H13 H H8) in H14.
          inversion H2. clear H17 memory_trace0.
          apply (filter_preserves_Forall l (fun a : action_type => a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H3.
          apply (Permutation_Forall H15) in H3.
          rewrite Forall_forall in H3.
          specialize (H3 action).
          apply H3 in H8.
          lia.
        }
        revert n. intro H9.
        {
          (* address0 <> address *)
          apply in_memory_trace.
          rewrite <- H6 in H7.
          rewrite H7 in H.
          rewrite H7.
          destruct H8 as [action [value1 H8]].
          destruct H8; destruct H10; destruct H11.
          exists action, value1.
          split; try split; try split; try tauto.
          apply (in_cons x action memory_trace'); tauto.
          assert (Int256.eq address0 address = false).
          {
            apply Int256.eq_false in H9; tauto.
          }
          rewrite H13; tauto.
          intros.
          destruct H13.
          - rewrite <- H13 in H14.
            rewrite ins_type in H14.
            destruct H14; congruence.
          - apply (H12 action' value' H13 H14 H15).
        }
      + pose proof (Int256.eq_dec address0 address).
        destruct H10.
        revert e. intro H10.
        {
          apply in_memory_trace.
          exists x, value.
          rewrite ! H7, <- H10.
          split; try split; try split; try tauto.
          simpl; left; tauto.
          rewrite H10; rewrite Int256.eq_true; tauto.
          intros.
          destruct H11; try congruence.
          rewrite <- H6 in H11.
          inversion H2.
          pose proof (filter_preserves_Forall l (fun a : action_type =>
          a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non H3).
          pose proof (Permutation_Forall H14 H17).
          rewrite Forall_forall in H18.
          apply (H18 action' H11).
        }
        revert n. intro H10.
        {
          apply Int256.eq_false in H10.
          apply not_in_memory_trace; try tauto; try rewrite H10; try tauto.
          rewrite H7.
          intros.
          destruct H11.
          - rewrite <- H11 in H12.
            destruct H12; try rewrite ins_type in H12.
            + discriminate.
            + inversion H12.
              rewrite H14 in H10.
              unfold not.
              intros.
              rewrite H13 in H10.
              rewrite Int256.eq_true in H10.
              discriminate.
          - rewrite <- H6 in H11.
            apply (H8 action0 address1 value0); try tauto.
        }
    * pose proof (cons_app_eq a l1).
      destruct H8 as [y [l' H8]].
      rewrite H8 in H6, H7; clear H8.
      specialize (H5 address).
      inversion H5.
      + pose proof (Int256.eq_dec address0 address).
        destruct H9.
        revert e. intro H9.
        {
          (* address0 = address -> False *)
          rewrite H9 in ins_type.
          destruct H8 as [action [value1 H8]].
          destruct H8; destruct H10; destruct H11.
          rewrite H6 in H8.
          apply in_app_or in H8.
          inversion H8.
          - apply in_app_or in H13.
            inversion H13.
            + pose proof (memory_trace_is_read_or_write_in memory_trace' y).
              assert (In y memory_trace').
              {
                rewrite H6.
                apply in_or_app.
                left.
                apply in_or_app.
                right.
                simpl; tauto.
              }
              specialize (H15 H16 H1).
              destruct H15 as [address_y [value_y H15]].
              pose proof (memory_trace_address_less_than_in l' l2 action y address value1 address_y value_y).
              assert (action.(mem_ins) = read address value1 /\
              y.(mem_ins) = read address_y value_y \/
              action.(mem_ins) = read address value1 /\
              y.(mem_ins) = write address_y value_y \/
              action.(mem_ins) = write address value1 /\
              y.(mem_ins) = read address_y value_y \/
              action.(mem_ins) = write address value1 /\
              y.(mem_ins) = write address_y value_y). { tauto. }
              rewrite <- app_assoc in H6.
              rewrite <- H6 in H17.
              apply (H17 H14 H1) in H18. clear H17.
              pose proof (memory_trace_address_less_than_next l' l2 y x address_y value_y address value).
              assert (y.(mem_ins) = read address_y value_y /\
              x.(mem_ins) = read address value \/
              y.(mem_ins) = read address_y value_y /\
              x.(mem_ins) = write address value \/
              y.(mem_ins) = write address_y value_y /\
              x.(mem_ins) = read address value \/
              y.(mem_ins) = write address_y value_y /\
              x.(mem_ins) = write address value). { tauto. }
              rewrite app_assoc in H17.
              rewrite <- H7 in H17.
              apply (H17 H) in H19.
              clear H17.
              assert (Int256.unsigned address = Int256.unsigned address_y). { lia. }
              clear H18 H19 H16.
              assert (address = address_y).
              {
                assert (Int256.repr (Int256.unsigned address) = Int256.repr (Int256.unsigned address_y)).
                {
                  rewrite H17; tauto.
                }
                rewrite (Int256.repr_unsigned address) in H16.
                rewrite ((Int256.repr_unsigned address_y)) in H16.
                tauto.
              }
              rewrite <- ! H16 in H15.
              pose proof (memory_trace_timestamp_less_than_in_front l' l2 y action address value_y value1).
              rewrite <- H6 in H18.
              assert (y.(mem_ins) = read address value_y /\
              action.(mem_ins) = read address value1 \/
              y.(mem_ins) = read address value_y /\
              action.(mem_ins) = write address value1 \/
              y.(mem_ins) = write address value_y /\
              action.(mem_ins) = read address value1 \/
              y.(mem_ins) = write address value_y /\
              action.(mem_ins) = write address value1). { tauto. }
              specialize (H18 H1 H14 H19). clear H19.
              specialize (H12 y value_y).
              assert (In y memory_trace').
              {
                rewrite H6.
                apply in_or_app.
                right.
                apply in_or_app.
                left.
                simpl; tauto.
              }
              specialize (H12 H19 H15).
              assert (y <> action).
              {
                intro.
                rewrite H20 in H18.
                lia.
              }
              apply H12 in H20.
              clear H12.
              lia.
            + simpl in H14.
              destruct H14; try tauto.
              pose proof (memory_trace_timestamp_less_than l' l2 [] y x address value1 value).
              rewrite <- ! app_assoc in H7.
              rewrite <- H14 in H10.
              assert (y.(mem_ins) = read address value1 /\
              x.(mem_ins) = read address value \/
              y.(mem_ins) = read address value1 /\
              x.(mem_ins) = write address value \/
              y.(mem_ins) = write address value1 /\
              x.(mem_ins) = read address value \/
              y.(mem_ins) = write address value1 /\
              x.(mem_ins) = write address value). { tauto. }
              rewrite app_nil_l in H15.
              rewrite <- H7 in H15.
              specialize (H15 H H16). clear H16.
              rewrite <- H14 in H12.
              apply in_memory_trace.
              exists x, value.
              split; try split; try split; try tauto.
              {
                rewrite H7.
                apply in_or_app.
                right.
                apply in_or_app.
                right.
                apply in_or_app.
                left.
                simpl; tauto.
              }
              {
                rewrite H9; rewrite Int256.eq_true; tauto.
              }
              rewrite H7.
              intros.
              apply in_app_or in H16.
              destruct H16.
              {
                assert (In action' memory_trace').
                {
                  rewrite H6.
                  apply in_or_app.
                  left.
                  apply in_or_app.
                  left.
                  tauto.
                }
                specialize (H12 action' value' H19 H17).
                assert (action' <> y).
                {
                  intro.
                  pose proof (memory_trace_timestamp_less_than_in_front l' l2 y action' address value1 value').
                  rewrite <- app_assoc in H6.
                  rewrite <- H6 in H21.
                  assert (y.(mem_ins) = read address value1 /\
                  action'.(mem_ins) = read address value' \/
                  y.(mem_ins) = read address value1 /\
                  action'.(mem_ins) = write address value' \/
                  y.(mem_ins) = write address value1 /\
                  action'.(mem_ins) = read address value' \/
                  y.(mem_ins) = write address value1 /\
                  action'.(mem_ins) = write address value'). { tauto. }
                  specialize (H21 H1 H16 H22).
                  rewrite H20 in H21.
                  lia.
                }
                apply H12 in H20.
                lia.
              }
              apply in_app_or in H16.
              destruct H16.
              {
                simpl in H16; destruct H16; try tauto.
                rewrite H16 in H15.
                assumption.
              }
              apply in_app_or in H16.
              destruct H16.
              {
                simpl in H16; destruct H16; try tauto.
                congruence.
              }
              {
                assert (In action' memory_trace').
                {
                  rewrite H6.
                  apply in_or_app.
                  right.
                  tauto.
                }
                specialize (H12 action' value' H19 H17).
                assert (action' <> y).
                {
                  intro.
                  pose proof (memory_trace_timestamp_less_than_in_behind l' l2 y action' address value1 value').
                  rewrite <- app_assoc in H6.
                  rewrite <- H6 in H21.
                  assert (y.(mem_ins) = read address value1 /\
                  action'.(mem_ins) = read address value' \/
                  y.(mem_ins) = read address value1 /\
                  action'.(mem_ins) = write address value' \/
                  y.(mem_ins) = write address value1 /\
                  action'.(mem_ins) = read address value' \/
                  y.(mem_ins) = write address value1 /\
                  action'.(mem_ins) = write address value'). { tauto. }
                  specialize (H21 H1 H16 H22).
                  rewrite H20 in H21.
                  lia.
                }
                apply H12 in H20.
                lia.
                (* also a contradiction *)
              }
          - rewrite H6 in H2.
            inversion H2.
            apply (filter_preserves_Forall l (fun a : action_type =>
            a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H3.
            apply (Permutation_Forall H14) in H3.
            apply Forall_app in H3.
            destruct H3.
            rewrite (Forall_forall (fun a : action_type =>
            a.(timestamp) < x.(timestamp)) l2) in H17.
            specialize (H17 action H13).
            pose proof (memory_trace_timestamp_less_than_in_behind (l' ++ [y]) l2 x action address value value1).
            assert (x.(mem_ins) = read address value /\
            action.(mem_ins) = read address value1 \/
            x.(mem_ins) = read address value /\
            action.(mem_ins) = write address value1 \/
            x.(mem_ins) = write address value /\
            action.(mem_ins) = read address value1 \/
            x.(mem_ins) = write address value /\
            action.(mem_ins) = write address value1). { tauto. }
            rewrite <- H7 in H18.
            specialize (H18 H H13 H19).
            lia.
        }
        revert n. intro H9.
        {
          (* address0 <> address *)
          apply in_memory_trace.
          destruct H8 as [action' [value' H8]].
          destruct H8. destruct H10. destruct H11.
          exists action', value'.
          split; try split; try split; try tauto.
          - rewrite H6 in H8.
            rewrite H7.
            apply in_app_or in H8.
            destruct H8.
            + apply in_or_app; left; tauto.
            + apply in_or_app; right; apply in_or_app; right; tauto.
          - pose proof H9.
            apply Int256.eq_false in H13.
            rewrite H13. tauto.
          - intros.
            rewrite H7 in H13.
            apply in_app_or in H13.
            destruct H13.
            + assert (In action'0 memory_trace').
              {
                rewrite H6; apply in_or_app; left; tauto.
              }
              exact (H12 action'0 value'0 H16 H14 H15).
            + apply in_app_or in H13.
              destruct H13.
              * simpl in H13; destruct H13; try tauto.
                rewrite H13 in ins_type.
                destruct H14; congruence.
              * assert (In action'0 memory_trace').
                {
                  rewrite H6; apply in_or_app; right; tauto.
                }
                exact (H12 action'0 value'0 H16 H14 H15).
        }
      + pose proof (Int256.eq_dec address0 address).
        destruct H10.
        revert e. intro H10.
        {
          (* address0 = address *)
          apply in_memory_trace.
          exists x, value.
          split; try split; try split.
          - rewrite H7.
            apply in_or_app; right; apply in_or_app; left; simpl; left; tauto.
          - rewrite H10 in ins_type.
            tauto.
          - rewrite H10.
            rewrite Int256.eq_true.
            tauto.
          - intros.
            rewrite H7 in H11.
            apply in_app_or in H11.
            destruct H11.
            + assert (In action' memory_trace').
              {
                rewrite H6.
                apply in_or_app.
                left.
                tauto.
              }
              apply (filter_preserves_Forall l (fun a : action_type => a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H3.
              inversion H2.
              apply (Permutation_Forall H15) in H3.
              rewrite Forall_forall in H3.
              apply (H3 action' H14).
            + apply in_app_or in H11.
              destruct H11.
              * simpl in H11; destruct H11; try tauto.
                congruence.
              * assert (In action' memory_trace').
                {
                  rewrite H6.
                  apply in_or_app.
                  right.
                  tauto.
                }
                apply (filter_preserves_Forall l (fun a : action_type => a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H3.
                inversion H2.
                apply (Permutation_Forall H15) in H3.
                rewrite Forall_forall in H3.
                apply (H3 action' H14).
        }
        revert n. intro H10.
        {
          (* address0 <> address *)
          apply not_in_memory_trace; try tauto.
          rewrite H7.
          intros.
          apply in_app_or in H11.
          destruct H11.
          - assert (In action0 memory_trace').
            {
              rewrite H6.
              apply in_or_app.
              left; tauto.
            }
            apply (H8 action0 address1 value0 H13 H12).
          - apply in_app_or in H11.
            destruct H11.
            + simpl in H11; destruct H11; try tauto.
              rewrite <- H11 in H12.
              rewrite ins_type in H12.
              assert (address0 = address1).
              {
                destruct H12; inversion H12; tauto.
              }
              rewrite <- H13.
              congruence.
            + assert (In action0 memory_trace').
              {
                rewrite H6.
                apply in_or_app.
                right; tauto.
              }
              apply (H8 action0 address1 value0 H13 H12).
          - apply Int256.eq_false in H10.
            rewrite H10; tauto.
        }
  - subst.
    apply (H5 address).
Qed.

Lemma in_property : forall (A B C D: Type) (x: A) (l: list A) (f: A -> B -> C -> D -> Prop)
  (s1: B)(s2: C)(s3: D),
  In x l -> f x s1 s2 s3 -> fold_right Sets.union ∅ (map f l) s1 s2 s3.
Proof.
  intros A B C D x l f s1 s2 s3 Hin Hfx.
  
  (* 使用 fold_right 的性质对列表 l 进行归纳 *)
  induction l as [| y l' IHl'].
  - (* Case: l is empty *)
    simpl. simpl in Hin. tauto.
    
  - (* Case: l is not empty *)
    simpl. destruct Hin as [Hx | Hin].
    + (* Subcase: x is the first element of l *)
      rewrite Hx.
      left.
      tauto.
    + (* Subcase: x is in the rest of the list *)
      apply IHl' in Hin. right. apply Hin.
Qed.

Lemma additional_property_to_for_new_read:
  forall (address value: int256)(x: action_type)(memory_trace memory_trace' l1 l2 l: list action_type)
  (last_mem': int256 -> int256),
  memory_constraint memory_trace ->
  memory_constraint memory_trace' ->
  permutation_constraint l memory_trace' ->
  permutation_constraint (l ++ [x]) memory_trace ->
  action_trace_timestamp_constraint (l ++ [x]) ->
  memory_trace' = l1 ++ l2 ->
  memory_trace = l1 ++ [x] ++ l2 ->
  x.(mem_ins) = read address value ->
  last_mem_prop last_mem' memory_trace' address ->
  last_mem' address = value.
Proof.
  intros.
  inversion H7.
  - destruct H8 as [action' [value' H8]].
    destruct H8; destruct H9; destruct H10.
    destruct l1.
    + simpl in H4.
      rewrite app_nil_l in H5.
      pose proof (memory_trace_timestamp_less_than_in_behind [] l2 x action' address value value').
      rewrite app_nil_l in H12.
      rewrite H4 in H8.
      assert (x.(mem_ins) = read address value /\
      action'.(mem_ins) = read address value' \/
      x.(mem_ins) = read address value /\
      action'.(mem_ins) = write address value' \/
      x.(mem_ins) = write address value /\
      action'.(mem_ins) = read address value' \/
      x.(mem_ins) = write address value /\
      action'.(mem_ins) = write address value'). { tauto. }
      rewrite <- H5 in H12.
      apply (H12 H H8) in H13.
      clear H12.
      pose proof (last_action_trace_timestamp_biggest (l ++ [x]) l x).
      assert (l ++ [x] = l ++ [x]). { reflexivity. }
      apply (H12 H14) in H3; clear H12 H14.
      inversion H1.
      apply (filter_preserves_Forall l (fun a : action_type =>
      a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H3.
      apply (Permutation_Forall H12) in H3.
      rewrite H4 in H3.
      rewrite Forall_forall in H3.
      specialize (H3 action' H8).
      lia.
    + pose proof (cons_app_eq a l1).
      destruct H12 as [y [l' H12]].
      rewrite H12 in H4, H5; clear H12.
      rewrite H4 in H8.
      apply in_app_or in H8.
      destruct H8.
      * apply in_app_or in H8.
        destruct H8.
        {
          assert (In y memory_trace').
          {
            rewrite H4.
            apply in_or_app.
            left.
            apply in_or_app.
            right.
            simpl; try tauto.
          }
          pose proof (memory_trace_is_read_or_write_in memory_trace' y H12 H0).
          destruct H13 as [address_y [value_y H13]].
          rewrite <- app_assoc in H5.
          pose proof (memory_trace_address_less_than_next l' l2 y x address_y value_y address value).
          rewrite <- H5 in H14.
          assert (y.(mem_ins) = read address_y value_y /\
          x.(mem_ins) = read address value \/
          y.(mem_ins) = read address_y value_y /\
          x.(mem_ins) = write address value \/
          y.(mem_ins) = write address_y value_y /\
          x.(mem_ins) = read address value \/
          y.(mem_ins) = write address_y value_y /\
          x.(mem_ins) = write address value). { tauto. }
          apply (H14 H) in H15.
          clear H14.
          pose proof (memory_trace_address_less_than_in l' l2 action' y address value' address_y value_y).
          rewrite <- app_assoc in H4.
          rewrite <- H4 in H14.
          assert (action'.(mem_ins) = read address value' /\
          y.(mem_ins) = read address_y value_y \/
          action'.(mem_ins) = read address value' /\
          y.(mem_ins) = write address_y value_y \/
          action'.(mem_ins) = write address value' /\
          y.(mem_ins) = read address_y value_y \/
          action'.(mem_ins) = write address value' /\
          y.(mem_ins) = write address_y value_y). { tauto. }
          specialize (H14 H8 H0 H16). clear H16.
          assert (address_y = address).
          {
            assert (Int256.unsigned address_y = Int256.unsigned address). { lia. }
            clear H15 H14.
            rewrite <- (Int256.repr_unsigned address_y).
            rewrite <- (Int256.repr_unsigned address).
            f_equal.
            tauto.
          }
          rewrite H16 in H13; clear H15 H14 H16.
          specialize (H11 y value_y H12 H13).
          pose proof (memory_trace_timestamp_less_than_in_front l' l2 y action' address value_y value').
          rewrite <- H4 in H14.
          assert (y.(mem_ins) = read address value_y /\
          action'.(mem_ins) = read address value' \/
          y.(mem_ins) = read address value_y /\
          action'.(mem_ins) = write address value' \/
          y.(mem_ins) = write address value_y /\
          action'.(mem_ins) = read address value' \/
          y.(mem_ins) = write address value_y /\
          action'.(mem_ins) = write address value'). { tauto. }
          specialize (H14 H0 H8 H15). clear H15.
          assert ( y <> action').
          {
            unfold not.
            intros.
            rewrite H15 in H14.
            lia.
          }
          apply H11 in H15.
          lia.
        }
        {
          simpl in H8; destruct H8; try tauto.
          rewrite <- H8 in H9.
          rewrite <- app_assoc in H5, H4.
          pose proof (memory_trace_read_value_eq l' l2 y x address value' value).
          assert (y.(mem_ins) = read address value' /\
          x.(mem_ins) = read address value \/
          y.(mem_ins) = write address value' /\
          x.(mem_ins) = read address value). { tauto. }
          rewrite <- H5 in H12.
          specialize (H12 H H13).
          assert (value' = value).
          {
            rewrite <- (Int256.repr_unsigned value').
            rewrite <- (Int256.repr_unsigned value).
            f_equal.
            tauto.
          }
          rewrite H14 in H10.
          tauto.
        }
      * pose proof (memory_trace_timestamp_less_than_in_behind (l' ++ [y]) l2 x action' address value value').
        rewrite <- H5 in H12.
        assert (x.(mem_ins) = read address value /\ action'.(mem_ins) = read address value' \/
        x.(mem_ins) = read address value /\ action'.(mem_ins) = write address value' \/
        x.(mem_ins) = write address value /\ action'.(mem_ins) = read address value' \/
        x.(mem_ins) = write address value /\ action'.(mem_ins) = write address value'). { tauto. }
        specialize (H12 H H8 H13); clear H13.
        pose proof (last_action_trace_timestamp_biggest (l ++ [x]) l x).
        assert (l ++ [x] = l ++ [x]). { reflexivity. }
        apply (H13 H14) in H3; clear H13 H14.
        inversion H1.
        apply (filter_preserves_Forall l (fun a : action_type =>
        a.(timestamp) < x.(timestamp)) mem_ins_type_is_not_non) in H3.
        apply (Permutation_Forall H13) in H3.
        rewrite H4 in H3.
        rewrite Forall_forall in H3.
        assert (In action' ((l' ++ [y]) ++ l2)).
        {
          apply in_or_app.
          right; tauto.
        }
        specialize (H3 action' H16).
        lia.
  - pose proof (memory_trace_fisrt_address_value_zero l1 l2 x address value).
    destruct H10; try tauto; try rewrite <- H5; try tauto.
    intros.
    assert (In action0 memory_trace').
    {
      rewrite H4.
      apply in_or_app.
      left; tauto.
    }
    apply (H8 action0 address0 value0 H12 H11).
Qed.

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
Proof.
  intros program CPU_trace rm_first_CPU_trace rm_last_CPU_trace first_CPU_state last_CPU_state action_trace memory_trace.
  revert program CPU_trace rm_first_CPU_trace rm_last_CPU_trace first_CPU_state last_CPU_state memory_trace.
  apply rev_ind with (l := action_trace).
  - intros. subst. inversion H. subst.
    inversion H0. subst.
    inversion H8. symmetry in H13, H14. subst. clear H8.
    (* CPU_trace should be a single value list; adjacent_CPU_state_for_action_trace has two constructors *)
    inversion H4. subst. inversion H8; subst.
    + symmetry in H1. apply app_eq_unit in H1. inversion H1. clear H1.
      { inversion H12. clear H12. subst. inversion H13. subst. clear H13.
        unfold combine_to_act_state_list. exists nil. simpl. (* mem_list = [] *)
        exists (fun _ => Int256.zero). exists (fun _ => Int256.zero). (* first_mem = last_mem = fun (n: int256) => Int256.zero *)
        destruct program.
        - inversion H2. subst. simpl in H1. inversion H1. contradiction. (* program = [] *)
        - intros.
          split.
          + tauto.
          + split.
            * apply sigma; try auto; try apply ActionListNil.
              unfold combine_to_pc_state, Build_pc_state, Build_program_state; simpl; exists 0; simpl.
              sets_unfold.
              tauto.
            * intros.
              assert (memory_trace = []).
              {
                inversion H5; subst.
                simpl in H1.
                apply Permutation_nil.
                tauto.
              }
              rewrite H1.
              apply not_in_memory_trace.
              simpl.
              intros.
              contradiction.
              tauto.
      }
      { inversion H12. discriminate. }
    + apply app_eq_nil in H13. inversion H13. discriminate.
  - intros. subst. inversion H0. subst. rewrite H2 in H0, H1, H3, H5, H8.
    assert (action_trace_constraint rm_last_CPU_trace l).
    {
      apply trace_action.
      inversion H5. subst.
      inversion H9.
      - symmetry in H12.
        apply app_eq_nil in H12.
        inversion H12.
        discriminate.
      - apply app_inj_tail in H10.
        destruct H10.
        apply app_inj_tail in H11.
        destruct H11.
        rewrite H10 in H13.
        rewrite H11 in H13.
        apply H13.
    }
    assert (CPU_trace_constraint rm_last_CPU_trace).
    {
      inversion H1. subst.
      rewrite <- H2 in H10.
      inversion H10.
      clear H10.
      rewrite <- H15 in H11.
      rewrite <- H15 in H12.
      clear rm_first_CPU_trace0 first_CPU_state0 H15 H16.
      inversion H13; subst.
      - symmetry in H14.
        apply app_eq_unit in H14.
        inversion H14.
        + inversion H10.
          apply action_CPU_trace_len_cons in H9.
          rewrite H15 in H9.
          discriminate.
        + inversion H10.
          discriminate.
      - assert (l0 ++ [x0; y]= (l0 ++ [x0]) ++ [y]). { rewrite <- app_assoc. tauto. }
        rewrite H16 in H10.
        apply app_inj_tail in H10.
        inversion H10.
        destruct rm_last_CPU_trace.
        + apply app_eq_nil in H17.
          inversion H17.
          discriminate.
        + rewrite H17 in H15.
          rewrite <- app_comm_cons in H2.
          inversion H2.
          rewrite <- H20.
          pose proof (trace_CPU (first_CPU_state :: rm_last_CPU_trace) rm_last_CPU_trace first_CPU_state).
          apply H19.
          tauto.
          tauto.
          tauto.
          rewrite <- H20 in H15.
          tauto.
    }
    assert (multiset_constraint rm_last_CPU_trace program).
    { 
      inversion H3.
      rewrite map_app in H11.
      apply Forall_app in H11.
      inversion H11.
      apply trace_multiset.
      tauto.
    }
    assert (action_trace_timestamp_constraint l).
    {
      inversion H4.
      - symmetry in H13.
        apply app_eq_nil in H13.
        inversion H13.
        discriminate.
      - symmetry in H12.
        apply app_eq_unit in H12.
        inversion H12.
        + inversion H14.
          rewrite H15.
          apply ActionListTraceNil.
        + inversion H14.
          discriminate.
      - apply app_inj_tail in H12.
        inversion H12.
        rewrite <- H15.
        apply H14.
    }
    assert (exists memory_trace', memory_trace_legal l memory_trace' /\
    (x.(mem_ins) <> non /\ (exists l1' l2', (memory_trace' = l1' ++ l2' /\ memory_trace = l1' ++ [x] ++ l2')) \/
    (x.(mem_ins) = non /\ memory_trace = memory_trace'))).
    {
      apply (exists_memory_trace' l memory_trace x); try tauto;
      apply (last_action_trace_timestamp_biggest (l ++ [x]) l x); tauto.
    }
    inversion H13 as [memory_trace' H14]. clear H13.
    destruct H14 as [H14 H_for_last_mem].
    assert (constraints program rm_last_CPU_trace l memory_trace').
    {
      apply all_constraints.
      apply H10.
      apply H11.
      apply H12.
      apply H9.
      inversion H14. subst.
      apply H13.
      inversion H14. subst.
      apply H15.
      apply public.
    }
    assert (exists (rm_first_CPU_trace'
    rm_last_CPU_trace' : list CPU_state)
    (first_CPU_state' last_CPU_state' : CPU_state),
    rm_last_CPU_trace = first_CPU_state' :: rm_first_CPU_trace' /\
    rm_last_CPU_trace = rm_last_CPU_trace' ++ [last_CPU_state']).
    {
      apply action_CPU_trace_len_cons in H9.
      destruct rm_last_CPU_trace.
      - discriminate.
      - exists rm_last_CPU_trace.
        specialize (cons_app_eq c rm_last_CPU_trace).
        intros.
        destruct H15. destruct H15.
        exists x1, c, x0.
        split.
        + tauto.
        + apply H15.
    }
    inversion H15 as [rm_first_CPU_trace' H16]. clear H15.
    inversion H16 as [rm_last_CPU_trace' H17]. clear H16.
    inversion H17 as [first_CPU_state' H18]. clear H17.
    inversion H18 as [last_CPU_state' H19]. clear H18.
    inversion H19 as [H20 H21]. clear H19.
    apply (H program rm_last_CPU_trace rm_first_CPU_trace' rm_last_CPU_trace'
    first_CPU_state' last_CPU_state' memory_trace') in H13; try tauto.
    inversion H13 as [mem_list' H15]. clear H13.
    inversion H15 as [first_mem' H13]. clear H15.
    inversion H13 as [last_mem' H15]. clear H13.
    exists (mem_list' ++ [last_mem']). exists first_mem'.
    assert (exists last_mem, last_mem = (fun address0 =>
      match x.(mem_ins) with
      | write address value => if (Int256.eq address address0) then value else (last_mem' address0)
      | _ => last_mem' address0
      end
    ) /\ (forall address : int256,
    last_mem_prop last_mem memory_trace
      address)).
    { 
      destruct H15; destruct H15.
      exists (fun address0 =>
        match x.(mem_ins) with
        | write address value => if (Int256.eq address address0) then value else (last_mem' address0)
        | _ => last_mem' address0
        end
      ).
      intros.
      inversion H14. clear H19 H22 action_trace0 memory_trace0.
      pose proof (last_action_trace_timestamp_biggest (l ++ [x]) l x).
      assert (Forall
      (fun a : action_type =>
       a.(timestamp) < x.(timestamp)) l).
      {
        assert (l ++ [x] = l ++ [x]). { tauto. }
        apply (H19 H22 H4).
      }
      clear H19.
      split; try tauto.
      intro.
      apply (construct_last_mem
      memory_trace memory_trace' l 
      x address last_mem' H7 H6 H18 H17 H22 H_for_last_mem).
      tauto.
    }
    destruct H13 as [last_mem H13]. 
    assert (eval_ins_list_single program
    (combine_to_pc_state last_CPU_state' last_mem')
    (combine_to_act_state_list [last_CPU_state']
      [last_mem'] 
      [x])
    (combine_to_pc_state last_CPU_state last_mem)).
    {
      rewrite H21 in H5.
      inversion H5.
      inversion H16.
      - symmetry in H23.
        apply app_eq_nil in H23.
        inversion H23.
        discriminate.
      - apply app_inj_tail in H19.
        inversion H19. clear H19.
        apply app_inj_tail in H25.
        inversion H25. clear H25.
        apply app_inj_tail in H22.
        inversion H22. clear H22.
        rewrite H27 in H23.
        rewrite H26 in H23.
        rewrite H28 in H23.
        destruct H15.
        destruct H22.
        inversion H1. clear H30 H31 H32 H34 CPU_trace0 rm_first_CPU_trace0 first_CPU_state0.
        rewrite H21 in H33.
        inversion H33.
        + symmetry in H31.
          apply app_eq_unit in H31.
          destruct H31.
          {
            destruct H30.
            apply app_eq_nil in H30.
            destruct H30.
            discriminate.
          }
          {
            destruct H30.
            discriminate.
          }
        + assert (l1 ++ [x1; y0] = (l1 ++ [x1]) ++ [y0]). { rewrite <- app_assoc; tauto. }
          rewrite H34 in H30.
          apply app_inj_tail in H30.
          destruct H30.
          apply app_inj_tail in H30.
          destruct H30.
          rewrite H36, H35 in H31.
          clear H32 H30 H36 H34 H35 H33 x1 y0 l1.
          clear H26 H19 H25 H28 H24 H27 H18 l0 x0 y action0 l_action H17 H16 action_trace0 CPU_trace action_trace0.
          inversion H23.
          {
            clear H24 H25 H26 state0 next_state action0.
            unfold eval_constraint in H31.
            rewrite H16 in H31.
            assert (MLOAD_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
            last_mem') (combine_to_act_state_list
            [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
            last_mem)).
            {
              inversion H31. clear H26 H27 x0 y.
              inversion H25. clear H27 H25 offset value0.
              assert (last_mem' address = value).
              {
                specialize (H29 address).
                destruct H_for_last_mem; destruct H25.
                - destruct H26 as [l1 [l2 H26]].
                  destruct H26 as [H_pre H_now].
                  inversion H14.
                  apply (additional_property_to_for_new_read address value x memory_trace memory_trace' l1 l2 l last_mem' H7 H27 H26 H6 H4 H_pre H_now H17 H29).
                - rewrite H25 in H17.
                  discriminate.
              }
              apply mload_sem with (offset := address) (l := remaining_stack); try tauto.
              {
                assert (((combine_to_pc_state last_CPU_state' last_mem').(state)).(memory) address = value).
                {
                  unfold combine_to_pc_state.
                  tauto.
                }
                rewrite H26.
                unfold combine_to_pc_state.
                tauto.
              }
              {
                simpl.
                destruct H13.
                rewrite H13.
                rewrite H17.
                reflexivity.
              }
              {
                simpl.
                rewrite H25.
                tauto.
              }
            }
            assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
            (seq 0 (Datatypes.length program)))).
            {
              inversion H11.
              clear H27 program0.
              rewrite Forall_forall in H25.
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
              (fun cpu_state : CPU_state =>
               (cpu_state.(inst), cpu_state.(pc)))
              rm_last_CPU_trace)).
              {
                rewrite H21.
                rewrite map_app.
                apply in_or_app.
                right.
                simpl.
                left.
                tauto.
              }
              apply (H25 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H27).
            }
            constructor.
            unfold fold_ins_sem.
            assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
            last_mem') (combine_to_act_state_list
            [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
            last_mem)).
            {
              unfold eval_ins.
              rewrite H16.
              tauto.
            }
            apply (in_property (ins * nat) 
            pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
            (combine program (seq 0 (Datatypes.length program)))
            eval_ins
            (combine_to_pc_state last_CPU_state' last_mem')
            (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
            (combine_to_pc_state last_CPU_state last_mem)
            ); tauto.
          }
          {
            clear H24 H25 H19 state0 next_state action0.
            unfold eval_constraint in H31.
            rewrite H16 in H31.
            assert (MSTORE_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
            last_mem') (combine_to_act_state_list
            [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
            last_mem)).
            {
              inversion H31. clear H25 H26 x0 y.
              rewrite H18 in H24.
              inversion H24.
              rewrite H28 in H18.
              clear H24 H26 H27 H28 offset value0.
              apply mstore_sem with (offset := address) (v := value); try tauto.
              destruct H13.
              rewrite H13.
              rewrite H17.
              simpl.
              unfold update_memory.
              apply functional_extensionality.
              intros address0.
              destruct (Int256.eq_dec address address0).
              - rewrite e. reflexivity.
              - pose proof n as n'.
                apply not_eq_sym in n'.
                apply Int256.eq_false in n.
                apply Int256.eq_false in n'.
                rewrite n, n'.
                reflexivity.
            }
            assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
            (seq 0 (Datatypes.length program)))).
            {
              inversion H11.
              clear H26 program0.
              rewrite Forall_forall in H24.
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
              (fun cpu_state : CPU_state =>
               (cpu_state.(inst), cpu_state.(pc)))
              rm_last_CPU_trace)).
              {
                rewrite H21.
                rewrite map_app.
                apply in_or_app.
                right.
                simpl.
                left.
                tauto.
              }
              apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
            }
            constructor.
            unfold fold_ins_sem.
            assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
            last_mem') (combine_to_act_state_list
            [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
            last_mem)).
            {
              unfold eval_ins.
              rewrite H16.
              tauto.
            }
            apply (in_property (ins * nat) 
            pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
            (combine program (seq 0 (Datatypes.length program)))
            eval_ins
            (combine_to_pc_state last_CPU_state' last_mem')
            (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
            (combine_to_pc_state last_CPU_state last_mem)
            ); tauto.
          }
          {
            clear H24 H25 H19 state0 next_state action0.
            unfold eval_constraint in H31.
            destruct last_CPU_state'.(inst) eqn: H_ins.
            - assert (JUMPI_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply jumpi_sem with (dest := dest) (cond := cond); try tauto.
                simpl.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - assert (JUMP_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply jump_sem with (v := v); try tauto.
                simpl.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - assert (POP_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply pop_sem with (v := v); try tauto.
                simpl.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - assert (ADD_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply add_sem with (v1 := v1) (v2 := v2) (l := l0); try simpl; try tauto.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - assert (MUL_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply mul_sem with (v1 := v1) (v2 := v2) (l := l0); try simpl; try tauto.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - assert (SUB_sem last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply sub_sem with (v1 := v1) (v2 := v2) (l := l0); try simpl; try tauto.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
            - congruence.
            - congruence.
            - assert (PUSH32_sem v last_CPU_state'.(pc) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                inversion H31.
                apply push32_sem; try simpl; try tauto.
                destruct H13.
                rewrite H13.
                rewrite H18.
                reflexivity.
              }
              assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine program
              (seq 0 (Datatypes.length program)))).
              {
                inversion H11.
                clear H26 program0.
                rewrite Forall_forall in H24.
                assert (In (last_CPU_state'.(inst), last_CPU_state'.(pc)) (map
                (fun cpu_state : CPU_state =>
                (cpu_state.(inst), cpu_state.(pc)))
                rm_last_CPU_trace)).
                {
                  rewrite H21.
                  rewrite map_app.
                  apply in_or_app.
                  right.
                  simpl.
                  left.
                  tauto.
                }
                apply (H24 (last_CPU_state'.(inst), last_CPU_state'.(pc)) H26).
              }
              constructor.
              unfold fold_ins_sem.
              assert (eval_ins (last_CPU_state'.(inst), last_CPU_state'.(pc)) (combine_to_pc_state last_CPU_state'
              last_mem') (combine_to_act_state_list
              [last_CPU_state'] [last_mem'] [x]) (combine_to_pc_state last_CPU_state
              last_mem)).
              {
                unfold eval_ins.
                rewrite H_ins.
                tauto.
              }
              apply (in_property (ins * nat) 
              pc_state (list act_state) pc_state (last_CPU_state'.(inst), last_CPU_state'.(pc))
              (combine program (seq 0 (Datatypes.length program)))
              eval_ins
              (combine_to_pc_state last_CPU_state' last_mem')
              (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x])
              (combine_to_pc_state last_CPU_state last_mem)
              ); tauto.
          }
    }
    destruct H15.
    destruct H17.
    exists last_mem.
    assert (first_CPU_state' = first_CPU_state).
    {
      rewrite H20 in H2. Search app.
      rewrite <- app_comm_cons in H2.
      inversion H2.
      tauto.
    }
    rewrite H19 in H17.
    inversion H17.
    split.
    {
      rewrite ! last_length.
      lia.
    }
    clear H19 H27 H28 H29 H30 l0 x0 y z.
    apply and_comm.
    split; try tauto.
    clear H18 H13.
    apply sigma; try auto.
    {
      clear H22 H23 H24 H26.
      inversion H4.
      - symmetry in H18; apply app_eq_nil in H18; inversion H18; discriminate.
      - symmetry in H13; apply app_eq_unit in H13.
        inversion H13.
        + inversion H19.
          apply length_zero_iff_nil in H22.
          rewrite H22 in H15.
          apply action_CPU_trace_len_cons in H9.
          rewrite H22 in H9.
          apply length_one_iff_single in H9.
          inversion H9.
          rewrite H24.
          apply length_zero_iff_nil in H15.
          rewrite H15.
          simpl.
          apply ActionListSingle.
          simpl.
          apply H18.
        + inversion H19.
          discriminate.
      - rewrite H21.
        apply app_inj_tail in H13.
        inversion H13.
        rewrite <- H22 in H25.
        apply action_CPU_trace_len_cons in H9.
        rewrite H21 in H9.
        rewrite last_length in H9.
        apply eq_add_S in H9.
        rewrite <- H22 in H9.
        destruct rm_last_CPU_trace'.
        + simpl in H9.
          symmetry in H9.
          apply length_zero_iff_nil in H9.
          apply app_eq_nil in H9.
          inversion H9.
          discriminate.
        + destruct mem_list'.
          * rewrite <- H22 in H15.
            symmetry in H15.
            simpl in H15.
            apply length_zero_iff_nil in H15.
            apply app_eq_nil in H15.
            inversion H15.
            discriminate.
          * specialize (cons_app_eq c rm_last_CPU_trace').
            intros. destruct H24. destruct H24.
            specialize (cons_app_eq i mem_list').
            intros. destruct H26. destruct H26.
            rewrite H24, H26 in H25.
            rewrite H24, H26.
            assert (Datatypes.length (x2 ++ [x1]) =
                Datatypes.length (x4 ++ [x3])).
            {
              rewrite H22 in H9.
              rewrite <- H9 in H15.
              rewrite <- H24. rewrite <- H26.
              rewrite H15.
              tauto.
            }
            assert (Datatypes.length
            (combine (x2 ++ [x1]) (x4 ++ [x3])) =
            Datatypes.length (l0 ++ [x0])).
            {
              apply len_combine in H27.
              rewrite <- H27.
              rewrite <- H26.
              rewrite H22.
              apply H15.
            }
            assert (Datatypes.length
            (combine [last_CPU_state'] [last_mem']) =
            Datatypes.length [y]).
            {
              assert (length [last_CPU_state'] = length [last_mem']).
              { tauto. }
              apply len_combine in H29.
              rewrite <- H29.
              tauto.
            }
            assert (Datatypes.length x2 = Datatypes.length x4).
            {
              rewrite ! app_length in H27.
              simpl in H27.
              lia.
            }
            assert (Datatypes.length [x1] = Datatypes.length [x3]).
            {
              tauto.
            }
            assert (Datatypes.length (combine x2 x4) =
            Datatypes.length l0).
            {
              rewrite combine_app in H28; try tauto.
              rewrite ! app_length in H28.
              apply len_combine in H31.
              rewrite <- H31 in H28.
              simpl in H28.
              lia.
            }
            assert (Datatypes.length (combine [x1] [x3]) =
            Datatypes.length [x3]).
            {
              apply len_combine in H31.
              rewrite <- H31.
              tauto.
            }
            unfold combine_to_act_state_list.
            rewrite combine_app; try tauto.
            rewrite combine_app; try tauto.
            rewrite map_app; try tauto.
            rewrite combine_app; try tauto.
            rewrite combine_app; try tauto.
            rewrite map_app.
            apply ActionListCons; try tauto.
            rewrite <- H22 in H17.
            rewrite H24 in H17.
            rewrite H26 in H17.
            unfold combine_to_act_state_list in H17.
            rewrite combine_app in H17; try tauto.
            rewrite combine_app in H17; try tauto.
            rewrite map_app in H17.
            simpl in H17.
            inversion H17. subst.
            apply H37.
      (* Increasing_timestamp *)
    }
    {
      clear H22 H23 H24 H25.
      (* eval_ins_list_single *)
      rewrite H21.
      pose proof (rt_trans_n1 (eval_ins_list_single program)).
      assert ((combine_to_pc_state first_CPU_state first_mem',
      combine_to_act_state_list (rm_last_CPU_trace' ++ [last_CPU_state'])
      (mem_list' ++ [last_mem']) (l ++ [x]),
      combine_to_pc_state last_CPU_state last_mem)
      ∈ clos_refl_trans (eval_ins_list_single program)
      ∘ eval_ins_list_single program).
      {
        simpl.
        exists (combine_to_pc_state last_CPU_state' last_mem').
        exists (combine_to_act_state_list rm_last_CPU_trace' mem_list' l).
        exists (combine_to_act_state_list [last_CPU_state'] [last_mem'] [x]).
        split.
        - assert (combine_to_act_state_list rm_last_CPU_trace' mem_list' l ++
          combine_to_act_state_list [last_CPU_state'] [last_mem'] [x] =
          combine_to_act_state_list (rm_last_CPU_trace' ++ [last_CPU_state'])
          (mem_list' ++ [last_mem']) (l ++ [x])).
          {
            unfold combine_to_act_state_list.
            unfold combine_to_act_state.
            rewrite <- map_app.
            assert (combine (combine rm_last_CPU_trace' mem_list') l ++
            combine (combine [last_CPU_state'] [last_mem']) [x] =
            combine (combine (rm_last_CPU_trace' ++ [last_CPU_state']) (mem_list' ++ [last_mem'])) (l ++ [x])).
            {
              (* combine property, correct only when
              rm_last_CPU_trace, mem_list and action_trace have the same length,
              which need a lemma to prove it *)
              assert (length rm_last_CPU_trace' = length mem_list').
              { 
                assert (length rm_last_CPU_trace' = length l).
                {
                  assert (length rm_last_CPU_trace = S (length l)).
                  {
                    apply action_CPU_trace_len_cons.
                    apply H9.
                  }
                  rewrite H21 in H18.
                  simpl in H18.
                  rewrite last_length in H18.
                  injection H18.
                  intros. apply H19.
                }
                rewrite H15.  apply H18.
              }
              rewrite ! combine_app; try tauto.
              apply len_combine in H18.
              rewrite <- H18.
              tauto.
            }
            rewrite H18.
            reflexivity.
          }
          apply H18.
        - split.
          + simpl.
            inversion H17. apply H24.
          + apply H16.
      }
      apply H13 in H18. apply H18.
    }
Qed.

End Definition_and_soundness.
