Require Import SetsClass.SetsClass.
Import SetsNotation.

Local Open Scope sets.

Module SetTest0a.

Goal forall (A: Type) (X Y: A -> Prop) (P: Prop),
  X ∩ Y == Y ∩ Sets.prop_inj P.
Proof.
  idtac "Set Test 0a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall a : A, X a /\ Y a <-> Y a /\ P => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest0a.

Module SetTest0b.

Goal forall (A: Type) (X Y: A -> Prop) (P: Prop),
  X ∩ Y == Y ∩ Sets.prop_inj P.
Proof.
  idtac "Set Test 0b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall a : A, a ∈ X /\ a ∈ Y <-> a ∈ Y /\ P => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest0b.

Module SetTest0c.

Goal forall (A: Type) (X Y: A -> Prop) (P: Prop),
  X ∩ Y == Y ∩ Sets.prop_inj P.
Proof.
  idtac "Set Test 0c.".
  intros.
  Sets_unfold.
  sets_unfold.
  match goal with
  | |- forall a : A, X a /\ Y a <-> Y a /\ P => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest0c.

Module SetTest1a.

Goal forall (A B: Type) (X Y: A -> B -> Prop),
  X ∪ Y == Y ∪ X ∪ Y.
Proof.
  idtac "Set Test 1a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall a b, X a b \/ Y a b <->
                   (Y a b \/ X a b) \/ Y a b => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest1a.

Module SetTest1b.

Goal forall (A B: Type) (X Y: A -> B -> Prop),
  X ∪ Y == Y ∪ X ∪ Y.
Proof.
  idtac "Set Test 1b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall (a : A) (a0 : B),
          (a, a0) ∈ X \/ (a, a0) ∈ Y <->
          ((a, a0) ∈ Y \/ (a, a0) ∈ X) \/ (a, a0) ∈ Y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest1b.

Module SetTest2a.

Goal forall (A: Type) (X: nat * bool -> A -> Prop) (Y: A -> Prop),
  ∅ ∪ ⋃ X ⊆ Y ∪ ∅.
Proof.
  idtac "Set Test 2a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall a : A, False \/ (exists i : nat * bool, X i a) -> Y a \/ False => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest2a.

Module SetTest2b.

Goal forall (A: Type) (X: nat * bool -> A -> Prop) (Y: A -> Prop),
  ∅ ∪ ⋃ X ⊆ Y ∪ ∅.
Proof.
  idtac "Set Test 2b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall a : A, False \/ (exists i : nat * bool, a ∈ X i) -> a ∈ Y \/ False => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest2b.

Module SetTest3a.

Goal forall (A: Type) (X: A -> A -> Prop) (Y: A -> Prop),
  ⋂ X ⊆ Y ∪ Sets.full.
Proof.
  idtac "Set Test 3a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall a : A, (forall i : A, X i a) -> Y a \/ True => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest3a.

Module SetTest3b.

Goal forall (A: Type) (X: A -> A -> Prop) (Y: A -> Prop),
  ⋂ X ⊆ Y ∪ Sets.full.
Proof.
  idtac "Set Test 3b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall a : A, (forall i : A, a ∈ X i) -> a ∈ Y \/ True => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest3b.

Module SetTest4a.

Goal forall (A: Type) (X: nat -> A -> Prop) (Y: (A -> Prop) -> Prop),
  Sets.omega_union X == Sets.general_union Y.
Proof.
  idtac "Set Test 4a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall a : A, (exists i : nat, X i a) <-> (exists x : A -> Prop, Y x /\ x a) => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest4a.

Module SetTest4b.

Goal forall (A: Type) (X: nat -> A -> Prop) (Y: (A -> Prop) -> Prop),
  Sets.omega_union X == Sets.general_union Y.
Proof.
  idtac "Set Test 4b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall a : A, (exists i : nat, a ∈ X i) <-> (exists x : A -> Prop, Y x /\ a ∈ x) => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest4b.

Module SetTest5a.

Goal forall (A B: Type) (X: nat -> A -> B -> Prop) (Y: (A -> B -> Prop) -> Prop),
  Sets.omega_intersect X == Sets.general_intersect Y.
Proof.
  idtac "Set Test 5a.".
  intros.
  sets_unfold.
  match goal with
  | |- forall (a : A) (b: B),
      (forall i : nat, X i a b) <->
      (forall x : A -> B -> Prop, Y x -> x a b) => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest5a.

Module SetTest5b.

Goal forall (A B: Type) (X: nat -> A -> B -> Prop) (Y: (A -> B -> Prop) -> Prop),
  Sets.omega_intersect X == Sets.general_intersect Y.
Proof.
  idtac "Set Test 5b.".
  intros.
  Sets_unfold.
  match goal with
  | |- forall (a : A) (b: B),
      (forall i : nat, (a, b) ∈ X i) <->
      (forall x : A -> B -> Prop, Y x -> (a, b) ∈ x) => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest5b.

Module SetTest6.

Goal forall (X: nat -> nat -> Prop) (n m: nat),
  (n, m) ∈ X ->
  (n, m) ∈ X.
Proof.
  idtac "Set Test 6.".
  intros.
  sets_unfold.
  sets_unfold in H.
  match goal with
  | H: X n m  |- X n m => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End SetTest6.

Module RelTest0.

Goal forall (A: Type) (X: A -> A -> Prop) (x y: A),
  Rels.concat X X x y: Prop.
Proof.
  idtac "Rel Test 0.".
  intros.
  unfold_RELS_tac.
  match goal with
  | |- exists x' : A, X x x' /\ X x' y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest0.

Module RelTest1.

Goal forall (A: Type) (X: A -> Prop) (x y: A),
  Rels.test X x y: Prop.
Proof.
  idtac "Rel Test 1.".
  intros.
  unfold_RELS_tac.
  match goal with
  | |- X x /\ x = y => idtac "  Pass."
  | _ => idtac "  Fail."
  end.
Abort.

End RelTest1.

Goal forall (A: Type) (X Y: A -> A -> Prop),
  X ⊆ Y ∪ X.    
Proof.
  intros.
  sets_unfold.
  intros.
  right.
  exact H.
Qed.

Print Unnamed_thm.
