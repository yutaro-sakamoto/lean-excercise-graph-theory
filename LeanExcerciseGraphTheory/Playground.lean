import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Data.Nat.Defs

open Nat

variable (P Q R : Prop)

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR
  rcases h with (hP | hQ)
  · apply hPR hP
  · apply hQR hQ

example : P ∧ Q → Q ∧ P := by
  intro h
  rcases h with ⟨hP, hQ⟩
  exact ⟨hQ, hP⟩

inductive Sample where
  | foo (x y : Nat)
  | bar (z : String)

example (s : Sample) : True := by
  rcases s with ⟨x, y⟩ | ⟨z⟩
  case foo =>
    guard_hyp x : Nat
    guard_hyp y : Nat
    trivial
  case bar =>
    guard_hyp z : String
    trivial

lemma comm_add_z_mod (n : Nat) (a b : ZMod n) : a + b = b + a := by
  -- ZMod n の加法の交換法則をスクラッチから証明
  by_cases h : n = 0
  · -- n = 0 の場合、ZMod 0 は Int と同型
    subst h
    -- Int の加法の交換法則を使用
    exact Int.add_comm a b
  · -- n ≠ 0 の場合
    have n_not_zero : NeZero n := ⟨h⟩
    have eq : (a + b).val = (b + a).val := by
      simp +arith [ZMod.val_add]
    exact ZMod.val_injective n eq

#check Nat.casesOn
#check @Add.add (Fin 1)
#check ZMod.val_injective

structure MyZMod (n : ℕ) where
  val : ℕ
  h : val < n

def myZModAdd {n : ℕ} (h : n > 0) (a b : MyZMod n) : MyZMod n :=
  ⟨(a.val + b.val) % n, Nat.mod_lt (a.val + b.val) h⟩

def squareGraph : SimpleGraph (Fin 4) where
  Adj := fun i j =>
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨  -- 0-1 辺
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨  -- 1-2 辺
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨  -- 2-3 辺
    (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3)    -- 3-0 辺
  loopless := by
    -- 自己ループがないことを証明
    intro i
    fin_cases i <;> simp

#check SimpleGraph.loopless

variable (n : Nat)
variable (t : Nat)
variable (h₁ : n > 1)
variable (h₂ : t > 0)
variable (h₃ : t < n)

def all_vertices : Finset (Nat × ZMod n) := by
  exact (Finset.range n).image (fun i : Nat => ((0 : Nat), (i : ZMod n))) ∪
        (Finset.range n).image (fun i : Nat => ((1 : Nat), (i : ZMod n))) ∪
        (Finset.range n).image (fun i : Nat => ((2 : Nat), (i : ZMod n))) ∪
        (Finset.range n).image (fun i : Nat => ((3 : Nat), (i : ZMod n)))

def vertices := {x // x ∈ all_vertices n}

lemma absurd_one_eq_zero (nGt1 : n > 1) : ((1 : ZMod n) ≠ (0 : ZMod n))  := by
  intro h_eq
  -- n > 1 から Fact (1 < n) を提供
  haveI : Fact (1 < n) := ⟨nGt1⟩
  -- ZMod.val で矛盾を導く
  have h_val_eq : (1 : ZMod n).val = (0 : ZMod n).val := by
    rw [h_eq]
  simp +arith at h_val_eq

#check absurd_one_eq_zero
def vertex_x (w : Nat) : Bool := w = 0
def vertex_u (w : Nat) : Bool := w = 1
def vertex_v (w : Nat) : Bool := w = 2
def vertex_y (w : Nat) : Bool := w = 3

def dgpg (nGt1 : n > 1) : SimpleGraph (vertices n) where
  Adj := fun v₁ v₂ =>
    let (w₁, i) := v₁.val
    let (w₂, j) := v₂.val
    if w₁ = 0 ∧  w₂ = 0 then
      j = i + 1 ∨ i = j + 1
    else if (w₁ = 0 ∧ w₂ = 1) ∨ (w₁ = 1 ∧ w₂ = 0) then
      i = j
    else
      False
  --symm := by
  --  intro v₁ v₂ h
  --  by_cases h' : v₁.val.1 = 0 ∧ v₂.val.1 = 0
  --  · simp [*] at *
  --    apply Or.symm h
  --  · simp [*] at *

  loopless := by
    let oneNeqZero : (1 : ZMod n) ≠ (0 : ZMod n) := absurd_one_eq_zero n nGt1
    intro vertex
    let (w, i) := vertex.val
    by_cases h : w = 0 <;> {
      simp [*]
      intro h'
      simp [*]
    }
