import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Set.Finite.Basic
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

def example_graph (nGt1 : n > 1) : SimpleGraph (vertices n) where
  Adj := fun v₁ v₂ =>
    let (w₁, i) := v₁.val
    let (w₂, j) := v₂.val
    if w₁ = 0 ∧  w₂ = 0 then
      j = i + 1 ∨ i = j + 1
    else if (w₁ = 0 ∧ w₂ = 1) ∨ (w₁ = 1 ∧ w₂ = 0) then
      i = j
    else
      False

  symm := by
    intro v₁ v₂ h
    by_cases h' : v₁.val.1 = 0 ∧ v₂.val.1 = 0
    · simp [*] at *
      apply Or.symm h
    · simp [*] at *
      by_cases h'' : (v₂.val.1 = 0 ∧ v₁.val.1 = 0)
      · simp [*] at *
      · simp [*] at *
        cases h.left with
        | inl h_left =>
          apply Or.inr
          exact ⟨h_left.right, h_left.left⟩
        | inr h_right =>
          apply Or.inl
          exact ⟨h_right.right, h_right.left⟩

  loopless := by
    let oneNeqZero : (1 : ZMod n) ≠ (0 : ZMod n) := absurd_one_eq_zero n nGt1
    intro vertex
    let (w, i) := vertex.val
    by_cases h : w = 0 <;> {
      simp [*]
      intro h'
      simp [*]
    }

universe univ_u
def List.toSet {α : Type univ_u} :  List α → Set α
  | []    => ∅
  | a::as => {a} ∪ as.toSet

def n_neq_zero : n ≠ 0 := by
  intro h
  rw [h] at h₁
  contradiction

def xx (i : ZMod n) : vertices n := by
  -- (0, i) が all_vertices に含まれることを示す
  use (0, i)
  simp [all_vertices]
  -- ∃ a < n, ↑a = i を証明
  have n_ne_zero : n ≠ 0 := n_neq_zero n h₁
  have : NeZero n := ⟨n_ne_zero⟩
  use i.val, i.val_lt
  simp

def yy (i : ZMod n) : vertices n := by
  -- (1, i) が all_vertices に含まれることを示す
  use (1, i)
  simp [all_vertices]
  -- ∃ a < n, ↑a = i を証明
  have n_ne_zero : n ≠ 0 := n_neq_zero n h₁
  have : NeZero n := ⟨n_ne_zero⟩
  use i.val, i.val_lt
  simp

def uu (i : ZMod n) : vertices n := by
  -- (2, i) が all_vertices に含まれることを示す
  use (2, i)
  simp [all_vertices]
  -- ∃ a < n, ↑a = i を証明
  have n_ne_zero : n ≠ 0 := n_neq_zero n h₁
  have : NeZero n := ⟨n_ne_zero⟩
  use i.val, i.val_lt
  simp

def vv (i : ZMod n) : vertices n := by
  -- (3, i) が all_vertices に含まれることを示す
  use (3, i)
  simp [all_vertices]
  -- ∃ a < n, ↑a = i を証明
  have n_ne_zero : n ≠ 0 := n_neq_zero n h₁
  have : NeZero n := ⟨n_ne_zero⟩
  use i.val, i.val_lt
  simp

-- 局所的な記法を使って関数呼び出しを簡潔にする
local notation "x" => xx n h₁
local notation "y" => yy n h₁
local notation "u" => uu n h₁
local notation "v" => vv n h₁

def dgpg : SimpleGraph (vertices n) :=
  SimpleGraph.fromEdgeSet <| List.toSet <|
    ((List.range n).map fun m => Sym2.mk (x ↑m, x ↑(m + 1))) ++
    ((List.range n).map fun m => Sym2.mk (y ↑m, y ↑(m + 1))) ++
    ((List.range n).map fun m => Sym2.mk (u ↑m, v ↑(m + t))) ++
    ((List.range n).map fun m => Sym2.mk (v ↑m, u ↑(m + t))) ++
    ((List.range n).map fun m => Sym2.mk (x ↑m, u ↑m)) ++
    ((List.range n).map fun m => Sym2.mk (y ↑m, v ↑m))

-- vertices n は Nat × ZMod n のサブタイプなので、推論で決定可能
instance : DecidableEq (vertices n) := Subtype.instDecidableEq
-- Finsetのサブタイプに対するFintypeインスタンス
noncomputable instance : Fintype (vertices n) := by
  exact (all_vertices n).finite_toSet.fintype

--Hamiltonian サイクルに関する定理（コメントアウト）
theorem dgpg_is_hamiltonian (nGt1 : n > 1) (tGt0 : t > 0) (tLtN : t < n) :
  SimpleGraph.IsHamiltonian (dgpg n t nGt1) := by
  -- Hamiltonian cycle の構成と証明をここに記述
  sorry
