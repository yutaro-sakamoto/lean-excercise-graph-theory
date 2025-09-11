import Mathlib.Data.ZMod.Basic
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
