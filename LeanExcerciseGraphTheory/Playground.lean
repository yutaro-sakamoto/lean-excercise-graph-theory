variable (P Q R : Prop)

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR
  rcases h with (hP | hQ)
  . apply hPR hP
  . apply hQR hQ

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
