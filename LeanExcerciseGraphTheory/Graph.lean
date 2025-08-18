import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs

universe u
class Graph' (V : Type u) where
  adj : V → V → Prop

class SimpleGraph (V : Type u) extends Graph' V where
  symm : ∀ a : V, ∀ b : V, adj a b = adj b a
  noLoop : ∀ a : V, ¬ adj a a

def example_vertecies : Finset Nat := {1, 2, 3, 4}
def example_adj : {x // x ∈ example_vertecies} → {x // x ∈ example_vertecies} → Prop
  | ⟨1, _⟩, ⟨2, _⟩ => True
  | ⟨2, _⟩, ⟨1, _⟩ => True
  | _, _ => False

lemma example_adj_symm :
    ∀ (a b : {x // x ∈ example_vertecies}), example_adj a b = example_adj b a := by
  intro a b
  -- a と b を分解
  obtain ⟨av, ah⟩ := a
  obtain ⟨bv, bh⟩ := b
  simp only [example_adj]
  -- 具体的な値での証明
  simp only [example_vertecies] at ah bh
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ah bh
  -- すべてのケースを網羅
  rcases ah with (rfl | rfl | rfl | rfl) <;>
  rcases bh with (rfl | rfl | rfl | rfl) <;>
  rfl

lemma example_no_loop :
    ∀ a : {x // x ∈ example_vertecies}, ¬ example_adj a a := by
  intro a
  obtain ⟨av, ah⟩ := a
  simp only [example_adj]
  -- 具体的な値での証明
  simp only [example_vertecies] at ah
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ah
  -- 各ケースを確認
  rcases ah with (rfl | rfl | rfl | rfl) <;> decide

def example_simple_graph : SimpleGraph (example_vertecies) :=
  { adj := example_adj,
    symm := example_adj_symm,
    noLoop := example_no_loop
  }
