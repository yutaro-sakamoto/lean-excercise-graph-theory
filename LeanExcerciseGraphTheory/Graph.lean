universe u
class Graph' (V : Type u) where
  adj : V → V → Prop

class SimpleGraph (V : Type u) extends Graph' V where
  symm : ∀ a : V, ∀ b : V, adj a b = adj b a
  noLoop : ∀ a : V, ¬ adj a a
