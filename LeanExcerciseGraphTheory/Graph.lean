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

def list_to_graph : {V : Type u} → List (V × V) → SimpleGraph V := sorry

def example_adj2 : Nat → Nat → Prop
  | 1, 2 => True
  | 2, 1 => True
  | 1, 3 => True
  | 3, 1 => True
  | _, _ => False

lemma example_adj_symm2_3 : ∀ a, ∀ b : Nat, example_adj2 a b = example_adj2 b a := by
  intro a b
  by_cases h1 : a = 1
  · subst h1
    by_cases h2 : b = 2
    · subst h2
      simp [example_adj2]
    · by_cases h3 : b = 3
      · subst h3
        simp [example_adj2]
      · simp [example_adj2, h2, h3]
  · by_cases h2 : a = 2
    · subst h2
      by_cases h3 : b = 1
      · subst h3
        simp [example_adj2]
      · simp [example_adj2, h3]
    · by_cases h3 : a = 3
      · subst h3
        by_cases h4 : b = 1
        subst h4
        · simp [example_adj2]
        simp [example_adj2, h4]
      · simp [example_adj2, h1, h2, h3]

lemma example_adj_symm2_2 : ∀ a, ∀ b : Nat, example_adj2 a b = example_adj2 b a := by
  intro a b
  -- 最もシンプルな方法：重要なケースだけ場合分け
  by_cases h1 : a = 1
  · subst h1
    by_cases h2 : b = 2
    · subst h2; simp [example_adj2]  -- 1,2 = 2,1
    · by_cases h3 : b = 3
      · subst h3; simp [example_adj2]  -- 1,3 = 3,1
      · simp [example_adj2, h2, h3]  -- その他は False = False
  · by_cases h2 : a = 2
    · subst h2
      by_cases h3 : b = 1
      · subst h3; simp [example_adj2]  -- 2,1 = 1,2
      · simp [example_adj2, h3]  -- その他は False = False
    · by_cases h3 : a = 3
      · subst h3
        by_cases h4 : b = 1
        · subst h4; simp [example_adj2]  -- 3,1 = 1,3
        · simp [example_adj2, h4]  -- その他は False = False
      · simp [example_adj2, h1, h2, h3]  -- a ≠ 1,2,3 なら常に False = False

lemma example_adj_symm2 : ∀ a, ∀ b : Nat, example_adj2 a b = example_adj2 b a := by
  intro a b
  -- 重要なケースのみ具体的に証明
  cases a with
  | zero =>
    cases b with
    | zero => simp [example_adj2]
    | succ _ => simp [example_adj2]
  | succ a' =>
    cases a' with
    | zero => -- a = 1
      cases b with
      | zero => simp [example_adj2]
      | succ b' =>
        cases b' with
        | zero => simp [example_adj2]  -- 1, 1
        | succ b'' =>
          cases b'' with
          | zero => simp [example_adj2]  -- 1, 2: True = True
          | succ b''' =>
            cases b''' with
            | zero => simp [example_adj2]  -- 1, 3: True = True
            | succ _ => simp [example_adj2]  -- 1, n≥4: False = False
    | succ a'' =>
      cases a'' with
      | zero => -- a = 2
        cases b with
        | zero => simp [example_adj2]
        | succ b' =>
          cases b' with
          | zero => simp [example_adj2]  -- 2, 1: True = True
          | succ _ => simp [example_adj2]  -- 2, n≥2: False = False
      | succ a''' =>
        cases a''' with
        | zero => -- a = 3
          cases b with
          | zero => simp [example_adj2]
          | succ b' =>
            cases b' with
            | zero => simp [example_adj2]
            | succ _ => simp [example_adj2]
        | succ _ =>
          cases b with
          | zero => simp [example_adj2]
          | succ _ =>
            simp [example_adj2]

lemma example_adj_symm2_4 : ∀ a, ∀ b : Nat, example_adj2 a b = example_adj2 b a := by
  intro a b
  by_cases a_eq_1 : a = 1
  · subst a_eq_1
    by_cases b_eq_2 : b = 2; · subst b_eq_2; simp [example_adj2, *]
    by_cases b_eq_3 : b = 3; · subst b_eq_3; simp [example_adj2, *]
    simp [example_adj2, *]
  by_cases a_eq_2 : a = 2
  · subst a_eq_2
    by_cases b_eq_1 : b = 1; · subst b_eq_1; simp [example_adj2, *]
    by_cases b_eq_3 : b = 3; · subst b_eq_3; simp [example_adj2, *]
    simp [example_adj2, *]
  by_cases a_eq_3 : a = 3
  · subst a_eq_3
    by_cases b_eq_1 : b = 1; · subst b_eq_1; simp [example_adj2, *]
    by_cases b_eq_2 : b = 2; · subst b_eq_2; simp [example_adj2, *]
    simp [example_adj2, *]
  simp [example_adj2, *]

def list_to_adj {V : Type u} [DecidableEq V] (lst : List (V × V)) : (V → V → Prop) :=
  match lst with
  | [] => fun _ _ => False
  | (x, y)::xs => fun a b =>
    if (x = a ∧ y = b) ∨ (x = b ∧ y = a)
      then True
      else list_to_adj xs a b

--lemma list_to_adj_symm {V : Type u} [DecidableEq V] (lst : List (V × V))
--    : ∀ a, ∀ b : V, list_to_adj lst a b = list_to_adj lst b a :=
--  fun a =>
--  fun b =>
--    match lst with
--    | [] => by simp [list_to_adj]
--    | x::xs => sorry

lemma list_to_adj_symm2 {V : Type u} [DecidableEq V] (lst : List (V × V))
    : ∀ a, ∀ b : V, list_to_adj lst a b = list_to_adj lst b a := by
  intro a b
  induction lst with
  | nil => simp [list_to_adj]
  | cons x xs ih =>
    simp [list_to_adj, ih]
    apply Iff.intro <;>
    · intro h _ _
      apply h <;> assumption

lemma list_to_adj_symm {V : Type u} [DecidableEq V] (lst : List (V × V))
    : ∀ a, ∀ b : V, list_to_adj lst a b = list_to_adj lst b a := by
  intro a b
  induction lst with
  | nil => simp [list_to_adj]
  | cons x xs ih =>
    simp only [list_to_adj]
    -- 条件式の対称性を利用
    have h_symm : (x.1 = a ∧ x.2 = b) ∨ (x.1 = b ∧ x.2 = a) ↔
                  (x.1 = b ∧ x.2 = a) ∨ (x.1 = a ∧ x.2 = b) := by
      constructor
      · intro h
        cases h with
        | inl h => exact Or.inr h
        | inr h => exact Or.inl h
      · intro h
        cases h with
        | inl h => exact Or.inr h
        | inr h => exact Or.inl h
    by_cases h : (x.1 = a ∧ x.2 = b) ∨ (x.1 = b ∧ x.2 = a)
    · rw [if_pos h, if_pos (h_symm.mp h)]
    · rw [if_neg h, if_neg (h_symm.not.mp h)]
      exact ih

def filter_loop_pairs {V : Type u} [DecidableEq V] (lst : List (V × V)) : List (V × V) :=
  match lst with
  | [] => []
  | (x, y) :: xs =>
    if x = y
      then filter_loop_pairs xs
      else (x, y) :: filter_loop_pairs xs

theorem filter_loop_pairs_no_loop {V : Type u} [DecidableEq V] (lst : List (V × V)) :
  ∀ a : V, ¬ list_to_adj (filter_loop_pairs lst) a a := by
  intro x
  induction lst with
  | nil => simp [filter_loop_pairs, list_to_adj]
  | cons y ys ih =>
    simp [filter_loop_pairs]
    by_cases h : y.1 = y.2
    · simp [h]
      assumption
    · simp [h, list_to_adj]
      apply And.intro
      · intro g
        simp [Eq.symm g]
        intro s
        exact absurd (Eq.symm s) h
      assumption

def simple_graph_from_list {V : Type u} [DecidableEq V] (lst : List (V × V))
    : SimpleGraph V :=
  {
    adj := list_to_adj (filter_loop_pairs lst),
    symm := list_to_adj_symm2 (filter_loop_pairs lst),
    noLoop := filter_loop_pairs_no_loop lst
  }

def sample_simple_graph : SimpleGraph Nat := simple_graph_from_list [(1, 2), (1, 3), (2, 4)]

def vertices_3 : Finset Nat := {1, 2, 3}
def set_vertices_3 := {x // x ∈ vertices_3}

-- より直接的な方法で DecidableEq インスタンスを定義
instance : DecidableEq set_vertices_3 := fun a b =>
  if h : a.val = b.val then
    isTrue (Subtype.ext h)
  else
    isFalse (fun heq => h (congrArg Subtype.val heq))

-- 方法2: サブタイプを使用して vertices_3 の要素として定義
def sample_complete_graph : SimpleGraph set_vertices_3 :=
  simple_graph_from_list [
    (⟨1, by simp [vertices_3]⟩, ⟨2, by simp [vertices_3]⟩),
    (⟨1, by simp [vertices_3]⟩, ⟨3, by simp [vertices_3]⟩),
    (⟨2, by simp [vertices_3]⟩, ⟨3, by simp [vertices_3]⟩)
  ]
