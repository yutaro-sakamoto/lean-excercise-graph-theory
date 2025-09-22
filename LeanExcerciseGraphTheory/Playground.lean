import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum
import Init.Data.List.Basic

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
variable (nGt1 : n > 1)
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


-- ===============================================
-- 頂点数3の完全グラフのサイクル存在証明
-- ===============================================

-- 頂点数3の完全グラフの定義（全ての頂点間に辺がある）

-- 3つの頂点を明示的に定義
def v0 : Fin 3 := 0  -- 頂点 0
def v1 : Fin 3 := 1  -- 頂点 1
def v2 : Fin 3 := 2  -- 頂点 2

-- 不等性の補助lemma（完全グラフの隣接性に必要）
lemma v0_ne_v1 : v0 ≠ v1 := by simp [v0, v1]
lemma v1_ne_v2 : v1 ≠ v2 := by simp [v1, v2]
lemma v2_ne_v0 : v2 ≠ v0 := by simp [v2, v0]

def complete_graph_3 : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet <|
  { Sym2.mk (v0, v1), Sym2.mk (v1, v2), Sym2.mk (v2, v0) }

-- メイン定理：頂点数3の完全グラフには長さ3のサイクルが存在する
theorem complete_graph_3_triangle_cycle :
  ∃ (p : SimpleGraph.Walk complete_graph_3 v0 v0), p.length = 3 := by
  -- 完全グラフでは任意の異なる頂点間に辺がある
  have h01 : complete_graph_3.Adj v0 v1 := by
    simp [complete_graph_3]
    exact v0_ne_v1
  have h12 : complete_graph_3.Adj v1 v2 := by
    simp [complete_graph_3]
    exact v1_ne_v2
  have h20 : complete_graph_3.Adj v2 v0 := by
    simp [complete_graph_3]
    exact v2_ne_v0

  -- 三角形サイクル 0 → 1 → 2 → 0 を構築
  let triangle := SimpleGraph.Walk.cons h01
    (SimpleGraph.Walk.cons h12 (SimpleGraph.Walk.cons h20 SimpleGraph.Walk.nil))

  use triangle
  -- 長さが3であることを確認
  simp [triangle]

-- より一般的な形：頂点数3の完全グラフにはサイクルがある
theorem complete_graph_3_has_cycle_general :
  ∃ (p : SimpleGraph.Walk complete_graph_3 v0 v0), p.length ≥ 3 := by
  -- 上で構築した長さ3の三角形サイクルを使用
  obtain ⟨triangle, h_len⟩ := complete_graph_3_triangle_cycle
  use triangle
  rw [h_len]

-- ===============================================

universe univ_u
def List.toSet {α : Type univ_u} :  List α → Set α
  | []    => ∅
  | a::as => {a} ∪ as.toSet

def n_neq_zero : n ≠ 0 := by
  intro h
  rw [h] at nGt1
  contradiction

def xx (i : ZMod n) : vertices n := by
  -- (0, i) が all_vertices に含まれることを示す
  use (0, i)
  simp [all_vertices]
  -- ∃ a < n, ↑a = i を証明
  have n_ne_zero : n ≠ 0 := n_neq_zero n nGt1
  have : NeZero n := ⟨n_ne_zero⟩
  use i.val, i.val_lt
  simp

def yy (i : ZMod n) : vertices n := by
  -- (1, i) が all_vertices に含まれることを示す
  use (1, i)
  simp [all_vertices]
  -- ∃ a < n, ↑a = i を証明
  have n_ne_zero : n ≠ 0 := n_neq_zero n nGt1
  have : NeZero n := ⟨n_ne_zero⟩
  use i.val, i.val_lt
  simp

def uu (i : ZMod n) : vertices n := by
  -- (2, i) が all_vertices に含まれることを示す
  use (2, i)
  simp [all_vertices]
  -- ∃ a < n, ↑a = i を証明
  have n_ne_zero : n ≠ 0 := n_neq_zero n nGt1
  have : NeZero n := ⟨n_ne_zero⟩
  use i.val, i.val_lt
  simp

def vv (i : ZMod n) : vertices n := by
  -- (3, i) が all_vertices に含まれることを示す
  use (3, i)
  simp [all_vertices]
  -- ∃ a < n, ↑a = i を証明
  have n_ne_zero : n ≠ 0 := n_neq_zero n nGt1
  have : NeZero n := ⟨n_ne_zero⟩
  use i.val, i.val_lt
  simp

-- 局所的な記法を使って関数呼び出しを簡潔にする
local notation "x" => xx n nGt1
local notation "y" => yy n nGt1
local notation "u" => uu n nGt1
local notation "v" => vv n nGt1

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
noncomputable instance : Fintype (vertices n) := (all_vertices n).finite_toSet.fintype

lemma dgpg_is_hamiltonian_even (nIsEven : n % 2 = 0) :
  SimpleGraph.IsHamiltonian (dgpg n t nGt1) := by
  -- n が偶数のときの Hamiltonian cycle の構成と証明をここに記述
  sorry

def G := dgpg n t nGt1

lemma neq_2_0 : 2 ≠ 0 := by
  norm_num

lemma u0x0_ne : (u 0) ≠ (x 0) := by
  intro h
  simp [uu, xx] at *
  -- h から val フィールドの等価性を取得
  have h_val : (u 0).val = (x 0).val := by
    exact congrArg Subtype.val h
  have : 2 = 0 := by
    -- val フィールドから最初の成分を比較
    have : (u 0).val.fst = (x 0).val.fst := by
      rw [h_val]
    simp [uu, xx] at this
  have : 2 ≠ 0 := neq_2_0
  contradiction

lemma ux_ne (i : ZMod n): (u i) ≠ (x i) := by
  intro h
  simp [uu, xx] at *
  -- h から val フィールドの等価性を取得
  have h_val : (u i).val = (x i).val := by
    exact congrArg Subtype.val h
  have : 2 = 0 := by
    -- val フィールドから最初の成分を比較
    have : (u i).val.fst = (x i).val.fst := by
      rw [h_val]
    simp [uu, xx] at this
  have : 2 ≠ 0 := neq_2_0
  contradiction

lemma elem_not_mem_of_empty_list {α : Type univ_u} {elem : α} : List.Mem elem [] → False := by
  intro h
  cases h

lemma elem_list_to_set
  {α : Type univ_u} {elem : α} {lst : List α}
  : List.Mem elem lst → elem ∈ List.toSet lst := by
  intro h
  induction lst with
  | nil =>
    exact elem_not_mem_of_empty_list h
  | cons a as ih =>
    simp [List.toSet]
    cases h with
    | head =>
      apply Or.inl
      rfl
    | tail =>
      apply Or.inr
      exact ih ‹List.Mem elem as›

#check List.mem_append_left

lemma elem_mem_concated_list_6
  {α : Type univ_u} {elem : α}
  {lst1 lst2 lst3 lst4 lst5 lst6 : List α}
  : List.Mem elem lst6
    → List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5 ++ lst6) := by
  intro h
  exact List.mem_append_right (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5) h

lemma elem_mem_concated_list_5
  {α : Type univ_u} {elem : α}
  {lst1 lst2 lst3 lst4 lst5 lst6 : List α}
  : List.Mem elem lst5
    → List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5 ++ lst6) := by
  intro h
  have : List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5) := by
    exact List.mem_append_right (lst1 ++ lst2 ++ lst3 ++ lst4) h
  exact List.mem_append_left lst6 this

lemma elem_mem_concated_list_4
  {α : Type univ_u} {elem : α}
  {lst1 lst2 lst3 lst4 lst5 lst6 : List α}
  : List.Mem elem lst4
    → List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5 ++ lst6) := by
  intro h
  have : List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4) := by
    exact List.mem_append_right (lst1 ++ lst2 ++ lst3) h
  have : List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5) := by
    exact List.mem_append_left lst5 this
  exact List.mem_append_left lst6 this

lemma elem_mem_concated_list_3
  {α : Type univ_u} {elem : α}
  {lst1 lst2 lst3 lst4 lst5 lst6 : List α}
  : List.Mem elem lst3
    → List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5 ++ lst6) := by
  intro h
  have : List.Mem elem (lst1 ++ lst2 ++ lst3) := by
    exact List.mem_append_right (lst1 ++ lst2) h
  have : List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4) := by
    exact List.mem_append_left lst4 this
  have : List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5) := by
    exact List.mem_append_left lst5 this
  exact List.mem_append_left lst6 this

lemma elem_mem_concated_list_2
  {α : Type univ_u} {elem : α}
  {lst1 lst2 lst3 lst4 lst5 lst6 : List α}
  : List.Mem elem lst2
    → List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5 ++ lst6) := by
  intro h
  have : List.Mem elem (lst1 ++ lst2) := by
    exact List.mem_append_right lst1 h
  have : List.Mem elem (lst1 ++ lst2 ++ lst3) := by
    exact List.mem_append_left lst3 this
  have : List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4) := by
    exact List.mem_append_left lst4 this
  have : List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5) := by
    exact List.mem_append_left lst5 this
  exact List.mem_append_left lst6 this

lemma elem_mem_concated_list_1
  {α : Type univ_u} {elem : α}
  {lst1 lst2 lst3 lst4 lst5 lst6 : List α}
  : List.Mem elem lst1
    → List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5 ++ lst6) := by
  intro h
  have : List.Mem elem (lst1 ++ lst2) := by
    exact List.mem_append_left lst2 h
  have : List.Mem elem (lst1 ++ lst2 ++ lst3) := by
    exact List.mem_append_left lst3 this
  have : List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4) := by
    exact List.mem_append_left lst4 this
  have : List.Mem elem (lst1 ++ lst2 ++ lst3 ++ lst4 ++ lst5) := by
    exact List.mem_append_left lst5 this
  exact List.mem_append_left lst6 this

lemma u0x0_edge : (dgpg n t nGt1).Adj (u ↑0) (x ↑0) := by
  simp [dgpg, u0x0_ne]
  apply elem_list_to_set
  -- s(u ↑0, x ↑0) = s(x ↑0, u ↑0) なので、第5リストの要素として存在する
  have h_sym : s(u ↑0, x ↑0) = s(x ↑0, u ↑0) := by simp [Sym2.eq_swap]
  rw [h_sym]
  -- List.mem_append を何回か使って段階的に拡張
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  -- 5番目のリストに直接含まれることを証明
  apply List.mem_map.mpr
  use 0
  constructor
  · -- 0 ∈ List.flatMap (fun a ↦ [a]) (do let a ← List.range n; pure ↑a) を証明
    simp [List.mem_flatMap]
    use 0
    constructor
    · -- 0 ∈ List.range n を証明
      exact Nat.pos_of_ne_zero (n_neq_zero n nGt1)
    · -- 0 ∈ [↑0] を証明
      simp
  · -- s(x 0, u 0) = s(x ↑0, u ↑0) を証明
    simp

--lemma ux_edge (i : ZMod n): (dgpg n t nGt1).Adj (u i) (x i) := by
--  simp [dgpg, ux_ne]
--  apply elem_list_to_set
--  -- s(u ↑0, x ↑0) = s(x ↑0, u ↑0) なので、第5リストの要素として存在する
--  have h_sym : s(u ↑i, x ↑i) = s(x ↑i, u ↑i) := by simp [Sym2.eq_swap]
--  rw [h_sym]
--  -- List.mem_append を何回か使って段階的に拡張
--  apply List.mem_append_right
--  apply List.mem_append_right
--  apply List.mem_append_right
--  apply List.mem_append_right
--  apply List.mem_append_left
--  -- 5番目のリストに直接含まれることを証明
--  apply List.mem_map.mpr
--  use i
--  constructor
--  · -- 0 ∈ List.flatMap (fun a ↦ [a]) (do let a ← List.range n; pure ↑a) を証明
--    simp [List.mem_flatMap]
--    use i.val
--    constructor
--    · have : ZMod n = Fin n := by
--        simp [ZMod]
--        match n with
--        | 0 => contradiction
--        | 1 => contradiction
--        | Nat.succ n' => rfl
--      have : Fin n := by



--Hamiltonian サイクルに関する定理（コメントアウト）
theorem dgpg_is_hamiltonian :
  SimpleGraph.IsHamiltonian (dgpg n t nGt1) := by
  by_cases nIsEven : n % 2 = 0
  . exact dgpg_is_hamiltonian_even n t nGt1 nIsEven
  -- Hamiltonian cycle の構成と証明をここに記述
  sorry
