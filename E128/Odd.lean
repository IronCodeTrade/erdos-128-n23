import Mathlib
/-! Erdős #128: a counterexample on an odd number 2m+1 of vertices yields one on 2m vertices.
  e2 G S = number of ordered adjacent pairs inside S (= 2 · edges of the induced subgraph).
  "more than n²/50 edges" ⇔ 50·e > n² ⇔ 25·e2 > n². -/
namespace R7E128
variable {α : Type*} [DecidableEq α]

def e2 (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : ℕ :=
  (S.offDiag.filter (fun p => G.Adj p.1 p.2)).card

def Counterex (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) : Prop :=
  (∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)) ∧
  ∀ S ⊆ V, V.card / 2 ≤ S.card → V.card ^ 2 < 25 * e2 G S

theorem odd_reduce (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (v : α)
    (hv : v ∈ V) (hodd : V.card % 2 = 1) (h : Counterex G V) : Counterex G (V.erase v) := by
  obtain ⟨htf, hc⟩ := h
  have hcard : (V.erase v).card = V.card - 1 := Finset.card_erase_of_mem hv
  refine ⟨fun a ha b hb c hc' => htf a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
      c (Finset.mem_of_mem_erase hc'), ?_⟩
  intro S hS hk
  have hSV : S ⊆ V := hS.trans (Finset.erase_subset v V)
  have hk' : V.card / 2 ≤ S.card := by rw [hcard] at hk; omega
  have h1 := hc S hSV hk'
  rw [hcard]
  have : (V.card - 1) ^ 2 ≤ V.card ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
  omega

/-- Consequently: if no counterexample exists on any 2m-vertex set, none exists on any
  (2m+1)-vertex set (in any type with a vertex to delete). -/
theorem no_odd_of_no_even (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (m : ℕ)
    (hV : V.card = 2 * m + 1)
    (hEven : ∀ W : Finset α, W.card = 2 * m → ¬ Counterex G W) : ¬ Counterex G V := by
  intro h
  have hne : V.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hne
  have := odd_reduce G V v hv (by omega) h
  exact hEven (V.erase v) (by rw [Finset.card_erase_of_mem hv]; omega) this
end R7E128
#print axioms R7E128.no_odd_of_no_even
