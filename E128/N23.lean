import Mathlib
/-! Erdős #128, n = 23 from n = 22 (in the exact formulation of `E128.Dense`). -/

/-! Erdős #128: reduction of a counterexample search to maximal triangle-free graphs. -/

namespace E128
open Finset

variable {n : ℕ}

/-- number of edges of `G` inside `S` (ordered pairs with `a < b`) -/
def eIn (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/-- the hypothesis of #128: every set of `⌊n/2⌋` vertices spans more than `n²/50` edges -/
def Dense (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset (Fin n), S.card = n / 2 → n ^ 2 < 50 * eIn G S

lemma eIn_mono {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G ≤ H) (S : Finset (Fin n)) : eIn G S ≤ eIn H S := by
  unfold eIn
  apply card_le_card
  intro p hp
  simp only [mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, h hp.2.2⟩

lemma dense_mono {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G ≤ H) (hG : Dense G) : Dense H := fun S hS =>
  lt_of_lt_of_le (hG S hS) (Nat.mul_le_mul_left 50 (eIn_mono h S))

/-- maximal triangle-free: triangle-free, and adding any missing edge creates a triangle -/
def MaxTF (H : SimpleGraph (Fin n)) : Prop :=
  H.CliqueFree 3 ∧ ∀ H' : SimpleGraph (Fin n), H ≤ H' → H'.CliqueFree 3 → H' = H

/-- every triangle-free graph lies below a maximal triangle-free graph on the same vertices -/
theorem exists_maxTF (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) :
    ∃ H, G ≤ H ∧ MaxTF H := by
  classical
  -- choose a triangle-free supergraph with the largest number of edges
  let T : Finset (SimpleGraph (Fin n)) := univ.filter (fun H => G ≤ H ∧ H.CliqueFree 3)
  have hT : T.Nonempty := ⟨G, by simp [T, hG]⟩
  obtain ⟨H, hH, hmax⟩ := T.exists_max_image (fun H => H.edgeFinset.card) hT
  simp only [T, mem_filter, mem_univ, true_and] at hH
  refine ⟨H, hH.1, hH.2, fun H' hle hfree => ?_⟩
  have hH'T : H' ∈ T := by simp [T, le_trans hH.1 hle, hfree]
  have hc := hmax H' hH'T
  have hsub : H.edgeFinset ⊆ H'.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono hle he
  have heq : H.edgeFinset = H'.edgeFinset := eq_of_subset_of_card_le hsub hc
  apply SimpleGraph.edgeSet_injective
  have := congrArg (fun s : Finset (Sym2 (Fin n)) => (s : Set (Sym2 (Fin n)))) heq
  simpa using this.symm

open Classical in
/-- **Reduction.** If no maximal triangle-free graph on `n` vertices satisfies the hypothesis,
then every graph on `n` vertices satisfying the hypothesis contains a triangle. This is exactly
what an exhaustive search over maximal triangle-free graphs has to establish. -/
theorem reduction
    (hmtf : ∀ H : SimpleGraph (Fin n), MaxTF H → ¬ Dense H) :
    ∀ G : SimpleGraph (Fin n), Dense G → ¬ G.CliqueFree 3 := by
  intro G hD hfree
  obtain ⟨H, hle, hH⟩ := exists_maxTF G hfree
  exact hmtf H hH (dense_mono hle hD)

/-- sanity check of the definitions: the 5-cycle (n = 5, ⌊5/2⌋ = 2) is not `Dense`. -/
example : ¬ Dense (SimpleGraph.cycleGraph 5) := by
  intro h
  have := h {0, 2} (by decide)
  revert this
  decide

end E128




namespace E128
open Finset

/-- Restricting to the first 22 vertices preserves the edge count inside a set. -/
lemma eIn_comap_castSucc (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj]
    [DecidableRel (G.comap (Fin.castSuccEmb : Fin 22 ↪ Fin 23)).Adj]
    (S : Finset (Fin 22)) :
    eIn (G.comap (Fin.castSuccEmb : Fin 22 ↪ Fin 23)) S = eIn G (S.map Fin.castSuccEmb) := by
  unfold eIn
  rw [← Finset.card_map (Function.Embedding.prodMap Fin.castSuccEmb Fin.castSuccEmb)]
  congr 1
  ext ⟨a, b⟩
  simp only [mem_map, mem_filter, mem_product, Function.Embedding.prodMap, Prod.exists,
    Function.Embedding.coeFn_mk, Prod.map, Prod.mk.injEq, SimpleGraph.comap_adj,
    Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨x, y, ⟨⟨hx, hy⟩, hxy, hadj⟩, rfl, rfl⟩
    exact ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, Fin.castSucc_lt_castSucc_iff.mpr hxy, hadj⟩
  · rintro ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, hxy, hadj⟩
    exact ⟨x, y, ⟨⟨hx, hy⟩, Fin.castSucc_lt_castSucc_iff.mp hxy, hadj⟩, rfl, rfl⟩

open Classical in
/-- If no maximal triangle-free graph on 22 vertices is `Dense`, then every `Dense` graph on
23 vertices contains a triangle. The hypothesis is what the exhaustive n = 22 search checks. -/
theorem n23_of_n22
    (h22 : ∀ H : SimpleGraph (Fin 22), MaxTF H → ¬ Dense H) :
    ∀ G : SimpleGraph (Fin 23), Dense G → ¬ G.CliqueFree 3 := by
  intro G hD hfree
  let G' : SimpleGraph (Fin 22) := G.comap (Fin.castSuccEmb : Fin 22 ↪ Fin 23)
  have hfree' : G'.CliqueFree 3 :=
    hfree.comap ⟨(SimpleGraph.Embedding.comap (Fin.castSuccEmb : Fin 22 ↪ Fin 23) G).toCopy⟩
  have hD' : Dense G' := by
    intro S hS
    have hS' : (S.map Fin.castSuccEmb).card = 23 / 2 := by simpa using hS
    have := hD _ hS'
    have e := eIn_comap_castSucc G S
    have : (22:ℕ) ^ 2 < 50 * eIn G' S := by
      have h1 : 50 * eIn G (S.map Fin.castSuccEmb) = 50 * eIn G' S := by
        rw [← e]
      omega
    exact this
  exact reduction h22 G' hD' hfree'

end E128
#print axioms E128.reduction
#print axioms E128.n23_of_n22
