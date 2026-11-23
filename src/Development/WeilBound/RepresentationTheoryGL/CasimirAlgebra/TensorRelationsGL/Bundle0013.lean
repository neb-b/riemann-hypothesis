module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PYoungB

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllC
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  {ι : Type} [DecidableEq ι] (lab : P → ι) (τ₀ : ι)

def labR : {p // ¬ lab p = τ₀} → {τ // τ ≠ τ₀} := fun p => ⟨lab p.1, p.2⟩

theorem conj_tensor_entry_base (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (tE Finset.univ (fun a b => lift (F a b)) c d) =
      tE (fib lab τ₀) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ₀) = Finset.univ := by
    ext x
    simp [fib, Finset.mem_subtype, x.2]
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ₀) = ∅ := by
    ext x
    simp [fib, Finset.mem_subtype, x.2]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]

theorem conj_tensor_entry_fibre (τ : {τ // τ ≠ τ₀}) (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (lift (tE (fib (labR lab τ₀) τ) F c d)) =
      tE (fib lab τ.1) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ.1) = ∅ := by
    ext x
    simp only [Finset.mem_subtype, fib, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    rw [x.2]
    exact fun h => τ.2 h.symm
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ.1) = fib (labR lab τ₀) τ := by
    ext x
    simp [fib, labR, Finset.mem_subtype, Subtype.ext_iff]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]

omit [DecidableEq P] in
theorem card_R (τ : {τ // τ ≠ τ₀}) (co : P → Fin n) (k : Fin n) :
    (Finset.univ.filter fun p : {p // ¬ lab p = τ₀} => labR lab τ₀ p = τ ∧ co p.1 = k).card =
      (Finset.univ.filter fun p => lab p = τ.1 ∧ co p = k).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff] at hp ⊢
    exact hp
  · intro p _ q _ h
    exact Subtype.ext h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨⟨p, fun h => τ.2 (hp.1.symm.trans h)⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff]
    exact hp

omit [Fintype P] in
theorem base (E : ι → Fin n → Fin n → Module.End ℂ M) (l : ι → Fin n → ℤ)
    (hl : ∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) [Fintype P] [IsEmpty P]
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin n) :
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) •
          (ℓ ∘ₗ cA col b ∘ₗ S) := by
  have hfib : ∀ τ, fib lab τ = ∅ := fun τ => Finset.eq_empty_of_isEmpty _
  have hG : colG col = {1} := by
    ext σ
    simp [colG, Subsingleton.elim σ 1]
  obtain ⟨m, hm⟩ : ∃ m, ℓ m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  refine ⟨1, Subalgebra.one_mem _, ?_, ?_⟩
  · intro h
    apply hm
    have := LinearMap.congr_fun h (fun _ => m)
    simpa [cA, alt, hG, pm] using this
  · intro τ u
    have hc := qdet_lift (P := P) (E τ) (fun k => (l τ k : ℂ)) (hl τ) u
    simp only [hfib, tE_empty]
    rw [hc, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul]
    simp
    rfl

end PositivityTheory.Rg.Cz.TA

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PYoung
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace YoungTableau

section Main

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [DecidableEq ι]
  {Q : Type} [Fintype Q] [DecidableEq Q] {N : ℕ} {C : Type} [DecidableEq C]

theorem altPair_apply (tl : Fin N → ι) (f : TV n M (Q ⊕ (Fin N ⊕ Fin N))) (I : Q ⊕ (Fin N ⊕ Fin N) → Fin n) :
    altPair tl f I = ∑ σ ∈ colG tl, ((Equiv.Perm.sign σ : ℤ) : ℂ) • f (I ∘ dbl σ) := by
  rw [altPair, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, pm_apply]

def inF (Q : Type) (N : ℕ) : Fin N → Q ⊕ (Fin N ⊕ Fin N) := fun k => .inr (.inl k)

def inS (Q : Type) (N : ℕ) : Fin N → Q ⊕ (Fin N ⊕ Fin N) := fun k => .inr (.inr k)

theorem term (tl : Fin N → ι) (col : Q ⊕ (Fin N ⊕ Fin N) → C) (b : Q ⊕ (Fin N ⊕ Fin N) → Fin n)
    (hT : IsTab col b) (h1 : ∀ p k, col (.inl p) ≠ col (.inr k)) (h2 : ∀ k k', col (.inr (.inl k)) ≠ col (.inr (.inr k')))
    (ξ : TV n M (Q ⊕ (Fin N ⊕ Fin N))) (σ : Equiv.Perm (Fin N)) :
    alt (colG col) ξ (b ∘ dbl σ) =
      ((sg (col ∘ inF Q N) (b ∘ inF Q N) ((b ∘ inF Q N) ∘ σ) * sg (col ∘ inS Q N) (b ∘ inS Q N) ((b ∘ inS Q N) ∘ σ) : ℤ) : ℂ)
        • alt (colG col) ξ b := by
  have hFtab : IsTab (col ∘ inF Q N) (b ∘ inF Q N) := by
    refine isTab_comp col b hT (inF Q N) ?_ ?_
    · intro x y hxy
      simpa [inF] using hxy
    · intro q y hq
      simp only [inF] at hq
      rcases q with q | k | k
      · exact absurd hq (h1 q _)
      · exact ⟨k, rfl⟩
      · exact absurd hq.symm (h2 y k)
  have hStab : IsTab (col ∘ inS Q N) (b ∘ inS Q N) := by
    refine isTab_comp col b hT (inS Q N) ?_ ?_
    · intro x y hxy
      simpa [inS] using hxy
    · intro q y hq
      simp only [inS] at hq
      rcases q with q | k | k
      · exact absurd hq (h1 q _)
      · exact absurd hq (h2 k y)
      · exact ⟨k, rfl⟩
  have key : ColInj col (b ∘ dbl σ) →
      (∃ π ∈ colG (col ∘ inF Q N), (b ∘ inF Q N) ∘ ⇑π = (b ∘ inF Q N) ∘ ⇑σ) ∧
      (∃ π ∈ colG (col ∘ inS Q N), (b ∘ inS Q N) ∘ ⇑π = (b ∘ inS Q N) ∘ ⇑σ) := by
    intro hc
    refine ⟨exists_perm _ _ hFtab σ ?_, exists_perm _ _ hStab σ ?_⟩
    · intro k k' hk hb'
      have := hc (inF Q N k) (inF Q N k') hk (by simpa [dbl, inF] using hb')
      simpa [inF] using this
    · intro k k' hk hb'
      have := hc (inS Q N k) (inS Q N k') hk (by simpa [dbl, inS] using hb')
      simpa [inS] using this
  have hdup : ¬ ColInj col (b ∘ dbl σ) → alt (colG col) ξ (b ∘ dbl σ) = 0 := by
    intro hc
    simp only [ColInj, not_forall] at hc
    obtain ⟨p, q, hcol, hbq, hpq⟩ := hc
    exact alt_dup col ξ _ p q hpq hcol hbq
  by_cases hF : ∃ π ∈ colG (col ∘ inF Q N), (b ∘ inF Q N) ∘ ⇑π = (b ∘ inF Q N) ∘ ⇑σ
  · by_cases hS : ∃ π ∈ colG (col ∘ inS Q N), (b ∘ inS Q N) ∘ ⇑π = (b ∘ inS Q N) ∘ ⇑σ
    · obtain ⟨πF, hπF, eF⟩ := hF
      obtain ⟨πS, hπS, eS⟩ := hS
      rw [← eF, ← eS, sg_perm _ _ hFtab.1 πF hπF, sg_perm _ _ hStab.1 πS hπS]
      rw [mem_colG] at hπF hπS
      have hπ : (Equiv.refl Q).sumCongr (πF.sumCongr πS) ∈ colG col := by
        rw [mem_colG]
        rintro (q | k | k)
        · rfl
        · simpa [inF] using hπF k
        · simpa [inS] using hπS k
      have hb : b ∘ dbl σ = b ∘ ⇑((Equiv.refl Q).sumCongr (πF.sumCongr πS)) := by
        funext p
        rcases p with q | k | k
        · rfl
        · simpa [dbl, inF] using (congrFun eF k).symm
        · simpa [dbl, inS] using (congrFun eS k).symm
      rw [hb, alt_perm col ξ b _ hπ, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_sumCongr]
      simp
    · rw [sg_zero _ _ _ hS, mul_zero, Int.cast_zero, zero_smul]
      exact hdup (fun hc => hS (key hc).2)
  · rw [sg_zero _ _ _ hF, zero_mul, Int.cast_zero, zero_smul]
    exact hdup (fun hc => hF (key hc).1)

end Main

end YoungTableau

open YoungTableau in
theorem young_holds : Young := by
  intro n M _ _ ι _ Q _ _ N tl C _ col b hT h1 h2 h3 h4 ξ h
  rw [cA_apply]
  have key : altPair tl (alt (colG col) ξ) b = ((kap tl (col ∘ inF Q N) (col ∘ inS Q N) (b ∘ inF Q N)
      (b ∘ inS Q N) : ℤ) : ℂ) • alt (colG col) ξ b := by
    rw [altPair_apply, kap, Int.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [term tl col b hT h1 h2 ξ σ, smul_smul]
    push_cast
    ring_nf
  rw [h] at key
  have hk := kap_pos tl (col ∘ inF Q N) (col ∘ inS Q N) (b ∘ inF Q N) (b ∘ inS Q N) (fun k k' => h3 k k')
    (fun k k' => h4 k k') (fun k k' ht hr hc => by
      have := hT.1 (inF Q N k) (inF Q N k') ((h3 k k').mpr ⟨ht, hc⟩) hr
      simpa [inF] using this)
  exact (smul_eq_zero.mp key.symm).resolve_left (by exact_mod_cast hk.ne')

end PositivityTheory.Rg.Cz

end
end

