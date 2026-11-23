module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.PrimCj
section
namespace UpperTheory.V.Z.Sym.Unl

private theorem ker_cj {N : ℕ} (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) :
    (cj σ χ).toUnitHom.ker = χ.toUnitHom.ker := by
  ext x
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, cj, MulChar.ringHomComp_apply]
  exact map_eq_one_iff σ σ.injective

theorem primCj : PrimCj := by
  intro N _ χ σ hχ
  have key : ∀ d : ℕ, (cj σ χ).FactorsThrough d ↔ χ.FactorsThrough d := by
    intro d
    constructor
    · intro h
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd, ← ker_cj σ χ]
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
    · intro h
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd, ker_cj σ χ]
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
  have hc : (cj σ χ).conductor = χ.conductor := by
    unfold DirichletCharacter.conductor DirichletCharacter.conductorSet
    congr 1
    ext d
    exact key d
  unfold DirichletCharacter.IsPrimitive at hχ ⊢
  rw [hc]
  exact hχ

end UpperTheory.V.Z.Sym.Unl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.RootOfSmul
section
open UpperTheory.V.Af UpperTheory.GalN.V

private theorem root_of_smul {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K) (hc : c ≠ 0) (α : K)
    (h : (c • M).charpoly.IsRoot α) : M.charpoly.IsRoot (c⁻¹ * α) := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at h ⊢
  have key : (Matrix.scalar (Fin n)) α - c • M = c • ((Matrix.scalar (Fin n)) (c⁻¹ * α) - M) := by
    rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
    congr 2
    ext i
    simp [mul_inv_cancel_left₀ hc]
  rw [key, Matrix.det_smul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (pow_eq_zero_iff'.mp h1).1 hc
  · exact h1

theorem UpperTheory.V.Z.Sym.Unl.twOk :
    UpperTheory.V.Z.Sym.Unl.TwOk := by
  intro F Ω _ _ _ _ l _ n ι r δ
  have hc : ∀ s, ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) ≠ 0 := fun s => Units.ne_zero _
  have hroot : ∀ s α, (↑((tw r δ) s) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.IsRoot α →
      (↑(r s) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.IsRoot (((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)⁻¹ * α) := by
    intro s α h
    rw [tw_val] at h
    exact root_of_smul _ _ (hc s) α h
  have hnorm : ∀ s α, ‖ι α‖ = ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ *
      ‖ι (((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)⁻¹ * α)‖ := by
    intro s α
    rw [← norm_mul, ← map_mul, mul_inv_cancel_left₀ (hc s)]
  have hpos : ∀ s, 0 < ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ := by
    intro s
    exact norm_pos_iff.mpr ((map_ne_zero ι).mpr (hc s))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro w hw A hA s hs α β hα hβ heq
    apply h w hw A hA s hs _ _ (hroot s α hα) (hroot s β hβ)
    have hp := hpos s
    rw [hnorm s α, hnorm s β, mul_pow, mul_pow] at heq
    have hp2 : 0 < ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ ^ 2 := by positivity
    have := heq
    rw [mul_left_comm] at this
    exact mul_left_cancel₀ hp2.ne' this
  · intro w hw A hA s hs α β hα hβ
    have key := h w hw A hA s hs _ _ (hroot s α hα) (hroot s β hβ)
    have hp := hpos s
    rw [hnorm s α, hnorm s β, mul_left_comm]
    exact mul_lt_mul_of_pos_left key hp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SplitTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.GalN.V

private theorem ratio_ne {A B q x y : ℝ} (hA : 0 < A) (hB : 0 < B) (hq : 1 < q) (h1 : A < q * B) (h2 : B < q * A)
    (h3 : A ^ 2 ≠ q * B ^ 2) (h4 : B ^ 2 ≠ q * A ^ 2)
    (hx : x = A / B ∨ x = 1 ∨ x = B / A) (hy : y = A / B ∨ y = 1 ∨ y = B / A) : x ≠ q * y := by
  have hAn : A ≠ 0 := hA.ne'
  have hBn : B ≠ 0 := hB.ne'
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> intro h <;> field_simp at h
  all_goals first
    | nlinarith
    | exact h3 (by nlinarith)
    | exact h4 (by nlinarith)

private theorem split_two {K : Type} [Field K] [IsAlgClosed K] (g : GL (Fin 2) K) :
    ∃ a b : Kˣ, (g : Matrix (Fin 2) (Fin 2) K).charpoly = (X - C (a : K)) * (X - C (b : K)) := by
  set M : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hM
  have hmon : M.charpoly.Monic := Matrix.charpoly_monic M
  have hsplit : M.charpoly.Splits := IsAlgClosed.splits _
  have hprod := hsplit.eq_prod_roots_of_monic hmon
  have hcard : M.charpoly.roots.card = 2 := by
    rw [← hsplit.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have hdet : M.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det M).mp (Units.isUnit g)
    exact this.ne_zero
  have hnz : ∀ c ∈ M.charpoly.roots, c ≠ 0 := by
    intro c hc h0
    rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly, h0] at hc
    apply hdet
    simpa [Matrix.det_neg] using hc
  have ha : a ≠ 0 := hnz a (by rw [hab]; simp)
  have hb : b ≠ 0 := hnz b (by rw [hab]; simp)
  refine ⟨Units.mk0 a ha, Units.mk0 b hb, ?_⟩
  rw [hprod, hab]
  simp

theorem UpperTheory.V.Z.Sym.Unl.adUnl :
    UpperTheory.V.Z.Sym.Unl.AdUnl := by
  intro F Ω _ _ _ _ _ l _ ι r hR hN w hw A hA _
  obtain ⟨s, hs⟩ := exists_isFrob hA
  refine ⟨s, 1, le_rfl, by simpa using hs, ?_⟩
  intro α β hα hβ k hk heq
  obtain ⟨a, b, hab⟩ := split_two (r s)
  have hc := (ad0Facts l (G F Ω) r).2.2.2.2.1 s a b hab
  have ra : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot (a : Qbar l) := by
    rw [hab]; simp
  have rb : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot (b : Qbar l) := by
    rw [hab]; simp
  have hA0 : 0 < ‖ι (a : Qbar l)‖ := norm_pos_iff.2 (by simp)
  have hB0 : 0 < ‖ι (b : Qbar l)‖ := norm_pos_iff.2 (by simp)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have := hR w hw A hA s hs _ _ ra ra
    by_contra h
    nlinarith [not_lt.mp h]
  have root : ∀ x : Qbar l, (ad0 r s : Matrix (Fin 3) (Fin 3) (Qbar l)).charpoly.IsRoot x →
      ‖ι x‖ = ‖ι (a : Qbar l)‖ / ‖ι (b : Qbar l)‖ ∨ ‖ι x‖ = 1 ∨ ‖ι x‖ = ‖ι (b : Qbar l)‖ / ‖ι (a : Qbar l)‖ := by
    intro x hx
    rw [hc] at hx
    simp only [IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hx
    rcases hx with (rfl | rfl) | rfl
    · left; simp
    · right; left; simp
    · right; right; simp
  have hn : ‖ι α‖ ^ k = (((normV w : ℕ) : ℝ) * ‖ι β‖) ^ k := by
    have := congrArg (fun z => ‖ι z‖) heq
    simpa [map_pow, map_mul, norm_pow, norm_mul, Complex.norm_natCast] using this
  have hn' : ‖ι α‖ = ((normV w : ℕ) : ℝ) * ‖ι β‖ :=
    (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (by omega)).1 hn
  exact ratio_ne hA0 hB0 hq (hR w hw A hA s hs _ _ ra rb) (hR w hw A hA s hs _ _ rb ra)
    (hN w hw A hA s hs _ _ ra rb) (hN w hw A hA s hs _ _ rb ra) (root α hα) (root β hβ) hn'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SqrtFlip
section
private theorem UpperTheory.V.Z.Sym.Unl.exists_ring_equiv_flip_sqrt (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsAlgClosed Ω]
    (ε : Ω →+* ℂ) (p : ℕ) (hp : p.Prime) :
    ∃ σ : ℂ ≃+* ℂ, σ ((Real.sqrt p : ℝ) : ℂ) = -((Real.sqrt p : ℝ) : ℂ) := by
  have hne : ∀ b : ℚ, b ^ 2 ≠ (p : ℚ) := by
    intro b hb
    apply hp.irrational_sqrt
    refine ⟨|b|, ?_⟩
    have h2 : ((b : ℝ)) ^ 2 = (p : ℝ) := by exact_mod_cast hb
    rw [← h2, Real.sqrt_sq_eq_abs]
    push_cast
    rfl
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (p : Ω) (by norm_num : 0 < 2)
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hne
  have hev : ∀ x : Ω, x ^ 2 = (p : Ω) → Polynomial.aeval x (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)) = 0 := by
    intro x hx
    simp [hx]
  have hmon : (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)).Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hmin : minpoly ℚ (-a) = minpoly ℚ a := by
    rw [← minpoly.eq_of_irreducible_of_monic hirr (hev a ha) hmon,
      ← minpoly.eq_of_irreducible_of_monic hirr (hev (-a) (by rw [neg_sq, ha])) hmon]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).mp hmin
  let s : Ω ≃+* Ω := σ.toRingEquiv
  have hsa : s a = -a := hσ
  obtain ⟨g, hg⟩ := GlobalTheory.FN.exists_ringEquiv_extend_of_embedding Ω ε s
  refine ⟨g, ?_⟩
  have hea : (ε a) ^ 2 = ((Real.sqrt p : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, ha, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hga : g (ε a) = -(ε a) := by rw [hg, hsa, map_neg]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hea with h | h
  · rw [← h, hga]
  · have : ((Real.sqrt p : ℝ) : ℂ) = -(ε a) := by rw [h, neg_neg]
    rw [this, map_neg, hga, neg_neg]

theorem UpperTheory.V.Z.Sym.Unl.sqrtFlip :
    UpperTheory.V.Z.Sym.Unl.SqrtFlip := fun p hp =>
  UpperTheory.V.Z.Sym.Unl.exists_ring_equiv_flip_sqrt (AlgebraicClosure ℚ)
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom p hp
end

