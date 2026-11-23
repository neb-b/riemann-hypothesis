module

public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0036
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionSkewAdjointL2
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary PositivityTheory.S2.Clozel Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.PeterssonSkew

theorem integral_deriv_eq_zero {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) [IsFiniteMeasure ν]
    (u v u' v' : ℝ → Q → ℂ) (C : ℝ)
    (hu : ∀ t q, HasDerivAt (fun s => u s q) (u' t q) t) (hv : ∀ t q, HasDerivAt (fun s => v s q) (v' t q) t)
    (bu : ∀ t q, ‖u t q‖ ≤ C) (bv : ∀ t q, ‖v t q‖ ≤ C) (bu' : ∀ t q, ‖u' t q‖ ≤ C) (bv' : ∀ t q, ‖v' t q‖ ≤ C)
    (mu : ∀ t, AEStronglyMeasurable (u t) ν) (mv : ∀ t, AEStronglyMeasurable (v t) ν)
    (mu' : AEStronglyMeasurable (u' 0) ν) (mv' : AEStronglyMeasurable (v' 0) ν)
    (hc : ∀ t, ∫ q, u t q * conj (v t q) ∂ν = ∫ q, u 0 q * conj (v 0 q) ∂ν) :
    ∫ q, (u' 0 q * conj (v 0 q) + u 0 q * conj (v' 0 q)) ∂ν = 0 := by
  have mc : ∀ {f : Q → ℂ}, AEStronglyMeasurable f ν → AEStronglyMeasurable (fun q => conj (f q)) ν :=
    fun h => Complex.continuous_conj.comp_aestronglyMeasurable h
  have hC : 0 ≤ C ∨ IsEmpty Q := by
    by_cases h : Nonempty Q
    · obtain ⟨q⟩ := h
      exact Or.inl ((norm_nonneg _).trans (bu 0 q))
    · exact Or.inr (not_nonempty_iff.1 h)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t q => u t q * conj (v t q))
    (F' := fun t q => u' t q * conj (v t q) + u t q * conj (v' t q))
    (bound := fun _ => C * C + C * C) Filter.univ_mem
    (Eventually.of_forall fun t => (mu t).mul (mc (mv t)))
    (Integrable.of_bound ((mu 0).mul (mc (mv 0))) (C * C) (Eventually.of_forall fun q => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (bu 0 q) (bv 0 q) (norm_nonneg _) ((norm_nonneg _).trans (bu 0 q))))
    ((mu'.mul (mc (mv 0))).add ((mu 0).mul (mc mv')))
    (Eventually.of_forall fun q t _ => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul, RCLike.norm_conj]
      · exact mul_le_mul (bu' t q) (bv t q) (norm_nonneg _) ((norm_nonneg _).trans (bu' t q))
      · exact mul_le_mul (bu t q) (bv' t q) (norm_nonneg _) ((norm_nonneg _).trans (bu t q)))
    (integrable_const _)
    (Eventually.of_forall fun q t _ => (hu t q).mul (hv t q).star)
  have h0 : HasDerivAt (fun t : ℝ => ∫ q, u t q * conj (v t q) ∂ν) 0 0 := by
    simp only [hc]
    exact hasDerivAt_const _ _
  exact key.2.unique h0

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


open scoped Matrix.Norms.Operator in
theorem exists_curve (X : Lie E a) : ∃ c : ℝ → Matrix.GeneralLinearGroup (Fin a) (Cinf E), c 0 = 1 ∧
    (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => toL (c t).val) X 0 := by
  set Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of X with hY
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  have hadd : ∀ s t : ℝ, NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y) := fun s t => by
    rw [add_smul]
    exact NormedSpace.exp_add_of_commute (((Commute.refl Y).smul_left s).smul_right t)
  have hone : ∀ t : ℝ, NormedSpace.exp (t • Y) * NormedSpace.exp ((-t) • Y) = 1 := fun t => by
    rw [← hadd, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  refine ⟨fun t => ⟨NormedSpace.exp (t • Y), NormedSpace.exp ((-t) • Y), hone t, by simpa using hone (-t)⟩,
    Units.ext (by simp [NormedSpace.exp_zero]), fun s t => Units.ext (hadd s t), ?_⟩
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_translate {X : Lie E a} {c : ℝ → Matrix.GeneralLinearGroup (Fin a) (Cinf E)} (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hX : HasDerivAt (fun t => toL (c t).val) X 0) (φ : Sm E a) (g : GA E a)
    (t : ℝ) : HasDerivAt (fun s => φ.1 (g * infGL E a (c s))) (lieD X φ.1 (g * infGL E a (c t))) t := by
  have h := hasDerivAt_curve φ (g * infGL E a (c t)) c X h0 hX
  have h2 : HasDerivAt (fun s => φ.1 (g * infGL E a (c t) * infGL E a (c (s - t))))
      (lieD X φ.1 (g * infGL E a (c t))) t := HasDerivAt.comp_sub_const t t (by simpa using h)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [mul_assoc, ← map_mul, ← hadd]
  simp

theorem pet_mul_right (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {φ ψ : GA E a → ℂ}
    (hφ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ) (hψ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ) (g : GA E a) :
    pet (GlobalTheory.UnitaryBC.latticeGL E a) μ (fun x => φ (x * g)) (fun x => ψ (x * g)) =
      pet (GlobalTheory.UnitaryBC.latticeGL E a) μ φ ψ := by
  rw [← MemL2Quotient.inner_toL2_eq_theta_pairing (hφ.mul_right g) (hψ.mul_right g), ← right_translate_toL2, ← right_translate_toL2, ← MemL2Quotient.inner_toL2_eq_theta_pairing hφ hψ]
  exact LinearIsometry.inner_map_map
    { toLinearMap := (R (GlobalTheory.UnitaryBC.latticeGL E a) μ g :
        L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ →L[ℂ] L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ).toLinearMap
      norm_map' := norm_R g } _ _

theorem pet_lie_add (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E a) (φ ψ : Sm E a)
    (hφ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) (hψ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ.1)
    (hφ' : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1)
    (hψ' : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X ψ).1)
    (C : ℝ) (bφ : ∀ g, ‖φ.1 g‖ ≤ C) (bψ : ∀ g, ‖ψ.1 g‖ ≤ C)
    (bφ' : ∀ g, ‖(lie E a X φ).1 g‖ ≤ C) (bψ' : ∀ g, ‖(lie E a X ψ).1 g‖ ≤ C) :
    pet (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1 ψ.1 +
      pet (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 (lie E a X ψ).1 = 0 := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  obtain ⟨c, h0, hadd, hX⟩ := exists_curve X
  have e0 : infGL E a (c 0) = 1 := by rw [h0, map_one]
  have key := integral_deriv_eq_zero (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GlobalTheory.UnitaryBC.latticeGL E a) μ)
    (fun t q => φ.1 (q.out * infGL E a (c t))) (fun t q => ψ.1 (q.out * infGL E a (c t)))
    (fun t q => lieD X φ.1 (q.out * infGL E a (c t))) (fun t q => lieD X ψ.1 (q.out * infGL E a (c t))) C
    (fun t q => hasDerivAt_translate h0 hadd hX φ q.out t) (fun t q => hasDerivAt_translate h0 hadd hX ψ q.out t)
    (fun _ _ => bφ _) (fun _ _ => bψ _) (fun _ _ => bφ' _) (fun _ _ => bψ' _)
    (fun t => (hφ.mul_right (infGL E a (c t))).2.aestronglyMeasurable) (fun t => (hψ.mul_right (infGL E a (c t))).2.aestronglyMeasurable)
    (by simp only [e0, mul_one]; exact hφ'.2.aestronglyMeasurable) (by simp only [e0, mul_one]; exact hψ'.2.aestronglyMeasurable)
    (fun t => by
      have h1 := pet_mul_right μ hφ hψ (infGL E a (c t))
      simp only [e0, mul_one]
      exact h1)
  simp only [e0, mul_one] at key
  exact (integral_add (hφ'.integrable_mul_conj hψ) (hφ.integrable_mul_conj hψ')).symm.trans key

theorem lie_skew_adjoint : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a) (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1), (∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) → ∀ (X : Lie E a) (φ ψ : π.V), inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm ψ) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) φ)) = -inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) ψ)) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm φ) := by
  intro E _ _ _ a μ _ _ π hm hb X φ ψ
  have hL : ∀ f : π.V, ∃ C : ℝ, ∀ g, ‖f.1.1 g‖ ≤ C := fun f => hb f.1 f.2
  obtain ⟨C₁, b₁⟩ := hL φ
  obtain ⟨C₂, b₂⟩ := hL ψ
  obtain ⟨C₃, b₃⟩ := hL (π.op (.lie X) φ)
  obtain ⟨C₄, b₄⟩ := hL (π.op (.lie X) ψ)
  have h := pet_lie_add μ X φ.1 ψ.1 (hm _ φ.2) (hm _ ψ.2) (hm _ (π.op (.lie X) φ).2) (hm _ (π.op (.lie X) ψ).2)
    (max (max C₁ C₂) (max C₃ C₄))
    (fun g => (b₁ g).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun g => (b₂ g).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (fun g => (b₃ g).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (fun g => (b₄ g).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have e1 := MemL2Quotient.inner_toL2_eq_theta_pairing (hm _ (π.op (.lie X) φ).2) (hm _ ψ.2)
  have e2 := MemL2Quotient.inner_toL2_eq_theta_pairing (hm _ φ.2) (hm _ (π.op (.lie X) ψ).2)
  change inner ℂ (hm _ ψ.2).toL2 (hm _ (π.op (.lie X) φ).2).toL2 =
    -inner ℂ (hm _ (π.op (.lie X) ψ).2).toL2 (hm _ φ.2).toL2
  rw [e1, e2]
  exact eq_neg_of_add_eq_zero_left h

end GlobalTheory.CompanionTheory.PeterssonSkew
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.ClozelLie

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem Eop_add_conjugate (τ : E →+* ℂ) (i : Fin a) :
    Eop τ i i + Eop (ComplexEmbedding.conjugate τ) i i = lieS E a i i (atEmb τ 1) := by
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  simp only [Eop, e1, e2, map_neg]
  module

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (1 + 1 : Cinf E) := by
  classical
  have e : ∀ τ : E →+* ℂ, atEmb τ 1 = Pi.single (InfinitePlace.mk τ) (1 : ℂ) := fun τ => by
    unfold atEmb
    split_ifs <;> simp
  funext w
  simp only [e, Finset.sum_apply, Pi.single_apply, Pi.add_apply, Pi.one_apply]
  simp only [eq_comm (a := w)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    IsTotallyComplex.mult_eq]
  norm_num

theorem sum_Eop_diag (i : Fin a) : ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 := by
  have hs : ∑ τ : E →+* ℂ, Eop (ComplexEmbedding.conjugate τ) i i = ∑ τ : E →+* ℂ, Eop τ i i :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (fun τ : E →+* ℂ => star_star τ))
      (fun τ => Eop τ i i)
  have h : (∑ τ : E →+* ℂ, Eop τ i i) + ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 + lieS E a i i 1 := by
    nth_rw 2 [← hs]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => Eop_add_conjugate τ i, ← map_sum,
      sum_atEmb_one, map_add]
  have h2 : (2 : ℂ) • (∑ τ : E →+* ℂ, Eop τ i i) = (2 : ℂ) • lieS E a i i 1 := by
    rw [two_smul, two_smul, h]
  exact smul_right_injective _ (two_ne_zero (α := ℂ)) h2

theorem lie_oneL_eq_sum_Eop (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop_diag i]
  simp only [lieS_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  have hm : ∑ i : Fin a, Matrix.single i i (1 : Cinf E) = 1 := by
    refine Matrix.ext fun p q => ?_
    rw [Matrix.sum_apply, Matrix.one_apply]
    by_cases h : p = q
    · subst h
      simp [Matrix.single_apply]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h rfl
  congr 1
  exact (congrArg Matrix.of.symm hm).symm

end GlobalTheory.CompanionTheory.ClozelLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorHermitianSkew
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelHerm

theorem op_lie_single_neg {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (i j : Fin a) (x : Cinf E) :
    π.op (.lie (toL (Matrix.single i j (-x)))) = -π.op (.lie (toL (Matrix.single i j x))) := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  change lieS E a i j (-x) φ.1 = -(lieS E a i j x φ.1)
  rw [map_neg]
  rfl

theorem EopV_adjoint : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (i j : Fin a) (φ ψ : π.V),
    B (EopV π τ i j φ) ψ = -B φ (EopV π (NumberField.ComplexEmbedding.conjugate τ) i j ψ) := by
  intro E _ _ _ a π B hB τ i j φ ψ
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  have c2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact Complex.conj_ofReal _
  have s1 := hB.1 (toL (Matrix.single i j (atEmb τ 1))) φ ψ
  have s2 := hB.1 (toL (Matrix.single i j (atEmb τ Complex.I))) φ ψ
  simp only [EopV, e1, e2, op_lie_single_neg, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.add_apply,
    map_smul, map_sub, map_neg, map_smulₛₗ, c2, Complex.conj_I, smul_eq_mul, s1, s2, RingHom.id_apply, smul_neg,
    sub_neg_eq_add, map_add]
  ring

end GlobalTheory.CompanionTheory.ClozelHerm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationUnique
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.SW.FibSch

theorem fib_scale_core (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [MeasurableSpace R] [BorelSpace R] (hR : GlobalTheory.CompanionTheory.SW.IsLocR R) (n : ℕ)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n))
    (m : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) (hm : GlobalTheory.CompanionTheory.SW.IsGramFib R σ J n μ ν m)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hg : IsUnit g.det) :
    ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ S S' : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n,
      (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g →
      m S' = κ • (m S).map (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨-, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hg2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have hrc : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun X : Fin n → Fin M → R ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul R X h := by
    intro h
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [GlobalTheory.CompanionTheory.SW.rmul]
    refine continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun Y : Fin n → Fin M → R ⊗[F] E => Y k i :=
      (continuous_apply i).comp (continuous_apply k)
    exact h1.mul continuous_const
  let e : (Fin n → Fin M → R ⊗[F] E) ≃+ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := fun X => GlobalTheory.CompanionTheory.SW.rmul R X g
      invFun := fun X => GlobalTheory.CompanionTheory.SW.rmul R X g⁻¹
      left_inv := fun X => by simp only [hcomp, hg1, hone]
      right_inv := fun X => by simp only [hcomp, hg2, hone]
      map_add' := fun X Y => by
        funext b i
        simp only [GlobalTheory.CompanionTheory.SW.rmul, Pi.add_apply, add_mul, Finset.sum_add_distrib] }
  have hc1 : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ)
      (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    unfold HeckeCharacterZeroLocus.SiegelWeilU.cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have key : ∀ (h h' A : Matrix (Fin n) (Fin n) (R ⊗[F] E)), h * h' = 1 →
      HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
        (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h * A * h) * h' = A := by
    intro h h' A hh
    have h1 : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
        HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h = 1 := by
      rw [← HeckeCharacterZeroLocus.SiegelWeilU.cT_mul, hh, hc1]
    calc HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
          (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h * A * h) * h'
        = (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
            HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h) * A * (h * h') := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [h1, hh, Matrix.one_mul, Matrix.mul_one]
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun S : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n =>
        HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h *
          (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * h := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let t : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n ≃+ HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n :=
    { toFun := fun S => ⟨HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) g *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g, hmem S g⟩
      invFun := fun S => ⟨HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) g⁻¹ *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹, hmem S g⁻¹⟩
      left_inv := fun S => Subtype.ext (key _ _ _ hg1)
      right_inv := fun S => Subtype.ext (key _ _ _ hg2)
      map_add' := fun S T => Subtype.ext (by
        simp only [AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]) }
  have hec : Continuous e := hrc g
  have hes : Continuous e.symm := hrc g⁻¹
  have htc : Continuous t := (hcj g).subtype_mk _
  have hts : Continuous t.symm := (hcj g⁻¹).subtype_mk _
  haveI hμe : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ hec hes
  haveI hνt : (ν.map t).IsAddHaarMeasure := t.isAddHaarMeasure_map ν htc hts
  obtain ⟨a, ha0, hmu⟩ : ∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) μ).ne',
      Measure.isAddLeftInvariant_eq_smul _ _⟩
  obtain ⟨c, hc0, hnu⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ ν.map t = c • ν :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (ν.map t) ν).ne',
      Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hfib := _root_.GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul F E σ hσ M J hJ R hR n μ ν m hμ hν hm g hg t (fun _ => rfl) a c hmu hnu
  refine ⟨c / a, div_ne_zero hc0 ha0, fun S S' hS => ?_⟩
  have hS' : S' = t S := Subtype.ext hS
  have h := hfib S
  rw [← hS'] at h
  calc m S' = a⁻¹ • (a • m S') := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
    _ = (c / a) • (m S).map (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) := by
      rw [h, smul_smul, div_eq_inv_mul]

theorem fib_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], GlobalTheory.CompanionTheory.SW.IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → GlobalTheory.CompanionTheory.SW.IsGramFib R σ J n μ ν m → ∀ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsUnit g.det → ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ S S' : HermR R σ n, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g → m S' = κ • (m S).map (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm g hg
  exact fib_scale_core F E σ hσ M J hJ R hR n μ ν m hμ hν hm g hg

end GlobalTheory.CompanionTheory.SW.FibSch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureStandardVolume
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem GlobalTheory.CompanionTheory.SiegelND.Coef.finV_compactOpenN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → MeasurableSet A ∧ mv c A ≠ ⊤ := by
  intro F E _ _ _ _ _ σ hσ M J hJ n _ d b v lv hlv mv hm c _ A hAc hAo
  have hR := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hR
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := (GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hσ M J hJ (Fv F v) hR n _ _ mv (hW n M) (hH n) hm c).1
  exact ⟨hAo.measurableSet, hAc.measure_lt_top.ne⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatC
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsCoord (σ : E →ₐ[F] E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
    (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) : Prop :=
  IsHomeomorph Θ ∧ (∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) ∧
    (∀ x w, Θ ((1 : Ainf F) ⊗ₜ[F] x) w = τ w x) ∧
    ∀ z w, ((e (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w : ℝ) : ℂ) = Θ z w + conj (Θ z w)

def tupC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n M : ℕ} (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    InfinitePlace F → Fin n → Fin M → ℂ :=
  fun w a i => Θ (X a i) w

def matC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n : ℕ}
    (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (w : InfinitePlace F) : Matrix (Fin n) (Fin n) ℂ :=
  fun a c => Θ (b a c) w

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
end

