module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCoefficientEmbeddingNormLeOfL1Bound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPhiHatIndPhi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesKaehlerBasis
section
open scoped TensorProduct Polynomial

namespace GlobalTheory.EtaleCoordSpread

open KaehlerDifferential TensorProduct

theorem fibre_bijective (B K : Type) [CommRing B] [Field K] [Algebra B K] (M : Type) [AddCommGroup M]
    [Module B M] [Module.Finite B M] (d : ℕ) (v : Fin d → M)
    (hd : Module.finrank K (K ⊗[B] M) = d)
    (hli : LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] v a)) :
    Function.Bijective (Finsupp.linearCombination (RingHom.ker (algebraMap B K)).ResidueField
      (fun a => (1 : (RingHom.ker (algebraMap B K)).ResidueField) ⊗ₜ[B] v a)) := by
  classical
  set p := RingHom.ker (algebraMap B K) with hp
  let φ : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap B K) le_rfl (fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact fun h => hx (RingHom.mem_ker.2 h))
  letI : Algebra p.ResidueField K := φ.toAlgebra
  haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap _ _ _ _ r).symm
  let e := AlgebraTensorModule.cancelBaseChange B p.ResidueField K K M
  have he : ∀ a, e ((1 : K) ⊗ₜ[p.ResidueField] ((1 : p.ResidueField) ⊗ₜ[B] v a)) = (1 : K) ⊗ₜ[B] v a :=
    fun a => by simp [e, AlgebraTensorModule.cancelBaseChange_tmul]
  have hfun : (e.symm.toLinearMap ∘ fun a => (1 : K) ⊗ₜ[B] v a) =
      fun a => (1 : K) ⊗ₜ[p.ResidueField] ((1 : p.ResidueField) ⊗ₜ[B] v a) := by
    funext a
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq, he]
  have hli2 : LinearIndependent K (fun a => (1 : K) ⊗ₜ[p.ResidueField] ((1 : p.ResidueField) ⊗ₜ[B] v a)) :=
    hfun ▸ hli.map' e.symm.toLinearMap (LinearEquiv.ker _)
  have hli3 : LinearIndependent p.ResidueField (fun a => (1 : p.ResidueField) ⊗ₜ[B] v a) := by
    haveI : FaithfulSMul p.ResidueField K := (faithfulSMul_iff_algebraMap_injective _ K).2 φ.injective
    exact LinearIndependent.of_comp (TensorProduct.mk p.ResidueField K (p.ResidueField ⊗[B] M) 1)
      (hli2.restrict_scalars' p.ResidueField)
  have hdim : Module.finrank p.ResidueField (p.ResidueField ⊗[B] M) = d := by
    rw [← hd, ← e.finrank_eq]
    exact (Module.finrank_baseChange (R := K) (S := p.ResidueField) (M' := p.ResidueField ⊗[B] M)).symm
  refine ⟨hli3, ?_⟩
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_finsupp_self, Fintype.card_fin]; exact hdim.symm)]
  exact hli3

theorem exists_away_etale : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.Smooth R B] (d : ℕ) (t : Fin d → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) → ∃ h : B, algebraMap B K h ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away h)) (fun a => algebraMap B (Localization.Away h) (t a))).Etale := by
  intro R B K _ _ _ _ _ _ d t hd hli
  classical
  have hbij := fibre_bijective B K Ω[B⁄R] d (fun a => D R B (t a)) hd hli
  obtain ⟨g, hg, hspan, hrel⟩ := GlobalTheory.FibreBasisSpread.exists_away_linearCombination_bijective B
    Ω[B⁄R] (Fin d) (fun a => D R B (t a)) (RingHom.ker (algebraMap B K)) hbij
  refine ⟨g, fun h0 => hg (RingHom.mem_ker.2 h0), ?_⟩
  let A := Localization.Away g
  haveI : Algebra.Smooth B A := Algebra.Smooth.of_isLocalization_Away g
  haveI : Algebra.Smooth R A := Algebra.Smooth.comp R B A
  let f := KaehlerDifferential.map R R B A
  haveI : IsLocalizedModule (Submonoid.powers g) f :=
    KaehlerDifferential.isLocalizedModule_map R B A (Submonoid.powers g)
  let w : Fin d → Ω[A⁄R] := fun a => D R A (algebraMap B A (t a))
  have hfw : ∀ a, f (D R B (t a)) = w a := fun a => KaehlerDifferential.map_D R R B A (t a)
  have hunit : ∀ s ∈ Submonoid.powers g, IsUnit (algebraMap B A s) := fun s hs =>
    IsLocalization.map_units A (⟨s, hs⟩ : Submonoid.powers g)
  have hsB : ∀ (s : B) (y : Ω[A⁄R]), s • y = algebraMap B A s • y := fun s y =>
    (algebraMap_smul A s y).symm

  have hsp : ⊤ ≤ Submodule.span A (Set.range w) := by
    intro y _
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalizedModule.surj (Submonoid.powers g) f y
    obtain ⟨n, c, hc⟩ := hspan x
    have h1 : ((g ^ n * s : B)) • y = Finsupp.linearCombination B (f ∘ fun a => D R B (t a)) c := by
      rw [mul_smul, Submonoid.smul_def] at *
      simp only at hxs
      rw [hxs, ← map_smul, hc, Finsupp.apply_linearCombination]
    have h2 : ((g ^ n * s : B)) • y ∈ Submodule.span A (Set.range w) := by
      rw [h1]
      refine Submodule.span_le_restrictScalars B A _ ?_
      rw [Finsupp.mem_span_range_iff_exists_finsupp]
      refine ⟨c, ?_⟩
      rw [Finsupp.linearCombination_apply]
      simp only [Function.comp_apply, hfw]
    rw [hsB] at h2
    obtain ⟨u, hu⟩ := hunit (g ^ n * s) (Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers g) n) s.2)
    have key : y = (↑u⁻¹ : A) • ((algebraMap B A (g ^ n * s)) • y) := by
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
    rw [key]
    exact Submodule.smul_mem _ _ h2

  have hliA : LinearIndependent A w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers g)
      (Finset.univ : Finset (Fin d)) a
    choose c hc using fun j => hbint j (Finset.mem_univ j)

    have h1 : f (∑ j, c j • D R B (t j)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul, hfw, hsB, hc]
      simp only [smul_assoc, ← Finset.smul_sum, ha, smul_zero]
    obtain ⟨⟨s, hs⟩, hs0⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers g) (f := f)
      (h1.trans (map_zero f).symm)
    rw [smul_zero] at hs0
    replace hs0 : s • (∑ j, c j • D R B (t j)) = 0 := hs0
    obtain ⟨n, hn⟩ := hrel (Finsupp.equivFunOnFinite.symm (fun j => s * c j)) (by
      simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype, mul_smul, ← Finset.smul_sum] using hs0)
    have hi : g ^ n * (s * c i) = 0 := by
      have := congrArg (fun x => x i) hn
      simpa using this
    have hci : algebraMap B A (c i) = 0 := by
      have hu := hunit (g ^ n * s) (Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers g) n) hs)
      rw [← hu.mul_right_eq_zero, ← map_mul, mul_assoc, hi, map_zero]
    rw [hc, Algebra.smul_def] at hci
    exact ((hunit b hb).mul_right_eq_zero).1 hci
  letI : Algebra (MvPolynomial (Fin d) R) A :=
    (MvPolynomial.eval₂Hom (algebraMap R A) (fun a => algebraMap B A (t a))).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin d) R) A :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R A r = MvPolynomial.eval₂Hom (algebraMap R A) _ (MvPolynomial.C r)
      simp
  refine GlobalTheory.EtaleCoordJacobian.etale_of_basis R A (Fin d) (Module.Basis.mk hliA hsp) fun i => ?_
  rw [Module.Basis.mk_apply]
  show D R A (algebraMap B A (t i)) = D R A (MvPolynomial.eval₂Hom (algebraMap R A)
    (fun a => algebraMap B A (t a)) (MvPolynomial.X i))
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]

end GlobalTheory.EtaleCoordSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBound
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovGmin

theorem petW_le_of_homN_le : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (G : WTZ D.host.E) (σ : Y.d.c₂.F →+* ℂ) (f : Rul Y.d.Xo₂ Y.d.c₂) (B : ℝ), 0 ≤ B → (∀ z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X k).Ψ D.R.r, z.2 ∈ ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X z.1).dom → AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f z ≤ B) → AllWt.petW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict G σ f ≤ B ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z G σ f ≤ B := by
  intro D T j Y G σ f B hB h
  have key : ∀ μ : MeasureTheory.Measure (AutQ (D.sp.W j)), μ Set.univ ≤ 1 →
      AllWt.petAt (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) (D.sp.W j) (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) μ G f ≤ B := by
    intro μ hμ
    rw [AllWt.petAt_eq]
    have hb : ∀ q : AutQ (D.sp.W j), ‖AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
        (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out)‖ₑ ≤ ENNReal.ofReal B := by
      intro q
      rw [Real.enorm_eq_ofReal (AllWt.homN_nonneg _ _ _ _ _)]
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out).2 ∈
          ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out).1).dom
      · exact h _ hz
      · have h0 : AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
            (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out) = 0 := by
          simp [AllWt.homN, AllWt.ptN, rdU, hz, ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm]
        rw [h0]; exact hB
    have h1 : MeasureTheory.eLpNorm' (fun q : AutQ (D.sp.W j) =>
        AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
          (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out)) 2 μ ≤
        MeasureTheory.eLpNorm' (fun _ : AutQ (D.sp.W j) => B) 2 μ := by
      apply MeasureTheory.eLpNorm'_mono_eNorm_ae (by norm_num)
      exact Filter.Eventually.of_forall (fun q => by simpa [Real.eNorm_eq_ofReal hB] using hb q)
    rw [MeasureTheory.eLpNorm'_const B (by norm_num), Real.eNorm_eq_ofReal hB] at h1
    have h2 : MeasureTheory.eLpNorm' (fun q : AutQ (D.sp.W j) =>
        AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
          (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out)) 2 μ ≤ ENNReal.ofReal B := by
      exact h1.trans ((mul_le_mul_right (ENNReal.rpow_le_one hμ (by positivity)) _).trans (by simp))
    exact ENNReal.toReal_le_of_le_ofReal hB h2
  refine ⟨key _ ?_, fun Z => key _ (AllWt.muPart_univ_le _ _ _)⟩
  rw [← AllWt.muPart_univ (D.sp.W j) (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ))]
  exact AllWt.muPart_univ_le _ _ _


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem nrm_le_of_eq_smul (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (G : WTZ D.host.E) (σ : Y.d.c₂.F →+* ℂ)
    (w : Y.V G) (f : Rul Y.d.Xo₂ Y.d.c₂) (Na : ℕ) (A B : ℝ) (hB : 0 ≤ B) (hA : (Na : ℝ) ≤ A)
    (hc : (w : Rul Y.d.Xo₂ Y.d.c₂) = (Na : Y.d.c₂.F) • f)
    (h : ∀ z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X k).Ψ D.R.r,
      z.2 ∈ ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X z.1).dom →
        AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f z ≤ B) :
    Y.nrm G σ w ≤ A * B ∧
      ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z G σ (w : Rul Y.d.Xo₂ Y.d.c₂) ≤ A * B := by
  obtain ⟨h1, h2⟩ := petW_le_of_homN_le D T j Y G σ f B hB h
  have hn1 : ‖σ (Na : Y.d.c₂.F)‖ = Na := by rw [map_natCast, Complex.norm_natCast]
  have hN0 : (0 : ℝ) ≤ Na := Nat.cast_nonneg _
  refine ⟨?_, fun Z => ?_⟩
  · show AllWt.petW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict G σ (w : Rul Y.d.Xo₂ Y.d.c₂) ≤ _
    rw [hc, AllWt.petW_smul, hn1]
    exact (mul_le_mul_of_nonneg_left h1 hN0).trans (mul_le_mul_of_nonneg_right hA hB)
  · rw [hc, AllWt.petOn_smul, hn1]
    exact (mul_le_mul_of_nonneg_left (h2 Z) hN0).trans (mul_le_mul_of_nonneg_right hA hB)

theorem span_eq_top_of_multiples {F M : Type*} [Field F] [CharZero F] [AddCommGroup M] [Module F M] (W : Submodule F M)
    (S S' : Set W) (hS : Submodule.span F S = ⊤) (Na : ℕ) (hNa : 0 < Na)
    (h : ∀ y ∈ S, ∃ s : F, s ≠ 0 ∧ ∀ y₁ : W, (y₁ : M) = s • (y : M) →
      ((Na • y₁ : W) : M) = (Na : F) • (s • (y : M)) → Na • y₁ ∈ S') :
    Submodule.span F S' = ⊤ := by
  rw [eq_top_iff, ← hS, Submodule.span_le]
  intro y hy
  obtain ⟨s, hs, hm⟩ := h y hy
  have hm' := hm (s • y) rfl (by rw [Nat.cast_smul_eq_nsmul]; rfl)
  have hNa' : ((Na : F)) ≠ 0 := by exact_mod_cast hNa.ne'
  have e1 : y = (s⁻¹ * (Na : F)⁻¹) • (Na • (s • y)) := by
    rw [← Nat.cast_smul_eq_nsmul F, smul_smul, smul_smul, mul_assoc s⁻¹, inv_mul_cancel₀ hNa', mul_one,
      inv_mul_cancel₀ hs, one_smul]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm')

theorem exp_consts (CA CB CC Q κ : ℝ) :
    Real.exp (CC * Q * κ) * (Real.exp (391 * Q * κ) * Real.exp (CA * Q * κ) * Real.exp (CB * Q * κ)) =
      Real.exp ((CA + CB + CC + 391) * Q * κ) := by
  simp only [← Real.exp_add]
  congr 1
  ring


end GlobalTheory.CovGmin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsAmplePowSectionsCuttingOutClosed
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CutOutSections

theorem sec_eq_zero_of_nonzeroLocus_eq_bot {Y : Scheme.{0}} [IsReduced Y] {M : LB Y} (s : M.Sec)
    (h : nonzeroLocus s = ⊥) : s = 0 := by
  apply DVR.SecOps.sec_ext
  intro k
  have hk : Y.basicOpen (s.f k) = ⊥ := le_bot_iff.1 ((basicOpen_le_nonzeroLocus s k).trans h.le)
  rw [AlgebraicGeometry.basicOpen_eq_bot_iff] at hk
  rw [hk]
  rfl

theorem eventually_isGenerated_lbPow {X : Scheme.{0}} {N : LB X} (hN : IsAmpleLB N) :
    ∀ᶠ k in atTop, IsGenerated (lbPow N k) := by
  refine (hN.eventually_isGenerated_tens_lbPow (LB.isLB_triv X)).mono fun k hk => ?_
  obtain ⟨c, u, hu⟩ := hk
  have hP := isLB_lbPow hN.isLB k
  have hT := isLB_tens (LB.isLB_triv X) hP
  obtain ⟨v, hv⟩ := CechPic.exists_generating_secs_of_cls_eq X _ _ hT hP
    (by simp only [CechPic.cls_tens (LB.isLB_triv X) hP, cls_triv, zero_add]) (Fin c) u hu
  exact ⟨c, v, hv⟩

theorem eventually_exists_secs_cutting_out : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∃ (r : ℕ) (κ : Fin r → (lbPow N l).Sec), (∀ i, GlobalTheory.secPull (κ i) (redι Z) = 0) ∧ (∀ i, ∀ y ∈ Z, y ∉ nonzeroLocus (κ i)) ∧ ∀ y, y ∉ Z → ∃ i, y ∈ nonzeroLocus (κ i) := by
  intro X _ _ p hp N Z hN
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  let U : X.Opens := ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩
  have hloc : ∀ y : U, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow N n).Sec, (y : X) ∈ nonzeroLocus s ∧
      nonzeroLocus s ≤ U ∧ IsAffineOpen (nonzeroLocus s) := fun y => hN.exists_affine_le y.2
  choose n hn s hys hle _ using hloc
  have hc : IsCompact (U : Set X) := NoetherianSpace.isCompact _
  obtain ⟨T, hT⟩ := hc.elim_finite_subcover (fun y : U => (nonzeroLocus (s y) : Set X))
    (fun y => (nonzeroLocus (s y)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hys ⟨y, hy⟩⟩)
  obtain ⟨m, -, t, ht⟩ := exists_common_pow (fun y : T => n y) (fun y => hn y) (fun y => s y)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_isGenerated_lbPow hN)
  refine eventually_atTop.2 ⟨K + m, fun l hl => ?_⟩
  obtain ⟨c, g, hg⟩ := hK (l - m) (by omega)
  have hml : m + (l - m) = l := by omega
  let κ' : T × Fin c → (lbPow N l).Sec := fun q => secCast hml (secMul (t q.1) (g q.2))
  have hκ' : ∀ q, nonzeroLocus (κ' q) = nonzeroLocus (s q.1) ⊓ nonzeroLocus (g q.2) := fun q => by
    simp only [κ', nonzeroLocus_secCast, nonzeroLocus_secMul, ht]
  have hb : ∀ q, ∀ y ∈ Z, y ∉ nonzeroLocus (κ' q) := fun q y hy h => by
    rw [hκ'] at h
    exact hle _ h.1 hy
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (T × Fin c)
  refine ⟨r, fun i => κ' (e.symm i), fun i => ?_, fun i => hb _, fun y hy => ?_⟩
  · have := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
    apply sec_eq_zero_of_nonzeroLocus_eq_bot
    rw [GlobalTheory.nonzeroLocus_secPull]
    refine le_bot_iff.1 fun z hz => ?_
    have hz' : redι Z z ∈ (Z : Set X) := by
      rw [← range_redι Z]
      exact Set.mem_range_self z
    exact hb _ _ hz' hz
  · obtain ⟨a, ha', hya'⟩ := Set.mem_iUnion₂.1 (hT hy)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hg.ge (Set.mem_univ y))
    refine ⟨e (⟨a, ha'⟩, j), ?_⟩
    show y ∈ nonzeroLocus (κ' (e.symm (e (⟨a, ha'⟩, j))))
    rw [e.symm_apply_apply, hκ']
    exact ⟨hya', hj⟩

end GlobalTheory.CutOutSections
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsLiftSectionOfAmplePowFromClosed
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftClosed
open GlobalTheory.QCoh GlobalTheory.Twist

theorem res_eq {X : Scheme.{0}} (I : X.IdealSheafData) {V W : X.Opens} (h : W ≤ V)
    (x : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)) :
    structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W)
      (resM ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) h
        ((structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ V)).symm x)) =
      (I.subscheme.presheaf.map (homOfLE (fun _ hz => h hz :
        I.subschemeι ⁻¹ᵁ W ≤ I.subschemeι ⁻¹ᵁ V)).op).hom x := rfl

theorem smul_eq {X : Scheme.{0}} (I : X.IdealSheafData) {W : X.Opens} (r : Γ(X, W))
    (m : Γ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme), W)) :
    structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W) (r • m) =
      (I.subschemeι.app W).hom r * structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W) m := rfl

theorem epi_toSubscheme {X : Scheme.{0}} (I : X.IdealSheafData) : Epi (toSubscheme I) := by
  rw [epi_iff_forall_affine]
  intro U hU y
  obtain ⟨f, hf⟩ := I.subschemeι_app_surjective ⟨U, hU⟩ ((structureModuleSectionsEquiv _) y)
  refine ⟨(structureModuleSectionsEquiv U).symm f, ?_⟩
  apply (structureModuleSectionsEquiv _).injective
  rw [← hf]
  rfl

theorem exists_twistSec_of_sec {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (σ : (M.pull I.subschemeι).Sec) :
    ∃ b : Γ(twist ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) M, ⊤),
    ∀ i, structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) (coord b i) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)) := by
  refine ⟨mkSec (fun i => (structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i))).symm
    ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))) ?_,
    fun i => ?_⟩
  · intro i j
    apply (structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j))).injective
    dsimp only
    rw [smul_eq, res_eq, res_eq]
    have hi : ∀ z ∈ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j), z ∈ (M.pull I.subschemeι).U (fun _ => i) :=
      fun z hz => (mem_pull (F := I.subschemeι)).2 hz.1.2
    have hj : ∀ z ∈ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j), z ∈ (M.pull I.subschemeι).U (fun _ => j) :=
      fun z hz => (mem_pull (F := I.subschemeι)).2 hz.2
    refine fn_ext fun z hz => ?_
    have e1 := gs_res (𝟙 I.subscheme) z (fun _ hz => hz.1 : I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j) ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) hz
      ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))
    have e1' := gs_res (𝟙 I.subscheme) z (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i)) hz.1 (σ.f (fun _ => i))
    have e2 := gs_res (𝟙 I.subscheme) z (fun _ hz => ⟨hz.1.1, hz.2⟩ : I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j) ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j)) hz
      ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => j)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j) ≤ (M.pull I.subschemeι).U (fun _ => j))).op).hom (σ.f (fun _ => j)))
    have e2' := gs_res (𝟙 I.subscheme) z (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => j)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j) ≤ (M.pull I.subschemeι).U (fun _ => j)) ⟨hz.1.1, hz.2⟩ (σ.f (fun _ => j))
    have hz' : I.subschemeι z ∈ M.U i ⊓ M.U j := ⟨hz.1.2, hz.2⟩
    have e3 := gs_pull (𝟙 I.subscheme) I.subschemeι z (⊤ ⊓ M.U i ⊓ M.U j) hz (resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (M.g i j : Γ(X, M.U i ⊓ M.U j)))
    have e4 := gs_res (𝟙 I.subscheme ≫ I.subschemeι) z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ⊤ ⊓ M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j) hz (M.g i j : Γ(X, M.U i ⊓ M.U j))
    have e5 := gs_unit (𝟙 I.subscheme ≫ I.subschemeι) z _ hz' (M.g i j)
    have e6 := gs_compat σ (𝟙 _) z (hi z hz) (hj z hz)
    have e7 := gm_pull_g M I.subschemeι (𝟙 _) z (fun _ => i) (fun _ => j) (hi z hz) (hj z hz)
    rw [gs_mul _ z _ hz]
    erw [e1, e1', e2, e2', e3, e4, e5, e6, e7]
  · exact LinearEquiv.apply_symm_apply _ _

theorem secPull_secOfTwist_eq {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (σ : (M.pull I.subschemeι).Sec)
    (b : Γ(twist ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) M, ⊤))
    (hb : ∀ i, structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) (coord b i) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))
    (a : Γ(twist (QCoh.structureModule X) M, ⊤)) (ha : (Twist.map M (toSubscheme I)).app ⊤ a = b) :
    GlobalTheory.secPull (Twist.secOfTwist (𝟙 _) a) I.subschemeι = σ := by
  refine DVR.SecOps.sec_ext fun J => ?_
  have h1 := hb (J PUnit.unit)
  rw [← ha, coord_map_app] at h1
  change (I.subschemeι.appLE _ _ _).hom (resG X _ (structureModuleSectionsEquiv _ (coord a (J PUnit.unit)))) = _

  set i := J PUnit.unit
  have h2 : (I.subschemeι.app (⊤ ⊓ M.U i)).hom (structureModuleSectionsEquiv _ (coord a i)) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f J) := h1
  have e3 : ∀ y : Γ(X, ⊤ ⊓ M.U i), (I.subschemeι.appLE (M.U i) ((M.pull I.subschemeι).U J)
      (fun z hz => (mem_pull (F := I.subschemeι)).1 hz)).hom (resG X (le_inf le_top le_rfl) y) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => ⟨trivial, (mem_pull (F := I.subschemeι)).1 hz⟩ :
        (M.pull I.subschemeι).U J ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i))).op).hom ((I.subschemeι.app _).hom y) := by
    intro y
    rw [← CommRingCat.comp_apply]
    erw [Scheme.Hom.map_appLE]
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  refine (e3 _).trans ?_
  rw [h2, ← CommRingCat.comp_apply, ← Functor.map_comp]
  exact (congrArg (fun q => (I.subscheme.presheaf.map q).hom (σ.f J)) (Subsingleton.elim _ (𝟙 _))).trans
    (by rw [CategoryTheory.Functor.map_id]; rfl)

theorem exists_secPull_eq_of_subsingleton {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (hM : M.IsLB)
    (h : Subsingleton (coh (twist (idealModule I) M) 1)) (σ : (M.pull I.subschemeι).Sec) :
    ∃ s : M.Sec, GlobalTheory.secPull s I.subschemeι = σ := by
  haveI := epi_toSubscheme I
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (idealModuleι I) (toSubscheme I) (Limits.kernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hsurj := cohOn.app_surjective (Twist.shortExact_map hM hS) ⊤ h
  obtain ⟨b, hb⟩ := exists_twistSec_of_sec I M σ
  obtain ⟨a, ha⟩ := hsurj b
  exact ⟨_, secPull_secOfTwist_eq I M σ b hb a ha⟩

theorem eventually_exists_secPull_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∀ σ : ((lbPow N l).pull (redι Z)).Sec, ∃ s : (lbPow N l).Sec, GlobalTheory.secPull s (redι Z) = σ := by
  intro X _ _ p hp N Z hN
  letI := algebraΓOfHom p
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  refine (hN.eventually_subsingleton_coh_twist (f := p) (fun _ => rfl)
    (idealModule (Scheme.IdealSheafData.vanishingIdeal Z))).mono fun l hl σ => ?_
  exact exists_secPull_eq_of_subsingleton _ _ (isLB_lbPow hN.isLB l) (hl 1 one_pos) σ

end GlobalTheory.LiftClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_field_point_through_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (L : Type) [Field L] (ρ : R →+* L) (y : Sp L ⟶ M.S), Function.Injective ρ → y ≫ M.π = spMap ρ → ∃ ga : FractionRing R →+* L, (∀ r, ga (algebraMap R _ r) = ρ r) ∧ y = spMap ga ≫ M.gp := by
  first | exact @GlobalTheory.Mum.Modif.factor_gp | exact GlobalTheory.Mum.Modif.factor_gp | (intros; apply GlobalTheory.Mum.Modif.factor_gp <;> assumption)
end

