module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierMalliavinFactorisationBasisStep
section
noncomputable section

open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic Set
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_dixmierMalliavin_step : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ (i : Fin d) (ε : ℝ), 0 < ε → ∃ (Λ' : List (Fin d) → (G → ℂ) → ℂ) (u v : ℝ → ℂ), SmFn h b μ S K Λ' ∧ ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ v ∧ tsupport u ⊆ Set.Icc (-ε) ε ∧ tsupport v ⊆ Set.Icc (-ε) ε ∧ ∀ f ∈ S, Λ [] f = (∫ t, u t * Λ' [] fun y => f (h.expG (t • b i) * y)) + ∫ t, v t * Λ [] fun y => f (h.expG (t • b i) * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hcont hinv K hK Λ hΛ i ε hε
  obtain ⟨M, hM0, hMb, hser⟩ := _root_.GlobalTheory.HCA.smFn_tsum_replicate 𝔸 G 𝔤 h d b μ hμ S hcont hinv K hK Λ hΛ i
  obtain ⟨c, u, v, hu, hv, hus, hvs, hc, hid⟩ := exists_dixmierMalliavin_line M hε
  refine ⟨fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f, u, v,
    hser c hc, hu, hv, hus, hvs, fun f hf => ?_⟩
  have hmem : ∀ t : ℝ, (fun y => f (h.expG (t • b i) * y)) ∈ S := fun t => hinv f hf _
  set F : ℝ → ℂ := fun t => Λ [] fun y => f (h.expG (t • b i) * y) with hFdef
  obtain ⟨hF, hD'⟩ := _root_.GlobalTheory.HCA.smFn_contDiff_line 𝔸 G 𝔤 h d b μ hμ S hcont hinv K hK Λ hΛ [] i f hf
  have hD : ∀ p t, iteratedDeriv p F t = Λ (List.replicate p i) fun y => f (h.expG (t • b i) * y) := by
    intro p t; rw [hD' p t, List.append_nil]

  have hfc : Continuous f := hcont f hf
  have hjc : Continuous fun q : ℝ × G => f (h.expG (q.1 • b i) * q.2) :=
    hfc.comp ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_snd)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hjc.continuousOn
  set B : ℝ := max C 0 * μ.real K with hB
  have hB0 : 0 ≤ B := mul_nonneg (le_max_right _ _) measureReal_nonneg
  have hKint : ∀ t ∈ Icc (-ε) ε, (∫ x in K, ‖f (h.expG (t • b i) * x)‖ ∂μ) ≤ B := by
    intro t ht
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := K) (C := max C 0)
      (f := fun x => ‖f (h.expG (t • b i) * x)‖) hK.measure_lt_top (fun x hx => by
        rw [norm_norm]; exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _))
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at this
    exact this
  have hDb : ∀ p, ∀ t ∈ Icc (-ε) ε, ‖iteratedDeriv p F t‖ ≤ M p * B := by
    intro p t ht
    rw [hD]
    exact (hMb p _ (hmem t)).trans (mul_le_mul_of_nonneg_left (hKint t ht) (hM0 p))

  set a : ℂ := ((B + 1 : ℝ) : ℂ)⁻¹ with ha
  have hB1 : (0 : ℝ) < B + 1 := by linarith
  have ha0 : a ≠ 0 := inv_ne_zero (by exact_mod_cast hB1.ne')
  have hFa : ContDiff ℝ ∞ fun t => a * F t := contDiff_const.mul hF
  have hDa : ∀ p t, iteratedDeriv p (fun t => a * F t) t = a * iteratedDeriv p F t := by
    intro p t
    exact iteratedDeriv_const_mul a (hF.contDiffAt.of_le (by exact_mod_cast le_top))
  have key := hid (fun t => a * F t) hFa (fun p t ht => by
    rw [hDa, norm_mul, ha, norm_inv, Complex.norm_real, Real.norm_of_nonneg hB1.le]
    rw [inv_mul_le_iff₀ hB1]
    calc ‖iteratedDeriv p F t‖ ≤ M p * B := hDb p t ht
      _ ≤ (B + 1) * M p := by nlinarith [hM0 p])
  simp_rw [hDa] at key
  have e1 : ∀ p, (c p : ℂ) * ∫ t, a * iteratedDeriv p F t * u t = a * ((c p : ℂ) * ∫ t, iteratedDeriv p F t * u t) := by
    intro p
    simp_rw [mul_assoc a, integral_const_mul]; ring
  have e2 : ∫ t, a * F t * v t = a * ∫ t, F t * v t := by
    rw [← integral_const_mul a]; simp_rw [mul_assoc]
  simp_rw [e1] at key
  rw [e2, tsum_mul_left, ← mul_add] at key
  have key' := mul_left_cancel₀ ha0 key
  have hF0 : F 0 = Λ [] f := by
    simp only [hFdef, zero_smul]; rw [h.expG_zero]; simp only [one_mul]
  rw [← hF0, key']
  congr 1
  · have hugc : HasCompactSupport u := isCompact_Icc.of_isClosed_subset (isClosed_tsupport u) hus
    have hcD : ∀ p, Continuous (fun t => iteratedDeriv p F t) := fun p =>
      hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
    let T : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (iteratedDeriv p F t * u t)
    have hTi : ∀ p, Integrable (T p) := fun p =>
      (((hcD p).mul hu.continuous).integrable_of_hasCompactSupport hugc.mul_left).const_mul _
    have hTb : ∀ p t, ‖T p t‖ ≤ |c p| * M p * (B * ‖u t‖) := by
      intro p t
      by_cases ht : t ∈ tsupport u
      · simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have := hDb p t (hus ht)
        calc |c p| * (‖iteratedDeriv p F t‖ * ‖u t‖) ≤ |c p| * ((M p * B) * ‖u t‖) := by gcongr
          _ = |c p| * M p * (B * ‖u t‖) := by ring
      · have hu0 : u t = 0 := image_eq_zero_of_notMem_tsupport ht
        simp only [T, hu0, mul_zero, norm_zero, le_refl]
    have hgi : Integrable (fun t => B * ‖u t‖) :=
      (hu.continuous.integrable_of_hasCompactSupport hugc).norm.const_mul _
    have hsum : Summable fun p => ∫ t, ‖T p t‖ := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, B * ‖u t‖))
      rw [← integral_const_mul]
      exact integral_mono (hTi p).norm (hgi.const_mul _) (fun t => hTb p t)
    have e3 : ∀ p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * u t = ∫ t, T p t := fun p =>
      (integral_const_mul _ _).symm
    simp_rw [e3]
    rw [integral_tsum_of_summable_integral_norm hTi hsum]
    congr 1
    funext t
    rw [← tsum_mul_left]
    congr 1
    funext p
    dsimp only [T, List.nil_append]
    rw [hD]
    ring
  · congr 1; funext t; rw [mul_comm]

end GlobalTheory.HCA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeBaseSeparablePointIntegralClosure
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlargePoint

theorem enlarge_point : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginEnlarge.PointAtZero A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hRet
  obtain ⟨hi, _hil, _hqA, _hQA, _hjA, _hψA, hTor⟩ := hFits
  have hu : ∀ y : Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A),
      IsUnit (((algebraMap A (FractionRing A)).comp ρ) (y : Localization.AtPrime QA)) := by
    rintro ⟨y, a, ha, rfl⟩
    have h1 : ρ (algebraMap A (Localization.AtPrime QA) a) = a := by
      simpa using congrArg (fun f => f a) hRet.1
    simp only [RingHom.comp_apply, h1]
    exact IsLocalization.map_units (FractionRing A) (⟨a, ha⟩ : nonZeroDivisors A)
  let ρK : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* FractionRing A := IsLocalization.lift hu
  have hρK : ρK.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap A (FractionRing A)).comp ρ := IsLocalization.lift_comp hu
  obtain ⟨L, _, _, _, _, σL, hσL⟩ := GlobalTheory.T.zmodTorsor_exists_point_finite_separable _ (FractionRing A) ρK DA q hq actA hTor
  obtain ⟨A₁, _, _, _, _, _, _, j, i₁, hj, hi₁, hl₁, hji, κ, hκ⟩ := GlobalTheory.T.exists_normal_local_between_alt T hAIC A i hi L
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, actA₁, ρ₁, hF₁, hR₁, β, h, hβ, hh, hσ⟩ :=
    GlobalTheory.T.exists_baseChange_fittingDatum_retraction T O P φ hφ hSH hP q hq A i EA QA jA ψA DA actA ⟨hi, _hil, _hqA, _hQA, _hjA, _hψA, hTor⟩ ρ hRet
      A₁ j i₁ hj hi₁ hl₁ hji
  obtain ⟨σ₁, hσ₁⟩ := hσ (κ.comp σL) (by
    ext x
    have h1 := congrArg (fun f => f (algebraMap (Localization.AtPrime QA)
      (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) x)) hσL
    have h2 := congrArg (fun f => f x) hρK
    have h3 := congrArg (fun f => f (ρ x)) hκ
    simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3])
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁,
    EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance, jA₁, ψA₁,
    DA₁, inferInstance, inferInstance, actA₁, hF₁, ⟨ρ₁, hR₁, ?_⟩, β, h, hβ, hh⟩
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ (Localization.AtPrime QA₁) DA₁
  refine ⟨σ₁.comp (GlobalTheory.KeyOriginNoeth.closure A₁ (Localization.AtPrime QA₁) DA₁).subtype, ?_⟩
  ext r
  exact congrArg (fun f => f r) hσ₁

end GlobalTheory.KeyOriginEnlargePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle :
    ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X)
      (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F),
      cobd (R := R) (E := cech f) (n := 1) s = 0 →
      ∀ x : H R (sch.obj X) F ((1 : ℕ) : ℤ),
        IsCls (R := R) (E := cech f) (n := 1) s (pull R (cechAug f) F ((1 : ℕ) : ℤ) x) →
        pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  intro R _ F Y X f s hs x hx
  have hc := congrArg (fun t => (free R).map ((cechDiag f).app (op ⦋2⦌)) ≫ t) hs
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul, ← Functor.map_comp_assoc,
    cechDiag_δ, comp_zero] at hc
  have hc' : ((free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s :
      (free R).obj ((sch.obj Y).obj (op ⦋2⦌)) ⟶ F) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hd : (free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s = 0 := hc'
  obtain ⟨z, hzClass, hz⟩ := hx
  rw [← cechDiag_aug f, pull_comp, ← hzClass]
  simp only [pull, HK.pull, HK.pre, cpre_mk]
  rw [← CohomologyClass.mk_zero]
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  change (Cochain.ofHom ((chains R).map (cechDiag f))).comp z.1 (zero_add _) = 0
  rw [hz, ClsBasic.ofHom_comp_single]
  simp only [← Category.assoc, ClsBasic.chainsXIso_nat]
  simp [Category.assoc, hd]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatFilteredColimitFiniteType
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EtFFApprox

variable {J : Type} [SmallCategory J] (D0 : J ⥤ CommRingCat.{0}) (j : J) {B' : CommRingCat.{0}} (g' : D0.obj j ⟶ B')

def pmap {k k' : Under j} (φ : k ⟶ k') : pushout g' (D0.map k.hom) ⟶ pushout g' (D0.map k'.hom) :=
  pushout.desc (pushout.inl _ _) (D0.map φ.right ≫ pushout.inr _ _)
    (by rw [pushout.condition, ← Category.assoc, ← D0.map_comp, Under.w φ])

@[reassoc (attr := simp)] lemma inl_pmap {k k' : Under j} (φ : k ⟶ k') :
    pushout.inl _ _ ≫ pmap D0 j g' φ = pushout.inl _ _ := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] lemma inr_pmap {k k' : Under j} (φ : k ⟶ k') :
    pushout.inr _ _ ≫ pmap D0 j g' φ = D0.map φ.right ≫ pushout.inr _ _ := pushout.inr_desc _ _ _

def arrF : Under j ⥤ Arrow CommRingCat.{0} where
  obj k := Arrow.mk (pushout.inr g' (D0.map k.hom))
  map {k k'} φ := Arrow.homMk' (D0.map φ.right) (pmap D0 j g' φ) (inr_pmap D0 j g' φ).symm
  map_id k := by
    ext : 1
    · simp
    · apply pushout.hom_ext <;> simp
  map_comp φ ψ := by
    ext : 1
    · simp
    · apply pushout.hom_ext <;> simp

@[simp] lemma arrF_map_left {k k' : Under j} (φ : k ⟶ k') : ((arrF D0 j g').map φ).left = D0.map φ.right := rfl
@[simp] lemma arrF_map_right {k k' : Under j} (φ : k ⟶ k') : ((arrF D0 j g').map φ).right = pmap D0 j g' φ := rfl

variable {A B : CommRingCat.{0}} (ι0 : D0 ⟶ (Functor.const J).obj A) (g : A ⟶ B) (h : B' ⟶ B)
  (hnat : ∀ k : Under j, g' ≫ h = D0.map k.hom ≫ ι0.app k.right ≫ g)

def pdesc (k : Under j) : pushout g' (D0.map k.hom) ⟶ B := pushout.desc h (ι0.app k.right ≫ g) (hnat k)

def coc : arrF D0 j g' ⟶ (Functor.const (Under j)).obj (Arrow.mk g) where
  app k := Arrow.homMk (f := (arrF D0 j g').obj k) (g := Arrow.mk g) (ι0.app k.right) (pdesc D0 j g' ι0 g h hnat k)
    (pushout.inr_desc _ _ (hnat k)).symm
  naturality k k' φ := by
    ext : 1
    · simp only [Arrow.comp_left, Functor.const_obj_map, Arrow.id_left, Category.comp_id, Arrow.homMk_left, arrF_map_left]
      rw [ι0.naturality φ.right]
      simp
    · simp only [Arrow.comp_right, Functor.const_obj_map, Arrow.id_right, Category.comp_id, Arrow.homMk_right, arrF_map_right]
      apply pushout.hom_ext
      · simp [pdesc]
      · simp only [pdesc, inr_pmap_assoc, pushout.inr_desc]
        rw [ι0.naturality_assoc φ.right]
        simp

lemma snd_coc (k : Under j) : (Comma.snd (𝟭 _) (𝟭 _)).map ((coc D0 j g' ι0 g h hnat).app k) = pdesc D0 j g' ι0 g h hnat k := rfl

@[reassoc] lemma inl_pdesc (k : Under j) : pushout.inl _ _ ≫ pdesc D0 j g' ι0 g h hnat k = h := pushout.inl_desc _ _ _
@[reassoc] lemma inr_pdesc (k : Under j) : pushout.inr _ _ ≫ pdesc D0 j g' ι0 g h hnat k = ι0.app k.right ≫ g := pushout.inr_desc _ _ _

def leftOf (s : Cocone (arrF D0 j g' ⋙ Comma.snd (𝟭 _) (𝟭 _))) : Cocone (Under.forget j ⋙ D0) where
  pt := s.pt
  ι := { app := fun k => pushout.inr g' (D0.map k.hom) ≫ s.ι.app k
         naturality := fun k k' φ => by
           have hw := s.w φ
           simp only [Functor.comp_map, Comma.snd_map] at hw
           dsimp
           rw [← hw, Category.comp_id]
           simp }

@[simp] lemma leftOf_ι_app (s : Cocone (arrF D0 j g' ⋙ Comma.snd (𝟭 _) (𝟭 _))) (k : Under j) :
    (leftOf D0 j g' s).ι.app k = pushout.inr g' (D0.map k.hom) ≫ s.ι.app k := rfl

def rightIsColimit (hP : IsPushout g' (ι0.app j) h g) (hL : IsColimit ((Cocone.mk A ι0).whisker (Under.forget j))) :
    IsColimit ((Comma.snd (𝟭 _) (𝟭 _)).mapCocone (Cocone.mk (Arrow.mk g) (coc D0 j g' ι0 g h hnat))) where
  desc s := hP.desc (pushout.inl _ _ ≫ s.ι.app (Under.mk (𝟙 j))) (hL.desc (leftOf D0 j g' s)) (by
      have := hL.fac (leftOf D0 j g' s) (Under.mk (𝟙 j))
      simp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Under.forget_obj, leftOf_ι_app] at this
      rw [pushout.condition_assoc]
      simp only [Under.mk_right] at this
      rw [this]
      simp)
  fac s k := by
    change pdesc D0 j g' ι0 g h hnat k ≫ _ = s.ι.app k
    apply pushout.hom_ext
    · have hw := s.w (Under.homMk k.hom (by simp) : Under.mk (𝟙 j) ⟶ k)
      simp only [Functor.comp_map, Comma.snd_map, arrF_map_right] at hw
      rw [inl_pdesc_assoc, IsPushout.inl_desc, ← hw]
      exact inl_pmap_assoc D0 j g' _ _
    · have := hL.fac (leftOf D0 j g' s) k
      simp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Under.forget_obj, leftOf_ι_app] at this
      rw [inr_pdesc_assoc, IsPushout.inr_desc, this]
  uniq s m hm := by
    apply hP.hom_ext
    · rw [IsPushout.inl_desc]
      have h1 := hm (Under.mk (𝟙 j))
      change pdesc D0 j g' ι0 g h hnat (Under.mk (𝟙 j)) ≫ m = s.ι.app (Under.mk (𝟙 j)) at h1
      rw [← h1, inl_pdesc_assoc]
    · rw [IsPushout.inr_desc]
      apply hL.hom_ext
      intro k
      have h1 := hL.fac (leftOf D0 j g' s) k
      have h2 := hm k
      change ι0.app k.right ≫ _ = pushout.inr g' (D0.map k.hom) ≫ s.ι.app k at h1
      change pdesc D0 j g' ι0 g h hnat k ≫ m = s.ι.app k at h2
      change ι0.app k.right ≫ _ = ι0.app k.right ≫ _
      rw [h1, ← h2, inr_pdesc_assoc]

end GlobalTheory.EtFFApprox


open GlobalTheory.EtFFApprox in
theorem GlobalTheory.EtC.etFF_filtered_colimit_finiteType : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Arrow CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj (Arrow.mk g)), Nonempty (IsColimit (Cocone.mk (Arrow.mk g) ι)) ∧ ∀ j, EtFF (D.obj j).hom ∧ Algebra.FiniteType ℤ (D.obj j).left ∧ Algebra.FiniteType ℤ (D.obj j).right := by
  intro A B g hg
  obtain ⟨J, _, _, D0, ι0, ⟨hc⟩, hft⟩ := GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType A
  obtain ⟨j, B', g', h, hg', hP⟩ := GlobalTheory.T.etaleFaithfullyFlat_descends_of_isColimit J D0 (Cocone.mk A ι0) hc B g hg
  have hb := GlobalTheory.EtC.etFF_basic
  haveI := hb.1.2.1
  have hP' : IsPushout g' (ι0.app j) h g := hP
  have hL : IsColimit ((Cocone.mk A ι0).whisker (Under.forget j)) :=
    (Functor.Final.isColimitWhiskerEquiv (Under.forget j) _).symm hc
  have hnat : ∀ (k : Under j), g' ≫ h = D0.map k.hom ≫ ι0.app k.right ≫ g := by
    intro k
    rw [← Category.assoc, ι0.naturality k.hom]
    simpa using hP'.w
  refine ⟨Under j, inferInstance, inferInstance, arrF D0 j g', coc D0 j g' ι0 g h hnat, ⟨?_⟩, fun k => ?_⟩
  · exact Comma.fstSndJointlyReflectColimit hL (rightIsColimit D0 j g' ι0 g h hnat hP' hL)
  · have hk : EtFF (pushout.inr g' (D0.map k.hom)) :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout (IsPushout.of_hasPushout g' (D0.map k.hom)).flip hg'
    exact ⟨hk, hft k.right, hb.2.2 _ _ _ hk (hft k.right)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTorsorOfFractionFieldsStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_integralClosure_torsor_of_fraction_fields : (∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M))) →
  ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA)).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginBC.BC β DA))) := by
  first | (exact @GlobalTheory.KeyOriginTransport.etale_closure_of_field) | (exact GlobalTheory.KeyOriginTransport.etale_closure_of_field) | (intros; apply GlobalTheory.KeyOriginTransport.etale_closure_of_field  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeRightEpiStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleMayerVietoris_free_right_epi : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → Epi (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) := by
  first | (exact @GlobalTheory.EtC.MVEpi.mv_right_epi) | (exact GlobalTheory.EtC.MVEpi.mv_right_epi) | (intros; apply GlobalTheory.EtC.MVEpi.mv_right_epi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleModuleSheafSectionsCoprodBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → Function.Bijective (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) := by
  first | (exact @GlobalTheory.EtC.sec_coprod) | (exact GlobalTheory.EtC.sec_coprod) | (intros; apply GlobalTheory.EtC.sec_coprod  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodKernelLocallyMultipleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafExtendScalars_zmod_kernel_locally_multiple : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (x : Sec M U), extSh.sec (ZMod.castHom hq (ZMod q)) M U x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  first | (exact @GlobalTheory.EtC.extSh_sec_eq_zero_loc) | (exact GlobalTheory.EtC.extSh_sec_eq_zero_loc) | (intros; apply GlobalTheory.EtC.extSh_sec_eq_zero_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodSectionLocallyTmulStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafExtendScalars_zmod_section_locally_tmul : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (y : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj M) U), Loc U fun V g => ∃ x : Sec M V, extSh.sec (ZMod.castHom hq (ZMod q)) M V x = Sec.res g y := by
  first | (exact @GlobalTheory.EtC.ExtOnto.ext_onto) | (exact GlobalTheory.EtC.ExtOnto.ext_onto) | (intros; apply GlobalTheory.EtC.ExtOnto.ext_onto  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.exactIff) | (exact GlobalTheory.EtC.exactIff) | (intros; apply GlobalTheory.EtC.exactIff  <;> assumption)
end

