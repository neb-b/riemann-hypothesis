module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientConjugateThetaForm
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0181
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralQuotientOfValuationSubringAboveDvr
section
set_option autoImplicit false

noncomputable section

open Polynomial GlobalTheory.Published.AbVarRed IsLocalRing

namespace GlobalTheory.ValAbove

theorem partialSum_mul_pow_mem {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (c : ℕ → R) (n : ℕ)
    (x : Ω) (h : ∑ i ∈ Finset.range (n + 1), c i • x ^ i = 0) {m t : ℕ} (hm : m ≤ n) (ht : t ≤ n + 1) :
    (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n) := by
  have hmem : ∀ e, e ≤ n → ∀ r : R, r • x ^ e ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n) := by
    intro e he r
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_image_of_mem _ (Set.mem_Iic.2 he)
  by_cases htm : t < m
  · rw [Finset.sum_mul]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [smul_mul_assoc, ← pow_add]
    exact hmem _ (by omega) _
  · push_neg at htm
    have hsplit := Finset.sum_range_add_sum_Ico (fun i => c i • x ^ i) (show m ≤ n + 1 by omega)
    rw [h] at hsplit
    have e1 : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t
        = (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ i) * x ^ (t - m) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      rw [smul_mul_assoc, smul_mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega
    have key : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t
        = -∑ i ∈ Finset.range m, c i • x ^ (i + (t - m)) := by
      rw [e1, eq_neg_of_add_eq_zero_right hsplit, neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, ← pow_add]
    rw [key]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    rw [Finset.mem_range] at hi
    exact hmem _ (by omega) _

theorem isIntegral_of_mul_pow_mem {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (n : ℕ) (x z : Ω)
    (hz : ∀ t ≤ n, z * x ^ t ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) :
    IsIntegral R z := by
  refine isIntegral_of_smul_mem_submodule
    (Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) ?_ (Submodule.fg_span ((Set.finite_Iic n).image _)) z ?_
  · rw [Ne, Submodule.span_eq_bot]
    push_neg
    refine ⟨1, ?_, one_ne_zero⟩
    exact ⟨0, Set.mem_Iic.2 (Nat.zero_le n), pow_zero x⟩
  · intro w hw
    refine Submodule.span_induction (fun w hw => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [smul_add]; exact Submodule.add_mem _ ha hb)
      (fun r a _ ha => by rw [smul_eq_mul, mul_smul_comm]; exact Submodule.smul_mem _ r ha) hw
    obtain ⟨t, ht, rfl⟩ := hw
    rw [Set.mem_Iic] at ht
    rw [smul_eq_mul]
    exact hz t (by omega)

theorem exists_integral_mul_eq_of_isAbove : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ y ∈ V, ∃ a s : Ω,
      ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem a ∧
      ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem s ∧ V.valuation s = 1 ∧ y * s = a := by
  intro R K Ω _ _ _ _ _ _ _ _ _ V hV y hy
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hιinj : Function.Injective ((algebraMap K Ω).comp (algebraMap R K)) :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hmemV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact this
  have hle : ∀ r : R, V.valuation (algebraMap R Ω r) ≤ 1 := fun r => (V.valuation_le_one_iff _).2 (hmemV r)
  have hlt : ∀ r : R, ¬ IsUnit r → V.valuation (algebraMap R Ω r) < 1 := by
    intro r hr
    refine lt_of_le_of_ne (hle r) fun h1 => hr ?_
    have h0 : algebraMap R Ω r ≠ 0 := by
      intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
    have hinv : (algebraMap R Ω r)⁻¹ ∈ V := (V.valuation_le_one_iff _).1 (by rw [map_inv₀, h1, inv_one])
    have hK : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω ((algebraMap R K r)⁻¹) ∈ V
      rw [map_inv₀]; exact hinv
    rw [hV] at hK
    obtain ⟨r', hr'⟩ := hK
    have hrK : algebraMap R K r ≠ 0 := by
      intro h; apply h0; change algebraMap K Ω (algebraMap R K r) = 0; rw [h, map_zero]
    have hrr : r * r' = 1 :=
      IsFractionRing.injective R K (by rw [map_mul, hr', mul_inv_cancel₀ hrK, map_one])
    exact ⟨⟨r, r', hrr, by rw [mul_comm, hrr]⟩, rfl⟩
  have hunit : ∀ r : R, IsUnit r → V.valuation (algebraMap R Ω r) = 1 := by
    intro r hr
    obtain ⟨u, rfl⟩ := hr
    have h := congrArg (fun w => V.valuation (algebraMap R Ω w)) u.mul_inv
    simp only [map_mul, map_one] at h
    refine le_antisymm (hle _) ?_
    by_contra hlt'
    push_neg at hlt'
    have : V.valuation (algebraMap R Ω ↑u) * V.valuation (algebraMap R Ω ↑u⁻¹) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' (hle _)) hlt'
    rw [h] at this
    exact lt_irrefl _ this

  classical
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have halgK : IsAlgebraic K y := Algebra.IsAlgebraic.isAlgebraic y
  have halgR : IsAlgebraic R y := (IsFractionRing.isAlgebraic_iff R K Ω).2 halgK
  obtain ⟨f, hf0, hfy⟩ := halgR
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hex : ∃ e : ℕ, ¬ (C (ϖ ^ (e + 1)) ∣ f) := by
    have hc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hf0
    obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    refine ⟨e, fun hd => ?_⟩
    have hd' : ϖ ^ e * ϖ ∣ ϖ ^ e * (u : R) := by
      rw [← pow_succ, mul_comm]; rw [← hu]
      exact (C_dvd_iff_dvd_coeff _ _).1 hd _
    have : ϖ ∣ (u : R) := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).1 hd'
    exact hϖ.not_isUnit (isUnit_of_dvd_unit this u.isUnit)
  have hdiv : ∀ e, (∀ k < e, ¬ ¬ (C (ϖ ^ (k + 1)) ∣ f)) → C (ϖ ^ e) ∣ f := by
    intro e he
    cases e with
    | zero => simp
    | succ k => exact not_not.1 (he k (Nat.lt_succ_self k))
  obtain ⟨g, hg⟩ := hdiv (Nat.find hex) (fun k hk => Nat.find_min hex hk)
  have hgunit : ∃ i, IsUnit (g.coeff i) := by
    by_contra hno
    push_neg at hno
    apply Nat.find_spec hex
    have hmax : maximalIdeal R = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    have hCg : C ϖ ∣ g := (C_dvd_iff_dvd_coeff _ _).2 fun i => by
      have : g.coeff i ∈ maximalIdeal R := (mem_maximalIdeal _).2 (hno i)
      rw [hmax] at this
      exact Ideal.mem_span_singleton.1 this
    have h2 := mul_dvd_mul_left (C (ϖ ^ Nat.find hex)) hCg
    rw [← hg, ← C_mul, ← pow_succ] at h2
    exact h2
  have hgy : aeval y g = 0 := by
    rw [hg, map_mul, aeval_C] at hfy
    refine (mul_eq_zero.1 hfy).resolve_left ?_
    exact fun h => pow_ne_zero _ hϖ.ne_zero (hιinj (h.trans (map_zero _).symm))
  set n := g.natDegree with hn
  set c := g.coeff with hc
  have hsum : ∑ i ∈ Finset.range (n + 1), c i • y ^ i = 0 := by
    rw [← hgy, aeval_eq_sum_range]
  obtain ⟨i₀, hi₀⟩ := hgunit
  have hS : ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).Nonempty :=
    ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hi₀.ne_zero)), hi₀⟩⟩
  set j := ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).max' hS with hj
  have hjmem := Finset.max'_mem _ hS
  rw [← hj, Finset.mem_filter, Finset.mem_range] at hjmem
  have hjn : j ≤ n := Nat.le_of_lt_succ hjmem.1
  have hbig : ∀ i, j < i → i ≤ n → ¬ IsUnit (c i) := by
    intro i hji hin hu
    have := Finset.le_max' ((Finset.range (n + 1)).filter fun i => IsUnit (c i)) i
      (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hu⟩)
    rw [← hj] at this
    omega
  set b := ∑ i ∈ Finset.Ico j (n + 1), c i • y ^ (i - j) with hb
  have hyle : V.valuation y ≤ 1 := (V.valuation_le_one_iff y).2 hy
  have hvb : V.valuation b = 1 := by
    rw [hb, Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hjn), Nat.sub_self, pow_zero, Algebra.smul_def,
      mul_one, add_comm]
    rw [Valuation.map_add_eq_of_lt_right, hunit _ hjmem.2]
    rw [hunit _ hjmem.2]
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [Algebra.smul_def, map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hyle _)) (hlt _ (hbig i (by omega) (by omega)))
  refine ⟨y * b, b, ?_, ?_, hvb, rfl⟩
  · exact isIntegral_of_mul_pow_mem n y (y * b) fun t ht => by
      rw [show y * b * y ^ t = b * y ^ (t + 1) by ring]
      exact partialSum_mul_pow_mem c n y hsum hjn (by omega)
  · exact isIntegral_of_mul_pow_mem n y b fun t ht => partialSum_mul_pow_mem c n y hsum hjn (by omega)

end GlobalTheory.ValAbove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIoConjOfFive
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedWeights


open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift in
theorem exists_io_conj_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → HypConj R i σ μ' η' → ∀ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ io, IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ B f) (deltaConj i σ) io := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ _ μ' η' _ hH c c₁ hc ω f₀ f B hω hv
  have hM := hR.models
  have hθ : IsInfFam R.θ := hM.inf
  have hψ : IsStdChar D R.ψ (-1) := hv.vec.1.1
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f :=
    hv.vec.2.elim fun _ h => isThetaFunO_of_isThetaAt hψ hθ h.2 hv.vec.1.2.theta
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => onb_eq_one (hM.BV i τ)
  have hBu : ∀ τ, IsUnit (R.BV i τ) := fun τ => (IsUnit.of_mul_eq_one_right _ (hBS τ))
  have hw := fun ρ => weights_label D i (lab σ ρ) (pW D i ρ) (qW D i ρ)
    (congrArg Prod.fst ((hH.sig ρ).trans (hH.sig _).symm)) (congrArg Prod.snd ((hH.sig ρ).trans (hH.sig _).symm))
    ((R.MW i σ).lam ρ) ((R.MW i σ).ε ρ) (by have := (R.MW i σ).enum ρ; rw [hH.par ρ] at this; exact this)
  choose x₁ x₂ x₃ hx₁ hx₂ hx₃ hK hU hpq hε hap ham using hw
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hj := exists_poly_model (Vc D i) R.θ c (lamV D i) σ (Equiv.ofBijective _ hH.lab_bij) hH.lab_at c₁ hθ
    hc.coef hc.act hc.indep hc.span (R.BV i) hBu
  obtain ⟨j, hj1, hj2⟩ := hj
  exact exists_isIoW D (Vc D i) (Wc D i) R.ψ R.θ _ (R.MW i σ) c (lamV D i) (Equiv.ofBijective _ hH.lab_bij) (R.BV i) B
    j hj1 hj2 _ _ _ _ x₁ x₂ x₃ (hrk.le.trans (r_le_V i)) hpq hε hap ham hK hU _ _ ω hω hψ hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS hv.onb _ _ hH.mu_inf
    (fun τ => GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hH.mu_inf τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hH.eta_inf τ)))
    hx₁ hx₂ hx₃ f hth (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv.vec hth)

end GlobalTheory.MovedWeights

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGenIsoPullbackLineBundleZpow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullPow

variable {X Y Z : Scheme.{0}}

theorem pull_pw_g (H : LB X) (g : Z ⟶ X) (n : ℤ) (i j : ((GlobalTheory.AbLaw.pw H n).pull g).ι) :
    ((GlobalTheory.AbLaw.pw H n).pull g).g i j = ((H.pull g).g i j) ^ n := by
  show (∏ k : PUnit, _) = (∏ k : PUnit, _) ^ n
  erw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
  erw [map_zpow, map_zpow]
  rfl

theorem div_pull_pw_g (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y) (n : ℤ)
    (p q : (LB.div ((GlobalTheory.AbLaw.pw H n).pull g) ((GlobalTheory.AbLaw.pw M n).pull f)).ι) :
    (LB.div ((GlobalTheory.AbLaw.pw H n).pull g) ((GlobalTheory.AbLaw.pw M n).pull f)).g p q =
      ((LB.div (H.pull g) (M.pull f)).g p q) ^ n := by
  simp only [LB.div, pull_pw_g]
  erw [map_zpow, map_zpow, ← inv_zpow, ← mul_zpow]
  rfl

def isoPow {M : LB X} {H : LB Y} {f : Z ⟶ X} {g : Z ⟶ Y} (w : LB.Iso (M.pull f) (H.pull g)) (n : ℤ) :
    LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g) where
  s := fun p => (w.s p) ^ n

theorem isoPow_isGen {M : LB X} {H : LB Y} {f : Z ⟶ X} {g : Z ⟶ Y} (w : LB.Iso (M.pull f) (H.pull g))
    (hw : w.IsGen) (n : ℤ) : (isoPow w n).IsGen := by
  intro p q
  rw [div_pull_pw_g]
  erw [map_zpow, map_zpow]
  erw [hw p q, mul_zpow]
  rfl

theorem exists_isGen_iso_pw : ∀ {X Y Z : Scheme.{0}} (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y)
    (w : LB.Iso (M.pull f) (H.pull g)), M.IsLB → H.IsLB → w.IsGen → ∀ n : ℤ,
    ∃ w' : LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g), w'.IsGen :=
  fun _ _ _ _ w _ _ hw n => ⟨isoPow w n, isoPow_isGen w hw n⟩

end GlobalTheory.PullPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsometryConjPointSplitUpToIndex
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjSplitIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nsmul_cancel {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) {N : ℕ} (hN : 0 < N) {u u' : D.La} (h : N • u = N • u') : u = u' := by
  apply hP.2.1
  have h' := congrArg P h
  rw [map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h'
  exact smul_right_injective _ (Nat.cast_ne_zero.2 hN.ne') h'

theorem form_nsmul_nsmul (D : Datum H) (N : ℕ) (x y : D.La) : D.EF (N • x) (N • y) = (N * N : ℤ) * D.EF x y := by
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  ring

end GlobalTheory.ConjSplitIndex

namespace GlobalTheory.CompRat


open ConjIsometry in
theorem exists_isometry_of_conj_split_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P') (N : ℕ), 0 < N → (∀ v : (F.Di i).La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → C.ActsBy τ io N (1, 0) → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) ∧ (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) ∧ ∀ n : ℕ, 0 < n → C.ActsBy τ io (N * n) (1, 0) → ∀ v, spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P v)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ v))).left := by
  intro E _ _ _ H D l Xo σ g ty F h₁ h₂ h₃ τ hτ C io hio i P hP i' P' hP' N hN hNv hu hAN
  obtain ⟨f, hadd, hw, -, hact, hf⟩ := GlobalTheory.ConjSplit.exists_param C τ hτ io hio
  let U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have key : ∀ (ε : ℤˣ) (ρ : ℂ), ((ε : ℤ) : ℂ) * H.rt0 = ρ → ∃ Φ : lat hP ρ →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' ρ) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ a : lat hP ρ,
        U ≫ F.ex i P ((n : ℂ)⁻¹ • P a) = F.ex i' P' ((n : ℂ)⁻¹ • wC H s • P' (Φ a)) := by
    rintro ε _ rfl
    obtain ⟨Φ, hΦ, hex⟩ := GlobalTheory.ConjSplitAnyLevel.exists_lin F hP h₁ h₂ h₃ C io hP' U f hadd hw hf ε
    refine ⟨Φ, hΦ, fun n s hA a => ?_⟩
    rw [smul_smul, mul_comm (n : ℂ)⁻¹, ← div_eq_mul_inv, hex,
      GlobalTheory.ConjSplit.ex_congr_type F hP ε a.2 (hact n s hA), one_div]
  obtain ⟨Φp, hp, tp⟩ := key 1 H.rt0 (by simp)
  obtain ⟨Φm, hm, tm⟩ := key (-1) (-H.rt0) (by simp)
  have hd := Submodule.disjoint_def.1 (disjoint_lat hP (GlobalTheory.ConjSplit.rt0_ne_neg (H := H)))

  have hsum : ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      U ≫ F.ex i P ((n : ℂ)⁻¹ • P (a.1 + b.1)) =
        F.ex i' P' ((n : ℂ)⁻¹ • P' (Φp (wE H s • a) + Φm (H.bar (wE H s) • b))) := by
    intro n s hA a b
    rw [map_smul, map_smul, map_add P', GlobalTheory.ConjSplit.period_wE hP' (hp a),
      GlobalTheory.ConjSplit.period_bar_wE hP' (hm b), smul_add, F.ex_add i' P' hP', ← tp n s hA, ← tm n s hA,
      ← MonObj.comp_mul, ← F.ex_add i P hP, ← smul_add, ← map_add]
  have hsum1 : ∀ n : ℕ, C.ActsBy τ io n (1, 0) → ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      U ≫ F.ex i P ((n : ℂ)⁻¹ • P (a.1 + b.1)) = F.ex i' P' ((n : ℂ)⁻¹ • P' (Φp a + Φm b)) := by
    intro n hA a b
    rw [hsum n (1, 0) hA a b]
    simp [wE]

  have hiso₀ : ∀ (a a' : lat hP H.rt0) (b b' : lat hP (-H.rt0)),
      (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') = (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1) := by
    intro a a' b b'
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') - (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1) := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.CompRat.Acts.main E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (congrArg (fun m => m.left) (hsum n s hs a b))
        (congrArg (fun m => m.left) (hsum n s hs a' b'))
      have hM := GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = M at hM hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = M := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP' H.rt0, ∀ v ∈ lat hP' (-H.rt0),
          (F.Di i').EF u v = 0 ∧ (F.Di i').EF v u = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' hu hv
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φp (wE H s • a) + Φm (H.bar (wE H s) • b)) (Φp (wE H s • a') + Φm (H.bar (wE H s) • b')) =
          M * (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') := by
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [(o _ (hp _) _ (hm _)).1, (o _ (hp _) _ (hm _)).2, (o _ (hp a) _ (hm b')).1, (o _ (hp a') _ (hm b)).2,
          map_smul Φp, map_smul Φp, map_smul Φm, map_smul Φm, form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hM] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') - (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1)).natAbs + 1)
      (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this
      (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hdec : ∀ v, ∃ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v := fun v => by
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hNv v)
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
  have huniq : ∀ (a a' : lat hP H.rt0) (b b' : lat hP (-H.rt0)), a.1 + b.1 = a'.1 + b'.1 → a = a' ∧ b = b' := by
    intro a a' b b' h
    have e : a.1 - a'.1 = b'.1 - b.1 := by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have z : a.1 - a'.1 = 0 := hd _ (sub_mem a.2 a'.2) (e ▸ sub_mem b'.2 b.2)
    exact ⟨Subtype.ext (sub_eq_zero.1 z), Subtype.ext (sub_eq_zero.1 (e ▸ z)).symm⟩
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hdiv : ∀ v, ∃ u : (F.Di i').La, ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v →
      Φp a + Φm b = N • u := by
    intro v
    obtain ⟨a, b, hab⟩ := hdec v
    have e := hsum1 N hAN a b
    rw [hab, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hNc, (F.ex_ker i P hP _).2 ⟨v, rfl⟩,
      MonObj.comp_one] at e
    obtain ⟨u, hu'⟩ := (F.ex_ker i' P' hP' _).1 e.symm
    refine ⟨u, fun a' b' h => ?_⟩
    obtain ⟨rfl, rfl⟩ := huniq a a' b b' (hab.trans h.symm)
    apply hP'.2.1
    rw [map_nsmul, hu', ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hNc]
  choose Ψ hΨ using hdiv
  let Φ : (F.Di i).La →ₗ[𝓞 E] (F.Di i').La :=
    { toFun := Ψ
      map_add' := fun v w => by
        obtain ⟨a, b, hab⟩ := hdec v
        obtain ⟨a', b', hab'⟩ := hdec w
        refine GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN ?_
        rw [smul_add, ← hΨ v a b hab, ← hΨ w a' b' hab', ← hΨ (v + w) (a + a') (b + b')
          (by rw [smul_add, ← hab, ← hab', Submodule.coe_add, Submodule.coe_add]; abel), map_add (f := _), map_add (f := _)]
        abel
      map_smul' := fun c v => by
        obtain ⟨a, b, hab⟩ := hdec v
        refine GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN ?_
        rw [RingHom.id_apply, smul_comm N c, ← hΨ v a b hab, ← hΨ (c • v) (c • a) (c • b)
          (by rw [smul_comm N c, ← hab, Submodule.coe_smul, Submodule.coe_smul, smul_add]), map_smul, map_smul,
          smul_add] }
  have hΦ : ∀ v (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v → Φp a + Φm b = N • Φ v := hΨ
  have hiso : ∀ v w, (F.Di i').EF (Φ v) (Φ w) = (F.Di i).EF v w := by
    intro v w
    obtain ⟨a, b, hab⟩ := hdec v
    obtain ⟨a', b', hab'⟩ := hdec w
    have e := hiso₀ a a' b b'
    rw [hΦ v a b hab, hΦ w a' b' hab', hab, hab', GlobalTheory.ConjSplitIndex.form_nsmul_nsmul,
      GlobalTheory.ConjSplitIndex.form_nsmul_nsmul] at e
    have hz : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact mul_left_cancel₀ (mul_ne_zero hz hz) e
  have hinj : Function.Injective Φ := (injective_iff_map_eq_zero _).2 fun v hv =>
    (F.Di i).unimod.1 (by
      ext z
      rw [← hiso, hv]; simp)
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, fun a ha => ?_, fun b hb => ?_, fun n hn hA v => ?_⟩
  · have e := hΦ a (N • ⟨a, ha⟩) 0 (by simp)
    rw [map_zero, add_zero, map_nsmul] at e
    show Φ a ∈ _
    rw [← GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN e]
    exact hp _
  · have e := hΦ b 0 (N • ⟨b, hb⟩) (by simp)
    rw [map_zero, zero_add, map_nsmul] at e
    show Φ b ∈ _
    rw [← GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN e]
    exact hm _
  · obtain ⟨a, b, hab⟩ := hdec v
    have e := hsum1 (N * n) hA a b
    have hc : ∀ x : Fin g → ℂ, ((N * n : ℕ) : ℂ)⁻¹ • N • x = (n : ℂ)⁻¹ • x := fun x => by
      rw [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_mul, mul_inv_rev, mul_smul, inv_smul_smul₀ hNc]
    rw [hΦ v a b hab, hab, map_nsmul, map_nsmul, hc, hc] at e
    exact congrArg (fun m => m.left) e

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPartnerCombinationGoodInertLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.VmTwo

theorem twoSided_goodInert : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → Formalism.DivisionValues.conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hL hW hE hS P hG hc
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  exact _root_.GlobalTheory.Hk3.TwoSidedInert.twoSided_of_inert hH R.toRealDat F.lv2 hL hcore hS _ P hG hc (_root_.GlobalTheory.FixAllGood.fixAll_of_good R F hW hE _ P hG hc)

end GlobalTheory.VmTwo
end

