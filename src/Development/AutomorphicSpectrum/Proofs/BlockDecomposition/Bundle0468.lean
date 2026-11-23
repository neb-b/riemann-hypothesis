module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import GroundTheory.LocalFields.Bundle0016
public import GroundTheory.LocalFields.KroneckerWeber
public import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import GroundTheory.GlobalFields.LocalAtPlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0448
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslate
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.TransDeriv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}

theorem descend_eq_sec {X : Type} {f : G → X} (h : LeftInv Γ f) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) :
    descend Γ f q = f (sec Γ q) := by
  conv_lhs => rw [← mk_sec q]
  exact h.descend_mk _

theorem sec_mul_eq {X : Type} {f : G → X} (h : LeftInv Γ f) (g : G) :
    (fun q : GlobalTheory.AutomorphicL2Unitary.Quot Γ => f (sec Γ q * g)) = descend Γ f ∘ rmul Γ g := by
  funext q
  have e : rmul Γ g q = mk Γ (sec Γ q * g) := by
    conv_lhs => rw [← mk_sec q]
    rfl
  rw [Function.comp_apply, e, h.descend_mk]

variable [μ.IsMulLeftInvariant]

theorem inner_toL2_eq_integral {f : G → ℂ} (hf : MemL2Quotient Γ μ f) (u : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) :
    ⟪u, hf.toL2⟫_ℂ = ∫ q : GlobalTheory.AutomorphicL2Unitary.Quot Γ, conj (u q) * f (sec Γ q) ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL2] with q e
  rw [e, descend_eq_sec hf.1]
  simp [mul_comm]

theorem sub_eq_integral {φ ψ : G → ℂ} {c : ℝ → G} (hψ : Continuous ψ) (hc : Continuous c) (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hd : ∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) (x : G) (t : ℝ) :
    φ (x * c t) - φ x = ∫ s in (0 : ℝ)..t, ψ (x * c s) := by
  have hs : ∀ s, HasDerivAt (fun r => φ (x * c r)) (ψ (x * c s)) s := fun s => by
    have h2 : HasDerivAt (fun t => φ (x * c s * c t)) (ψ (x * c s)) (s - s) := by simpa using hd (x * c s)
    have h3 := h2.comp_sub_const s s
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    have : c r = c s * c (r - s) := by rw [← hadd]; congr 1; ring
    simp only [this, mul_assoc]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hs s)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [h0]

theorem integrable_pair [μ.IsMulRightInvariant] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] {ψ : G → ℂ}
    (hψ : MemL2Quotient Γ μ ψ) (hψc : Continuous ψ) {c : ℝ → G} (hc : Continuous c) (u : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (t : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s))
      ((volume.restrict (Set.uIoc 0 t)).prod (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) := by
  have hsec := (measurableEmbedding_sec (Γ := Γ)).measurable
  have hm : Measurable (fun p : ℝ × GlobalTheory.AutomorphicL2Unitary.Quot Γ => ψ (sec Γ p.2 * c p.1)) :=
    hψc.measurable.comp ((hsec.comp measurable_snd).mul (hc.measurable.comp measurable_fst))
  have hu : Measurable (fun p : ℝ × GlobalTheory.AutomorphicL2Unitary.Quot Γ => conj (u p.2)) :=
    Complex.continuous_conj.measurable.comp ((Lp.stronglyMeasurable u).measurable.comp measurable_snd)
  have hF : Measurable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s)) :=
    hu.mul hm
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hF.enorm.aemeasurable]
  set C : ENNReal := eLpNorm u 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * eLpNorm (descend Γ ψ) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) with hC
  have hb : ∀ s, ∫⁻ q, ‖Function.uncurry (fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s)) (s, q)‖ₑ
      ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ ≤ C := fun s => by
    have h1 := eLpNorm_le_eLpNorm_mul_eLpNorm (μ := GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) (p := 2) (q := 2) (r := 1)
      (fun a b : ℂ => conj a * b) 1 (by fun_prop)
      (Lp.aestronglyMeasurable u) ((hψ.mul_right (c s)).2.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => by simp)
    have h2 : eLpNorm (descend Γ fun x => ψ (x * c s)) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) = eLpNorm (descend Γ ψ) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
      have e : descend Γ (fun x => ψ (x * c s)) = descend Γ ψ ∘ rmul Γ (c s) := by
        funext q
        rw [descend_eq_sec (hψ.1.mul_right (c s)), ← sec_mul_eq hψ.1]
      rw [e]
      exact eLpNorm_comp_measurePreserving hψ.2.aestronglyMeasurable (measurePreserving_rmul (c s))
    have hm₁ : AEStronglyMeasurable (fun q => conj (u q) * descend Γ (fun x => ψ (x * c s)) q)
        (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
      (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).mul
        (hψ.mul_right (c s)).2.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_eNorm hm₁, h2] at h1
    simp only [ENNReal.coe_one, one_mul] at h1
    refine le_trans (le_of_eq ?_) h1
    refine lintegral_congr fun q => ?_
    simp only [Function.uncurry, descend_eq_sec (hψ.1.mul_right (c s))]
  refine lt_of_le_of_lt (lintegral_mono hb) ?_
  rw [lintegral_const, Measure.restrict_apply_univ]
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (Lp.memLp u) hψ.2) ?_
  simp [Set.uIoc, Real.volume_Ioc]

variable [μ.IsMulRightInvariant] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ]

theorem R_sub_eq_integral {φ ψ : G → ℂ} (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ)
    (hψc : Continuous ψ) {c : ℝ → G} (hc : Continuous c) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hd : ∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) (t : ℝ) :
    R Γ μ (c t) hφ.toL2 - hφ.toL2 = ∫ s in (0 : ℝ)..t, R Γ μ (c s) hψ.toL2 := by
  have hcont : Continuous fun s => R Γ μ (c s) hψ.toL2 := (continuous_R _).comp hc
  refine ext_inner_left ℂ fun u => ?_
  have e1 := (innerSL ℂ u).intervalIntegral_comp_comm (hcont.intervalIntegrable (μ := volume) 0 t)
  simp only [innerSL_apply_apply] at e1
  rw [← e1, inner_sub_right]
  simp only [right_translate_toL2, inner_toL2_eq_integral]
  have hi : ∀ {f : G → ℂ} (hf : MemL2Quotient Γ μ f),
      Integrable (fun q : GlobalTheory.AutomorphicL2Unitary.Quot Γ => conj (u q) * f (sec Γ q)) (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := fun {f} hf => by
    have h := (Lp.memLp u).star.integrable_mul hf.2
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    simp [descend_eq_sec hf.1]
  rw [← integral_sub (hi (hφ.mul_right (c t))) (hi hφ), intervalIntegral.intervalIntegral_eq_integral_uIoc,
    integral_integral_swap (integrable_pair hψ hψc hc u t), ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [integral_const_mul]
  rw [← mul_sub, sub_eq_integral hψc hc h0 hadd hd, intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [mul_smul_comm]

theorem hasDerivAt_R : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (φ ψ : G → ℂ) (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ) (c : ℝ → G), Continuous φ → Continuous ψ → Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → (∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) → ∀ t, HasDerivAt (fun s => R Γ μ (c s) hφ.toL2) (R Γ μ (c t) hψ.toL2) t := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c _ hψc hc h0 hadd hd t
  have hcont : Continuous fun s => R Γ μ (c s) hψ.toL2 := (continuous_R _).comp hc
  have e : (fun s => R Γ μ (c s) hφ.toL2) = fun s => hφ.toL2 + ∫ r in (0 : ℝ)..s, R Γ μ (c r) hψ.toL2 := by
    funext s
    rw [← R_sub_eq_integral hφ hψ hψc hc h0 hadd hd s]
    abel
  rw [e]
  exact (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _

end GlobalTheory.CompanionTheory.TransDeriv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvertibleExistsNonzeroMinor
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem det_mul_eq_sum_mnr {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R) :
    (L * M).det = ∑ g : Fin n → ι, (∏ i, L i (g i)) * mnr M g := by
  have h1 : (L * M).det =
      (Matrix.detRowAlternating (R := R) (n := Fin n)).toMultilinearMap
        (fun i => ∑ j, L i j • M j) := by
    have : (L * M) = Matrix.of (fun i => ∑ j, L i j • M j) := by
      ext i k
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem exists_mnr_ne_zero_of_left_inverse :
    ∀ (R : Type) [CommRing R] [Nontrivial R] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
      (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R),
      L * M = 1 → ∃ f, mnr M f ≠ 0 := by
  intro R _ _ ι _ _ n M L h
  by_contra hc
  push_neg at hc
  have key := det_mul_eq_sum_mnr M L
  rw [h, Matrix.det_one] at key
  simp [hc] at key

end GlobalTheory.CompanionTheory.GodementH
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBridgeLubinTateField
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem eq_one_of_pow_eq_one_of_valuation_sub_lt {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m : ℕ} {ξ : K}
    (hm : v (m : K) = 1) (hξ : ξ ^ m = 1) (h : v (ξ - 1) < 1) : ξ = 1 := by
  have hv : v ξ ≤ 1 := by
    have e : ξ = (ξ - 1) + 1 := by ring
    rw [e]
    exact (v.map_add _ _).trans (max_le h.le (by simp))
  have hp : ∀ i : ℕ, v (ξ ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : ξ ^ (i + 1) - 1 = ξ * (ξ ^ i - 1) + (ξ - 1) := by ring
      rw [e]
      refine Valuation.map_add_lt v ?_ h
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hv) ih
  have hs : v ((∑ i ∈ Finset.range m, ξ ^ i) - (m : K)) < 1 := by
    have e : (∑ i ∈ Finset.range m, ξ ^ i) - (m : K) = ∑ i ∈ Finset.range m, (ξ ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    exact Valuation.map_sum_lt v one_ne_zero fun i _ => hp i
  have hsum : (∑ i ∈ Finset.range m, ξ ^ i) ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hm] at hs
    exact lt_irrefl _ hs
  have := mul_geom_sum ξ m
  rw [hξ, sub_self] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsum)

theorem natCast_residue_eq_zero {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F (Om l)]
    [ValuativeExtension F (Om l)] : (l : 𝓀[F]) = 0 := by
  have hnl : ¬ ((1 : F) ≤ᵥ (l : F)) := by
    intro h
    have h2 := (ValuativeExtension.vle_iff_vle (A := F) (B := Om l)).2 h
    rw [map_one, map_natCast, GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le, norm_one,
      ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends] at h2
    exact absurd (Padic.norm_natCast_lt_one_iff.mpr (dvd_refl l)) (not_lt.mpr h2)
  have hlt : valuation F (((l : 𝒪[F]) : 𝒪[F]) : F) < 1 := by
    refine not_le.mp fun h => hnl ?_
    rw [Valuation.Compatible.vle_iff_le (v := valuation F), map_one]
    simpa using h
  have hmem : (l : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one]
    exact ne_of_lt hlt
  rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff]
  exact hmem

theorem unramifiedDegree_eq_one_of_mem_inertia : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [IsSepClosure F (Om l)]
    (σ : ↥(Dec (F := E) A)), (σ : G E Ω) ∈ Ine (F := E) A → ∀ g : Om l ≃ₐ[F] Om l,
    (∀ y, g y = ((Bw.e σ : ↥(GK Bw.Kw)) : GQ l) y) → unramifiedDegree F (Om l) g = 1 := by
  intro l _ E Ω _ _ _ _ _ A O _ _ _ Bw hj F _ _ _ _ _ _ _ σ hσ g hg
  rw [GroundTheory.LocalField.unramifiedDegree_eq_one_iff]
  intro ζ hζ
  obtain ⟨m, hm, hζm⟩ := mem_unramifiedRoots_iff.1 hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hcop : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply hm
    rw [Nat.cast_mul, natCast_residue_eq_zero (l := l) (F := F), zero_mul]
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero m := ⟨hm0⟩
  have : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ₀, h₀⟩ : ∃ z : Ω, IsPrimitiveRoot z m := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hj0 := h₀.map_of_injective Bw.j.injective
  obtain ⟨i, -, hi⟩ := hj0.eq_pow_of_pow_eq_one hζm

  obtain ⟨z, hz, hzm⟩ : ∃ z : Ω, Bw.j z = ζ ∧ z ^ m = 1 :=
    ⟨ζ₀ ^ i, by rw [map_pow, hi], by rw [← pow_mul, mul_comm, pow_mul, h₀.pow_eq_one, one_pow]⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [hm0] at hzm
  let s : G E Ω := (σ : G E Ω)
  have hgz : g ζ = Bw.j (s z) := by
    rw [hg, ← hz]
    exact Bw.e_comm σ z
  have hnorm : ‖Bw.j z‖ = 1 := by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp ?_
    rw [← norm_pow, ← map_pow, hzm, map_one, norm_one]
  have hzA : A.valuation z ≤ 1 := by
    rw [A.valuation_le_one_iff]
    exact (hj z).mpr hnorm.le
  have hzunit : A.valuation z = 1 :=
    le_antisymm hzA (not_lt.mp fun h => ((hj.valuation_lt_one_iff z).mp h).ne hnorm)
  have hlt : A.valuation (s z - z) < 1 := hσ.2 z hzA
  have hmn : ‖Bw.j (m : Ω)‖ = 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends,
      Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcop
  have hmv : A.valuation (m : Ω) = 1 := by
    refine le_antisymm ?_ (not_lt.mp fun h => ((hj.valuation_lt_one_iff _).mp h).ne hmn)
    rw [A.valuation_le_one_iff]
    exact (hj _).mpr hmn.le
  have hsz : (s z / z) ^ m = 1 := by
    rw [div_pow, ← map_pow, hzm, map_one, div_one]
  have hone : s z / z = 1 := by
    refine eq_one_of_pow_eq_one_of_valuation_sub_lt A.valuation hmv hsz ?_
    have e : s z / z - 1 = (s z - z) / z := by field_simp
    rw [e, map_div₀, hzunit, div_one]
    exact hlt
  rw [hgz, (div_eq_one_iff_eq hz0).mp hone, hz]

end GlobalTheory.CompanionTheory.LTLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTHodge.CompletionRange

theorem isClosed_finExt {l : ℕ} [Fact l.Prime] (K : FinExt l) : IsClosed (K.1 : Set (Om l)) := by
  haveI : FiniteDimensional ℚ_[l] K.1.toSubmodule := K.2
  exact Submodule.closed_of_finiteDimensional K.1.toSubmodule

theorem valued_le_one_of_norm_le_one {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : ‖φ x‖ ≤ 1) : Valued.v x ≤ 1 := by
  by_contra hv
  have hv' : 1 < Valued.v x := not_le.1 hv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hv'
  have hy : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hv'
  have ht : Filter.Tendsto (fun n : ℕ => x⁻¹ ^ n) Filter.atTop (nhds 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one hy
  have ht' : Filter.Tendsto (fun n : ℕ => φ (x⁻¹ ^ n)) Filter.atTop (nhds 0) := by
    have h := (hφ.tendsto 0).comp ht
    rw [map_zero] at h
    exact h
  have hge : ∀ n : ℕ, 1 ≤ ‖φ (x⁻¹ ^ n)‖ := fun n => by
    have hφ0 : φ x ≠ 0 := (map_ne_zero φ).2 hx0
    rw [map_pow, map_inv₀, norm_pow, norm_inv]
    exact one_le_pow₀ ((one_le_inv₀ (norm_pos_iff.2 hφ0)).2 hx)
  have hn := ht'.norm
  rw [norm_zero] at hn
  have := ge_of_tendsto' hn hge
  linarith

theorem isClosed_image_integers {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ) :
    IsClosed (φ '' (w.adicCompletionIntegers E : Set (w.adicCompletion E))) := by
  have hc : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (w.adicCompletionIntegers E)))
  exact (hc.image hφ).isClosed

theorem range_eq_Kw : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l), Continuous φ →
    (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    Set.range φ = (Bw.Kw.1 : Set (Om l)) := by
  intro l _ E Ω _ _ _ _ Gw O _ _ _ Bw w φ hφ hE
  have hcl := isClosed_finExt Bw.Kw

  have key : ∀ k ∈ (Bw.Kw.1 : Set (Om l)), ‖k‖ ≤ 1 → k ∈ Set.range φ := by
    intro k hk hk1
    have hden : k ∈ closure (Set.range φ) := by
      refine closure_mono ?_ (Bw.j_dense hk)
      rintro _ ⟨y, rfl⟩
      exact ⟨algebraMap E _ y, hE y⟩
    have hS : IsOpen (Metric.closedBall (0 : Om l) 1) :=
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero
    have hk' : k ∈ Metric.closedBall (0 : Om l) 1 := by simpa using hk1
    have h2 : k ∈ closure (Metric.closedBall (0 : Om l) 1 ∩ Set.range φ) :=
      hS.inter_closure ⟨hk', hden⟩
    have h3 : Metric.closedBall (0 : Om l) 1 ∩ Set.range φ ⊆
        φ '' (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
      rintro _ ⟨hb, x, rfl⟩
      refine ⟨x, ?_, rfl⟩
      exact valued_le_one_of_norm_le_one w φ hφ x (by simpa using hb)
    have h4 := closure_minimal h3 (isClosed_image_integers w φ hφ) h2
    obtain ⟨x, -, rfl⟩ := h4
    exact ⟨x, rfl⟩
  refine Set.Subset.antisymm ?_ fun k hk => ?_
  · rintro _ ⟨x, rfl⟩
    refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on
      (p := fun x => φ x ∈ (Bw.Kw.1 : Set (Om l))) x (hcl.preimage hφ) fun y => ?_
    rw [hE y]
    exact Bw.j_E y
  · rcases le_total ‖k‖ 1 with h | h
    · exact key k hk h
    · have hinv : k⁻¹ ∈ (Bw.Kw.1 : Set (Om l)) := inv_mem hk
      obtain ⟨a, ha⟩ := key k⁻¹ hinv (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h)
      exact ⟨a⁻¹, by rw [map_inv₀, ha, inv_inv]⟩

end GlobalTheory.CompanionTheory.LTHodge.CompletionRange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormFinitePlaceBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH

theorem absEv_mul_locFin_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (v : Pl (F := F)) (u : J → E) (δ : (Fv F v ⊗[F] E)ˣ) (z : J → Fv F v ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : Fv F v) ⊗ₜ[F] u f) * δ.1) → (∀ f, absFin F v (z f) ≤ c) →
    GlobalTheory.Doubling.absEv F E v δ * locFin σ v u ≤ c ^ 2 := by
  intro F E _ _ _ _ _ σ hσ J _ v u δ z c hz hc
  have e2 : ∀ (τ : E →ₐ[F] FvBar F v) (w : Fv F v ⊗[F] E),
      finEmb F v τ (sigR (Fv F v) σ w) = finEmb F v (τ.comp σ) w := by
    intro τ w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hN := congrArg (fun y => absBar F v (finEmb F v (embBar F E v) y))
    (GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) δ.1)
  simp only [map_mul, absBar_mul, e2, AlgHom.commutes, absBar_algebraMap] at hN
  have key : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (finEmb F v τ δ.1) * supBar v τ u ≤ c := by
    intro τ
    unfold supBar
    rw [NNReal.mul_finset_sup]
    refine Finset.sup_le fun f _ => ?_
    refine le_trans (le_of_eq ?_) ((le_absFin F v τ (z f)).trans (hc f))
    rw [hz f, map_mul, absBar_mul, finEmb_tmul, map_one, one_mul, mul_comm]
  rw [GlobalTheory.Doubling.absEv_apply, hN]
  unfold locFin
  calc _ = (absBar F v (finEmb F v (embBar F E v) δ.1) * supBar v (embBar F E v) u) *
        (absBar F v (finEmb F v ((embBar F E v).comp σ) δ.1) * supBar v ((embBar F E v).comp σ) u) := by ring
    _ ≤ c * c := mul_le_mul' (key _) (key _)
    _ = c ^ 2 := (sq c).symm

end GlobalTheory.CompanionTheory.GodementH

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslationStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_coefficient_translation : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), TwInv T T' B s → (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B (T (uM (n + 1) y) v) v' x = coef T B v v' (x + y)) ∧ (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B v (T' (uM (n + 1) y) v') x = coef T B v v' (x - y)) ∧ (∀ (g : GL (Fin (n + 1)) k) (x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B (T (levi k (n + 1) g) v) (T' (levi k (n + 1) g) v') x = ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * coef T B v v' (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.coef_rules | exact GlobalTheory.CompanionTheory.MirPair.coef_rules | (intros; apply GlobalTheory.CompanionTheory.MirPair.coef_rules <;> assumption)
end

