module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0103
public import ReciprocityTheory.GaloisValuations.Global

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualMeasuresAndAbsKScale
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise NNReal ENNReal

noncomputable section

namespace GlobalTheory.JR.MeasScale

theorem fourB_nnreal_smul {V : Type} [MeasurableSpace V] (μ : Measure V) (c : ℝ≥0) (B : V → V → ℂ)
    (f : V → ℂ) (y : V) : fourB (c • μ) B f y = (c : ℂ) * fourB μ B f y := by
  simp only [fourB]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem fourB_const_mul {V : Type} [MeasurableSpace V] (μ : Measure V) (a : ℂ) (B : V → V → ℂ)
    (g : V → ℂ) (y : V) : fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by
  simp only [fourB, mul_assoc]
  exact integral_const_mul a _

theorem fourB_twice_nnreal_smul {V : Type} [MeasurableSpace V] (μ : Measure V) (c : ℝ≥0) (B : V → V → ℂ)
    (f : V → ℂ) (y : V) :
    fourB (c • μ) B (fourB (c • μ) B f) y = (c : ℂ) ^ 2 * fourB μ B (fourB μ B f) y := by
  have h : fourB (c • μ) B f = fun z => (c : ℂ) * fourB μ B f z :=
    funext fun z => fourB_nnreal_smul μ c B f z
  rw [fourB_nnreal_smul, h, fourB_const_mul]
  ring

theorem exists_test_ne_zero {V : Type} [AddCommGroup V] [TopologicalSpace V] [T2Space V]
    (h : ∃ S : Set V, IsOpen S ∧ IsCompact S ∧ S.Nonempty) : ∃ f : V → ℂ, IsTest f ∧ ∃ y, f (-y) ≠ 0 := by
  obtain ⟨S, hSo, hSc, s, hs⟩ := h
  have hcl : IsClosed S := hSc.isClosed
  refine ⟨S.indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, -s, ?_⟩
  · intro t
    have := Set.indicator_const_preimage S t (1 : ℂ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact isOpen_univ
    · exact hSo
    · exact hcl.isOpen_compl
    · exact isOpen_empty
  · exact HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _
  · simp [hs]

theorem selfDual_unique {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (hS : ∃ S : Set V, IsOpen S ∧ IsCompact S ∧ S.Nonempty) (B : V → V → ℂ) {μ μ' : Measure V}
    (h : SelfDual μ B) (h' : SelfDual μ' B) : μ' = μ := by
  obtain ⟨hμ, hF⟩ := h
  obtain ⟨hμ', hF'⟩ := h'
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ
  obtain ⟨f, hf, y, hy⟩ := exists_test_ne_zero hS
  have h1 := hF' f hf y
  rw [e, fourB_twice_nnreal_smul, hF f hf y] at h1
  have hc : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℂ) ^ 2 = 1 :=
    mul_right_cancel₀ hy (h1.trans (one_mul _).symm)
  have hc2 : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℝ) ^ 2 = 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ (μ'.addHaarScalarFactor μ : ℝ≥0) := NNReal.coe_nonneg _
  have hc1 : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℝ) = 1 := by nlinarith
  have hc3 : μ'.addHaarScalarFactor μ = 1 := by exact_mod_cast hc1
  rw [e, hc3, one_smul]

theorem integral_units_smul {L : Type} [CommRing L] [TopologicalSpace L] [IsTopologicalRing L]
    [LocallyCompactSpace L] [T2Space L] [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (μ : Measure L) [μ.IsAddHaarMeasure] (u : Lˣ) (G : L → ℂ) :
    ∫ y, G (u • y) ∂μ = ((distribHaarChar L u : ℝ≥0) : ℂ)⁻¹ * ∫ y, G y ∂μ := by
  let φ := Homeomorph.smul (α := L) u
  have hmap : μ.map (fun y => u • y) = (distribHaarChar L u⁻¹) • μ := by
    ext s hs
    rw [Measure.map_apply (continuous_const_smul u).measurable hs, Set.preimage_smul, Measure.smul_apply,
      ← distribHaarChar_mul μ u⁻¹ s]
    rfl
  have : ∫ y, G y ∂(μ.map fun y => u • y) = ∫ y, G (u • y) ∂μ :=
    φ.measurableEmbedding.integral_map (μ := μ) G
  rw [← this, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, map_inv]
  push_cast
  rfl

end GlobalTheory.JR.MeasScale

namespace GlobalTheory.JR.MeasScale

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def unitL (A : Et F E) (x : A.Kˣ) : A.Lˣ := Units.map (algebraMap A.K A.L : A.K →* A.L) x

theorem unitL_smul (A : Et F E) (x : A.Kˣ) (y : A.L) : unitL A x • y = algebraMap A.K A.L x * y := rfl

theorem kerL_eq (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (y' y : A.L) :
    A.kerL ψ x y' y = A.kerL ψ ((1 : A.Kˣ) : A.K) y' (unitL A x • y) := by
  simp only [Et.kerL, unitL_smul, Units.val_one, one_mul]
  congr 1
  have : star y' * (algebraMap A.K A.L x * y) = (x : A.K) • (star y' * y) := by
    rw [Algebra.smul_def]; ring
  rw [this, map_smul, smul_eq_mul]

theorem kerL_swap (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (y' y : A.L) :
    A.kerL ψ ((1 : A.Kˣ) : A.K) y' (unitL A x • y) = A.kerL ψ ((1 : A.Kˣ) : A.K) (unitL A x • y') y := by
  simp only [Et.kerL, unitL_smul]
  rw [star_mul', A.star_K]
  congr 3
  ring

theorem selfDual_scale [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (h : SelfDual μ (A.kerL ψ ((1 : A.Kˣ) : A.K))) :
    SelfDual (distribHaarChar A.K x • μ) (A.kerL ψ x) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hN : distribHaarChar A.L (unitL A x) = distribHaarChar A.K x ^ 2 := by
    obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
    obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
    have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
    rw [← map_pow]
    refine GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_
    simp [unitL, A.star_K, pow_two]
  obtain ⟨hμ, hF⟩ := h
  have hc : distribHaarChar A.K x ≠ 0 := distribHaarChar_pos.ne'
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul _ hc, fun f hf y => ?_⟩
  set c := distribHaarChar A.K x with hcdef
  set B1 := A.kerL ψ ((1 : A.Kˣ) : A.K)
  have h1 : ∀ g z, fourB (c • μ) (A.kerL ψ x) g z = (c : ℂ) * fourB μ B1 g (unitL A x • z) := by
    intro g z
    rw [fourB_nnreal_smul]
    simp only [fourB, kerL_eq A ψ x, B1]
  have h2 : fourB (c • μ) (A.kerL ψ x) f = fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z) :=
    funext (h1 f)
  rw [h1, h2]
  have h3 : fourB μ B1 (fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z)) (unitL A x • y) =
      (c : ℂ) * ((distribHaarChar A.L (unitL A x) : ℝ≥0) : ℂ)⁻¹ * fourB μ B1 (fourB μ B1 f) y := by
    rw [fourB_const_mul, mul_assoc]
    congr 1
    have e := integral_units_smul μ (unitL A x) (fun z => fourB μ B1 f z * B1 z y)
    refine Eq.trans ?_ e
    show ∫ y', fourB μ B1 f (unitL A x • y') * B1 y' (unitL A x • y) ∂μ = _
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    exact congrArg _ (kerL_swap A ψ x y' y)
  rw [h3, hF f hf y, hN]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp

theorem meas_scale [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (m : A.Meas ψ) (x : A.Kˣ) :
    m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  have := (inferInstance : Unram F E).charZero
  have hu := ‹Unram F E›.ultraF; have := ‹Unram F E›.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, hS⟩ := EtMeas.top_facts F A.L
  rw [EtMeas.absK_unit, ENNReal.ofReal_coe_nnreal]
  exact selfDual_unique hS _ (selfDual_scale A ψ x (m.μL 1) (m.sdL 1)) (m.sdL x)

end GlobalTheory.JR.MeasScale

theorem GlobalTheory.JR.exists_meas_and_scale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    Nonempty (A.Meas ψ) ∧ ∀ (m : A.Meas ψ) (x : A.Kˣ), m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  intro F E _ _ _ _ _ A ψ hψ
  exact ⟨(EtMeas.nonempty_meas_and_reps F E A ψ hψ).1, GlobalTheory.JR.MeasScale.meas_scale A ψ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformizerCompatibleUnramifiedExt
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem exists_gen_of_valuation_eq (K : UQ) (x : K.E)
    (hx : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x = WithZero.exp (-1)) :
    ∃ a : K.O, algebraMap K.O K.E a = x ∧ IsLocalRing.maximalIdeal K.O = Ideal.span {a} := by
  set v := IsDiscreteValuationRing.maximalIdeal K.O with hv
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := K.O) (K := K.E)
    (x := x) (by rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
  refine ⟨a, rfl, ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at hx
  have h1 : a ∈ v.asIdeal := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem, hx, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]; norm_num
  have h2 : a ∉ v.asIdeal ^ 2 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hx, WithZero.exp_le_exp]; norm_num
  change a ∈ IsLocalRing.maximalIdeal K.O at h1
  change a ∉ IsLocalRing.maximalIdeal K.O ^ 2 at h2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hm := hϖ.maximalIdeal_eq
  rw [hm] at h1 h2 ⊢
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 h1
  have hb : IsUnit b := by
    by_contra hb
    apply h2
    have : b ∈ IsLocalRing.maximalIdeal K.O := (IsLocalRing.mem_maximalIdeal b).2 hb
    rw [hm] at this
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]
    exact mul_dvd_mul (Ideal.mem_span_singleton.1 this) dvd_rfl
  rw [Ideal.span_singleton_mul_left_unit hb]

theorem exists_unif (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (h : IsUnrExt K K' d φ) :
    ∃ π : K.O, ∃ π' : K'.O, algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) ∧
      IsLocalRing.maximalIdeal K.O = Ideal.span {π} ∧ IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} := by
  obtain ⟨x, hx⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  have hx' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x = WithZero.exp (-1) := hx
  obtain ⟨π, hπ, hm⟩ := exists_gen_of_valuation_eq K x hx'
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx'
    exact WithZero.exp_ne_zero hx'.symm
  have hv := h.2.2.1 x
  unfold val at hv
  rw [hx', WithZero.log_exp] at hv
  have hy0 : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) ≠ 0 := by
    simpa using (map_ne_zero φ).2 hx0
  have hy : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) = WithZero.exp (-1) := by
    rw [← WithZero.exp_log hy0]; congr 1; omega
  obtain ⟨π', hπ', hm'⟩ := exists_gen_of_valuation_eq K' (φ x) hy
  exact ⟨π, π', by rw [hπ', hπ], hm, hm'⟩

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatWachLetterRingCompletionOfDenseSaturated
section
open Formalism.BasicNotions

namespace GlobalTheory
namespace FlatCompl

section Level

variable {A R E : Type} [CommRing A] [CommRing R] [CommRing E] [Algebra A R] [Algebra A E]
  [Algebra R E] [IsScalarTower A R E]

theorem mem_pow_smul_top_iff (p : ℕ) (n : ℕ) (e : E) :
    e ∈ ((Ideal.span {(p : R)}) ^ n • ⊤ : Submodule R E) ↔ e ∈ Ideal.span {(p : E) ^ n} := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, by simp [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, Submodule.mem_top, by simp [Algebra.smul_def, mul_comm]⟩

variable (s : A) [IsLocalization.Away s R] (p : ℕ)

theorem level_surj
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ),
      x * algebraMap A E (s ^ m) - algebraMap A E a ∈ Ideal.span {(p : E) ^ k})
    (n : ℕ) (e : E) : ∃ r : R, algebraMap R E r - e ∈ Ideal.span {(p : E) ^ n} := by
  obtain ⟨a, m, h⟩ := hd e n
  obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := R) s).pow m
  refine ⟨algebraMap A R a * ↑u⁻¹, ?_⟩
  have hE : algebraMap R E ↑u * algebraMap R E ↑u⁻¹ = 1 := by
    rw [← map_mul, u.mul_inv, map_one]
  have key : algebraMap R E (algebraMap A R a * ↑u⁻¹) - e =
      -((e * algebraMap A E (s ^ m) - algebraMap A E a) * algebraMap R E ↑u⁻¹) := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A R E (s ^ m),
      map_pow, ← hu]
    linear_combination e * hE
  rw [key]
  exact (Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_right _ _ h)

include s in
theorem level_inj
    (hsat : ∀ (a : A) (k : ℕ), algebraMap A E a ∈ Ideal.span {(p : E) ^ k} →
      ∃ b : A, a = (p : A) ^ k * b)
    (n : ℕ) (r : R) (h : algebraMap R E r ∈ Ideal.span {(p : E) ^ n}) :
    r ∈ Ideal.span {(p : R) ^ n} := by
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers s) r
  simp only at hr
  have hE : algebraMap A E a ∈ Ideal.span {(p : E) ^ n} := by
    rw [IsScalarTower.algebraMap_apply A R E, ← hr, map_mul]
    exact Ideal.mul_mem_right _ _ h
  obtain ⟨b, rfl⟩ := hsat a n hE
  obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := R) s).pow m
  rw [Ideal.mem_span_singleton']
  refine ⟨algebraMap A R b * ↑u⁻¹, ?_⟩
  have h1 : r = r * (↑u * ↑u⁻¹) := by simp
  rw [h1, ← mul_assoc, hu, ← map_pow, hr]
  simp only [map_mul, map_pow, map_natCast]
  ring

end Level

end FlatCompl
end GlobalTheory

namespace GlobalTheory
namespace FlatCompl

open AdicCompletion

theorem flat_of_dense_sat {A E : Type} [CommRing A] [IsNoetherianRing A] [CommRing E] [Algebra A E]
    (s : A) (p : ℕ) (hs : IsUnit (algebraMap A E s))
    (hc : IsAdicComplete (Ideal.span {(p : E)}) E)
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ),
      x * algebraMap A E (s ^ m) - algebraMap A E a ∈ Ideal.span {(p : E) ^ k})
    (hsat : ∀ (a : A) (k : ℕ), algebraMap A E a ∈ Ideal.span {(p : E) ^ k} →
      ∃ b : A, a = (p : A) ^ k * b) :
    Module.Flat A E := by
  let R := Localization.Away s
  letI : Algebra R E := (IsLocalization.Away.lift s hs).toAlgebra
  haveI : IsScalarTower A R E :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq _ a).symm)
  let I : Ideal R := Ideal.span {(p : R)}
  have hmap : I.map (algebraMap R E) = Ideal.span {(p : E)} := by
    simp [I, Ideal.map_span]
  haveI : IsAdicComplete I E := by
    have h1 : IsHausdorff I E :=
      IsHausdorff.map_algebraMap_iff.mp (by rw [hmap]; exact hc.toIsHausdorff)
    have h2 : IsPrecomplete I E :=
      IsPrecomplete.map_algebraMap_iff.mp (by rw [hmap]; exact hc.toIsPrecomplete)
    exact { toIsHausdorff := h1, toIsPrecomplete := h2 }
  let f : R →ₗ[R] E := Algebra.linearMap R E
  have hinj : ∀ n, Function.Injective (f.reduceModIdeal (I ^ n)) := by
    intro n
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H r =>
      rw [LinearMap.reduceModIdeal_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_iff (E := R)]
      exact level_inj s p hsat n r ((mem_pow_smul_top_iff p n _).mp hx)
  have hsurj : ∀ n, Function.Surjective (f.reduceModIdeal (I ^ n)) := by
    intro n y
    induction y using Submodule.Quotient.induction_on with
    | H e =>
      obtain ⟨r, hr⟩ := level_surj (R := R) s p hd n e
      refine ⟨Submodule.Quotient.mk r, ?_⟩
      rw [LinearMap.reduceModIdeal_apply, Submodule.Quotient.eq, mem_pow_smul_top_iff]
      exact hr
  have hbij : Function.Bijective (AdicCompletion.map I f) := by
    constructor
    · intro x y hxy
      ext n
      apply hinj n
      have := congrArg (fun z => z.val n) hxy
      simpa only [AdicCompletion.map_val_apply] using this
    · intro y
      let g := fun n => Function.surjInv (hsurj n)
      refine ⟨⟨fun n => g n (y.val n), fun {m n} hmn => ?_⟩, ?_⟩
      · apply hinj m
        have h1 := LinearMap.congr_fun
          (AdicCompletion.transitionMap_comp_reduceModIdeal I f hmn) (g n (y.val n))
        simp only [LinearMap.coe_comp, Function.comp_apply] at h1
        rw [show (f.reduceModIdeal (I ^ m)) (transitionMap I R hmn (g n (y.val n))) =
          transitionMap I E hmn (f.reduceModIdeal (I ^ n) (g n (y.val n))) from h1.symm]
        rw [Function.surjInv_eq (hsurj n), Function.surjInv_eq (hsurj m)]
        exact y.property hmn
      · ext n
        exact Function.surjInv_eq (hsurj n) _
  let Φ : AdicCompletion I R ≃ₗ[R] E :=
    (LinearEquiv.ofBijective ((AdicCompletion.map I f).restrictScalars R) hbij).trans
      (AdicCompletion.ofLinearEquiv I E).symm
  haveI : Module.Flat R E := Module.Flat.of_linearEquiv Φ.symm
  haveI : Module.Flat A R := IsLocalization.flat R (Submonoid.powers s)
  exact Module.Flat.trans A R E

end FlatCompl
end GlobalTheory

namespace GlobalTheory

theorem flat_letA_of_dense_sat : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (p : ℕ) (E : Type) [CommRing E] [Algebra (LetA O n) E], IsUnit (algebraMap (LetA O n) E letπ) → IsAdicComplete (Ideal.span {(p : E)}) E → (∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k}) → (∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} → ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) → Module.Flat (LetA O n) E :=
  fun _ _ _ _ _ p _ _ _ hs hc hd hsat => FlatCompl.flat_of_dense_sat letπ p hs hc hd hsat

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaMinusOneDivVariablePolarKernelLeSenWeights
section
noncomputable section
namespace GlobalTheory.PhiGam.PolarKernel
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam Module

section lin
variable {k : Type} [Field k] {U : Type} [AddCommGroup U] [Module k U]

theorem finrank_quot (A B : Submodule k U) :
    finrank k (↥A ⧸ B.submoduleOf A) = finrank k (A.map B.mkQ) := by
  have h := (LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)).finrank_eq
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  exact h

theorem finrank_le_gmult (T : Module.End k U) (P Q Z S : Submodule k U) [FiniteDimensional k S]
    (hP : P ≤ S ⊔ Q) (hZ : ∀ x ∈ Z, x ∈ P ∧ T x ∈ Q) :
    finrank k (↥Z ⧸ Q.submoduleOf Z) ≤ gmult T P Q 0 := by
  unfold gmult
  rw [finrank_quot, finrank_quot, map_zero (algebraMap k (Module.End k U)), sub_zero]
  have hfin : FiniteDimensional k ((P ⊓ ⨆ m : ℕ, Q.comap (T ^ m)).map Q.mkQ) := by
    have h : (P ⊓ ⨆ m : ℕ, Q.comap (T ^ m)).map Q.mkQ ≤ S.map Q.mkQ := by
      have := Submodule.map_mono (f := Q.mkQ) ((inf_le_left (b := ⨆ m : ℕ, Q.comap (T ^ m))).trans hP)
      rwa [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq] at this
    exact Submodule.finiteDimensional_of_le h
  refine Submodule.finrank_mono (Submodule.map_mono fun x hx => ⟨(hZ x hx).1, ?_⟩)
  refine Submodule.mem_iSup_of_mem 1 ?_
  rw [Submodule.mem_comap, pow_one]
  exact (hZ x hx).2
end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem le_span_sup {ι : Type} (e : ι → V) (P : Submodule k⟦X⟧ V)
    (hP : Submodule.span k⟦X⟧ (Set.range e) = P) :
    P.restrictScalars k ≤ Submodule.span k (Set.range e) ⊔ (sh 1 P).restrictScalars k := by
  intro x hx
  rw [Submodule.restrictScalars_mem, ← hP, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  refine Submodule.sum_mem _ fun i _ => ?_
  show c i • e i ∈ _
  have he : e i ∈ P := hP ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : k⟦X⟧, c i = algebraMap k k⟦X⟧ (PowerSeries.constantCoeff (c i)) + PowerSeries.X * d :=
    ⟨_, by rw [add_comm]; exact PowerSeries.eq_X_mul_shift_add_const (c i)⟩
  rw [hd, add_smul, algebraMap_smul]
  refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) ?_
  refine mem_sh_iff_exists.2 ⟨d • e i, P.smul_mem _ he, ?_⟩
  rw [zpow_one, vv_eq_coe_X, mul_smul]
  exact algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) _

theorem exists_finite_le_sup (N : Submodule k⟦X⟧ V) (hN : N.FG) (a : ℤ) (m : ℕ) :
    ∃ S : Submodule k V, FiniteDimensional k S ∧
      (sh a N).restrictScalars k ≤ S ⊔ (sh (a + m) N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp⟩
  | succ m ih =>
    obtain ⟨S, hS, h⟩ := ih
    have hfg : (sh (a + m) N).FG := hN.map _
    obtain ⟨n, e, he⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
    have h2 := le_span_sup e _ he
    rw [sh_sh_eq, add_comm (1 : ℤ)] at h2
    have : FiniteDimensional k (Submodule.span k (Set.range e)) :=
      FiniteDimensional.span_of_finite k (Set.finite_range e)
    refine ⟨S ⊔ Submodule.span k (Set.range e), inferInstance, h.trans ?_⟩
    rw [sup_assoc]
    refine sup_le_sup_left ?_ _
    rw [Nat.cast_succ, ← add_assoc]
    exact h2

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (w : ℕ) (Z : Submodule k V), (∀ x ∈ Z, x ∈ sh (-w) N ∧ nab g x ∈ N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) ≤ ∑ j ∈ Finset.range w, sen g N ((-(w : ℤ) + j : ℤ) : k) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC w Z hZ
  have hr := _root_.GlobalTheory.PhiGam.Range.qmult_sh_range R g hg N hN hC (-w) w 0
  simp only [zero_add, neg_add_cancel, sh_zero_eq] at hr
  obtain ⟨S, hS, hF⟩ := exists_finite_le_sup N hN.1 (-w) w
  rw [neg_add_cancel, sh_zero_eq] at hF
  rw [← hr]
  exact finrank_le_gmult (nab g) _ _ Z S hF hZ

end GlobalTheory.PhiGam.PolarKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobFixesRootOfOneModPlaceStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrob_fixes_root_of_one_mod_place : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (M : ℕ) (ζ : F),
    IsPrimitiveRoot ζ M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
    ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G F Ω, Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ →
    ∀ x : 𝓞 F, x - 1 ∈ v.asIdeal → ∀ w : Ω, w ^ M = algebraMap F Ω (x : F) → σ w = w := by
  first | exact @GlobalTheory.frob_fixes_root_of_one_mod | exact GlobalTheory.frob_fixes_root_of_one_mod | (intros; apply GlobalTheory.frob_fixes_root_of_one_mod <;> assumption)
end

