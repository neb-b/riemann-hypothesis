module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0106
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0077
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0088
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0108
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0089
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0100
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0116
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0002
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBound
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

variable {K : Type} [Field K] [NumberField K]

theorem index_toAddSubgroup (a : Ideal (𝓞 K)) :
    (Submodule.toAddSubgroup a).index = Ideal.absNorm a := (Ideal.absNorm_eq_index a).symm

theorem relIndex_mul_ideal (𝔱 a : Ideal (𝓞 K)) (ha : a ≠ ⊥) :
    (Submodule.toAddSubgroup (𝔱 * a)).relIndex (Submodule.toAddSubgroup a) =
      Ideal.absNorm 𝔱 := by
  have hle : Submodule.toAddSubgroup (𝔱 * a) ≤ Submodule.toAddSubgroup a :=
    (Submodule.toAddSubgroup_le _ _).2 Ideal.mul_le_right
  have h := AddSubgroup.relIndex_mul_index hle
  rw [index_toAddSubgroup, index_toAddSubgroup, map_mul] at h
  have hne : Ideal.absNorm a ≠ 0 := fun h0 => ha (Ideal.absNorm_eq_zero_iff.1 h0)
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) h

theorem mem_den_iff (x : K) (a : 𝓞 K) :
    a ∈ den K x ↔ (a : K) * x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [den, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h 0
    exact Submodule.mem_one.2 ⟨o, by simpa [Algebra.smul_def] using ho⟩
  · intro h
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h
    intro i
    exact ⟨o, by simpa [Algebra.smul_def] using ho⟩

theorem absNorm_den_le (x : K) (d e : 𝓞 K) (hd : d ≠ 0) (hex : (e : K) = (d : K) * x)
    (B : Ideal (𝓞 K)) (hdB : Ideal.span {d} ≤ B) (heB : e ∈ B)
    (hfin : (Submodule.toAddSubgroup (Ideal.span {d})).relIndex (Submodule.toAddSubgroup B) ≠ 0) :
    Ideal.absNorm (den K x) ≤
      (Submodule.toAddSubgroup (Ideal.span {d})).relIndex (Submodule.toAddSubgroup B) := by
  set H := (Submodule.toAddSubgroup (Ideal.span {d})).addSubgroupOf (Submodule.toAddSubgroup B)
    with hH
  let g : 𝓞 K →+ Submodule.toAddSubgroup B :=
    { toFun := fun r => ⟨r * e, B.mul_mem_left r heB⟩
      map_zero' := by ext; simp
      map_add' := fun r s => by ext; simp [add_mul] }
  let f : 𝓞 K →+ (Submodule.toAddSubgroup B) ⧸ H := (QuotientAddGroup.mk' H).comp g
  have hdK : (d : K) ≠ 0 := by simpa using hd
  have hker : f.ker = Submodule.toAddSubgroup (den K x) := by
    ext r
    rw [AddMonoidHom.mem_ker]
    change (QuotientAddGroup.mk (g r) : _ ⧸ H) = 0 ↔ r ∈ den K x
    rw [QuotientAddGroup.eq_zero_iff, hH, AddSubgroup.mem_addSubgroupOf, mem_den_iff]
    change r * e ∈ Ideal.span {d} ↔ _
    rw [Ideal.mem_span_singleton', Submodule.mem_one]
    constructor
    · rintro ⟨o, ho⟩
      refine ⟨o, ?_⟩
      have := congrArg (fun y : 𝓞 K => (y : K)) ho
      simp only [map_mul, hex] at this
      apply mul_left_cancel₀ hdK
      change (d : K) * (o : K) = _
      linear_combination this
    · rintro ⟨o, ho⟩
      refine ⟨o, ?_⟩
      apply RingOfIntegers.coe_injective
      have ho' : (o : K) = (r : K) * x := ho
      simp only [map_mul, hex, ho']
      ring
  have hidx : (den K x).toAddSubgroup.index = Nat.card f.range := by
    rw [← hker]; exact AddSubgroup.index_ker f
  have hfinite : Finite ((Submodule.toAddSubgroup B) ⧸ H) := Nat.finite_of_card_ne_zero hfin
  calc Ideal.absNorm (den K x) = Nat.card f.range := by rw [Ideal.absNorm_eq_index]; exact hidx
    _ ≤ Nat.card ((Submodule.toAddSubgroup B) ⧸ H) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = _ := rfl

theorem span_le_mul (𝔱 a : Ideal (𝓞 K)) (h𝔱 : 𝔱 ≠ ⊥) (d : 𝓞 K) (hd : d ≠ 0)
    (H : ∀ b : K, (∀ u ∈ 𝔱, (u : K) * b ∈ (1 : Submodule (𝓞 K) K)) →
      ∃ y ∈ a, (y : K) = (d : K) * b) :
    Ideal.span {d} ≤ 𝔱 * a := by
  obtain ⟨s, hs𝔱, hs⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔱
  obtain ⟨𝔰, h𝔰⟩ := Ideal.dvd_span_singleton.2 hs𝔱
  have hsK : (s : K) ≠ 0 := by simpa using hs
  have h𝔰0 : 𝔰 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h𝔰
    exact hs (Ideal.span_singleton_eq_bot.1 h𝔰)
  have hle : Ideal.span {d} * 𝔰 ≤ (𝔱 * a) * 𝔰 := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro u hu
    have hmem : ∀ v ∈ 𝔱, (v : K) * ((u : K) / s) ∈ (1 : Submodule (𝓞 K) K) := by
      intro v hv
      have hvu : v * u ∈ Ideal.span {s} := by
        rw [h𝔰]; exact Ideal.mul_mem_mul hv hu
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hvu
      refine Submodule.mem_one.2 ⟨r, ?_⟩
      have := congrArg (fun y : 𝓞 K => (y : K)) hr
      simp only [map_mul] at this
      change (r : K) = _
      field_simp
      linear_combination this
    obtain ⟨y, hya, hy⟩ := H _ hmem
    have heq : d * u = s * y := by
      apply RingOfIntegers.coe_injective
      simp only [map_mul, hy]
      field_simp
    rw [heq, mul_right_comm 𝔱 a 𝔰, ← h𝔰, mul_comm s y]
    exact Ideal.mul_mem_mul hya (Ideal.mem_span_singleton_self s) |> fun h => by
      rwa [mul_comm a] at h
  rw [← Ideal.dvd_iff_le] at hle ⊢
  exact (mul_dvd_mul_iff_right h𝔰0).1 hle

theorem absNorm_mul_den_le_idx : ∀ (K : Type) [Field K] [NumberField K] (𝔱 : Ideal (𝓞 K)),
    𝔱 ≠ ⊥ → ∀ c : Submodule (𝓞 K) K, c.FG → (1 : Submodule (𝓞 K) K) ≤ c →
    (∀ b : K, (∀ a ∈ 𝔱, (a : K) * b ∈ (1 : Submodule (𝓞 K) K)) → b ∈ c) →
    ∀ (t : 𝓞 K) (w x : K), t ∈ 𝔱 → w ∈ c → (t : K) * w - x ∈ (1 : Submodule (𝓞 K) K) →
    Ideal.absNorm 𝔱 * Ideal.absNorm (den K x) ≤ idx K c := by
  intro K _ _ 𝔱 h𝔱 c hfg h1 hinv t w x ht hw hx
  obtain ⟨d, hd0, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 K)) hfg
  have hd : d ≠ 0 := nonZeroDivisors.ne_zero hd0
  have hdK : (d : K) ≠ 0 := by simpa using hd
  have hint' : ∀ b ∈ c, ∃ y : 𝓞 K, (y : K) = (d : K) * b := by
    intro b hb
    obtain ⟨y, hy⟩ := hint b hb
    exact ⟨y, by simpa [Algebra.smul_def] using hy⟩
  let g : 𝓞 K →ₗ[𝓞 K] K := LinearMap.toSpanSingleton (𝓞 K) K ((d : K)⁻¹)
  have hg : ∀ y : 𝓞 K, g y = (y : K) * (d : K)⁻¹ := fun y => by
    simp [g, LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  let a : Ideal (𝓞 K) := c.comap g
  have hmema : ∀ y : 𝓞 K, y ∈ a ↔ (y : K) * (d : K)⁻¹ ∈ c := fun y => by
    change g y ∈ c ↔ _
    rw [hg]
  have hga : ∀ b ∈ c, ∃ y ∈ a, (y : K) = (d : K) * b := by
    intro b hb
    obtain ⟨y, hy⟩ := hint' b hb
    refine ⟨y, (hmema y).2 ?_, hy⟩
    rw [hy]
    convert hb using 1
    field_simp
  have hda : d ∈ a := by
    rw [hmema, mul_inv_cancel₀ hdK]
    exact h1 (Submodule.one_le.1 le_rfl)
  have ha0 : a ≠ ⊥ := fun h => hd (by simpa [h] using hda)
  have hdle : Ideal.span {d} ≤ 𝔱 * a :=
    span_le_mul 𝔱 a h𝔱 d hd fun b hb => hga b (hinv b hb)
  have hBa : 𝔱 * a ≤ a := Ideal.mul_le_right

  have hinj : Function.Injective g.toAddMonoidHom := by
    intro y z hyz
    change g y = g z at hyz
    rw [hg, hg] at hyz
    exact RingOfIntegers.coe_injective (mul_right_cancel₀ (inv_ne_zero hdK) hyz)
  have hc : c.toAddSubgroup = (Submodule.toAddSubgroup a).map g.toAddMonoidHom := by
    ext b
    constructor
    · intro hb
      obtain ⟨y, hya, hy⟩ := hga b hb
      refine ⟨y, hya, ?_⟩
      change g y = b
      rw [hg, hy]
      field_simp
    · rintro ⟨y, hya, rfl⟩
      exact hya
  have hone : (1 : Submodule (𝓞 K) K).toAddSubgroup =
      (Submodule.toAddSubgroup (Ideal.span {d})).map g.toAddMonoidHom := by
    ext b
    constructor
    · intro hb
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 hb
      refine ⟨o * d, Ideal.mem_span_singleton'.2 ⟨o, rfl⟩, ?_⟩
      change g (o * d) = b
      rw [hg, ← ho]
      simp only [map_mul]
      change (o : K) * d * _ = o
      field_simp
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      refine Submodule.mem_one.2 ⟨o, ?_⟩
      change (o : K) = g (o * d)
      rw [hg]
      simp only [map_mul]
      field_simp
  have hidx : idx K c = (Submodule.toAddSubgroup (Ideal.span {d})).relIndex
      (Submodule.toAddSubgroup a) := by
    rw [idx, hc, hone, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  have hdB : Submodule.toAddSubgroup (Ideal.span {d}) ≤ Submodule.toAddSubgroup (𝔱 * a) :=
    (Submodule.toAddSubgroup_le _ _).2 hdle
  have hBa' : Submodule.toAddSubgroup (𝔱 * a) ≤ Submodule.toAddSubgroup a :=
    (Submodule.toAddSubgroup_le _ _).2 hBa
  have hfin : (Submodule.toAddSubgroup (Ideal.span {d})).relIndex
      (Submodule.toAddSubgroup (𝔱 * a)) ≠ 0 := by
    intro h0
    have h := AddSubgroup.relIndex_mul_index hdB
    rw [h0, zero_mul, index_toAddSubgroup] at h
    exact hd (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h.symm))

  obtain ⟨yw, hywa, hyw⟩ := hga w hw
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 hx
  have ho' : (o : K) = (t : K) * w - x := ho
  have heK : ((t * yw - d * o : 𝓞 K) : K) = (d : K) * x := by
    simp only [map_sub, map_mul, hyw, ho']
    ring
  have heB : t * yw - d * o ∈ 𝔱 * a :=
    Ideal.sub_mem _ (Ideal.mul_mem_mul ht hywa)
      (hdle (Ideal.mem_span_singleton'.2 ⟨o, mul_comm _ _⟩))
  have hden := absNorm_den_le x d _ hd heK (𝔱 * a) hdle heB hfin
  rw [hidx, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hdB hBa', relIndex_mul_ideal 𝔱 a ha0,
    mul_comm]
  exact Nat.mul_le_mul_right _ hden

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundByRecursion
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.DensityIter

theorem bounded_density_of_iterated
    (H ι : Type) [MeasurableSpace H] (ν : Measure H) (D : Set H → ℝ≥0∞) (Dtot : ℝ≥0∞)
    (hDtot : Dtot ≠ ⊤) (hD : ∀ Y, MeasurableSet Y → D Y ≤ Dtot)
    (I : Finset ι) (α β : ι → ℝ≥0) (C₀ : ℝ≥0)
    (hit : ∀ Y, MeasurableSet Y → ∃ Z : ι → Set H,
      (∀ i ∈ I, MeasurableSet (Z i) ∧ ν (Z i) = β i * ν Y) ∧
        D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i))
    (hρ : ∑ i ∈ I, α i * β i < 1) (hr : ∑ i ∈ I, α i < 1) :
    ∃ C : ℝ≥0, ∀ Y, MeasurableSet Y → D Y ≤ C * ν Y := by
  set ρ : ℝ≥0 := ∑ i ∈ I, α i * β i with hρdef
  set r : ℝ≥0 := ∑ i ∈ I, α i with hrdef
  set K : ℝ≥0 := C₀ / (1 - ρ) with hK
  have hKeq : C₀ + K * ρ = K := by
    have h1 : K * (1 - ρ) = C₀ := div_mul_cancel₀ C₀ (tsub_pos_of_lt hρ).ne'
    calc C₀ + K * ρ = K * (1 - ρ) + K * ρ := by rw [h1]
      _ = K * (1 - ρ + ρ) := by rw [mul_add]
      _ = K := by rw [tsub_add_cancel_of_le hρ.le, mul_one]
  have hKeq' : (C₀ : ℝ≥0∞) + K * ρ = K := by exact_mod_cast hKeq
  have hρc : (ρ : ℝ≥0∞) = ∑ i ∈ I, (α i : ℝ≥0∞) * β i := by
    simp only [hρdef, ENNReal.ofNNReal_finsetSum, ENNReal.coe_mul]
  have hrc : (r : ℝ≥0∞) = ∑ i ∈ I, (α i : ℝ≥0∞) := by
    simp only [hrdef, ENNReal.ofNNReal_finsetSum]
  have key : ∀ n : ℕ, ∀ Y, MeasurableSet Y → D Y ≤ K * ν Y + (r : ℝ≥0∞) ^ n * Dtot := by
    intro n
    induction n with
    | zero =>
      intro Y hY
      rw [pow_zero, one_mul]
      exact le_add_left (hD Y hY)
    | succ n ih =>
      intro Y hY
      obtain ⟨Z, hZ, hDY⟩ := hit Y hY
      have e1 : ∑ i ∈ I, (α i : ℝ≥0∞) * (K * ((β i : ℝ≥0∞) * ν Y)) = K * ρ * ν Y := by
        rw [hρc, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ i ∈ I, (α i : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n * Dtot) = (r : ℝ≥0∞) ^ (n + 1) * Dtot := by
        rw [← Finset.sum_mul, ← hrc]
        ring
      calc D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i) := hDY
        _ ≤ C₀ * ν Y + ∑ i ∈ I, (α i : ℝ≥0∞) * (K * ((β i : ℝ≥0∞) * ν Y) + (r : ℝ≥0∞) ^ n * Dtot) := by
          gcongr with i hi
          rw [← (hZ i hi).2]
          exact ih _ (hZ i hi).1
        _ = C₀ * ν Y + (K * ρ * ν Y + (r : ℝ≥0∞) ^ (n + 1) * Dtot) := by
          simp only [mul_add, Finset.sum_add_distrib, e1, e2]
        _ = K * ν Y + (r : ℝ≥0∞) ^ (n + 1) * Dtot := by
          rw [← add_assoc, ← add_mul, hKeq']
  refine ⟨K, fun Y hY => ?_⟩
  have hr1 : (r : ℝ≥0∞) < 1 := by exact_mod_cast hr
  have ht : Filter.Tendsto (fun n : ℕ => (K : ℝ≥0∞) * ν Y + (r : ℝ≥0∞) ^ n * Dtot) Filter.atTop
      (nhds ((K : ℝ≥0∞) * ν Y + 0 * Dtot)) :=
    tendsto_const_nhds.add
      (ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1) (Or.inr hDtot))
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht fun n => key n Y hY

end GlobalTheory.CompanionTheory.DensityIter
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagRigid
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DiagRigid

theorem diag_rigid : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ), Function.Injective y → ∀ (d d' : Fin n → Lˣ), (∀ i, ordL (d i : L) = y i) → (∀ i, ordL (d' i : L) = y i) → ∀ h : GL (Fin n) L, h⁻¹ * GlobalTheory.SmGL.diagT L (Fin n) d * h = GlobalTheory.SmGL.diagT L (Fin n) d' → d = d' ∧ ∃ s : Fin n → Lˣ, h = GlobalTheory.SmGL.diagT L (Fin n) s := by
  intro L _ _ n y hy d d' hd hd' h hh
  have key : GlobalTheory.SmGL.diagT L (Fin n) d * h = h * GlobalTheory.SmGL.diagT L (Fin n) d' := by
    rw [← hh]; simp only [mul_assoc, mul_inv_cancel_left]
  have key' : (Matrix.diagonal fun i => (d i : L)) * (h : Matrix (Fin n) (Fin n) L)
      = (h : Matrix (Fin n) (Fin n) L) * Matrix.diagonal fun i => (d' i : L) := by
    have := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L)) key
    simpa only [Units.val_mul, GlobalTheory.SmGL.val_diagT] using this
  have ent : ∀ i j, (d i : L) * (h : Matrix (Fin n) (Fin n) L) i j
      = (h : Matrix (Fin n) (Fin n) L) i j * (d' j : L) := by
    intro i j
    have := congrFun (congrFun key' i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have off : ∀ i j, i ≠ j → (h : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hij
    by_contra hne
    have e : (d i : L) = (d' j : L) := by
      have := ent i j
      rw [mul_comm] at this
      exact mul_left_cancel₀ hne this
    apply hij
    apply hy
    rw [← hd i, ← hd' j, e]
  have hdiag : (h : Matrix (Fin n) (Fin n) L)
      = Matrix.diagonal fun i => (h : Matrix (Fin n) (Fin n) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]; exact off i j hij
  have hdet : ∏ i, (h : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
    have h1 : IsUnit (h : Matrix (Fin n) (Fin n) L).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
    rw [hdiag, Matrix.det_diagonal] at h1
    simpa [Matrix.diagonal_apply_eq] using h1.ne_zero
  have hii : ∀ i, (h : Matrix (Fin n) (Fin n) L) i i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  refine ⟨?_, fun i => Units.mk0 _ (hii i), ?_⟩
  · funext i
    apply Units.ext
    have := ent i i
    rw [mul_comm] at this
    exact mul_left_cancel₀ (hii i) this
  · apply Units.ext
    rw [GlobalTheory.SmGL.val_diagT]
    simpa using hdiag

end GlobalTheory.CompanionTheory.DiagRigid
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisorGeneralPointBranches
section
namespace GlobalTheory.CompanionTheory.ComplexSets


open GroundTheory.Heights₂.Heights in
theorem divisorGeneralPointBranches : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement :=
  DivisorGeneralPointBranches.proof DivisorOneComponent.proof
    (DivisorBranches.proof IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof
      GroundTheory.Heights₂.Heights.AutoClose.DivisorRegularGeneric
      (NormalDivisorChartGeneric.proof
        (NormalModelDivisorChartGeneric.proof
          (NormalModelGoodPointGeneric.proof NormalCodimOneCompleteIntersection.proof
            NormalCodimOneUniformiser.proof JacobianRankOffHypersurface.proof
            ProjectionUnramifiedGeneric.proof)
          NormalModelGoodPointChart.proof))
      NormalDoublePointsGeneric.proof DivisorGoodPointBranches.proof)

end GlobalTheory.CompanionTheory.ComplexSets
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesContinuation
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.SiegelEis

theorem rpow_le_add_rpow {A u c d : ℝ} (hA : 0 < A) (hc : c ≤ u) (hd : u ≤ d) :
    A ^ u ≤ A ^ c + A ^ d := by
  rcases le_total 1 A with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hd
    have := Real.rpow_nonneg hA.le c
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hA h hc
    have := Real.rpow_nonneg hA.le d
    linarith

theorem differentiable_cpow_term {A : ℝ} (hA : 0 < A) (s₁ w : ℂ) :
    Differentiable ℂ (fun s : ℂ => (A : ℂ) ^ (s - s₁) * w) := by
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  exact ((differentiable_id.sub_const s₁).const_cpow (Or.inl hA')).mul_const w

theorem eis_half_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧ ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  intro F E _ _ _ _ _ σ B n Y r s' hB hn hY b K a hb hK hH χ s₁ f hf
  have hKc := GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s' hB hn hY b K a hb hK hH
  obtain ⟨-, hpos⟩ := GlobalTheory.T.height_function_continuous_pos' F E σ B n Y r s' hB hn hY b K a hb hK hH
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.flat_section_growth_bound K a hKc hH hpos χ s₁ f hf
  obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.T.eisenstein_series_convergent F E σ B n Y r s' hB hn hY b K a hb hK hH
  have hC : ∀ s x, ‖flat a f s₁ s x‖ ≤ max C₀ 0 * a x ^ (s.re + (n : ℝ) / 2) := fun s x =>
    (hC₀ s x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hpos x).le _))
  have hsum : ∀ σ' : ℝ, σ₀ < σ' → ∀ x, Summable fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ' := by
    intro σ' h x
    obtain ⟨C', N, h'⟩ := hσ₀ σ' h
    exact (h' x).1
  refine ⟨fun s x => ∑' q, eisTerm (flat a f s₁ s) x q, σ₀ - (n : ℝ) / 2, ?_, ?_⟩
  · intro s hs x
    apply Summable.hasSum
    have hg := (hsum (s.re + (n : ℝ) / 2) (by linarith) x).mul_left (max C₀ 0)
    first
      | exact Summable.of_norm_bounded _ hg (fun q => hC s _)
      | exact Summable.of_norm_bounded hg (fun q => hC s _)
  · intro x s₀ hs₀
    have hs₀' : σ₀ - (n : ℝ) / 2 < s₀.re := hs₀
    set c := (σ₀ - (n : ℝ) / 2 + s₀.re) / 2 with hc
    set d := s₀.re + 1 with hd
    have hU : IsOpen {s : ℂ | c < s.re ∧ s.re < d} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hmem : {s : ℂ | c < s.re ∧ s.re < d} ∈ 𝓝 s₀ :=
      hU.mem_nhds ⟨by linarith, by linarith⟩
    have hg : Summable fun q : Cos σ Y => max C₀ 0 * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
        a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2)) :=
      ((hsum _ (by linarith) x).add (hsum _ (by linarith) x)).mul_left (max C₀ 0)
    have hD : DifferentiableOn ℂ (fun s => ∑' q, eisTerm (flat a f s₁ s) x q) {s : ℂ | c < s.re ∧ s.re < d} := by
      refine Complex.differentiableOn_tsum_of_summable_norm (F := fun q s => eisTerm (flat a f s₁ s) x q) hg
        (fun q => ?_) hU (fun q s hs => ?_)
      · exact (differentiable_cpow_term (hpos _) s₁ (f ((Quotient.out q).1 * x))).differentiableOn
      · refine (hC s _).trans (mul_le_mul_of_nonneg_left (rpow_le_add_rpow (hpos _) ?_ ?_) (le_max_right _ _))
        · linarith [hs.1]
        · linarith [hs.2]
    exact (hD.differentiableAt hmem).differentiableWithinAt

end GlobalTheory.CompanionTheory.SiegelEis
end

