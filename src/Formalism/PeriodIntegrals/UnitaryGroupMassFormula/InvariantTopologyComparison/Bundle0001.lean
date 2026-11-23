module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.EntriesLat

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.FiniteNeighbourhoodSecond
section
noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Topology Filter

theorem isOpen_intAd (F : Type) [Field F] [NumberField F] :
    IsOpen ((Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))) :=
  RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _

theorem finite_neighbourhood_first : FinNhdA := by
  intro F _ _ N hN
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hu : IsUnit (N : FiniteAdeleRing (𝓞 F) F) := by
    have : (N : FiniteAdeleRing (𝓞 F) F) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F) := by
      simp
    rw [this]
    exact (IsUnit.mk0 _ hNF).map _
  obtain ⟨u, hu⟩ := hu
  have hcont : Continuous (fun a : FiniteAdeleRing (𝓞 F) F => ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) * a) := continuous_const.mul continuous_id
  refine Filter.mem_of_superset (((isOpen_intAd F).preimage hcont).mem_nhds ?_) ?_
  · simp only [Set.mem_preimage, mul_zero, SetLike.mem_coe]
    exact zero_mem _
  · intro a ha
    refine ⟨_, ha, ?_⟩
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]

theorem natCast_apply (F : Type) [Field F] [NumberField F] (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (N : FiniteAdeleRing (𝓞 F) F) v = (N : v.adicCompletion F) := by
  induction N with
  | zero =>
    rw [Nat.cast_zero, Nat.cast_zero]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← ih]
    rfl

theorem natCast_mul_apply (F : Type) [Field F] [NumberField F] (N : ℕ)
    (z : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((N : FiniteAdeleRing (𝓞 F) F) * z) v = (N : v.adicCompletion F) * z v := by
  rw [← natCast_apply F N v]
  rfl

theorem norm_natCast_lt_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) : ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e : (c : v.adicCompletion F) = (((algebraMap (𝓞 F) F (c : 𝓞 F)) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    rw [show (((c : F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (c : F) from rfl,
      map_natCast]
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hval

theorem finite_neighbourhood_second : FinNhdB := by
  intro F _ _ U hU
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun _ => Valued.isOpen_valuationSubring _
  have hU' : U ∈ Filter.map (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
      (𝓝 (fun v => ⟨0, zero_mem (v.adicCompletionIntegers F)⟩)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hAopen]
    exact hU
  have hU2 : (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) ⁻¹'
      (U : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)) ∈
      𝓝 (fun v : HeightOneSpectrum (𝓞 F) => (⟨0, zero_mem (v.adicCompletionIntegers F)⟩ :
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := hU'
  rw [nhds_pi, Filter.mem_pi] at hU2
  obtain ⟨I, hI, t, ht, hIt⟩ := hU2
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > (0 : ℝ),
      ∀ y : (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        ‖(y : v.adicCompletion F)‖ < ε → y ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨ε, hε, fun y hy => hut (hball ?_)⟩
    simpa [Metric.mem_ball, dist_zero_right] using hy
  choose ε hεpos hεt using hε
  set c : ℕ := ∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one F v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))
  have hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v := fun v hv =>
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually
      (Iio_mem_nhds (hεpos v))
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hI).2 hev).exists
  refine ⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun z hz => ?_⟩
  have hmem : ∀ v, (((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v ∈
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    rw [natCast_mul_apply]
    exact mul_mem (natCast_mem _ _) (hz v)
  have hx : ((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z = RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
      (fun v => ⟨_, hmem v⟩) := by
    ext v
    rfl
  rw [hx]
  apply hIt
  intro v hv
  apply hεt
  show ‖(((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v‖ < ε v
  rw [natCast_mul_apply, norm_mul, Nat.cast_pow, norm_pow]
  have hz1 : ‖z v‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v)
  calc ‖(c : v.adicCompletion F)‖ ^ k * ‖z v‖ ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 :=
        mul_le_mul_of_nonneg_left hz1 (pow_nonneg (norm_nonneg _) _)
    _ < ε v := by rw [mul_one]; exact hk v hv

end PI.InvTopW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.LinearIndependentOneBeta
section
noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

variable (I : AutInst)

theorem exists_not_mem_range : ∃ x : I.E, x ∉ Set.range (algebraMap I.F I.E) := by
  by_contra h
  push_neg at h
  have hs : Function.Surjective (Algebra.linearMap I.F I.E) := fun x => by
    obtain ⟨a, ha⟩ := h x
    exact ⟨a, ha⟩
  have e := (LinearEquiv.ofBijective (Algebra.linearMap I.F I.E)
    ⟨(algebraMap I.F I.E).injective, hs⟩).finrank_eq
  rw [I.cm.deg2] at e
  rw [Module.finrank_self] at e
  omega

private theorem exists_nat_mul_lemma {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ d : ℕ, 1 ≤ d ∧ (d : E) * x ∈ Formalism.UG.intOE E := by
  have H : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * x) := by
    have hq : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) x hq
    exact ⟨m, nonZeroDivisors.coe_ne_zero m, by rw [← zsmul_eq_mul]; exact hm⟩
  obtain ⟨y, hy0, hint⟩ := H
  have hmem : (y : E) * x ∈ Formalism.UG.intOE E :=
    RingHom.mem_range.2 ((IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hy0), ?_⟩
    simpa using hmem
  · refine ⟨n, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hy0), ?_⟩
    simpa using hmem

theorem exists_beta : ∃ β : I.E, β ∈ Formalism.UG.intOE I.E ∧ β ∉ Set.range (algebraMap I.F I.E) := by
  obtain ⟨x, hx⟩ := exists_not_mem_range I
  obtain ⟨d, hd, hdx⟩ := exists_nat_mul_lemma x
  have hd0 : (d : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨(d : I.E) * x, hdx, fun ⟨a, ha⟩ => hx ⟨a / d, ?_⟩⟩
  rw [map_div₀, map_natCast, ha]
  exact mul_div_cancel_left₀ x hd0

def beta : I.E := (exists_beta I).choose

theorem beta_mem : beta I ∈ Formalism.UG.intOE I.E := (exists_beta I).choose_spec.1

theorem beta_not_mem : beta I ∉ Set.range (algebraMap I.F I.E) := (exists_beta I).choose_spec.2

theorem linearIndependent_one_beta : LinearIndependent I.F ![(1 : I.E), beta I] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp at hst
    exact ⟨hst, rfl⟩
  · exfalso
    apply beta_not_mem I
    refine ⟨-s / t, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have ht' : algebraMap I.F I.E t ≠ 0 := (map_ne_zero _).2 ht
    rw [map_div₀, map_neg, div_eq_iff ht']
    linear_combination -hst

def basisE : Module.Basis (Fin 2) I.F I.E :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_beta I)
    (by rw [Fintype.card_fin, I.cm.deg2])

theorem basisE_apply (k : Fin 2) : basisE I k = ![(1 : I.E), beta I] k := by
  simp [basisE]

theorem basisE_mem (k : Fin 2) : basisE I k ∈ Formalism.UG.intOE I.E := by
  rw [basisE_apply]
  fin_cases k
  · exact one_mem _
  · exact beta_mem I

end PI.InvTopW
end
end

