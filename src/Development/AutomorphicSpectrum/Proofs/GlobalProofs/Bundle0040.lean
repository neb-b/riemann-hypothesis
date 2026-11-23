module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.WeilBound.CoreStatements.MeasureExistence.ExistsMeas

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HaarIntegralIntegersFiniteSum
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

open MeasureTheory

namespace GlobalTheory.CompanionTheory.PeriodicInt

variable {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)}

theorem valued_algebraMap (x : E) :
    Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem valued_int_le_one (a : 𝓞 E) :
    Valued.v (algebraMap E (v.adicCompletion E) (a : E)) ≤ 1 := by
  rw [valued_algebraMap]
  exact v.valuation_le_one a

theorem valued_le_one_of_mem_valBall {m : ℕ} {x : v.adicCompletion E}
    (h : x ∈ valBall (v.adicCompletion E) (m : ℤ)) : Valued.v x ≤ 1 := by
  refine (mem_valBall_iff_valued.1 h).trans ?_
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem exists_int_close (m : ℕ) {y : v.adicCompletion E} (hy : Valued.v y ≤ 1) :
    ∃ a : 𝓞 E, y - algebraMap E (v.adicCompletion E) (a : E) ∈
      valBall (v.adicCompletion E) (m : ℤ) := by
  have hopen : IsOpen {z : v.adicCompletion E | y - z ∈ valBall (v.adicCompletion E) (m : ℤ)} :=
    (isOpen_valBall (m : ℤ)).preimage (continuous_const.sub continuous_id)
  obtain ⟨x, hx⟩ := (v.denseRange_algebraMap E).exists_mem_open hopen
    ⟨y, by simp [zero_mem]⟩
  have hx' : y - algebraMap E (v.adicCompletion E) x ∈ valBall (v.adicCompletion E) (m : ℤ) := hx
  have h1 : Valued.v (algebraMap E (v.adicCompletion E) x) ≤ 1 := by
    have e : algebraMap E (v.adicCompletion E) x =
        y - (y - algebraMap E (v.adicCompletion E) x) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hy (valued_le_one_of_mem_valBall hx'))
  rw [valued_algebraMap] at h1
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer h1
    (Units.mk0 _ (WithZero.exp_ne_zero (a := -(m : ℤ))))
  rw [Units.val_mk0] at ha
  refine ⟨a, ?_⟩
  have e : y - algebraMap E (v.adicCompletion E) (a : E) =
      (y - algebraMap E (v.adicCompletion E) x) +
        algebraMap E (v.adicCompletion E) (x - (a : E)) := by
    rw [map_sub]; ring
  rw [e]
  refine add_mem hx' (mem_valBall_iff_valued.2 ?_)
  rw [valued_algebraMap, Valuation.map_sub_swap]
  exact ha.le

theorem sub_mem_pow_of_close {m : ℕ} {a b : 𝓞 E}
    (h : algebraMap E (v.adicCompletion E) (a : E) - algebraMap E (v.adicCompletion E) (b : E) ∈
      valBall (v.adicCompletion E) (m : ℤ)) : a - b ∈ v.asIdeal ^ m := by
  have h1 := mem_valBall_iff_valued.1 h
  rw [← map_sub, valued_algebraMap] at h1
  rw [← v.intValuation_le_pow_iff_mem, ← v.valuation_of_algebraMap (K := E)]
  simpa using h1

theorem close_of_sub_mem_pow {m : ℕ} {a b : 𝓞 E} (h : a - b ∈ v.asIdeal ^ m) :
    algebraMap E (v.adicCompletion E) (a : E) - algebraMap E (v.adicCompletion E) (b : E) ∈
      valBall (v.adicCompletion E) (m : ℤ) := by
  rw [mem_valBall_iff_valued, ← map_sub, valued_algebraMap]
  exact valuation_sub_le h

theorem integral_eq_finsum : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (g : v.adicCompletion E → ℂ), (∀ y, 1 < Valued.v y → g y = 0) → (∀ y h : v.adicCompletion E, Valued.v h ≤ WithZero.exp (-(m : ℤ)) → g (y + h) = g y) → ∫ y, g y ∂haarIntegers (v.adicCompletion E) = (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ))⁻¹ * ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, g (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) := by
  intro E _ _ v m g h0 hp
  classical
  have : Finite (𝓞 E ⧸ v.asIdeal ^ m) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ v.ne_bot)
  have := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal ^ m)
  let a : (𝓞 E ⧸ v.asIdeal ^ m) → v.adicCompletion E := fun r =>
    algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)
  let S : (𝓞 E ⧸ v.asIdeal ^ m) → Set (v.adicCompletion E) := fun r =>
    (fun y => y + (-a r)) ⁻¹' (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E))
  have memS : ∀ r y, y ∈ S r ↔ y - a r ∈ valBall (v.adicCompletion E) (m : ℤ) := fun r y => by
    simp only [S, Set.mem_preimage, SetLike.mem_coe, sub_eq_add_neg]
  have hSm : ∀ r, MeasurableSet (S r) := fun r =>
    ((isOpen_valBall (m : ℤ)).preimage (continuous_id.add continuous_const)).measurableSet
  have hB : (haarIntegers (v.adicCompletion E)).real
      (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E)) =
      (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ))⁻¹ := by
    rw [measureReal_def, haarIntegers_valBall, residueCard_adicCompletion, ENNReal.coe_toReal,
      NNReal.coe_zpow, NNReal.coe_natCast, zpow_neg, zpow_natCast]
    push_cast
    rfl
  have hSμ : ∀ r, (haarIntegers (v.adicCompletion E)).real (S r) =
      (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ))⁻¹ := fun r => by
    rw [← hB, measureReal_def, measureReal_def]
    exact congrArg ENNReal.toReal (measure_preimage_add_right _ _ _)
  have hfin : ∀ r, haarIntegers (v.adicCompletion E) (S r) ≠ ⊤ := fun r => by
    have : haarIntegers (v.adicCompletion E) (S r) =
        haarIntegers (v.adicCompletion E)
          (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E)) :=
      measure_preimage_add_right _ _ _
    rw [this, haarIntegers_valBall]
    exact ENNReal.coe_ne_top
  have hdecomp : ∀ y, g y = ∑ r, (S r).indicator (fun _ => g (a r)) y := by
    intro y
    by_cases hy : Valued.v y ≤ 1
    · obtain ⟨b, hb⟩ := exists_int_close (v := v) m hy
      set r : 𝓞 E ⧸ v.asIdeal ^ m := Ideal.Quotient.mk _ b with hr
      have hclose : a r - algebraMap E (v.adicCompletion E) (b : E) ∈
          valBall (v.adicCompletion E) (m : ℤ) :=
        close_of_sub_mem_pow (Ideal.Quotient.eq.1 (by rw [Ideal.Quotient.mk_out]))
      have hyr : y ∈ S r := by
        rw [memS]
        have e : y - a r = (y - algebraMap E (v.adicCompletion E) (b : E)) -
            (a r - algebraMap E (v.adicCompletion E) (b : E)) := by ring
        rw [e]
        exact sub_mem hb hclose
      rw [Finset.sum_eq_single r, Set.indicator_of_mem hyr]
      · have := hp (a r) (y - a r) (mem_valBall_iff_valued.1 ((memS r y).1 hyr))
        rwa [add_sub_cancel] at this
      · intro r' _ hne
        refine Set.indicator_of_notMem (fun hyr' => hne ?_) _
        have h1 := sub_mem ((memS r y).1 hyr) ((memS r' y).1 hyr')
        have e : y - a r - (y - a r') = a r' - a r := by ring
        rw [e] at h1
        have h2 := sub_mem_pow_of_close h1
        have h3 := Ideal.Quotient.eq.2 h2
        simpa [Ideal.Quotient.mk_out] using h3
      · simp
    · rw [h0 y (not_le.1 hy)]
      refine (Finset.sum_eq_zero fun r _ => Set.indicator_of_notMem (fun hyr => hy ?_) _).symm
      have e : y = (y - a r) + a r := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans
        (max_le (valued_le_one_of_mem_valBall ((memS r y).1 hyr)) (valued_int_le_one _))
  have hint : ∀ r, Integrable ((S r).indicator (fun _ => g (a r)))
      (haarIntegers (v.adicCompletion E)) := fun r =>
    (integrable_indicator_iff (hSm r)).2 (integrableOn_const (hfin r))
  calc ∫ y, g y ∂haarIntegers (v.adicCompletion E)
      = ∫ y, ∑ r, (S r).indicator (fun _ => g (a r)) y ∂haarIntegers (v.adicCompletion E) :=
        integral_congr_ae (Filter.Eventually.of_forall hdecomp)
    _ = ∑ r, ∫ y, (S r).indicator (fun _ => g (a r)) y ∂haarIntegers (v.adicCompletion E) :=
        integral_finsetSum _ fun r _ => hint r
    _ = _ := by
        rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [integral_indicator_const _ (hSm r), hSμ r, Complex.real_smul]
        push_cast
        rfl

end GlobalTheory.CompanionTheory.PeriodicInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeGaussSumLocalTerm
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge.GaussSum

variable {E : Type} [Field E] [NumberField E]

theorem dvd_conductor (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0)
    (h : ExpAt χ v m) : v.asIdeal ∣ (toHecke χ hu).conductor := by
  by_contra hv
  refine h.not_unrAt hm fun x hx => ?_
  have hx' : Valued.v (x : v.adicCompletion E) = 1 := hx
  have hmem : x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units := by
    refine Submonoid.mem_units_iff _ _ |>.2 ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx'.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx', inv_one]
  have h1 := (toHecke χ hu).localComponent_eq_one_of_not_dvd hv hmem
  have h2 := coe_localComponent χ hu v x
  rw [h1] at h2
  exact Units.ext (by simpa using h2.symm)

theorem hval (v : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem valued_eq_one {v : HeightOneSpectrum (𝓞 E)} {y : 𝓞 E} (hy : y ∉ v.asIdeal) :
    Valued.v (algebraMap E (v.adicCompletion E) (y : E)) = 1 := by
  exact (hval v _).trans ((v.valuation_eq_one_iff_notMem (K := E)).2 hy)

theorem valued_ne_one {v : HeightOneSpectrum (𝓞 E)} {y : 𝓞 E} (hy : y ∈ v.asIdeal) :
    Valued.v (algebraMap E (v.adicCompletion E) (y : E)) ≠ 1 := by
  exact fun h => (v.valuation_eq_one_iff_notMem (K := E)).1 ((hval v _).symm.trans h) hy

theorem term_of_notMem (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal ∣ (toHecke χ hu).conductor) (c : Eˣ) {y : 𝓞 E} (hy : y ∉ v.asIdeal) :
    (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) (y : E)) *
        psiAt v (((atFin v c : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * algebraMap E (v.adicCompletion E) (y : E)) =
      gaussTerm χ v c (y : E) := by
  have hy0 : (y : E) ≠ 0 := by
    intro h0
    have : y = 0 := by exact_mod_cast h0
    exact hy (this ▸ v.asIdeal.zero_mem)
  have h1 := (toHecke χ hu).finiteTest_of_dvd hv (atFin v (Units.mk0 (y : E) hy0)) (valued_eq_one hy)
  have h2 : ((atFin v (Units.mk0 (y : E) hy0) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (y : E) := rfl
  rw [h2] at h1
  rw [h1, coe_localComponent, gaussTerm, dite_eq_right hy0, Units.val_inv_eq_inv_val]
  have h3 : ((atFin v c : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (c : E) := rfl
  rw [h3, map_div₀, div_eq_mul_inv, mul_comm (algebraMap E _ _)]
  rfl

theorem finiteTest_sum_eq_gaussSumAt (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ)
    (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (hm : m ≠ 0) (hE : ExpAt χ v m) :
    ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) =
      gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  have hv := dvd_conductor χ hu v hm hE
  rw [gaussSumAt]
  have hG : ∀ y : (𝓞 E ⧸ v.asIdeal ^ m)ˣ, gaussTerm χ v (unif v ^ (m + diffExp v)) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E) =
      (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E)) :=
    fun y => (term_of_notMem χ hu v hv _ (out_notMem v hm y)).symm
  rw [finsum_congr hG, ← finsum_mem_range (g := ((↑) : (𝓞 E ⧸ v.asIdeal ^ m)ˣ → 𝓞 E ⧸ v.asIdeal ^ m)) Units.val_injective
    (f := fun r : 𝓞 E ⧸ v.asIdeal ^ m => (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E))), finsum_mem_def]
  refine finsum_congr fun r => ?_
  by_cases hr : r ∈ Set.range ((↑) : (𝓞 E ⧸ v.asIdeal ^ m)ˣ → 𝓞 E ⧸ v.asIdeal ^ m)
  · rw [Set.indicator_of_mem hr]
  · rw [Set.indicator_of_notMem hr]
    have hmem : (Quotient.out r : 𝓞 E) ∈ v.asIdeal := by
      by_contra hn
      have h1 := Ideal.Quotient.isUnit_mk_pow_of_notMem v.asIdeal (n := m) hn
      rw [Ideal.Quotient.mk_out] at h1
      exact hr ⟨h1.unit, rfl⟩
    rw [(toHecke χ hu).finiteTest_eq_zero_of_dvd hv (valued_ne_one hmem), zero_mul]

end GlobalTheory.CompanionTheory.HeckeBridge.GaussSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeLFunctionEulerProduct
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

theorem unrAt_iff_not_dvd_conductor (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) :
    χ.UnrAt v ↔ ¬ v.asIdeal ∣ (toHecke χ hu).conductor := by
  rw [HeckeCharacter.not_dvd_conductor_iff]
  constructor
  · intro h a ha
    rw [Submonoid.mem_units_iff] at ha
    have h1 : Valued.v (a : v.adicCompletion E) ≤ 1 := ha.1
    have h2 : Valued.v ((a⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 := ha.2
    have h3 : Valued.v (a : v.adicCompletion E) = 1 := by
      refine le_antisymm h1 ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
      exact (inv_le_one₀ (by simp [zero_lt_iff])).1 h2
    rw [MonoidHom.mem_ker]
    show (toHecke χ hu).localComponent v a = 1
    apply Circle.ext
    rw [coe_localComponent, h a h3]
    simp
  · intro h x hx
    have hx' : x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units := by
      rw [Submonoid.mem_units_iff]
      refine ⟨le_of_eq hx, ?_⟩
      show Valued.v ((x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      have hx1 : Valued.v (x : v.adicCompletion E) = 1 := hx
      rw [hx1, inv_one]
    have h1 : (toHecke χ hu).localComponent v x = 1 := MonoidHom.mem_ker.1 (h hx')
    have h2 := coe_localComponent χ hu v x
    rw [h1] at h2
    ext
    simpa using h2.symm

theorem coeff_eq_val (χ : HChar E) (hu : IsUnitary χ) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ¬ v.asIdeal ∣ (toHecke χ hu).conductor) :
    (toHecke χ hu).coeff v.asIdeal = (χ.val v : ℂ) := by
  rw [(toHecke χ hu).coeff_asIdeal_eq_toIdele hv (unif_spec v), ← HeckeCharacter.localComponent_apply,
    coe_localComponent]
  rfl

theorem hasProd_eulerFactor_toHecke : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (s : ℂ),
    1 < s.re → HasProd (eulerFactor χ s) ((toHecke χ hu).LFunction s) := by
  intro E _ _ χ hu s hs
  have h : eulerFactor χ s = fun v : HeightOneSpectrum (𝓞 E) ↦
      (1 - (toHecke χ hu).coeff v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
    funext v
    unfold eulerFactor
    by_cases hv : χ.UnrAt v
    · rw [if_pos hv, coeff_eq_val χ hu ((unrAt_iff_not_dvd_conductor χ hu v).1 hv)]
    · rw [if_neg hv, HeckeCharacter.coeff_asIdeal_of_dvd _
        (not_not.1 (mt (unrAt_iff_not_dvd_conductor χ hu v).2 hv))]
      simp
  rw [h]
  exact (toHecke χ hu).LFunction_hasProd_all hs

end GlobalTheory.CompanionTheory.HeckeBridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp

open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}


variable (θ V) in
abbrev Mc : Submodule ℂ (GA D V → ℂ) := GlobalTheory.Cusp.cuspForms θ V ⊥

theorem mem_Mc_iff {φ : GA D V → ℂ} : φ ∈ Mc θ V ↔ IsAutFunSm θ V φ ∧ IsCuspFun V φ := by
  refine ⟨fun h => (mem_cuspForms.1 h).1, fun h => mem_cuspForms.2 ⟨h, ?_⟩⟩
  refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨Submodule.span ℂ {φ}, inferInstance, fun k hk => ?_⟩
  rw [Subgroup.mem_bot.1 hk]
  exact Submodule.subset_span (by simp)

def der (hθ : IsInfFam θ) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Module.End ℂ (Mc θ V) where
  toFun φ := ⟨Rder θ V τ X φ.1, mem_Mc_iff.2
    ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX (mem_Mc_iff.1 φ.2).1,
      GlobalTheory.CuspLie.isCuspFun_Rder hθ hX (mem_Mc_iff.1 φ.2).1 (mem_Mc_iff.1 φ.2).2⟩⟩
  map_add' f g := Subtype.ext (Rder_add (mem_Mc_iff.1 f.2).1.smooth (mem_Mc_iff.1 g.2).1.smooth hX)
  map_smul' c f := Subtype.ext (Rder_smul c f.1 τ X)

def io (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) : Mc θ V →ₗ[ℂ] L2cusp V μ :=
  GlobalTheory.Cusp.cuspToL2 ⊥ μ
    (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound) hθ

theorem io_injective (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) :
    Function.Injective (io (V := V) μ hθ) := cusp_form_toL2_injective _ hθ

def derInf (hθ : IsInfFam θ) (X : GlobalTheory.SmoothForms.LieN V) : Module.End ℂ (Mc θ V) :=
  ∑ τ, der hθ τ (X := (X τ).1) (X τ).2

def IsKLie {n : ℕ} (e : Fin n → Bool) (y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  yᴴ = -y ∧ y * Formalism.REAL.Jm e = Formalism.REAL.Jm e * y

end GlobalTheory.CompanionTheory.HCCusp
end
end

