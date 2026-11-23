module

public import Formalism.LocalToGlobal.ExponentGrids.ScaledCoordinatesValuationLemma
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.KappaNormalise
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.PairingDivisors.PairingDivisorProofs.Height
public import Formalism.PairingDivisors.PairingDivisorProofs.SumValuationNat
public import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
public import Formalism.TowerValuationBounds.TowerValuationProofs.SumAdditiveCharacterEqZero
public import Lemmata.PlaneOverMembership.PlOverOfMem

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)

noncomputable section

namespace Formalism.AtG

theorem grid_ell_bound : FinitePlaceLiesOverPrime := by
  first | exact Bl.PlaneOverMembership.goal1 .. | (apply Bl.PlaneOverMembership.goal1 <;> assumption) | (intros; apply Bl.PlaneOverMembership.goal1 <;> assumption) | (apply @Bl.PlaneOverMembership.goal1 <;> assumption) | (intros; apply @Bl.PlaneOverMembership.goal1 <;> assumption) | (apply @Bl.PlaneOverMembership.goal1 <;> first | assumption | infer_instance)

theorem sum_le_finsum' {α : Type} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hs : (Function.support f).Finite)
    (F : Finset α) : ∑ a ∈ F, f a ≤ ∑ᶠ a, f a := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := hs.toFinset ∪ F) (by
    intro x hx
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact Or.inl hx)]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun a _ _ => hf a)

theorem partial_nat (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ)
    (F : Finset (Pl K)) : ∑ w ∈ F, lw w * (vw w (n : K) : ℝ) ≤ Real.log n := by
  obtain ⟨h1, h2⟩ := Formalism.PairingDivisionLocalBalance.sum_valuation_nat K n
  rw [← h2]
  exact sum_le_finsum' _ (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w)
    (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w n)) h1 F

theorem partial_ht {K : Type} [Field K] [NumberField K] [StarRing K] {g : Pl K → ℤ} {z : K} {B : ℝ}
    (h : HtLe g z B) (F : Finset (Pl K)) :
    ∑ w ∈ F, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ B :=
  (sum_le_finsum' _ (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w) (abs_nonneg _)) h.1 F).trans h.2

theorem j3Wt : NormalisedPrimeUnitWeight := by
  intro K _ _ _ ell hell S c hS w
  classical
  have hz : ∀ l ∈ S, l ≠ ell w → (vw w (l : K) : ℝ) = 0 := by
    intro l hl hne
    have hco : Nat.Coprime l (ell w) := (Nat.coprime_primes (hS l hl) (hell w).1).2 hne
    have h1 := Formalism.DivisionValues.places_over_coprime K l (ell w) hco w
    have h2 : ¬ PlOver l w := fun h => h1 ⟨h, (hell w).2⟩
    have h3 := Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l
    unfold Formalism.DivisionValues.PlOver at h2
    have : vw w (l : K) = 0 := by omega
    exact_mod_cast this
  unfold Formalism.PairingDivisionLocalBalance.wt
  by_cases h : ell w ∈ S
  · rw [if_pos h, Finset.sum_eq_single_of_mem (ell w) h]
    intro l hl hne
    rw [hz l hl hne, mul_zero]
  · rw [if_neg h, zero_mul]
    apply Finset.sum_eq_zero
    intro l hl
    rw [hz l hl (fun e => h (e ▸ hl)), mul_zero]

theorem norm_height_bound : DisjointUnionFactorProduct := by
  intro K _ _ _ _ x dl Bδ hx hdl hden hB
  classical
  obtain ⟨hfin, hpf⟩ := Formalism.DivisionValues.prod_formula' K x hx
  have hc : (Fintype.card (InfinitePlace K) : ℝ) * 2 = (finrank ℚ K : ℝ) := by
    have h3 := IsTotallyComplex.finrank K
    have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h5 := IsTotallyComplex.nrRealPlaces_eq_zero K
    rw [h3, h4, h5]; push_cast; ring
  have hpos : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hcard : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hc; linarith
  have hmean : ∀ φ : InfinitePlace K → ℝ,
      (2 / (finrank ℚ K : ℝ)) * ∑ v, φ v = (∑ v, φ v) / Fintype.card (InfinitePlace K) := by
    intro φ
    rw [← hc]
    field_simp
  have hsupp : ∀ w, w ∉ hfin.toFinset → ((vw w x : ℤ) : ℝ) = 0 := by
    intro w hw
    have h0 : lw w * (vw w x : ℝ) = 0 := by
      by_contra hne
      exact hw (hfin.mem_toFinset.2 hne)
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (Formalism.DivisionValues.PlaceSumConjugation.lw_pos w).ne'
    · exact h
  have hsum : ∑ w ∈ hfin.toFinset, lw w * (vw w x : ℝ) =
      (∑ v : InfinitePlace K, Real.log ‖v.embedding x‖) / Fintype.card (InfinitePlace K) := by
    rw [← hmean, hpf, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp)]
  obtain ⟨_, _, h3⟩ := Formalism.ValuationGridEstimates.height_bound_alt (Pl K) (InfinitePlace K) (fun w => lw w)
    (fun w => (vw w x : ℝ)) dl (fun v => ‖v.embedding x‖) hfin.toFinset Bδ
    (fun w => Formalism.PairingDivisionLocalBalance.lw_nonneg w) hsupp hsum
  have h4 := h3 hdl hden hB hfin.toFinset
  have hsub : (Function.support fun w : Pl K => lw w * |((vw w x + 0 : ℤ) : ℝ)|) ⊆
      (hfin.toFinset : Set (Pl K)) := by
    intro w hw
    by_contra hne
    apply hw
    have := hsupp w hne
    simp only [add_zero]
    rw [this, abs_zero, mul_zero]
  refine ⟨(hfin.toFinset.finite_toSet).subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsub]
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [hmean]
  simpa only [add_zero] using h4

theorem denIdeal_ne_zero {K : Type} [Field K] [NumberField K] (T : Finset (Pl K)) (a : Pl K → ℤ) :
    denIdeal T a ≠ 0 := by
  unfold denIdeal
  rw [Finset.prod_ne_zero_iff]
  intro w _
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)

theorem absNorm_pl_ne_zero {K : Type} [Field K] [NumberField K] (w : Pl K) :
    (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
  have h : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  exact_mod_cast h

theorem log_absNorm_denIdeal {K : Type} [Field K] [NumberField K] (T : Finset (Pl K))
    (a : Pl K → ℤ) :
    Real.log ((FractionalIdeal.absNorm (denIdeal T a) : ℚ) : ℝ) =
      -∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ) := by
  unfold denIdeal
  rw [map_prod, Rat.cast_prod, Real.log_prod]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Real.log_zpow]
    push_cast
    ring
  · intro w _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow]
    apply zpow_ne_zero
    have := absNorm_pl_ne_zero w
    exact_mod_cast this

theorem lw_nonneg' {K : Type} [Field K] [NumberField K] (w : Pl K) : 0 ≤ lw w := by
  unfold Formalism.DivisionValues.lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem grid_lemma_A : SlopeInequalityDenominators := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B T a hA hA0 hB hB0 hφ hincl
  have hI : denIdeal T a ≠ 0 := denIdeal_ne_zero T a
  obtain ⟨hfg, -, hmax, -⟩ :=
    Formalism.LFunctionChainParameters.LLcv.ideal_scaling_holds K W κ b' X' hX' (denIdeal T a) hI B hB hB0
  have hmap : A.map (φ.restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h
    apply hA0
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h1 : (φ.restrictScalars (𝓞 K)) x ∈ A.map (φ.restrictScalars (𝓞 K)) :=
      Submodule.mem_map_of_mem hx
    rw [h, Submodule.mem_bot] at h1
    apply hφ
    rw [map_zero]
    exact h1
  obtain ⟨-, h2⟩ := Formalism.HN.slope_inequality_mean K V ι W κ b X b' X' hX hX' φ A hA hmap
  have h3 := (h2 _ hfg hincl).2 hφ.injOn
  rw [hmax, log_absNorm_denIdeal] at h3
  have e : ∑ w ∈ T, lw w * (a w : ℝ) =
      (∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ)) / (finrank ℚ K : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold Formalism.DivisionValues.lw
    ring
  rw [e]
  generalize (∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ)) = sm at h3 ⊢
  have e2 : (2 * -sm) / (finrank ℚ K : ℝ) = -(2 * (sm / (finrank ℚ K : ℝ))) := by ring
  rw [e2] at h3
  linarith

def LargestSlopeFullLatticeFrames : Prop :=
  ∀ (K W κ : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (D : ℕ), 0 < D →
    ∀ (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (kap : InfinitePlace K → ℝ)
      (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (XE v).det) → (∀ v, 0 < kap v) → (∀ v, IsUnit (X' v).det) →
    ∀ (R : Submodule (𝓞 K) (Fin D → K)) (M : Submodule (𝓞 K) W) (Ψ : (Fin D → K) →ₗ[K] W)
      (T : Finset (Pl K)) (a : Pl K → ℤ) (r : Pl K → K) (dF : Pl K → ℝ) (EM hInf Gr BF : ℝ),
    Submodule.IsFullLattice K R → M.FG → M ≠ ⊥ → Function.Injective Ψ →
    R.map (Ψ.restrictScalars (𝓞 K)) ≤ Formalism.HermitianLatticesTheory.idealSmul (denIdeal T a : Submodule (𝓞 K) K) M →
    (∀ w ∈ T, (a w : ℝ) ≤ (vw w (r w) : ℝ) + dF w) →
    muMaxDef b' X' M ≤ EM →
    htMap (Pi.basisFun K (Fin D)) (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' Ψ ≤ hInf →
    ∑ w ∈ T, lw w * (vw w (r w) : ℝ) ≤ Gr → ∑ w ∈ T, lw w * dF w ≤ BF →
    muMaxDef (Pi.basisFun K (Fin D)) XE R ≤ -meanLog kap + (EM + hInf + 2 * (Gr + BF))


theorem grid_function_of_lemma_A (hA : SlopeInequalityDenominators) : LargestSlopeFullLatticeFrames := by
  intro K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a r dF EM hInf Gr BF
    hR hM hM0 hΨ hincl ha hEM hh hGr hBF
  obtain ⟨hfg, hne⟩ := Formalism.DivisionValues.lattice_fg_ne_bot hD R hR
  obtain ⟨hu, -, -, -, h5⟩ := Formalism.DivisionValues.kappa_normalise K D hD XE hXE kap hkap
  obtain ⟨-, e2, -⟩ := h5 R hR
  have h := hA K (Fin D → K) (Fin D) W κ (Pi.basisFun K (Fin D))
    (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' hu hX' Ψ R M T a hfg hne hM hM0 hΨ hincl
  have hs : ∑ w ∈ T, lw w * (a w : ℝ) ≤ Gr + BF := by
    calc ∑ w ∈ T, lw w * (a w : ℝ)
        ≤ ∑ w ∈ T, (lw w * (vw w (r w) : ℝ) + lw w * dF w) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have h1 := ha w hw
          have hl : 0 ≤ lw w := lw_nonneg' w
          nlinarith
      _ = ∑ w ∈ T, lw w * (vw w (r w) : ℝ) + ∑ w ∈ T, lw w * dF w := Finset.sum_add_distrib
      _ ≤ Gr + BF := add_le_add hGr hBF
  rw [e2]
  linarith

theorem grid_function_bound : LargestSlopeFullLatticeFrames := grid_function_of_lemma_A grid_lemma_A


end Formalism.AtG
