module

public import Mathlib
public import GroundTheory.AutomorphicForms.RealIwasawaSubgroups
public import GroundTheory.AutomorphicForms.WhittakerDistribution
public import GroundTheory.AutomorphicForms.WhittakerCriterion
public import GroundTheory.AutomorphicForms.MeasuresGL

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.ReductionLocalVolumeTorus
section
open MeasureTheory Set Finset Real

namespace GroundTheory.Automorphic

namespace Reduction

section Chain

variable {m : ℕ} {x : Fin (m + 1) → ℝ} {L : ℝ}

theorem chain_sub_ge (hx : ∀ l : Fin m, L ≤ x l.castSucc - x l.succ) :
    ∀ k : ℕ, ∀ i : Fin (m + 1), ∀ hk : (i : ℕ) + k < m + 1,
      (k : ℝ) * min L 0 ≤ x i - x ⟨i + k, hk⟩
  | 0 => fun i hk => by simp
  | k + 1 => fun i hk => by
      have h1 := chain_sub_ge hx k i (by omega)
      have hl : (i : ℕ) + k < m := by omega
      have h2 := hx ⟨i + k, hl⟩
      have e1 : (⟨i + k, hl⟩ : Fin m).castSucc = ⟨i + k, by omega⟩ := rfl
      have e2 : (⟨i + k, hl⟩ : Fin m).succ = ⟨i + (k + 1), hk⟩ := by ext; simp; omega
      rw [e1, e2] at h2
      push_cast
      nlinarith [min_le_left L 0]

theorem pair_sub_ge (hx : ∀ l : Fin m, L ≤ x l.castSucc - x l.succ) {i j : Fin (m + 1)}
    (hij : i < j) : ((m : ℝ) + 1) * min L 0 ≤ x i - x j := by
  have hk : (i : ℕ) + ((j : ℕ) - i) < m + 1 := by have := j.isLt; omega
  have h := chain_sub_ge hx ((j : ℕ) - i) i hk
  have hj : (⟨i + ((j : ℕ) - i), hk⟩ : Fin (m + 1)) = j := by ext; simp; omega
  rw [hj] at h
  refine le_trans ?_ h
  have hle : (((j : ℕ) - i : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
    have := j.isLt
    have : (j : ℕ) - i ≤ m + 1 := by omega
    exact_mod_cast this
  nlinarith [min_le_right L 0]

theorem sub_add_le_sum_pairs (hx : ∀ l : Fin m, L ≤ x l.castSucc - x l.succ) (l : Fin m) :
    x l.castSucc - x l.succ +
        (Fintype.card (StrictUpperIndex (Fin (m + 1))) : ℝ) * (((m : ℝ) + 1) * min L 0) ≤
      ∑ p : StrictUpperIndex (Fin (m + 1)), (x p.1.1 - x p.1.2) := by
  classical
  set c : ℝ := ((m : ℝ) + 1) * min L 0 with hc
  have hc0 : c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (min_le_right _ _)
  set p₀ : StrictUpperIndex (Fin (m + 1)) := ⟨(l.castSucc, l.succ), Fin.castSucc_lt_succ⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p₀)]
  refine add_le_add le_rfl ?_
  calc (Fintype.card (StrictUpperIndex (Fin (m + 1))) : ℝ) * c
      ≤ ((Finset.univ.erase p₀).card : ℝ) * c := by
        refine mul_le_mul_of_nonpos_right ?_ hc0
        exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    _ = ∑ _p ∈ Finset.univ.erase p₀, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ Finset.univ.erase p₀, (x p.1.1 - x p.1.2) :=
        Finset.sum_le_sum fun p _ => pair_sub_ge hx p.2

end Chain

section Coordinates

variable (m : ℕ)

def chamberCoords : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun x i := Fin.lastCases (∑ j, x j) (fun l => x l.castSucc - x l.succ) i
  map_add' x y := by
    ext i
    induction i using Fin.lastCases with
    | last => simp [Finset.sum_add_distrib]
    | cast l => simp; ring
  map_smul' c x := by
    ext i
    induction i using Fin.lastCases with
    | last => simp [Finset.mul_sum]
    | cast l => simp; ring

@[simp] theorem chamberCoords_last (x : Fin (m + 1) → ℝ) :
    chamberCoords m x (Fin.last m) = ∑ j, x j := by simp [chamberCoords]

@[simp] theorem chamberCoords_castSucc (x : Fin (m + 1) → ℝ) (l : Fin m) :
    chamberCoords m x l.castSucc = x l.castSucc - x l.succ := by simp [chamberCoords]

theorem chamberCoords_injective : Function.Injective (chamberCoords m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hd : ∀ l : Fin m, x l.castSucc = x l.succ := fun l => by
    have := congrFun hx l.castSucc
    rw [chamberCoords_castSucc] at this
    simpa [sub_eq_zero] using this
  have hconst : ∀ k : ℕ, ∀ hk : k < m + 1, x ⟨k, hk⟩ = x 0 := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have h := hd ⟨k, by omega⟩
      have e1 : (⟨k, by omega⟩ : Fin m).castSucc = ⟨k, by omega⟩ := rfl
      have e2 : (⟨k, by omega⟩ : Fin m).succ = ⟨k + 1, hk⟩ := rfl
      rw [e1, e2] at h
      rw [← h, ih]
  have hall : ∀ j, x j = x 0 := fun j => hconst j j.isLt
  have hs := congrFun hx (Fin.last m)
  rw [chamberCoords_last] at hs
  simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Pi.zero_apply] at hs
  have h0 : x 0 = 0 := by
    rcases mul_eq_zero.1 hs with h | h
    · exact absurd h (by positivity)
    · exact h
  funext j
  rw [hall, h0, Pi.zero_apply]

theorem det_chamberCoords_ne_zero : LinearMap.det (chamberCoords m) ≠ 0 :=
  (LinearMap.isUnit_det _ ((LinearMap.isUnit_iff_ker_eq_bot _).2
    (LinearMap.ker_eq_bot.2 (chamberCoords_injective m)))).ne_zero

end Coordinates

theorem lintegral_chamber_lt_top (m : ℕ) {e : ℝ} (he : 1 ≤ e) (L α β : ℝ) :
    ∫⁻ x : Fin (m + 1) → ℝ,
      {x : Fin (m + 1) → ℝ | (∀ l : Fin m, L ≤ x l.castSucc - x l.succ) ∧
        α ≤ ∑ i, x i ∧ ∑ i, x i ≤ β}.indicator
        (fun x => ENNReal.ofReal (exp (-(e * ∑ p : StrictUpperIndex (Fin (m + 1)),
          (x p.1.1 - x p.1.2))))) x < ⊤ := by
  classical
  set K : ℝ := (Fintype.card (StrictUpperIndex (Fin (m + 1))) : ℝ) * (((m : ℝ) + 1) * min L 0)
    with hK
  set mm : ℝ := max (m : ℝ) 1 with hmm
  have hmm1 : 1 ≤ mm := le_max_right _ _

  set g : Fin (m + 1) → ℝ → ℝ := fun i => Fin.lastCases ((Icc α β).indicator (fun _ => (1 : ℝ)))
    (fun _ => (Ici L).indicator (fun y => exp (-(e / mm) * y))) i with hg
  have hgint : ∀ i, Integrable (g i) volume := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [hg, Fin.lastCases_last]
      exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    | cast l =>
      simp only [hg, Fin.lastCases_castSucc]
      refine IntegrableOn.integrable_indicator ?_ measurableSet_Ici
      have hpos : 0 < e / mm := div_pos (by linarith) (by linarith)
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact exp_neg_integrableOn_Ioi L hpos
  have hprod : Integrable (fun y : Fin (m + 1) → ℝ => ∏ i, g i (y i)) volume :=
    Integrable.fintype_prod hgint
  have hfin := hprod.lintegral_lt_top

  set C : ℝ := exp (-(e * K)) with hC
  have hbound : ∀ x : Fin (m + 1) → ℝ,
      {x : Fin (m + 1) → ℝ | (∀ l : Fin m, L ≤ x l.castSucc - x l.succ) ∧
        α ≤ ∑ i, x i ∧ ∑ i, x i ≤ β}.indicator
        (fun x => ENNReal.ofReal (exp (-(e * ∑ p : StrictUpperIndex (Fin (m + 1)),
          (x p.1.1 - x p.1.2))))) x ≤
      ENNReal.ofReal C * ENNReal.ofReal (∏ i, g i (chamberCoords m x i)) := by
    intro x
    by_cases hx : x ∈ {x : Fin (m + 1) → ℝ | (∀ l : Fin m, L ≤ x l.castSucc - x l.succ) ∧
        α ≤ ∑ i, x i ∧ ∑ i, x i ≤ β}
    · rw [indicator_of_mem hx, ← ENNReal.ofReal_mul (exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      obtain ⟨hd, hα, hβ⟩ := hx
      have hgx : ∏ i, g i (chamberCoords m x i) =
          exp (-(e / mm) * ∑ l : Fin m, (x l.castSucc - x l.succ)) := by
        rw [Fin.prod_univ_castSucc]
        simp only [hg, Fin.lastCases_castSucc, Fin.lastCases_last, chamberCoords_castSucc,
          chamberCoords_last]
        rw [indicator_of_mem (show ∑ j, x j ∈ Icc α β from ⟨hα, hβ⟩), mul_one,
          Finset.mul_sum, Real.exp_sum]
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [indicator_of_mem (show x l.castSucc - x l.succ ∈ Ici L from hd l)]
      rw [hgx, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_

      set S : ℝ := ∑ p : StrictUpperIndex (Fin (m + 1)), (x p.1.1 - x p.1.2) with hS
      have hK0 : K ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (min_le_right _ _))
      have hSK : K ≤ S := by
        rw [hS, hK]
        calc (Fintype.card (StrictUpperIndex (Fin (m + 1))) : ℝ) * (((m : ℝ) + 1) * min L 0)
            = ∑ _p : StrictUpperIndex (Fin (m + 1)), (((m : ℝ) + 1) * min L 0) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum fun p _ => pair_sub_ge hd p.2
      have havg : (∑ l : Fin m, (x l.castSucc - x l.succ)) ≤ mm * (S - K) := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · subst hm0
          simp only [Finset.univ_eq_empty, Finset.sum_empty]
          exact mul_nonneg (by linarith) (by linarith)
        · calc (∑ l : Fin m, (x l.castSucc - x l.succ)) ≤ ∑ _l : Fin m, (S - K) :=
                Finset.sum_le_sum fun l _ => by linarith [sub_add_le_sum_pairs hd l]
            _ = (m : ℝ) * (S - K) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
            _ ≤ mm * (S - K) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      have hmmpos : 0 < mm := by linarith
      have h1 : (e / mm) * (∑ l : Fin m, (x l.castSucc - x l.succ)) ≤ e * (S - K) := by
        calc (e / mm) * (∑ l : Fin m, (x l.castSucc - x l.succ)) ≤ (e / mm) * (mm * (S - K)) :=
              mul_le_mul_of_nonneg_left havg (div_nonneg (by linarith) hmmpos.le)
          _ = e * (S - K) := by field_simp
      nlinarith
    · rw [indicator_of_notMem hx]
      exact zero_le

  have hT := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin (m + 1) → ℝ)))
    (det_chamberCoords_ne_zero m)
  have hgm : ∀ i, Measurable (g i) := by
    intro i
    induction i using Fin.lastCases with
    | last => simp only [hg, Fin.lastCases_last]; exact measurable_const.indicator measurableSet_Icc
    | cast l =>
      simp only [hg, Fin.lastCases_castSucc]
      exact (measurable_exp.comp (measurable_const.mul measurable_id)).indicator measurableSet_Ici
  have hmeasG : Measurable fun y : Fin (m + 1) → ℝ => ENNReal.ofReal (∏ i, g i (y i)) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
      (hgm i).comp (measurable_pi_apply (X := fun _ : Fin (m + 1) => ℝ) i))
  calc _ ≤ ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (∏ i, g i (chamberCoords m x i)) :=
        lintegral_mono hbound
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (∏ i, g i (chamberCoords m x i)) :=
        lintegral_const_mul _ (hmeasG.comp (LinearMap.continuous_of_finiteDimensional _).measurable)
    _ = ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (∏ i, g i (y i))
          ∂(Measure.map (chamberCoords m) volume) := by
        rw [lintegral_map hmeasG (LinearMap.continuous_of_finiteDimensional _).measurable]
    _ < ⊤ := by
        rw [hT, lintegral_smul_measure]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

end Reduction

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.WhittakerLocal
section
namespace GroundTheory.Automorphic

namespace Whittaker

open MeasureTheory Measure ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem biEquivariantSigmaInvariant_GL (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) :
    BiEquivariantSigmaInvariant (Iwasawa.unipotent F n)
      (fun u => psiN ψ₀ (u : GL (Fin n) F)) sigmaHomeo := by
  intro D hD f
  have key := distribution_sigma_invariant ψ₀ hψ hψ₁ D (fun f u₁ u₂ hu₁ hu₂ => by
    have e : (⟨fun x => (f : GL (Fin n) F → ℂ) (u₁⁻¹ * x * u₂), twoSided_mem f.2 u₁ u₂⟩ :
        locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = biTranslL u₁ u₂ f :=
      Subtype.ext (coe_biTranslL u₁ u₂ f).symm
    rw [e]
    exact hD f ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩) f
  have e : compHomeoL sigmaHomeo f =
      (⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ :
        locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) := Subtype.ext rfl
  rw [e]
  exact key

section Measure

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

def thetaEquiv : GL (Fin n) F ≃* GL (Fin n) F where
  toFun := theta
  invFun := theta
  left_inv := theta_theta
  right_inv := theta_theta
  map_mul' := theta_mul

theorem map_sigma_eq (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.map sigma = μ := by
  have hθc : Continuous (theta : GL (Fin n) F → GL (Fin n) F) := continuous_theta
  have hθm : Measurable (theta : GL (Fin n) F → GL (Fin n) F) := hθc.measurable
  have : (μ.map theta).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ (thetaEquiv (F := F) (n := n)) hθc hθc
  set c := haarScalarFactor (μ.map theta) μ
  have e : μ.map theta = c • μ := isMulLeftInvariant_eq_smul (μ.map theta) μ
  have e2 : μ = (c * c) • μ := by
    have h1 : (μ.map theta).map theta = μ := by
      rw [Measure.map_map hθm hθm]
      have : (theta ∘ theta : GL (Fin n) F → GL (Fin n) F) = id := funext theta_theta
      rw [this, Measure.map_id]
    have h2 : (μ.map theta).map theta = (c * c) • μ := by
      rw [e, Measure.map_smul, e, smul_smul]
      exact hθm.aemeasurable
    exact h1.symm.trans h2
  set K := GLnLocal.integralGL F n
  have hK0 : μ K ≠ 0 := (GLnLocal.isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (GLnLocal.isCompact_integralGL F n).measure_lt_top.ne
  have hc : c = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e2
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have h' := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    have hcc : (c * c : NNReal) = 1 := by exact_mod_cast h'
    have hr : ((c : ℝ) * (c : ℝ)) = 1 := by exact_mod_cast hcc
    have hc0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  have eθ : μ.map theta = μ := by rw [e, hc, one_smul]
  have hσ : (sigma : GL (Fin n) F → GL (Fin n) F) = (fun g => g⁻¹) ∘ theta := by
    funext g
    simp [theta]
  rw [hσ, ← Measure.map_map continuous_inv.measurable hθm, eθ]
  exact Measures.inv_eq_self_GL F n μ

end Measure

theorem rank_whittaker_le_one_of_contragredient (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀)
    (hψ₁ : ψ₀ ≠ 1) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible]
    (hne : equivariantFunctionals (contragredient π)
      (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) ≤ 1 := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  have : (haar : Measure (GL (Fin n) F)).IsInvInvariant := ⟨Measures.inv_eq_self_GL F n _⟩
  exact rank_le_one_of_ne_bot (haar : Measure (GL (Fin n) F)) (σ := sigmaHomeo)
    (fun x y => sigma_mul x y) (map_sigma_eq _) (biEquivariantSigmaInvariant_GL ψ₀ hψ hψ₁) hπ hne

end Whittaker

end GroundTheory.Automorphic
end

