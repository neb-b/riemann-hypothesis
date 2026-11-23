module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bridge
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem brcc_discr_one_ne (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    discr (lamOf D cc 1) ≠ 0 :=
  discr_latI_ne_zero D.host.K D.host.d (discriminant_mod_four D) ⟨D.host.sqrtMinusD, br_sqrt_mem D⟩
    (br_sqrt_sq D) (br_finrank_K D) (brPhi D) cc hcc

theorem brcc_delta_ne (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := by
  intro h0
  have hcc' := hcc
  obtain ⟨hcc0, -⟩ := hcc'
  have h12 : δ ^ 12 = discr (lamOf D cc 1) := hδ
  apply brcc_discr_one_ne D cc hcc0
  rw [← h12, h0]
  norm_num

private lemma lamOf_eq_map_mulLeft (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    lamOf D cc δ = (lamOf D cc 1).map (AddMonoidHom.mulLeft δ) := by
  unfold lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, by simp⟩
  · rintro ⟨v, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, by simp⟩

private lemma eisG_map_mulLeft (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) (k : ℕ) :
    Formalism.MainNotions.TaylorLogMetric.eisG (Λ.map (AddMonoidHom.mulLeft δ)) k = (δ ^ (2 * k))⁻¹ * Formalism.MainNotions.TaylorLogMetric.eisG Λ k := by
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ.map (AddMonoidHom.mulLeft δ) ∧ w ≠ 0} :=
    (Equiv.mulLeft₀ δ hδ).subtypeEquiv (fun w => by
      show (w ∈ Λ ∧ w ≠ 0) ↔ (δ * w ∈ Λ.map (AddMonoidHom.mulLeft δ) ∧ δ * w ≠ 0)
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨AddSubgroup.mem_map.2 ⟨w, h1, rfl⟩, mul_ne_zero hδ h2⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨v, hv, hvw⟩ := AddSubgroup.mem_map.1 h1
        have hvw' : δ * v = δ * w := hvw
        have hv' : v = w := mul_left_cancel₀ hδ hvw'
        rw [hv'] at hv
        exact ⟨hv, right_ne_zero_of_mul h2⟩)
  unfold Formalism.MainNotions.TaylorLogMetric.eisG
  refine (e.tsum_eq (fun w => 1 / (w : ℂ) ^ (2 * k))).symm.trans ?_
  rw [← tsum_mul_left]
  congr 1
  funext w
  show 1 / (δ * (w : ℂ)) ^ (2 * k) = (δ ^ (2 * k))⁻¹ * (1 / (w : ℂ) ^ (2 * k))
  rw [mul_pow, one_div, one_div, mul_inv]

private lemma g2_map_mulLeft (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    Formalism.MainNotions.TaylorLogMetric.g2 (Λ.map (AddMonoidHom.mulLeft δ)) = (δ ^ 4)⁻¹ * Formalism.MainNotions.TaylorLogMetric.g2 Λ := by
  unfold Formalism.MainNotions.TaylorLogMetric.g2
  rw [eisG_map_mulLeft Λ δ hδ]
  ring

private lemma g3_map_mulLeft (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    Formalism.MainNotions.TaylorLogMetric.g3 (Λ.map (AddMonoidHom.mulLeft δ)) = (δ ^ 6)⁻¹ * Formalism.MainNotions.TaylorLogMetric.g3 Λ := by
  unfold Formalism.MainNotions.TaylorLogMetric.g3
  rw [eisG_map_mulLeft Λ δ hδ]
  ring

private lemma discr_map_mulLeft (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    Formalism.MainNotions.TaylorLogMetric.discr (Λ.map (AddMonoidHom.mulLeft δ)) = (δ ^ 12)⁻¹ * Formalism.MainNotions.TaylorLogMetric.discr Λ := by
  unfold Formalism.MainNotions.TaylorLogMetric.discr
  rw [g2_map_mulLeft Λ δ hδ, g3_map_mulLeft Λ δ hδ]
  ring

theorem br_discr_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : discr (lamOf D cc δ) = 1 := by
  have hne : δ ≠ 0 := brcc_delta_ne D cc hcc δ hδ
  have h12 : δ ^ 12 = Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc 1) := hδ
  show Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1
  rw [lamOf_eq_map_mulLeft D cc δ, discr_map_mulLeft _ δ hne, ← h12]
  exact inv_mul_cancel₀ (pow_ne_zero _ hne)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Period
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem br_ellT_eq (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (τ : D.what₂.Tau) :
    Formalism.MainNotions.TaylorLogMetric.ellT D M τ = lineR M (embT D) D.host.AA0 τ := rfl

theorem br_brN_eq (D : D7) : brN D = ((FractionalIdeal.absNorm (D.host.AA0 *
    ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : ℚ) : ℝ) := rfl

theorem br_exists_ellT (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M]
    (hemb : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau) :
    ∃ s : M, s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ := by
  rw [br_ellT_eq, lineR_eq D.host.K D.host.E (brPhi D) M D.what₂.Tau (embT D) (br_embT_injective D)
    (br_embT_res D) (br_card_tau D) hemb]
  have hJ : D.host.AA0 * ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    mul_ne_zero (leading_constant_ne_zero D) (coeIdeal_different_ne_zero _ _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hJ)
  refine ⟨liftM M (embT D τ a), ?_, Submodule.subset_span ⟨a, ha, rfl⟩⟩
  have hm := hemb τ a
  unfold liftM
  rw [dite_eq_left hm]
  intro h
  have : embT D τ a = 0 := congrArg Subtype.val h
  exact ha0 ((map_eq_zero (embT D τ)).mp this)

theorem br_meanLogOm_eq (D : D7) (Λ : AddSubgroup ℂ) (M : IntermediateField ℚ ℂ) [NumberField M]
    (hemb : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau)
    (hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ Λ)) :
    meanLogOm D Λ M τ =
      -(2 / (Module.finrank ℚ D.host.E : ℝ)) * Real.log (brN D) +
        (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ) / Real.pi)) /
          (Module.finrank ℚ M : ℝ) := by
  have hex := br_exists_ellT D M hemb τ
  unfold meanLogOm
  dsimp only
  set s : M := Classical.epsilon (fun s : M => s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ) with hsdef
  have hs : s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ := Classical.epsilon_spec hex
  rw [br_ellT_eq] at hs ⊢
  have hidx := index_lineR D.host.K D.host.E (brPhi D) M D.what₂.Tau (embT D) (br_embT_injective D)
    (br_embT_res D) (br_card_tau D) hemb D.host.AA0 (leading_constant_ne_zero D) τ s hs.1 hs.2
  rw [← br_brN_eq] at hidx
  set x : ℝ := ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (lineR M (embT D) D.host.AA0 τ).toAddSubgroup).index : ℕ) : ℝ) with hxdef
  set e : ℕ := Module.finrank ℚ D.host.E with he
  set m : ℕ := Module.finrank ℚ M with hm
  set ns : ℝ := |((Algebra.norm ℚ s : ℚ) : ℝ)| with hns
  have hns0 : ns ≠ 0 := by
    rw [hns, abs_ne_zero, Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).mpr hs.1
  have hrhs : ns ^ e ≠ 0 := pow_ne_zero _ hns0
  have hl : x ^ e * brN D ^ m ≠ 0 := hidx ▸ hrhs
  have hx0 : x ^ e ≠ 0 := left_ne_zero_of_mul hl
  have hN0 : brN D ^ m ≠ 0 := right_ne_zero_of_mul hl
  have hlog : (e : ℝ) * Real.log x + (m : ℝ) * Real.log (brN D) = (e : ℝ) * Real.log ns := by
    have := congrArg Real.log hidx
    rw [Real.log_mul hx0 hN0, Real.log_pow, Real.log_pow, Real.log_pow] at this
    exact this
  have he0 : (e : ℝ) ≠ 0 := by
    rw [he]; exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ D.host.E).ne'
  have hm0 : (m : ℝ) ≠ 0 := by
    rw [hm]; exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ M).ne'
  have hterm : ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.logMet M Λ ρ s =
      Real.log Real.pi + Real.log (‖ρ s‖ ^ 2) - Real.log (area (lamConj M ρ Λ)) := by
    intro ρ
    unfold Formalism.MainNotions.TaylorLogMetric.logMet
    rw [br_area_eq]
    have hρ : ‖ρ s‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ((map_ne_zero ρ).mpr hs.1))
    rw [Real.log_div (mul_ne_zero Real.pi_ne_zero hρ) (hpos ρ).ne', Real.log_mul Real.pi_ne_zero hρ]
  have hsum : ∑ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.logMet M Λ ρ s =
      (m : ℝ) * Real.log Real.pi + 2 * Real.log ns -
        ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ)) := by
    rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      br_sum_log_norm_sq M s hs.1, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul]
  have hsum2 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ) / Real.pi) =
      ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ)) - (m : ℝ) * Real.log Real.pi := by
    rw [Finset.sum_congr rfl (fun ρ _ => Real.log_div (hpos ρ).ne' Real.pi_ne_zero),
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul]
  rw [hsum, hsum2]
  field_simp
  linear_combination 2 * hlog

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end

