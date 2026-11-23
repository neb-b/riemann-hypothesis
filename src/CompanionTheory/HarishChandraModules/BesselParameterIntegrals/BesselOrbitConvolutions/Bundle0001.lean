module

public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.AtFormAdmOneOfSteps
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc

@[expose] public section

-- bundled from CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.DDFormC
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section
set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData

namespace GC

theorem discrete_form_one_side : CompanionTheory.D.Upq.BesselFunctionalConstruction.C.DDFormOneOfSteps := by
  intro hPsi hSch _ _ _ _ hBC hNI hBB hSh hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => fdeg_eq hd hSd hx
  have hmu := muSof_facts hW hN
  have hae := ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, -, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), hid x (hsm x hx) v hv⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x (hsm x hx) v (Or.inl hv) (l v)).1
    rw [hid v (hsm v hv) v hv] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hid _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x (hsm x hx) _ hg) v hv]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    refine ⟨fun _ => 0, bessel_zero, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    rw [hnz x hx v hv]
    ext ξ; simp

end GC

end Formalism.FourierDecayAlt.P.DDSmoothness

end
end

-- bundled from CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.KFinFormOf
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness

theorem bessel_add {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ}
    {σ : Mx k r → (H →L[ℂ] H)} {π : Mx k r → (Wp →L[ℂ] Wp)} {B B' : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B)
    (hB' : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B') :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun x => B x + B' x) := by
  obtain ⟨a1, a2, a3, C, Ws, hWs, hC⟩ := hB
  obtain ⟨b1, b2, b3, C', Ws', hWs', hC'⟩ := hB'
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun g hg m hm v hv => ?_, |C| + |C'|, Ws ++ Ws',
    fun W hW => (List.mem_append.1 hW).elim (hWs W) (hWs' W), fun v hv => ?_⟩
  · simp only [a1 v hv w hw, b1 v hv w hw]; abel
  · simp only [a2 c v hv, b2 c v hv, smul_add]
  · simp only [a3 g hg m hm v hv, b3 g hg m hm v hv, map_add (f := _), smul_add]
  · have hnn : ∀ L : List (List (Mx k r)),
        0 ≤ (L.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W v‖).sum := fun L =>
      List.sum_nonneg fun t ht => by
        obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht
        exact norm_nonneg _
    rw [List.map_append, List.sum_append]
    have h1 := (hC v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hnn Ws))
    have h2 := (hC' v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (hnn Ws'))
    have h3 := mul_nonneg (abs_nonneg C) (hnn Ws')
    have h4 := mul_nonneg (abs_nonneg C') (hnn Ws)
    refine (norm_add_le _ _).trans ?_
    nlinarith

theorem kFinForm_of (hBC : BeConv) (hBB : BeBessel) : KFinForm := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hl _ hid v hv x hx
  have hK := hIn.2.2.1
  have hvs := hK k r ε lam H σ hS.1 hS.2.1 v hv
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  have hB := bessel_add
    (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inr hv) ξ)
    (bessel_smul hl (-⟪l v, ξ⟫_ℂ))
  have h0 := bessel_ne_zero_of_cyclic_orbit (Sm.smoothCyc_of_kFinSmooth hK) hK k r ε lam H σ w0 Wp z c π hS.1
    hS.2.1 hS.2.2.2.2.1 _ hB (fun y hy => by
      have hadj := (hBC4 y hy v (Or.inr hv)).2
      refine ext_inner_left ℂ fun η => ?_
      have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN y v) ξ η
      rw [hadj, hid v hvs y hy] at e
      simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left,
        inner_conj_symm] at e
      rw [inner_add_right, ← e, inner_smul_right, inner_zero_right]
      ring) x hx
  rw [neg_smul, add_neg_eq_zero] at h0
  rw [h0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

end CompanionTheory.D.Upq.BesselFunctionalConstruction

end
end

