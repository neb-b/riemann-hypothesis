module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreSheetFormCompare
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0024

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartSheetCompare
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix Filter Topology

namespace SegreChartSheetComparison

theorem hessC_congr_germ {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    ReciprocityTheory.AnForm.hessC f y = ReciprocityTheory.AnForm.hessC g y := by
  unfold ReciprocityTheory.AnForm.hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eq_segre_chartLift {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i)
    {x : Fin m → ℂ} (hx : x ∈ zeroSet J) : x = fun a => segre (chartLift σ i x) (σ a) := by
  have hle : segreChartIdeal P σ i ≤ J := (mem_segreChartComponents.1 hJ).1.2
  funext a
  set q : MvPolynomial (Fin m) ℂ := MvPolynomial.X a -
    ∏ k, MvPolynomial.X (σ.symm (Function.update i k (σ a k))) with hq
  have heval : ∀ w : Fin m → ℂ, MvPolynomial.eval w q = w a - segre (chartLift σ i w) (σ a) := fun w => by
    simp [hq, segre, chartLift, map_prod]
  have hmem : q ∈ segreChartIdeal P σ i := by
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, -, hzi, rfl⟩
    show MvPolynomial.eval _ q = 0
    rw [heval, segre_chartLift σ i z hzi, sub_self]
  have h := hx q (hle hmem)
  rw [heval] at h
  exact sub_eq_zero.1 h

end SegreChartSheetComparison


open SegreChartSheetComparison in
theorem SegreChartSheetCompare.of_segreSheetFormCompare (hF : SegreSheetFormCompare.Statement) :
    SegreChartSheetCompare.Statement := by
  intro K _ _ ι _ P e m σ i L hL
  obtain ⟨C, hC⟩ := hF K ι e L hL
  refine ⟨|C|, fun J hJ A x s hx hs => ?_⟩
  obtain ⟨U, hU, hyU, hsd, hsx, hsU, -⟩ := hs
  set z : (Fin e → ℂ) → (Σ k, ι k) → ℂ := chartLift σ i ∘ s with hzdef
  have hz : DifferentiableOn ℂ z U :=
    differentiableOn_pi.2 fun p => (differentiableOn_pi.1 hsd) (σ.symm (Function.update i p.1 p.2))
  have hblk : ∀ k, ∃ j, z (A *ᵥ x) ⟨k, j⟩ ≠ 0 := by
    have h1 : s (A *ᵥ x) (σ.symm i) = 1 := by rw [hsx]; exact chart_coord_eq_one hJ hx
    exact chartLift_blockNonzero σ i h1
  have h1 := hC z U (A *ᵥ x) hU hyU hz hblk
  have hfs : (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s =ᶠ[𝓝 (A *ᵥ x)]
      (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    have he := eq_segre_chartLift hJ (hsU y' hy').2
    simp only [Function.comp_apply, hzdef]
    congr 1
    have hd : (HermNorm.std m).dualNorm (s y') = √(∑ a, ‖s y' a‖ ^ 2) := by
      simp [HermNorm.dualNorm, HermNorm.std]
    rw [hd]
    congr 1
    conv_lhs => rw [he]
    exact Equiv.sum_comp σ (fun i' => ‖segre (chartLift σ i (s y')) i'‖ ^ 2)
  have hden : ReciprocityTheory.AnForm.maDens
      (fun _ => (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s) (A *ᵥ x) =
      ReciprocityTheory.AnForm.maDens (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z)
        (A *ᵥ x) := by
    unfold ReciprocityTheory.AnForm.maDens
    dsimp only
    rw [hessC_congr_germ hfs]
  have hpot : (fun k => chartPot σ i L k ∘ s) = fun j => pot L j ∘ z := rfl
  rw [hpot, hden]
  calc _ ≤ _ := h1
    _ ≤ |C * ReciprocityTheory.AnForm.maDens
          (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) (A *ᵥ x)| := le_abs_self _
    _ = _ := abs_mul _ _

theorem SegreChartSheetCompare.proof : SegreChartSheetCompare.Statement :=
  SegreChartSheetCompare.of_segreSheetFormCompare SegreSheetFormCompare.proof

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSheetLift
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet bsmul eval_bsmul_of_isMultiHomog
  prod_update_eq)

namespace SheetLift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem bsmul_mem {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : bsmul c z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · obtain ⟨S, hS, hPS⟩ := hP
    have hle : P ≤ RingHom.ker ((eval (bsmul c z)).comp (map (Int.castRingHom ℂ))) := by
      rw [hPS, Ideal.span_le]
      intro g hg
      obtain ⟨a, ha⟩ := hS g hg
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, eval_bsmul_of_isMultiHomog ha c z,
        hz.2 g (by rw [hPS]; exact Ideal.subset_span hg), mul_zero]
    exact hle hf


omit [∀ k, Fintype (ι k)] in
theorem segre_bsmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (bsmul c z) = fun i => (∏ k, c k) * segre z i := by
  funext i
  simp only [segre, bsmul, Finset.prod_mul_distrib]

def lift [DecidableEq K] (i0 : (k : K) → ι k) (k0 : K) (w : ((k : K) → ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => (if p.1 = k0 then w i0 else 1) * (w (Function.update i0 p.1 p.2) / w i0)

theorem lift_segre [DecidableEq K] (i0 : (k : K) → ι k) (k0 : K) {z : (Σ k, ι k) → ℂ}
    (hz : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) = bsmul (fun k => (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩) z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hz) k (Finset.mem_univ k)
  funext ⟨k, j⟩
  have e1 : segre z (Function.update i0 k j) = z ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ :=
    prod_update_eq z i0 k j
  have e2 : segre z i0 = z ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ := by
    have := prod_update_eq z i0 k (i0 k)
    rwa [Function.update_eq_self] at this
  have hQ : ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' _ => h0 k'
  have hk := h0 k
  simp only [lift, bsmul]
  rw [e1, e2]
  field_simp

theorem lift_spec [DecidableEq K] {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (i0 : (k : K) → ι k)
    (k0 : K) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hne : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) ∈ mcPts P ∧ segre (lift i0 k0 (segre z)) = segre z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hne) k (Finset.mem_univ k)
  rw [lift_segre i0 k0 hne]
  refine ⟨bsmul_mem hP (fun k => div_ne_zero (by split_ifs <;> simp [hne]) (h0 k)) hz, ?_⟩
  have hprod : ∏ k, (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩ = 1 := by
    rw [Finset.prod_div_distrib, Finset.prod_ite_eq' Finset.univ k0, if_pos (Finset.mem_univ _)]
    exact div_self hne
  rw [segre_bsmul, hprod]
  funext i
  rw [one_mul]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem differentiableAt_lift [DecidableEq K] {e : ℕ} (i0 : (k : K) → ι k) (k0 : K)
    {h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} {y : Fin e → ℂ} (hd : DifferentiableAt ℂ h y)
    (hne : h y i0 ≠ 0) : DifferentiableAt ℂ (fun y' => lift i0 k0 (h y')) y := by
  have hc : ∀ i, DifferentiableAt ℂ (fun y' => h y' i) y := fun i => differentiableAt_pi.mp hd i
  refine differentiableAt_pi.mpr fun p => ?_
  simp only [lift, div_eq_mul_inv]
  refine DifferentiableAt.mul ?_ ((hc (Function.update i0 p.1 p.2)).mul ((hc i0).inv hne))
  by_cases hp : p.1 = k0
  · simp only [hp, if_true]
    exact hc i0
  · simp only [hp, if_false]
    exact differentiableAt_const _

theorem proof : SheetLift.Statement := by
  intro K _ ι _ P e Ψ y h hP hev
  classical
  obtain ⟨hd0, ⟨z0, hz0, hs0⟩, -⟩ := hev.self_of_nhds
  rcases isEmpty_or_nonempty K with hK | ⟨⟨k0⟩⟩
  · refine ⟨fun _ => z0, hs0, hev.mono fun y' ⟨_, ⟨z, hz, hs⟩, hΨ⟩ => ?_⟩
    have hzz : z0 = z := funext fun p => (IsEmpty.false p.1).elim
    refine ⟨differentiableAt_const _, hzz ▸ hz, ?_⟩
    show Ψ (segre z0) = _
    rw [hzz, hs]
    exact hΨ
  · choose i0 hi0 using hz0.1
    have hy : h y i0 ≠ 0 := by
      rw [← hs0]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hi0 k
    have hnear : ∀ᶠ y' in 𝓝 y, h y' i0 ≠ 0 :=
      (differentiableAt_pi.mp hd0 i0).continuousAt.eventually_ne hy
    refine ⟨fun y' => lift i0 k0 (h y'), ?_, (hev.and hnear).mono fun y' ⟨⟨hd, ⟨z, hz, hs⟩, hΨ⟩, hne⟩ => ?_⟩
    · show segre (lift i0 k0 (h y)) = h y
      rw [← hs0]
      exact (lift_spec hP i0 k0 hz0 (hs0 ▸ hy)).2
    · have hne' : segre z i0 ≠ 0 := hs ▸ hne
      obtain ⟨h1, h2⟩ := lift_spec hP i0 k0 hz hne'
      refine ⟨differentiableAt_lift i0 k0 hd hne, ?_, ?_⟩
      · show lift i0 k0 (h y') ∈ mcPts P
        rw [← hs]
        exact h1
      · show Ψ (segre (lift i0 k0 (h y'))) = _
        rw [← hs, h2, hs]
        exact hΨ

end SheetLift

end GroundTheory.Heights₂.Heights
end
end

