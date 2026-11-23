module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0181
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0157
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0162
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjS
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace CAS

variable {k r : ℕ}

def TF (a : B.Mat k r → ℂ) : Prop := ContDiff ℝ ∞ a ∧ HasCompactSupport a

theorem tsupport_rdV {ψ : B.Mat k r → ℂ} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    tsupport (RdV X ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro g hg
  by_contra hgs
  apply hg
  have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
  have hcont : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    continuous_const.mul (Formalism.REAL.continuous_exp_real_smul X)
  have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' (tsupport ψ)ᶜ ∈ 𝓝 (0 : ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    apply hopen.mem_nhds
    simpa using hgs
  have hev : (fun t : ℝ => ψ (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  show deriv _ 0 = 0
  rw [hev.deriv_eq]
  simp

theorem tf_rdV {a : B.Mat k r → ℂ} (ha : TF a) (X : B.Mat k r) : TF (RdV X a) := by
  exact ⟨rdV_contDiff ha.1 X, ha.2.mono' ((subset_tsupport _).trans (tsupport_rdV ha.1 X))⟩

theorem tf_rw {a : B.Mat k r → ℂ} (ha : TF a) : ∀ w : List (B.Mat k r), TF (B.Rw w a)
  | [] => ha
  | X :: w => tf_rdV (tf_rw ha w) X

theorem level_zero_set_eq_group : Q.Glev k r 0 = B.GV k r := by
  ext g
  simp only [Q.Glev, Set.mem_setOf_eq, B.GV, Fin.val_zero, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
    and_true]

theorem haar0 {μ : Measure (Mt k r)} (h : B.IsHaarOn (B.GV k r) μ) : B.IsHaarOn (Q.Glev k r 0) μ := by
  rw [level_zero_set_eq_group]
  exact h

theorem lie0 {X : B.Mat k r} (hX : B.inLie k r X) : Q.inLieLev k r 0 X := by
  exact ⟨hX, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem smooth0 {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ∞ a) : Q.SmoothLev k r 0 Set.univ a := by
  exact fun g₀ _ => ⟨Set.univ, a, isOpen_univ, trivial, ha.contDiffOn, fun _ _ _ => rfl⟩

theorem cpt0 {a : B.Mat k r → ℂ} (ha : HasCompactSupport a) : Q.CptOn k r 0 a := by
  exact ⟨tsupport a, ha, fun g _ hg => image_eq_zero_of_notMem_tsupport hg⟩

theorem word_adj_scalar {μ : Measure (Mt k r)} (h : B.IsHaarOn (B.GV k r) μ) :
    ∀ (w : List (B.Mat k r)), (∀ X ∈ w, B.inLie k r X) → ∀ {a b : B.Mat k r → ℂ}, TF a → TF b →
      (∫ x : Mt k r, B.Rw w a (Matrix.of x) * star (b (Matrix.of x)) ∂μ) =
        (-1 : ℂ) ^ w.length * ∫ x : Mt k r, a (Matrix.of x) * star (B.Rw w.reverse b (Matrix.of x)) ∂μ
  | [], _, a, b, _, _ => by simp [B.Rw]
  | X :: w, hw, a, b, ha, hb => by
    have hX : B.inLie k r X := hw X (by simp)
    have hw' : ∀ Z ∈ w, B.inLie k r Z := fun Z hZ => hw Z (by simp [hZ])
    have e1 : B.Rw (X :: w) a = RdV X (B.Rw w a) := rfl
    have e2 : B.Rw (X :: w).reverse b = B.Rw w.reverse (RdV X b) := by
      simp only [B.Rw, List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have hra := tf_rw ha w
    have sk := Formalism.FourierDecayAlt.P.right_differential_skew k r 0 μ (haar0 h) X (B.Rw w a) b (lie0 hX) (smooth0 hra.1)
      (smooth0 hb.1) (cpt0 hra.2) (cpt0 hb.2)
    rw [e1, sk, word_adj_scalar h w hw' ha (tf_rdV hb X), e2, List.length_cons, pow_succ]
    ring

end CAS

open CAS in
theorem capacity_adjoint_scalar : CapAdjScalar := by
  intro k r Y μ h a b ha hac hb hbc
  have ta : TF a := ⟨ha, hac⟩
  have tb : TF b := ⟨hb, hbc⟩
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  obtain ⟨hLw, hCV⟩ := Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)
  have hLie : ∀ cw ∈ capLw k r Y, ∀ X ∈ cw.2, B.inLie k r X := fun cw hc X hX => ((hLw cw hc).1 X hX).1

  have hintA : ∀ v : B.Mat k r → ℂ, Continuous v →
      Integrable (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) μ := by
    intro v hv
    have hc : Continuous (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) :=
      ha.continuous.mul (continuous_star.comp hv)
    have hs : HasCompactSupport (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) :=
      hac.mono fun x hx h0 => hx (by show a x * _ = 0; rw [h0, zero_mul])
    exact hc.integrable_of_hasCompactSupport hs
  have hintB : ∀ v : B.Mat k r → ℂ, Continuous v →
      Integrable (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) μ := by
    intro v hv
    have hc : Continuous (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) :=
      hv.mul (continuous_star.comp hb.continuous)
    have hs : HasCompactSupport (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) :=
      hbc.mono fun x hx h0 => hx (by show _ * star (b x) = 0; rw [h0, star_zero, mul_zero])
    exact hc.integrable_of_hasCompactSupport hs

  have hH := Formalism.FourierDecayAlt.P.hermitian_haar_invariance k r 0 0 0 μ (haar0 h) (fun _ _ => rfl) (fun _ _ => rfl) a b
    (smooth0 ha) (smooth0 hb) (cpt0 hac) (cpt0 hbc) Y 0 0
  have eT : ∀ (Y' : ℂ), Q.tL k r (E := ℂ) 0 0 0 Y' 0 0 = Q.CV k r Y' := fun _ => rfl
  have eS : star Y = conj Y := rfl
  rw [eT, eT, eS] at hH
  rw [← hH]

  have e2 : (∫ x : Mt k r, Q.CV k r Y a (Matrix.of x) * star (b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, ((capLw k r Y).map fun cw =>
        cw.1 * (B.Rw cw.2 a (Matrix.of x) * star (b (Matrix.of x)))).sum ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae h] with x hx
    have := hCV ℂ (B.GV k r) a (ckOn_of_contDiff ha _ _) (Matrix.of x) hx hx
    rw [this, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun cw _ => ?_)
    rw [smul_eq_mul, mul_assoc]

  have e1 : (∫ x : Mt k r, a (Matrix.of x) * star (wsAdj (capLw k r Y) b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, ((capLw k r Y).map fun cw =>
        cw.1 * ((-1 : ℂ) ^ cw.2.length * (a (Matrix.of x) * star (B.Rw cw.2.reverse b (Matrix.of x))))).sum ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [wsAdj, Complex.star_def, map_list_sum, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun cw _ => ?_)
    simp only [Function.comp_apply, map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
    ring
  rw [e1, e2,
    (Formalism.FourierDecayAlt.P.B5.integral_listSum μ _ _ fun cw _ =>
      ((hintA _ (tf_rw tb _).1.continuous).const_mul _).const_mul _).2,
    (Formalism.FourierDecayAlt.P.B5.integral_listSum μ _ _ fun cw _ => (hintB _ (tf_rw ta _).1.continuous).const_mul _).2]
  refine congrArg List.sum (List.map_congr_left fun cw hcw => ?_)
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    word_adj_scalar h cw.2 (hLie cw hcw) ta tb]

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjFund
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

theorem fundG_hs_sub_left {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A A' C : Wq →L[ℂ] Wp) :
    B.hsInner (A - A') C = B.hsInner A C - B.hsInner A' C := by
  unfold B.hsInner
  simp only [← Formalism.FourierDecayAlt.P.B5.hsL_apply, map_sub, inner_sub_right]

theorem fundamental_domain_group : FundG := by
  intro k r Wp Wq _ _ _ _ _ _ D A A' hA hA' hI g₀ hg₀
  have hμ := D.haarG
  have : IsFiniteMeasureOnCompacts D.μG := ⟨hμ.finite_compact⟩
  have hg₀G : g₀ ∈ B.GV k r := hg₀.1
  have hG0 : 0 < Gf k r D.z D.z' g₀ := hg₀.2
  by_contra hne
  set C : Wq →L[ℂ] Wp := A g₀ - A' g₀ with hC
  have hC0 : C ≠ 0 := sub_ne_zero.2 hne
  have hvC : B.hsVec C ≠ 0 := fun h0 => hC0 (Formalism.FourierDecayAlt.P.JFxI.hsVec_injective (h0.trans (by
      rw [← Formalism.FourierDecayAlt.P.B5.hsL_apply, map_zero])))
  set u : B.Mat k r → ℝ := fun x => (B.hsInner (A x) C - B.hsInner (A' x) C).re with hu
  have hu0 : u g₀ = ‖B.hsVec C‖ ^ 2 := by
    show (B.hsInner (A g₀) C - B.hsInner (A' g₀) C).re = _
    rw [← fundG_hs_sub_left]
    unfold B.hsInner
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpos0 : 0 < u g₀ := by rw [hu0]; positivity
  have huc : ContinuousOn u (B.GV k r) := by
    have hhs := Formalism.FourierDecayAlt.P.B5.hs_continuous (Wp := Wp) (Wq := Wq)
    have h1 : ContinuousOn (fun x => B.hsInner (A x) C) (B.GV k r) :=
      hhs.comp_continuousOn (f := fun x => (A x, C)) (hA.prodMk continuousOn_const)
    have h2 : ContinuousOn (fun x => B.hsInner (A' x) C) (B.GV k r) :=
      hhs.comp_continuousOn (f := fun x => (A' x, C)) (hA'.prodMk continuousOn_const)
    exact Complex.continuous_re.comp_continuousOn (h1.sub h2)

  have hgf := Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r D.z D.z'
  obtain ⟨ε1, hε1, h1⟩ := Metric.continuousOn_iff.1 huc g₀ hg₀G (u g₀ / 2) (by positivity)
  obtain ⟨ε2, hε2, h2⟩ := Metric.continuous_iff.1 hgf g₀ (Gf k r D.z D.z' g₀ / 2) (by positivity)
  set ε := min ε1 ε2 with hε
  have hεpos : 0 < ε := lt_min hε1 hε2
  have hgood : ∀ x ∈ B.GV k r, dist x g₀ < ε → 0 < u x ∧ x ∈ B.GPos D := by
    intro x hx hd
    have hd1 := h1 x hx (lt_of_lt_of_le hd (min_le_left _ _))
    have hd2 := h2 x (lt_of_lt_of_le hd (min_le_right _ _))
    rw [Real.dist_eq] at hd1 hd2
    refine ⟨by linarith [(abs_lt.1 hd1).1], hx, ?_⟩
    show 0 < Gf k r D.z D.z' x
    linarith [(abs_lt.1 hd2).1]

  obtain ⟨β, hβin, hβout⟩ : ∃ β : ContDiffBump g₀, β.rIn = ε / 4 ∧ β.rOut = ε / 2 :=
    ⟨⟨ε / 4, ε / 2, by positivity, by linarith⟩, rfl, rfl⟩
  have hβd : ∀ x : B.Mat k r, β x ≠ 0 → dist x g₀ < ε / 2 := by
    intro x hx
    by_contra hc
    push Not at hc
    exact hx (β.zero_of_le_dist (by rw [hβout]; exact hc))
  set φ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • C with hφ
  have hφs : ContDiff ℝ ∞ φ := (Complex.ofRealCLM.contDiff.comp β.contDiff).smul contDiff_const
  have hφc : HasCompactSupport φ := (β.hasCompactSupport.comp_left Complex.ofReal_zero).smul_right
  have hφsupp : B.SuppIn (B.GPos D) φ := by
    intro x hx
    have hsub : {g | g ∈ B.GV k r ∧ φ g ≠ 0} ⊆ Metric.closedBall g₀ (ε / 2) ∩ B.GV k r := by
      rintro g ⟨hgG, hg⟩
      refine ⟨?_, hgG⟩
      have hβ0 : β g ≠ 0 := fun h0 => hg (by simp [hφ, h0])
      exact Metric.mem_closedBall.2 (le_of_lt (hβd g hβ0))
    have hGc : IsClosed (B.GV k r) := Formalism.FourierDecayAlt.P.B7.isClosed_GV
    have hcl : IsClosed (Metric.closedBall g₀ (ε / 2) ∩ B.GV k r) := Metric.isClosed_closedBall.inter hGc
    have hx' := closure_minimal hsub hcl hx
    exact (hgood x hx'.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hx'.1) (by linarith))).2
  have hEq := hI φ (Formalism.FourierDecayAlt.P.CutMP.ER.ckOn_of_contDiff hφs ⊤ _) hφc hφsupp

  have hGc' : IsClosed {x : Mt k r | Matrix.of x ∈ B.GV k r} := Formalism.FourierDecayAlt.P.B7.isClosed_GV
  have hK : IsCompact ({x : Mt k r | Matrix.of x ∈ B.GV k r} ∩ tsupport φ) := hφc.isCompact.inter_left hGc'
  have hint : ∀ A₁ : B.Mat k r → (Wq →L[ℂ] Wp), ContinuousOn A₁ (B.GV k r) →
      Integrable (fun x : Mt k r => B.hsInner (A₁ (Matrix.of x)) (φ (Matrix.of x))) D.μG := by
    intro A₁ hA₁
    have hof : Continuous (fun x : Mt k r => (Matrix.of x : B.Mat k r)) := continuous_id
    have hc : ContinuousOn (fun x : Mt k r => B.hsInner (A₁ (Matrix.of x)) (φ (Matrix.of x)))
        ({x : Mt k r | Matrix.of x ∈ B.GV k r} ∩ tsupport φ) :=
      (Formalism.FourierDecayAlt.P.B5.hs_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn
        (f := fun x : Mt k r => (A₁ (Matrix.of x), φ (Matrix.of x)))
        ((hA₁.comp hof.continuousOn (fun x (hx : x ∈ {x : Mt k r | Matrix.of x ∈ B.GV k r} ∩ tsupport φ) => hx.1)).prodMk (hφs.continuous.comp hof).continuousOn)
    refine (hc.integrableOn_compact hK).integrable_of_ae_notMem_eq_zero ?_
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hxG hxK
    have hx : x ∉ tsupport φ := fun h => hxK ⟨hxG, h⟩
    show B.hsInner (A₁ (Matrix.of x)) (φ (Matrix.of x)) = 0
    have hz : φ (Matrix.of x) = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hz]
    exact Formalism.FourierDecayAlt.P.B5.hs_zero_right _
  have i1 := hint A hA
  have i2 := hint A' hA'

  set h : Mt k r → ℝ := fun x => β (Matrix.of x) * u (Matrix.of x) with hh
  have hpt : ∀ x : Mt k r, (B.hsInner (A (Matrix.of x)) (φ (Matrix.of x)) -
      B.hsInner (A' (Matrix.of x)) (φ (Matrix.of x))).re = h x := by
    intro x
    simp only [hh, hu, hφ, Formalism.FourierDecayAlt.P.B5.hs_smul_right, Complex.conj_ofReal, ← mul_sub, Complex.re_ofReal_mul]
  have hintR : Integrable h D.μG :=
    (i1.sub i2).re.congr (Eventually.of_forall fun x => by rw [← hpt x]; rfl)
  have hzero : ∫ x, h x ∂D.μG = 0 := by
    have e := integral_re (i1.sub i2)
    simp only [Pi.sub_apply] at e
    rw [integral_sub i1 i2, hEq, sub_self, map_zero] at e
    rw [← e]
    exact integral_congr_ae (Eventually.of_forall fun x => by rw [← hpt x]; rfl)
  have hnn : 0 ≤ᵐ[D.μG] h := by
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hxG
    show 0 ≤ β (Matrix.of x) * u (Matrix.of x)
    by_cases hb : β (Matrix.of x) = 0
    · rw [hb, zero_mul]
    · exact mul_nonneg β.nonneg (hgood _ hxG (by linarith [hβd _ hb])).1.le
  have hae : h =ᵐ[D.μG] 0 := (integral_eq_zero_iff_of_nonneg_ae hnn hintR).1 hzero

  have hO : IsOpen {x : Mt k r | 0 < β (Matrix.of x)} := isOpen_lt continuous_const β.continuous
  have hg₀O : (g₀ : Mt k r) ∈ {x : Mt k r | 0 < β (Matrix.of x)} := by
    show 0 < β g₀
    rw [β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)]
    exact one_pos
  apply Formalism.FourierDecayAlt.P.CutMP.ER.haar_open_pos hμ hO (g₀ := g₀) hg₀G hg₀O
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae, Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx0 hxG hxO
  have hb : 0 < β (Matrix.of x) := hxO
  have hpos : 0 < h x := mul_pos hb (hgood _ hxG (by linarith [hβd _ hb.ne'])).1
  rw [hx0] at hpos
  exact lt_irrefl _ hpos

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocPhi
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

theorem lphi_log_deriv (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv (m + 1) Real.log x‖ = (m.factorial : ℝ) * (x ^ (m + 1))⁻¹ := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  congr 1
  have e : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_neg, zpow_natCast, norm_inv, norm_pow, Real.norm_of_nonneg hx.le]

theorem lphi_deriv_bdd {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {a : ℝ} (ha : 0 < a) (j : ℕ) : ∃ D : ℝ, ∀ x, a < x → ‖iteratedDeriv j φ x‖ ≤ D := by
  choose C hC using hld
  set Φ : ℝ → ℝ := fun u => φ (Real.exp u) with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := hφ
  set s : Set ℝ := Set.Ioi a with hs
  have hso : IsOpen s := isOpen_Ioi
  set K : ℝ := ∑ i ∈ Finset.range (j + 1), |C i| with hK
  have hKi : ∀ i ≤ j, |C i| ≤ K := fun i hi =>
    Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set M : ℝ := max 1 a⁻¹ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  set Dd : ℝ := (j.factorial : ℝ) * M with hDd
  refine ⟨(j.factorial : ℝ) * K * Dd ^ j, fun x hx => ?_⟩
  have hx0 : 0 < x := ha.trans hx
  have hxs : x ∈ s := hx
  have hlogc : ContDiffOn ℝ ∞ Real.log s :=
    Real.contDiffOn_log.mono fun y hy => ne_of_gt (ha.trans (show a < y from hy))
  have hFdB := norm_iteratedFDerivWithin_comp_le (n := j) (N := ∞) (g := Φ) (f := Real.log) (t := Set.univ)
    hΦ.contDiffOn hlogc (by exact_mod_cast le_top) uniqueDiffOn_univ hso.uniqueDiffOn (Set.mapsTo_univ _ _) hxs
    (C := K) (D := Dd) (fun i hi => by
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have := hC i x hx0
      unfold LE.ld at this
      rw [Real.norm_eq_abs]
      exact this.trans ((le_abs_self _).trans (hKi i hi)))
    (fun i hi1 hij => by
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [lphi_log_deriv m hx0]
      have hxi : (x ^ (m + 1))⁻¹ ≤ M ^ (m + 1) := by
        rw [← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hx0.le)
          ((inv_anti₀ ha hx.le).trans (le_max_right _ _)) _
      have hf1 : (m.factorial : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
      have hj1 : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
      have hjp : (j.factorial : ℝ) ≤ (j.factorial : ℝ) ^ (m + 1) := le_self_pow₀ hj1 (by omega)
      rw [hDd, mul_pow]
      exact mul_le_mul (hf1.trans hjp) hxi (by positivity) (by positivity))
  rw [iteratedFDerivWithin_of_isOpen j hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hFdB
  have heq : (Φ ∘ Real.log) =ᶠ[nhds x] φ := by
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
    simp [hΦdef, Real.exp_log (show (0 : ℝ) < y from hy)]
  rw [← heq.iteratedDeriv_eq]
  exact hFdB

theorem lphi_cut {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {δ : ℝ} (hδ : 0 < δ) : ∃ (h : ℝ → ℝ) (ε' : ℝ), U.IsCutG ε' h ∧ ∀ x, δ ≤ x → h x = φ x := by
  set χ₀ : ℝ → ℝ := fun y => Real.smoothTransition (2 * y - 1) with hχ₀
  have hχ : C6.IsCut0 χ₀ := by
    refine ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const),
      ⟨1 / 2, by norm_num, fun y hy => Real.smoothTransition.zero_of_nonpos (by linarith)⟩,
      fun y hy => Real.smoothTransition.one_of_one_le (by linarith)⟩
  obtain ⟨δ₀, hδ₀, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hδ
  set ψ : ℝ → ℝ := fun x => χ₀ (x / δ) with hψ
  have hε : 0 < δ₀ * δ := mul_pos hδ₀ hδ
  have hψ1 : ∀ x, δ ≤ x → ψ x = 1 := fun x hx =>
    hχ.2.2 _ (by rw [le_div_iff₀ hδ]; linarith)
  have hψ0 : ∀ x, x < δ₀ * δ → ψ x = 0 := hcut.2.2
  have hφc := smoothLog_contDiffOn hφ
  refine ⟨fun x => ψ x * φ x, δ₀ * δ, ⟨?_, ?_, fun x hx => by simp [hψ0 x hx]⟩,
    fun x hx => by simp [hψ1 x hx]⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < δ₀ * δ
    · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      simp [hψ0 y hy]
    · have hx0 : 0 < x := lt_of_lt_of_le hε (not_lt.1 hx)
      exact hcut.1.contDiffAt.mul (hφc.contDiffAt (isOpen_Ioi.mem_nhds hx0))
  · intro q
    set a : ℝ := δ₀ * δ / 2 with ha
    have ha0 : 0 < a := by positivity
    choose cψ hcψ using hcut.2.1
    choose D hD using fun j => lphi_deriv_bdd hφ hld ha0 j
    refine ⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)|, fun x => ?_⟩
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)| :=
      Finset.sum_nonneg fun i _ => by positivity
    by_cases hx : x < δ₀ * δ
    · have e : (fun x => ψ x * φ x) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        simp [hψ0 y hy]
      rw [e.iteratedDeriv_eq]
      simp only [iteratedDeriv_const]
      split_ifs <;> simpa using hS0
    · have hxa : a < x := by linarith [not_lt.1 hx]
      set s : Set ℝ := Set.Ioi a with hs
      have hso : IsOpen s := isOpen_Ioi
      have hxs : x ∈ s := hxa
      have hφs : ContDiffOn ℝ ∞ φ s := hφc.mono fun y hy => ha0.trans (show a < y from hy)
      have hL := norm_iteratedFDerivWithin_mul_le (N := ∞) (hcut.1.contDiffOn (s := s)) hφs hso.uniqueDiffOn
        hxs (n := q) (by exact_mod_cast le_top)
      rw [iteratedFDerivWithin_of_isOpen q hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hL
      refine hL.trans (Finset.sum_le_sum fun i hi => ?_)
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedFDerivWithin_of_isOpen (q - i) hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have h1 : ‖iteratedDeriv i ψ x‖ ≤ |cψ i| := (hcψ i x).trans (le_abs_self _)
      have h2 : ‖iteratedDeriv (q - i) φ x‖ ≤ |D (q - i)| := (hD (q - i) x hxa).trans (le_abs_self _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _) (by positivity)

theorem local_phi_transfer_holds : JALocPhi := by
  refine ⟨2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v φ Bg A J hφ hld hBg hJ hFF
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨h, ε', hcut, hhφ⟩ := lphi_cut hφ hld hδ
  obtain ⟨hck, hcc⟩ := gcut_graded (T v).base.z (T v).base.z' h ε' hcut (A := A) hBg hF1 hF2
  refine ⟨fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g, hck, hcc, fun x hx hG => ?_⟩
  have e1 : (fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g) = D.cutF (T v).base h F 1 := by
    funext g; simp [D.cutF, GfP]
  rw [e1, Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, div_one, ← hF3 x hx hG]
  simp only [mulG]
  unfold GfP at hG
  rw [hhφ _ hG]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACBump
section
open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem averaging_bump_holds : ACBump := by
  intro k r Wp Wq _ _ _ _ D K hK hKQ
  have : LocallyCompactSpace (B.Mat k r) :=
    (inferInstance : LocallyCompactSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  have hcont : ContinuousOn (fun q => B.gq D q) (JF.QDom k r D.z D.z') :=
    (Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D 0).continuousOn
  have hgK : IsCompact ((fun q => B.gq D q) '' K) := hK.image_of_continuousOn (hcont.mono hKQ)
  have hsub : (fun q => B.gq D q) '' K ⊆ Q.OmPlus k r D.z D.z' := by
    rintro _ ⟨q, hq, rfl⟩
    exact (Formalism.FourierDecayAlt.P.big_cell_domain k r Wp Wq D q (hKQ hq)).2
  obtain ⟨L, hLc, hKL, hLO⟩ := exists_compact_between hgK (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z') hsub
  obtain ⟨φ₀, hsupp, hsmooth, hrange⟩ :=
    (isOpen_interior : IsOpen (interior L)).exists_contDiff_support_eq (n := ⊤)
  have hts : tsupport φ₀ ⊆ L := by
    unfold tsupport
    rw [hsupp]
    exact closure_minimal interior_subset hLc.isClosed
  refine ⟨φ₀, hsmooth, fun g => (hrange ⟨g, rfl⟩).1, hLc.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hLO, fun q hq => ?_⟩
  have hin : B.gq D q ∈ Function.support φ₀ := by
    rw [hsupp]; exact hKL ⟨q, hq, rfl⟩
  exact lt_of_le_of_ne (hrange ⟨_, rfl⟩).1 (Ne.symm hin)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

