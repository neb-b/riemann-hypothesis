module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalZerosNowhereDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem isAnalyticNear_zeroSetIn {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    IsAnalyticNear (zeroSetIn I) w := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  refine ⟨Set.univ, s.card, fun i z => eval z (s.equivFin.symm i : MvPolynomial σ ℂ), isOpen_univ, trivial,
    fun i => AnalyticOnNhd.eval_mvPolynomial _, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq, true_and]
  constructor
  · intro hz i
    apply hz
    rw [← hs]
    exact Submodule.subset_span (s.equivFin.symm i).2
  · intro hz q hq
    have hle : Ideal.span (s : Set (MvPolynomial σ ℂ)) ≤ RingHom.ker (MvPolynomial.eval z) := by
      rw [Ideal.span_le]
      intro p hp
      rw [SetLike.mem_coe, RingHom.mem_ker]
      simpa using hz (s.equivFin ⟨p, hp⟩)
    rw [← hs] at hq
    exact hle hq

theorem analyticOnNhd_of_differentiableOn_scalar_fin {d : ℕ} {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) : AnalyticOnNhd ℂ F U := by
  refine analyticOnNhd_of_continuousOn_of_separately hU hF.continuousOn (fun z hz i => ?_)
  have h1 : DifferentiableAt ℂ F (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hF.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem germIrreducibleAt_zeroSetIn_of_integrallyClosed (hic : NormalGermIntegrallyClosed.Statement)
    {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (hI : I.IsPrime)
    (hn : IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I)) (hw : w ∈ zeroSetIn I) :
    GermIrreducibleAt (zeroSetIn I) w := by
  refine ⟨hw, fun f g hf hg hfg => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hfne, hgne⟩ := hcon
  set X := zeroSetIn I with hX
  set N : Set (σ → ℂ) :=
    ({z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z}) ∩ interior {z | z ∈ X → f z * g z = 0} with hNdef
  have hNo : IsOpen N := ((isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g)).inter isOpen_interior
  have hwN : w ∈ N := ⟨⟨hf, hg⟩, mem_interior_iff_mem_nhds.mpr hfg⟩
  have hfd : DifferentiableOn ℂ f N := fun z hz => hz.1.1.differentiableAt.differentiableWithinAt
  have hgd : DifferentiableOn ℂ g N := fun z hz => hz.1.2.differentiableAt.differentiableWithinAt
  have hfgN : ∀ z ∈ X ∩ N, f z * g z = 0 := fun z hz => interior_subset hz.2.2 hz.1
  have hGne : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → (f + g) z = 0 := by
    intro hev
    apply hfne
    filter_upwards [hev, hfg] with z h1 h2 hz
    have hs : f z + g z = 0 := h1 hz
    have hp : f z * g z = 0 := h2 hz
    have hff : f z * f z = 0 := by linear_combination f z * hs - hp
    exact mul_self_eq_zero.mp hff
  have ha : ∀ j, DifferentiableOn ℂ ((![0, -1] : Fin 2 → (σ → ℂ) → ℂ) j) N := by
    intro j
    fin_cases j
    · exact differentiableOn_const (0 : ℂ)
    · exact differentiableOn_const (-1 : ℂ)
  obtain ⟨V, hV, hwV, H, hH, hfH⟩ := hic σ I w N f (f + g) 2 ![0, -1] hI hn hw hNo hwN hfd (hfd.add hgd)
    ha hGne (by
      intro z hz
      have hp := hfgN z hz.1
      simp [Fin.sum_univ_two]
      linear_combination -hp)
  have hHc : ContinuousAt H w := (hH.differentiableAt (hV.mem_nhds hwV)).continuousAt
  have hev : ∀ᶠ z in 𝓝 w, z ∈ V ∧ (z ∈ X → f z * g z = 0) := (show ∀ᶠ z in 𝓝 w, z ∈ V from hV.mem_nhds hwV).and hfg
  rw [Filter.not_eventually] at hfne hgne
  have h1 : H w = 1 := by
    by_contra hne
    obtain ⟨z, hz, hzH⟩ := (hfne.and_eventually (hev.and (hHc.eventually_ne hne))).exists
    push Not at hz
    have hg0 : g z = 0 := (mul_eq_zero.mp (hzH.1.2 hz.1)).resolve_left hz.2
    have hfz := hfH z ⟨hz.1, hzH.1.1⟩
    simp only [Pi.add_apply, hg0, add_zero] at hfz
    exact hzH.2 (mul_left_cancel₀ hz.2 (hfz.symm.trans (mul_one _).symm))
  have h0 : H w = 0 := by
    by_contra hne
    obtain ⟨z, hz, hzH⟩ := (hgne.and_eventually (hev.and (hHc.eventually_ne hne))).exists
    push Not at hz
    have hf0 : f z = 0 := (mul_eq_zero.mp (hzH.1.2 hz.1)).resolve_right hz.2
    have hfz := hfH z ⟨hz.1, hzH.1.1⟩
    simp only [Pi.add_apply, hf0, zero_add] at hfz
    exact hzH.2 ((mul_eq_zero.mp hfz.symm).resolve_left hz.2)
  exact one_ne_zero (h1.symm.trans h0)

theorem NormalZerosNowhereDense.proof (hic : NormalGermIntegrallyClosed.Statement)
    (hconn : IrreducibleGermRegularConnected.Statement) (hdense : RegularLocusDense.Statement) :
    NormalZerosNowhereDense.Statement := by
  intro σ _ I w N G hI hn hw hN hwN hG hne
  have han := isAnalyticNear_zeroSetIn I w
  have hirr := germIrreducibleAt_zeroSetIn_of_integrallyClosed hic I w hI hn hw
  set X := zeroSetIn I with hX
  obtain ⟨N₀, hN₀, hwN₀, hd⟩ := hdense σ X w han
  obtain ⟨B, hB, hwB, hBU, hpc⟩ :=
    hconn σ X w han hirr (N ∩ N₀) (Filter.inter_mem (hN.mem_nhds hwN) (hN₀.mem_nhds hwN₀))
  have hBN : B ⊆ N := hBU.trans Set.inter_subset_left
  have hdB : X ∩ B ⊆ closure (regLocus (X ∩ B)) := hd B hB (hBU.trans Set.inter_subset_right)
  refine ⟨B, hB, hwB, hBN, ?_⟩
  intro z hz V hV
  by_contra hall
  push Not at hall
  set R := regLocus (X ∩ B) with hR
  set T : Set (σ → ℂ) := {y | y ∈ X → G y = 0} with hT

  have hloc : ∀ x ∈ R, ∃ M : Set (σ → ℂ), IsOpen M ∧ x ∈ M ∧ ((∃ p ∈ X ∩ M, T ∈ 𝓝 p) → M ⊆ T) := by
    intro x hx
    have hx' : IsRegularPointOf (X ∩ B) x := hx
    obtain ⟨hxXB, d, A, O, W, g, hO, hW, hxW, hg, hAg, hYW⟩ := hx'
    obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := by rw [← hYW]; exact ⟨hxXB, hxW⟩
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO y₀ hy₀O
    have hgO : ∀ y ∈ O, g y ∈ X ∩ B := by
      intro y hy
      have hy' : g y ∈ (X ∩ B) ∩ W := by rw [hYW]; exact Set.mem_image_of_mem g hy
      exact hy'.1
    have hxA : A x ∈ Metric.ball y₀ r := by
      rw [← hgy₀, hAg y₀ hy₀O]
      exact Metric.mem_ball_self hr
    refine ⟨W ∩ B ∩ A ⁻¹' Metric.ball y₀ r,
      (hW.inter hB).inter (Metric.isOpen_ball.preimage A.continuous), ⟨⟨hxW, hxXB.2⟩, hxA⟩, ?_⟩
    have hcov : ∀ p ∈ X ∩ (W ∩ B ∩ A ⁻¹' Metric.ball y₀ r), ∃ y ∈ Metric.ball y₀ r, g y = p := by
      rintro p ⟨hpX, ⟨hpW, hpB⟩, hpA⟩
      obtain ⟨y, hyO, rfl⟩ : p ∈ g '' O := by rw [← hYW]; exact ⟨⟨hpX, hpB⟩, hpW⟩
      refine ⟨y, ?_, rfl⟩
      have hpA' : A (g y) ∈ Metric.ball y₀ r := hpA
      rwa [hAg y hyO] at hpA'
    have hF : AnalyticOnNhd ℂ (fun y => G (g y)) (Metric.ball y₀ r) := by
      refine analyticOnNhd_of_differentiableOn_scalar_fin Metric.isOpen_ball (fun y hy => ?_)
      have hyO := hrO hy
      exact ((hG.differentiableAt (hN.mem_nhds (hBN (hgO y hyO).2))).comp y
        (hg y hyO).differentiableAt).differentiableWithinAt
    rintro ⟨p, hpXM, hpT⟩
    obtain ⟨y₁, hy₁, rfl⟩ := hcov p hpXM
    have hev : (fun y => G (g y)) =ᶠ[𝓝 y₁] 0 := by
      filter_upwards [(hg y₁ (hrO hy₁)).continuousAt.preimage_mem_nhds hpT,
        Metric.isOpen_ball.mem_nhds hy₁] with y hyT hyb
      exact hyT (hgO y (hrO hyb)).1
    have hzero := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y₀ r).isPreconnected hy₁ hev
    intro q hq hqX
    obtain ⟨y, hy, rfl⟩ := hcov q ⟨hqX, hq⟩
    exact hzero hy
  choose! M hMo hxM hMT using hloc

  have hallR : ∀ x ∈ R, T ∈ 𝓝 x := by
    obtain ⟨x₀, hx₀V, hx₀R⟩ := mem_closure_iff_nhds.mp (hdB hz) (interior V) (interior_mem_nhds.mpr hV)
    have hx₀T : T ∈ 𝓝 x₀ :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hx₀V) (fun y hy hyX => hall y ⟨hyX, interior_subset hy⟩)
    by_contra hbad
    push Not at hbad
    obtain ⟨x₁, hx₁R, hx₁T⟩ := hbad
    have hu : IsOpen (⋃ x ∈ {x | x ∈ R ∧ T ∈ 𝓝 x}, M x) := isOpen_biUnion fun x hx => hMo x hx.1
    have hv : IsOpen (⋃ x ∈ {x | x ∈ R ∧ T ∉ 𝓝 x}, M x) := isOpen_biUnion fun x hx => hMo x hx.1
    have hcover : R ⊆ (⋃ x ∈ {x | x ∈ R ∧ T ∈ 𝓝 x}, M x) ∪ (⋃ x ∈ {x | x ∈ R ∧ T ∉ 𝓝 x}, M x) := by
      intro x hx
      by_cases h : T ∈ 𝓝 x
      · exact Or.inl (Set.mem_biUnion (x := x) ⟨hx, h⟩ (hxM x hx))
      · exact Or.inr (Set.mem_biUnion (x := x) ⟨hx, h⟩ (hxM x hx))
    obtain ⟨q, hqR, hqu, hqv⟩ := hpc _ _ hu hv hcover
      ⟨x₀, hx₀R, Set.mem_biUnion (x := x₀) ⟨hx₀R, hx₀T⟩ (hxM x₀ hx₀R)⟩
      ⟨x₁, hx₁R, Set.mem_biUnion (x := x₁) ⟨hx₁R, hx₁T⟩ (hxM x₁ hx₁R)⟩
    obtain ⟨a, ⟨haR, haT⟩, hqa⟩ := Set.mem_iUnion₂.mp hqu
    obtain ⟨b, ⟨hbR, hbT⟩, hqb⟩ := Set.mem_iUnion₂.mp hqv
    have hqX : q ∈ X := (regLocus_subset _ hqR).1
    have hMa : M a ⊆ T := hMT a haR ⟨a, ⟨(regLocus_subset _ haR).1, hxM a haR⟩, haT⟩
    have hqT : T ∈ 𝓝 q := Filter.mem_of_superset ((hMo a haR).mem_nhds hqa) hMa
    have hMb : M b ⊆ T := hMT b hbR ⟨q, ⟨hqX, hqb⟩, hqT⟩
    exact hbT (Filter.mem_of_superset ((hMo b hbR).mem_nhds (hxM b hbR)) hMb)

  have hzeroB : ∀ y ∈ X ∩ B, G y = 0 := by
    intro y hy
    by_contra hGy
    have hc : ContinuousAt G y := (hG.differentiableAt (hN.mem_nhds (hBN hy.2))).continuousAt
    obtain ⟨x, hxG, hxR⟩ := mem_closure_iff_nhds.mp (hdB hy) _ (hc.eventually_ne hGy)
    exact hxG (mem_of_mem_nhds (hallR x hxR) (regLocus_subset _ hxR).1)
  exact hne (Filter.mem_of_superset (hB.mem_nhds hwB) fun y hyB hyX => hzeroB y ⟨hyX, hyB⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolyGermPointPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter Asymptotics

noncomputable section

namespace PolyGermPointPow

theorem coeff_eq_zero_of_isBigO {P : Polynomial ℂ} {k : ℕ}
    (h : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k) : ∀ d < k, P.coeff d = 0 := by
  induction k with
  | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
  | succ k ih =>
    have hn : (fun t : ℂ => ‖t‖) =O[𝓝 0] fun _ => (1 : ℝ) := (continuous_norm.tendsto (0 : ℂ)).isBigO_one ℝ
    have hk := ih (h.trans (by simpa [pow_succ] using (isBigO_refl (fun t : ℂ => ‖t‖ ^ k) _).mul hn))
    obtain ⟨Q, hQ⟩ := Polynomial.X_pow_dvd_iff.mpr hk
    intro d hd
    rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
    · exact hk d hd
    rw [hd, hQ, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨c, hc⟩ := h.bound
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖Q.eval t‖ ≤ c * ‖t‖ := by
      filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with t ht ht0
      rw [hQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow, norm_pow,
        norm_norm, pow_succ] at ht
      have hp : 0 < ‖t‖ ^ k := pow_pos (norm_pos_iff.mpr ht0) k
      exact le_of_mul_le_mul_left (by linarith) hp
    have h2 : Tendsto (fun t => ‖Q.eval t‖) (𝓝[≠] 0) (𝓝 ‖Q.eval 0‖) :=
      ((Q.continuous.tendsto 0).norm).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun t : ℂ => c * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((continuous_norm.tendsto (0 : ℂ)).const_mul c).mono_left nhdsWithin_le_nhds
    exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto h2 h3 h1)

theorem eval_smul_of_isHomogeneous {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ}
    (hh : h.IsHomogeneous d) (t : ℂ) (v : σ → ℂ) : eval (t • v) h = t ^ d * eval v h :=
  _root_.UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous hh t v

variable {σ : Type} [Fintype σ] (w : σ → ℂ)

def bigOIdeal (k : ℕ) : Ideal (holGerms w) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, (f : Germ (𝓝 w) ℂ) = (φ : Germ (𝓝 w) ℂ) ∧
    f =O[𝓝 w] fun z => ‖z - w‖ ^ k}
  add_mem' := by
    rintro φ ψ ⟨f, hf, hfO⟩ ⟨g, hg, hgO⟩
    exact ⟨f + g, by rw [Subring.coe_add, ← hf, ← hg]; rfl, hfO.add hgO⟩
  zero_mem' := ⟨0, rfl, isBigO_zero _ _⟩
  smul_mem' := by
    rintro c φ ⟨f, hf, hfO⟩
    obtain ⟨a, ha, hac⟩ := c.2
    refine ⟨a * f, ?_, ?_⟩
    · rw [smul_eq_mul, Subring.coe_mul, ← hf, ← hac]; rfl
    · show (fun z => a z * f z) =O[𝓝 w] fun z => ‖z - w‖ ^ k
      simpa using (ha.continuousAt.tendsto.isBigO_one ℝ).mul hfO

theorem bigOIdeal_zero : bigOIdeal w 0 = ⊤ := by
  refine eq_top_iff.mpr fun φ _ => ?_
  obtain ⟨f, hf, hfφ⟩ := φ.2
  exact ⟨f, hfφ, by simpa using hf.continuousAt.tendsto.isBigO_one ℝ⟩

theorem pointIdeal_le_bigOIdeal_one : holGermPointIdeal w ≤ bigOIdeal w 1 := by
  intro φ hφ
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have h0 : f w = 0 := by
    have : (Germ.valueRingHom (x := w)) (f : Germ (𝓝 w) ℂ) = 0 := by rw [hfφ]; exact hφ
    exact this
  refine ⟨f, hfφ, ?_⟩
  have := hf.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [h0, sub_zero] at this
  simpa using this.norm_right

theorem bigOIdeal_mul_le (a b : ℕ) : bigOIdeal w a * bigOIdeal w b ≤ bigOIdeal w (a + b) := by
  rw [Ideal.mul_le]
  rintro φ ⟨f, hf, hfO⟩ ψ ⟨g, hg, hgO⟩
  refine ⟨f * g, ?_, ?_⟩
  · rw [Subring.coe_mul, ← hf, ← hg]; rfl
  · show (fun z => f z * g z) =O[𝓝 w] fun z => ‖z - w‖ ^ (a + b)
    simpa [pow_add] using hfO.mul hgO

theorem pointIdeal_pow_le (k : ℕ) : holGermPointIdeal w ^ k ≤ bigOIdeal w k := by
  induction k with
  | zero => rw [pow_zero, Ideal.one_eq_top, bigOIdeal_zero]
  | succ k ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (pointIdeal_le_bigOIdeal_one w)).trans (bigOIdeal_mul_le w k 1)

theorem mem_pow_ker_of_isBigO {k : ℕ} {q : MvPolynomial σ ℂ}
    (hq : (fun z => eval z q) =O[𝓝 w] fun z => ‖z - w‖ ^ k) :
    q ∈ RingHom.ker (MvPolynomial.eval w) ^ k := by
  set q' := bind₁ (fun i => X i + C (w i)) q with hq'def
  have hev : ∀ y, eval y q' = eval (y + w) q := by
    intro y
    rw [hq'def, show (eval y : MvPolynomial σ ℂ →+* ℂ) = eval₂Hom (RingHom.id ℂ) y from rfl, eval₂Hom_bind₁]
    have hfun : (fun i => eval₂Hom (RingHom.id ℂ) y (X i + C (w i))) = y + w := by
      ext i
      simp only [map_add (f := _), eval₂Hom_X', eval₂Hom_C, RingHom.id_apply, Pi.add_apply]
    rw [hfun]
    rfl

  have hcomp : ∀ d < k, homogeneousComponent d q' = 0 := by
    intro d hd
    by_cases hdT : d ∈ Finset.range (q'.totalDegree + 1)
    swap
    · exact homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hdT)
    refine MvPolynomial.funext fun v => ?_
    let P : Polynomial ℂ := ∑ e ∈ Finset.range (q'.totalDegree + 1),
      Polynomial.monomial e (eval v (homogeneousComponent e q'))
    have hP : ∀ t, P.eval t = eval (t • v + w) q := by
      intro t
      rw [← hev]
      conv_rhs => rw [← sum_homogeneousComponent q']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial, map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e q'), mul_comm]
    have hT : Tendsto (fun t : ℂ => t • v + w) (𝓝 0) (𝓝 w) := by
      simpa using ((continuous_id.smul continuous_const).add continuous_const).tendsto (0 : ℂ)
        (f := fun t : ℂ => t • v + w)
    have hPO : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k := by
      simp_rw [hP]
      refine (hq.comp_tendsto hT).trans (IsBigO.of_bound (‖v‖ ^ k) (Eventually.of_forall fun t => ?_))
      simp [norm_smul, mul_pow, mul_comm]
    have hc := coeff_eq_zero_of_isBigO hPO d hd
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Finsupp.single_apply, Finset.sum_ite_eq', if_pos hdT] at hc
    simpa using hc
  have hmem : q' ∈ idealOfVars σ ℂ ^ k := by
    refine (mem_pow_idealOfVars_iff' k q').mpr fun x hx => ?_
    have := congrArg (AddMonoidAlgebra.coeff · x) (hcomp _ hx)
    simpa [coeff_homogeneousComponent, AddMonoidAlgebra.coeff] using this
  have hback : bind₁ (fun i => X i - C (w i)) q' = q := by
    rw [hq'def, bind₁_bind₁]
    simp [bind₁_X_right]
  have := Ideal.mem_map_of_mem (bind₁ (fun i => (X i - C (w i) : MvPolynomial σ ℂ))) hmem
  rw [Ideal.map_pow, idealOfVars, Ideal.map_span, ← Set.range_comp, hback] at this
  rw [GroundTheory.Heights₂.Heights.GradientAtPoint.ker_eval_eq_span]
  simpa [Function.comp_def, bind₁_X_right] using this

end PolyGermPointPow

theorem PolyGermPointPow.proof : PolyGermPointPow.Statement := by
  intro σ _ w k q hq
  obtain ⟨f, hf, hfO⟩ := PolyGermPointPow.pointIdeal_pow_le w k hq
  have hf' : (f : Germ (𝓝 w) ℂ) = ((fun z => eval z q : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := hf
  exact PolyGermPointPow.mem_pow_ker_of_isBigO w (hfO.congr' (Germ.coe_eq.mp hf') EventuallyEq.rfl)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionLocalCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem ProperOpenProjectionLocalCover.proof (hR : ProperOpenProjectionLocalUnbranched.Statement) :
    ProperOpenProjectionLocalCover.Statement := by
  intro σ _ X B k f d A D hB hf hXB hDo hmaps hprop hopen y₀ hy₀
  obtain ⟨U₁, g, hU₁o, hy₀U₁, hU₁D, hg, hgd, hsec⟩ :=
    hR σ X B k f d A D hB hf hXB hDo hmaps hprop hopen y₀ hy₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU₁o y₀ hy₀U₁
  set U := Metric.ball y₀ r with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball
  have hy₀U : y₀ ∈ U := Metric.mem_ball_self hr
  have hUD : U ⊆ D := hball.trans hU₁D
  have hgU : AnalyticOnNhd ℂ g U := hg.mono hball
  have hgdU : ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0 :=
    fun W hW hWU hWne => hgd W hW (hWU.trans hball) hWne

  set Y : Set (σ → ℂ) := {x | x ∈ X ∩ B ∧ A x ∈ U} with hYdef
  have hfib : ∀ y ∈ U, {x | x ∈ Y ∧ A x = y} = {x | x ∈ X ∩ B ∧ A x = y} := by
    intro y hy
    ext x
    simp only [hYdef, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hx, _⟩, hAx⟩
      exact ⟨hx, hAx⟩
    · rintro ⟨hx, hAx⟩
      exact ⟨⟨hx, hAx ▸ hy⟩, hAx⟩
  have hYmaps : Set.MapsTo A Y U := fun x hx => hx.2
  have hYprop : ∀ K ⊆ U, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K} := by
    intro K hKU hK
    have : {x | x ∈ Y ∧ A x ∈ K} = {x | x ∈ X ∩ B ∧ A x ∈ K} := by
      ext x
      simp only [hYdef, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hKU h.2⟩, h.2⟩⟩
    rw [this]
    exact hprop K (hKU.trans hUD) hK
  have hYsec : ∀ x ∈ Y, g (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn h O ∧ (∀ y ∈ O, A (h y) = y) ∧ Y ∩ V = h '' O := by
    intro x hx hgx
    obtain ⟨O, V, h, hO, hV, hxV, hh, hAh, hXV⟩ := hsec (A x) (hball hx.2) hgx x hx.1 rfl
    refine ⟨O ∩ U, V ∩ A ⁻¹' U, h, hO.inter hUo, hV.inter (hUo.preimage A.continuous), ⟨hxV, hx.2⟩,
      hh.continuousOn.mono Set.inter_subset_left, fun y hy => hAh y hy.1, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨hzXB, hzU⟩, hzV, -⟩
      have : z ∈ h '' O := hXV ▸ ⟨hzXB, hzV⟩
      obtain ⟨y, hyO, rfl⟩ := this
      exact ⟨y, ⟨hyO, by rwa [hAh y hyO] at hzU⟩, rfl⟩
    · rintro ⟨y, ⟨hyO, hyU⟩, rfl⟩
      have hmem : h y ∈ X ∩ B ∩ V := hXV ▸ ⟨y, hyO, rfl⟩
      have hAy : A (h y) ∈ U := by rw [hAh y hyO]; exact hyU
      exact ⟨⟨hmem.1, hAy⟩, hmem.2, hAy⟩

  obtain ⟨n, hn⟩ := UnbranchedProperCountConstant.proof UnbranchedProperCountLocallyConstant.proof
    ManifoldZerosComplementConnected.proof σ Y d A U g hUo (convex_ball y₀ r).isPreconnected hYmaps hYprop
    hgU hYsec
  have hcount : ∀ y ∈ U, g y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = n := by
    intro y hy hgy
    rw [← hfib y hy]
    exact hn y hy hgy

  have hle : ∀ y ∈ U, {x | x ∈ X ∩ B ∧ A x = y}.encard ≤ n := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    have hn1 : ((n + 1 : ℕ) : ℕ∞) ≤ {x | x ∈ X ∩ B ∧ A x = y}.encard := by
      rw [Nat.cast_add, Nat.cast_one]
      exact Order.add_one_le_of_lt hlt
    obtain ⟨T, hTF, hTcard⟩ := Set.exists_subset_encard_eq hn1
    have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard
    obtain ⟨S, hS, hSdisj⟩ := hTfin.t2_separation
    have hW : U ∩ ⋂ x ∈ T, A '' (X ∩ B ∩ S x) ∈ 𝓝 y := by
      refine Filter.inter_mem (hUo.mem_nhds hy) ((Filter.biInter_mem hTfin).2 fun x hx => ?_)
      have hxF := hTF hx
      have := hopen x hxF.1 (S x) ((hS x).2.mem_nhds (hS x).1)
      rwa [hxF.2] at this
    obtain ⟨t, ⟨htW, hgt⟩⟩ := hgdU (interior (U ∩ ⋂ x ∈ T, A '' (X ∩ B ∩ S x))) isOpen_interior
      (interior_subset.trans Set.inter_subset_left) ⟨y, mem_interior_iff_mem_nhds.2 hW⟩
    have htW' := interior_subset htW
    have htU : t ∈ U := htW'.1
    have hpick : ∀ x ∈ T, ∃ z, z ∈ X ∩ B ∩ S x ∧ A z = t := by
      intro x hx
      have := Set.mem_iInter₂.1 htW'.2 x hx
      obtain ⟨z, hz, hAz⟩ := this
      exact ⟨z, hz, hAz⟩
    choose! z hz hAz using hpick
    have hinj : Set.InjOn z T := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.1 (hSdisj ha hb hne) (hz a ha).2 (hab ▸ (hz b hb).2)
    have hsub : z '' T ⊆ {x | x ∈ X ∩ B ∧ A x = t} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hz x hx).1, hAz x hx⟩
    have := (Set.encard_le_encard hsub).trans_eq (hcount t htU hgt)
    rw [hinj.encard_image, hTcard] at this
    exact absurd this (by norm_cast; omega)
  refine ⟨U, g, n, hUo, hy₀U, hUD, hgU, hgdU, hle, fun y hy hgy => ⟨hcount y hy hgy, ?_⟩⟩
  intro x hx hAx
  exact hsec y (hball hy) hgy x hx hAx

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchSheetAE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def BranchSheetAE.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (p : Fin n → ℂ)
    (γ : VarBranch J d p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ᵐ t ∂(volume.restrict (Metric.ball (0 : Fin d → ℂ) γ.radius)), ∃ s, IsSheetAt J A (γ.toFun t) s

end

end GroundTheory.Heights₂.Heights
end

