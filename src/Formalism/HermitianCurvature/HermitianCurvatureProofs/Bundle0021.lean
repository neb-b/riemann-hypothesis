module

public import Formalism.HermitianCurvature.StatementG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionCriticalPoints
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AffineChangeOfVariables
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardCharacterExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakApproximationGL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WhittakerVanishingImpliesZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitTailEstimates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionDerivatives
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EtaleIntegralityFacts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StationaryPhaseEstimates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StationaryPhaseModel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0020
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Markov
public import Formalism.HermitianCurvature.PositionExpansionTopCoefficients
public import Lemmata.HermitianSesquilinear.ConjEqOfNonnegReal
public import Formalism.HermitianCurvature.StatementM
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0019

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChangeOfVariablesXy
section
namespace Formalism.FourierDecayAlt.P

theorem orbit_tail_estimate : Formalism.FourierDecayAlt.G.TailStep :=
  tail_estimate_of_bound tailBound_statement matrix_cutoff_spec cutoff_phase_bound

theorem change_of_variables_xy : Formalism.FourierDecayAlt.G.InnerXY :=
  inner_xy_of_reduced orbital_integral_reduced reduced_integrand_integrable split_xy_coordinates amplitude_eq

theorem nonstationary_estimate : Formalism.FourierDecayAlt.G.NonStatStep :=
  nonstationary_estimate_of_parts nonstationary_phase gradient_lower_bound phase_function_deriv phase_relative_deriv
    critical_cutoff_spec amplitude_bound_far orbital_integral_converges_abs cutoff_phase_bound change_of_variables_xy

theorem stationary_estimate : Formalism.FourierDecayAlt.G.StatStep :=
  stationary_estimate_of_parts stationary_phase_holomorphic phase_function_deriv phase_function_critical_points hessian_at_critical hessian_determinant
    phase_near_critical critical_cutoff_spec amplitude_bound_critical amplitude_continuous_at_critical majorant_y
    orbital_integral_converges_abs cutoff_phase_bound change_of_variables_xy

theorem germ_rate : Formalism.FourierDecayAlt.G.GermRate :=
  germ_rate_of_estimates orbital_integral_converges_abs cutoff_phase_bound critical_cutoff_spec exists_small_delta
    root_set_characterization orbit_tail_estimate change_of_variables_xy nonstationary_estimate stationary_estimate amplitude_limit
    limit_integral stationary_leading_constant germ_large_parameter

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EnergyEstimateFromParts
section
namespace Formalism.FourierDecayAlt.P

theorem le_thetaRange_proof : Formalism.FourierDecayAlt.LE.ThetaRange := by
  intro ε σ x hε hσ hx
  simp only [LE.th]
  have hb : 0 < x / (x + ε) := by positivity
  exact ⟨Real.rpow_pos_of_pos hb σ, Real.rpow_le_one hb.le ((div_le_one (by linarith)).mpr (by linarith)) hσ⟩

theorem le_thetaSmooth_proof : Formalism.FourierDecayAlt.LE.ThetaSmooth := Formalism.FourierDecayAlt.P.LEx1.thetaSmooth

theorem cutoff_bound : Formalism.FourierDecayAlt.LE.CutBound := Formalism.FourierDecayAlt.P.LEx1.cutBound

theorem cutoff_theta : Formalism.FourierDecayAlt.LE.CutTheta := Formalism.FourierDecayAlt.P.LEx1.cutTheta

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GramProductIdentities
section
namespace Formalism.FourierDecayAlt.P.GramProductIdentities

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

end Rep

section CS

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem cs_of_pos (Ξ : F7.Sesq M) (h : ∀ m, 0 ≤ (Ξ m m).re ∧ (Ξ m m).im = 0) (x y : M) :
    ‖Ξ x y‖ ^ 2 ≤ (Ξ x x).re * (Ξ y y).re := by
  first | exact Bl.HermitianSesquilinear.goal1 .. | (apply Bl.HermitianSesquilinear.goal1 <;> assumption) | (intros; apply Bl.HermitianSesquilinear.goal1 <;> assumption) | (apply @Bl.HermitianSesquilinear.goal1 <;> assumption) | (intros; apply @Bl.HermitianSesquilinear.goal1 <;> assumption) | (apply @Bl.HermitianSesquilinear.goal1 <;> first | assumption | infer_instance) | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h x y | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h x | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› | exact @Bl.HermitianSesquilinear.goal1 M ‹_› | exact @Bl.HermitianSesquilinear.goal1 M

end CS

theorem exp_le_one_add {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.exp (-2 * |x|) ≤ 1 + x := by
  rcases le_or_gt 0 x with h0 | h0
  · have : Real.exp (-2 * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg x])
    linarith
  · have hu : |x| = -x := abs_of_neg h0
    set u := -x with hu'
    have hu0 : 0 ≤ u := by linarith
    have hu1 : u ≤ 1 / 2 := by rw [← hu]; exact hx
    have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
    have h2 : Real.exp (-2 * u) * Real.exp (2 * u) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp (-2 * u) * (1 + 2 * u) ≤ 1 := by
      calc Real.exp (-2 * u) * (1 + 2 * u) ≤ Real.exp (-2 * u) * Real.exp (2 * u) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := h2
    rw [hu]
    have he := Real.exp_pos (-2 * u)
    nlinarith [mul_nonneg hu0 (by linarith : (0:ℝ) ≤ 1 - 2 * u)]

theorem prod_bounds {ι : Type} (g : ι → ℝ) (ε : ℝ) (hε : ε ≤ 1 / 2) :
    ∀ w : List ι, (∀ l ∈ w, |g l - 1| ≤ ε) →
      Real.exp (-2 * ε * w.length) ≤ (w.map g).prod ∧ (w.map g).prod ≤ Real.exp (ε * w.length) := by
  intro w
  induction w with
  | nil => intro _; simp
  | cons l w ih =>
    intro hw
    obtain ⟨ih1, ih2⟩ := ih fun l' hl' => hw l' (by simp [hl'])
    have hl := hw l (by simp)
    have hx : |g l - 1| ≤ 1 / 2 := le_trans hl hε
    have hlo : Real.exp (-2 * ε) ≤ g l := by
      have := exp_le_one_add hx
      have : Real.exp (-2 * ε) ≤ Real.exp (-2 * |g l - 1|) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hhi : g l ≤ Real.exp ε := by
      have := Real.add_one_le_exp (g l - 1)
      have : Real.exp (g l - 1) ≤ Real.exp ε := Real.exp_le_exp.mpr (le_trans (le_abs_self _) hl)
      linarith
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have e1 : Real.exp (-2 * ε * (w.length + 1)) = Real.exp (-2 * ε) * Real.exp (-2 * ε * w.length) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (ε * (w.length + 1)) = Real.exp ε * Real.exp (ε * w.length) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    constructor
    · exact mul_le_mul hlo ih1 (Real.exp_pos _).le (le_trans (Real.exp_pos _).le hlo)
    · exact mul_le_mul hhi ih2 (le_trans (Real.exp_pos _).le ih1) (Real.exp_pos _).le

theorem qProduct : QProduct := by
  intro S _ _ q w Y hq hw
  induction w with
  | nil => simp [qw, hq]
  | cons l w ih =>
    have hl := hw l (by simp)
    have ih' := ih fun l' hl' => hw l' (by simp [hl'])
    simp only [qw, List.map_cons, List.prod_cons]
    rw [← ih']
    cases hp : l.plus
    · simp only [hp] at hl ⊢
      simp only [Bool.false_eq_true, if_false]
      have h2 : l.pt - Y - 1 ≠ 0 := hl
      field_simp
      try ring
    · simp only [hp] at hl ⊢
      simp only [if_true]
      have h2 : Y - l.pt ≠ 0 := hl
      field_simp
      try ring

theorem lemmaQ : LemmaQ := by
  intro S _ _ q w N dl Y hN hw hdl hpts hq
  have hN' : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hdlpos : 0 < dl := by nlinarith
  set g : Letter ℝ S → ℝ := fun l => if l.plus then 1 + 1 / (Y - l.pt) else 1 + 1 / (l.pt - Y - 1)
    with hg
  have hfac : ∀ l ∈ w, |g l - 1| ≤ 1 / dl := by
    intro l hl
    have h := hpts l hl
    cases hp : l.plus
    · simp only [hp, Bool.false_eq_true, if_false] at h
      simp only [hg, hp, Bool.false_eq_true, if_false, add_sub_cancel_left, abs_div, abs_one]
      have : |l.pt - Y - 1| = |Y - (l.pt - 1)| := by rw [← abs_neg]; ring_nf
      rw [this]
      exact one_div_le_one_div_of_le hdlpos h.2
    · simp only [hp, if_true] at h
      simp only [hg, hp, if_true, add_sub_cancel_left, abs_div, abs_one]
      exact one_div_le_one_div_of_le hdlpos h
  have hreg : ∀ l ∈ w, if l.plus then Y - l.pt ≠ 0 else l.pt - Y - 1 ≠ 0 := by
    intro l hl
    have h := hpts l hl
    cases hp : l.plus
    · simp only [hp, Bool.false_eq_true, if_false] at h ⊢
      intro h0
      have : |Y - (l.pt - 1)| = 0 := by rw [abs_eq_zero]; linarith
      linarith [h.2]
    · simp only [hp, if_true] at h ⊢
      intro h0
      rw [h0, abs_zero] at h
      linarith
  have hprod := qProduct S q w Y hq hreg
  have hε : 1 / dl ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  obtain ⟨hlo, hhi⟩ := prod_bounds g (1 / dl) hε w hfac
  have hlen : (w.length : ℝ) ≤ N := by exact_mod_cast hw
  have hkey : 1 / dl * w.length ≤ 1 / 4 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hdlpos]
    nlinarith
  rw [hprod]
  constructor
  · refine le_trans (Real.exp_le_exp.mpr ?_) hlo
    nlinarith
  · refine le_trans hhi (Real.exp_le_exp.mpr ?_)
    linarith

theorem dkStep4 : DKStep4 := by
  intro S q w L hL
  induction L with
  | nil => simp [kapF]
  | cons l L ih =>
    have hl : l.plus = true := hL l (by simp)
    have hL' : ∀ l' ∈ L, l'.plus = true := fun l' h => hL l' (by simp [h])
    have h1 : (L.map fun l' => if l.plus = l'.plus then (1:ℂ)
        else 1 - ((l.pt - l'.pt + (if l.plus then 1 else -1)) ^ 2)⁻¹).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨l', hl', rfl⟩ := hx
      simp [hl, hL' l' hl']
    simp only [kapF, List.map_cons, List.prod_cons]
    rw [h1, ih hL']
    simp only [ypt, hl, if_true]
    ring

end Formalism.FourierDecayAlt.P.GramProductIdentities

theorem Formalism.FourierDecayAlt.P.lemma_Q_estimate : Formalism.FourierDecayAlt.FormPairingAction.LemmaQ := Formalism.FourierDecayAlt.P.GramProductIdentities.lemmaQ
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelWordsAssemble
section
namespace Formalism.FourierDecayAlt.P

open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M

namespace Mx9

theorem eq_ofReal {z : ℂ} (h : z.im = 0) : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])

theorem star_eq {z : ℂ} (h : z.im = 0) : star z = z := by
  exact Complex.conj_eq_iff_im.mpr h

theorem far {z z' : ℂ} (h : 2 < |z.re - z'.re|) (n : ℤ) (hn : |n| ≤ 2) : z - z' ≠ (n : ℂ) := by
  intro heq
  have h1 := congrArg Complex.re heq
  simp only [Complex.sub_re, Complex.intCast_re] at h1
  rw [h1] at h
  have h2 : ((|n| : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hn
  rw [Int.cast_abs] at h2
  linarith

noncomputable def ty0 (P : Par) : Ty P := fun _ => 0

theorem xC_ne (hR : RealPoints) (P : Par) (π : Ty P) (n : ℕ) (Y : ℝ)
    (h : 0 < (-1 : ℝ) ^ n * I.xpoly P.k (rho P π) Y) : xC P π (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P π Y).1] at h0
  have h1 : I.xpoly P.k (rho P π) Y = 0 := by exact_mod_cast h0
  rw [h1, mul_zero] at h
  exact lt_irrefl _ h

theorem qC_ne (hR : RealPoints) (P : Par) (Y : ℝ)
    (h : 0 < I.qpoly P.k P.T P.T' P.u P.u' Y) : qC P (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P (ty0 P) Y).2] at h0
  have h1 : I.qpoly P.k P.T P.T' P.u P.u' Y = 0 := by exact_mod_cast h0
  rw [h1] at h
  exact lt_irrefl _ h

end Mx9

open Mx9

theorem cut_admissible : Formalism.FourierDecayAlt.M.CutAdm := by
  intro hIS hQP hQS hTy hR P hP l hl1 hlk S _ _ w hw
  obtain ⟨hnd, hpt, hpw⟩ := hw
  have key : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ∀ e ∈ ({-1, 0, 1} : Finset ℝ),
      ((Y + e : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY e he
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + e) (hIS P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY e he)
  have qpos : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q (Y : ℂ) ≠ 0 := by
    intro Y hY
    exact qC_ne hR P Y (hQP P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
  have qsh : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q ((Y : ℂ) - 1) ≠ 0 := by
    intro Y hY
    have h := qC_ne hR P (Y - 1) (hQS P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
    push_cast at h
    exact h
  refine ⟨hnd, fun a ha => star_eq (hpt a ha).1, fun a ha => ?_, hpw.imp fun h n hn => far h n hn⟩
  obtain ⟨him, hcut⟩ := hpt a ha
  have hz : a.pt = ((a.pt.re : ℝ) : ℂ) := eq_ofReal him
  rw [hz]
  refine ⟨?_, ?_, ?_, qpos _ hcut, qsh _ hcut⟩
  · convert key _ hcut 0 (by norm_num) using 1 <;> push_cast <;> ring
  · convert key _ hcut 1 (by norm_num) using 1 <;> push_cast <;> ring
  · convert key _ hcut (-1) (by norm_num) using 1 <;> push_cast <;> ring

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MultiplicationOpHom
section
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.Mx1

theorem star_sc (P : Par) (w : Pr P.r) : star (sc P w) = sc P (star w) := by
  unfold sc
  ext i j
  rw [Matrix.star_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

end Formalism.FourierDecayAlt.P.Mx1

namespace Formalism.FourierDecayAlt.P

open Mx1

theorem model_nontrivial : Formalism.FourierDecayAlt.M.ModelNontrivial := by
  intro P
  have key : ∀ w : Pr P.r, sc P w = 0 → w = 0 := by
    intro w h
    have := congrFun (congrFun h (fun _ => 0)) (fun _ => 0)
    simpa [sc] using this
  refine ⟨⟨⟨0, 1, fun h => ?_⟩⟩, fun f fb h => ?_⟩
  · have h1 : (1 : Pr P.r) = 0 := key 1 (by unfold sc; rw [map_one]; exact h.symm)
    have h2 : (1 : Op P.r) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simp at h2
  · have h1 := key _ h
    have h2 : (mulOp f) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simpa [mulOp] using h2

theorem star_generators : Formalism.FourierDecayAlt.M.StarGens := by
  intro P
  have hs : ∀ X Y : Op P.r, star (mk X Y) = mk Y X := fun X Y => rfl
  have hneg : ∀ X Y : Op P.r, -(mk X Y : Pr P.r) = mk (-X) (-Y) := fun X Y => rfl
  have mc : ∀ f g : Fn P.r, mulOp f * mulOp g = mulOp g * mulOp f := fun f g => by
    refine LinearMap.ext fun x => ?_
    simp only [mulOp, Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, mul_comm f g]
  refine ⟨fun l => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cA cbA; rw [star_sc]; rfl
  · unfold ciA cbiA; rw [star_sc]; rfl
  · unfold pA pbA
    rw [star_sc]
    unfold sc
    rw [← map_neg]
    congr 1
    unfold pP pbP
    rw [hs, hneg, neg_neg]
  · unfold zA zbA; rw [star_sc]; rfl
  · unfold ziA zbiA; rw [star_sc]; rfl
  · unfold ggA; rw [star_sc]; rfl
  · unfold ggiA; rw [star_sc]; rfl
  · have e1 : star (dzP : Pr P.r) = -dzbP := by
      unfold dzP dzbP
      rw [hs, hneg, neg_neg]
    have e2 : star (zbP : Pr P.r) = zP := rfl
    have e3 : star (ggiP P.TT : Pr P.r) = ggiP P.TT := rfl
    have e4 : (ggiP P.TT : Pr P.r) * zP = zP * ggiP P.TT := by
      unfold ggiP zP fnP M.mk
      refine Prod.ext (mc _ _) ?_
      show MulOpposite.op _ * MulOpposite.op _ = MulOpposite.op _ * MulOpposite.op _
      rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, mc]
    unfold nabA nabsA
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext π
    rw [Pi.star_apply, star_add, star_smul, star_mul, e1, e2, e3, e4, Complex.star_def, Complex.conj_ofReal]

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThShiftInt
section
open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem Hh_add_int {w : ℂ} (k : ℤ) : w + (k : ℂ) * (2 * Real.pi * I) ∈ Hh TT ↔ w ∈ Hh TT := by
  simp only [Hh, Set.mem_ofPred_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem Hh_add_one {w : ℂ} (hw : w ∈ Hh TT) : w + 2 * Real.pi * I ∈ Hh TT := by
  have := (Hh_add_int (TT := TT) (w := w) 1).2 hw
  simpa using this

theorem th_shift (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    th TT α (w + 2 * Real.pi * I) = th TT α w + 2 * (circleIntegral α 0 (TT + 1)).im := by
  have hc : ∀ z ∈ Hh TT, HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I) - th TT α z)
      (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    have h1 : HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I)) (om α (z + 2 * Real.pi * I)) z := by
      have := (hasFDerivAt_th hTT hα hcurv (Hh_add_one hz)).comp z
        ((hasFDerivAt_id z).add_const (2 * Real.pi * I))
      exact this
    have h2 := hasFDerivAt_th hTT hα hcurv hz
    have hom : om α (z + 2 * Real.pi * I) = om α z := by
      have := bet_periodic α z 1
      simp only [Int.cast_one, one_mul] at this
      simp only [om, this]
    have := h1.sub h2
    rwa [hom, sub_self] at this
  have hconst := (convex_Hh TT).is_const_of_fderivWithin_eq_zero
    (fun z hz => (hc z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hc z hz).hasFDerivWithinAt.fderivWithin ((isOpen_Hh TT).uniqueDiffWithinAt hz))
    (base_point_mem_half_plane hTT) hw
  rw [th_top hTT hα, theta_at_base_point_zero, sub_zero] at hconst
  linarith

theorem th_shift_int (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (k : ℤ) :
    ∀ w ∈ Hh TT, th TT α (w + (k : ℂ) * (2 * Real.pi * I)) = th TT α w + k * (2 * (circleIntegral α 0 (TT + 1)).im) := by
  intro w hw
  refine Int.induction_on k ?_ ?_ ?_
  · simp
  · intro n ih
    have hmem : w + ((n : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int (n : ℤ)).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + ((n : ℂ) + 1) * (2 * Real.pi * I) = w + (n : ℂ) * (2 * Real.pi * I) + 2 * Real.pi * I by ring,
      h1, ih]
    ring
  · intro n ih
    have hmem : w + ((-(n : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int _).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + (-(n : ℂ) - 1) * (2 * Real.pi * I) + 2 * Real.pi * I = w + -(n : ℂ) * (2 * Real.pi * I) by ring,
      ih] at h1
    linarith

theorem expI_th_eq (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n)
    {w w' : ℂ} (hw : w ∈ Hh TT) (hw' : w' ∈ Hh TT) (he : Complex.exp w = Complex.exp w') :
    Complex.exp (I * (th TT α w : ℂ)) = Complex.exp (I * (th TT α w' : ℂ)) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  obtain ⟨m, hm⟩ := hhol
  have h := th_shift_int hTT hα hcurv n w' hw'
  rw [← hn, hm] at h
  apply Complex.exp_eq_exp_iff_exists_int.2
  refine ⟨n * m, ?_⟩
  rw [h]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

