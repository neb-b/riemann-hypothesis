module

public import Formalism.HermitianCurvature.Bundle0006
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0031
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
section
open MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem signed_coordinate_eq_sign_smul (P : M.Par) (l : ℕ) (Y : ℂ) :
    (fun ρ => M.x0 P l ρ Y) = M.sgn P l • fun ρ => M.xC P ρ Y := by
  funext ρ
  simp only [Pi.smul_apply, smul_eq_mul, M.x0, M.sgn, M.xC]

theorem xKappaOfNF : XKappaOfNF := by
  intro hNF hPos Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨hPl, -, hL, hQQ, -, hinv, -, hLS⟩ := hD
  obtain ⟨d, hdL, hdS, hdR, hdQ⟩ := hNF Wp Wq P z z' π π' hPl X
  have hfn : ∀ i j : Fin 6,
      (∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' i x.2 * fnVal P.k P.r z z' j x.2 = 1) →
      X.fn i * X.fn j = 1 := by
    intro i j hij
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun c => funext fun g => ?_)
    rw [Module.End.mul_apply, Module.End.one_apply]
    by_cases hx : (c, g) ∈ DomR P.k P.r z z'
    · have e1 := X.fn_apply i (X.fn j Φ) (c, g) hx
      have e2 := X.fn_apply j Φ (c, g) hx
      dsimp only at e1 e2
      rw [e1, e2, smul_smul, hij (c, g) hx, one_smul]
    · have e1 := (X.fn i (X.fn j Φ)).2.1 (c, g) hx
      have e2 := Φ.2.1 (c, g) hx
      dsimp only at e1 e2
      rw [e1, e2]
  have hG : ∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' 5 x.2 * fnVal P.k P.r z z' 4 x.2 = 1 := by
    intro x hx
    simp only [fnVal]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hx.2.2.ne')
  have hG' : ∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' 4 x.2 * fnVal P.k P.r z z' 5 x.2 = 1 := by
    intro x hx
    simp only [fnVal]
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx.2.2.ne')
  have hGinv : L.GGi * L.GG = 1 := by
    rw [hL.2.2.2.2.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine Prod.ext ?_ ?_
    · show X.fn 5 * X.fn 4 = 1
      exact hfn 5 4 hG
    · show MulOpposite.op (X.fn 5) * MulOpposite.op (X.fn 4) = MulOpposite.op 1
      rw [← MulOpposite.op_mul, hfn 4 5 hG']
  have hGG : L.GG = d.L.GG := hL.2.2.2.2.2.2.2.2.2.2.1.trans hdL.2.2.2.2.2.2.2.2.2.2.1.symm
  have hx : ∀ Y, st.x Y = d.κ fun ρ => M.x0 P l0 ρ Y := by
    intro Y
    have h1 := hLS.tau Y
    have h2 : d.QQ Y 1 1 = d.L.GG * d.x Y := by simp [NFData.QQ]
    rw [hQQ Y, hdQ Y, Matrix.smul_apply, h2, ← hGG, ← mul_smul_comm] at h1
    have h3 : st.x Y = M.sgn P l0 • d.x Y := by
      calc st.x Y = L.GGi * (L.GG * st.x Y) := by rw [← mul_assoc, hGinv, one_mul]
        _ = L.GGi * (L.GG * (M.sgn P l0 • d.x Y)) := by rw [← h1]
        _ = _ := by rw [← mul_assoc, hGinv, one_mul]
    rw [h3, NFData.x, signed_coordinate_eq_sign_smul, map_smul]
  have hxi : ∀ Y ∈ st.inv, st.xi Y = d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ := by
    intro Y hY
    have hne : ∀ ρ, M.x0 P l0 ρ Y ≠ 0 := by
      intro ρ
      have hY' := hY
      rw [hinv] at hY'
      have e := congrFun (signed_coordinate_eq_sign_smul P l0 Y) ρ
      simp only [Pi.smul_apply, smul_eq_mul] at e
      rw [e]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (hY' ρ)
    have hprod : (d.κ fun ρ => M.x0 P l0 ρ Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹) = 1 := by
      rw [← map_mul, ← map_one d.κ]
      congr 1
      funext ρ
      simp [hne ρ]
    calc st.xi Y
        = st.xi Y * ((d.κ fun ρ => M.x0 P l0 ρ Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹)) := by
          rw [hprod, mul_one]
      _ = (st.xi Y * st.x Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹) := by rw [hx Y, mul_assoc]
      _ = _ := by rw [(hLS.x_xi Y hY).2, one_mul]
  exact ⟨d.κ, hx, hxi, hPos Wp Wq P z z' π π' hPl X d hdL hdS hdR hdQ⟩

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem smooth_zero (σ : Mx k r → (H →L[ℂ] H)) : (0 : H) ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH]
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => map_zero (σ g)⟩

theorem smooth_add {σ : Mx k r → (H →L[ℂ] H)} {v w : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ)
    (hw : w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) : v + w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv hw ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hv g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hGe⟩ := hw g₀ hg₀
  refine ⟨U ∩ V, fun g => F g + G g, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  simp only [map_add (f := _), hFe g hg.1 hgH, hGe g hg.2 hgH]

theorem smooth_smul {σ : Mx k r → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) :
    a • v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hv g₀ hg₀
  refine ⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, fun g hg hgH => ?_⟩
  simp only [map_smul, hFe g hg hgH]

theorem DD_smooth (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hw : PI.UpqRep.IsLowUnitH k r ε lam σ w0) :
    ∀ x ∈ DDsp σ w0, x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hrep := hDS.2.2.1.1.2
  have hconj := Formalism.QuantumDeterminants.unitary_conjugation_holds _ ε (PI.UpqRep.Hpk k r) P hdet hPJ
  have hback : ∀ g, P⁻¹ * (P * g * P⁻¹) * P = g := by
    intro g
    rw [show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      hPP, Matrix.one_mul, Matrix.mul_one]
  have hmul : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b →
      σ (a * b) = (σ a).comp (σ b) := by
    intro a b ha hb
    have ha' := (hconj a).mp ha
    have hb' := (hconj b).mp hb
    have h := hrep _ ha' _ hb'
    simp only [hback] at h
    rw [← h]
    congr 1
    rw [show P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPP, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
  have hinUH : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b →
      PI.UpqRep.inUH (PI.UpqRep.Hpk k r) (a * b) := by
    intro a b ha hb
    unfold PI.UpqRep.inUH at *
    rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * PI.UpqRep.Hpk k r * (a * b) =
      bᴴ * (aᴴ * PI.UpqRep.Hpk k r * a) * b by simp only [Matrix.mul_assoc], ha, hb]
  have hw0 : PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g => σ g w0) :=
    low_smooth_of_k_finite hK k r ε lam H σ w0 hl ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ hw
  have htr : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    intro g hg
    have hgH : PI.UpqRep.inUH (PI.UpqRep.Hpk k r) g := hg
    have hcd : ContDiff ℝ ∞ (fun x : Mx k r => x * g) :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)).contDiff
    show PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g' => σ g' (σ g w0))
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFeq⟩ := hw0 (g₀ * g) (hinUH _ _ hg₀ hgH)
    refine ⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g), hU.preimage hcd.continuous, hgU,
      hF.comp hcd.contDiffOn (fun x hx => hx), ?_⟩
    intro x hx hxH
    have hx' := hFeq (x * g) hx (hinUH _ _ hxH hgH)
    simp only at hx'
    show σ x (σ g w0) = F (x * g)
    rw [← hx', hmul x g hxH hgH]
    rfl
  intro x hx
  unfold DDsp at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    exact htr g hg
  | zero => exact smooth_zero σ
  | add y z _ _ hy hz => exact smooth_add hy hz
  | smul a y _ hy => exact smooth_smul a hy

end Smooth

end Formalism.FourierDecayAlt.P.DDSmoothness
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3

theorem succAbove_val {n : ℕ} (p : Fin (n + 1)) (l : Fin n) :
    (p.succAbove l).val = if l.val < p.val then l.val else l.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def] <;> omega

private theorem sgnW_succ' (s : ℕ) : sgnW (s + 1) = (-1) ^ s * sgnW s := by
  unfold sgnW
  rw [← pow_add]
  congr 1
  cases s with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

theorem zb_det (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) :
    (Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val).det = h.det * t ^ s * sgnW s := by
  induction s with
  | zero =>
    have hs : sgnW 0 = 1 := by simp [sgnW]
    rw [hs, pow_zero, mul_one, mul_one]
    show Matrix.det (Matrix.of fun a b : Fin i0 => Zb i0 0 h t a.val b.val) = _
    congr 1
    ext a b
    simp [Zb, a.isLt, b.isLt]
  | succ s ih =>
    rw [Matrix.det_succ_row _ (⟨i0, by omega⟩ : Fin (i0 + s + 1)), Finset.sum_eq_single (Fin.last _)]
    · have hsub : (Matrix.of fun a b : Fin (i0 + (s + 1)) => Zb i0 (s + 1) h t a.val b.val).submatrix
          (⟨i0, by omega⟩ : Fin (i0 + s + 1)).succAbove (Fin.last (i0 + s)).succAbove =
          Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, succAbove_val, Fin.succAbove_last,
          Fin.coe_castSucc]
        have hb := b.isLt
        by_cases ha : (a : ℕ) < i0
        · simp only [ha, if_true]
          unfold Zb
          split_ifs <;> first | rfl | omega
        · simp only [ha, if_false]
          unfold Zb
          split_ifs <;> first | rfl | omega
      rw [hsub, ih, sgnW_succ']
      have he : Zb i0 (s + 1) h t i0 (i0 + s) = t := by
        simp only [Zb]
        rw [dite_eq_right (lt_irrefl _), if_pos (by omega)]
      simp only [Matrix.of_apply, Fin.val_last]
      rw [he]
      rw [show i0 + (i0 + s) = 2 * i0 + s by ring, pow_add, pow_mul]
      norm_num
      ring
    · intro j _ hj
      have hj' : (j : ℕ) ≠ i0 + s := fun e => hj (Fin.ext (by simp [e]))
      have he : Zb i0 (s + 1) h t i0 j = 0 := by
        have := j.isLt
        simp only [Zb]
        rw [dite_eq_right (lt_irrefl _), if_neg (by omega)]
      simp only [Matrix.of_apply]
      rw [he, mul_zero, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

theorem derivative_leading_zb : DleadZb := by
  intro i0 s h t
  refine ⟨?_, zb_det i0 s h t⟩
  unfold Dlead
  congr 1
  ext a b
  simp [Zb, a.isLt, b.isLt]

theorem minors_first_case : MinorsFirstCase := by
  intro i0 s' h t c
  by_cases hc : c.val = i0
  · rw [if_pos hc, ← zb_det i0 s' h t]
    congr 1
    ext a l
    simp only [Matrix.of_apply, succAbove_val, hc]
    have hl := l.isLt
    by_cases hl0 : (l : ℕ) < i0
    · simp only [hl0, if_true]
      unfold Zb
      split_ifs <;> first | rfl | omega
    · simp only [hl0, if_false]
      unfold Zb
      split_ifs <;> first | rfl | omega
  · rw [if_neg hc]
    have hne : (⟨i0, by omega⟩ : Fin (i0 + s' + 1)) ≠ c := fun e => hc (by rw [← e])
    obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hne
    apply Matrix.det_eq_zero_of_column_eq_zero l0
    intro a
    simp only [Matrix.of_apply, hl0]
    have ha := a.isLt
    unfold Zb
    split_ifs <;> first | rfl | omega

theorem third_polynomial_expansion : MinorsThirdCase := by
  intro i0 s'' h t
  rw [← zb_det i0 s'' h t]
  congr 1
  ext a b
  simp only [Matrix.of_apply, succAbove_val]
  have ha := a.isLt
  have hb := b.isLt
  by_cases ha0 : (a : ℕ) < i0 <;> by_cases hb0 : (b : ℕ) < i0 <;>
    simp only [ha0, hb0, if_true, if_false] <;>
    unfold Zb <;> split_ifs <;> first | rfl | omega

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopDensNonnegOfKappa
section
open Matrix MeasureTheory
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

namespace WordTransvectionCongruences

section Frames

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem ofWord_x_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st' w).x = (Fr.ofWord L st w).x := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hx]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hx]

theorem ofWord_q_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hq : st'.q = st.q) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st' w).q = (Fr.ofWord L st w).q := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hq]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hq]

theorem ofWord_xi_congr (L : R.LevelData A r) (st st' : Fr.Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : st'.xi Y = st.xi Y) : (Fr.ofWord L st' w).xi Y = (Fr.ofWord L st w).xi Y := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hY]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hY]

theorem ofWord_N (L : R.LevelData A r) (st : Fr.Start A) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st w).N = w.length := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih]

theorem ofWord_c_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (hq : st'.q = st.q)
    (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1)) :
    (Fr.ofWord L st' w).c = (Fr.ofWord L st w).c := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hx, hq]
  | cons l w ih =>
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have hl := hw l List.mem_cons_self
    have hxw := ofWord_x_congr L st st' hx w
    have hqw := ofWord_q_congr L st st' hq w
    have hxi1 := ofWord_xi_congr L st st' w (l.pt + 1) hl.1
    have hxi2 := ofWord_xi_congr L st st' w (l.pt - 1) hl.2
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih', hxw, hqw, hxi1, hxi2]

end Frames

section Act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_diagonal (D : Ix S → Pr (RadSp k r z z' π π')) (x : Ix S → RadSp k r z z' π π') (a : Ix S) :
    act (Matrix.diagonal D) x a = (D a).1 (x a) := by
  unfold act
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.diagonal_apply_eq]
  · intro b _ hb
    simp only [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    first
      | rfl
      | simp [Pr]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem pow_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (n : ℕ) (Φ : RadSp k r z z' π π') (p : (Fin r → ℂ) × Mx k r)
    (hp : p ∈ DomR k r z z') :
    ((((L.ζ * L.ζb * L.GGi) ^ n).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 =
      (fnVal k r z z' 0 p.2 * fnVal k r z z' 2 p.2 * fnVal k r z z' 5 p.2) ^ n •
        (Φ : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 := by
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, hgi, -⟩ := hAL
  induction n generalizing Φ with
  | zero => simp only [pow_zero, one_smul]; rfl
  | succ n ih =>
    rw [pow_succ, pr_fst_mul, Module.End.mul_apply, ih, pr_fst_mul, pr_fst_mul, Module.End.mul_apply,
      Module.End.mul_apply, hz, hzb, hgi]
    simp only [mkP]
    rw [X.fn_apply 0 _ p hp, X.fn_apply 2 _ p hp, X.fn_apply 5 _ p hp, smul_smul, smul_smul, smul_smul, pow_succ]
    ring_nf

end Act

theorem hsInner_zero_left {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (V : Wq →L[ℂ] Wp) : B.hsInner 0 V = 0 := by
  unfold B.hsInner
  have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
    unfold B.hsVec
    ext i
    simp
  rw [h0, inner_zero_right]

end WordTransvectionCongruences

open WordTransvectionCongruences in
theorem topDensNonnegOfKappa : TopDensNonnegOfKappa := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 K hD hl1 hlk hK
  obtain ⟨κ, hκx, hκxi, hκpos⟩ := hK
  obtain ⟨hPl, -, hAL, -, hq, -, -, -⟩ := hD
  intro w hw x _ c _ g

  let st' : Fr.Start (Pr (RadSp P.k P.r z z' π π')) :=
    { st with xi := fun Y => κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ }
  have hCD := (Formalism.FourierDecayAlt.P.c_diagonal (Pr (RadSp P.k P.r z z' π π')) S P.r L st' (M.Ty P) κ
    (fun ρ Y => M.x0 P l0 ρ Y) hκx (fun Y => rfl) w).2.2
  have hc : (Fr.ofWord L st w).c = Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    rw [← ofWord_c_congr L st st' rfl rfl w, hCD]
    · rw [← hq]
    · intro l hl
      have h := hw.1.2.2.1 l hl
      exact ⟨(hκxi _ h.2.1).symm, (hκxi _ h.2.2.1).symm⟩

  have hpos : ∀ (e : Ix S) (ρ : M.Ty P), 0 < Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    intro e ρ
    have h := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
      Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true S P.k P.u P.u' (M.rho P ρ) l0 P.T P.T' w hl1 hlk
      (Formalism.FourierDecayAlt.P.types_interlace P hPl.1 ρ) hPl.1.T_pos hPl.1.T'_pos hw.2.1 hw.2.2 e
    rw [Complex.lt_def]
    exact ⟨h.1, h.2.symm⟩
  unfold topDens
  refine Finset.sum_nonneg fun e _ => ?_
  have hd : (Fr.ofWord L st w).d L = io ((L.ζ * L.ζb * L.GGi) ^ (Fr.ofWord L st w).N) *
      Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    rw [Fr.FrameData.d, hc, Fr.wt, io, io, map_pow]
  rw [act_mul, hd, act_mul, act_io, act_diagonal]
  set Φ := act (Fr.ofWord L st w).F x e
  by_cases hp : (c, g) ∈ DomR P.k P.r z z'
  · have := pow_apply X L hAL (Fr.ofWord L st w).N ((κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e).1 Φ) (c, g) hp
    simp only at this
    rw [this, hsInner_smul_left]
    refine mul_nonneg ?_ (hκpos _ (hpos e) Φ c g)
    obtain ⟨-, -, hGG⟩ := hp
    have hre : fnVal P.k P.r z z' 0 g * fnVal P.k P.r z z' 2 g * fnVal P.k P.r z z' 5 g =
        ((Complex.normSq (zetaL P.k P.r z z' (Fin.last P.r) g) * (GGl P.k P.r z z' g)⁻¹ : ℝ) : ℂ) := by
      simp only [fnVal, Complex.ofReal_mul, Complex.ofReal_inv, ← Complex.mul_conj]
      rfl
    rw [hre, ← Complex.ofReal_pow]
    exact Complex.zero_le_real.mpr (pow_nonneg (mul_nonneg (Complex.normSq_nonneg _) (inv_nonneg.mpr hGG.le)) _)
  · have h0 := ((((L.ζ * L.ζb * L.GGi) ^ (Fr.ofWord L st w).N).1
      ((κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e).1 Φ)).2).1 (c, g) hp
    simp only at h0
    rw [h0, hsInner_zero_left]

end Formalism.FourierDecayAlt.P5
end
end

