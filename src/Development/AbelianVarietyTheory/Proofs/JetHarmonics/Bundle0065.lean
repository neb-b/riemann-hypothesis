module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormEntriesCommutatorMultiplier
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
open scoped ContDiff

theorem mulT_ld_contDiff {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u))) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv q hφ

theorem mulT_normSq_contDiff : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  have : (fun w : ℂ => Complex.normSq w) = fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
    funext w; simp [Complex.normSq_apply]
  rw [this]
  fun_prop

theorem mulT_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ContDiffOn ℝ ∞ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ))
      {w : ℂ | T < Complex.normSq w} := by
  have h1 : ContDiffOn ℝ ∞ (fun w : ℂ => Real.log (a * (Complex.normSq w - T)))
      {w : ℂ | T < Complex.normSq w} := by
    refine ContDiffOn.log (contDiff_const.mul (mulT_normSq_contDiff.sub contDiff_const)).contDiffOn ?_
    intro w hw
    exact (mul_pos ha (sub_pos.2 hw)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((mulT_ld_contDiff hφ q).comp_contDiffOn h1)

theorem mulT_fderiv {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) {w : ℂ}
    (hw : T < Complex.normSq w) (v : ℂ) :
    fderiv ℝ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w v =
      ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) * (Complex.normSq w - T)⁻¹ *
        (2 * (w.re * v.re + w.im * v.im)) : ℝ) : ℂ) := by
  have hp : 0 < Complex.normSq w - T := sub_pos.2 hw
  have hn : HasFDerivAt (fun w : ℂ => Complex.normSq w)
      ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM) w := by
    have : (fun w : ℂ => Complex.normSq w) =
        fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
      funext w; simp [Complex.normSq_apply]
    rw [this]
    have h1 := Complex.reCLM.hasFDerivAt (x := w)
    have h2 := Complex.imCLM.hasFDerivAt (x := w)
    refine ((h1.mul h1).add (h2.mul h2)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp
    ring
  have h1 := ((hn.sub_const T).const_mul a).log (mul_pos ha hp).ne'
  have h2 : HasDerivAt (iteratedDeriv q (fun u : ℝ => φ (Real.exp u)))
      (LE.ld (q + 1) φ (a * (Complex.normSq w - T))) (Real.log (a * (Complex.normSq w - T))) := by
    unfold LE.ld
    rw [iteratedDeriv_succ]
    exact (((mulT_ld_contDiff hφ q).differentiable (by simp)) _).hasDerivAt
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp w (h2.comp_hasFDerivAt w h1)
  have h4 : fderiv ℝ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w = _ := h3.fderiv
  rw [h4]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_apply,
    add_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  congr 1
  field_simp

theorem mulT_dZ {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) {w : ℂ}
    (hw : T < Complex.normSq w) :
    NF.dZ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w =
      star w * ((((Complex.normSq w - T : ℝ) : ℂ))⁻¹ *
        ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) ∧
    NF.dZb (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w =
      w * ((((Complex.normSq w - T : ℝ) : ℂ))⁻¹ *
        ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) := by
  unfold NF.dZ NF.dZb
  rw [mulT_fderiv hφ q ha T hw, mulT_fderiv hφ q ha T hw, ← Complex.ofReal_inv]
  generalize LE.ld (q + 1) φ (a * (Complex.normSq w - T)) = b
  generalize (Complex.normSq w - T)⁻¹ = e
  constructor <;> apply Complex.ext <;> simp <;> ring


open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx4 in
theorem t_mul_mulG (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hφ : LE.SmoothLog φ)
    (hW : IsMulG P Bs φ W) (q : ℕ) (Y : ℂ) :
    X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧
      X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧
      X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 := by
  have hU := isOpen_normSq_gt (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')
  have hDU := Dp_maps (k := P.k) (r := P.r) Bs.z Bs.z'
  have hD := Qx5.Dp_open P.k P.r Bs.z Bs.z'
  have ha : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', 0 < Complex.normSq (∏ a, x.1 a) := fun x hx =>
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)
  have key := fun (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r)
      (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') =>
    zeta_smooth_level Bs.z Bs.z' hD hU hDU (mulT_contDiffOn hφ q (ha x hx) _) (Qx5.slice_smooth Φ.2 hx.1)
      ⟨hx.2.1, hx.2.2⟩ Y
  have hd := fun (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') =>
    mulT_dZ hφ q (ha x hx) _ (hDU x.2 hx.2.2)
  have hWa : ∀ (p : ℕ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      (W p Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        ((LE.ld p φ (Complex.normSq (∏ a, c a) * (Complex.normSq (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g) -
          Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')) : ℝ) : ℂ) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g :=
    fun p Φ c g => hW p Φ c g
  have ht : ∀ (a b : Fin 2) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r),
      x ∈ Q.DomR P.k P.r Bs.z Bs.z' → (X.t Y a b (W q Φ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (fun y =>
          ((LE.ld q φ (Complex.normSq (∏ a, x.1 a) * (Complex.normSq (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) y) -
            Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')) : ℝ) : ℂ) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y) x.2 := by
    intro a b Φ x hx
    rw [X.t_apply Y a b _ x hx]
    congr 1
    funext y
    exact hWa q Φ x.1 y
  refine ⟨end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_⟩
  · rw [Module.End.mul_apply, ht 1 0 Φ x hx, (key Φ x hx).1, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply,
      Pi.sub_apply, X.fn_apply 2 _ x hx, X.fn_apply 5 _ x hx, hWa, hWa,
      X.t_apply Y 1 0 Φ x hx, X.t_apply Y 1 1 Φ x hx, (hd x hx).1, smul_smul, smul_smul, mul_assoc]
    rfl
  · rw [Module.End.mul_apply, ht 1 1 Φ x hx, (key Φ x hx).2.1, Module.End.mul_apply, hWa,
      X.t_apply Y 1 1 Φ x hx]
  · rw [Module.End.mul_apply, ht 0 1 Φ x hx, (key Φ x hx).2.2, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, X.fn_apply 0 _ x hx, X.fn_apply 5 _ x hx, hWa, hWa,
      X.t_apply Y 0 1 Φ x hx, X.t_apply Y 1 1 Φ x hx, (hd x hx).2, smul_smul, smul_smul, mul_assoc]
    rfl

theorem nf_t_mul_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (q : ℕ) (Y : ℂ), X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧ X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧ X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 :=
  fun Wp Wq _ _ _ _ _ _ P Bs X _ _ _ _ _ _ _ φ W hφ hW q Y => t_mul_mulG Wp Wq P Bs X φ W hφ hW q Y

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumOfStdHyp
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory.BpStdNum

theorem gapOK_of (k r : ℕ) (hk : 1 ≤ k) (h : ℝ)
    (hh : 10 ^ 6 * (((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ≤ h) :
    ThreeDimData.GapOK k r (h / 4) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = 2 * ((r : ℝ) + 1) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = 2 * (r : ℝ) + k + 1 := ⟨_, rfl⟩
  have em : ((2 * r + 2 : ℕ) : ℝ) = m := by rw [hm]; push_cast; ring
  have en : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  have hm1 : 1 ≤ m := by linarith
  have hmn : m ≤ n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hs1 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm1
  have e9 : m ^ ((9 : ℝ) / 2) = m ^ 4 * Real.sqrt m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    norm_num
  rw [em, en, e9] at hh
  have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
  have hm4 : 1 ≤ m ^ 4 := one_le_pow₀ hm1
  have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ hn1
  have ha : 1000 * (m ^ 4 * n ^ 3) ≤ ThreeDimData.aOf r (h / 4) := by
    unfold ThreeDimData.aOf
    rw [← hm, le_div_iff₀ (by positivity)]
    have : 0 ≤ m ^ 4 * Real.sqrt m * n ^ 3 := by positivity
    nlinarith
  have hM : ThreeDimData.Mexp r ≤ m ^ 2 := by unfold ThreeDimData.Mexp; rw [hm]; nlinarith
  have hM0 : 0 ≤ ThreeDimData.Mexp r := by unfold ThreeDimData.Mexp; positivity
  have hG : ThreeDimData.AG k r ≤ 4 * n ^ 2 := by unfold ThreeDimData.AG; rw [hn]; nlinarith
  have hG0 : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hd : ThreeDimData.dN k r ≤ n ^ 2 := by unfold ThreeDimData.dN; rw [hn]; nlinarith
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have hm24 : m ^ 2 ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hS : ThreeDimData.AS k r ≤ n ^ 3 := by
    unfold ThreeDimData.AS
    have h1 : ((2 * r + k : ℕ) : ℝ) ≤ n := by rw [hn]; push_cast; linarith
    calc ((2 * r + k : ℕ) : ℝ) * ThreeDimData.dN k r ≤ ((2 * r + k : ℕ) : ℝ) * n ^ 2 :=
          mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
      _ ≤ n * n ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = n ^ 3 := by ring
  have hX : n ^ 3 ≤ m ^ 4 * n ^ 3 := le_mul_of_one_le_left (by positivity) hm4
  refine ⟨hk, ?_, ?_, ?_⟩
  · rw [en]
    have : m ^ 4 * n ^ 3 ≤ m ^ 4 * Real.sqrt m * n ^ 3 := by
      have := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ m ^ 4 * n ^ 3 by positivity)
      linarith
    linarith
  · have h1 : ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤ m ^ 4 * (5 * n ^ 3) :=
      calc _ ≤ ThreeDimData.Mexp r * (5 * n ^ 3) := mul_le_mul_of_nonneg_left (by linarith) hM0
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  · rw [en]
    have h1 : ((r : ℝ) + 1) * n ^ 2 ≤ n * n ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : n * n ^ 2 = n ^ 3 := by ring
    linarith

section
variable {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ}

theorem lt_left (hk : 1 ≤ k)
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : a.val < k) : lam a < u (a.val + 1) := by
  by_cases h : a.val + 1 < k
  · exact (hI.1 a.val h).1
  · have h2 := hI.2 (by omega)
    have e : a = ⟨k - 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e]; exact h2

theorem lt_right
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < k) : u (a.val + 2) < lam a :=
  (hI.1 a.val ha).2

theorem cloud_of
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < k) :
    IsCloud (fun i : Fin k => u (i.val + 1)) lam a :=
  ⟨⟨⟨a.val, by omega⟩, (hI.1 a.val ha).1⟩, ⟨⟨a.val + 1, ha⟩, (hI.1 a.val ha).2⟩⟩

theorem not_cloud_of (hk : 1 ≤ k) (hA : StrictAnti lam)
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : k ≤ a.val + 1) :
    ¬ IsCloud (fun i : Fin k => u (i.val + 1)) lam a := by
  rintro ⟨-, i, hi⟩
  have hik := i.isLt
  have key : ∀ j : ℕ, j < k → lam a < u (k - 1 - j + 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      have h1 := lt_left hk hI ⟨k - 1, by omega⟩ (by simp only; omega)
      have h2 : lam a ≤ lam ⟨k - 1, by omega⟩ := hA.antitone (by
        rw [Fin.le_def]; simp only; omega)
      simp only [Nat.sub_zero] at h1 ⊢
      linarith
    | succ j ih =>
      intro hj
      have h0 := ih (by omega)
      have h1 := hI.1 (k - 1 - (j + 1)) (by omega)
      simp only at h1
      have e : k - 1 - (j + 1) + 1 = k - 1 - j := by omega
      have h4 : u (k - 1 - (j + 1) + 1 + 1) < u (k - 1 - (j + 1) + 1) := lt_trans h1.2 h1.1
      rw [e] at h4 ⊢
      linarith
  have h3 := key (k - 1 - i.val) (by omega)
  have e : k - 1 - (k - 1 - i.val) = i.val := by omega
  rw [e] at h3
  simp only at hi
  linarith

theorem half_of (hH : Formalism.QuantumDeterminants.IsHCParam lam)
    (hu : ∀ i ∈ Finset.Icc 1 k, ∃ a : ℤ, u i = (a : ℝ) + ((k : ℝ) - 1) / 2) :
    ∀ a, ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ, lam a - u i = (m : ℝ) + 1 / 2 := by
  intro a i hi
  obtain ⟨x, hx⟩ := hH.2 a
  obtain ⟨y, hy⟩ := hu i hi
  refine ⟨x - y + r, ?_⟩
  push_cast at hx ⊢
  linarith

theorem bound_of {b : ℝ} (hb : ∀ i : Fin k, |u (i.val + 1)| ≤ b) : ∀ i ∈ Finset.Icc 1 k, |u i| ≤ b := by
  intro i hi
  rw [Finset.mem_Icc] at hi
  have := hb ⟨i - 1, by omega⟩
  simp only at this
  rwa [Nat.sub_add_cancel hi.1] at this

end

theorem num_of_stdHyp : ∀ Cq : ℝ, 0 ≤ Cq → ∃ Cg₀ : ℝ, ∀ (Ch Cg : ℝ), Cg₀ ≤ Cg → ∀ (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (T T' ka b d : ℝ) (q0 : ℕ), 2 ≤ P.k → StdHyp Ch Cg P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) lam (fun i => P.u (i.val + 1)) (fun i => P.u' (i.val + 1)) T T' ka b → (∀ i ∈ Finset.Icc 1 P.k, (∃ a : ℤ, P.u i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) ∧ ∃ a : ℤ, P.u' i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) → 0 ≤ d → AllGaps lam (200 * d) → (q0 : ℝ) ≤ d + Cq * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 → ∃ bv ga h : ℝ, BranchingSupport.Num P.k P.r lam P.u b bv ga h q0 ∧ BranchingSupport.Num P.k P.r lam P.u' b bv ga h q0 ∧ Cg * (((2 * P.r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (P.r + 1) : ℕ) : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 3)) ≤ h := by
  intro Cq hCq
  refine ⟨10 ^ 6 + 200 * Cq, ?_⟩
  intro Ch Cg hCg P lam T T' ka b d q0 hk hS hint hd hgd hq
  obtain ⟨hH, hI, hI', -, -, -, -, -, -, -, hbl, hbu, hbu', hga, hgap, ⟨bv, hbv, hsh⟩, -⟩ := hS
  have hk1 : 1 ≤ P.k := by omega
  have hCg6 : (10 : ℝ) ^ 6 ≤ Cg := by linarith
  rw [mul_assoc] at hgap
  set h0 : ℝ := Cg * (((2 * P.r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (P.r + 1) : ℕ) : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 3)) with hh0
  set ga : ℝ := max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) (200 * d) with hgadef
  have hall : AllGaps lam ga := fun s s' hs => max_le (hga s s' hs) (hgd s s' hs)
  have hm3 : (1 : ℝ) ≤ ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * P.r + 2))
  have hq' : 100 * ((q0 : ℝ) + 1) ≤ ga := by
    have h1 : Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 ≤ ga := le_max_left _ _
    have h2 : 200 * d ≤ ga := le_max_right _ _
    have h3 := mul_le_mul_of_nonneg_right hCg (le_trans zero_le_one hm3)
    nlinarith
  have hgap' : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) lam (max h0 ga) := by
    intro a c hac
    exact max_le (hgap a c hac) (hall a c (fun e => hac (by rw [e])))
  have hok : ThreeDimData.GapOK P.k P.r (max h0 ga / 4) := by
    apply gapOK_of _ _ hk1
    refine le_trans ?_ (le_max_left _ _)
    rw [hh0]
    apply mul_le_mul hCg6 _ (by positivity) (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_left (by positivity)
  have hcl : ∀ a c : Fin (2 * P.r + P.k + 1), a < c → c.val + 1 < P.k → ga ≤ lam a - lam c := by
    intro a c hac _
    have := hall a c hac.ne
    rwa [abs_of_pos (sub_pos.mpr (hH.1 hac))] at this
  have hbv' : 10 ^ 6 * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 7 ≤ bv :=
    le_trans (mul_le_mul_of_nonneg_right hCg6 (by positivity)) hbv
  have hs1 : ∀ a : Fin (2 * P.r + P.k + 1), a.val + 1 < P.k → 0 ≤ lam a ∧ lam a ≤ bv / 8 :=
    fun a ha => (hsh a).1 (cloud_of hI a ha)
  have hs2 : ∀ a : Fin (2 * P.r + P.k + 1), P.k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv :=
    fun a ha => (hsh a).2 (not_cloud_of hk1 hH.1 hI a ha)
  refine ⟨bv, ga, max h0 ga, ?_, ?_, le_max_left _ _⟩
  · exact ⟨hk1, hH, half_of hH (fun i hi => (hint i hi).1), lt_left hk1 hI, lt_right hI, hs1, hs2, hbl,
      bound_of hbu, hcl, hgap', hok, hq', le_trans hq' (le_max_right _ _), hbv'⟩
  · exact ⟨hk1, hH, half_of hH (fun i hi => (hint i hi).2), lt_left hk1 hI', lt_right hI', hs1, hs2, hbl,
      bound_of hbu', hcl, hgap', hok, hq', le_trans hq' (le_max_right _ _), hbv'⟩

end GlobalTheory.BpStdNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsTaylorCoeffLeibnizRule
section
namespace GlobalTheory.HatTaylorPlus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Polynomial

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def ev (f : ℕ → A) (P : A[X]) : A := P.sum fun j a => f j * a

omit [Algebra ℂ A] in
theorem ev_add (f : ℕ → A) (P Q : A[X]) : ev f (P + Q) = ev f P + ev f Q :=
  Polynomial.sum_add_index _ _ _ (by simp) (by simp [mul_add])

omit [Algebra ℂ A] in
theorem ev_monomial (f : ℕ → A) (n : ℕ) (a : A) : ev f (monomial n a) = f n * a :=
  Polynomial.sum_monomial_index _ _ (by simp)

omit [Algebra ℂ A] in
theorem ev_mul (f g : ℕ → A) (P Q : A[X]) (z : A) (h : ∀ j, z * g j = ev (fun i => f (j + i)) P) :
    z * ev g Q = ev f (P * Q) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [ev_add, mul_add, mul_add, ev_add, hp, hq]
  | monomial n b =>
    rw [ev_monomial, ← mul_assoc, h]
    clear h
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [ev_add, add_mul, add_mul, ev_add, hp, hq]
    | monomial k a => rw [monomial_mul_monomial, ev_monomial, ev_monomial, mul_assoc, add_comm]

omit [Algebra ℂ A] in
theorem ev_eq_sum (f : ℕ → A) (P : A[X]) (n : ℕ) (h : P.natDegree < n) :
    ev f P = ∑ j ∈ Finset.range n, f j * P.coeff j :=
  Polynomial.sum_over_range' _ (by simp) n h

omit [Algebra ℂ A] in
theorem mul_ev (z : A) (f : ℕ → A) (P : A[X]) : z * ev f P = ev (fun i => z * f i) P := by
  simp [ev, Polynomial.sum, Finset.mul_sum, mul_assoc]

def Deg (L : LevelData A r) (Y : ℂ) (D : ℕ) (Z : ℂ → A) : Prop :=
  ∃ P : A[X], P.natDegree ≤ D ∧ (∀ s : ℂ, Z (Y + s) = ev (fun j => algebraMap ℂ A (s ^ j)) P) ∧
    ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ev (fun j => m (q + j)) P

variable {L : LevelData A r} {Y : ℂ}

theorem Deg.mono {D E : ℕ} {Z : ℂ → A} (h : Deg L Y D Z) (hDE : D ≤ E) : Deg L Y E Z := by
  obtain ⟨P, h1, h2⟩ := h
  exact ⟨P, h1.trans hDE, h2⟩

theorem Deg.add {D : ℕ} {Z W : ℂ → A} (h : Deg L Y D Z) (h' : Deg L Y D W) :
    Deg L Y D (fun y => Z y + W y) := by
  obtain ⟨P, h1, h2, h3⟩ := h
  obtain ⟨Q, k1, k2, k3⟩ := h'
  refine ⟨P + Q, (natDegree_add_le _ _).trans (max_le h1 k1), fun s => ?_, fun m hm q => ?_⟩
  · rw [ev_add, ← h2, ← k2]
  · rw [ev_add, ← h3 m hm, ← k3 m hm, add_mul]

theorem Deg.mul {D E : ℕ} {Z W : ℂ → A} (h : Deg L Y D Z) (h' : Deg L Y E W) :
    Deg L Y (D + E) (fun y => Z y * W y) := by
  obtain ⟨P, h1, h2, h3⟩ := h
  obtain ⟨Q, k1, k2, k3⟩ := h'
  refine ⟨P * Q, natDegree_mul_le.trans (add_le_add h1 k1), fun s => ?_, fun m hm q => ?_⟩
  · show Z (Y + s) * W (Y + s) = _
    rw [k2]
    refine ev_mul _ _ _ _ _ fun j => ?_
    rw [← Algebra.commutes, h2, mul_ev]
    simp only [pow_add, map_mul]
  · show Z Y * W Y * m q = _
    rw [mul_assoc, k3 m hm]
    refine ev_mul _ _ _ _ _ fun j => ?_
    rw [h3 m hm]
    simp only [add_assoc]

theorem deg_const (a : A) (ha : ∀ m : ℕ → A, MulRel L m → ∀ q, a * m q = m q * a) :
    Deg L Y 0 (fun _ => a) := by
  refine ⟨monomial 0 a, natDegree_monomial_le _, fun s => ?_, fun m hm q => ?_⟩
  · rw [ev_monomial]; simp
  · rw [ev_monomial, ha m hm]; rfl

theorem deg_fn {a : A} (ha : a ∈ L.fns) : Deg L Y 0 (fun _ => a) :=
  deg_const a fun _ hm q => ((hm q).1 a ha).eq

theorem deg_lin (Z : ℂ → A) (b : A) (h1 : ∀ s, Z (Y + s) = Z Y + algebraMap ℂ A s * b)
    (h2 : ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = m q * Z Y + m (q + 1) * b) : Deg L Y 1 Z := by
  refine ⟨monomial 0 (Z Y) + monomial 1 b, (natDegree_add_le _ _).trans
    (max_le ((natDegree_monomial_le _).trans zero_le_one) (natDegree_monomial_le _)), fun s => ?_,
    fun m hm q => ?_⟩
  · rw [ev_add, ev_monomial, ev_monomial, h1]; simp
  · rw [ev_add, ev_monomial, ev_monomial, h2 m hm]; rfl

theorem deg_list (l : List A) (hl : ∀ a ∈ l, a ∈ L.fns) : Deg L Y 0 (fun _ => l.prod) := by
  induction l with
  | nil => exact deg_const _ (by simp)
  | cons a l ih =>
    simpa using (deg_fn (hl a (by simp))).mul (ih fun b hb => hl b (by simp [hb]))

theorem deg_Tl (l : Fin r) (i j : Fin 2) : Deg L Y 1 (fun y => L.Tl y l i j) := by
  have hc : L.c l ∈ L.fns := by simp [LevelData.fns]
  have hci : L.ci l ∈ L.fns := by simp [LevelData.fns]
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl]
  · refine deg_lin _ 1 (fun s => ?_) fun m hm q => ?_
    · simp [add_right_comm]
    · simp [add_mul, mul_add, (hm q).2.1 l, Algebra.commutes, add_assoc]
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    exact ((hm q).1 _ hc).neg_left.eq
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    simpa using ((hm q).1 _ hci).eq
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    exact (Commute.zero_left (m q)).eq

theorem deg_prod (l : List (Fin r)) (i j : Fin 2) :
    Deg L Y l.length (fun y => (l.map (L.Tl y)).prod i j) := by
  induction l generalizing i j with
  | nil =>
    refine deg_const ((1 : Matrix (Fin 2) (Fin 2) A) i j) fun m _ q => ?_
    rw [Matrix.one_apply]; split_ifs <;> simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]
    rw [add_comm l.length 1]
    exact ((deg_Tl a i 0).mul (ih 0 j)).add ((deg_Tl a i 1).mul (ih 1 j))

theorem deg_Tprod (i j : Fin 2) : Deg L Y r (fun y => L.Tprod y i j) := by
  have h := deg_prod (L := L) (Y := Y) (List.finRange r).reverse i j
  simp only [List.length_reverse, List.length_finRange] at h
  simpa only [LevelData.Tprod, List.ofFn_eq_map, List.map_reverse] using h

theorem forwardTaylorDegree_one_leftLetter : Deg L Y 1 L.l0 := by
  refine deg_lin _ (-(L.ζb * L.GGi)) (fun s => ?_) fun m hm q => ?_
  · simp only [LevelData.l0, add_right_comm Y s, map_add (algebraMap ℂ A) (Y + 1 / 2) s]
    noncomm_ring
  · have c1 : ∀ q, Commute (L.ζb * L.GGi) (m q) := fun q =>
      ((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))
    have c2 : Commute (algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) (m q) :=
      (Algebra.commute_algebraMap_left _ _).mul_left (c1 q)
    rw [LevelData.l0, sub_mul, neg_mul, (hm q).2.2.2.1, c2.eq, (c1 (q + 1)).eq]
    noncomm_ring

theorem deg_Ahat : Deg L Y r L.Ahat := by
  have h := (deg_list (L := L) (Y := Y) (List.ofFn L.c) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    simp [LevelData.fns])).mul (deg_Tprod 0 0)
  rw [zero_add] at h
  exact h

theorem forwardTaylorDegree_plusHatR : Deg L Y (r + 1) L.R0 := by
  have h := ((deg_list (L := L) (Y := Y) (List.ofFn L.cb) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    simp [LevelData.fns])).mul (deg_fn (a := L.GG) (by simp [LevelData.fns]))).mul
    ((forwardTaylorDegree_one_leftLetter.mul (deg_Tprod 0 0)).add ((deg_Tprod 1 0).mono (Nat.le_add_left _ _)))
  rw [zero_add, zero_add, add_comm 1 r] at h
  exact h

theorem taylor_plus : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahat (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0 (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahat Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0 Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  intro A _ _ r L Y
  obtain ⟨P, h1, h2, h3⟩ := deg_Ahat (L := L) (Y := Y)
  obtain ⟨Q, k1, k2, k3⟩ := forwardTaylorDegree_plusHatR (L := L) (Y := Y)
  have hP : P.natDegree < r + 2 := by omega
  have hQ : Q.natDegree < r + 2 := by omega
  refine ⟨P.coeff, Q.coeff, fun s => ?_, fun s => ?_, fun m hm q => ⟨?_, ?_⟩⟩
  · rw [h2, ev_eq_sum _ _ _ hP]; simp only [Algebra.smul_def]
  · rw [k2, ev_eq_sum _ _ _ hQ]; simp only [Algebra.smul_def]
  · rw [h3 m hm, ev_eq_sum _ _ _ hP]
  · rw [k3 m hm, ev_eq_sum _ _ _ hQ]

end

end GlobalTheory.HatTaylorPlus
end

