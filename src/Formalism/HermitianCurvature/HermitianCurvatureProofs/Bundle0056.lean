module

public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0027

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfZeta
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

section Entries

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem zeta_entries (hZ : NF.ActualZetaSmooth) {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ}
    {π : Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} (hP : IsPlace P z z' π π')
    (X : ActualOps P.k P.r z z' π π') (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hQQ : ∀ Y, st.QQ Y = M.sgn P l0 • X.QQ Y) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g))) :
    (∀ Y, mkP Wv' Wv * st.QQ Y 1 1 * mkP Wv Wv' = st.QQ Y 1 1) ∧
    (∀ Y, mkP Wv' Wv * st.QQ Y 1 0 * mkP Wv Wv' = st.QQ Y 1 0 - st.QQ Y 1 1 * algebraMap ℂ _ s) := by

  have hmz : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (m : ℂ → ℂ),
      multiplicationOperator W (fun _ g => m (zeta P.k P.r z z' g)) → NF.IsMulZ W m := by
    intro W m hWm Φ
    obtain ⟨h0, -, -⟩ := Φ.2
    funext c g
    rw [hWm Φ c g]
    show _ = (Q.DomR P.k P.r z z').indicator
      (fun x => m (Q.zetaL P.k P.r z z' (Fin.last P.r) x.2) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) (c, g)
    by_cases hx : (c, g) ∈ Q.DomR P.k P.r z z'
    · rw [Set.indicator_of_mem hx]
      rfl
    · have hz : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 := h0 (c, g) hx
      simp [Set.indicator_apply, hx, hz]

  have hfun : (fun ζ : ℂ => fsv s ζ) =
      (fun y : ℂ => Complex.exp (s * id y - conj s * Complex.conjCLE y)) := funext fun y => rfl
  have hfun2 : (fun ζ : ℂ => Complex.exp (s * ζ - conj s * conj ζ)) =
      (fun y : ℂ => Complex.exp (s * id y - conj s * Complex.conjCLE y)) := funext fun y => rfl
  have hder : ∀ ζ : ℂ, HasFDerivAt (fun y : ℂ => Complex.exp (s * id y - conj s * Complex.conjCLE y))
      (Complex.exp (s * id ζ - conj s * Complex.conjCLE ζ) •
        (s • ContinuousLinearMap.id ℝ ℂ - conj s • (Complex.conjCLE : ℂ →L[ℝ] ℂ))) ζ := fun ζ =>
    (((hasFDerivAt_id ζ).const_mul s).sub ((Complex.conjCLE.hasFDerivAt).const_mul (conj s))).cexp
  have hv1 : ∀ ζ : ℂ, fderiv ℝ (fun y : ℂ => Complex.exp (s * y - conj s * conj y)) ζ 1 =
      Complex.exp (s * ζ - conj s * conj ζ) * (s - conj s) := by
    intro ζ
    rw [hfun2, (hder ζ).fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id',
        id_eq, Complex.conjCLE_apply, map_one, Complex.conj_I, smul_eq_mul, ContinuousLinearMap.coe_coe,
        ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I]
    ring
  have hvI : ∀ ζ : ℂ, fderiv ℝ (fun y : ℂ => Complex.exp (s * y - conj s * conj y)) ζ Complex.I =
      Complex.exp (s * ζ - conj s * conj ζ) * ((s + conj s) * Complex.I) := by
    intro ζ
    rw [hfun2, (hder ζ).fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id',
        id_eq, Complex.conjCLE_apply, map_one, Complex.conj_I, smul_eq_mul, ContinuousLinearMap.coe_coe,
        ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I]
    ring
  have hdZ : ∀ ζ, NF.dZ (fun ζ : ℂ => fsv s ζ) ζ = s * fsv s ζ := by
    intro ζ
    unfold NF.dZ fsv
    rw [hv1, hvI]
    linear_combination (-(1 / 2 : ℂ) * Complex.exp (s * ζ - conj s * conj ζ) * (s + conj s)) * Complex.I_sq
  have hdZb : ∀ ζ, NF.dZb (fun ζ : ℂ => fsv s ζ) ζ = -conj s * fsv s ζ := by
    intro ζ
    unfold NF.dZb fsv
    rw [hv1, hvI]
    linear_combination ((1 / 2 : ℂ) * Complex.exp (s * ζ - conj s * conj ζ) * (s + conj s)) * Complex.I_sq
  have hsm : ∀ (c : ℂ) (m : ℂ → ℂ), (∀ ζ, m ζ = c * fsv s ζ) →
      multiplicationOperator (c • Wv) (fun _ g => m (zeta P.k P.r z z' g)) := by
    intro c m hm Φ c' g
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hW Φ c' g, smul_smul, hm]
  have hA : ∀ Y, X.t Y 1 0 * Wv = Wv * X.t Y 1 0 - (s • Wv) * X.t Y 1 1 ∧
      X.t Y 1 1 * Wv = Wv * X.t Y 1 1 ∧
      X.t Y 0 1 * Wv = Wv * X.t Y 0 1 + ((-conj s) • Wv) * X.t Y 1 1 := fun Y =>
    hZ Wp Wq P z z' π π' hP X (fun ζ => fsv s ζ)
      (by rw [hfun]; exact ((((contDiff_const.mul contDiff_id).sub
        (contDiff_const.mul Complex.conjCLE.contDiff)).cexp).contDiffOn)) Wv (s • Wv) ((-conj s) • Wv)
      (hmz Wv (fun ζ => fsv s ζ) hW) (hmz _ _ (hsm s _ hdZ)) (hmz _ _ (hsm (-conj s) _ hdZb)) Y

  have hWW : Wv' * Wv = 1 := by
    apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    show ((Wv' (Wv Φ) : RadSp P.k P.r z z' π π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    funext c g
    rw [hW' (Wv Φ) c g, hW Φ c g, smul_smul]
    have h1 : fsv (-s) (zeta P.k P.r z z' g) * fsv s (zeta P.k P.r z z' g) = 1 := by
      unfold fsv
      rw [← Complex.exp_add]
      convert Complex.exp_zero using 2
      rw [map_neg]
      ring
    rw [h1, one_smul]
  have hcore : ∀ A B : Module.End ℂ (RadSp P.k P.r z z' π π'),
      mkP Wv' Wv * mkP A B * mkP Wv Wv' = mkP (Wv' * A * Wv) (Wv' * B * Wv) := by
    intro A B
    refine pr_ext rfl ?_
    change Wv' * (B * Wv) = Wv' * B * Wv
    exact (mul_assoc _ _ _).symm
  have e11 : ∀ Y, Wv' * X.t Y 1 1 * Wv = X.t Y 1 1 := by
    intro Y
    rw [mul_assoc, (hA Y).2.1, ← mul_assoc, hWW, one_mul]
  have e10 : ∀ Y, Wv' * X.t Y 1 0 * Wv = X.t Y 1 0 - s • X.t Y 1 1 := by
    intro Y
    rw [mul_assoc, (hA Y).1, mul_sub, ← mul_assoc, hWW, one_mul, smul_mul_assoc, mul_smul_comm,
      ← mul_assoc, hWW, one_mul]
  have e01 : ∀ Y, Wv' * X.t Y 0 1 * Wv = X.t Y 0 1 + (-conj s) • X.t Y 1 1 := by
    intro Y
    rw [mul_assoc, (hA Y).2.2, mul_add, ← mul_assoc, hWW, one_mul, smul_mul_assoc, mul_smul_comm,
      ← mul_assoc, hWW, one_mul]
  refine ⟨fun Y => ?_, fun Y => ?_⟩
  · rw [hQQ Y, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc]
    congr 1
    simp only [ActualOps.QQ, Matrix.of_apply]
    rw [hcore, e11 Y, e11 (star Y)]
  · rw [hQQ Y, Matrix.smul_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, ← smul_sub]
    congr 1
    simp only [ActualOps.QQ, Matrix.of_apply]
    rw [hcore, e10 Y, e01 (star Y)]
    apply pr_ext
    · change X.t Y 1 0 - s • X.t Y 1 1 = X.t Y 1 0 - X.t Y 1 1 * algebraMap ℂ _ s
      rw [← Algebra.commutes, ← Algebra.smul_def]
    · change X.t (star Y) 0 1 + (-conj s) • X.t (star Y) 1 1 =
        X.t (star Y) 0 1 - algebraMap ℂ _ (conj s) * X.t (star Y) 1 1
      rw [← Algebra.smul_def, neg_smul, sub_eq_add_neg]

end Entries


open TwistedTransfer in
theorem topTwistDensOfZeta : TopTwistDensOfZeta := by
  intro hZ Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 K hD
  obtain ⟨hP, -, hAL, hQQ, -, -, hSL, hLS⟩ := hD
  intro w hw s Wv Wv' hW hW' x y _ _ c _ g
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hWW' : Wv * Wv' = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]
  have hW'W : Wv' * Wv = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]
  have f_fi : mkP Wv Wv' * mkP Wv' Wv = 1 := pr_ext hWW' hWW'
  have fi_f : mkP Wv' Wv * mkP Wv Wv' = 1 := pr_ext hW'W hW'W
  have hfn : ∀ g ∈ Fr.zfns L, Commute (mkP Wv Wv') g := by
    obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hG, hGi, -⟩ := hAL
    have key : ∀ j j' : Fin 6, Commute (mkP Wv Wv') (mkP (X.fn j) (X.fn j')) := by
      intro j j'
      show _ * _ = _ * _
      exact pr_ext (TwistedTransfer.mulOp_comm_fn X Wv _ hW j)
        (TwistedTransfer.mulOp_comm_fn X Wv' _ hW' j').symm
    intro g hg
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact key _ _
    · rw [hzi]; exact key _ _
    · rw [hzb]; exact key _ _
    · rw [hzbi]; exact key _ _
    · rw [hG]; exact key _ _
    · rw [hGi]; exact key _ _
  have hGG : Commute (mkP Wv Wv') L.GG := hfn _ (TwistedTransfer.mem_zfns L).2.2.2.2.1
  have hfiGG : Commute (mkP Wv' Wv) L.GG := (TwistedTransfer.commute_inv hGG.symm f_fi fi_f).symm
  obtain ⟨e11, e10⟩ := zeta_entries hZ hP X st l0 hQQ s Wv Wv' hW hW'
  have hx : ∀ Y, Commute (mkP Wv Wv') (st.x Y) := by
    intro Y
    have h := e11 Y
    rw [hLS.tau Y] at h
    have h1 : L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv') = L.GG * st.x Y := by
      conv_rhs => rw [← h]
      rw [← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq]
      simp only [mul_assoc]
    have h2 : mkP Wv' Wv * st.x Y * mkP Wv Wv' = st.x Y := by
      calc mkP Wv' Wv * st.x Y * mkP Wv Wv' = L.GGi * (L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv')) := by
            rw [← mul_assoc, L.GGi_GG, one_mul]
        _ = L.GGi * (L.GG * st.x Y) := by rw [h1]
        _ = st.x Y := by rw [← mul_assoc, L.GGi_GG, one_mul]
    show mkP Wv Wv' * st.x Y = st.x Y * mkP Wv Wv'
    calc mkP Wv Wv' * st.x Y = mkP Wv Wv' * (mkP Wv' Wv * st.x Y * mkP Wv Wv') := by rw [h2]
      _ = st.x Y * mkP Wv Wv' := by rw [← mul_assoc, ← mul_assoc, f_fi, one_mul]
  have hl : ∀ Y ∈ st.inv, mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv' =
      L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y - algebraMap ℂ _ s := by
    intro Y hY
    have h := e10 Y
    rw [hLS.low Y hY, hLS.tau Y] at h
    have hfix : Commute (mkP Wv' Wv) (st.x Y) := (TwistedTransfer.commute_inv (hx Y).symm f_fi fi_f).symm
    have cancel : ∀ T, st.xi Y * L.GGi * (L.GG * st.x Y * T) = T := by
      intro T
      calc st.xi Y * L.GGi * (L.GG * st.x Y * T) = st.xi Y * (L.GGi * L.GG) * st.x Y * T := by
            simp only [mul_assoc]
        _ = T := by rw [L.GGi_GG, mul_one, (hLS.x_xi Y hY).2, one_mul]
    have h3 : mkP Wv' Wv * (L.GG * st.x Y * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y)) * mkP Wv Wv' =
        L.GG * st.x Y * (mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv') := by
      rw [← mul_assoc (mkP Wv' Wv) (L.GG * st.x Y), ← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq,
        mul_assoc L.GG (mkP Wv' Wv), hfix.eq]
      simp only [mul_assoc]
    rw [h3, ← mul_sub] at h
    rw [← cancel (mkP Wv' Wv * _ * mkP Wv Wv'), h, cancel]
  have hWH : TwistedTransfer.WaveHyp L st (mkP Wv Wv') (mkP Wv' Wv) s := ⟨f_fi, fi_f, rfl, hfn, hx, hl⟩
  obtain ⟨hFV, hd⟩ := TwistedTransfer.frame_twist_F hSL hLS hWH w hw.1
  have hM : (Fr.ofWord L st w).d L * (Fr.ofWord L st w).F * Vw (mkP Wv Wv') s w =
      io (mkP Wv Wv') * ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) := by
    rw [mul_assoc, hFV, ← mul_assoc, ← hd.eq, mul_assoc]
  unfold topDens
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hfst : (mkP Wv Wv').1 = Wv := rfl
  rw [← act_mul, hM, act_mul, act_io, hfst, hW1, hsInner_smul_left]

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentSums
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace UnipotentSums

open C2x5 C2x6 FlagSpanVanishing HermitianXiVector

variable {k r : ℕ}

lemma sum_X (g : Fin (2 * r + k + 1) → ℂ) (hg : ∀ p : Fin (2 * r + k + 1), r ≤ p.val → g p = 0) :
    ∑ p, g p = ∑ c : Fin r, g (eI k r c) := by
  symm
  refine Fintype.sum_of_injective (eI k r) ?_ (fun c => g (eI k r c)) g ?_ (fun _ => rfl)
  · intro a b h
    have h1 : (eI k r a).val = (eI k r b).val := congrArg Fin.val h
    exact Fin.ext h1
  · intro p hp
    apply hg
    by_contra h
    exact hp ⟨⟨p.val, by omega⟩, Fin.ext rfl⟩

lemma sig_eI (c : Fin r) : GBasic.sig k r (eI k r c) = esI k r c := by
  unfold GBasic.sig
  split_ifs with h
  · rfl
  · exact absurd (Or.inl c.isLt) h

lemma sig_esI (c : Fin r) : GBasic.sig k r (esI k r c) = eI k r c := by
  have hc := c.isLt
  unfold GBasic.sig
  split_ifs with h
  · exact Fin.ext (by show 2 * r + k - (2 * r + k - c.val) = c.val; omega)
  · exact absurd (Or.inr (by show r + k < 2 * r + k - c.val; omega)) h

lemma sum_Xs (g : Fin (2 * r + k + 1) → ℂ) (hg : ∀ p : Fin (2 * r + k + 1), p.val ≤ r + k → g p = 0) :
    ∑ p, g p = ∑ c : Fin r, g (esI k r c) := by
  symm
  refine Fintype.sum_of_injective (esI k r) ?_ (fun c => g (esI k r c)) g ?_ (fun _ => rfl)
  · intro a b h
    have h1 : 2 * r + k - a.val = 2 * r + k - b.val := congrArg Fin.val h
    have := a.isLt
    have := b.isLt
    exact Fin.ext (by omega)
  · intro p hp
    apply hg
    by_contra h
    have hp2 := p.isLt
    exact hp ⟨⟨2 * r + k - p.val, by omega⟩, Fin.ext (by show 2 * r + k - (2 * r + k - p.val) = p.val; omega)⟩

lemma sgn_X (p : Fin (2 * r + k + 1)) (hp : p.val < r ∨ r + k < p.val) : GBasic.sgn k r p = 1 := by
  unfold GBasic.sgn
  rw [if_neg (show ¬ p.val = r + k by omega)]

lemma mX_apply_X (vX : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) (j : Fin (2 * r + k + 1)) :
    C2.mX k r vX (eI k r c) j = if hj : j.val < r then vX c ⟨j.val, hj⟩ else 0 := by
  simp only [C2.mX]
  rw [dif_pos (show (eI k r c).val < r from c.isLt)]
  rfl

lemma mX_apply_Xs (vX : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) (j : Fin (2 * r + k + 1)) :
    C2.mX k r vX (esI k r c) j = if hj : r + k < j.val then (vXᴴ)⁻¹ c ⟨2 * r + k - j.val, by omega⟩ else 0 := by
  have hc := c.isLt
  have h1 : ¬ (esI k r c).val < r := by show ¬ 2 * r + k - c.val < r; omega
  have h2 : r + k < (esI k r c).val := by show r + k < 2 * r + k - c.val; omega
  simp only [C2.mX]
  rw [dif_neg h1, dif_pos h2]
  by_cases hj : r + k < j.val
  · rw [dif_pos hj, dif_pos hj]
    have e : (⟨2 * r + k - (esI k r c).val, by omega⟩ : Fin r) = c :=
      Fin.ext (by show 2 * r + k - (2 * r + k - c.val) = c.val; omega)
    rw [e]
  · rw [dif_neg hj, dif_neg hj]

lemma unipotent_apply_middle_row (vX : Matrix (Fin r) (Fin r) ℂ) (i j : Fin (2 * r + k + 1)) (hi1 : r ≤ i.val) (hi2 : i.val ≤ r + k) :
    C2.mX k r vX i j = if i = j then 1 else 0 := by
  simp only [C2.mX]
  rw [dif_neg (show ¬ i.val < r by omega), dif_neg (show ¬ r + k < i.val by omega)]

lemma mX_col_X (vX : Matrix (Fin r) (Fin r) ℂ) (p : Fin (2 * r + k + 1)) (c : Fin r) :
    C2.mX k r vX p (eI k r c) = if hp : p.val < r then vX ⟨p.val, hp⟩ c else 0 := by
  have hc := c.isLt
  simp only [C2.mX]
  by_cases h1 : p.val < r
  · rw [dif_pos h1, dif_pos h1, dif_pos (show (eI k r c).val < r from hc)]
    rfl
  · rw [dif_neg h1, dif_neg h1]
    by_cases h2 : r + k < p.val
    · rw [dif_pos h2, dif_neg (show ¬ r + k < (eI k r c).val from by show ¬ r + k < c.val; omega)]
    · rw [dif_neg h2, if_neg]
      intro h
      apply h1
      rw [h]
      exact hc

lemma unipotent_apply_middle_column (vX : Matrix (Fin r) (Fin r) ℂ) (p j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    C2.mX k r vX p j = if p = j then 1 else 0 := by
  have hne : ∀ h : p.val < r ∨ r + k < p.val, p ≠ j := fun h he => by rw [he] at h; omega
  simp only [C2.mX]
  by_cases h1 : p.val < r
  · rw [dif_pos h1, dif_neg (show ¬ j.val < r by omega), if_neg (hne (Or.inl h1))]
  · by_cases h2 : r + k < p.val
    · rw [dif_neg h1, dif_pos h2, dif_neg (show ¬ r + k < j.val by omega), if_neg (hne (Or.inr h2))]
    · rw [dif_neg h1, dif_neg h2]

end UnipotentSums

namespace UnipotentSums

open C2x5 C2x6 FlagSpanVanishing HermitianXiVector

variable {k r : ℕ}

lemma mX_col_Xs (vX : Matrix (Fin r) (Fin r) ℂ) (p : Fin (2 * r + k + 1)) (a : Fin r) :
    C2.mX k r vX p (esI k r a) = if hp : r + k < p.val then (vXᴴ)⁻¹ ⟨2 * r + k - p.val, by omega⟩ a else 0 := by
  have ha := a.isLt
  have h1 : ¬ (esI k r a).val < r := by show ¬ 2 * r + k - a.val < r; omega
  have h2 : r + k < (esI k r a).val := by show r + k < 2 * r + k - a.val; omega
  simp only [C2.mX]
  by_cases hp1 : p.val < r
  · rw [dif_pos hp1, dif_neg h1, dif_neg (show ¬ r + k < p.val by omega)]
  · by_cases hp2 : r + k < p.val
    · rw [dif_neg hp1, dif_pos hp2, dif_pos h2, dif_pos hp2]
      exact congrArg _ (Fin.ext (by show 2 * r + k - (2 * r + k - a.val) = a.val; omega))
    · rw [dif_neg hp1, dif_neg hp2, dif_neg hp2, if_neg]
      intro h
      apply hp2
      rw [h]
      exact h2

lemma mX_uh (vX : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit vX.det) : C2.mX k r vX ∈ UH (Hpk k r) := by
  have hu' : IsUnit vXᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
  have hs1 : ∀ c : Fin r, GBasic.sgn k r (eI k r c) = 1 := fun c => sgn_X _ (Or.inl c.isLt)
  have hs2 : ∀ c : Fin r, GBasic.sgn k r (esI k r c) = 1 := fun c =>
    sgn_X _ (Or.inr (by have := c.isLt; show r + k < 2 * r + k - c.val; omega))
  show (C2.mX k r vX)ᴴ * Hpk k r * C2.mX k r vX = Hpk k r
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Hpk_mul_apply, Matrix.conjTranspose_apply]
  have hilt := i.isLt
  have hjlt := j.isLt
  by_cases hi1 : i.val < r
  · obtain ⟨a, rfl⟩ : ∃ a : Fin r, eI k r a = i := ⟨⟨i.val, hi1⟩, Fin.ext rfl⟩
    have ha := a.isLt
    have hea : (eI k r a).val = a.val := rfl
    rw [sum_X _ (fun p hp => by
      rw [mX_col_X, dif_neg (show ¬ p.val < r by omega), star_zero, zero_mul])]
    have hcol : ∀ c : Fin r, C2.mX k r vX (eI k r c) (eI k r a) = vX c a := fun c => by
      rw [mX_col_X, dif_pos (show (eI k r c).val < r from c.isLt)]
      rfl
    simp only [sig_eI, hs1, one_mul, hcol, mX_apply_Xs]
    by_cases hj : r + k < j.val
    · simp only [dif_pos hj]
      have key : ∑ c : Fin r, star (vX c a) * (vXᴴ)⁻¹ c ⟨2 * r + k - j.val, by omega⟩ =
          (vXᴴ * (vXᴴ)⁻¹) a ⟨2 * r + k - j.val, by omega⟩ := by
        rw [Matrix.mul_apply]
        simp only [Matrix.conjTranspose_apply]
      rw [key, Matrix.mul_nonsing_inv _ hu', Matrix.one_apply]
      simp only [Hpk, Fin.ext_iff]
      show _ = if a.val < r ∧ a.val + j.val = 2 * r + k then (1 : ℂ) else _
      split_ifs <;> first | rfl | (exfalso; omega) | omega
    · simp only [dif_neg hj, mul_zero, Finset.sum_const_zero]
      simp only [Hpk]
      show (0 : ℂ) = if a.val < r ∧ a.val + j.val = 2 * r + k then (1 : ℂ) else _
      split_ifs <;> first | rfl | (exfalso; omega) | omega
  · by_cases hi2 : r + k < i.val
    · obtain ⟨a, rfl⟩ : ∃ a : Fin r, esI k r a = i :=
        ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)⟩
      have ha := a.isLt
      have hea : (esI k r a).val = 2 * r + k - a.val := rfl
      rw [sum_Xs _ (fun p hp => by
        rw [mX_col_Xs, dif_neg (show ¬ r + k < p.val by omega), star_zero, zero_mul])]
      have hcol : ∀ c : Fin r, C2.mX k r vX (esI k r c) (esI k r a) = (vXᴴ)⁻¹ c a := fun c => by
        have hc := c.isLt
        rw [mX_col_Xs, dif_pos (show r + k < (esI k r c).val from by show r + k < 2 * r + k - c.val; omega)]
        have e : (⟨2 * r + k - (esI k r c).val, by show 2 * r + k - (2 * r + k - c.val) < r; omega⟩ : Fin r) = c :=
          Fin.ext (by show 2 * r + k - (2 * r + k - c.val) = c.val; omega)
        rw [e]
      simp only [sig_esI, hs2, one_mul, hcol, mX_apply_X]
      by_cases hj : j.val < r
      · simp only [dif_pos hj]
        have key : ∑ c : Fin r, star ((vXᴴ)⁻¹ c a) * vX c ⟨j.val, hj⟩ =
            (((vXᴴ)⁻¹)ᴴ * vX) a ⟨j.val, hj⟩ := by
          rw [Matrix.mul_apply]
          simp only [Matrix.conjTranspose_apply]
        rw [key, ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
          Matrix.nonsing_inv_mul _ hu, Matrix.one_apply]
        simp only [Hpk, Fin.ext_iff]
        show _ = if 2 * r + k - a.val < r ∧ 2 * r + k - a.val + j.val = 2 * r + k then (1 : ℂ) else _
        split_ifs <;> first | rfl | (exfalso; omega) | omega
      · simp only [dif_neg hj, mul_zero, Finset.sum_const_zero]
        simp only [Hpk]
        show (0 : ℂ) = if 2 * r + k - a.val < r ∧ 2 * r + k - a.val + j.val = 2 * r + k then (1 : ℂ) else _
        split_ifs <;> first | rfl | (exfalso; omega) | omega
    · rw [Finset.sum_eq_single i (fun p _ hp => by
          rw [unipotent_apply_middle_column vX p i (by omega) (by omega), if_neg hp, star_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ i) h)]
      rw [unipotent_apply_middle_column vX i i (by omega) (by omega), if_pos rfl, star_one, one_mul,
        FlagSpanVanishing.sig_fixes_middle_block i ⟨by omega, by omega⟩, unipotent_apply_middle_row vX i j (by omega) (by omega)]
      simp only [GBasic.sgn, Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega) | omega | simp

lemma mX_mem (vX : Matrix (Fin r) (Fin r) ℂ) (hv : vX ∈ C2.UTset r) : C2.mX k r vX ∈ Nset k r := by
  obtain ⟨hv1, hv2⟩ := hv
  have hdet : vX.det = 1 := by
    rw [Matrix.det_of_upperTriangular (by intro i j hij; exact hv1 i j hij)]
    simp [hv2]
  refine ⟨mX_uh vX (by rw [hdet]; exact isUnit_one), ?_, ?_⟩
  · intro a i hai
    rw [mX_col_X]
    by_cases hi : i.val < r
    · rw [dif_pos hi]
      by_cases he : i = eI k r a
      · rw [if_pos he]
        subst he
        exact hv2 a
      · rw [if_neg he]
        apply hv1
        show a.val < i.val
        have : i.val ≠ a.val := fun h => he (Fin.ext h)
        omega
    · rw [dif_neg hi, if_neg]
      intro h
      apply hi
      rw [h]
      exact a.isLt
  · intro i j hj1 hj2 _
    exact unipotent_apply_middle_column vX i j hj1 hj2

end UnipotentSums

end Formalism.FourierDecayAlt.P
end

