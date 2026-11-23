module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0184
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWave

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PicMemUclsC
section
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section TowerC

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}

theorem transportC {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
    {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
    {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
    {l0 : ℕ} (hD : IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0)
    {ε : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)} (hF : JC.NiceCoef (T.bs j) ε F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) (Y : ℝ) (a b : Fin 2) {R : ℝ} (hRF : BSR R F) :
    ∃ F', JC.NiceCoef (T.bs j) ε F' ∧ BSR R F' ∧ IsPic T j ((QQi L st 0 (Y : ℂ) a b).1 Φ) F' := by
  let w : List C.Letter := [(true, Y)]
  let Fv : Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := Pi.single (eS 0 b) F
  have hFv : ∀ e, JC.NiceCoef (T.bs j) ε (Fv e) := by
    intro e
    by_cases h : e = eS 0 b
    · subst h; simpa [Fv] using hF
    · simp only [Fv, Pi.single_eq_of_ne h]; exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  let xv : Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := fun e => B.JF (T.bs j) (Fv e)
  let Φv : Ix (Fin w.length) →
      RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' :=
    Pi.single (eS 0 b) Φ
  have hx : ∀ e, xv e ∈ FFl (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' 0
      (OmPlus (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z') := fun e =>
    Formalism.FourierDecayAlt.P.bessel_function_finite_class _ _ Wp Wq (T.bs j) (Fv e) ε hε (hFv e)
  have hΦv : ∀ e, ∀ y ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (Φv e : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (xv e) y.1 y.2 := by
    intro e y hy
    by_cases h : e = eS 0 b
    · subst h
      have := hΦ y hy
      simp only [Φv, xv, Fv, Pi.single_eq_same]
      exact this
    · simp only [Φv, xv, Fv, Pi.single_eq_of_ne h]
      have h0 := congrFun (congrFun (resG_JF_zero (T.bs j) (Fin.last (JC.parLev P0 j).r)) y.1) y.2
      exact h0.symm
  have hRv : ∀ e, BSR R (Fv e) := by
    intro e
    by_cases h : e = eS 0 b
    · subst h; simpa [Fv] using hRF
    · simp only [Fv, Pi.single_eq_of_ne h]; exact fun g _ h0 => absurd rfl h0
  refine ⟨D.actOp (D.RRlev T (M.sgn P0 l0) j w) Fv (eS 0 a),
    Formalism.FourierDecayAlt.P.module_regularity Wp Wq P0 T (M.sgn P0 l0) j w Fv ε hε hFv (eS 0 a),
    (actOp_nice_bsr P0 T (M.sgn P0 l0) j w Fv hFv hRv (eS 0 a)).2, fun y hy => ?_⟩
  have hact := Formalism.FourierDecayAlt.P.radial_module_action Wp Wq P0 T j X μ L st l0 hD w xv Φv hx hΦv (eS 0 a) y hy
  have hbes := Formalism.FourierDecayAlt.P.bessel_module Wp Wq P0 T (M.sgn P0 l0) j w Fv ε hε hFv (eS 0 a) y hy
  have e : P5.act (RRi L st 0 (D.positionted w)) Φv (eS 0 a) = (QQi L st 0 (Y : ℂ) a b).1 Φ := by
    show actP (RRw (QQi L st 0) [(⟨true, 0, (Y : ℂ)⟩ : Letter ℂ (Fin 1))]) (Pi.single (eS 0 b) Φ) (eS 0 a) = _
    exact blockMulVec_one_letter _ _ _ _ _ _
  have e' := congrArg (fun Ψ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
    (T.bs j).π' => (Ψ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2) e
  exact e'.symm.trans (hact.trans hbes.symm)

end TowerC

section ClsC

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}
  {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
  {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
  {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
  {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
  {l0 : ℕ}
  {K : Fin ((JC.parLev P0 j).r + 1) →
    Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')}

def PicsInBS (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (K0 : Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) :
    Prop :=
  ∀ (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε R : ℝ), 0 < ε → JC.NiceCoef (T.bs j) ε F → BSR R F →
    ∃ Φ ∈ K0, ∀ x ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (Φ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) x.1 x.2 =
        resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last (JC.parLev P0 j).r) (B.JF (T.bs j) F) x.1 x.2

theorem pic_mem_K0C (hJ : PicsInBS T j (K 0)) {ε R : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}
    (hF : JC.NiceCoef (T.bs j) ε F) (hRF : BSR R F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) : Φ ∈ K 0 := by
  obtain ⟨Φ', hK, hΦ'⟩ := hJ F ε R hε hF hRF
  have e : Φ = Φ' := radSp_ext Φ Φ' (fun y hy => (hΦ y hy).trans (hΦ' y hy).symm)
  rw [e]; exact hK

theorem pic_mem_UclsC (hD : IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0)
    (hJ : PicsInBS T j (K 0)) (Pts : Set ℝ) {ε R : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}
    (hF : JC.NiceCoef (T.bs j) ε F) (hRF : BSR R F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) : Φ ∈ Ucls (K 0) (Gen L st Pts) := by
  intro m hm
  have key : ∀ m ∈ Submonoid.closure (Gen L st Pts), ∀ (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      JC.NiceCoef (T.bs j) ε F → BSR R F → IsPic T j Φ F →
      ∃ F', JC.NiceCoef (T.bs j) ε F' ∧ BSR R F' ∧ IsPic T j (m.1 Φ) F' := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem a ha =>
      intro F Φ hF hRF hΦ
      obtain ⟨Y, _, i, i', rfl⟩ := ha
      exact transportC hD hε hF Φ hΦ Y i i' hRF
    | one => intro F Φ hF hRF hΦ; exact ⟨F, hF, hRF, hΦ⟩
    | mul a b _ _ iha ihb =>
      intro F Φ hF hRF hΦ
      obtain ⟨F1, h1, hr1, h1'⟩ := ihb F Φ hF hRF hΦ
      obtain ⟨F2, h2, hr2, h2'⟩ := iha F1 _ h1 hr1 h1'
      exact ⟨F2, h2, hr2, h2'⟩
  obtain ⟨F', hF', hRF', hΦ'⟩ := key m hm F Φ hF hRF hΦ
  exact pic_mem_K0C hJ hε hF' hRF' _ hΦ'

end ClsC

end

end Formalism.FourierDecayAlt.P.PBF
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def cay {k r : ℕ} (X : B.Mat k r) : B.Mat k r := (1 + X) * (1 - X)⁻¹

def cayInv {k r : ℕ} (g : B.Mat k r) : B.Mat k r := (g - 1) * (g + 1)⁻¹

def LieBasis : Prop :=
  ∀ k r : ℕ, ∃ (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] B.Mat k r) (M : B.Mat k r →L[ℝ] (Fin d → ℝ)),
    (∀ x, B.inLie k r (L x)) ∧ (∀ x, M (L x) = x) ∧ ∀ X, B.inLie k r X → L (M X) = X

def CayAlg : Prop :=
  ∀ k r : ℕ,
    (∀ X : B.Mat k r, B.inLie k r X → IsUnit (1 - X) → cay X ∈ B.GV k r ∧ IsUnit (cay X + 1) ∧ cayInv (cay X) = X) ∧
    ∀ g ∈ B.GV k r, IsUnit (g + 1) → B.inLie k r (cayInv g) ∧ IsUnit (1 - cayInv g) ∧ cay (cayInv g) = g

def GVGrp : Prop :=
  ∀ k r : ℕ, IsUnit ((1 : B.Mat k r) + 1) ∧ ∀ g₀ ∈ B.GV k r, g₀⁻¹ * g₀ = 1 ∧
    ∀ h ∈ B.GV k r, g₀ * h ∈ B.GV k r ∧ g₀⁻¹ * h ∈ B.GV k r ∧ g₀ * (g₀⁻¹ * h) = h

def CaySmooth : Prop :=
  ∀ (k r : ℕ) (g₀ : B.Mat k r),
    IsOpen {X : B.Mat k r | IsUnit (1 - X)} ∧ IsOpen {m : B.Mat k r | IsUnit (g₀⁻¹ * m + 1)} ∧
    ContDiffOn ℝ ∞ (fun X : B.Mat k r => g₀ * cay X) {X | IsUnit (1 - X)} ∧
    ContDiffOn ℝ ∞ (fun m : B.Mat k r => cayInv (g₀⁻¹ * m)) {m | IsUnit (g₀⁻¹ * m + 1)}

theorem gChart_of (hB : LieBasis) (hA : CayAlg) (hG : GVGrp) (hS : CaySmooth) : GChart := by
  intro k r
  obtain ⟨d, L, M, hL, hML, hLM⟩ := hB k r
  refine ⟨d, fun g₀ hg₀ => ?_⟩
  obtain ⟨hA1, hA2⟩ := hA k r
  obtain ⟨hOne, hGg⟩ := hG k r
  obtain ⟨hinv, hmul⟩ := hGg g₀ hg₀
  obtain ⟨hO1, hU1, hκs, hΦs⟩ := hS k r g₀
  refine ⟨{x | IsUnit (1 - L x)}, {m | IsUnit (g₀⁻¹ * m + 1)}, fun x => g₀ * cay (L x),
    fun m => M (cayInv (g₀⁻¹ * m)), hO1.preimage L.continuous, hU1, ?_, ?_, ?_, ?_, ?_⟩
  · show IsUnit (g₀⁻¹ * g₀ + 1)
    rw [hinv]; exact hOne
  · exact hκs.comp L.contDiff.contDiffOn (fun x hx => hx)
  · exact M.contDiff.comp_contDiffOn hΦs
  · intro x hx
    obtain ⟨hc, hc1, hci⟩ := hA1 (L x) (hL x) hx
    have e : g₀⁻¹ * (g₀ * cay (L x)) = cay (L x) := by
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    refine ⟨(hmul _ hc).1, ?_, ?_⟩
    · show IsUnit (g₀⁻¹ * (g₀ * cay (L x)) + 1)
      rw [e]; exact hc1
    · show M (cayInv (g₀⁻¹ * (g₀ * cay (L x)))) = x
      rw [e, hci, hML]
  · intro g hg hgG
    obtain ⟨-, hh, hgh⟩ := hmul g hgG
    obtain ⟨hl, hu, hc⟩ := hA2 _ hh hg
    refine ⟨?_, ?_⟩
    · show IsUnit (1 - L (M (cayInv (g₀⁻¹ * g))))
      rw [hLM _ hl]; exact hu
    · show g₀ * cay (L (M (cayInv (g₀⁻¹ * g)))) = g
      rw [hLM _ hl, hc, hgh]

def IsDomOmPlus : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    Q.IsDom k r z z' 0 (Q.OmPlus k r z z')

def RightTypeAction0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wq]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (mm : ℕ∞), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    IsCRepOn (UWset k r z') π' → ContinuousOn π' (UWset k r z') →
    ∀ J ∈ Gr.FFlM mm k r z z' π π' 0 D, ∀ g ∈ Q.Glev k r 0 ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z'] Bs → ∀ (w : ℂ) (v : Wq),
      Q.capR k r Bs w J g v = J g (Q.capRep k r π' Bs w v)

def LeftTypeAction0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (mm : ℕ∞), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) →
    ∀ J ∈ Gr.FFlM mm k r z z' π π' 0 D, ∀ g ∈ Q.Glev k r 0 ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs → ∀ (w : ℂ) (v : Wq),
      Q.capLft k r Bs w J g v = Q.capRep k r π Bs w (J g v)

theorem uCap_of (h0 : IsDomOmPlus) (hR : RightTypeAction0) (hL : LeftTypeAction0) : UCap := by
  intro k r Wp Wq _ _ _ _ _ _ D u u' J hT hT' hF
  have hD := h0 k r D.z D.z' D.z_mem D.z'_mem
  have hg0 : ∀ g ∈ JF.Om k r D.z D.z', g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r D.z D.z' :=
    fun g hg => ⟨⟨hg.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩
  refine ⟨fun Bs hBs w => ⟨∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ)), fun g hg => ?_⟩,
    fun Bs hBs w => ⟨∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u' i : ℂ)), fun g hg => ?_⟩⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [hL Wp Wq k r k D.z D.z' D.π D.π' _ _ D.z_mem D.z'_mem hD hT.2.1 hT.2.2.1 J hF g (hg0 g hg) Bs hBs w v,
      hT.2.2.2.2.2 Bs hBs w (J g v)]
    rfl
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [hR Wp Wq k r k D.z D.z' D.π D.π' _ _ D.z_mem D.z'_mem hD hT'.2.1 hT'.2.2.1 J hF g (hg0 g hg) Bs hBs w v,
      hT'.2.2.2.2.2 Bs hBs w v, map_smul]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtMinusW
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem onOld_id {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {w : List C.Letter} :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
      KB.onOld (⇑(LinearMap.id : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] _)) ys x = x
  | [], x => rfl
  | y :: ys, x => by
    funext e
    simp only [KB.onOld]
    rw [onOld_id ys]
    exact congrArg x (Fin.cons_self_tail e)

theorem mix_push {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) {K d : ℕ}
    (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) (p q : C.LPt) :
    KB.mix S v ε i (PBD.pushU grid mk) (PBD.pushTh grid mk) p q =
      ∑ n : Fin K → Fin (d + 1), (F7.thGrid grid n : ℂ) *
        KB.gN S v ε i (mk (List.ofFn fun b => grid b (n b))) p q := by
  unfold KB.mix PBD.pushTh
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hmem : mk (List.ofFn fun b => grid b (n b)) ∈ PBD.pushU grid mk :=
    Finset.mem_image_of_mem _ (Finset.mem_univ n)
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    simp

section sizes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem sizeAt_plusW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ys : List ℝ) (a : List C.Letter) :
    S.sizeAt v (KB.plusW ys a) = (ys.map fun y => |S.P v y|).prod * S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  rw [PBD.plusW_eq, List.map_append, List.prod_append, List.map_map]
  rfl

theorem sizeAt_minusW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ys : List ℝ) (a : List C.Letter) :
    S.sizeAt v (KB.minusW ys a) = (ys.map fun y => |S.P v (y + 1)|).prod * S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  rw [PBD.minusW_eq, List.map_append, List.prod_append, List.map_map]
  rfl

theorem sizeAt_pos (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : D.AdmAt S v a) : 0 < S.sizeAt v a := by
  obtain ⟨w, hw⟩ := ha
  have hA := (PBD.admissible_list_of_word S w v).1
  rw [hw] at hA
  unfold C.HidaSetting.sizeAt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hnode := hA j hj
  have hgrid : (∃ a', PBD.nodeOf a[j] ∈ S.grid v a') ∨ PBD.nodeOf a[j] ∈ S.grid1 v := by
    rcases Finset.mem_union.1 hnode with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr h
  obtain ⟨-, -, hP, hP1⟩ := (hG v).2.2.2.2.2 _ hgrid
  refine abs_pos.2 ?_
  unfold PBD.nodeOf at hP hP1
  split_ifs at hP hP1 with hs
  · exact hP
  · simpa using hP1

end sizes

section nodes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

def NodeOK (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (one : Bool) (y : ℝ) : Prop :=
  (one = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ y ∈ S.grid v a') ∨
    (one = true ∧ y ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, y) x)

theorem nodes_level (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (a : List C.Letter) (ha : D.AdmAt S v a)
    (K : ℕ) (hK : a.length + K ≤ S.Ntop) (j : ℕ) (hj : j ≤ S.G.r) :
    ∃ grid : Fin K → Fin (2 * j + 1) → ℝ,
      (∀ b, Function.Injective (grid b)) ∧
      (∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * j)) ∧
      (∀ n : Fin K → Fin (2 * j + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        (List.ofFn fun b => grid b (n b)).Pairwise (fun y y' => 2 < |y - y'|) ∧
        ∀ y ∈ (List.ofFn fun b => grid b (n b)), NodeOK S v a (decide (j = 0)) y) ∧
      KB.LocProb S v (a.length + K) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) ∧
      KB.LocProb S v (a.length + K) (PBD.pushU grid fun ys => KB.minusW ys a)
        (PBD.pushTh grid fun ys => KB.minusW ys a) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGr, -⟩ := hB'
  have hCI := PBCut.cutInside_of_built hB
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  ·
    obtain ⟨ys, hlen, -, hg1, hp, hm, hcp, hcm, hpw⟩ :=
      Formalism.FourierDecayAlt.P.new_letters_admissible_level_one E Wp Wq S hGo hGr hCI v a K ha hK
    set grid : Fin K → Fin (2 * 0 + 1) → ℝ := fun b _ => ys.get ⟨b, by rw [hlen]; exact b.2⟩ with hgrid
    have hys : ∀ n : Fin K → Fin (2 * 0 + 1), (List.ofFn fun b => grid b (n b)) = ys := by
      intro n
      apply List.ext_get
      · simp [hlen]
      · intro i h1 h2
        simp [hgrid]
    have hsep : ∀ y ∈ ys, ∀ x ∈ a, PBD.Sep (true, y) x := by
      obtain ⟨w, hw⟩ := hp
      have hA := (PBD.admissible_list_of_word S w v).2
      rw [hw, PBD.plusW_eq] at hA
      intro y hy x hx
      exact (List.pairwise_append.1 hA).2.2 _ (List.mem_map.2 ⟨y, hy, rfl⟩) _ hx
    have hmk : ∀ mk : List ℝ → List C.Letter, (mk ys = KB.plusW ys a ∨ mk ys = KB.minusW ys a) →
        ∀ n : Fin K → Fin (2 * 0 + 1), D.AdmAt S v (mk (List.ofFn fun b => grid b (n b))) ∧
          (mk (List.ofFn fun b => grid b (n b))).length ≤ a.length + K := by
      intro mk hmk n
      rw [hys n]
      rcases hmk with h | h <;> rw [h]
      · exact ⟨hp, by rw [PBD.plusW_eq]; simp [hlen]; omega⟩
      · exact ⟨hm, by rw [PBD.minusW_eq]; simp [hlen]; omega⟩
    refine ⟨grid, fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega), fun b => ?_, fun n => ?_, ?_, ?_⟩
    · simp [F7.lagCo]
    · rw [hys n]
      refine ⟨hp, hm, hcp, hcm, hpw.imp fun h => by linarith, fun y hy => Or.inr ⟨rfl, hg1 y hy, hsep y hy⟩⟩
    · exact PBD.locProb_push S v _ grid (fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega)) _
        (hmk (fun ys => KB.plusW ys a) (Or.inl rfl))
    · exact PBD.locProb_push S v _ grid (fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega)) _
        (hmk (fun ys => KB.minusW ys a) (Or.inr rfl))
  ·
    obtain ⟨-, grid, hinj, hl1, hmem, hall, hlp, hlm⟩ :=
      Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a K (2 * j) ha hK (by omega)
    refine ⟨grid, hinj, hl1, fun n => ?_, hlp, hlm⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hall n
    refine ⟨h1, h2, h3, h4, h5.imp fun h => by linarith, fun y hy => Or.inl ⟨by simp; omega, ?_⟩⟩
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨a.length + K - b, by omega, by omega, hmem b (n b)⟩

end nodes

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatio
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def topR {P : M.Par} (l0 : ℕ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty P) (y : ℝ) : ℂ :=
  Wd.qw (M.qC P) (D.positionted w) (y : ℂ) / Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) e ((y : ℂ) + 1)

def TopRatio : Prop :=
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → 28 * Real.exp 1 ≤ Cc → ∀ (v : Fin S.f) (w : List C.Letter) (y : ℝ),
    KB.CutWord (D.parOf S v) (S.l + 1) ((true, y) :: w) → (∃ m, y ∈ S.grid v m) → w.length < S.Ntop →
    (∀ x ∈ w, (S.Ntop : ℝ) ^ 2 + 1 ≤ |y - x.2| ∧ (x.1 = false → (S.Ntop : ℝ) ^ 2 + 1 ≤ |y - (x.2 - 1)|)) →
    ∀ (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)),
      0 < (topR (S.l + 1) w e ρ y).re ∧ (topR (S.l + 1) w e ρ y).im = 0 ∧
      |S.P v y| ≤ Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (Real.sqrt (S.T * S.T'))⁻¹ * (topR (S.l + 1) w e ρ y).re

def lamTop {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (b : ℕ) (v : Fin S.f) : ℝ :=
  √((2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r b ((S.G.r : ℤ) + 2 - b))) * Real.exp 1 *
    (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
    (√(S.T * S.T'))⁻¹)

def TopLocB : Prop :=
  KB.DegTop → Top.VecVTypes → TopRatio →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    (∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ v, 0 ≤ lamTop S (S.G.r + 2 - s) v ∧
      2 * lamTop S (S.G.r + 2 - s) v ≤ S.base.szL (S.G.r + 2 - s) s v) ∧
    ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.TopLoc (setC S p F) v fun b _ => lamTop S b v

end

end Formalism.FourierDecayAlt.P.PBL
end

