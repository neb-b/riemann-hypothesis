module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0217
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0220
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0219

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocSetCApp
section
namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate

noncomputable section

def PStdC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2)

theorem pStdC_of (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) : PStdC :=
  Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT

theorem decay_scale (lam x : ℝ) (hlam : 0 < lam) (hx : 0 ≤ x) :
    ((1 + lam * x) ^ 3)⁻¹ ≤ (max 1 lam⁻¹) ^ 3 * ((1 + x) ^ 3)⁻¹ := by
  have hM : 1 ≤ max 1 lam⁻¹ := le_max_left _ _
  have hle : 1 + x ≤ max 1 lam⁻¹ * (1 + lam * x) := by
    rcases le_or_gt 1 lam with h1 | h1
    · have e1 : x ≤ lam * x := le_mul_of_one_le_left hx h1
      have e2 : 1 + lam * x ≤ max 1 lam⁻¹ * (1 + lam * x) := le_mul_of_one_le_left (by positivity) hM
      linarith
    · have hi : lam⁻¹ ≤ max 1 lam⁻¹ := le_max_right _ _
      have e : lam⁻¹ * (1 + lam * x) = lam⁻¹ + x := by field_simp
      have h2 : 1 ≤ lam⁻¹ := by rw [le_inv_comm₀ one_pos hlam]; simpa using h1.le
      nlinarith [mul_le_mul_of_nonneg_right hi (by positivity : (0 : ℝ) ≤ 1 + lam * x)]
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 + lam * x := by positivity
  have hc : (1 + x) ^ 3 ≤ (max 1 lam⁻¹) ^ 3 * (1 + lam * x) ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h1.le hle 3
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ((1 + lam * x) ^ 3)⁻¹ * (1 + x) ^ 3 ≤ ((1 + lam * x) ^ 3)⁻¹ * ((max 1 lam⁻¹) ^ 3 * (1 + lam * x) ^ 3) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (max 1 lam⁻¹) ^ 3 := by field_simp

section frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def Kg (S : C.HidaSetting E Wp Wq) (j : ℕ) (h h' : C.LPt) : ℝ :=
  √(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S (j + 1))) * rhoS S j

theorem gramLoc_setC_app {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) (c : ℂ) (hc : c ≠ 0) :
    (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) =
      ((Kg S j h h' : ℝ) : ℂ) * ((KB.levW (D.parOf S v) (j + 1) ((lamS S j : ℂ) * c) : ℝ) : ℂ) *
        (p v).RR (F v ε) (j + 1) w (stdS S h ++ [(1, (lamS S j : ℂ) * c)])
          (stdS S h' ++ [(1, (lamS S j : ℂ) * c)]) := by
  have hgpos := g_pos_of_built hB
  have hTT := (pdG_of_built hB v).2
  have hrd := rd_pos' E
  have hfr : ∀ b s, 0 < S.fr b s := fun b s => Real.rpow_pos_of_pos hrd _
  set lam := lamS S j with hlam
  have hlam_pos : 0 < lam := lamS_pos S hgpos j
  set xw : ℂ → ℝ := fun c => C.nAux S.G.k S.G.r (Complex.normSq c - S.T * S.T') S.fr (j + 1) [(1, c)] with hxw
  have hn_nonneg : ∀ H, D.ptSize H = j → 0 ≤ nnS S H := fun H hH =>
    lpt_value_nonneg_of_pos_of_size_le _ _ _ _ hfr H 1 le_rfl (by omega)
  have hsq : √(nnS S (h ++ [(1, c)])) * √(nnS S (h' ++ [(1, c)])) =
      √(nnS S h) * √(nnS S h') * (√(xw c) * √(xw c)) := by
    rw [nnS_app S j hj h c hsz, nnS_app S j hj h' c hsz', Real.sqrt_mul (hn_nonneg h hsz),
      Real.sqrt_mul (hn_nonneg h' hsz')]
    ring
  set RRs : ℕ → C.LPt → C.LPt → ℂ := fun i P Q => (p v).RR (F v ε) i w P Q with hRRs
  set Mj : ℤ := C.Mlev S.G.k S.G.r (j + 1) with hMj
  have hW : ∀ (H H' : C.LPt), D.ptSize H = j →
      ((√(xw c) * √(xw c) : ℝ) : ℂ) * RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) =
        ((rhoS S j * KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) : ℝ) : ℂ) *
          RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) := by
    intro H H' hH
    by_cases hjt : j = S.G.r
    · have hnu : S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
        unfold S6.nuBlock; rw [hjt]; push_cast; ring
      have hlam1 : lam = 1 := by rw [hlam, lamS, hnu, zpow_zero]
      have hfr1 : S.fr (j + 1) 1 = 1 := by
        unfold C.HidaSetting.fr
        have : ((S6.nuBlock (S.G.r : ℤ) (Nat.cast (j + 1)) (Nat.cast 1) : ℤ) : ℝ) = 0 := by
          unfold S6.nuBlock; rw [hjt]; push_cast; ring
        rw [this]; simp
      have hρ1 : rhoS S j = 1 := by rw [rhoS, ← hlam, hlam1, hfr1]; simp
      have hx : xw c = (Complex.normSq c - S.T * S.T') ^ (S.G.k - 1) := by
        simp only [hxw, C.nAux]
        rw [if_pos (by constructor <;> first | trivial | omega), mul_one]
      have hlev : KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) = B2.zWeight S.G.k S.T S.T' c := by
        rw [hlam1, Complex.ofReal_one, one_mul]
        unfold KB.levW
        rw [if_pos (by simp [hjt])]
      rw [hρ1, hlev, one_mul, hx]
      by_cases hc2 : S.T * S.T' ≤ Complex.normSq c
      · rw [Real.mul_self_sqrt (pow_nonneg (by linarith) _)]
        unfold B2.zWeight
        rw [if_pos hc2]
      · have h0 : RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) = 0 := by
          have := rrTop_zero (D.parOf S v) (p v).l0 (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP
            (M.sgn (D.parOf S v) (p v).l0) (F v ε) w H (H' ++ [(1, (lam : ℂ) * c)])
            ((lam : ℂ) * c) (by rw [hH, hjt]) (by
              rw [hlam1, Complex.ofReal_one, one_mul]
              rw [hTT]; linarith)
          simp only [hRRs]
          rw [show j + 1 = (D.parOf S v).r + 1 by rw [hjt]]
          exact this
        rw [h0, mul_zero, mul_zero]
    · have hx : xw c = (S.fr (j + 1) 1 * ‖c‖) ^ (2 * (Mj - 2)) := by
        simp only [hxw, C.nAux]
        rw [if_neg (by omega), mul_one, hMj]
        congr 1
        simp only [Nat.add_sub_cancel, Nat.cast_one]
        ring
      have hxpos : 0 < xw c := by rw [hx]; exact zpow_pos (mul_pos (hfr _ _) (norm_pos_iff.2 hc)) _
      rw [Real.mul_self_sqrt hxpos.le]
      congr 2
      rw [hx, rhoS, ← hlam, ← hMj]
      unfold KB.levW
      rw [if_neg (by show ¬ (j + 1 = S.G.r + 1); omega)]
      have hnorm : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnorm, ← mul_zpow]
      congr 1
      field_simp
  rw [gramLoc_setC hB, stdS_app S j h c hsz, stdS_app S j h' c hsz']
  have hWc := hW (stdS S h) (stdS S h') (by rw [stdS_size]; exact hsz)
  have hb1 : bS S (h ++ [(1, c)]) = bS S h := bSt_append_one _ _ _
  have hb2 : bS S (h' ++ [(1, c)]) = bS S h' := bSt_append_one _ _ _
  rw [hb1, hb2, hsq]
  simp only [hRRs] at hWc
  unfold Kg
  push_cast at hWc ⊢
  linear_combination ((√(nnS S h) : ℂ) * (√(nnS S h') : ℂ) *
    (1 / ((bS S h : ℂ) * (bS S h' : ℂ) * (ΓS S (j + 1) : ℂ)))) * hWc

theorem int_gramLoc_setC (hPS : PStdC) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (hF : KB.CptCoef (p v).T.base (F v ε)) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter)
    (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt) (hh : D.IsLocPt h j)
    (hh' : D.IsLocPt h' j) :
    ∫ c : ℂ, (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S l c =
      ((Kg S j h h' * |(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)))
        (KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2)) := by
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
  have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
  obtain ⟨φ, -, -, hφ, hφint⟩ := hPS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj w
    (stdS S h) (stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) hF (by rw [hl0]; exact hw)
  have hlam_pos := lamS_pos S hgpos j
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun c' => P5.fsv (sW S j l) c' * φ c' := ⟨_, rfl⟩
  have hae : (fun c : ℂ => (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) *
      KB.psiL S l c) =ᵐ[volume] fun c => ((Kg S j h h' : ℝ) : ℂ) * g (lamS S j • c) := by
    filter_upwards [ae_ne_zero_complex] with c hc
    have hlc : (lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
    simp only [hgdef, Complex.real_smul]
    rw [gramLoc_setC_app hB F v ε j hj w h h' hh.2 hh'.2 c hc, hφ _ hlc, psiL_eq_fsv S hgpos j l c]
    ring
  rw [integral_congr_ae hae, integral_const_mul, Measure.integral_comp_smul, Complex.finrank_real_complex,
    Complex.real_smul, hgdef]
  simp only
  rw [hφint (sW S j l)]
  push_cast
  ring

end frame

end

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtRightDerivativeCurve
section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section RdV

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def cur (X : Q.Mx k ρ) (y : Mt k ρ) (t : ℝ) : Mt k ρ :=
  Matrix.of.symm (Matrix.of y * NormedSpace.exp ((t : ℂ) • X))

theorem cur_zero (X : Q.Mx k ρ) (y : Mt k ρ) : cur X y 0 = y := by
  simp [cur, NormedSpace.exp_zero]

theorem cur_add (X : Q.Mx k ρ) (y : Mt k ρ) (s t : ℝ) : cur X (cur X y s) t = cur X y (s + t) := by
  have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
  have e : NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
    rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]
  unfold cur
  rw [Equiv.apply_symm_apply, e, Matrix.mul_assoc]

theorem cur_hasDerivAt0 (X : Q.Mx k ρ) (y : Mt k ρ) :
    HasDerivAt (cur X y) (Matrix.of.symm (Matrix.of y * X)) 0 :=
  Formalism.REAL.hasDerivAt_mul_exp_smul_zero (Matrix.of y) X

theorem cur_hasDerivAt (X : Q.Mx k ρ) (y : Mt k ρ) (s : ℝ) :
    HasDerivAt (cur X y) (Matrix.of.symm (Matrix.of (cur X y s) * X)) s := by
  have h0 := cur_hasDerivAt0 X (cur X y s)
  rw [← sub_self s] at h0
  have h1 := h0.comp_sub_const s s
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show cur X y t = cur X (cur X y s) (t - s)
  rw [cur_add, add_sub_cancel]

def mulX (X : Q.Mx k ρ) : Mt k ρ →ₗ[ℝ] Mt k ρ where
  toFun y := Matrix.of.symm (Matrix.of y * X)
  map_add' a b := by
    show Matrix.of.symm ((Matrix.of a + Matrix.of b) * X) = _
    rw [Matrix.add_mul]; rfl
  map_smul' c a := by
    show Matrix.of.symm ((c • Matrix.of a) * X) = _
    rw [Matrix.smul_mul]; rfl

variable {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par]

def dirL (X : Q.Mx k ρ) : Par × Mt k ρ →L[ℝ] Par × Mt k ρ :=
  (ContinuousLinearMap.inr ℝ Par (Mt k ρ)).comp
    ((LinearMap.toContinuousLinearMap (mulX X)).comp (ContinuousLinearMap.snd ℝ Par (Mt k ρ)))

theorem rdv_local {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {f : Par → Q.Mx k ρ → E}
    {U : Set (Par × Mt k ρ)} {F : Par × Mt k ρ → E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ q ∈ U, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q.1 (Matrix.of q.2) = F q)
    {q : Par × Mt k ρ} (hq : q ∈ U) (hqG : Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ)) :
    HasDerivAt (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) (fderiv ℝ F q (dirL X q)) 0 := by
  have hc := cur_hasDerivAt0 X q.2
  have hγ : HasDerivAt (fun t : ℝ => ((q.1, cur X q.2 t) : Par × Mt k ρ)) (dirL X q) 0 :=
    (hasDerivAt_const (0 : ℝ) q.1).prodMk hc
  have hγ0 : ((q.1, cur X q.2 0) : Par × Mt k ρ) = q := by rw [cur_zero]
  have hFd : DifferentiableAt ℝ F q := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((q.1, cur X q.2 t) : Par × Mt k ρ) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hq)
  filter_upwards [hmem] with t ht
  exact hfF _ ht (Formalism.FourierDecayAlt.P.Qx3.glev_mul hqG (hX t))

theorem parFam_contAt_comp {Y : Type} [TopologicalSpace Y] {U₀ : Set (Par × Mt k ρ)} {g : Par × Mt k ρ → E}
    (hg : PBI.ParFam k ρ U₀ g) {m : Y → Par × Mt k ρ} {y₀ : Y} (hm : ContinuousAt m y₀) (hU : m y₀ ∈ U₀)
    (hG : ∀ y, Matrix.of (m y).2 ∈ Q.Glev k ρ (Fin.last ρ)) : ContinuousAt (fun y => g (m y)) y₀ := by
  obtain ⟨U, F, hUo, hqU, hF, hgF⟩ := hg (m y₀) hU (hG y₀)
  have hcF : ContinuousAt F (m y₀) := hF.continuousOn.continuousAt (hUo.mem_nhds hqU)
  have h := ContinuousAt.comp (g := F) (f := m) (x := y₀) hcF hm
  refine h.congr ?_
  have hmem : ∀ᶠ y in 𝓝 y₀, m y ∈ U := hm.preimage_mem_nhds (hUo.mem_nhds hqU)
  filter_upwards [hmem] with y hy
  exact (hgF (m y) hy (hG y)).symm

theorem rdv_parFam {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {U₀ : Set (Par × Mt k ρ)}
    {f : Par → Q.Mx k ρ → E} (hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2))) :
    PBI.ParFam k ρ U₀ (fun q => RdV X (f q.1) (Matrix.of q.2)) := by
  intro q₀ hq₀ hG₀
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq₀ hG₀
  refine ⟨U, fun q => fderiv ℝ F q (dirL X q), hU, hqU, ?_, fun q hq hqG => ?_⟩
  · exact (hF.fderiv_of_isOpen (m := ∞) hU Formalism.REAL.withTop_enat_infty_add_one_le_infty).clm_apply
      (ContinuousLinearMap.contDiff (n := ∞) (dirL (Par := Par) (k := k) (ρ := ρ) X)).contDiffOn
  · exact (rdv_local hX hU hF hfF hq hqG).deriv

theorem hasDerivAt_right_derivative_curve {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {U₀ : Set (Par × Mt k ρ)}
    {f : Par → Q.Mx k ρ → E} (hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2))) (Z : Par) (y : Mt k ρ)
    (s : ℝ) (hq : (Z, cur X y s) ∈ U₀) (hG : Matrix.of (cur X y s) ∈ Q.Glev k ρ (Fin.last ρ)) :
    HasDerivAt (fun t : ℝ => f Z (Matrix.of (cur X y t))) (RdV X (f Z) (Matrix.of (cur X y s))) s := by
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf _ hq hG
  have h0 := rdv_local hX hU hF hfF hqU hG
  have h1 : HasDerivAt (fun t : ℝ => f Z (Matrix.of (cur X (cur X y s) t)))
      (RdV X (f Z) (Matrix.of (cur X y s))) 0 := h0.differentiableAt.hasDerivAt
  rw [← sub_self s] at h1
  have h2 := h1.comp_sub_const s s
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show f Z (Matrix.of (cur X y t)) = f Z (Matrix.of (cur X (cur X y s) (t - s)))
  rw [cur_add, add_sub_cancel]

end RdV

theorem parOK_rdV {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {X : Q.Mx k ρ}
    (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) : ParOK k ρ (E := E) (RdV X) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  have hD := rdv_parFam hX hf
  refine ⟨hD, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show deriv (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) 0 = 0
    have hγ : ContinuousAt (fun t : ℝ => ((q.1, cur X q.2 t) : Par × Mt k ρ)) 0 :=
      continuousAt_const.prodMk (cur_hasDerivAt0 X q.2).continuousAt
    have hγ0 : ((q.1, cur X q.2 0) : Par × Mt k ρ) = q := by rw [cur_zero]
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((q.1, cur X q.2 t) : Par × Mt k ρ) ∈ W :=
      hγ.preimage_mem_nhds (by rw [hγ0]; exact hW.mem_nhds hqW)
    have hev : (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) =ᶠ[𝓝 0] (fun _ => (0 : E)) := by
      filter_upwards [hmem] with t ht
      exact hz _ ht (Formalism.FourierDecayAlt.P.Qx3.glev_mul hG (hX t))
    rw [hev.deriv_eq, deriv_const]
  · have hGt : ∀ t : ℝ, Matrix.of (cur X y t) ∈ Q.Glev k ρ (Fin.last ρ) := fun t =>
      Formalism.FourierDecayAlt.P.Qx3.glev_mul hyG (hX t)
    have hpre : cur X y ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
      (cur_hasDerivAt0 X y).continuousAt.preimage_mem_nhds (by rw [cur_zero]; exact hV.mem_nhds hyV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hδ : 0 < ε / 2 := half_pos hε
    have hcb : Metric.closedBall (0 : ℝ) (ε / 2) ⊆ cur X y ⁻¹' V := fun t ht =>
      hball (Metric.closedBall_subset_ball (half_lt_self hε) ht)
    have hUt : ∀ t ∈ Metric.closedBall (0 : ℝ) (ε / 2), ∀ Z ∈ Kp, (Z, cur X y t) ∈ U₀ :=
      fun t ht Z hZ => hKV ⟨hZ, hcb ht⟩
    have hcont : ContinuousOn (fun p : Par × ℝ => RdV X (f p.1) (Matrix.of (cur X y p.2)))
        (Kp ×ˢ Metric.closedBall (0 : ℝ) (ε / 2)) := by
      intro p hp
      have hm : ContinuousAt (fun p : Par × ℝ => ((p.1, cur X y p.2) : Par × Mt k ρ)) p :=
        continuous_fst.continuousAt.prodMk
          (ContinuousAt.comp (g := cur X y) (f := Prod.snd) (x := p) (cur_hasDerivAt X y p.2).continuousAt
            continuous_snd.continuousAt)
      exact (parFam_contAt_comp (g := fun q => RdV X (f q.1) (Matrix.of q.2)) hD hm (hUt p.2 hp.2 p.1 hp.1)
        (fun p => hGt p.2)).continuousWithinAt
    obtain ⟨C, hC⟩ := (hKp.prod (isCompact_closedBall (0 : ℝ) (ε / 2))).exists_bound_of_continuousOn hcont
    have hae : ∀ᵐ Z ∂ν, Z ∈ Kp := by
      rw [ae_iff]
      simpa [Set.compl_def] using hν
    have hb : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hδ
    have hin : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), t ∈ Metric.closedBall (0 : ℝ) (ε / 2) :=
      fun t ht => Metric.ball_subset_closedBall ht
    have hF_int : ∀ t ∈ Metric.closedBall (0 : ℝ) (ε / 2),
        Integrable (fun Z => f Z (Matrix.of (cur X y t))) ν := fun t ht =>
      parFam_integrable (f := fun q => f q.1 (Matrix.of q.2)) hf hKp hν (hGt t) (fun Z hZ => hUt t ht Z hZ)
    have h0c : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) (ε / 2) := Metric.mem_closedBall_self hδ.le
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun t Z => f Z (Matrix.of (cur X y t)))
      (F' := fun t Z => RdV X (f Z) (Matrix.of (cur X y t))) (x₀ := 0) (bound := fun _ => C) hb
      (by
        filter_upwards [hb] with t ht
        exact (hF_int t (hin t ht)).aestronglyMeasurable)
      (hF_int 0 h0c)
      ((parFam_integrable (f := fun q => RdV X (f q.1) (Matrix.of q.2)) hD hKp hν (hGt 0)
        (fun Z hZ => hUt 0 h0c Z hZ)).aestronglyMeasurable)
      (by
        filter_upwards [hae] with Z hZ
        intro t ht
        exact hC (Z, t) ⟨hZ, hin t ht⟩)
      (integrable_const C)
      (by
        filter_upwards [hae] with Z hZ
        intro t ht
        exact hasDerivAt_right_derivative_curve hX hf Z y t (hUt t (hin t ht) Z hZ) (hGt t))
    show deriv (fun t : ℝ => fi (Matrix.of (cur X y t))) 0 = ∫ Z, RdV X (f Z) (Matrix.of y) ∂ν
    have hev : (fun t : ℝ => fi (Matrix.of (cur X y t))) =ᶠ[𝓝 0]
        (fun t => ∫ Z, f Z (Matrix.of (cur X y t)) ∂ν) := by
      filter_upwards [hb] with t ht
      exact hi (cur X y t) (hcb (hin t ht)) (hGt t)
    rw [hev.deriv_eq, key.2.deriv, cur_zero]

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftLocalBuiltPlaces
section
namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section consts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def lamLift (S : C.HidaSetting E Wp Wq) (b s : ℕ) (v : Fin S.f) : ℝ :=
  (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) * Real.exp 1 * (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) *
    J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)

theorem g_cast' (S : C.HidaSetting E Wp Wq) : ((S.g : ℕ) : ℝ) = S.G.g := by
  unfold C.HidaSetting.g Sz.Glob.g; push_cast; rfl

theorem len_eq' (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem norm_lamB' (S : C.HidaSetting E Wp Wq) (hg : 0 < S.G.g) (b s : ℕ) :
    ‖lamB S b s‖ = (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) := by
  have hg' : (0 : ℝ) < (S.g : ℝ) := by rw [g_cast']; exact hg
  rw [norm_lamB S hg' b s, g_cast', zpow_neg, ← inv_zpow, inv_div]

variable {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem lenI_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) : 0 < S.G.lenI := by
  have hGo := hB.2.2.2.2.2.2.2.2.2.2.1
  have h := (hGo v).1
  rw [len_eq'] at h
  have : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by have := PBD.ntop_ge S; positivity
  linarith

theorem lamLift_nonneg (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (v : Fin S.f) : 0 ≤ lamLift S b s v := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  have hN : (0 : ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hA := supA_nonneg S hg hk v false
  unfold lamLift
  have : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

theorem thr_lift (hCc : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (hb : 1 ≤ b)
    (hs : 1 ≤ s) (hbs : b + s ≤ S.G.r + 1) (v : Fin S.f) :
    0 ≤ lamLift S b s v ∧ lamLift S b s v ≤ S.base.szL b s v := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  have hCA : Cc ≤ S.CA := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hN : (0:ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hcg : (0:ℝ) ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) := by positivity
  have h := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hl
    (hCc.trans hCA) (fun one => supA_nonneg S hg hk v one)).1 b s (Real.exp 1)
    ((28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s)) hb (Real.exp_pos 1).le le_rfl hcg le_rfl
  have hdec : decide (b = 1 ∧ s + 1 = 1) = false := decide_eq_false (by omega)
  rw [hdec] at h
  refine ⟨lamLift_nonneg hB b s v, ?_⟩
  show lamLift S b s v ≤ (if b + s ≤ S.G.r + 1 then _ else _)
  rw [if_pos hbs]
  unfold lamLift
  exact h

theorem lift_K (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (b s j K : ℕ) (hjb : b + s = j + 1)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ)
    (hl1 : ∀ c, ∑ i, |F7.lagCo (grid c) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * (j - s) + s)) :
    (∏ c, ∑ i, |F7.lagCo (grid c) i|) * ‖lamB S b s‖ ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)) ^ K ≤ (lamLift S b s v) ^ K := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  rw [norm_lamB' S hg b s]
  have hexp : 2 * (j - s) + s = 2 * (b - 1) + s := by omega
  have hl1' : ∀ c, ∑ i, |F7.lagCo (grid c) i| ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) := fun c =>
    (hl1 c).trans_eq (by rw [hexp, ntop_eq_N', len_eq'])
  unfold lamLift
  set cg := (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) with hcg
  set Tf := (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) with hTf
  set A := J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) with hA
  have hA0 : 0 ≤ A := supA_nonneg S hg hk v _
  have hgg : 0 < 2 * Real.pi / S.G.g := by positivity
  have hTf0 : 0 ≤ Tf := by positivity
  have hprod : (∏ c, ∑ i, |F7.lagCo (grid c) i|) ≤ cg ^ K := by
    calc (∏ c, ∑ i, |F7.lagCo (grid c) i|) ≤ ∏ _c : Fin K, cg :=
          Finset.prod_le_prod₀ (fun c _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun c _ => hl1' c
      _ = cg ^ K := by simp
  have h1 : 0 ≤ Tf ^ K * (Real.exp 1 * A) ^ K := by positivity
  calc (∏ c, ∑ i, |F7.lagCo (grid c) i|) * Tf ^ K * (Real.exp 1 * A) ^ K
      = (∏ c, ∑ i, |F7.lagCo (grid c) i|) * (Tf ^ K * (Real.exp 1 * A) ^ K) := by ring
    _ ≤ cg ^ K * (Tf ^ K * (Real.exp 1 * A) ^ K) := mul_le_mul_of_nonneg_right hprod h1
    _ = (Tf * Real.exp 1 * cg * A) ^ K := by ring

theorem norm_u (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s K : ℕ) :
    ‖((((‖lamB S b s‖ : ℝ) : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K)‖ = 1 := by
  rw [norm_pow, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), norm_pow,
    norm_neg, norm_one, one_pow, mul_one, mul_inv_cancel₀ (norm_ne_zero_iff.2 (lamB_ne S hg b s)), one_pow]

end consts

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

