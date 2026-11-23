module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormPositivity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0121
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0117
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0023
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0120
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PairLevZeroIndep
section
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem tprod_succ (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) (l : Fin r) :
    P5.tprod L Y l.val = P5.tprod L Y (l.val + 1) * Ts (site L l) Y := by
  rw [P5.tprod, dite_eq_left l.isLt]

theorem tprod_top (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) : P5.tprod L Y r = 1 := by
  rw [P5.tprod, dite_eq_right (lt_irrefl r)]

theorem QQi_step (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (l : Fin r) : QQi L st l.castSucc = fun Y => Matrix.conjTranspose (Ts (site L l) (star Y)) * QQi L st l.succ Y * Ts (site L l) Y := by
  funext Y
  simp only [QQi, Fin.coe_castSucc, Fin.val_succ]
  rw [tprod_succ L (star Y) l, tprod_succ L Y l, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem QQi_top (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π'))) :
    QQi L st (Fin.last r) = st.QQ := by
  funext Y
  simp only [QQi, Fin.val_last, tprod_top, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def bet (μ : MeasureTheory.Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') : ℂ := pairLev μ 0 Φ Ψ (fun _ => 1)

theorem pairAt_zero_left (μ : MeasureTheory.Measure (Mt k r)) (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ 0 Ψ c = 0 := by
  have h0 : ∀ A : Wq →L[ℂ] Wp, B.hsInner 0 A = 0 := fun A => by
    simp only [B.hsInner, B.hsVec, ContinuousLinearMap.zero_apply]
    rw [show (fun _ : Fin (Module.finrank ℂ Wq) => (0 : Wp)) = 0 from rfl, WithLp.toLp_zero,
      inner_zero_right]
  simp [P5.pairAt, h0]

theorem pairAt_zero_right (μ : MeasureTheory.Measure (Mt k r)) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Φ 0 c = 0 := by
  have h0 : ∀ A : Wq →L[ℂ] Wp, B.hsInner A 0 = 0 := fun A => by
    simp only [B.hsInner, B.hsVec, ContinuousLinearMap.zero_apply]
    rw [show (fun _ : Fin (Module.finrank ℂ Wq) => (0 : Wp)) = 0 from rfl, WithLp.toLp_zero,
      inner_zero_left]
  simp [P5.pairAt, h0]

variable {S : Type} [Fintype S] [DecidableEq S]

theorem form_single_left (μ : MeasureTheory.Measure (Mt k r)) (a : Ix S) (Φ : RadSp k r z z' π π')
    (y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (Pi.single a Φ) y c = pairLev μ 0 Φ (y a) c := by
  simp only [P5.form, pairLev]
  congr 1
  funext c'
  congr 1
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, pairAt_zero_left]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem form_eq_pairS (μ : MeasureTheory.Measure (Mt k r)) (K0 : Submodule ℂ (RadSp k r z z' π π'))
    (c : Fin r → ℂ) (hS : SesqOn (Submodule.pi Set.univ fun _ : Ix S => K0) (fun x y => form μ 0 x y c))
    (x y : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ K0) (hy : ∀ a, y a ∈ K0) :
    form μ 0 x y c = pairS (fun Φ Ψ => pairLev μ 0 Φ Ψ c) x y := by
  classical
  have hyU : y ∈ Submodule.pi Set.univ (fun _ : Ix S => K0) := Submodule.mem_pi.mpr (fun a _ => hy a)
  have hsingle : ∀ a, Pi.single a (x a) ∈ Submodule.pi Set.univ (fun _ : Ix S => K0) := by
    intro a
    refine Submodule.mem_pi.mpr (fun b _ => ?_)
    by_cases h : b = a
    · subst h
      simpa using hx b
    · rw [Pi.single_eq_of_ne h]
      exact K0.zero_mem
  have hzero : form μ 0 0 y c = 0 := by
    have h := (hS 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) y hyU 1).1
    simp only [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have key : ∀ s : Finset (Ix S), form μ 0 (∑ a ∈ s, Pi.single a (x a)) y c =
      ∑ a ∈ s, pairLev μ 0 (x a) (y a) c := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb]
      have hmem : (∑ a ∈ s, Pi.single a (x a)) ∈ Submodule.pi Set.univ (fun _ : Ix S => K0) :=
        Submodule.sum_mem _ (fun a _ => hsingle a)
      have h := (hS _ (hsingle b) _ hmem y hyU 1).1
      dsimp only at h
      rw [one_smul, one_mul] at h
      rw [h, ih, form_single_left]
  have h2 := key Finset.univ
  rw [Finset.univ_sum_single] at h2
  rw [h2]
  rfl

end Lev

section Data

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : MeasureTheory.Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)

theorem isStart_QQi (hD : IsData P z z' π π' X μ L st l0) (i : Fin (P.r + 1)) :
    IsStart (QQi L st i) (M.qC P) := by
  have h0 : IsStart st.QQ (M.qC P) := by
    have hX := (Formalism.FourierDecayAlt.P.actual_start Wp Wq P z z' π π' hD.1 X).1
    have h := Formalism.FourierDecayAlt.P.Mx8.isStart_smul X.QQ (M.qC P) (M.sgn P l0) (Formalism.FourierDecayAlt.P.Mx8.sgn_sq P l0)
      (Formalism.FourierDecayAlt.P.Mx8.sgn_star P l0) hX
    have e : st.QQ = fun Y => M.sgn P l0 • X.QQ Y := funext hD.2.2.2.1
    rw [e]; exact h
  have key : ∀ d i : ℕ, ∀ hi : i + d = P.r, IsStart (QQi L st ⟨i, by omega⟩) (M.qC P) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have e : (⟨i, by omega⟩ : Fin (P.r + 1)) = Fin.last P.r := Fin.ext (by simp; omega)
      rw [e, QQi_top]; exact h0
    | succ d ih =>
      intro i hi
      have hlt : i < P.r := by omega
      let l : Fin P.r := ⟨i, hlt⟩
      have e : (⟨i, by omega⟩ : Fin (P.r + 1)) = l.castSucc := rfl
      rw [e, QQi_step]
      have ih' := ih (i + 1) (by omega)
      have e' : (⟨i + 1, by omega⟩ : Fin (P.r + 1)) = l.succ := rfl
      rw [e'] at ih'
      exact Formalism.FourierDecayAlt.P.Mx8.isStart_step _ _ _ (isSite_actual hD.2.2.1 l)
        (qqCommutes_actual P z z' π π' X μ L st l0 hD l) ih'
  exact key (P.r - i.val) i.val (by omega)

theorem form_single_right (μ : MeasureTheory.Measure (Mt P.k P.r)) (a : Ix S)
    (x : Ix S → RadSp P.k P.r z z' π π') (Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) :
    form μ 0 x (Pi.single a Ψ) c = pairLev μ 0 (x a) Ψ c := by
  simp only [P5.form, pairLev]
  congr 1
  funext c'
  congr 1
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, pairAt_zero_right]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem herm_on {W : Type} [AddCommGroup W] [Module ℂ W] (U' : Submodule ℂ W) (f : W → W → ℂ) (hS : SesqOn U' f)
    (hN : NonnegOn U' f) (x : W) (hx : x ∈ U') (y : W) (hy : y ∈ U') : f y x = conj (f x y) := by
  have key : ∀ a : ℂ, (f (x + a • y) (x + a • y)).im = 0 := fun a =>
    (Complex.nonneg_iff.mp (hN _ (U'.add_mem hx (U'.smul_mem a hy)))).2.symm
  have hxx : (f x x).im = 0 := (Complex.nonneg_iff.mp (hN x hx)).2.symm
  have hyy : (f y y).im = 0 := (Complex.nonneg_iff.mp (hN y hy)).2.symm
  have expand : ∀ a : ℂ, f (x + a • y) (x + a • y) =
      f x x + conj a * f x y + a * (f y x + conj a * f y y) := by
    intro a
    rw [(hS x hx y hy (x + a • y) (U'.add_mem hx (U'.smul_mem a hy)) a).1,
      (hS x hx y hy x hx a).2, (hS x hx y hy y hy a).2]
  have h1 := key 1
  have hI := key Complex.I
  rw [expand] at h1 hI
  simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.mul_re, map_one, hxx, hyy] at h1 hI
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

end Data

end

end Formalism.FourierDecayAlt.P.PBF
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadDZKapLeft
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section pts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem annZ_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    AnnZ P Bs = {ζ : ℂ | P.TT < Complex.normSq ζ} := by
  ext ζ
  simp only [Set.mem_setOf_eq]
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem radR_fn (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (j : Fin 6) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (q : (Fin P.r → ℂ) × ℂ) (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (X.fn j Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec q.2) •
        NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q := by
  unfold NF.radR
  rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
  exact X.fn_apply j Φ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq)

theorem fnVal_zero (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 0 (NF.muZ P.k P.r Bs.μsec ζ) = ζ := by
  show Q.zetaL _ _ _ _ _ _ = _
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]

theorem fnVal_two (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 2 (NF.muZ P.k P.r Bs.μsec ζ) = starRingEnd ℂ ζ := by
  show star (Q.zetaL _ _ _ _ _ _) = _
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]
  rfl

theorem fnVal_five (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 5 (NF.muZ P.k P.r Bs.μsec ζ) =
      (((Complex.normSq ζ - Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' : ℝ)) : ℂ)⁻¹ := by
  show (((Q.GGl _ _ _ _ _ : ℝ)) : ℂ)⁻¹ = _
  unfold Q.GGl
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]

theorem ggi_smooth (c : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => (((Complex.normSq ζ - c : ℝ)) : ℂ)⁻¹)
      {ζ : ℂ | c < Complex.normSq ζ} := by
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => (((Complex.normSq ζ - c : ℝ)) : ℂ)) := by
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => Complex.normSq ζ - c) := by
      simp only [Complex.normSq_apply]
      exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
        (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)).sub contDiff_const
    exact Complex.ofRealCLM.contDiff.comp this
  refine hn.contDiffOn.inv fun ζ hζ h0 => ?_
  have h : c < Complex.normSq ζ := hζ
  have : Complex.normSq ζ - c = 0 := by exact_mod_cast h0
  linarith

theorem conj_smooth' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => starRingEnd ℂ ζ) :=
  Complex.conjCLE.contDiff

theorem radDZ_fn_left (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 5)
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) :
    RadDZ P Bs (X.fn j * T) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ζ => Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec ζ)) (AnnZ P Bs) := by
    rcases hj with rfl | rfl | rfl
    · exact (contDiffOn_id (s := AnnZ P Bs)).congr fun ζ hζ => fnVal_zero P Bs hpl hζ
    · exact conj_smooth'.contDiffOn.congr fun ζ hζ => fnVal_two P Bs hpl hζ
    · exact (ggi_smooth _).congr fun ζ hζ => fnVal_five P Bs hpl hζ
  refine radDZ_fun_left hT _ hs fun Φ q hq => ?_
  rw [Module.End.mul_apply, radR_fn P Bs hpl X j _ q hq]

def Lp [FiniteDimensional ℂ Wp] {P : M.Par} (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (ζ : ℂ) :
    (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ((LinearMap.toContinuousLinearMap (Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem.Lin (B.hsVec (e ρ ζ)))).smulRight (e ρ ζ)).restrictScalars ℝ

theorem Lp_apply [FiniteDimensional ℂ Wp] {P : M.Par} (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (ζ : ℂ)
    (Xv : Wq →L[ℂ] Wp) : Lp e ρ ζ Xv = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Xv) • e ρ ζ := rfl

theorem Lp_smooth [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} (he : IsFrameB P Bs e) (ρ : M.Ty P) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Lp e ρ) (AnnZ P Bs) := by
  rw [contDiffOn_clm_apply]
  intro y
  rw [annZ_eq P Bs hpl]
  exact (((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn (he.1 ρ)).inner ℂ contDiffOn_const).smul (he.1 ρ)).congr
    fun ζ _ => rfl

theorem radR_fib (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ) (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q ∈
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' q.2 := by
  intro p hp
  unfold NF.radR
  rw [Set.indicator_of_mem hq]
  have hx := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq
  have h := Θ.2.2.2 _ hx p.1 hp.1 p.2 hp.2.1
  simp only at h
  rw [hp.2.2] at h
  exact h.symm

theorem radR_kap [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ)
    (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      ∑ ρ, f ρ • (inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) • e ρ q.2) := by
  obtain ⟨hpl, hk2, -, -, -, -, -⟩ := hH
  have hζ : P.TT < Complex.normSq q.2 := by
    have h := hq.2
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1] at h
    exact h
  let q' : MA.Qp P.r P.TT := ⟨q, hq.1, hζ⟩
  have hw : ((wR P.k P.TT q.2 : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
    exact Real.sqrt_pos.2 (pow_pos (sub_pos.2 hζ) _)
  have hcoef : ∀ ρ, inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
      ((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) =
      f ρ * inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) := by
    intro ρ
    have hK := congrFun (hk f Φ) ρ
    rw [actA_kap] at hK
    have s1 := radial_space_smoothness Wp Wq P Bs hpl hk2 e he ((d.κ f).1 Φ) ρ
    have s2 := radial_space_smoothness Wp Wq P Bs hpl hk2 e he Φ ρ
    unfold trR at hK
    rw [Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem P s1, Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem P s2] at hK
    have h3 := congrFun (congrArg Subtype.val hK) q'
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, rawR] at h3
    unfold NF.radR
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    have h4 : ((wR P.k P.TT q.2 : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.2))
        (B.hsVec (((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec q.2))) =
        ((wR P.k P.TT q.2 : ℝ) : ℂ) * (f ρ * inner ℂ (B.hsVec (e ρ q.2))
          (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec q.2)))) := by
      rw [h3]; ring
    exact mul_left_cancel₀ hw h4
  rw [(he.2 q.2 hζ).2.2 _ (radR_fib P Bs hpl _ q hq)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [hcoef ρ, mul_smul]

def dl {P : M.Par} (ρ : M.Ty P) : M.Ty P → ℂ := fun ρ' => if ρ' = ρ then 1 else 0

theorem radR_kap_dl [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (ρ : M.Ty P) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ)
    (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((d.κ (dl ρ)).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      Lp e ρ q.2 (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q) := by
  rw [radR_kap P Bs X d hH e he hk _ Φ q hq, Finset.sum_eq_single ρ]
  · simp [dl, Lp_apply]
  · intro b _ hb; simp [dl, hb]
  · intro h; exact absurd (Finset.mem_univ ρ) h

theorem radDZ_kap_left [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (ρ : M.Ty P) {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) :
    RadDZ P Bs ((d.κ (dl ρ)).1 * T) :=
  radDZ_comp_left hT (Lp e ρ) (Lp_smooth P Bs hH.1 he ρ) fun Φ q hq => by
    rw [Module.End.mul_apply, radR_kap_dl P Bs X d hH e he hk ρ _ q hq]

end pts

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

