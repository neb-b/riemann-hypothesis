module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0224
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0225

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormWaveMDiff
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
open scoped ComplexConjugate

theorem fsv_mul_fsv (a b t : ℂ) : P5.fsv a t * P5.fsv b t = P5.fsv (a + b) t := by
  unfold P5.fsv
  rw [← Complex.exp_add]
  congr 1
  simp only [map_add (f := _)]
  ring

section wave

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem uInv_cons_apply (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (e : Wd.Ix (Fin (w.length + 1))) :
    KB.uInv s (l :: w) x e =
      if e 0 = 0 then KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)
      else KB.uInv s w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
        (if l.1 then s else conj s) • KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ) :=
  rfl

theorem uInv_cons0 (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    (fun e' => KB.uInv s (l :: w) x (Fin.cons (0 : Fin 2) e')) = KB.uInv s w (fun e' => x (Fin.cons 0 e')) := by
  funext e'
  rw [uInv_cons_apply, ite_eq_left (by simp)]
  simp

theorem uInv_cons1 (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    (fun e' => KB.uInv s (l :: w) x (Fin.cons (1 : Fin 2) e')) =
      KB.uInv s w (fun e' => x (Fin.cons 1 e')) + (if l.1 then s else conj s) • KB.uInv s w (fun e' => x (Fin.cons 0 e')) := by
  funext e'
  rw [uInv_cons_apply, ite_eq_right (by simp)]
  simp only [Fin.cons_succ, Pi.add_apply, Pi.smul_apply]

theorem uInv_comp (s σ : ℂ) : ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
    KB.uInv s w (KB.uInv σ w x) = KB.uInv (s + σ) w x
  | [], x => rfl
  | l :: w, x => by
    have hlinear : ∀ (v : List C.Letter)
        (a b : Wd.Ix (Fin v.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℂ),
        KB.uInv s v (a + c • b) = KB.uInv s v a + c • KB.uInv s v b := by
      intro v
      induction v with
      | nil => intros; rfl
      | cons m v ih =>
        intro a b c
        funext e
        have htail (j : Fin 2) :
            KB.uInv s v (fun i => a (Fin.cons j i) + c • b (Fin.cons j i)) (fun i => e i.succ) =
              KB.uInv s v (fun i => a (Fin.cons j i)) (fun i => e i.succ) +
                c • KB.uInv s v (fun i => b (Fin.cons j i)) (fun i => e i.succ) :=
          congrFun (ih (fun i => a (Fin.cons j i)) (fun i => b (Fin.cons j i)) c) (fun i => e i.succ)
        by_cases h : e 0 = 0
        · simpa only [uInv_cons_apply, ite_eq_left h, Pi.add_apply, Pi.smul_apply] using htail 0
        · simp only [uInv_cons_apply, ite_eq_right h, Pi.add_apply, Pi.smul_apply, htail 0, htail 1,
            smul_add, smul_smul, mul_comm c]
          abel
    funext e
    rw [uInv_cons_apply, uInv_cons0, uInv_cons1, uInv_cons_apply (s + σ), hlinear,
      uInv_comp s σ w, uInv_comp s σ w]
    split_ifs with h0 hl
    · rfl
    · simp only [Pi.add_apply, Pi.smul_apply]
      rw [add_assoc, ← add_smul, add_comm σ s]
    · simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _)]
      rw [add_assoc, ← add_smul, add_comm (conj σ) (conj s)]

theorem uInv_smulFun (s : ℂ) (φ : B.Mat k ρ → ℂ) : ∀ (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
    KB.uInv s w (fun e g => φ g • x e g) = fun e g => φ g • KB.uInv s w x e g
  | [], x => rfl
  | l :: w, x => by
    funext e g
    have ih0 := congrFun (congrFun (uInv_smulFun s φ w (fun i => x (Fin.cons 0 i))) (fun a => e a.succ)) g
    have ih1 := congrFun (congrFun (uInv_smulFun s φ w (fun i => x (Fin.cons 1 i))) (fun a => e a.succ)) g
    by_cases h : e 0 = 0
    · simpa only [uInv_cons_apply, ite_eq_left h] using ih0
    · simp only [uInv_cons_apply, ite_eq_right h, Pi.add_apply, Pi.smul_apply, ih0, ih1, smul_add]
      rw [smul_comm (φ g)]

theorem waveG_comp (Bs : B.RealPlaceData k ρ Wp Wq) (s σ : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    KB.waveG Bs s w (KB.waveG Bs σ w x) = KB.waveG Bs (s + σ) w x := by
  have e : KB.waveG Bs σ w x = fun e g => P5.fsv σ (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) • KB.uInv σ w x e g := rfl
  funext e' g
  rw [e]
  show P5.fsv s (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) •
      KB.uInv s w (fun e g => P5.fsv σ (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) • KB.uInv σ w x e g) e' g =
    P5.fsv (s + σ) (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) • KB.uInv (s + σ) w x e' g
  rw [uInv_smulFun, uInv_comp, smul_smul, fsv_mul_fsv]

theorem onOld_eq_self {w : List C.Letter}
    (M : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) → Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (hM : ∀ x, M x = x) :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)), KB.onOld M ys x = x
  | [], x => hM x
  | _ :: ys, x => by
    funext e
    show KB.onOld M ys (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) (fun a => e a.succ) = x e
    rw [onOld_eq_self M hM ys]
    exact congrArg x (Fin.cons_self_tail e)

theorem mDiff_eq (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    mDiff Bs σ w x = KB.waveG Bs (3 * σ) w x - (3 : ℂ) • KB.waveG Bs (2 * σ) w x +
      (3 : ℂ) • KB.waveG Bs σ w x - x := by
  have hV : ∀ y, waveL Bs σ w y = KB.waveG Bs σ w y := fun _ => rfl
  have e2 : KB.waveG Bs σ w (KB.waveG Bs σ w x) = KB.waveG Bs (2 * σ) w x := by
    rw [waveG_comp]; congr 1; ring
  have e3 : KB.waveG Bs σ w (KB.waveG Bs (2 * σ) w x) = KB.waveG Bs (3 * σ) w x := by
    rw [waveG_comp]; congr 1; ring
  simp only [mDiff, pow_succ, pow_zero, one_mul, mul_apply_eq_comp, LinearMap.sub_apply, one_apply_eq_self,
    map_sub, hV]
  rw [e2, e3]
  module

end wave

section forms

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem mDiff_apply_eq (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (e : Wd.Ix (Fin w.length)) :
    mDiff Bs σ w x e = KB.waveG Bs (3 * σ) w x e + (-3 : ℂ) • KB.waveG Bs (2 * σ) w x e +
      (3 : ℂ) • KB.waveG Bs σ w x e + (-1 : ℂ) • x e := by
  rw [mDiff_eq]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
  module

theorem mDiff_nice (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter) (ε : ℝ)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (hx : ∀ e, JC.NiceCoef Bs ε (x e)) :
    ∀ e, JC.NiceCoef Bs ε (mDiff Bs σ w x e) := by
  intro e
  rw [mDiff_apply_eq]
  have hw : ∀ t, JC.NiceCoef Bs ε (KB.waveG Bs t w x e) := fun t => Formalism.FourierDecayAlt.P.PBFV.waveG_nice Bs ε t w x hx e
  exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_add (Formalism.FourierDecayAlt.P.JCx2.mn_nice_add (Formalism.FourierDecayAlt.P.JCx2.mn_nice_add (hw _)
    (Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hw _))) (Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hw _)))
    (Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hx e))

end forms

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem mDiff_cpt (hP : P5.ThmPActualCpt) (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r)
    (w : List C.Letter) (hw : KB.CutWord P p.l0 w) (σ : ℂ)
    (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hx : ∀ e, KB.CptCoef (p.T.bs j) (x e)) :
    ∀ e, KB.CptCoef (p.T.bs j) (mDiff (p.T.bs j) σ w x e) := by
  have hc : ∀ t e, KB.CptCoef (p.T.bs j) (KB.waveG (p.T.bs j) t w x e) := fun t =>
    (Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support hP Wp Wq P p j hj w hw t x x hx hx).1
  intro e
  rw [mDiff_apply_eq]
  exact Formalism.FourierDecayAlt.P.PBG.cpt_add_smul _ _ (Formalism.FourierDecayAlt.P.PBG.cpt_add_smul _ _
    (Formalism.FourierDecayAlt.P.PBG.cpt_add_smul _ _ (hc _ e) (hc _ e)) (hc _ e)) (hx e)

theorem form_wave_mDiff (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : ∀ e, KB.CptCoef (p.T.bs j) (x e)) (hy : ∀ e, KB.CptCoef (p.T.bs j) (y e)) (s σ : ℂ) :
    p.form j hj w (KB.waveG (p.T.bs j) s w (mDiff (p.T.bs j) σ w x)) y =
      p.form j hj w (KB.waveG (p.T.bs j) (s + 3 * σ) w x) y - 3 * p.form j hj w (KB.waveG (p.T.bs j) (s + 2 * σ) w x) y +
        3 * p.form j hj w (KB.waveG (p.T.bs j) (s + σ) w x) y - p.form j hj w (KB.waveG (p.T.bs j) s w x) y := by
  obtain ⟨ε, hε, hxn⟩ := nice_common (p.T.bs j) hx
  obtain ⟨ε', hε', hyn⟩ := nice_common (p.T.bs j) hy
  have hd : ∀ t, Formalism.FourierDecayAlt.P.PBG.DecV (KB.waveG (p.T.bs j) t w x) := fun t =>
    Formalism.FourierDecayAlt.P.PBG.decV_of_nice (Formalism.FourierDecayAlt.P.PBFV.waveG_nice (p.T.bs j) ε t w x hxn)
  have hdy : Formalism.FourierDecayAlt.P.PBG.DecV y := Formalism.FourierDecayAlt.P.PBG.decV_of_nice hyn
  have hV : ∀ z, waveL (p.T.bs j) s w z = KB.waveG (p.T.bs j) s w z := fun _ => rfl
  have hW : KB.waveG (p.T.bs j) s w (mDiff (p.T.bs j) σ w x) =
      KB.waveG (p.T.bs j) (s + 3 * σ) w x + (-3 : ℂ) • KB.waveG (p.T.bs j) (s + 2 * σ) w x +
        (3 : ℂ) • KB.waveG (p.T.bs j) (s + σ) w x + (-1 : ℂ) • KB.waveG (p.T.bs j) s w x := by
    rw [mDiff_eq]
    calc KB.waveG (p.T.bs j) s w (KB.waveG (p.T.bs j) (3 * σ) w x - (3 : ℂ) • KB.waveG (p.T.bs j) (2 * σ) w x +
          (3 : ℂ) • KB.waveG (p.T.bs j) σ w x - x)
        = waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) (3 * σ) w x - (3 : ℂ) • KB.waveG (p.T.bs j) (2 * σ) w x +
          (3 : ℂ) • KB.waveG (p.T.bs j) σ w x - x) := rfl
      _ = waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) (3 * σ) w x) -
            (3 : ℂ) • waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) (2 * σ) w x) +
            (3 : ℂ) • waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) σ w x) - waveL (p.T.bs j) s w x := by
          simp only [map_sub, map_add (f := _), map_smul]
      _ = _ := by
          simp only [hV, waveG_comp]
          module
  rw [hW]
  unfold KB.Pl.form
  set A3 := KB.waveG (p.T.bs j) (s + 3 * σ) w x
  set A2 := KB.waveG (p.T.bs j) (s + 2 * σ) w x
  set A1 := KB.waveG (p.T.bs j) (s + σ) w x
  set A0 := KB.waveG (p.T.bs j) s w x
  have d32 := Formalism.FourierDecayAlt.P.PBG.decV_add (hd (s + 3 * σ)) (Formalism.FourierDecayAlt.P.PBG.decV_smul (-3 : ℂ) (hd (s + 2 * σ)))
  have d321 := Formalism.FourierDecayAlt.P.PBG.decV_add d32 (Formalism.FourierDecayAlt.P.PBG.decV_smul (3 : ℂ) (hd (s + σ)))
  rw [Formalism.FourierDecayAlt.P.PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w (A3 + (-3 : ℂ) • A2 + (3 : ℂ) • A1) A0 y
      (-1) d321 (hd s) hdy,
    Formalism.FourierDecayAlt.P.PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w (A3 + (-3 : ℂ) • A2) A1 y 3 d32
      (hd (s + σ)) hdy,
    Formalism.FourierDecayAlt.P.PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w A3 A2 y (-3) (hd (s + 3 * σ))
      (hd (s + 2 * σ)) hdy]
  ring

end place

end Formalism.FourierDecayAlt.P.PBO
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts
section
namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

open Classical

theorem uInv_zero_eq_self {X : Type} [AddCommGroup X] [Module ℂ X] :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → X), KB.uInv (0 : ℂ) w x = x
  | [], _ => rfl
  | l :: w, x => by
    funext e
    have he : (Fin.cons (e 0) (fun a => e a.succ) : Wd.Ix (Fin (w.length + 1))) = e := Fin.cons_self_tail e
    unfold KB.uInv
    simp only [map_zero, ite_self, zero_smul, add_zero, uInv_zero_eq_self w]
    by_cases h0 : e 0 = 0
    · rw [ite_eq_left h0]
      conv_rhs => rw [← he]
      rw [h0]
    · have h1 : e 0 = 1 := by
        rcases Fin.exists_fin_two.1 ⟨e 0, rfl⟩ with h | h
        · exact absurd h h0
        · exact h
      rw [ite_eq_right h0]
      conv_rhs => rw [← he]
      rw [h1]

theorem waveG_zero_eq_self {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) : KB.waveG Bs 0 w x = x := by
  funext e g
  simp only [KB.waveG, uInv_zero_eq_self, P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_smul]

theorem psiL_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (c : ℂ) : KB.psiL S 0 c = 1 := by
  simp [KB.psiL]

theorem intB_of (hPS : StandardPairingDecay.PStdC) (hD : DecayUnif) : IntB := by
  intro Cb
  obtain ⟨c1, h1⟩ := limit_of_module_forms Cb
  obtain ⟨c7, h7⟩ := hD Cb
  refine ⟨max c1 c7, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n
  have hB7 := PBJoint.built_setting_to_model_place (le_max_right c1 c7) hB
  have hB' := hB
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  have hCI : KB.CutInside S := PBCut.cutInside_of_built hB
  have hgpos := PBL.g_pos_of_built hB
  have hcpt : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (cutSeq S p f χ n v ε) := by
    intro v ε hε
    obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
    refine (h1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop cutN (by rw [hl0]; exact hInD)
      hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  intro v ε hε i hi1 hi2 w h h' hsz hsz'
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j ≤ S.G.r := Nat.le_of_succ_le_succ hi2
  have hsz1 : D.ptSize h = j := hsz.trans (Nat.add_sub_cancel j 1)
  have hsz1' : D.ptSize h' = j := hsz'.trans (Nat.add_sub_cancel j 1)
  rw [Nat.add_sub_cancel]
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hw : KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := PBD.cutWord_of_adm S hGo hCI w v
  have hi2' : j + 1 ≤ S.G.r + 1 := Nat.succ_le_succ hj
  have hadm : D.AdmAt S v (w.1 v) := ⟨w, rfl⟩
  have h7' := h7 E Wp Wq S p f χ A₀ hB7 v ε hε (j + 1) hi1 hi2' (w.1 v) hadm h h' hsz hsz'
  refine h7'.elim fun Cd hC => ?_
  have hdec := (hC n).1
  have hloc_app : ∀ (H : C.LPt) (c : ℂ), D.ptSize H = j → D.IsLocPt (H ++ [(1, c)]) (j + 1) → D.IsLocPt H j :=
    fun H c hH hl => ⟨fun b hb => hl.1 b (List.mem_append_left _ hb), hH⟩
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (PBL.stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (PBL.stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    have hPS' := hPS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (cutSeq S p f χ n v ε) j hj (w.1 v)
      (PBL.stdS S h) (PBL.stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) (hcpt v ε hε) (by rw [hl0]; exact hw)
    refine hPS'.elim fun φ0 hφ0all => ?_
    obtain ⟨hφ0c, -, hφ0, -⟩ := hφ0all
    have hlam := PBL.lamS_pos S hgpos j
    set φ : ℂ → ℂ := fun c => ((StandardPairingDecay.Kg S j h h' : ℝ) : ℂ) * φ0 ((PBL.lamS S j : ℂ) * c) with hφdef
    have hφc : Continuous φ := continuous_const.mul (hφ0c.comp (continuous_const.mul continuous_id))
    have hφeq : ∀ c : ℂ, c ≠ 0 → φ c = (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
        (h ++ [(1, c)]) (h' ++ [(1, c)]) := by
      intro c hc
      have hlc : (PBL.lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam.ne') hc
      rw [StandardPairingDecay.gramLoc_setC_app hB (cutSeq S p f χ n) v ε j hj (w.1 v) h h' hh.2 hh'.2 c hc, hφdef]
      simp only
      rw [hφ0 _ hlc]
      ring
    refine ⟨φ, hφc, hφeq, ⟨Cd, fun c => ?_⟩, ?_⟩
    · exact PBB.K8.bound_all hφc (fun c hc => by rw [hφeq c hc]; exact hdec c hc) c
    · have hae : (fun c => φ c) =ᵐ[volume] fun c => (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
          (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S 0 c := by
        filter_upwards [PBL.ae_ne_zero_complex] with c hc
        rw [psiL_zero, mul_one, hφeq c hc]
      rw [integral_congr_ae hae, StandardPairingDecay.int_gramLoc_setC hPS hB (cutSeq S p f χ n) v ε (hcpt v ε hε) j hj (w.1 v) hw 0
        h h' hh hh']
      have hs0 : PBL.sW S j 0 = 0 := by simp [PBL.sW]
      rw [hs0, waveG_zero_eq_self, ← PBL.rr_eq_form (p v) _ j hj (w.1 v) _ _ hH hH']
      erw [PBL.gramLoc_setC hB]
      have hsA := PBL.sizeAt_pos S hGo v (w.1 v) hadm
      have hk := PBL.kc_scal hB v j hj (w.1 v) h h'
      have hrd := PBD.rd_pos' E
      have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
      have hdl : 0 < KB.dlB S (j + 1) 1 := by unfold KB.dlB; exact div_pos (zpow_pos hrd _) hδ
      have key : StandardPairingDecay.Kg S j h h' * |(PBL.lamS S j ^ 2)⁻¹| =
          KB.dlB S (j + 1) 1 * (√(PBL.nnS S h) * √(PBL.nnS S h') * (1 / (PBL.bS S h * PBL.bS S h' * PBL.ΓS S j))) := by
        unfold PBL.Kc PBL.dW at hk
        unfold StandardPairingDecay.Kg
        field_simp at hk ⊢
        linear_combination hk
      show ((StandardPairingDecay.Kg S j h h' * |(PBL.lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * _ = ((KB.dlB S (j + 1) 1 : ℝ) : ℂ) * _
      rw [key]
      push_cast
      ring
  · have hz : ∀ c : ℂ, (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
      intro c
      erw [PBL.gramLoc_setC hB, PBL.rr_zero_of_not, mul_zero]
      rintro ⟨h1, h2⟩
      refine hloc ⟨hloc_app h c hsz1 ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h1),
        hloc_app h' c hsz1' ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h2)⟩
    have hz0 : (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε j (w.1 v) h h' = 0 := by
      erw [PBL.gramLoc_setC hB, PBL.rr_zero_of_not, mul_zero]
      rintro ⟨h1, h2⟩
      exact hloc ⟨(PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h1, (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h2⟩
    refine ⟨fun _ => 0, continuous_const, fun c _ => (hz c).symm, ⟨0, fun c => by simp⟩, ?_⟩
    rw [hz0, integral_zero, mul_zero]

def IntBOfParts : Prop := StandardPairingDecay.PStdC → DecayUnif → IntB

theorem intBOfParts : IntBOfParts := intB_of

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

theorem integral_bound_of_parts : PBASM.IntBOfParts := PBASM.intBOfParts

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PolyTopOf
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ae_left {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) :
    ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧
      (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
  have := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarN
  have a1 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z :=
    Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarW)
  have a2 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarN)
  filter_upwards [a1, a2] with x h1 h2 using ⟨h1, h2⟩

theorem polyTop_of (hKA : KrAA) : PBN.PolyTop := by
  intro Wp Wq _ _ _ _ _ _ P p G s h t hs hq hG
  set q : C.LPt := h ++ [(s, t)] with hqdef
  set Bs := p.T.base with hBs
  by_cases hpos : D.IsLocPt q (P.r + 1) ∧ 0 < D.ptG (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') P.r q
  · by_cases h' : ∃ γ ∈ B.GV P.k P.r, Zhat P.k P.r Bs.z Bs.z' γ = D.ptMatN q (P.r + 1) ∧ D.IsDFrame Bs p.ν' p.m₀ γ
    · obtain ⟨θL, hsplit⟩ := vecV_split Bs p.ν' p.m₀ q hpos h'
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r Bs.z Bs.z' q h'.choose hpos.1 hZ
      have hposG : 0 < Gf P.k P.r Bs.z Bs.z' h'.choose := hGq ▸ hpos.2
      set κ : ℂ := (-1) ^ (s - 1) / t with hκ
      have hA : ∀ y : ℝ, KB.CptCoef Bs (PBN.aaTop Bs y G) := fun y => Formalism.FourierDecayAlt.P.raising_compact_support P.k P.r Wp Wq Bs G y hG
      obtain ⟨c, hc, hcy⟩ := poly_integral (Bs.μW.prod Bs.μN) (D.ptSize h)
        (fun y x => lint Bs h'.choose θL (PBN.aaTop Bs y G) x) (fun x => κ • lint Bs h'.choose θL G x)
        (fun y => (hsplit _ (hA y)).1)
        (by
          filter_upwards [ae_left Bs] with x hx
          obtain ⟨c, hc, hcy⟩ := pt_poly hKA Bs hG h s t hs hq hγ hZ hposG hx
          set a : ℂ := ((θL x : ℝ) : ℂ) * psi P.k P.r Bs.z cStd (Matrix.of x.2) with ha
          set L := ContinuousLinearMap.compL ℂ Wq Wp Wp (Bs.π (Matrix.of x.1)) with hL
          refine ⟨fun n => a • L (c n), ?_, fun y => ?_⟩
          · simp only
            rw [hc, map_smul, smul_comm]
            rfl
          · show a • L (PBG.Kr Bs (PBN.aaTop Bs y G) _) = _
            set_option synthInstance.maxHeartbeats 100000 in
              rw [hcy y, map_sum, Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro n _
            rw [map_smul, smul_comm])
      refine ⟨c, ?_, fun y => ?_⟩
      · rw [hc, integral_smul, ← (hsplit G hG).2]
        rfl
      · show D.vecV Bs p.ν' p.m₀ (PBN.aaTop Bs y G) q = _
        rw [(hsplit _ (hA y)).2, hcy y]
    · refine ⟨fun _ => 0, ?_, fun y => ?_⟩
      · show (0 : Wq →L[ℂ] Wp) = _ • D.vecV Bs p.ν' p.m₀ G q
        unfold D.vecV
        rw [dite_eq_left hpos, dite_eq_right h', smul_zero]
      · show D.vecV Bs p.ν' p.m₀ _ q = _
        unfold D.vecV
        rw [dite_eq_left hpos, dite_eq_right h']
        simp
  · refine ⟨fun _ => 0, ?_, fun y => ?_⟩
    · show (0 : Wq →L[ℂ] Wp) = _ • D.vecV Bs p.ν' p.m₀ G q
      unfold D.vecV
      rw [dite_eq_right hpos, smul_zero]
    · show D.vecV Bs p.ν' p.m₀ _ q = _
      unfold D.vecV
      rw [dite_eq_right hpos]
      simp

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

