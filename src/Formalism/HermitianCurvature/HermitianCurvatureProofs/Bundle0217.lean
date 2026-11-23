module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0211
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0147
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegLiftOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0212
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHAsm
section
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fsv_zero' (t : ℂ) : fsv 0 t = 1 := by simp [fsv]

theorem fsv_mul' (s s' t : ℂ) : fsv s t * fsv s' t = fsv (s + s') t := by
  unfold fsv
  rw [← Complex.exp_add]
  congr 1
  simp only [map_add (f := _)]
  ring

theorem fsv_contDiff' (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hc : ContDiff ℝ ∞ (fun t : ℂ => conj t) := Complex.conjCLE.contDiff
  have h1 : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul hc)
  have he : ContDiff ℝ ∞ Complex.exp := Complex.contDiff_exp
  exact he.comp h1

section asm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem cc_zero {P : M.Par} (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc j hj t c ⟨0, by omega⟩ = t := by
  simp [cc, consC]

theorem vw_entry (hU : UUiwScalar) {V : Type} [AddCommGroup V] [Module ℂ V] (S : Type) [Fintype S] [DecidableEq S]
    (Wv Wv' : Module.End ℂ V) (s : ℂ) (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S) :
    ∃ lam : ℂ, ∀ Φ : V, (Wd.Vw (mkP Wv Wv') s w a b).1 Φ = lam • Wv Φ := by
  obtain ⟨lam, hlam⟩ := Algebra.mem_bot.1 (hU (Pr V) S s w a b)
  refine ⟨lam, fun Φ => ?_⟩
  have hab : Wd.Vw (mkP Wv Wv') s w a b = mkP Wv Wv' * Wd.UUiw (A := Pr V) s w a b := by
    simp [Wd.Vw, Wd.io, Matrix.scalar_apply, Matrix.diagonal_mul]
  rw [hab, ← hlam]
  change (Wv * algebraMap ℂ (Module.End ℂ V) lam) Φ = _
  rw [Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]

theorem class0_form (hU : UUiwScalar) (S : Type) [Fintype S] [DecidableEq S] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
    (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))) (l0 : ℕ) :
    ∀ (i : Fin ((JC.parLev P j).r + 1))
      (Ψ : RadSp (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      HerGenC S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) i Ψ → i = 0 →
      ∃ (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
        (Φ : RadSp (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (s κ : ℂ),
        JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F ∧
        IsRadJF (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' (T.bs j) F Φ ∧
        ∀ c g, (Ψ : Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp)) c g =
          (κ * fsv s (c ⟨0, by change 0 < P.r - j; omega⟩)) •
            (Φ : Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp)) c g := by
  intro i Ψ h
  induction h with
  | jf F Φ hF hΦ =>
    intro _
    exact ⟨F, Φ, 0, 1, hF, hΦ, fun c g => by simp [fsv_zero']⟩
  | slice l w a b Φ hw hΦ ih =>
    intro h
    exact absurd h (Fin.succ_ne_zero l)
  | waveC l w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
    intro h
    have hl0 : l.val = 0 := by
      have := congrArg Fin.val h
      simpa using this
    obtain ⟨F, Φ0, s0, κ0, hF, hΦ0, hv⟩ := ih h
    obtain ⟨lam, hlam⟩ := vw_entry hU S Wv Wv' s w a b
    refine ⟨F, Φ0, s + s0, lam * κ0, hF, hΦ0, fun c g => ?_⟩
    have hcl : c l = c ⟨0, by change 0 < P.r - j; omega⟩ := congrArg c (Fin.ext hl0)
    rw [hlam, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hW, hv, smul_smul, smul_smul]
    beta_reduce
    rw [hcl, ← fsv_mul']
    congr 1
    ring
  | waveZ w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
    intro h
    have := congrArg Fin.val h
    simp [JC.parLev] at this
    omega

variable {P : M.Par} {T : D.LevTower P.k P.r Wp Wq} {j : ℕ} {hj : j + 1 ≤ P.r}

theorem inC_add (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    (h : InC T j hj Ψ) (h' : InC T j hj Ψ') : InC T j hj (Ψ + Ψ') := by
  obtain ⟨G, hG, hR⟩ := h
  obtain ⟨G', hG', hR'⟩ := h'
  refine ⟨fun t γ => G t γ + G' t γ, (h2 Wp Wq P T j G G' hG hG' (fun _ => 1) contDiffOn_const).1,
    fun t ht x hx => ?_⟩
  rw [Submodule.coe_add, Pi.add_apply, Pi.add_apply, hR t ht x hx, hR' t ht x hx,
    (h4 Wp Wq P T hP hT j hj hPs G G' hG hG' t ht 0 x hx).1]

theorem inC_smul (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    (h : InC T j hj Ψ) (a : ℂ) : InC T j hj (a • Ψ) := by
  obtain ⟨G, hG, hR⟩ := h
  refine ⟨fun t γ => a • G t γ, (h2 Wp Wq P T j G G hG hG (fun _ => a) contDiffOn_const).2,
    fun t ht x hx => ?_⟩
  rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hR t ht x hx,
    (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht a x hx).2]

theorem inC_seed (h6 : CellTie) (h7 : SliceFamGood) (h8 : SliceFamJF)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hF : JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F)
    (Φ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsRadJF (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' (T.bs j) F Φ) :
    InC T j hj Φ := by
  refine ⟨sliceFam T j hj F, h7 Wp Wq P T hP hT j hj hPj hPs F hF, fun t ht x hx => ?_⟩
  obtain ⟨hdom, hGV, hOm⟩ := h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx
  have e1 : (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
      resG P.k (P.r - j) (Fin.last _) (B.JF (T.bs j) F) (cc j hj t x.1) (gi j hj x.2) :=
    hΦ (cc j hj t x.1, gi j hj x.2) hdom
  have e2 := Formalism.FourierDecayAlt.P.PBP.resG_cast (k := P.k) (ρ := P.r - (j + 1)) (n := P.r - j) (by omega) ht
    (B.JF (T.bs j) F) x.1 x.2
  rw [e1]
  refine e2.trans ?_
  unfold resG
  rw [h8 Wp Wq P T hP hT j hj hPj hPs F hF t ht _ hGV hOm, smul_comm]
  congr 2

theorem inC_wave (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Φ Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'} (s κ : ℂ)
    (hv : ∀ c g, (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c g =
      (κ * fsv s (c ⟨0, by omega⟩)) • (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c g)
    (h : InC T j hj Φ) : InC T j hj Ψ := by
  obtain ⟨G, hG, hR⟩ := h
  have hm : ContDiffOn ℝ ∞ (fun t : ℂ => κ * fsv s t) {t | t ≠ 0} :=
    (contDiff_const.mul (fsv_contDiff' s)).contDiffOn
  refine ⟨fun t γ => (κ * fsv s t) • G t γ, (h2 Wp Wq P T j G G hG hG _ hm).2, fun t ht x hx => ?_⟩
  rw [hv, cc_zero, hR t ht x hx, (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht _ x hx).2]

theorem inC_adjoin (h2 : FamAlg) (h4 : RepLin) (h9 : OpClosed)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (X : ActualOps P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (A : Module.End ℂ (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
    (hA : A ∈ Algebra.adjoin ℂ (Set.range (X.op ⟨0, by omega⟩))) :
    ∀ Ψ, InC T j hj Ψ → InC T j hj (A Ψ) := by
  induction hA using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact fun Ψ h => h9 Wp Wq P T hP hT j hj hPj hPs X i Ψ h
  | algebraMap r =>
    intro Ψ h
    rw [Module.algebraMap_end_apply]
    exact inC_smul h2 h4 hP hT hPs h r
  | add x y _ _ hx hy =>
    intro Ψ h
    rw [LinearMap.add_apply]
    exact inC_add h2 h4 hP hT hPs (hx Ψ h) (hy Ψ h)
  | mul x y _ _ hx hy =>
    intro Ψ h
    rw [Module.End.mul_apply]
    exact hx _ (hy Ψ h)

theorem herKc_jf' {S : Type} [Fintype S] [DecidableEq S] {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ}
    {π : Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}
    {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
    {D : B.RealPlaceData P.k P.r Wp Wq} (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F)
    (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) : Φ ∈ herKc S P z z' π π' L st l0 D 0 :=
  Submodule.subset_span (HerGenC.jf F Φ hF hΦ)

theorem span_step
    (Tt : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →ₗ[ℂ]
      RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (A : Module.End ℂ (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
    (K : Submodule ℂ (RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π'))
    (s : Set (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (hgen : ∀ Ψ ∈ s, Tt (A Ψ) ∈ K) :
    ∀ Ψ ∈ Submodule.span ℂ s, Tt (A Ψ) ∈ K := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact K.add_mem hx hy
  | smul r x _ hx => rw [map_smul, map_smul]; exact K.smul_mem r hx

end asm

theorem sliceStepHer_of (h1 : FamJFOK) (h2 : FamAlg) (h4 : RepLin) (h6 : CellTie) (h7 : SliceFamGood)
    (h8 : SliceFamJF) (h9 : OpClosed) (h10 : BTlAdjoin) (h11 : UUiwScalar) : PTie.SliceStepHer := by
  intro Wp Wq _ _ _ _ _ _ P T hP hT j hj l0 _ _ Xj μj Lj stj Xs μs Ls sts hDj hDs Tt t ht hTt S _ _ w a b hw Ψ hΨ
  have hPj := hDj.1
  have hPs := hDs.1
  have hAct := hDj.2.2.1
  have hA := h10 Wp Wq P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj Lj hAct S
    ⟨0, by change 0 < P.r - j; omega⟩ w a b
  have hΨ' : Ψ ∈ Submodule.span ℂ
      {Φ | HerGenC S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) 0 Φ} := hΨ
  refine span_step (P := P) (T := T) (j := j) Tt (bTl Lj ⟨0, by change 0 < P.r - j; omega⟩ w a b).1
    (herKc S (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' Ls sts
      l0 (T.bs (j + 1)) 0) _ (fun Ψ hg => ?_) Ψ hΨ'
  obtain ⟨F, Φ, s, κ, hF, hΦ, hv⟩ := class0_form h11 S P T j hj Lj stj l0 0 Ψ hg rfl
  have hC0 : InC T j hj Φ := inC_seed h6 h7 h8 hP hT hPj hPs F hF Φ hΦ
  have hC : InC T j hj Ψ := inC_wave (Φ := Φ) h2 h4 hP hT hPs s κ hv hC0
  obtain ⟨G, hG, hR⟩ := inC_adjoin h2 h4 h9 hP hT hPj hPs Xj _ hA Ψ hC
  have hJ := h1 Wp Wq P T j G hG t ht
  have hRad : IsRadJF (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π'
      (T.bs (j + 1)) (G t) (Tt ((bTl Lj ⟨0, by change 0 < P.r - j; omega⟩ w a b).1 Ψ)) := fun x hx =>
    (hTt _ x.1 x.2).trans (hR t ht x hx)
  exact herKc_jf' (S := S) (P := JC.parLev P (j + 1)) (L := Ls) (st := sts) (l0 := l0) (G t) hJ _ hRad

end Formalism.FourierDecayAlt.P.CutSH

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstDerivativeAtNormalSet
section
open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem first_derivative_at_normal_set {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') (i0 s : ℕ) (hs : 1 ≤ s) (hj : i0 + s ≤ r)
    (hh : Matrix (Fin i0) (Fin i0) ℂ) (τ : ℂ) (hdet : hh.det ≠ 0) (hτ : τ ≠ 0) (x₁ : B.Mat k r)
    (hx₁G : x₁ ∈ B.GV k r) (hD₁ : Dmin k r z z' x₁ ⟨i0 + s, by omega⟩ ≠ 0)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi0 x₁ a p = if p.val < i0 + s then C3.Zb i0 s hh τ a.val p.val else 0)
    (hnfy : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      y0 x₁ a p = if r + k < p.val ∧ 2 * r + k - p.val < i0 + s then star (C3.Zb i0 s hh τ a.val (2 * r + k - p.val))
        else 0)
    (K : B.Mat k r → E) (hK : ∀ y ∈ B.GV k r, Dmin k r z z' y ⟨i0 + s, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K y)
    (hR : ∀ y (p q : Fin (2 * r + k + 1)), C3.InNp k r p q → EabH (Hpk k r) p q K y = C3.dpsiP k r z' p q • K y)
    (sx : B.Mat k r) (hsx : sx ∈ Sset k r z) (b : Bool) (Y : ℝ) :
    D.vLet k r z z' (i0 + s) hj (b, Y) 1 K (sx * x₁) =
      cLift s τ b • D.vLet k r z z' i0 (by omega) (b, Y) 0 K (sx * x₁) := by
  rw [vLet_left z z' hz hz' _ _ _ _ K sx x₁ hsx hx₁G, vLet_left z z' hz hz' _ _ _ _ K sx x₁ hsx hx₁G]
  have hsG : sx ∈ B.GV k r := Formalism.QuantumDeterminants.Sset_UH hsx
  set Dset : Set (Q.Mx k r) := {y | Dmin k r z z' y ⟨i0 + s, by omega⟩ ≠ 0} with hDset
  have hDo : IsOpen Dset := isOpen_ne_fun ((contDiff_Dmin z z' _).continuous) continuous_const
  have hx₁ : x₁ ∈ Q.Glev k r 0 ∩ Dset := ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx₁G, hD₁⟩
  have hDinv : ∀ y, Dmin k r z z' (sx * y) ⟨i0 + s, by omega⟩ = Dmin k r z z' y ⟨i0 + s, by omega⟩ := by
    intro y
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' sx hsx 1 (one_mem_Sset k r z') y ⟨i0 + s, by omega⟩
    rwa [Matrix.mul_one] at this
  have hK' : Q.SmoothLev k r 0 Dset (fun y => K (sx * y)) := by
    apply smoothLev_of_loc
    intro y hy
    refine loc_left hsG (hK _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hsG hy.1.1) ?_)
    rw [hDinv]; exact hy.2
  have hR' : ∀ g ∈ Q.Glev k r 0 ∩ Dset, ∀ p q, C3.InNp k r p q →
      Q.EH k r p q (fun y => K (sx * y)) g = C3.dpsiP k r z' p q • (fun y => K (sx * y)) g := by
    intro g _ p q hpq
    show EabH (Hpk k r) p q (fun y => K (sx * y)) g = _
    rw [AAInvW.ly_Eab_left]
    exact hR _ p q hpq
  cases b
  · have := letter_minus_component_one_eq_smul_component_zero hDo z z' i0 s hs hj hh τ hdet hτ x₁ hx₁ hx₁G hnf hnfy _ hK' hR' Y
    simp only [cLift, Bool.false_eq_true, if_false]
    exact this
  · have := letter_plus_component_one_eq_smul_component_zero hDo z z' i0 s hs hj hh τ hdet hτ x₁ hx₁ hnf _ hK' hR' Y
    simp only [cLift, if_true]
    exact this

theorem vLet_congr_level {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) {j₁ j₂ : ℕ} (hj : j₁ = j₂) (h₁ : j₁ ≤ r) (h₂ : j₂ ≤ r) (l : C.Letter) (e : Fin 2)
    (f : B.Mat k r → E) : D.vLet k r z z' j₁ h₁ l e f = D.vLet k r z z' j₂ h₂ l e f := by subst hj; rfl

theorem dmin_congr {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) {j₁ j₂ : ℕ} (hj : j₁ = j₂)
    (h₁ : j₁ < r + 2) (h₂ : j₂ < r + 2) : Dmin k r z z' g ⟨j₁, h₁⟩ = Dmin k r z z' g ⟨j₂, h₂⟩ := by subst hj; rfl

theorem coeff_recover {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (C : Fin n → V) (l : Fin n) :
    C l = ∑ i : Fin n, (Matrix.vandermonde (fun i : Fin n => (((i : ℕ) : ℝ) : ℂ)))⁻¹ l i •
      ∑ m : Fin n, ((((i : ℕ) : ℝ) : ℂ) ^ (m : ℕ)) • C m := by
  have hτ : Function.Injective (fun i : Fin n => (((i : ℕ) : ℝ) : ℂ)) := by
    intro a b hab
    simp only [Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  simp only [vand_row _ hτ l, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

section core

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem liftDeg_core {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ r)
    (h : C.LPt) (τ : ℂ) (ha : D.IsLocPt (h ++ [(s, τ)]) j)
    (w' : List C.Letter) (a' : Wd.Ix (Fin w'.length)) (b : Bool) (δ : ℝ) (g : B.Mat k (r - j))
    (X : Type) [MeasurableSpace X] (μ : Measure X) (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)))
    (sx : X → B.Mat k r) (x₁ : B.Mat k r) (hsx : ∀ x, sx x ∈ Sset k r T.base.z) (hx₁G : x₁ ∈ B.GV k r)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < D.ptSize h + s →
      xi0 x₁ a p = if p.val < D.ptSize h + s then
        C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a.val p.val else 0)
    (hnfy : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < D.ptSize h + s →
      y0 x₁ a p = if r + k < p.val ∧ 2 * r + k - p.val < D.ptSize h + s then
        star (C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a.val (2 * r + k - p.val)) else 0)
    (PC : (B.Mat k r → (Wq →L[ℂ] Wp)) → Prop)
    (hFub : ∀ H, PC H → Integrable (fun x => ℓ x (Kr T.base H (sx x * x₁))) μ ∧
      B.JF (T.bs j) (D.castF (by simp [ha.2]) (D.sliceAt k r T.base.z T.base.z' H (h ++ [(s, τ)]))) g =
        ∫ x, ℓ x (Kr T.base H (sx x * x₁)) ∂μ)
    (hPW : ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), PC (D.uwG k r T.base.z T.base.z' F j hj w e))
    (hloc : ∀ H, PC H → ∀ y ∈ B.GV k r, Dmin k r T.base.z T.base.z' y ⟨j, by omega⟩ ≠ 0 →
      CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (Kr T.base H) y)
    (hvl : ∀ H, PC H → ∀ y ∈ B.GV k r, Dmin k r T.base.z T.base.z' y ⟨j, by omega⟩ ≠ 0 → ∀ (l : C.Letter) (e : Fin 2),
      Kr T.base (D.vLet k r T.base.z T.base.z' j hj l e H) y = D.vLet k r T.base.z T.base.z' j hj l e (Kr T.base H) y) :
    ∃ c : Fin (j - s + 1) → (Wq →L[ℂ] Wp),
      c (Fin.last (j - s)) = cLift s τ b • B.JF (T.bs j) (KB.slv T F j hj w' (h ++ [(s, τ)]) ha.2 a') g ∧
      ∀ y : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha.2 (Fin.cons 1 a')) g =
        ∑ l : Fin (j - s + 1), ((y : ℂ) ^ (l : ℕ)) • c l := by
  classical
  set z := T.base.z with hzdef
  set z' := T.base.z' with hz'def
  have hz : inWb k r z := T.base.z_mem
  have hz' : inWb k r z' := T.base.z'_mem
  have hsz : D.ptSize (h ++ [(s, τ)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hs1 : 1 ≤ s := (ha.1 (s, τ) (by simp)).1
  have hτ : τ ≠ 0 := (ha.1 (s, τ) (by simp)).2
  have hjeq : j = D.ptSize h + s := by rw [← ha.2, hsz]
  set i0 := D.ptSize h with hi0
  have hloc_h : D.IsLocPt h (D.ptSize h) := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head ⟨ha.1, rfl⟩
  set hh := U.hMat (D.ptPerm h) (D.ptDiag h) with hhdef
  have hdet : hh.det ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _
    (fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hloc_h.1 q q.2)
  have hjr : i0 + s ≤ r := by omega
  have hDl : C3.Dlead i0 s hh τ (i0 + s) ≠ 0 := by
    rw [(Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh τ).2]
    refine mul_ne_zero (mul_ne_zero hdet (pow_ne_zero _ hτ)) ?_
    unfold C3.sgnW; exact pow_ne_zero _ (by norm_num)
  have hD₁ : Dmin k r z z' x₁ ⟨i0 + s, by omega⟩ ≠ 0 := by
    rw [dmin_nf z z' x₁ i0 s hh τ hjr hnf (i0 + s) le_rfl]; exact hDl
  have hDinv : ∀ (y x : B.Mat k r) (hyS : y ∈ Sset k r z) (n : ℕ) (hn : n < r + 2),
      Dmin k r z z' (y * x) ⟨n, hn⟩ = Dmin k r z z' x ⟨n, hn⟩ := by
    intro y x hyS n hn
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' y hyS 1 (one_mem_Sset k r z') x ⟨n, hn⟩
    rwa [Matrix.mul_one] at this
  have hyG : ∀ x, sx x * x₁ ∈ B.GV k r := fun x => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.QuantumDeterminants.Sset_UH (hsx x)) hx₁G
  have hyD : ∀ x, Dmin k r z z' (sx x * x₁) ⟨j, by omega⟩ ≠ 0 := by
    intro x
    rw [hDinv _ _ (hsx x), dmin_congr z z' x₁ hjeq _ (by omega)]
    exact hD₁
  set G := D.uwG k r z z' F j hj w' a' with hGdef
  have hG := hPW w' a'
  set KG := Kr T.base G with hKG

  have key : ∀ (x : X) (Y : ℝ), Kr T.base (D.uwG k r z z' F j hj ((b, Y) :: w') (Fin.cons 1 a')) (sx x * x₁) =
      cLift s τ b • D.vLet k r z z' i0 (by omega) (b, Y) 0 KG (sx x * x₁) := by
    intro x Y
    show Kr T.base (D.vLet k r z z' j hj (b, Y) 1 G) (sx x * x₁) = _
    rw [hvl G hG _ (hyG x) (hyD x), vLet_congr_level z z' hjeq hj hjr]
    refine first_derivative_at_normal_set z z' hz hz' i0 s hs1 hjr hh τ hdet hτ x₁ hx₁G hD₁ hnf hnfy KG (fun y hy hyd => ?_)
      (fun y p q hpq => kr_rule T.base G y p q hpq) (sx x) (hsx x) b Y
    exact hloc G hG y hy (by rw [dmin_congr z z' y hjeq _ (by omega)]; exact hyd)

  have poly : ∀ x : X, ∃ c : Fin (i0 + 1) → (Wq →L[ℂ] Wp), c (Fin.last i0) = KG (sx x * x₁) ∧
      ∀ Y : ℝ, D.vLet k r z z' i0 (by omega) (b, Y + δ) 0 KG (sx x * x₁) = ∑ l : Fin (i0 + 1), ((Y : ℂ) ^ (l : ℕ)) • c l := by
    intro x
    have hDi : Dmin k r z z' (sx x * x₁) ⟨i0, by omega⟩ ≠ 0 := by
      rw [hDinv _ _ (hsx x), dmin_nf z z' x₁ i0 s hh τ hjr hnf i0 (by omega),
        (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh τ).1]
      exact hdet
    obtain ⟨c₀, hc₀l, hc₀⟩ := vLet_poly (E := Wq →L[ℂ] Wp) (j := i0) (by omega) z z' KG (sx x * x₁) (hyG x) hDi
      (hloc G hG _ (hyG x) (hyD x)) b 0
    obtain ⟨c', hc'l, hsh⟩ := poly_shift i0 c₀ (δ : ℂ)
    refine ⟨c', by rw [hc'l, hc₀l, if_pos rfl], fun Y => ?_⟩
    rw [hc₀ (Y + δ), ← hsh (Y : ℂ)]
    push_cast
    rfl
  choose cf hcfl hcfY using poly
  have hcL : cLift s τ b ≠ 0 := by
    unfold cLift
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    cases b
    · simp only [Bool.false_eq_true, if_false]; exact inv_ne_zero ((map_ne_zero _).2 hτ)
    · simp only [if_true]; exact inv_ne_zero hτ

  have hnode : ∀ (x : X) (Y : ℝ), D.vLet k r z z' i0 (by omega) (b, Y) 0 KG (sx x * x₁) =
      (cLift s τ b)⁻¹ • Kr T.base (D.uwG k r z z' F j hj ((b, Y) :: w') (Fin.cons 1 a')) (sx x * x₁) := by
    intro x Y
    rw [key x Y, smul_smul, inv_mul_cancel₀ hcL, one_smul]
  set Vi := (Matrix.vandermonde (fun i : Fin (i0 + 1) => (((i : ℕ) : ℝ) : ℂ)))⁻¹ with hVi
  have hdl : ∀ (x : X) (l : Fin (i0 + 1)), ℓ x (cf x l) = ∑ i : Fin (i0 + 1), (Vi l i * (cLift s τ b)⁻¹) •
      ℓ x (Kr T.base (D.uwG k r z z' F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') (Fin.cons 1 a')) (sx x * x₁)) := by
    intro x l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_recover (i0 + 1) (cf x) l, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hcfY x ((i : ℕ) : ℝ), hnode x, map_smul, map_smul, smul_smul]
  have hint : ∀ l : Fin (i0 + 1), Integrable (fun x => ℓ x (cf x l)) μ := by
    intro l
    simp only [hdl]
    exact integrable_finsetSum _ (fun i _ => ((hFub (D.uwG k r z z' F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') (Fin.cons 1 a'))
      (hPW _ _)).1).smul (Vi l i * (cLift s τ b)⁻¹))
  set c' : Fin (i0 + 1) → (Wq →L[ℂ] Wp) := fun l => cLift s τ b • ∫ x, ℓ x (cf x l) ∂μ with hc'
  have hc'top : c' (Fin.last i0) = cLift s τ b • B.JF (T.bs j) (KB.slv T F j hj w' (h ++ [(s, τ)]) ha.2 a') g := by
    simp only [hc', hcfl]
    congr 1
    exact ((hFub G hG).2).symm
  have hc'exp : ∀ y : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha.2 (Fin.cons 1 a')) g =
      ∑ l : Fin (i0 + 1), ((y : ℂ) ^ (l : ℕ)) • c' l := by
    intro y
    have e1 := (hFub _ (hPW ((b, y + δ) :: w') (Fin.cons 1 a'))).2
    show B.JF (T.bs j) (D.castF _ (D.sliceAt k r z z' (D.uwG k r z z' F j hj ((b, y + δ) :: w') (Fin.cons 1 a'))
      (h ++ [(s, τ)]))) g = _
    rw [e1]
    have e2 : ∀ x, ℓ x (Kr T.base (D.uwG k r z z' F j hj ((b, y + δ) :: w') (Fin.cons 1 a')) (sx x * x₁)) =
        ∑ l : Fin (i0 + 1), (((y : ℂ) ^ (l : ℕ)) * cLift s τ b) • ℓ x (cf x l) := by
      intro x
      set_option synthInstance.maxHeartbeats 100000 in
        rw [key x (y + δ), hcfY x y, map_smul, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [map_smul, smul_smul, mul_comm]
    simp only [e2]
    rw [integral_finsetSum Finset.univ (f := fun (l : Fin (i0 + 1)) x => (((y : ℂ) ^ (l : ℕ)) * cLift s τ b) • ℓ x (cf x l))
      (fun l _ => (hint l).smul (((y : ℂ) ^ (l : ℕ)) * cLift s τ b))]
    apply Finset.sum_congr rfl
    intro l _
    rw [integral_smul, hc', smul_smul]
  have hcast : j - s + 1 = i0 + 1 := by omega
  refine ⟨fun l => c' (Fin.cast hcast l), ?_, fun y => ?_⟩
  · have : Fin.cast hcast (Fin.last (j - s)) = Fin.last i0 := Fin.ext (by simp <;> omega)
    simp only [this]
    exact hc'top
  · rw [hc'exp y]
    exact (Fintype.sum_equiv (finCongr hcast) _ _ (fun l => rfl)).symm

end core

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def PStdOfHeads : Prop := KB.RadHead → KB.HeadTop → KB.PStd

theorem pStdOfHeads : PStdOfHeads := fun hRH hHT =>
  pStdOfParts hRH hHT Formalism.FourierDecayAlt.P.module_form_eq_radial_form_one Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar

theorem pStdCpt_of_heads (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) :=
  pStd_cpt_of_parts hP hRH hHT Formalism.FourierDecayAlt.P.module_form_eq_radial_form_one Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar

end Formalism.FourierDecayAlt.P.PBO

theorem Formalism.FourierDecayAlt.P.standard_pairing_of_heads : Formalism.FourierDecayAlt.P.PBO.PStdOfHeads := Formalism.FourierDecayAlt.P.PBO.pStdOfHeads
end
end

