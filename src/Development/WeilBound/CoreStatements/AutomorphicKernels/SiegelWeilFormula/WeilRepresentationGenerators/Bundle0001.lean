module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.HgSch
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

def zInv (z : InfinitePlace F → Fin d.m → Fin d.n → ℂ) : Iw d → ℝ :=
  fun i => if i.2.2.2 then (z i.1 i.2.1 i.2.2.1).re else (z i.1 i.2.1 i.2.2.1).im


variable (d) in
def zLE : (Iw d → ℝ) ≃ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) where
  toFun := zOf (d := d)
  invFun := zInv (d := d)
  map_add' u v := by
    funext w a j
    apply Complex.ext <;> simp [zOf]
  map_smul' c u := by
    funext w a j
    apply Complex.ext <;> simp [zOf]
  left_inv u := by
    funext i
    obtain ⟨w, a, j, b⟩ := i
    cases b <;> simp [zOf, zInv]
  right_inv z := by
    funext w a j
    apply Complex.ext <;> simp [zOf, zInv]

theorem hg_sch (R : RD d) {νf : Measure (Yf d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    {g : Yf d → ℂ} (hg' : g ∈ SB (Yf d)) : ∃ h : 𝓢(Vw d, ℂ), ⇑h = hg R νf f g := by
  obtain ⟨L, hL⟩ := KFock.archEquiv d R
  let Zc : Vw d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (Iw d) ℝ).trans (zLE d).toContinuousLinearEquiv
  let c : Vw d → Yf d → (Fin d.m × Fin d.n × Fin 2 → AF F) := fun u y k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (Zc u) k)) (y k) : AF F)
  have hc1 : ∀ u y, (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c u y k).1) = L.symm (Zc u) := by
    intro u y
    funext k
    exact RingEquiv.apply_symm_apply _ _
  have hjn : ∀ u y, jn R u y = d.cmb (c u y) := by
    intro u y
    refine (exists_jn R u y).unique ⟨arc_jn R u y, fin_jn R u y⟩ ⟨?_, ?_⟩
    · rw [arc_eq_iff]
      intro w
      rw [← hL (c u y) w, hc1, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    · funext k
      show (d.crd (d.cmb (c u y)) k).2 = y k
      rw [KFock.crd_cmb']
  haveI := hνf
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : BorelSpace (Yf d) := Pi.borelSpace
  have hint : ∀ g' ∈ SB (Yf d), Integrable (fun y => g' y * star (g y)) νf := by
    intro g' hg''
    have hc : Continuous (fun y => g' y * star (g y)) :=
      hg''.1.continuous.mul (continuous_star.comp hg'.1.continuous)
    exact hc.integrable_of_hasCompactSupport (hg''.2.mul_right (f' := fun y => star (g y)))
  have key : ∀ Φ ∈ schA F (Fin d.m × Fin d.n × Fin 2), (∀ u, Integrable (fun y => Φ (c u y) * star (g y)) νf) ∧
      ∃ h : 𝓢(Vw d, ℂ), ∀ u, h u = ∫ y, Φ (c u y) * star (g y) ∂νf := by
    intro Φ hΦ
    unfold schA at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hmem =>
      obtain ⟨φ, g', hg'', rfl⟩ := hmem
      have e : ∀ u y, pureA F φ g' (c u y) = φ (L.symm (Zc u)) * g' y := by
        intro u y
        simp only [pureA]
        rw [hc1]
      refine ⟨fun u => ?_, ⟨(∫ y, g' y * star (g y) ∂νf) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Zc.trans L.symm) φ,
        fun u => ?_⟩⟩
      · simp only [e, mul_assoc]
        exact (hint g' hg'').const_mul _
      · simp only [e, mul_assoc, integral_const_mul, SchwartzMap.smul_apply,
          SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, ContinuousLinearEquiv.trans_apply,
          smul_eq_mul]
        ring
    | zero => exact ⟨fun u => by simp, 0, fun u => by simp⟩
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      obtain ⟨i1, k1, e1⟩ := h₁
      obtain ⟨i2, k2, e2⟩ := h₂
      refine ⟨fun u => ?_, k1 + k2, fun u => ?_⟩
      · simp only [Pi.add_apply, add_mul]
        exact (i1 u).add (i2 u)
      · simp only [Pi.add_apply, add_mul, SchwartzMap.add_apply, e1, e2]
        rw [integral_add (i1 u) (i2 u)]
    | smul a Φ _ h =>
      obtain ⟨i1, k1, e1⟩ := h
      refine ⟨fun u => ?_, a • k1, fun u => ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact (i1 u).const_mul a
      · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, SchwartzMap.smul_apply, e1, integral_const_mul]
  obtain ⟨-, h, eh⟩ := key (f ∘ d.cmb) hf
  refine ⟨h, funext fun u => ?_⟩
  rw [eh u]
  show _ = ∫ y, f (jn R u y) * star (g y) ∂νf
  simp only [hjn, Function.comp_apply]

end PositivityTheory.SiegelWeilFormula.KFP.OswGen

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.MulCoordMem
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem arc_apply (R : RD d) (X : Mx F E d.m d.n) (i : Iw d) :
    arc R X i = if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im := rfl

theorem norm_arc_sq (R : RD d) (X : Mx F E d.m d.n) :
    ‖arc R X‖ ^ 2 = ∑ w, ∑ a, ∑ j, ‖R.loc w X a j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, arc_apply, if_true, Bool.false_eq_true, if_false,
    Real.norm_eq_abs, sq_abs]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem gauss_eq (R : RD d) (X : Mx F E d.m d.n) :
    ((Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℝ) : ℂ) = ∏ w, gs (2 * Real.pi) (R.loc w X) := by
  rw [Complex.ofReal_exp, norm_arc_sq]
  simp only [gs]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_neg_distrib]

def lin (a : Fin d.m) (j : Fin d.n) (b : Bool) : PX d.m d.n :=
  if b then MvPolynomial.C (1 / 2) * (MvPolynomial.X (a, j, false) + MvPolynomial.X (a, j, true))
  else MvPolynomial.C (-Complex.I / 2) * (MvPolynomial.X (a, j, false) - MvPolynomial.X (a, j, true))

theorem evX_lin (a : Fin d.m) (j : Fin d.n) (b : Bool) (z : Fin d.m → Fin d.n → ℂ) :
    evX (lin (d := d) a j b) z = ((if b then (z a j).re else (z a j).im : ℝ) : ℂ) := by
  cases b
  · simp only [lin, evX, Bool.false_eq_true, if_false, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
      if_true]
    apply Complex.ext <;> simp <;> ring
  · simp only [lin, evX, if_true, Bool.false_eq_true, if_false, map_mul, map_add (f := _), MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    apply Complex.ext <;> simp <;> ring

theorem fP_mul (P Q : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ) : fP (P * Q) u = evX P u * fP Q u := by
  simp only [fP, evX, map_mul]
  ring

theorem mul_coord_mem (R : RD d) (i : Iw d) {h : Mx F E d.m d.n → ℂ} (hh : h ∈ R.fock) :
    (fun X => ((arc R X i : ℝ) : ℂ) * h X) ∈ R.fock := by
  unfold RD.fock RD.fockOn at hh ⊢
  induction hh using Submodule.span_induction with
  | mem h hmem =>
    obtain ⟨P, g, hg, rfl⟩ := hmem
    apply Submodule.subset_span
    refine ⟨Function.update P i.1 (lin i.2.1 i.2.2.1 i.2.2.2 * P i.1), g, hg, ?_⟩
    funext X
    have e1 : ∏ w ∈ Finset.univ, fP (Function.update P i.1 (lin i.2.1 i.2.2.1 i.2.2.2 * P i.1) w) (R.loc w X) =
        fP (lin i.2.1 i.2.2.1 i.2.2.2 * P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.1), Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    have e2 : ∏ w ∈ Finset.univ, fP (P w) (R.loc w X) =
        fP (P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i.1)).symm
    dsimp only
    rw [e1, e2, fP_mul, evX_lin, arc_apply]
    ring
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext X
    simp
  | add h₁ h₂ _ _ i₁ i₂ =>
    convert Submodule.add_mem _ i₁ i₂ using 1
    funext X
    simp [mul_add]
  | smul a h _ i₁ =>
    convert Submodule.smul_mem _ a i₁ using 1
    funext X
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem poly_mem (R : RD d) (Q : MvPolynomial (Iw d) ℂ) {g : Yf d → ℂ} (hg : g ∈ SB (Yf d)) :
    (fun X => MvPolynomial.eval (fun i => ((arc R X i : ℝ) : ℂ)) Q * (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) *
      g (fin d X)) ∈ R.fock := by
  have base : (fun X => (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) * g (fin d X)) ∈ R.fock := by
    unfold RD.fock RD.fockOn
    apply Submodule.subset_span
    refine ⟨fun _ => 1, g, hg, ?_⟩
    funext X
    rw [gauss_eq]
    simp only [fP, evX, map_one, one_mul]
    rfl
  induction Q using MvPolynomial.induction_on with
  | C a =>
    convert Submodule.smul_mem _ a base using 1
    funext X
    simp only [MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
    ring
  | add p q hp hq =>
    convert Submodule.add_mem _ hp hq using 1
    funext X
    simp only [map_add, Pi.add_apply]
    ring
  | mul_X p i hp =>
    convert mul_coord_mem R i hp using 1
    funext X
    simp only [map_mul, MvPolynomial.eval_X]
    ring

end PositivityTheory.SiegelWeilFormula.KFP.OswGen

end
end

