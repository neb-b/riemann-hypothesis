module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ExistsMeanAdm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0047
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Assemble
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0034
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0048
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0018
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0038
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.Imports
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalWeilElements.ThetaW
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilOswgenHg
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def zInv_k (z : InfinitePlace F → Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ :=
  fun i => if i.2.2.2 then (z i.1 i.2.1 i.2.2.1).re else (z i.1 i.2.1 i.2.2.1).im
variable (d) in
def zLE_k : (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ) ≃ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (d := d)
  invFun := _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zInv_k (d := d)
  map_add' u v := by
    funext w a j
    apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k]
  map_smul' c u := by
    funext w a j
    apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k]
  left_inv u := by
    funext i
    obtain ⟨w, a, j, b⟩ := i
    cases b <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zInv_k]
  right_inv z := by
    funext w a j
    apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zInv_k]
theorem hg_sch_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg' : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) : ∃ h : 𝓢(_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d, ℂ), ⇑h = _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g := by
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  let Zc : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).trans (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zLE_k d).toContinuousLinearEquiv
  let c : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin d.m × Fin d.n × Fin 2 → AF F) := fun u y k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (Zc u) k)) (y k) : AF F)
  have hc1 : ∀ u y, (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c u y k).1) = L.symm (Zc u) := by
    intro u y
    funext k
    exact RingEquiv.apply_symm_apply _ _
  have hjn : ∀ u y, _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y = d.cmb (c u y) := by
    intro u y
    refine (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).unique ⟨_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k R u y, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R u y⟩ ⟨?_, ?_⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k]
      intro w
      rw [← hL (c u y) w, hc1, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    · funext k
      show (d.crd (d.cmb (c u y)) k).2 = y k
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb'_k]
  haveI := hνf
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  have hint : ∀ g' ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), Integrable (fun y => g' y * star (g y)) νf := by
    intro g' hg''
    have hc : Continuous (fun y => g' y * star (g y)) :=
      hg''.1.continuous.mul (continuous_star.comp hg'.1.continuous)
    exact hc.integrable_of_hasCompactSupport (hg''.2.mul_right (f' := fun y => star (g y)))
  have key : ∀ Φ ∈ schA F (Fin d.m × Fin d.n × Fin 2), (∀ u, Integrable (fun y => Φ (c u y) * star (g y)) νf) ∧
      ∃ h : 𝓢(_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d, ℂ), ∀ u, h u = ∫ y, Φ (c u y) * star (g y) ∂νf := by
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
  show _ = ∫ y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (g y) ∂νf
  simp only [hjn, Function.comp_apply]
end PositivityTheory.SiegelWeilFormula.KFP.OswGen
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilOswgenPoly
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem arc_apply_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) (i : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i = if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im := rfl
theorem norm_arc_sq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) :
    ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2 = ∑ w, ∑ a, ∑ j, ‖R.loc w X a j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.arc_apply_k, if_true, Bool.false_eq_true, if_false,
    Real.norm_eq_abs, sq_abs]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring
theorem gauss_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) :
    ((Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℝ) : ℂ) = ∏ w, gs (2 * Real.pi) (R.loc w X) := by
  rw [Complex.ofReal_exp, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.norm_arc_sq_k]
  simp only [gs]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_neg_distrib]
def lin_k (a : Fin d.m) (j : Fin d.n) (b : Bool) : PX d.m d.n :=
  if b then MvPolynomial.C (1 / 2) * (MvPolynomial.X (a, j, false) + MvPolynomial.X (a, j, true))
  else MvPolynomial.C (-Complex.I / 2) * (MvPolynomial.X (a, j, false) - MvPolynomial.X (a, j, true))
theorem evX_lin_k (a : Fin d.m) (j : Fin d.n) (b : Bool) (z : Fin d.m → Fin d.n → ℂ) :
    evX (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k (d := d) a j b) z = ((if b then (z a j).re else (z a j).im : ℝ) : ℂ) := by
  cases b
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k, evX, Bool.false_eq_true, if_false, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
      if_true]
    apply Complex.ext <;> simp <;> ring
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k, evX, if_true, Bool.false_eq_true, if_false, map_mul, map_add (f := _), MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    apply Complex.ext <;> simp <;> ring
theorem fP_mul_k (P Q : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ) : fP (P * Q) u = evX P u * fP Q u := by
  simp only [fP, evX, map_mul]
  ring
theorem mul_coord_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (i : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) {h : Mx F E d.m d.n → ℂ} (hh : h ∈ R.fock) :
    (fun X => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ) * h X) ∈ R.fock := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.fock _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn at hh ⊢
  induction hh using Submodule.span_induction with
  | mem h hmem =>
    obtain ⟨P, g, hg, rfl⟩ := hmem
    apply Submodule.subset_span
    refine ⟨Function.update P i.1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1), g, hg, ?_⟩
    funext X
    have e1 : ∏ w ∈ Finset.univ, fP (Function.update P i.1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) w) (R.loc w X) =
        fP (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.1), Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    have e2 : ∏ w ∈ Finset.univ, fP (P w) (R.loc w X) =
        fP (P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i.1)).symm
    dsimp only
    rw [e1, e2, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.fP_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.evX_lin_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.arc_apply_k]
    ring
  | zero =>
    convert Submodule.zero_mem _ using 1
    ext X
    simp
  | add h₁ h₂ _ _ i₁ i₂ =>
    convert Submodule.add_mem _ i₁ i₂ using 1
    funext X
    simp [mul_add]
  | smul a h _ i₁ =>
    convert Submodule.smul_mem _ a i₁ using 1
    ext X
    simp [smul_eq_mul, mul_comm, mul_assoc]
theorem poly_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Q : MvPolynomial (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℂ) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) :
    (fun X => MvPolynomial.eval (fun i => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ)) Q * (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) *
      g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
  have base : (fun X => (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.fock _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn
    apply Submodule.subset_span
    refine ⟨fun _ => 1, g, hg, ?_⟩
    funext X
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.gauss_eq_k]
    simp only [fP, evX, map_one, one_mul]
    rfl
  induction Q using MvPolynomial.induction_on with
  | C a =>
    convert Submodule.smul_mem _ a base using 1
    ext X
    simp [smul_eq_mul, mul_assoc]
  | add p q hp hq =>
    convert Submodule.add_mem _ hp hq using 1
    ext X
    simp [add_mul]
  | mul_X p i hp =>
    convert _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.mul_coord_mem_k R i hp using 1
    ext X
    simp only [map_mul, MvPolynomial.eval_X]
    ring
end PositivityTheory.SiegelWeilFormula.KFP.OswGen
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoAdm
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_meanAdm_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) :
    ∃ Λ ∈ (adeleClass F).adm d.κ, ∀ Ψ ∈ d.sch,
      Λ Ψ = (d.μ.real d.D)⁻¹ • ∫ g in d.D, thetaSum F (d.S g Ψ) ∂d.μ := by
  obtain ⟨l, hl, hlθ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.exists_lth_k d
  have hpres : ∀ g, ∀ Ψ ∈ d.sch, d.S g Ψ ∈ d.sch := fun g Ψ hΨ => d.ok.dbl.lin.pres g Ψ hΨ
  have hfun : ∀ Ψ ∈ d.sch, (fun g => l (d.S g Ψ)) = fun g => thetaSum F (d.S g Ψ) :=
    fun Ψ hΨ => funext fun g => hlθ _ (hpres g Ψ hΨ)
  have hint : ∀ Ψ ∈ d.sch, IntegrableOn (fun g => l (d.S g Ψ)) d.D d.μ := fun Ψ hΨ => by
    rw [hfun Ψ hΨ]; exact _root_.PositivityTheory.SiegelWeilFormula.Tauto.intOn_S_k hS hP hT d hΨ
  set c : ℝ := (d.μ.real d.D)⁻¹ with hc
  let L0 : d.sch →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => c • ∫ g in d.D, l (d.S g Ψ.1) ∂d.μ
      map_add' := fun Ψ Ψ' => by
        simp only [Submodule.coe_add, map_add (f := _)]
        rw [integral_add (hint _ Ψ.2) (hint _ Ψ'.2), smul_add]
      map_smul' := fun a Ψ => by
        simp only [SetLike.val_smul, map_smul, RingHom.id_apply, smul_eq_mul]
        rw [integral_const_mul, mul_smul_comm] }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend L0
  have hΛv : ∀ Ψ (hΨ : Ψ ∈ d.sch), Λ Ψ = c • ∫ g in d.D, l (d.S g Ψ) ∂d.μ := fun Ψ hΨ => by
    have := congrArg (fun L => L ⟨Ψ, hΨ⟩) hΛ
    simpa [L0] using this
  refine ⟨Λ, fun gf hgf => ?_, fun Ψ hΨ => by rw [hΛv Ψ hΨ, hfun Ψ hΨ]⟩
  choose Th hTh using fun h : UA σ d.A.J => d.ok.dbl.lin.adm h l hl gf hgf
  have hmem : ∀ f : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f gf ∈ d.sch :=
    fun f => Submodule.subset_span ⟨f, gf, hgf, rfl⟩
  have hTv : ∀ h f, Th h f = thetaSum F (d.S h (pureA F f gf)) := fun h f => by
    rw [← hTh h f, LinearMap.comp_apply, hlθ _ (hpres h _ (hmem f))]
  haveI : BarrelledSpace ℂ (SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ) := _root_.GlobalTheory.schwartzMap_barrelledSpace _
  have hUE : UniformEquicontinuous ((↑) ∘ Th) := (norm_withSeminorms ℂ ℂ).banach_steinhaus fun _ f => by
    obtain ⟨C, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.bdd_S_k hS hP hT d (hmem f)
    refine ⟨C, ?_⟩
    rintro _ ⟨h, rfl⟩
    simpa [hTv] using hC h
  have hpa : ∀ f f' : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ,
      pureA F (f + f') gf = pureA F f gf + pureA F f' gf := fun f f' => funext fun x => by
    simp [pureA, add_mul]
  have hps : ∀ (a : ℂ) (f : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ),
      pureA F (a • f) gf = a • pureA F f gf := fun a f => funext fun x => by
    simp [pureA, mul_assoc]
  let Lf : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f => Λ (pureA F f gf)
      map_add' := fun f f' => by rw [hpa, map_add (f := _)]
      map_smul' := fun a f => by rw [hps, map_smul]; rfl }
  have hLf : ∀ f, Lf f = c • ∫ g in d.D, Th g f ∂d.μ := fun f => by
    show Λ (pureA F f gf) = _
    rw [hΛv _ (hmem f)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show l (d.S g (pureA F f gf)) = Th g f
    rw [← hTh g f]; rfl
  have hfin : d.μ d.D < ⊤ := (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom
  have hpos : 0 < d.μ.real d.D := by
    haveI := (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).cnt
    haveI := d.ok.haar
    exact ENNReal.toReal_pos (fd_ne d.ok.dom) hfin.ne
  have hcont : Continuous Lf := by
    refine continuous_of_continuousAt_zero Lf.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.equicontinuousAt_iff_right.1 (hUE.equicontinuous 0)) (ε / 2) (half_pos hε)] with f hf
    rw [dist_zero_right]
    show ‖Lf f‖ < ε
    rw [hLf]
    have hb : ∀ g ∈ d.D, ‖Th g f‖ ≤ ε / 2 := fun g _ => by
      have := (hf g).le
      simpa [dist_comm] using this
    calc ‖c • ∫ g in d.D, Th g f ∂d.μ‖ ≤ c * (ε / 2 * d.μ.real d.D) := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
          gcongr
          exact norm_setIntegral_le_of_norm_le_const hfin hb
      _ = ε / 2 := by rw [hc]; field_simp
      _ < ε := half_lt_self hε
  exact ⟨⟨Lf, hcont⟩, fun f => rfl⟩
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictAssemble
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
def RelRealP_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf →
  ∀ (x : d.G) (t u : GL (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 →
  ∀ η : E, η ≠ 0 → (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) →
  ∃ (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) (l : InfinitePlace F → ℝ) (εs : InfinitePlace F → Fin d.m → Bool)
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
    (∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y)) ∧
    (∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star) ∧
    (∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1) ∧
    (∀ Y, Φg Y = d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ)) ∧
    (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ ∧ Gen.IsPlaces σ d.B.ψ θ l ∧ Gen.IsFrames (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) θ εs fr ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin Φg (Gen.phiInf θ l fr g P) Φf
theorem relReal_k : _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.RelRealP_k := by
  intro F E _ _ _ _ _ σ d R Φ P gf hP x t u _ η hη herm
  obtain ⟨Φf, Φv, hpf, hpr⟩ := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.pure_prod_of'_k R Φ P gf hP u η (thW d.B) (thW_th' d.B) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη) (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w)
    (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη) (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_gc_k d u η hη w) (fun _ => -1) (fun _ => by norm_num)
  refine ⟨thW d.B, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη, fun _ => -1, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k R η, _, Φf, Φv, thW_th' d.B, fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w,
    fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_gc_k d u η hη w, fun _ => rfl, ⟨fun w => decide (0 < (((d.B.emb w).1 η / R.ζ) * ((R.sg w : ℤ) : ℂ)).re), rfl⟩,
    _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isCharAF_of_good_k d.B d.ok.good, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isPlaces_thW'_k d.B d.ok.good,
    _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isFrames_of'_k R η hη d.ok.good.cm herm (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.eta_zeta'_k R hη herm) (thW d.B) (thW_th' d.B) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη)
      (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w), hpf, hpr⟩
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylBase
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem std_k : IsStd d.B.ψ := d.ok.good.std
include d in
theorem cm_k : IsCMExt F E σ := d.ok.good.1
theorem hS_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (fun (g : UA σ d.A.J) x => mat g * x) d.S := d.ok.dbl.lin
theorem hO_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om := d.ok.dbl.weil.2.1
theorem hR_k : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) d.dd d.χ
    (diagCols (Fin d.n)) d.om := d.ok.dbl.weil.2.2
theorem mat_mul_inv_k (g : UA σ d.A.J) : mat g * mat g⁻¹ = 1 := by
  show g.1.1 * (g⁻¹).1.1 = 1
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
end PositivityTheory.SiegelWeilFormula.tweyl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwvThetaW
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isW_rat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) : w ∈ rat2 σ d.Y := by
  refine PositivityTheory.SiegelWeilFormula.kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
  rw [(hw : inFrame d.b w = _)]
  ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp
theorem thetaW_k : _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaW_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun ε w hw Φ hΦ => ?_, GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ⟩
  exact ⟨d.ok.dbl.weil.2.1.pres w Φ hΦ, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_rational_invariant d w (_root_.PositivityTheory.SiegelWeilFormula.TW.ThetaWPf.isW_rat_k d hw) Φ hΦ⟩
end PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilPairLocalFactor
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pair_local_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  first | exact @_root_.GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport_k | exact _root_.GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport_k | (intros; apply _root_.GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport_k <;> assumption)
end
end

