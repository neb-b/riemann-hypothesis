module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.SpCharpoly

theorem charpoly_blockDiag {m o R : Type*} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] [CommRing R] (B : o → Matrix m m R) :
    (Matrix.blockDiagonal B).charpoly = ∏ k, (B k).charpoly := by
  have e : Matrix.charmatrix (Matrix.blockDiagonal B) =
      Matrix.blockDiagonal (fun k => Matrix.charmatrix (B k)) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [Matrix.charpoly, e, Matrix.det_blockDiagonal]
  rfl

theorem charpoly_map_diagEnd {n m : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (c : Fin m → ℂ) :
    LinearMap.charpoly (TensorProduct.map f (diagEnd c)) = ∏ i, LinearMap.charpoly (c i • f) := by
  classical
  set b := Pi.basisFun ℂ (Fin n)
  have e : LinearMap.toMatrix (Pi.basisFun ℂ (Fin m)) (Pi.basisFun ℂ (Fin m)) (diagEnd c) =
      Matrix.diagonal c := by
    ext i j
    simp [Matrix.diagonal_apply, Pi.single_apply]
  rw [← LinearMap.charpoly_toMatrix _ (b.tensorProduct (Pi.basisFun ℂ (Fin m))),
    TensorProduct.toMatrix_map, e]
  have e2 : Matrix.kroneckerMap (· * ·) (LinearMap.toMatrix b b f) (Matrix.diagonal c) =
      Matrix.blockDiagonal fun i => LinearMap.toMatrix b b (c i • f) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      map_smul, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [mul_comm]
  rw [e2, charpoly_blockDiag]
  exact Finset.prod_congr rfl fun i _ => LinearMap.charpoly_toMatrix _ _

end GlobalTheory.WeilDeligne.SpCharpoly

namespace GlobalTheory.WeilDeligne

theorem charPol_lpTw_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), (x.lpTw 0).lpChar (WD.lpSp (h := h) 1) = x ∧ ∀ (l : ℕ) (σ : Weil h), ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) l)).charPol σ = ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
  intro E Ω _ _ _ _ _ A w h x
  refine ⟨?_, fun l σ => ?_⟩
  · rw [WD.lpTw_zero]
    induction x using WD.ind with
    | hP n a =>
      rw [WD.lpSp, WD.lpChar_mk]
      refine WD.sound (WDRep.Iso.symm ⟨(TensorProduct.rid ℂ (Fin n → ℂ)).symm ≪≫ₗ
        TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm,
        fun σ v => ?_, fun v => ?_⟩)
      · have : (WDRep.sp (h := h) 1).ρ σ = 1 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [WDRep.spEig]
        rw [WDRep.tensor_ρ, this]
        simp
      · have : (WDRep.sp (h := h) 1).N = 0 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [shiftEnd_apply]
        rw [WDRep.tensor_N, this]
        simp
  · induction x using WD.ind with
    | hP n a =>
      have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
      rw [WD.lpSp, WD.lpTw_mk, WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
        SpCharpoly.charpoly_map_diagEnd]
      change _ = ∏ j ∈ Finset.range l, ((WD.mk a).lpTw (j : ℕ)).charPol σ
      rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => ((WD.mk a).lpTw (j : ℕ)).charPol σ)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.tw_ρ, smul_smul, ← mul_zpow, WDRep.spEig,
        coe_qPow, ← Complex.cpow_add _ _ hq, ← Complex.ofReal_add, sub_add_cancel]

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneParamDualListSumAbsTwistSpecialStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l : List (WD h), (sumList l).lpDual = sumList (l.map WD.lpDual)) ∧ (∀ (y : WD h) (s : ℝ), (y.lpTw s).lpDual = y.lpDual.lpTw (-s)) ∧ ∀ (y : WD h) (n : ℕ), (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
  intro E Ω _ _ _ _ _ A w h
  have dual_sp (y : WD h) (n : ℕ) :
      (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
    induction y using WD.ind with
    | hP m a =>
      rw [WD.lpSp, WD.lpChar_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpChar_mk]
      exact WD.sound ((GlobalTheory.WDDual.iso_tensor_dual a (WDRep.sp (h := h) n)).symm.trans
        ((WDRep.Iso.refl a.dual).tensor (GlobalTheory.WDDual.iso_sp_dual (h := h) n)))
  exact ⟨GlobalTheory.WDDual.WDClass.lpDual_sumList, GlobalTheory.WDDual.WDClass.lpDual_lpTw,
    dual_sp⟩
end

