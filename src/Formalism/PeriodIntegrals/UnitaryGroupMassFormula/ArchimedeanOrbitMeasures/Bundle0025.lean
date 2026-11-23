module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousThetaInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0022

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DKForm
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

theorem hasFDerivAt_conj_exp {ι : Type} [Fintype ι] {n : ℕ}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    ∃ D : EuclideanSpace ℝ ι →L[ℝ] (Fin n → ℂ),
      HasFDerivAt (fun y => (A * NormedSpace.exp (L y) * B) *ᵥ w) D 0 ∧ ∀ y, D y = (A * L y * B) *ᵥ w := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  let Lc : EuclideanSpace ℝ ι →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap L
  let h : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun M => (A * M * B) *ᵥ w
      map_add' := fun M N => by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
      map_smul' := fun r M => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.smul_sum, mul_assoc] }
  let hc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap h
  have hexp : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (Lc 0) := by
    rw [map_zero]; exact hasFDerivAt_exp_zero
  have h1 := hc.hasFDerivAt.comp (0 : EuclideanSpace ℝ ι) (hexp.comp (0 : EuclideanSpace ℝ ι) Lc.hasFDerivAt)
  refine ⟨hc.comp ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).comp Lc), h1, fun y => rfl⟩

theorem dKForm_holds : DKForm := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL x v
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  let Φ : TupI X →+ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) :=
    { toFun := fun Y v b i => PI.AprimeInfU.thetaInf X v (Y b i)
      map_zero' := by funext v b i; exact map_zero _
      map_add' := by intro Y Z; funext v b i; exact map_add _ _ _ }
  have hsa : ∀ z z', (tupCoord X).symm (z + z') = (tupCoord X).symm z + (tupCoord X).symm z' := by
    intro z z'; apply (tupCoord X).injective; rw [tupCoord_add]; simp
  let T0 : EuclideanSpace ℝ (KapI X) →+ TupI X :=
    { toFun := (tupCoord X).symm
      map_zero' := by
        have h := hsa 0 0
        rw [add_zero] at h
        simpa using h
      map_add' := hsa }
  let Ψ0 := Φ.comp T0
  have hc0 : Continuous Ψ0 := by
    refine continuous_pi fun v => continuous_pi fun b => continuous_pi fun i => ?_
    exact (continuous_thetaInf X v).comp ((continuous_apply i).comp ((continuous_apply b).comp
      (tupCoord X).symm.continuous))
  let Ψ := Ψ0.toRealLinearMap hc0
  have hΨ : ∀ z v b i, Ψ z v b i = PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) := fun _ _ _ _ => rfl
  have hinj : Function.Injective Ψ := by
    intro z z' h
    apply (tupCoord X).symm.injective
    funext b i
    have key : ∀ v, PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) =
        PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z' b i) := by
      intro v
      rw [← hΨ, ← hΨ, h]
    exact sub_eq_zero.1 (thetaInf_inj X _ fun v => by rw [map_sub, key v, sub_self])
  have hcbi : Fintype.card (Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex,
      Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Ainf X.B.I.F)
        (Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2)), Fintype.card_fin]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (KapI X)) =
      Module.finrank ℝ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) := by
    simp only [finrank_euclideanSpace, Fintype.card_prod, hcbi, Module.finrank_pi_fintype,
      Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
    ring
  let Ψe := LinearMap.linearEquivOfInjective (Ψ : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] _) hinj hdim
  have hΨe : ∀ Z : TupI X, tupCoord X Z = Ψe.symm (Φ Z) := by
    intro Z
    apply Ψe.injective
    rw [LinearEquiv.apply_symm_apply, LinearMap.linearEquivOfInjective_apply]
    show Φ (T0 (tupCoord X Z)) = Φ Z
    simp [T0]
  have hG : ∀ x v b, (fun i => Φ (kap0 X hb c L x • Y0 X u') v b i) =
      ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (L x v) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
        fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    intro x v b
    funext i
    show PI.AprimeInfU.thetaInf X v ((X.toInf hb (c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) • Y0 X u') b i) = _
    rw [theta_act]
    have hu : uMat ((c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) v) =
        uMat (c v) * NormedSpace.exp (L x v) * uMat (c v)⁻¹ := by
      have e := expU_val (X.B.I.ε v) (L x v) (hL.1 x v).1
      simp only [uMat, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at e ⊢
      rw [e]
    rw [hu]
    simp only [Matrix.mul_assoc]

  have hD : ∀ v b, ∃ Dvb : EuclideanSpace ℝ ι →L[ℝ] (Fin X.B.I.n → ℂ),
      HasFDerivAt (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) Dvb 0 ∧
        ∀ y, Dvb y = ((X.B.I.P v * uMat (c v)) * L y v * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    intro v b
    obtain ⟨Dvb, h1, h2⟩ := hasFDerivAt_conj_exp ((LinearMap.proj v : (InfinitePlace X.B.I.F →
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) (X.B.I.P v * uMat (c v)) (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)
      (fun j => X.B.I.φ v (tupH (frameOf X u') b j))
    refine ⟨Dvb, ?_, fun y => h2 y⟩
    have e : (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) = fun x =>
        ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (((LinearMap.proj v : (InfinitePlace X.B.I.F →
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) x) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
      funext x
      exact hG x v b
    rw [e]
    exact h1
  choose Dv hDv1 hDv2 using hD
  let DD : EuclideanSpace ℝ ι →L[ℝ] (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) :=
    ContinuousLinearMap.pi fun v => ContinuousLinearMap.pi fun b => Dv v b
  have hGd : HasFDerivAt (fun x => Φ (kap0 X hb c L x • Y0 X u')) DD 0 :=
    hasFDerivAt_pi.2 fun v => hasFDerivAt_pi.2 fun b => hDv1 v b
  have hK : KapOrb X u' (kap0 X hb c L) = fun x => Ψe.symm (Φ (kap0 X hb c L x • Y0 X u')) := by
    funext x
    exact hΨe _
  have hKd : HasFDerivAt (KapOrb X u' (kap0 X hb c L))
      (Ψe.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp DD) 0 := by
    rw [hK]
    exact Ψe.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp (0 : EuclideanSpace ℝ ι) hGd
  rw [hKd.fderiv]
  have hΦ : Φ ((tupCoord X).symm (Ψe.symm (DD x))) = DD x := by
    have h1 : Ψe (Ψe.symm (DD x)) = DD x := Ψe.apply_symm_apply (DD x)
    rw [LinearMap.linearEquivOfInjective_apply] at h1
    exact h1
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  ext i b
  have e1 : (fun j => PI.AprimeInfU.thetaInf X v ((tupCoord X).symm (Ψe.symm (DD x)) b j)) = DD x v b :=
    funext fun j => congrFun (congrFun (congrFun hΦ v) b) j
  have hY0 : (fun j => PI.AprimeInfU.thetaInf X v (Y0 X u' b j)) = fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    funext j
    rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]
  show ((X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v ((tupCoord X).symm (Ψe.symm (DD x)) b j)) i =
    (uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b
  rw [e1, show DD x v b = Dv v b x from rfl, hDv2]
  have eR : (uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b =
      ((uMat (c v) * L x v * uMat (c v)⁻¹) *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j))) i := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    show ((X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y0 X u' b j)) k = _
    rw [hY0]
    rfl
  have hM : (X.B.I.P v)⁻¹ * (X.B.I.P v * uMat (c v) * L x v * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) =
      uMat (c v) * L x v * uMat (c v)⁻¹ * (X.B.I.P v)⁻¹ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu,
      Matrix.one_mul, Matrix.mul_assoc (uMat (c v) * L x v)]
  rw [eR, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MuBridgeB
section
noncomputable section

namespace PI.AprimeInfW.MuB

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix ComplexConjugate

open Classical

variable {D : D7} (X : HidaSetting D)

abbrev BrI : Type := InfinitePlace X.B.I.F × Fin X.B.I.n × Fin (D.R.rS + 1 + D.R.rS) × Bool

theorem reimV_apply {V : Type} {n m : ℕ} (M : V → Matrix (Fin n) (Fin m) ℂ) (p : V × Fin n × Fin m × Bool) :
    reimV M p = if p.2.2.2 then (M p.1 p.2.1 p.2.2.1).re else (M p.1 p.2.1 p.2.2.1).im := rfl

theorem reimV_addB {V : Type} {n m : ℕ} (A B : V → Matrix (Fin n) (Fin m) ℂ) :
    reimV (A + B) = reimV A + reimV B := by
  ext p
  by_cases h : p.2.2.2 <;> simp [reimV, h]

def bAdd : EuclideanSpace ℝ (KapI X) →+ EuclideanSpace ℝ (BrI X) :=
  AddMonoidHom.mk' (fun x => reimV (fun v => betaV X v ((tupCoord X).symm x))) fun x y => by
    rw [← reimV_addB]
    congr 1
    funext v
    rw [tupCoord_symm_add, betaV_add]
    rfl

theorem continuous_betaV (v : InfinitePlace X.B.I.F) (i : Fin X.B.I.n) (b : Fin (D.R.rS + 1 + D.R.rS)) :
    Continuous fun Y : TupI X => betaV X v Y i b := by
  simp only [betaV, Matrix.of_apply, Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul
    ((continuous_thetaInf X v).comp ((continuous_apply j).comp (continuous_apply b)))

theorem continuous_bAdd : Continuous (bAdd X) := by
  show Continuous fun x => reimV (fun v => betaV X v ((tupCoord X).symm x))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
  rcases p with ⟨v, i, b, s⟩
  cases s
  · exact Complex.continuous_im.comp ((continuous_betaV X v i b).comp (tupCoord X).symm.continuous)
  · exact Complex.continuous_re.comp ((continuous_betaV X v i b).comp (tupCoord X).symm.continuous)

def bL : EuclideanSpace ℝ (KapI X) →L[ℝ] EuclideanSpace ℝ (BrI X) :=
  (bAdd X).toRealLinearMap (continuous_bAdd X)

theorem bL_apply (x : EuclideanSpace ℝ (KapI X)) : bL X x = reimV (fun v => betaV X v ((tupCoord X).symm x)) :=
  rfl

def qD (p : BrI X) : ℝ := 2 * (if X.B.I.ε p.1 p.2.1 then 1 else -1)

theorem betaI_q (x y : EuclideanSpace ℝ (KapI X)) : betaI X x y = ∑ p : BrI X, qD X p * bL X x p * bL X y p := by
  rw [betaI_bridge]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, bL_apply, reimV_apply, qD, if_true, Bool.false_eq_true,
    if_false]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem card_cbi : Fintype.card
    (Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) = 2 := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  rw [← Module.finrank_eq_card_chooseBasisIndex, Module.finrank_baseChange, X.B.I.cm.deg2]

theorem card_BrI : Fintype.card (BrI X) = Fintype.card (KapI X) := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, card_cbi]
  ring

def eI : BrI X ≃ KapI X := Fintype.equivOfCardEq (card_BrI X)

def U : EuclideanSpace ℝ (BrI X) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (KapI X) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (eI X)

def fK : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
  (U X).toLinearEquiv.toLinearMap ∘ₗ (bL X).toLinearMap

theorem fK_apply (x : EuclideanSpace ℝ (KapI X)) (k : KapI X) : fK X x k = bL X x ((eI X).symm k) := by
  simp [fK, U, Equiv.piCongrLeft'_apply]


open Classical in
def Bq : Matrix (KapI X) (KapI X) ℝ := fun k l => bL X (EuclideanSpace.single l 1) ((eI X).symm k)

open Classical in
theorem toMatrix_fK : LinearMap.toMatrix (EuclideanSpace.basisFun (KapI X) ℝ).toBasis
    (EuclideanSpace.basisFun (KapI X) ℝ).toBasis (fK X) = Bq X := by
  ext k l
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, fK_apply]
  rfl

theorem det_fK : LinearMap.det (fK X) = (Bq X).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (KapI X) ℝ).toBasis, toMatrix_fK]

open Classical in
theorem matI_eq : matI X = (Bq X)ᵀ * Matrix.diagonal (fun k => qD X ((eI X).symm k)) * Bq X := by
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  show betaI X _ _ = _
  rw [betaI_q, ← (eI X).symm.sum_comp]
  refine Finset.sum_congr rfl fun k' _ => ?_
  simp only [Bq]
  ring

theorem det_matI : (matI X).det = (Bq X).det ^ 2 * ∏ p : BrI X, qD X p := by
  rw [matI_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    (eI X).symm.prod_comp (fun p => qD X p)]
  ring

theorem abs_prod_qD : |∏ p : BrI X, qD X p| =
    ((2 : ℝ) ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F))) ^ 2 := by
  rw [Finset.abs_prod]
  have h : ∀ p : BrI X, |qD X p| = 2 := by
    intro p
    unfold qD
    split_ifs <;> norm_num
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_mul]
  congr 1
  ring

theorem sqrt_matI (hd : (matI X).det ≠ 0) :
    (Bq X).det ≠ 0 ∧ Real.sqrt |(matI X).det| =
      |(Bq X).det| * 2 ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F)) := by
  have hdm := det_matI X
  refine ⟨fun h0 => hd (by rw [hdm, h0]; ring), ?_⟩
  rw [hdm, abs_mul, abs_prod_qD, abs_pow, sq_abs]
  have hnn : 0 ≤ |(Bq X).det| * (2 : ℝ) ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F)) :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (by norm_num) _)
  rw [← Real.sqrt_sq hnn, mul_pow, sq_abs]

end PI.AprimeInfW.MuB

namespace PI.AprimeInfW

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets
open Classical

theorem muBridge_holds : MuBridge := by
  intro D X u' ψ hT μinf νinf fibInf hP
  have hd : (matI X).det ≠ 0 := matNDH_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨hB0, hsq⟩ := MuB.sqrt_matI X hd
  have hfd : LinearMap.det (MuB.fK X) ≠ 0 := by rw [MuB.det_fK]; exact hB0
  have hfun : (fun Y => reimV (fun v => betaV X v Y)) = (MuB.U X).symm ∘ (MuB.fK X) ∘ (tupCoord X) := by
    funext Y
    simp [MuB.fK, MuB.bL_apply]
  have hUm : Measurable (MuB.U X).symm := (MuB.U X).symm.continuous.measurable
  have hfKm : Measurable (MuB.fK X) := (LinearMap.continuous_of_finiteDimensional (MuB.fK X)).measurable
  have htm : Measurable (tupCoord X) := (tupCoord X).continuous.measurable
  have e1 : μinf.map ((MuB.U X).symm ∘ (MuB.fK X) ∘ (tupCoord X)) =
      ((μinf.map (tupCoord X)).map (MuB.fK X)).map (MuB.U X).symm := by
    rw [Measure.map_map hUm hfKm, Measure.map_map (hUm.comp hfKm) htm]
    rfl
  rw [hfun, e1, densMu_holds X u' ψ hT μinf νinf fibInf hP, Measure.map_smul,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hfd, Measure.map_smul, Measure.map_smul,
    ((MuB.U X).symm.measurePreserving).map_eq, smul_smul, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hsq,
    MuB.det_fK]
  congr 2
  have ha : |(MuB.Bq X).det| ≠ 0 := abs_ne_zero.2 hB0
  rw [abs_inv]
  field_simp
  all_goals first | exact hUm.aemeasurable | exact hfKm.aemeasurable

theorem betaIso_holds : BetaIso := by
  intro D X
  have hinj : Function.Injective (MuB.fK X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hb : MuB.bL X x = 0 := by
      have := congrArg (MuB.U X).symm hx
      simpa [MuB.fK] using this
    have hβ : ∀ v, betaV X v ((tupCoord X).symm x) = betaV X v 0 := by
      intro v
      have h0 : betaV X v 0 = 0 := by
        have := betaV_add X v 0 0
        rw [add_zero] at this
        exact left_eq_add.1 this
      rw [h0]
      ext i b
      have hre := congrArg (fun z : EuclideanSpace ℝ (MuB.BrI X) => z (v, i, b, true)) hb
      have him := congrArg (fun z : EuclideanSpace ℝ (MuB.BrI X) => z (v, i, b, false)) hb
      simp only [MuB.bL_apply, MuB.reimV_apply, if_true, Bool.false_eq_true, if_false] at hre him
      exact Complex.ext (by simpa using hre) (by simpa using him)
    have h1 := betaV_inj X _ _ hβ
    have h2 : tupCoord X 0 = 0 := by
      have := tupCoord_add X 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [← (tupCoord X).apply_symm_apply x, h1, h2]
  have hsurj : Function.Surjective (MuB.fK X) := LinearMap.injective_iff_surjective.1 hinj
  let eF := LinearEquiv.ofBijective (MuB.fK X) ⟨hinj, hsurj⟩
  refine ⟨(eF.trans (MuB.U X).symm.toLinearEquiv).toContinuousLinearEquiv, fun Y => ?_⟩
  show (MuB.U X).symm (MuB.fK X (tupCoord X Y)) = _
  simp [MuB.fK, MuB.bL_apply]

end PI.AprimeInfW
end
end

