module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.AdjLawPf

variable {D : D7}

theorem inv_mul_gram (V : HSp D) : ((HSpace.gram V)⁻¹.map (incA D)) * ((HSpace.gram V).map (incA D)) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedAdjoint.gram_mul_inv V)

theorem gramI_conj (V : HSp D) : (((HSpace.gram V)⁻¹.map (incA D)).map (cA D))ᵀ = ((HSpace.gram V)⁻¹.map (incA D)) :=
  GlobalTheory.OrientedAdjoint.inv_conj (cA D) _ _ (GlobalTheory.OrientedAdjoint.gram_mul_inv V) (GlobalTheory.OrientedAdjoint.gram_conj V)

theorem conjT_mul {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) (B : Matrix (Fin n) (Fin k) (AE D)) :
    ((A * B).map (cA D))ᵀ = (B.map (cA D))ᵀ * (A.map (cA D))ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem conjT_conjT {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) : (((A.map (cA D))ᵀ).map (cA D))ᵀ = A := by
  ext i j; simp [GlobalTheory.DualPairCheck.cA_cA]

theorem adjO_eq (S T : HSp D) (y : WO T S) :
    (adjO S T y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      HMul.hMul (HMul.hMul ((HSpace.gram T)⁻¹.map (incA D)) ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose) ((HSpace.gram S).map (incA D)) := rfl

theorem adj_invol (S T : HSp D) (x : WO S T) : adjO S T (adjO T S x) = x := by
  rw [adjO_eq, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj]
  simp only [← Matrix.mul_assoc]
  rw [inv_mul_gram, Matrix.one_mul, Matrix.mul_assoc, inv_mul_gram, Matrix.mul_one]

theorem adj_add (S T : HSp D) (y y' : WO T S) : adjO S T (y + y') = adjO S T y + adjO S T y' := by
  rw [adjO_eq, adjO_eq, adjO_eq]
  have e : ((y + y' : WO T S) : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) =
      (y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) + (y' : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) := by
    ext i j; simp
  rw [e, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem hO_eq (S T : HSp D) (x y : WO S T) : hO S T x y = Matrix.trace (adjO T S y * x) := by
  rw [adjO_eq]
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem hO_herm (S T : HSp D) (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  rw [hO_eq, hO_eq]
  have e : cA D (Matrix.trace (adjO T S y * x)) = Matrix.trace (((adjO T S y * x).map (cA D))ᵀ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.trace_transpose]; simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]
  rw [e, conjT_mul, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj,
    adjO_eq, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

theorem hO_adj (S T : HSp D) (x y : WO T S) : hO S T (adjO S T x) (adjO S T y) = hO T S y x := by
  rw [hO_eq, hO_eq, adj_invol, Matrix.trace_mul_comm]

theorem adj_sympl (S T : HSp D) (y y' : WO T S) :
    symplO S T (adjO S T y) (adjO S T y') = -symplO T S y y' := by
  unfold symplO
  rw [hO_adj, ← hO_herm, ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem symplOH_adj (S T : HSp D) (y y' : WO T S) :
    symplOH S T (adjO S T y) (adjO S T y') = -symplOH T S y y' := by
  unfold symplOH; rw [adj_sympl, mul_neg]

end GlobalTheory.AdjLawPf

namespace GlobalTheory.AdjLawPf

variable {D : D7}

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by simp [Formalism.L2.Theta.mt]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

theorem conjT_gram (V : HSp D) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V g⁻¹ := by
  calc ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * (mt V g * mt V g⁻¹) := by
        rw [mt_mul_inv, Matrix.mul_one]
    _ = (((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * mt V g) * mt V g⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [GlobalTheory.DualPairCheck.mt_unit]

theorem gramI_conjT (V : HSp D) (h : GA D V) :
    ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ = mt V h * ((HSpace.gram V)⁻¹.map (incA D)) := by
  have k : ((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V h := by
    rw [conjT_gram, inv_inv]
  calc ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ = ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ * (((HSpace.gram V).map (incA D)) * ((HSpace.gram V)⁻¹.map (incA D))) := by
        rw [GlobalTheory.OrientedAdjoint.gram_mul_inv, Matrix.mul_one]
    _ = ((HSpace.gram V)⁻¹.map (incA D)) * (((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D))) * ((HSpace.gram V)⁻¹.map (incA D)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [k, ← Matrix.mul_assoc, inv_mul_gram, Matrix.one_mul]

theorem adj_act (S T : HSp D) (g : GA D S) (h : GA D T) (y : WO T S) :
    adjO S T (actO T S h g y) = actO S T g h (adjO S T y) := by
  unfold actO
  rw [adjO_eq, adjO_eq, conjT_mul, conjT_mul]
  simp only [← Matrix.mul_assoc]
  rw [gramI_conjT, Matrix.mul_assoc _ ((mt S g).map (cA D))ᵀ, conjT_gram]
  simp only [Matrix.mul_assoc]

theorem adj_ratW (S T : HSp D) (γ : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    adjO S T (ratW S T γ) = ratW T S (HMul.hMul (HMul.hMul (HSpace.gram T)⁻¹ (γ.map star)ᵀ) (HSpace.gram S)) := by
  have e : ((γ.map (incA D)).map (cA D))ᵀ = ((γ.map star)ᵀ).map (incA D) := by
    ext i j; simp [GlobalTheory.DualPairCheck.cA_incA]
  rw [adjO_eq]
  unfold ratW
  rw [e, Matrix.map_mul, Matrix.map_mul]

theorem adj_rat_of (S T : HSp D) (y : WO T S) (hy : y ∈ ratL S T) : adjO S T y ∈ ratL T S := by
  obtain ⟨γ, rfl⟩ := hy
  exact ⟨_, (adj_ratW S T γ).symm⟩

theorem adj_rat (S T : HSp D) (y : WO T S) : adjO S T y ∈ ratL T S ↔ y ∈ ratL S T :=
  ⟨fun h => by have := adj_rat_of T S _ h; rwa [adj_invol] at this, adj_rat_of S T y⟩

theorem adj_half (S T : HSp D) (e : AE D) (y : WO T S) (hy : IsHalf e y) : IsHalf (cA D e) (adjO S T y) := by
  intro i j
  have hy' : ∀ k l, cA D e * cA D (y k l) = cA D (y k l) := fun k l => by rw [← map_mul, hy]
  rw [adjO_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (incA D ((HSpace.gram T)⁻¹ i l) * incA D (HSpace.gram S k j)) * hy' k l

theorem adj_cont (S T : HSp D) : Continuous (adjO S T) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h : Continuous fun y : WO T S => ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D))ᵀ :=
    (continuous_id.matrix_map (GlobalTheory.HeckeConj.continuous_cA D)).matrix_transpose
  exact (continuous_const.matrix_mul h).matrix_mul continuous_const

set_option synthInstance.maxHeartbeats 400000 in
theorem adj_infPart (S T : HSp D) (u : WO T S) (hu : u.map (infPart D) = 0) : (adjO S T u).map (infPart D) = 0 := by
  have h0 : ∀ k l, infPart D (u k l) = 0 := fun k l => by
    have := congrFun (congrFun hu k) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  refine Matrix.ext fun i j => ?_
  show infPart D (adjO S T u i j) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    GlobalTheory.PlaceIdem.infPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem adj_finPart (S T : HSp D) (u : WO T S) (hu : u.map (finPart D) = 0) : (adjO S T u).map (finPart D) = 0 := by
  have h0 : ∀ k l, finPart D (u k l) = 0 := fun k l => by
    have := congrFun (congrFun hu k) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  refine Matrix.ext fun i j => ?_
  show finPart D (adjO S T u i j) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    GlobalTheory.PlaceIdem.finPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

def adjHom (S T : HSp D) : WO T S →+ WO S T := AddMonoidHom.mk' (adjO S T) (adj_add S T)

theorem conj_psi (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ a]
  simp

theorem adj_heis (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (y : WO T S) (f : WO S T → ℂ) :
    heisO ψ T S y (dag S T f) = dag S T (heisO ψ S T (adjO S T y) f) := by
  funext w
  simp only [heisO, dag, map_mul, adj_add, symplOH_adj, conj_psi ψ hψ, neg_neg]

theorem adj_theta (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ T S (dag S T f) := {
  quasi γ w := by
    simp only [dag]
    rw [adj_add, adj_ratW, hf.quasi, map_mul, conj_psi ψ hψ, ← adj_ratW, symplOH_adj]
    simp only [neg_neg]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap (adjHom S T), hUo.preimage (adj_cont S T), fun u hu h0 => ?_⟩
    rw [adj_heis ψ hψ]
    exact congrArg (dag S T) (hU (adjO S T u) hu (adj_infPart S T u h0))
  cont := Complex.continuous_conj.comp (hf.cont.comp (adj_cont S T))
  smooth k L hL hfin w := by
    have h := hf.smooth k ((adjHom S T).comp L) ((adj_cont S T).comp hL) (fun t => adj_finPart S T _ (hfin t))
      (adjO S T w)
    have e : (fun t => dag S T f (w + L t)) =
        fun t => Complex.conjCLE (f (adjO S T w + (adjHom S T).comp L t)) := by
      funext t; simp [dag, adj_add, adjHom]
    rw [e]
    exact Complex.conjCLE.contDiff.comp h }

theorem adjLaw : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, AdjLaw ψ S T := by
  intro D ψ hψ S T
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  exact { invol := adj_invol S T
          add := adj_add S T
          cont := adj_cont S T
          sympl := adj_sympl S T
          act := adj_act S T
          rat := adj_rat S T
          half := adj_half S T
          Heisenberg₂ := adj_heis ψ hn S T
          theta := adj_theta ψ hn S T }

end GlobalTheory.AdjLawPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InclTprodUpdate
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.FinTensor

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem inclK_injective (h : KSm M) : Function.Injective (inclK h) := by
  choose r hr using fun τ =>
    LinearMap.exists_leftInverse_of_injective (Submodule.inclusion (h τ))
      (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective (h τ)))
  have key : PiTensorProduct.map r ∘ₗ inclK h = LinearMap.id := by
    unfold inclK
    rw [← PiTensorProduct.map_comp]
    simp only [hr, PiTensorProduct.map_id]
  intro x y hxy
  calc x = (PiTensorProduct.map r ∘ₗ inclK h) x := by rw [key, LinearMap.id_apply]
    _ = (PiTensorProduct.map r ∘ₗ inclK h) y := by rw [LinearMap.comp_apply, hxy, ← LinearMap.comp_apply]
    _ = y := by rw [key, LinearMap.id_apply]

theorem incl_tprod (h : KSm M) (v : ∀ ρ, kFin M ρ) :
    inclT M (inclK h (PiTensorProduct.tprod ℂ v)) = PiTensorProduct.tprod ℂ fun ρ => (v ρ : M.H ρ) := by
  simp [inclT, inclK]

theorem incl_tprod_update (h : KSm M) (v : ∀ ρ, kFin M ρ) (τ : D.what₂.Tau) (u : kFin M τ) :
    inclT M (inclK h (PiTensorProduct.tprod ℂ (Function.update v τ u))) =
      PiTensorProduct.tprod ℂ (Function.update (fun ρ => (v ρ : M.H ρ)) τ (u : M.H τ)) := by
  rw [incl_tprod]
  congr 1
  funext ρ
  rcases eq_or_ne ρ τ with rfl | hρ
  · simp
  · simp [Function.update_of_ne hρ]

theorem act_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ ρ, M.H ρ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  simp only [actT, PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  rcases eq_or_ne ρ τ with rfl | hρ
  · simp
  · simp [Function.update_of_ne hρ]

theorem ell_update (w v : ∀ ρ, M.H ρ) (τ : D.what₂.Tau) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, v ρ⟫_ℂ := by
  have hs : ∀ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update v τ u ρ⟫_ℂ = ⟪w ρ, v ρ⟫_ℂ := fun ρ hρ => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
  simp only [ellT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]
  show ∏ ρ, ⟪w ρ, Function.update v τ u ρ⟫_ℂ = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl hs

private theorem hasDerivAt_ellT_actT_exp_tprod (h : KSm M) (τ : D.what₂.Tau)
    (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)) (ha : IsKAct M τ a)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (w : ∀ ρ, M.H ρ) (v : ∀ ρ, kFin M ρ) :
    HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M (inclK h (PiTensorProduct.tprod ℂ v)))))
      (ellT M w (inclT M (inclK h (intersection_update_fsHerm_neg_one τ (a X) (PiTensorProduct.tprod ℂ v))))) 0 := by
  have hd := ha.der X hX (v τ)
  have hi : HasDerivAt (fun t : ℝ => ⟪w τ, M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)⟫_ℂ)
      ⟪w τ, (a X (v τ) : M.H τ)⟫_ℂ 0 := by
    have hc := ((innerSL ℂ (w τ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simpa [Function.comp_def] using hc
  have e2 : ellT M w (inclT M (inclK h (intersection_update_fsHerm_neg_one τ (a X) (PiTensorProduct.tprod ℂ v)))) =
      ⟪w τ, (a X (v τ) : M.H τ)⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (v ρ : M.H ρ)⟫_ℂ := by
    rw [position_tprod, incl_tprod_update, ell_update]
  have e1 : (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M (inclK h (PiTensorProduct.tprod ℂ v))))) =
      fun t : ℝ => ⟪w τ, M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)⟫_ℂ *
        ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (v ρ : M.H ρ)⟫_ℂ := by
    funext t
    rw [incl_tprod, act_tprod, ell_update]
  rw [e1, e2]
  exact hi.mul_const _

theorem derT_mapFactor (h : KSm M) (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ))
    (ha : IsKAct M τ a) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (x : KT M) :
    DerT M τ X (inclK h x) (inclK h (intersection_update_fsHerm_neg_one τ (a X) x)) := by
  delta DerT
  intro w
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, smul_eq_mul]
    exact (hasDerivAt_ellT_actT_exp_tprod h τ a ha X hX w v).const_mul r
  | add x y hx hy =>
    simp only [map_add (f := _)]
    exact hx.add hy

theorem incl_mapFactor_kOp (h : KSm M) (τ : D.what₂.Tau) (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ maxCpt M τ)
    (x : KT M) : inclT M (inclK h (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x)) = actT M τ k (inclT M (inclK h x)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul]
    congr 1
    rw [position_tprod, incl_tprod_update, incl_tprod, act_tprod] <;> rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem kFinTensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (h : KSm M), Function.Injective (inclK h) ∧ (∀ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a → ∀ X ∈ lieAt V τ, ∀ x : KT M, DerT M τ X (inclK h x) (inclK h (intersection_update_fsHerm_neg_one τ (a X) x))) ∧ ∀ (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ maxCpt M τ) (x : KT M), inclT M (inclK h (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x)) = actT M τ k (inclT M (inclK h x)) := by
  intro D V S M τ h
  refine ⟨inclK_injective h, ?_, ?_⟩
  · intro a ha X hX x
    exact derT_mapFactor h τ a ha X hX x
  · intro k hk x
    exact incl_mapFactor_kOp h τ k hk x

end GlobalTheory.Chain.IoLift.FinTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinDual

theorem decomp : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (Kset ε) ρ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S → (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S) → ∀ v : H, IsKFin ε ρ v → v ∈ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
  classical
  intro n ε H _ _ ρ hU hirr
  have key : ∀ (d : ℕ) (F : Submodule ℂ H), FiniteDimensional ℂ F → Module.finrank ℂ F ≤ d →
      IsKStableOn ε ρ F → F ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
    intro d
    induction d with
    | zero =>
      intro F hF hd _
      rw [Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)]
      exact bot_le
    | succ d ih =>
      intro F hF hd hFK
      by_cases hF0 : F = ⊥
      · rw [hF0]; exact bot_le
      have hex : ∃ m, ∃ S : Submodule ℂ H, S ≤ F ∧ S ≠ ⊥ ∧ IsKStableOn ε ρ S ∧ Module.finrank ℂ S = m :=
        ⟨_, F, le_rfl, hF0, hFK, rfl⟩
      obtain ⟨S, hSF, hS0, hSK, hSm⟩ := Nat.find_spec hex
      haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSF
      have hirrS : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S := by
        intro S' hS' hS'K
        by_cases h0 : S' = ⊥
        · exact Or.inl h0
        right
        haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
        have h1 := Nat.find_min' hex ⟨S', hS'.trans hSF, h0, hS'K, rfl⟩
        exact Submodule.eq_of_le_of_finrank_le hS' (hSm ▸ h1)
      obtain ⟨Λ, hΛ⟩ := hirr S inferInstance hS0 hSK hirrS
      have hSle : S ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} :=
        (le_sSup (s := {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) hΛ).trans (le_iSup (fun Λ => sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) Λ)
      have hF'K : IsKStableOn ε ρ (Sᗮ ⊓ F) := by
        intro k hk v hv
        refine ⟨?_, hFK k hk v hv.2⟩
        show (ρ k) v ∈ Sᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 := GlobalTheory.Dec.FormF.inner_rep_K hU (Formalism.REAL.Kset_star ε hk) u v
        rw [star_star] at h1
        rw [← h1]
        exact (Submodule.mem_orthogonal S v).1 hv.1 _ (hSK _ (Formalism.REAL.Kset_star ε hk) u hu)
      haveI : FiniteDimensional ℂ (Sᗮ ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_right
      have hsup : S ⊔ Sᗮ ⊓ F = F := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hSF
      have hinf : S ⊓ (Sᗮ ⊓ F) = ⊥ :=
        eq_bot_iff.2 ((inf_le_inf_left S inf_le_left).trans (Submodule.inf_orthogonal_eq_bot S).le)
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq S (Sᗮ ⊓ F)
      rw [hsup, hinf, finrank_bot, add_zero] at hdim
      have hpos : 0 < Module.finrank ℂ S := Nat.pos_of_ne_zero fun h => hS0 (Submodule.finrank_eq_zero.1 h)
      have hle : F ≤ _ := hsup ▸ sup_le hSle (ih _ inferInstance (by omega) hF'K)
      exact hle
  intro v ⟨F, hF, hvF, hFK⟩
  exact key _ F hF le_rfl hFK hvF

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kIso (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) : Submodule ℂ H :=
  sSup {S | IsKTypeOf ε ρ Λ S}

theorem kIso_le (Λ : Fin n → ℝ) : kIso ε ρ Λ ≤ kFinVec ε ρ :=
  sSup_le fun S hS v hv => ⟨S, hS.1, hv, hS.2.1⟩

theorem kIso_orth (hU : IsURepOn (Kset ε) ρ) {Λ μ : Fin n → ℝ} (hne : μ ≠ Λ) :
    ∀ x ∈ kIso ε ρ Λ, ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq]
  refine Submodule.isOrtho_sSup_left.2 fun S hS => Submodule.isOrtho_sSup_right.2 fun T hT => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (GlobalTheory.Jet.MultGap.orth_of_ne hU hS hT hne)

theorem finset_orth (hU : IsURepOn (Kset ε) ρ) (s : Finset (Fin n → ℝ)) {μ : Fin n → ℝ} (hμ : μ ∉ s) :
    ∀ x ∈ s.sup (kIso ε ρ), ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq, Finset.sup_eq_iSup]
  refine Submodule.isOrtho_iSup_left.2 fun Λ => Submodule.isOrtho_iSup_left.2 fun hΛ => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (kIso_orth hU (fun e => hμ (e ▸ hΛ)))

theorem exists_finset (hd : ∀ v, IsKFin ε ρ v → v ∈ ⨆ Λ, kIso ε ρ Λ) (v : H) (hv : IsKFin ε ρ v) :
    ∃ s : Finset (Fin n → ℝ), v ∈ s.sup (kIso ε ρ) := by
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hd v hv)
  exact ⟨s, by rwa [Finset.sup_eq_iSup]⟩

end

section
variable {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}

theorem map_kIso_le {T : H →ₗ[ℂ] V} (hT : ∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y))
    (Λ : Fin n → ℝ) : (kIso ε ρ Λ).map T ≤ kIso ε π Λ := by
  rw [Submodule.map_le_iff_le_comap]
  refine sSup_le fun S hS => ?_
  rw [← Submodule.map_le_iff_le_comap]
  haveI := hS.1
  set Q : S →L[ℂ] V := LinearMap.toContinuousLinearMap (T ∘ₗ S.subtype) with hQdef
  have hR : S.map T = LinearMap.range (Q : S →ₗ[ℂ] V) := by
    rw [hQdef, LinearMap.coe_toContinuousLinearMap, LinearMap.range_comp, Submodule.range_subtype]
  by_cases hQ : Q = 0
  · rw [hR, hQ]; simp
  · rw [hR]
    refine le_sSup (GlobalTheory.Dec.FormF.rangeType n ε Λ H ρ S V π Q hS (fun k hk x y hxy => ?_) hQ)
    change T y = π k (T x)
    rw [hxy]
    exact hT k hk x ⟨S, hS.1, x.2, hS.2.1⟩

end

end GlobalTheory.KFinDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumTransportsHeisenbergMatrixCoeffs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilCoeff

theorem heis_coeff_eq : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (g : GA D V) (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), μ₀.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕₀ μ₀ → ∀ w₀ : WO V W, ∫ w in 𝓕₀, heisO ψ V W (actO V W g h w₀) (ω (g, h) f) w * starRingEnd ℂ (ω (g, h) f w) ∂μ₀ = ∫ w in 𝓕₀, heisO ψ V W w₀ f w * starRingEnd ℂ (f w) ∂μ₀ := by
  intro D V W ψ χS χT ω hω g h f hf μ₀ 𝓕₀ hμ h𝓕 w₀
  have hf1 := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hω.std V W).1 w₀ f hf
  rw [← hω.om_heis g h w₀ f hf]
  exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hω.std V W μ₀ 𝓕₀ hμ h𝓕 (ω (g, h))
    (fun f hf => hω.om_pres (g, h) f hf) (fun f hf => hω.om_unit μ₀ 𝓕₀ hμ h𝓕 (g, h) f hf) _ f hf1 hf

end GlobalTheory.WeilCoeff
end

