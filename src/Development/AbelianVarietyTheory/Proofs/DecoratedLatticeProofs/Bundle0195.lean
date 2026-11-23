module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0177
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOrthSummandSlicesSobolevBounded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0179
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChainHeckeParameter_twist_next_target_char : ∀ (D : D7) (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ), GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ = GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t := by
  first | exact @GlobalTheory.ChainOnto.chainPar_twist_chT | exact GlobalTheory.ChainOnto.chainPar_twist_chT | (intros; apply GlobalTheory.ChainOnto.chainPar_twist_chT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsPrimeWeightSizes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem GlobalTheory.CoreHt.sizes_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → (∀ u, 4 * L.sc.a < (((I.rec7 l Z).mem u).A.T : ℝ)) → Formalism.L2.Col.Sizes (B.primes X) B.wts L.sc.a := by
  intro B X I h l Z L CY hR hX' hx hT
  have hW := (GlobalTheory.Mem.wts_ok_and_sizes B X).2
  have hF := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).2
  obtain ⟨P⟩ := hR.1
  have hfN := GlobalTheory.ColumnNormCompare.SizeRows.f_mul_N_le_b P hR.2.2.2.1.1
  have hb1 := GlobalTheory.ColumnNormCompare.SizeRows.one_le_b L.sc
  refine ⟨hW.g_big, fun u => hT u, ?_, _root_.GlobalTheory.CoreHt.SpreadBound.spread_lamTrue_le I h l Z L CY hR hX' hx⟩
  have hab : 2 * L.sc.b ≤ L.sc.a := by
    show 2 * L.sc.b ≤ L.sc.x * L.sc.b
    nlinarith
  have hfN' : ((B.fields.f : ℝ)) * (B.R.N B.R.m : ℝ) ≤ L.sc.b := by
    rw [hF]; exact hfN
  push_cast
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointInfiniteMatricesEqOneOfFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}

def conjJAt (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) : X.Vpi u →ₗ[ℂ] ℂ where
  toFun η := star (tr.J η z)
  map_add' η η' := by simp [map_add (f := _)]
  map_smul' c η := by simp [map_smulₛₗ]

def rieszJ (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) : X.Vpi u :=
  (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap (conjJAt tr z))

theorem inner_rieszJ (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) (η : X.Vpi u) :
    ⟪η, rieszJ tr z⟫_ℂ = tr.J η z := by
  rw [← inner_conj_symm]
  simp [rieszJ, conjJAt]


variable (X) in
def RepM (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h : X.B.I.Gf) (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) : Prop :=
  ∀ j, X.B.I.fmat h *ᵥ Formalism.L2.SG.ColDict.qA X wt j = ∑ i, ιA.symm (M i j) • Formalism.L2.SG.ColDict.qA X wt i

end GlobalTheory.Core.Mi

end

namespace GlobalTheory.Core.Mi

section Helpers

variable {D : D7}

theorem unitaryAdelicPointFiniteMatrix_base_space_mul (a b : GA D (D.sp.X 0)) :
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a * b) =
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) b := by
  unfold GlobalTheory.AdForm.finM Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul, Matrix.map_mul]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem unitaryAdelicPointFiniteMatrix_base_space_one : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (1 : GA D (D.sp.X 0)) = 1 := by
  unfold GlobalTheory.AdForm.finM Formalism.L2.Theta.mt
  simp [Matrix.reindex_apply]

theorem unitaryAdelicPointInfiniteMatrices_base_space_mul (θ : InfFam D) (a b : GA D (D.sp.X 0)) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a * b) τ =
      GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) b τ := by
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = M.map ((θ τ).comp (infPart D)) := fun M => rfl
  rw [e, e, e, map_mul, Units.val_mul, Matrix.map_mul]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem unitaryAdelicPointInfiniteMatrices_base_space_one (θ : InfFam D) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (1 : GA D (D.sp.X 0)) τ = 1 := by
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = M.map ((θ τ).comp (infPart D)) := fun M => rfl
  rw [e, map_one, Units.val_one]
  simp [Matrix.reindex_apply]

theorem unitaryAdelicPointInfiniteMatrices_eq_one_of_finite (θ : InfFam D) (a : GA D (D.sp.X 0)) (ha : a ∈ GfC (D.sp.X 0)) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = 1 := by
  have h1 : Formalism.L2.Theta.infHom (D.sp.X 0) a = 1 := ha
  unfold Formalism.L2.Theta.infHom at h1
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have h2 := congrArg (fun x : GL (Fin (D.sp.X 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => ((x.1).map (θ τ))) h1
  simp only [MonoidHom.comp_apply, Units.val_one] at h2
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = (M.map (infPart D)).map (θ τ) := fun M => by ext; rfl
  rw [e]
  have h3 : ((Formalism.L2.Theta.matHom (D.sp.X 0)) a).1.map (infPart D) =
      ((Formalism.UG.bc (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom)
        ((Formalism.L2.Theta.matHom (D.sp.X 0)) a) : GL _ _).1 := rfl
  rw [h3, h2]
  simp [Matrix.reindex_apply]

end Helpers

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

theorem toH_mul {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D}
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) (a b : GA D A) :
    B.toH (a * b) = B.toH a * B.toH b := by
  unfold SBes.toH
  ext <;> simp [map_mul]

theorem RepM_cancel {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {wt : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {ιA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F}
    {h k : X.B.I.Gf} {A M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)}
    (hA : RepM X wt ιA h A) (hAM : RepM X wt ιA (h * k) (A * M)) : RepM X wt ιA k M := by
  intro j
  have hmul : X.B.I.fmat (h * k) = X.B.I.fmat h * X.B.I.fmat k := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have hinv : X.B.I.fmat h⁻¹ * X.B.I.fmat h = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : X.B.I.fmat h *ᵥ (X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j) =
      X.B.I.fmat h *ᵥ (∑ l, ιA.symm (M l j) • Formalism.L2.SG.ColDict.qA X wt l) := by
    rw [Matrix.mulVec_mulVec, ← hmul, hAM j, Matrix.mulVec_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec_smul, hA, Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hA l, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]
  calc X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j
      = X.B.I.fmat h⁻¹ *ᵥ (X.B.I.fmat h *ᵥ (X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j)) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = X.B.I.fmat h⁻¹ *ᵥ (X.B.I.fmat h *ᵥ (∑ l, ιA.symm (M l j) • Formalism.L2.SG.ColDict.qA X wt l)) := by rw [key]
    _ = _ := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

theorem span_rieszJ {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (tr : Formalism.L2.SG.ColDict.Transport X u F) :
    Submodule.span ℂ (Set.range fun y => rieszJ tr (F.val0.eY y)) = ⊤ := by
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro η hη
  apply tr.J_injective c
  rw [map_zero]
  funext z
  obtain ⟨y, rfl⟩ := F.val0.eY.surjective z
  rw [← inner_rieszJ]
  exact (Submodule.mem_orthogonal' _ _).1 hη _ (Submodule.subset_span ⟨y, rfl⟩)

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

theorem colDictL_eY_symm {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (c : (D.mem u).C.cls 0)
    (w : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) :
    Formalism.L2.SG.ColDict.colDictL X tr hK T c (F.val0.eY.symm w) = tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) w := by
  have : Formalism.L2.SG.ColDict.colDictL X tr hK T c (F.val0.eY.symm w) =
      tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) (F.val0.eY (F.val0.eY.symm w)) := rfl
  rw [this, Equiv.apply_symm_apply]

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSlice

variable {D : D7}

theorem symplOH_zero_right' (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem symplOH_zero_left' (S T : HSp D) (x : WO S T) : symplOH S T 0 x = 0 := by
  simp [symplOH, symplO, hO]

def shiftA {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) : WO S T →+ WO S T where
  toFun w := (o.resS T).symm (actO A T g⁻¹ h⁻¹ (o.resS T w).1, (o.resS T w).2)
  map_zero' := by simp [actO_eq]
  map_add' x y := by
    rw [map_add (f := _), Prod.fst_add, Prod.snd_add, ← map_add (f := _)]
    congr 1
    simp [actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem shiftA_apply {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T) :
    shiftA o T g h w = (o.resS T).symm (actO A T g⁻¹ h⁻¹ (o.resS T w).1, (o.resS T w).2) := rfl

theorem actO_shift (A T : HSp D) (g : GA D A) (h : GA D T) (u : WO A T) : actO A T g h (actO A T g⁻¹ h⁻¹ u) = u := by
  simp only [actO_eq, inv_inv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (mt T h), mt_mul_inv, Matrix.one_mul, mt_mul_inv, Matrix.mul_one]

theorem continuous_shiftA {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) :
    Continuous (shiftA o T g h) := by
  have h1 : Continuous fun w : WO S T => (o.resS T w).1 := continuous_fst.comp (o.continuous_resS T)
  have h2 : Continuous fun w : WO S T => (o.resS T w).2 := continuous_snd.comp (o.continuous_resS T)
  refine (o.continuous_resS_symm T).comp (Continuous.prodMk ?_ h2)
  simp only [actO_eq]
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const

theorem shiftA_fin {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T)
    (hw : w.map (finPart D) = 0) : (shiftA o T g h w).map (finPart D) = 0 := by
  rw [shiftA_apply, OrthDec.resS_symm_apply]
  simp only [OrthDec.resS_apply, actO_eq]
  rw [Matrix.map_add _ (map_add (finPart D))]
  simp only [Matrix.map_mul, hw, Matrix.zero_mul, Matrix.mul_zero, zero_add]

theorem shiftA_inf {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T)
    (hw : w.map (infPart D) = 0) : (shiftA o T g h w).map (infPart D) = 0 := by
  rw [shiftA_apply, OrthDec.resS_symm_apply]
  simp only [OrthDec.resS_apply, actO_eq]
  rw [Matrix.map_add _ (map_add (infPart D))]
  simp only [Matrix.map_mul, hw, Matrix.zero_mul, Matrix.mul_zero, zero_add]

theorem half (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (χ χ' : (AE D)ˣ →* Circle) (om : Om A T) (hom : IsWeilDatumO ψ A T χ χ' om)
    (p : GA D A × GA D T) :
    IsThetaFunO ψ S T fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 := by
  obtain ⟨g, h⟩ := p
  have hstd := hom.std
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hslice := (_root_.GlobalTheory.BoxSlice.main D ψ hstd S A B T o).2.2.2
  have hsob := (_root_.GlobalTheory.SliceForm.weil_slice_isSobForm D ψ θ hθ S A B T o).1 χ χ' om hom (g, h)
  refine _root_.GlobalTheory.ThetaMap.thetaMap D ψ hstd θ hθ S T S T (shiftA o T g h) (continuous_shiftA o T g h) (shiftA_fin o T g h)
    (shiftA_inf o T g h) (fun F x => om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1)
    ?_ ?_ ?_ f hf
  · have e : (fun F : WO S T → ℂ => om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T 0).2))) (o.resS T 0).1) =
        fun F => om (g, h) (fun u => F ((o.resS T).symm (u, 0))) 0 := by
      funext F
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    exact e ▸ hsob
  · intro F w hF
    funext x
    have hG := (hslice F hF).1 ((o.resS T x).2 + (o.resS T w).2)
    have hin : (fun u => heisO ψ S T (shiftA o T g h w) F ((o.resS T).symm (u, (o.resS T x).2))) =
        ψ (symplOH B T (o.resS T x).2 (o.resS T w).2) • heisO ψ A T (actO A T g⁻¹ h⁻¹ (o.resS T w).1)
          (fun u => F ((o.resS T).symm (u, (o.resS T x).2 + (o.resS T w).2))) := by
      funext u
      simp only [heisO, shiftA_apply, Pi.smul_apply, smul_eq_mul]
      rw [o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply]
      rw [← map_add (f := _), Prod.mk_add_mk, AddChar.map_add_eq_mul]
      ring
    show om (g, h) (fun u => heisO ψ S T (shiftA o T g h w) F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 = _
    rw [hin, map_smul, hom.om_heis g h _ _ hG, actO_shift]
    simp only [Pi.smul_apply, heisO, smul_eq_mul]
    rw [o.symplOH_resS, map_add (o.resS T) x w, AddChar.map_add_eq_mul]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  · intro F γ hF
    have hr : ratW T S γ ∈ ratL T S := ⟨γ, rfl⟩
    obtain ⟨ha, hb⟩ := (o.mem_ratL_resS T _).1 hr
    have hsl : (fun u => F ((o.resS T).symm (u, (o.resS T (ratW T S γ)).2))) =
        fun u => F ((o.resS T).symm (u, 0)) := by
      funext u
      have hb' : (o.resS T).symm (0, (o.resS T (ratW T S γ)).2) ∈ ratL T S := by
        refine (o.mem_ratL_resS T _).2 ?_
        simp only [AddEquiv.apply_symm_apply]
        exact ⟨zero_mem _, hb⟩
      obtain ⟨δ, hδ⟩ := hb'
      have hδ' : ratW T S δ = (o.resS T).symm (0, (o.resS T (ratW T S γ)).2) := hδ
      have e : (o.resS T).symm (u, (o.resS T (ratW T S γ)).2) = ratW T S δ + (o.resS T).symm (u, 0) := by
        rw [hδ', ← map_add (f := _), Prod.mk_add_mk, zero_add, add_zero]
      rw [e, hF.quasi δ, hδ', o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply, symplOH_zero_left', symplOH_zero_right', add_zero, neg_zero,
        AddChar.map_zero_eq_one, one_mul]
    show om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T (ratW T S γ)).2))) (o.resS T (ratW T S γ)).1 =
      om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T 0).2))) (o.resS T 0).1
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [hsl]
    obtain ⟨γa, hγa⟩ := ha
    have ea : (o.resS T (ratW T S γ)).1 = ratW T A γa + 0 := by rw [add_zero]; exact hγa.symm
    rw [ea, (hom.om_pres (g, h) _ ((hslice F hF).1 0)).quasi γa 0, symplOH_zero_right', neg_zero,
      AddChar.map_zero_eq_one, one_mul]

theorem resS_symm_swap {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (u : WO B T) (v : WO A T) :
    (o.symm.resS T).symm (u, v) = (o.resS T).symm (v, u) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply]; exact add_comm _ _

theorem weilSlice_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2 := by
  intro D ψ S A B T o f hf
  refine ⟨fun χ χ' om hom p => half D ψ S A B T o f hf χ χ' om hom p, fun χ χ' om hom p => ?_⟩
  have h2 := half D ψ S B A T o.symm f hf χ χ' om hom p
  have key : (fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2) =
      fun x => om p (fun u => f ((o.symm.resS T).symm (u, (o.symm.resS T x).2))) (o.symm.resS T x).1 := by
    funext x
    simp only [resS_symm_swap]
    rfl
  exact key ▸ h2

end GlobalTheory.WeilSlice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunctionStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_residue_ne_zero_of_simple_pole_lift_L_function : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ (D : D7) (S : Finset (FinPl D)) (r t : ℕ) (c par : GlobalTheory.LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (S : Set (FinPl D)) r t c par (GlobalTheory.LFun.val (F := D.host.F) χ) (GlobalTheory.LFun.val (F := D.host.F) χ) → ∀ (a b : ℕ) (Z : ℂ → ℂ) (C z : ℂ), C ≠ 0 → EqRight Z (fun s => GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / GlobalTheory.LFun.dSfun D.host.E (S : Set (FinPl D)) a b s * C) → CoeffAt Z ((t : ℂ) / 2) (-1) z → z ≠ 0 := by
  first | exact @GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole | exact GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole | (intros; apply GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole <;> assumption)
end

