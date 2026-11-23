module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothVectorMatrixCoeffIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalDictionarySplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeltaOrthonormalCoordsMemLatticeOfFiniteRational
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedTransLat

open Matrix

variable {D : D7}

theorem AA_le_Iid (a : D.host.E) (ha : a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)) :
    a ∈ GlobalTheory.InertSign.Iid D D.host.ccK := by
  have ha' : a ∈ D.host.ccE * D.host.AA0 := by rw [← Host.AA]; exact ha
  refine FractionalIdeal.mul_induction_on ha' (fun x hx y hy => ?_) (fun x y hx hy => add_mem hx hy)
  rw [Host.ccE] at hx
  obtain ⟨x', hx', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    exact Submodule.subset_span ⟨c, hc, y, hy, rfl⟩
  | zero => simp
  | add u w _ _ hu hw => rw [map_add (f := _), add_mul]; exact add_mem hu hw
  | smul o u _ hu =>
    rw [smul_eq_mul, map_mul, mul_assoc]
    exact Submodule.smul_mem _ o hu

theorem coord_genMap {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (a : D.host.E) (s' : Fin S.rank → D.host.E) (t' : Fin T.rank → D.host.E) :
    (frT⁻¹).1 * GlobalTheory.LatVac.genMap S T a (frS.1 *ᵥ s') (frT.1 *ᵥ t') * frS.1 = a • Matrix.vecMulVec t' (star s') := by
  have hS' : frS.1ᴴ * S.gram * frS.1 = 1 := hS
  have e : ∀ (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E),
      GlobalTheory.LatVac.genMap S T a s t = a • Matrix.vecMulVec t (star s ᵥ* S.gram) := by
    intro s t
    ext i j
    simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.vecMul,
      dotProduct, smul_eq_mul, Pi.star_apply, mul_assoc]
  rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_mulVec,
    Units.inv_mul, Matrix.one_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hS',
    Matrix.vecMul_one]

theorem vecMulVec_mem_homL {N N' : ℕ} {Ls : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lt : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D Ls) {s' : Fin N → D.host.E} (hs' : s' ∈ Ls)
    {t' : Fin N' → D.host.E} (ht' : t' ∈ Lt) : Matrix.vecMulVec t' (star s') ∈ homL D Ls Lt := by
  refine GlobalTheory.ThetaLatImage.mem_homL.2 fun x hx => ?_
  obtain ⟨o, ho⟩ := (((GlobalTheory.InertSign.sd_iff D Ls).1 hLs).2.2 x).1 hx s' hs'
  have e : Matrix.vecMulVec t' (star s') *ᵥ x = o • t' := by
    funext i
    rw [Pi.smul_apply, ← algebraMap_smul D.host.E o (t' i), ho, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, GlobalTheory.InertSign.hE, Pi.star_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [bridge_star_holds D.R D.host]; ring
  rw [e]
  exact Lt.smul_mem o ht'

theorem coord_mem_RL {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    {Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hLs : SD D Ls) {w : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hw : w ∈ GlobalTheory.LatVac.latRat S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt)) :
    (frT⁻¹).1 * w * frS.1 ∈ GlobalTheory.InertSign.RL D D.host.ccK Ls Lt := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, s, ⟨s', hs', rfl⟩, t, ⟨t', ht', rfl⟩, rfl⟩ := hw
    rw [coord_genMap frS frT hS]
    exact Submodule.subset_span ⟨a, AA_le_Iid a ha, _, vecMulVec_mem_homL hLs hs' ht', rfl⟩
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem hx

theorem mem_La_of_finRat : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), SD D Ls → SD D Lt → ∀ (δ : ℂ) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E), GlobalTheory.VacUnique.finRat S T v ∈ latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) → δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b) ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  intro D S T frS frT hS hT Ls Lt hLs hLt δ v hv
  obtain ⟨ΛS, hΛS, hSD⟩ := _root_.GlobalTheory.MovedDict.isSelfDualC_inV S frS hS Ls hLs
  obtain ⟨ΛT, hΛT, hTD⟩ := _root_.GlobalTheory.MovedDict.isSelfDualC_inV T frT hT Lt hLt
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  rw [← hΛS, ← hΛT] at hv
  have hrat := (GlobalTheory.AdForm.RatLat.finTens_mem_iff hψ hSD hTD v).1 hv
  rw [hΛS, hΛT] at hrat
  have hpt := GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (coord_mem_RL frS frT hS hLs hrat) 1
  rw [one_smul] at hpt
  convert hpt using 1
  funext τ a b
  rw [GlobalTheory.ThetaLatImage.pt_apply]
  have hi : (GlobalTheory.FockPos.frAt frT τ)⁻¹ = (frT⁻¹).1.map (tauE D τ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv' : Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) = v.map (tauE D τ) := rfl
  show δ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b = _
  rw [hi, hv', GlobalTheory.FockPos.frAt, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

end GlobalTheory.MovedTransLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelAdjointEqInvFiniteDimensional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

namespace GlobalTheory.RepAdj

theorem rep_adjoint_eq_inv : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      LinearMap.adjoint (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) = (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) := by
  intro D V S M τ _ g hg
  have hfd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : IsUnit (Formalism.REAL.Jm (M.ε τ)) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ))
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact ((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ |>.mul (M.fr_unit τ)
  have hgi : g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := GlobalTheory.SmVec.inv_mem_UH hG hg
  have hgu : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)
  refine ⟨hgi, ?_⟩
  have hU := (M.ds τ).2.2.1
  have m1 : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg
  have m2 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hgi
  have hprod : (M.fr τ * g⁻¹ * (M.fr τ)⁻¹) * (M.fr τ * g * (M.fr τ)⁻¹) = 1 := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hfd]
    rw [← Matrix.mul_assoc g⁻¹ g, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hfd]
  have hcomp : ∀ x, M.rep τ g⁻¹ (M.rep τ g x) = x := by
    intro x
    have := hU.1.2 _ m2 _ m1
    rw [hprod, hU.1.1] at this
    have hx := congrArg (fun T : M.H τ →L[ℂ] M.H τ => T x) this
    simpa [DSModel.rep] using hx.symm
  have hiso : ∀ x y, inner ℂ (M.rep τ g⁻¹ x) (M.rep τ g⁻¹ y) = inner ℂ x y := by
    have hn : ∀ v, ‖(M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) v‖ = ‖v‖ := fun v => hU.2.1 _ m2 v
    intro x y
    exact (LinearMap.norm_map_iff_inner_map_map (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ)).1 hn x y
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  have := hiso x (M.rep τ g y)
  rw [hcomp] at this
  simpa using this

end GlobalTheory.RepAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanSignatureFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLoc

theorem isEnum_cast' {S : SPar} {n k : ℕ} (h : k = n) {lam : Fin n → ℝ} {ε : Fin n → Bool} (hE : IsEnum S lam ε) :
    IsEnum S (fun i : Fin k => lam (Fin.cast h i)) (fun i => ε (Fin.cast h i)) := by
  subst h
  simpa using hE

theorem UH_mul' {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH H) (hb : b ∈ Formalism.QuantumDeterminants.UH H) :
    a * b ∈ Formalism.QuantumDeterminants.UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem conj_mul' {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B) (x y : Matrix (Fin n) (Fin n) ℂ) :
    B * (x * y) * B⁻¹ = B * x * B⁻¹ * (B * y * B⁻¹) := by
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).1 hB)
  calc B * (x * y) * B⁻¹ = B * x * (B⁻¹ * B) * y * B⁻¹ := by rw [hBi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = B * x * B⁻¹ * (B * y * B⁻¹) := by simp only [Matrix.mul_assoc]

end GlobalTheory.PackLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBoundMatrixBySymplecticFormHomAtRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SymplBound

theorem symplAt_pick {D : D7} (S T : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (i : Fin T.rank) (j : Fin S.rank) (w : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ
      (((tauE D τ D.host.xi0)⁻¹ * w) • ((gramAt D T τ)⁻¹ * Matrix.single i j (1 : ℂ) * gramAt D S τ)) X =
      2 * (w * starRingEnd ℂ (X i j)).re := by
  have hc : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hT := GlobalTheory.SmoothAutCheck.gramAt_unit T τ
  have hS := GlobalTheory.SmoothAutCheck.gramAt_unit S τ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
  congr 2
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have e1 : (gramAt D S τ)⁻¹ * Xᴴ * gramAt D T τ * ((gramAt D T τ)⁻¹ * Matrix.single i j (1 : ℂ) * gramAt D S τ) =
      (gramAt D S τ)⁻¹ * (Xᴴ * Matrix.single i j (1 : ℂ)) * gramAt D S τ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (gramAt D T τ), mul_nonsing_inv _ hT, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, mul_nonsing_inv _ hS, Matrix.one_mul,
    Matrix.trace_mul_single]
  simp only [Matrix.conjTranspose_apply, MulOpposite.op_one, one_smul, Complex.star_def]
  field_simp

theorem bound : ∀ (D : D7) (S T : HSp D) (τ : D.what₂.Tau), ∃ (n : ℕ) (zs : Fin n → Matrix (Fin T.rank) (Fin S.rank) ℂ) (κ : ℝ), ∀ X : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∑ i, ∑ j, ‖X i j‖ ≤ κ * ∑ l, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (zs l) X| := by
  intro D S T τ
  let g : Fin 2 × Fin T.rank × Fin S.rank → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun p =>
    ((tauE D τ D.host.xi0)⁻¹ * Complex.I ^ (p.1 : ℕ)) •
      ((gramAt D T τ)⁻¹ * Matrix.single p.2.1 p.2.2 (1 : ℂ) * gramAt D S τ)
  let e := Fintype.equivFin (Fin 2 × Fin T.rank × Fin S.rank)
  refine ⟨_, fun l => g (e.symm l), 1, fun X => ?_⟩
  rw [one_mul, Equiv.sum_comp e.symm (fun p => |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (g p) X|),
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  simp only [g, symplAt_pick, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul]
  have h1 : (starRingEnd ℂ (X i j)).re = (X i j).re := Complex.conj_re _
  have h2 : (Complex.I * starRingEnd ℂ (X i j)).re = (X i j).im := by simp
  rw [h1, h2, abs_mul, abs_mul, abs_two]
  have := Complex.norm_le_abs_re_add_abs_im (X i j)
  nlinarith [abs_nonneg (X i j).re, abs_nonneg (X i j).im]

end GlobalTheory.SymplBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactFiniteComponentsOfAnnihilatorOpenSu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.MixModel GlobalTheory.Unf
noncomputable section

namespace GlobalTheory.AnnihMat

variable {D : D7}

theorem hO_single (S T : HSp D) (w : WO S T) (i : Fin T.rank) (j : Fin S.rank) (e : AE D) :
    hO S T w (Matrix.single i j (cA D e)) = e * (gA T ⬝ w ⬝ giA S) i j := by
  have ha : adj (Matrix.single i j (cA D e)) = Matrix.single j i e := by
    ext a b
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
    by_cases h1 : i = b <;> by_cases h2 : j = a <;> simp [h1, h2, GlobalTheory.DualPairCheck.cA_cA]
  rw [hO_eq_trace, ha, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_single_mul, smul_eq_mul]

end GlobalTheory.AnnihMat


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.AnnihMat GlobalTheory.AnnihBox in
theorem GlobalTheory.AnnihMat.annihilator_inBox_full : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ Q : Set (WO S T), IsCompact Q ∧ ∀ w : WO S T, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1) → GlobalTheory.Unf.InBox Q w := by
  intro D ψ hψ S T U hU
  let g : Fin T.rank → Fin S.rank → (AE D →+ WO S T) := fun i j =>
    { toFun := fun c => Matrix.single i j (cA D c)
      map_zero' := by simp
      map_add' := fun a b => by simp [Matrix.single_add] }
  have hg : ∀ i j, Continuous (g i j) := fun i j => by
    show Continuous fun c => Matrix.single i j (cA D c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.single_apply]
    split_ifs
    · exact continuous_cA'
    · exact continuous_const
  have hK := fun i j => GlobalTheory.CondBound.annihilator_finPart_compact D ψ hψ (U.comap (g i j)) (hU.preimage (hg i j))
  choose K hKc hK using hK
  let R : WO S T → WO S T := fun k => giA T ⬝ k.map (fun z => incA D D.host.xi0⁻¹ * z) ⬝ gA S
  have hR : Continuous R :=
    (continuous_const.matrix_mul (continuous_id.matrix_map (continuous_const.mul continuous_id))).matrix_mul
      continuous_const
  refine ⟨R '' (Set.univ.pi fun i => Set.univ.pi fun j => K i j : Set (WO S T)),
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => hKc i j).image hR, ?_⟩
  intro w hw
  have hy : ∀ i j, ∃ k ∈ K i j, finPart D (incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k) = 0 := fun i j =>
    hK i j _ fun c hc hc0 => by
      have h1 : (Matrix.single i j (cA D c)).map (infPart D) = 0 := by
        ext a b
        simp only [Matrix.map_apply, Matrix.single_apply, Matrix.zero_apply]
        split_ifs
        · exact infPart_cA' c hc0
        · exact map_zero _
      have h2 := hw (Matrix.single i j (cA D c)) hc h1
      have e3 : incA D D.host.xi0 * hO S T w (Matrix.single i j (cA D c)) =
          incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j * c := by rw [hO_single]; ring
      unfold symplO at h2
      rwa [e3] at h2
  choose k hk hk0 using hy
  refine ⟨R (Matrix.of k), ⟨Matrix.of k, fun i _ j _ => hk i j, rfl⟩, ?_⟩
  have hsub : ∀ a b : WO S T, R (a - b) = R a - R b := fun a b => by
    simp only [R]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    simp [mul_sub]
  have hx' : R (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j) = w := by
    simp only [R]
    have e : (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j).map
        (fun z => incA D D.host.xi0⁻¹ * z) = gA T ⬝ w ⬝ giA S := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one, one_mul]
    rw [e]
    simp only [Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, giA_gA_cancel]
  have e : w - R (Matrix.of k) = R (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k i j) := by
    have hm : (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k i j) =
        (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j) - Matrix.of k := Matrix.ext fun _ _ => rfl
    rw [hm, hsub, hx']
  have h0 := map_finPart_mul_map (giA T) (incA D D.host.xi0⁻¹)
    (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k i j) fun i j => hk0 i j
  rw [e]
  simp only [R]
  rw [Matrix.map_mul, h0, Matrix.zero_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalDictionarySplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_dictionary_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  first | exact @GlobalTheory.SplitDict.exists_split_dictionary | exact GlobalTheory.SplitDict.exists_split_dictionary | (intros; apply GlobalTheory.SplitDict.exists_split_dictionary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmThetaLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaLiftSmoothAut

theorem isAutFunSm_thetaLift {D : D7} (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ)
    {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ) {ν : Measure (GA D T)} {𝓕 : Set (GA D T)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν) {φ : GA D T → ℂ}
    (hφ : IsAutFunSm θ T φ) (hc : IsCuspFun T φ) :
    IsAutFunSm θ S fun h => ∫ g in 𝓕, thetaKO om h g Φ * φ g ∂ν := by
  have hκ := (GlobalTheory.Mem.Lift.isKerSys_thKer hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont).swap
  exact (hκ.lift hP hθ ⟨hν, h𝓕⟩ ⟨hφ, hc⟩ ⟨Φ, hΦ⟩).2

end GlobalTheory.ThetaLiftSmoothAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChainStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.chain_ωY → R.chain_vY → ∀ t k, k + 1 < D.R.m → ∀ (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) g0 κ → IsLevelLift (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) g0 κ' → (levChi _ (R.βY k) (flagL (R.datYt t k R.triv)) κ)⁻¹ • R.ωY t k (κ, κ') (R.vY t k) = (levChi _ (R.βY (k + 1)) (flagL (R.datYt t (k + 1) R.triv)) κ')⁻¹ • R.vY t k := by
  first | exact @GlobalTheory.StepVecLaw.stepVec_lifts | exact GlobalTheory.StepVecLaw.stepVec_lifts | (intros; apply GlobalTheory.StepVecLaw.stepVec_lifts <;> assumption)
end

