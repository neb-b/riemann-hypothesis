module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0213
public import Formalism.LocalToGlobal.Columns.Bundle0030
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticesSelfDualMovedPair
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

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 800000

namespace GlobalTheory.MovedSD

open Matrix

open Formalism.UG in
theorem colLat_one_eq_stdLat (D : D7) (n : ℕ) :
    colLat (1 : GL (Fin n) D.host.E) = Formalism.L2.Col.stdLat D.host.E n := by
  ext x
  rw [GlobalTheory.TestLat.Inhabitant.mem_colLat_one]
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem move_vec (D : D7) {n : ℕ} (fr : GL (Fin n) D.host.E) (a b : GL (Fin n) (Lev.EAf D)) (v : Fin n → D.host.E) :
    (fr⁻¹).val.map (eToEAf D) *ᵥ ((b⁻¹).val *ᵥ ((a⁻¹).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i))) =
      (Formalism.UG.bc (eToEAf D) fr⁻¹ * b⁻¹ * a⁻¹ * Formalism.UG.bc (eToEAf D) fr).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (v i) := by
  have hb : ∀ g : GL (Fin n) D.host.E, (Formalism.UG.bc (eToEAf D) g).val = g.val.map (eToEAf D) := fun _ => rfl
  have ev : (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i)) =
      fr.val.map (eToEAf D) *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (v i) := by
    funext i
    exact RingHom.map_mulVec (eToEAf D) fr.val v i
  rw [ev]
  simp only [Units.val_mul, hb, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem mem_globLat_move (D : D7) {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (fr : GL (Fin n) D.host.E)
    (a b : GL (Fin n) (Lev.EAf D))
    (hu : ∀ w, w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔ b.val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (v : Fin n → D.host.E) :
    fr.val *ᵥ v ∈ Formalism.UG.CS.globLat a Λ ↔
      v ∈ Formalism.UG.CS.globLat (Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr) (Formalism.L2.Col.stdLat D.host.E n) := by
  change (_ ∈ Formalism.L2.Herm.hatL (F := D.host.F) _) ↔ (_ ∈ Formalism.L2.Herm.hatL (F := D.host.F) _)
  generalize hw : ((a⁻¹).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i)) = w
  have h1 := hu ((b⁻¹).val *ᵥ w)
  have e1 : b.val *ᵥ ((b⁻¹).val *ᵥ w) = w := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [e1] at h1
  rw [← h1]
  have hm := GlobalTheory.LatMulAd.mem_hatL_colLat_mul D fr 1 ((b⁻¹).val *ᵥ w)
  rw [mul_one, colLat_one_eq_stdLat] at hm
  rw [hm, ← hw]
  have eg : ((Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr)⁻¹ : GL (Fin n) (Lev.EAf D)) =
      Formalism.UG.bc (eToEAf D) fr⁻¹ * b⁻¹ * a⁻¹ * Formalism.UG.bc (eToEAf D) fr := by
    simp only [_root_.mul_inv_rev, ← map_inv, inv_inv, mul_assoc]
  rw [eg]
  refine Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Col.stdLat D.host.E n)) ?_)
  exact move_vec D fr a b v

theorem cT_map_inclE (D : D7) {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (M.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rfl

theorem move_mem_UAd (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (fr : GL (Fin n) D.host.E)
    (hfr : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.val * J * fr.val = 1) (a b : GL (Fin n) (Lev.EAf D))
    (ha : a ∈ Formalism.L2.DIV.UA D.sp.cm J) (hb : b ∈ Formalism.L2.DIV.UA D.sp.cm J) :
    Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr ∈ Formalism.L2.Col.UAd D.sp.cm n := by
  have hab : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (a * b).val *
      J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * (a * b).val =
      J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := mul_mem ha hb
  set A := (a * b).val
  set ι := Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (Formalism.L2.Herm.Af D.host.F)
  set σR := Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
  have hm : ∀ g : GL (Fin n) D.host.E, (Formalism.UG.bc (eToEAf D) g).val = g.val.map ι := fun _ => rfl
  have hF : Formalism.UG.cT σR (fr.val.map ι) * J.map ι * fr.val.map ι = 1 := by
    rw [cT_map_inclE, ← Matrix.map_mul, ← Matrix.map_mul, hfr, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : fr.val.map ι * (fr⁻¹).val.map ι = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι = J.map ι := by
    calc Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι
        = Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (Formalism.UG.cT σR (fr.val.map ι) * J.map ι * fr.val.map ι) * (fr⁻¹).val.map ι := by
          rw [hF, Matrix.mul_one]
      _ = Formalism.UG.cT σR (fr.val.map ι * (fr⁻¹).val.map ι) * J.map ι * (fr.val.map ι * (fr⁻¹).val.map ι) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J.map ι := by
          rw [h1]; simp [Formalism.UG.cT]
  show Formalism.UG.cT σR (_ : GL (Fin n) (Lev.EAf D)).val * (1 : Matrix (Fin n) (Fin n) D.host.E).map ι * _ = _
  rw [Units.val_mul, Units.val_mul, hm, hm, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  calc Formalism.UG.cT σR ((fr⁻¹).val.map ι * A * fr.val.map ι) * ((fr⁻¹).val.map ι * A * fr.val.map ι)
      = Formalism.UG.cT σR (fr.val.map ι) * (Formalism.UG.cT σR A * (Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι) * A) * fr.val.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hJ, hab, hF]

theorem sd_latAt {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X) : SD D (GlobalTheory.SumSize.latAt S X x) := by
  have e : GlobalTheory.SumSize.latAt S X x = Formalism.UG.CS.globLat (Formalism.UG.bc (eToEAf D) (S.N.fr X)⁻¹ *
      (finG (G.V X) x * Lev.finE (G.V X) (S.N.u X : Formalism.L2.Theta.GA D (G.V X))) * Formalism.UG.bc (eToEAf D) (S.N.fr X))
      (Formalism.L2.Col.stdLat D.host.E _) := by
    ext v
    exact mem_globLat_move D (G.Λ X) (S.N.fr X) _ _ (S.N.u_lat X hX) v
  have ha : finG (G.V X) x ∈ Formalism.L2.DIV.UA D.sp.cm (G.V X).gram := GlobalTheory.LevSplit.finE_mem_UA (G.V X) x.1
  have hb := GlobalTheory.LevSplit.finE_mem_UA (G.V X) (S.N.u X : Formalism.L2.Theta.GA D (G.V X))
  show IsSDLat D.host.E _ _
  rw [e]
  exact Formalism.L2.Col.DetChrChi.isSDLat_globLat D.sp.cm (move_mem_UAd D _ _ (S.N.fr_on X hX) _ _ ha hb)

end GlobalTheory.MovedSD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatAStdLIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TensColRead

variable {D : D7}

def embInf (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem embInf_add_emb (w : AE D) :
    embInf D (Formalism.L2.Theta.infPart D w) + GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    conv_rhs => rw [← ha, ← hb]
    abel
  | tmul a e =>
    have e1 : embInf D (Formalism.L2.Theta.infPart D (a ⊗ₜ[D.host.F] e)) =
        (pairA D.host.F (fstA D.host.F a) 0) ⊗ₜ[D.host.F] e := rfl
    have e2 : GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D (a ⊗ₜ[D.host.F] e)) =
        (pairA D.host.F 0 (sndA D.host.F a)) ⊗ₜ[D.host.F] e := rfl
    rw [e1, e2, ← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _) (zero_add _)

theorem emb_finPart (w : AE D) (h : Formalism.L2.Theta.infPart D w = 0) :
    GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D w) = w := by
  have := embInf_add_emb w
  rwa [h, map_zero, zero_add] at this

theorem col_iff {S T : HSp D} (L : Lt D.host.E T.rank) (x : WO S T) (k : Fin S.rank) :
    (fun c => Formalism.L2.Theta.finPart D (x c k)) ∈ hatV L ↔
      (fun c => toEAf D (x c k)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  GlobalTheory.LevSplit.latHat_iff L _

def colHom (S T : HSp D) (k : Fin S.rank) : WO S T →+ (Fin T.rank → AfE D) where
  toFun x := fun c => Formalism.L2.Theta.finPart D (x c k)
  map_zero' := by funext c; simp
  map_add' x y := by funext c; simp

theorem toAf_single_mem (n : ℕ) (k : Fin n) : toAf (Pi.single k (1 : D.host.E)) ∈ hatV (stdL D.host.E n) :=
  AddSubgroup.subset_closure ⟨1, GlobalTheory.TensLatMove.intAf_one, Pi.single k 1,
    Submodule.subset_span ⟨k, rfl⟩, rfl⟩

theorem mem_hatA_stdL_iff : ∀ (D : D7) (S T : HSp D) (L : Lt D.host.E T.rank) (x : WO S T), IsFinPt x → (x ∈ hatA S T (tens (stdL D.host.E S.rank) L) ↔ ∀ k : Fin S.rank, (fun c => toEAf D (x c k)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L) := by
  intro D S T L x hx
  constructor
  · intro hmem k
    rw [← col_iff]
    have hle : hatA S T (tens (stdL D.host.E S.rank) L) ≤ (hatV L).comap (colHom S T k) := by
      rw [hatA, AddSubgroup.closure_le]
      rintro _ ⟨α, hα, y, hy, rfl⟩
      exact AddSubgroup.subset_closure ⟨α, hα, y k, (GlobalTheory.SW.TensLat.mem_tens_stdL L y).1 hy k, rfl⟩
    exact hle hmem
  · intro h
    have hu : ∀ k, (fun c => Formalism.L2.Theta.finPart D (x c k)) ∈ hatV L := fun k => (col_iff L x k).2 (h k)
    have e : x = ∑ k, GlobalTheory.TensLatMove.outer S T (toAf (Pi.single k 1)) (fun c => Formalism.L2.Theta.finPart D (x c k)) := by
      ext c k'
      have hc : Formalism.L2.Theta.infPart D (x c k') = 0 := by
        have := congrFun (congrFun hx c) k'
        simpa using this
      rw [Matrix.sum_apply]
      simp only [GlobalTheory.TensLatMove.outer, Matrix.of_apply, toAf]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.sum_eq_single k']
      · rw [Pi.single_eq_same, ← Algebra.TensorProduct.one_def, mul_one]
        exact (emb_finPart _ hc).symm
      · intro j _ hj
        rw [Pi.single_eq_of_ne (Ne.symm hj), TensorProduct.tmul_zero, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ k') h'
    rw [e]
    exact sum_mem fun k _ => GlobalTheory.TensLatMove.outer_mem S T _ L _ (toAf_single_mem _ k) _ (hu k)

end GlobalTheory.TensColRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelTypeFormExpandsAlongDualFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.TypeExpand

theorem typeAt_expand : ∀ (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) {D : D7} (θ : InfFam D) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {m : ℕ} (k : Fin m → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : ∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (B : Fin m → (M.H τ →ₗ[ℂ] M.H τ))
    (hB : ∀ A : M.H τ →ₗ[ℂ] M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) *
          LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
    {φ : GA D V → ℂ} (hφ : IsTypeAt θ V τ (S τ) φ) (x : GA D V) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), φ (x * atTau θ V τ g) = ∑ j, φ (x * atTau θ V τ (k j)) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j) := by
  intro hU D θ V S M τ _ m k hk B hB φ hφ x g hg
  obtain ⟨H', _, _, σ, lam, ε, P, hen, hds, hPu, hPg, hx⟩ := hφ
  obtain ⟨v, -, ℓ, -, -, hsum⟩ := hx x
  obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) hen
  subst hl he
  obtain ⟨U, hU'⟩ := hU _ (M.ε τ) (M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) P
    (M.fr_unit τ) hPu (M.fr_gram τ) hPg _ _ (M.σ τ) σ (M.ds τ) hds

  set A : ℕ → (M.H τ →ₗ[ℂ] M.H τ) := fun i =>
    ((ℓ i).comp (U.symm.toLinearEquiv.toLinearMap)).smulRight (U (v i)) with hA
  have key : ∀ i, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      ℓ i (σ (P * h * P⁻¹) (v i)) =
        LinearMap.trace ℂ (M.H τ) ((M.rep τ h : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) := by
    intro i h hh
    have e1 : (M.rep τ h : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i =
        ((ℓ i).comp (U.symm.toLinearEquiv.toLinearMap)).smulRight (M.rep τ h (U (v i))) := by
      ext w
      simp [hA]
    rw [e1, LinearMap.trace_smulRight]
    have e2 : M.rep τ h (U (v i)) = U (σ (P * h * P⁻¹) (v i)) := (hU' h hh (v i)).symm
    rw [e2]
    simp
  have h1 : HasSum (fun i => ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
      (∑ j, φ (x * atTau θ V τ (k j)) *
        LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j)) := by
    refine hasSum_sum fun j _ => ?_
    refine HasSum.mul_right _ ?_
    have := hsum (k j) (hk j)
    refine this.congr_fun ?_
    intro i
    exact (key i (k j) (hk j)).symm
  have h2 : HasSum (fun i => ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j)) (φ (x * atTau θ V τ g)) := by
    refine (hsum g hg).congr_fun ?_
    intro i
    rw [key i g hg, hB (A i) g hg]
  exact h2.unique h1

end GlobalTheory.TypeExpand

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormDerivCharacterSymplecticPairingRealLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LatSum

theorem norm_deriv_psi_symplO_lineAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : WO S T), ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ = 2 * Real.pi * |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ z (compAt θ τ w)| := by
  intro D ψ hψ θ hθ S T τ z w
  set a : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ z (compAt θ τ w) with ha
  have h2 : ∀ x y : WO S T, symplO S T x y = symplOH S T x y + symplOH S T x y := by
    intro x y
    unfold symplOH
    rw [← add_mul, ← map_add (f := _)]
    norm_num
  have hphase : ∀ t : ℝ, ψ (symplO S T (lineAt θ τ z t) w) =
      Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * (t : ℂ)) := by
    intro t
    rw [GlobalTheory.Asc.symplO_swap, h2, AddChar.map_neg_eq_inv, AddChar.map_add_eq_mul,
      GlobalTheory.ThetaDecay.psi_symplOH_lineAt hψ hθ S T w τ z t, ← Complex.exp_add, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hfun : (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) =
      fun t : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * (t : ℂ)) := funext hphase
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * (t : ℂ)))
      (-(2 * Real.pi * Complex.I * (a : ℂ))) 0 := by
    have h3 : HasDerivAt (fun u : ℂ => Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * u))
        (Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * ((0:ℝ):ℂ)) * ((-(2 * Real.pi * Complex.I * (a : ℂ))) * 1))
        ((0:ℝ):ℂ) :=
      ((hasDerivAt_id _).const_mul (-(2 * Real.pi * Complex.I * (a : ℂ)))).cexp
    refine h3.comp_ofReal.congr_deriv ?_
    simp
  rw [hfun, hd.deriv, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simp

end GlobalTheory.LatSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierInversionSchwartzBruhat
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier

noncomputable section
namespace GlobalTheory.ColFourier

theorem fourier_pi_inversion_at {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type*} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} {c : kˣ} {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {g : (n → k) → ℂ} (hg : g ∈ SB (n → k)) (a : n → k) :
    ∫ y : n → k, (∫ x, g x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)
      ∂(Measure.pi fun _ => ν) = g a := by
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have hh : (fun x => g (x + a)) ∈ SB (n → k) :=
    ⟨hg.1.comp_continuous (by fun_prop), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have h1 := (FourierPi.fourier_pi_of_conductor h hν hh).2
  simp only [zero_add] at h1
  rw [← h1]
  congr 1
  funext y
  rw [← integral_mul_const,
    ← integral_add_right_eq_self (fun x => g x * (ψ (x ⬝ᵥ y) : ℂ) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)) a]
  congr 1
  funext x
  rw [add_dotProduct, AddChar.map_add_eq_mul, AddChar.inv_apply', dotProduct_comm y a, mul_assoc,
    ← Circle.coe_mul, mul_inv_cancel_right]

theorem fourierInt_inv_fourierInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ⁻¹ m P (fourierInt ψ m P Ξ) = Ξ := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m hψ hm P Ξ hΞ
  have hν : IsSelfDual ψ m := isSelfDual_of_isUnitVol m hψ hm
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  funext X
  have h0 := comp_setCols_mem_SB hΞ P X
  have hg : (fun x : (_ : A) × P → k => Ξ (setCols P X (Matrix.of fun i j => x ⟨i, j⟩))) ∈
      SB ((_ : A) × P → k) :=
    ⟨h0.1.comp_continuous (f := fun x : (_ : A) × P → k => (Matrix.of fun i j => x ⟨i, j⟩ : Matrix A P k))
        (continuous_pi fun i => continuous_pi fun j => continuous_apply _),
      HasCompactSupport.intro (h0.2.image (f := fun (U : Matrix A P k) (p : (_ : A) × P) => U p.1 p.2)
        (continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)))
        fun x hx => image_eq_zero_of_notMem_tsupport (f := fun U => Ξ (setCols P X U)) fun h => hx ⟨_, h, rfl⟩⟩
  have h1 := fourier_pi_inversion_at hψ hν hg (fun p => X p.1 p.2)
  have h2 : setCols P X (Matrix.of fun i (j : P) => X i j) = X := setCols_restrictCols P X
  simp only [h2] at h1
  rw [← h1, fourierInt_eq_pi]
  congr 1
  funext y
  rw [fourierInt_eq_pi]
  have h3 : (fun p : (_ : A) × P => setCols P X (Matrix.of fun i j => y ⟨i, j⟩) p.1 p.2) = y := by
    funext p
    simp [setCols, p.2.2]
  simp only [setCols_setCols, h3]

end GlobalTheory.ColFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacesDistinctTranslationsDerivativesCommute
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.PlaceComm

theorem place_comm : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    IsInfFam (D := D) θ → ∀ τ τ' : D.what₂.Tau, τ ≠ τ' →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), ∀ f : GA D V → ℂ,
      rTr V (atTau θ V τ g) (rTr V (atTau θ V τ' h) f) = rTr V (atTau θ V τ' h) (rTr V (atTau θ V τ g) f)) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ X ∈ lieAt V τ', ∀ f : GA D V → ℂ,
      Rder θ V τ' X (rTr V (atTau θ V τ g) f) = rTr V (atTau θ V τ g) (Rder θ V τ' X f)) ∧
    (∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ', ∀ f : GA D V → ℂ, IsAutFunSm θ V f →
      Rder θ V τ X (Rder θ V τ' Y f) = Rder θ V τ' Y (Rder θ V τ X f)) := by
  intro D θ V hθ τ τ' hne
  refine ⟨fun g hg h hh f => ?_, fun g hg X hX f => ?_, fun X hX Y hY f hf => ?_⟩
  · funext x
    simp only [rTr]
    rw [mul_assoc, mul_assoc, GlobalTheory.AvgOtherPlace.atTau_comm hθ (Ne.symm hne) hg hh]
  · rw [GlobalTheory.Mem.RealTranslate.Rder_rTr hθ (GlobalTheory.Mem.RealTranslate.isRealPt_atTau hθ τ hg) hX,
      GlobalTheory.AvgOtherPlace.adAt_atTau_of_ne hθ (Ne.symm hne) hg]
  · exact GlobalTheory.DerBracket.Rder_comm hθ hf.smooth hne hX hY

end GlobalTheory.PlaceComm

end
end

