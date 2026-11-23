module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIdempotentLocalShareBadTuplesLe
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainEigenspaceShare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0586
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0999
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumDoubledWeilAntidiagonalInvariantStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicThetaSum_doubledWeil_antidiagonal_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (κ ⊕ κ)), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd → SiegelRule (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) dd χ (diagCols (Fin b)) omd → ∀ (q : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (q₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = (_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) q₀ → ∀ (s : GL (Fin b) (AE F E)), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd q φ) = thetaSum F φ := by
  first | exact @GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag | exact GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag | (intros; apply GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleModuloEffectiveAwayFromPointPullAffine
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.AmplePull

theorem ampleAt_pull : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X,
    AmpleAt N (π x) → AmpleAt (N.pull π) x := by
  intro Y X π _ N hN x h
  obtain ⟨m, A, s, hm, hA, hAmp, hy⟩ := h
  have hNm : (lbPow N m).IsLB := isLB_lbPow hN m
  have hP : (LB.div (lbPow N m) A).IsLB := LB.isLB_div hNm hA
  have hN' : (N.pull π).IsLB := LB.isLB_pull hN π
  have hA' : (A.pull π).IsLB := LB.isLB_pull hA π
  have hNm' : (lbPow (N.pull π) m).IsLB := isLB_lbPow hN' m
  have hQ : (LB.div (lbPow (N.pull π) m) (A.pull π)).IsLB := LB.isLB_div hNm' hA'
  have iso : LBIso (LB.div (lbPow (N.pull π) m) (A.pull π)) ((LB.div (lbPow N m) A).pull π) := by
    rw [← cls_eq_iff hQ (LB.isLB_pull hP π), cls_div hNm' hA' hQ, cls_pull hP π, cls_div hNm hA hP,
      cls_lbPow hN' m hNm', cls_pull hN π hN', cls_pull hA π hA', cls_lbPow hN m hNm, map_sub, map_nsmul]
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hQ (LB.isLB_pull hP π) iso (ZM.RepBC.secPull _ π s)
  refine ⟨m, A.pull π, t, hm, hA', hAmp.pull_of_isAffineHom π, ?_⟩
  rw [ht, GlobalTheory.ZV.GraphSystem.nonzeroLocus_pull]
  exact hy

end GlobalTheory.AmplePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadWStOfRegular
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BadWOn

open Module GlobalTheory.BadCount GlobalTheory.TwistedRepresentationEmbedding GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

theorem model_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)) (T : ℕ)
    (hρ : IsPullRep M ka ρ)
    (hc : (M.p0 = 0 ∨ M.p0 = r) ∨ (0 < M.p0 ∧ M.p0 < r ∧ GlobalTheory.ShareOn.ArchOn M ka T ∧ GlobalTheory.ShareOn.sOf M ≤ T ∧
      LevelHyp (GlobalTheory.ShareOn.sub M ⊥)))
    (H P : Subgroup U) (hH : LevelHyp (GlobalTheory.ShareOn.sub M H)) (hP : LevelHyp (GlobalTheory.ShareOn.sub M P)) (lam : P →* ℂˣ) :
    ∃ n : ℕ, EmbReg ρ H n ∧ (n : ℝ) * Nat.card H ≤ 2 * Nat.card P * finrank ℂ (eig ρ P lam) := by
  rcases hc with hdef | ⟨h0, hr, hA, hs, hbot⟩
  · obtain ⟨-, hrest⟩ := _root_.GlobalTheory.ShareOn.Definite.share_definite E r U C M hdef ka ρ hρ
    obtain ⟨⟨n, hn, hnc⟩, -⟩ := hrest H hH
    have hP2 := (hrest P hP).2 lam
    refine ⟨n, hn, ?_⟩
    have e : (n : ℝ) * Nat.card H = Nat.card P * finrank ℂ (eig ρ P lam) := by exact_mod_cast (hnc.trans hP2.symm)
    rw [e]
    have : (0 : ℝ) ≤ Nat.card P * finrank ℂ (eig ρ P lam) := by positivity
    linarith
  · have hR := _root_.GlobalTheory.ShareRanks.ranks E r U C M hbot h0 hr ka T hA hs
    obtain ⟨n, hn, hb⟩ := _root_.GlobalTheory.CuspEmb.cusp_embReg E r U C M ka ρ hρ _ _ hR H hH
    have hS := (_root_.GlobalTheory.ShareEig.share_eig E r U C M ka ρ hρ _ _ hR P hP lam).1
    refine ⟨n, hn, ?_⟩
    have h4 := hR.2.2.2.1
    have hb' : (n : ℝ) * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) := by
      exact_mod_cast hb
    have hS' : (finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) : ℝ) ≤
        Nat.card P * finrank ℂ (eig ρ P lam) := by exact_mod_cast hS
    calc (n : ℝ) * Nat.card H ≤ _ := hb'
      _ ≤ 2 * finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) := h4
      _ ≤ 2 * (Nat.card P * finrank ℂ (eig ρ P lam)) := by linarith
      _ = 2 * Nat.card P * finrank ℂ (eig ρ P lam) := by ring

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}


end Point

end GlobalTheory.BadWOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsFiniteSpan
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Adelic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SectionsFieldChange

open GlobalTheory.AbLaw
open scoped TensorProduct

variable {X Y : Scheme.{0}}

theorem ofSec_secPull {L : LB X} (s : L.Sec) (π : Y ⟶ X) (V : X.Opens) :
    GlobalTheory.LB.ofSec (secPull s π) (π ⁻¹ᵁ V) =
      SecOn.pullLE L π V (π ⁻¹ᵁ V) le_rfl (GlobalTheory.LB.ofSec s V) := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [GlobalTheory.LB.coord_ofSec, SecOn.coord_pullLE, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.appLE_resG]
  exact GlobalTheory.LB.resG_appLE π _ _ (s.f (j PUnit.unit))

theorem ofSec_smul {L : LB X} (a : Γ(X, ⊤)) (s : L.Sec) (V : X.Opens) :
    GlobalTheory.LB.ofSec (a • s) V = rs X (le_top : V ≤ ⊤) a • GlobalTheory.LB.ofSec s V := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [GlobalTheory.LB.coord_smul, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, LB.smul_f, map_mul, GlobalTheory.resG_resG]
  exact congrArg (· * _) (GlobalTheory.resG_resG _ _ _).symm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

abbrev secModule {k : Type} [Field k] (S : LinSys k) : Module k S.L.Sec :=
  Module.compHom _ (algebraMap k Γ(S.Y, ⊤))

attribute [local instance] secModule

theorem secTower {k : Type} [Field k] (S : LinSys k) : IsScalarTower k Γ(S.Y, ⊤) S.L.Sec :=
  ⟨fun a g s => by
    show (algebraMap k Γ(S.Y, ⊤) a * g) • s = algebraMap k Γ(S.Y, ⊤) a • (g • s)
    rw [mul_smul]⟩

attribute [local instance] secTower

theorem isProper_str {k : Type} [Field k] {S : LinSys k} (hS : S.IsVariety) : IsProper S.str := by
  obtain ⟨N, i, hi, e⟩ := hS.proj
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str k N
  rw [← e]
  infer_instance

theorem finite_sec {k : Type} [Field k] {S : LinSys k} (hS : S.IsVariety) : Module.Finite k S.L.Sec := by
  have hfin : Module.Finite k (coh (twist (structureModule S.Y) S.L) 0) :=
    finite_coh_zero_twist_of_isProjOver (f := S.str) (fun _ => rfl) hS.proj S.isLB
  exact Module.Finite.equiv ((cohZeroTwistEquiv S.L).restrictScalars k)

theorem finrank_baseChange (S : LinSys F) (hS : S.IsVariety) :
    Module.finrank E (S.baseChange E).L.Sec = Module.finrank F S.L.Sec := by
  have := isProper_str hS
  rw [← lineBundleGlobalSectionsDim_eq_finrank, ← lineBundleGlobalSectionsDim_eq_finrank, lineBundleGlobalSectionsDim_def, lineBundleGlobalSectionsDim_def]
  exact FieldChangeInter.hdim_pull (S.isPullback_baseChange E) S.isLB 0

def resTo {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (V : X.Opens) :
    L.Sec →+ SecOnR f L V where
  toFun s := SecOnR.of f L V (GlobalTheory.LB.ofSec s V)
  map_zero' := SecOnR.ext fun i => by
    rw [SecOnR.coord_of, GlobalTheory.LB.coord_ofSec, LB.zero_f, map_zero, SecOnR.coord_zero]
  map_add' s t := SecOnR.ext fun i => by
    rw [SecOnR.coord_add, SecOnR.coord_of, SecOnR.coord_of, SecOnR.coord_of, GlobalTheory.LB.coord_ofSec,
      GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, LB.add_f, map_add]

theorem resTo_smul {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (V : X.Opens)
    (a : R) (s : L.Sec) :
    letI := algebraΓOfHom f
    resTo f L V (algebraMap R Γ(X, ⊤) a • s) = a • resTo f L V s :=
  ofSec_smul _ s V

theorem resTo_secPull (S : LinSys F) (E : Type) [Field E] [Algebra F E] (V : S.Y.Opens) (s : S.L.Sec) :
    resTo (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ V) (secPull s (S.bcFst E)) =
      SecOnR.pull S.L (S.isPullback_baseChange E).w V _ le_rfl (resTo S.str S.L V s) :=
  congrArg (SecOnR.of _ _ _) (ofSec_secPull s (S.bcFst E) V)

def pullSecs (S : LinSys F) (E : Type) [Field E] [Algebra F E] {n : ℕ} (b : Fin n → S.L.Sec) :
    Fin n → (S.baseChange E).L.Sec := fun j => secPull (b j) (S.bcFst E)

theorem linearIndependent_secPull (S : LinSys F) (hS : S.IsVariety) {n : ℕ} (b : Fin n → S.L.Sec)
    (hb : LinearIndependent F b) :
    LinearIndependent E (pullSecs S E b) := by
  classical
  have := isProper_str hS
  haveI : CompactSpace S.Y := QuasiCompact.compactSpace_of_compactSpace S.str
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := S.Y) (V := ⊤) isCompact_univ
  have H := S.isPullback_baseChange E
  let R : (Fin n → F) →ₗ[F] (∀ i, SecOnR S.str S.L (D i)) :=
    LinearMap.pi fun i => ∑ j, (LinearMap.proj j).smulRight (resTo S.str S.L (D i) (b j))
  have hRi : ∀ u i, R u i = resTo S.str S.L (D i) (∑ j, u j • b j) := fun u i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [R, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
    exact Finset.sum_congr rfl fun j _ => (resTo_smul S.str S.L (D i) (u j) (b j)).symm
  have hR : Function.Injective R := by
    refine (injective_iff_map_eq_zero R).2 fun u hu => ?_
    have h2 : ∑ j, u j • b j = 0 := by
      refine (SecOn.ofSec_bijective (M := S.L) (V := ⊤) rfl).injective ?_
      refine SecOn.ext_of_cover D (fun _ => le_top) hc.ge fun a => ?_
      rw [SecOn.restrict_ofSec, SecOn.restrict_ofSec]
      have := (hRi u a).symm.trans (congrFun hu a)
      exact this.trans (map_zero (resTo S.str S.L (D a))).symm
    funext j
    exact Fintype.linearIndependent_iff.1 hb u h2 j
  let Bc : ∀ i, E ⊗[F] SecOnR S.str S.L (D i) →ₗ[E]
      SecOnR (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) := fun i =>
    SecOnR.baseChangeHom S.L H.w (D i) (S.bcFst E ⁻¹ᵁ D i) le_rfl
  have hBc : ∀ i, Function.Bijective (Bc i) := fun i =>
    SecOnR.baseChangeHom_bijective S.isLB H (hD i) rfl
  let Φ : (Fin n → E) →ₗ[E] ∀ i, SecOnR (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) :=
    LinearMap.pi (fun i => Bc i ∘ₗ LinearMap.proj i) ∘ₗ
      (TensorProduct.piRight F E E fun i => SecOnR S.str S.L (D i)).toLinearMap ∘ₗ
      R.baseChange E ∘ₗ (TensorProduct.piScalarRight F E E (Fin n)).symm.toLinearMap
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (R.baseChange E) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap R hR
    have h2 : Function.Injective (LinearMap.pi (fun i => Bc i ∘ₗ LinearMap.proj i) :
        (∀ i, E ⊗[F] SecOnR S.str S.L (D i)) →ₗ[E] _) :=
      fun x y h => funext fun i => (hBc i).1 (congrFun h i)
    exact h2.comp ((TensorProduct.piRight F E E fun i => SecOnR S.str S.L (D i)).injective.comp
      (h1.comp (TensorProduct.piScalarRight F E E (Fin n)).symm.injective))
  have hΦc : ∀ c : Fin n → E, Φ c = fun i =>
      resTo (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) (∑ j, c j • pullSecs S E b j) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.piScalarRight_symm_single,
      LinearMap.baseChange_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
      LinearMap.pi_apply, LinearMap.proj_apply, Bc, SecOnR.baseChangeHom_tmul]
    change SecOnR.baseChangeHom S.L H.w (D i) (S.bcFst E ⁻¹ᵁ D i) le_rfl
      (c j ⊗ₜ[F] R (Pi.single j 1) i) = _
    rw [SecOnR.baseChangeHom_tmul, hRi]
    have hs : ∑ k, (Pi.single j (1 : F) : Fin n → F) k • b k = b j := by
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]
    rw [hs, ← resTo_secPull]
    exact (resTo_smul _ _ _ (c j) _).symm
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have h0 : Φ c = Φ 0 := by
    rw [hΦc, hc, map_zero]
    funext i
    exact map_zero _
  exact congrFun (hΦ h0)

theorem exists_pullSecs_spanning : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (S : LinSys F),
    S.IsVariety → ∃ (n : ℕ) (b : Fin n → S.L.Sec), ∀ t : (S.baseChange E).L.Sec, ∃ u : Fin n → E,
      (({ S with N := n, b := b } : LinSys F).baseChange E).comb u = t := by
  intro F E _ _ _ S hS
  haveI := finite_sec hS
  haveI : Module.Finite E (S.baseChange E).L.Sec := finite_sec (hS.baseChange E)
  let B := Module.finBasis F S.L.Sec
  refine ⟨_, B, fun t => ?_⟩
  have hli := linearIndependent_secPull (E := E) S hS B B.linearIndependent
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, finrank_baseChange S hS])
  have ht : t ∈ Submodule.span E (Set.range (pullSecs S E B)) := hsp ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ht
  exact ⟨u, hu⟩

end GlobalTheory.SectionsFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyProperties
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.BaseChangeVariety

theorem baseChange_props : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y) (D : ℕ) [SmoothOfRelativeDimension D p], IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → GeometricallyConnected p → IsIntegral X ∧ IsLocallyNoetherian X ∧ SmoothOfRelativeDimension D q ∧ IsProjOver q ∧ Function.Surjective π := by
  intro k E _ _ _ Y X p q π D _ H hP _
  have hs : SmoothOfRelativeDimension D q :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D).of_isPullback H ‹_›
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : Smooth q := SmoothOfRelativeDimension.smooth D q
  have hI : IsIntegral X := GlobalTheory.isIntegral_of_isPullback_of_smooth H
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  exact ⟨hI, hN, hs, GlobalTheory.PosBaseChange.isProjOver_of_isPullback H hP, GlobalTheory.PosBaseChange.surjective_proj H⟩

end GlobalTheory.BaseChangeVariety
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFramedLiftsLevelCoverConst
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.LevDegree

theorem card_lifts_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; ∀ y y' : FrPt Xo c (CAt σ₂), Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y'} := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ _ y y'
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  letI : Field (CAt σ₂) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ₂) := inferInstanceAs (IsAlgClosed ℂ)
  have hA : l.A = 1 := hL.levA
  have hA₂ : d.l₂.A = 1 := hL₂.levA
  have hpq : Dw.p ≠ Dw.q ∧ 1 ≤ Dw.p + Dw.q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hL.inR
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hk : ∀ a : c.F, algebraMap d.c₂.F (CAt σ₂) (d.eF a) = algebraMap c.F (CAt σ₂) a := fun _ => rfl
  obtain ⟨lift, hlift⟩ := GlobalTheory.LevPullModel.exists_isLift (Dw := Dw) (l := d.l₂)
  have hov : ∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom :=
    GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq.1 hA d
  have L := GlobalTheory.LevelActionOfLifts.actLev_of_lifts_of_eq_one D H Dw d.l₂ d.Xo₂ d.c₂ (Gam Dw d.l₂) lift hpq.2 hA₂
    (fun a => (Submodule.Quotient.eq _).1 ((GlobalTheory.LevPullModel.lift_mk hlift 1 a).trans rfl))
    (fun g h a => (Submodule.Quotient.eq _).1 (by
      rw [GlobalTheory.LevPullModel.lift_mk hlift, GlobalTheory.LevPullModel.lift_mk hlift, GlobalTheory.LevPullModel.lift_mk hlift]; rfl))
  have key : ∀ y : FrPt Xo c (CAt σ₂),
      Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} =
        Nat.card {γ : Gam Dw d.l₂ // CongMod l.Mb (lift γ) LinearMap.id} := by
    intro y
    obtain ⟨y₀, hy₀⟩ := hd.2.2.2.2.2.2.1 (CAt σ₂) hk y
    have T := _root_.GlobalTheory.LevOrbit.fibre_torsor D.host.E H Dw l Xo c d hpq.2 hd hA₂ hov lift hlift (CAt σ₂) hk y₀
    have hA₂' : d.l₂.A.Coprime d.l₂.M := by rw [hA₂]; exact Nat.coprime_one_left _
    have hex : ∀ γ : Gam Dw d.l₂, ∃ y₂', levR (lift γ, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La)) y₀ y₂' :=
      fun γ => L.total γ (CAt σ₂) y₀
    choose g hg using hex
    let f : {γ : Gam Dw d.l₂ // CongMod l.Mb (lift γ) LinearMap.id} →
        {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} :=
      fun γ => ⟨g γ.1, ((T (g γ.1) y hy₀).1).2 ⟨γ.1, γ.2, hg γ.1⟩⟩
    refine (Nat.card_eq_of_bijective f ⟨fun γ γ' e => Subtype.ext ?_, fun z => ?_⟩).symm
    · have e' : g γ.1 = g γ'.1 := congrArg Subtype.val e
      exact (T (g γ.1) y hy₀).2 γ.1 γ'.1 (hg γ.1) (e' ▸ hg γ'.1)
    · obtain ⟨γ, hγ, hl⟩ := ((T z.1 y hy₀).1).1 z.2
      exact ⟨⟨γ, hγ⟩, Subtype.ext (GlobalTheory.LevelSpanCompare.levR_unique hpq.2 hA₂' (lift γ) (hg γ) hl)⟩
  exact (key y).trans (key y').symm

end GlobalTheory.LevDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedAlmostAllPlaces
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PairVac

theorem eventually_unrAt_of_isHecke {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (χ : Chr F E) (hχ : IsHecke F E χ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, UnrAt χ w := by
  obtain ⟨H, hloc, -⟩ := GlobalTheory.HeckeBridge.exists_hchar F E σ hcm χ hχ
  refine (GlobalTheory.HeckeSplit.eventually_unrAt H.1 H.2.1).mono fun w hw x hx => ?_
  rw [← hloc w x]
  exact ((GlobalTheory.HeckeSplit.unrAt_iff E H w).1 hw) x hx

end GlobalTheory.PairVac

end
end

