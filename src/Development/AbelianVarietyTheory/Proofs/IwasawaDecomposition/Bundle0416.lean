module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnOfCoord
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0415
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DetSubMemOfConj

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicFormFunctionValuesMemCoefficientLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

theorem ext_vals : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → ∀ (c : CoefA V) (S : CSD D.what₂.LL) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ J χ) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k ∈ J, ∀ h, Bridge.hLat V (h * k) = Bridge.hLat V h) → (∀ k : J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = (χ k : ℂ)) → ∀ f : S.Forms, (∀ h, pres.ext f.1 h ∈ Set.range c0) ∧ ((∀ a, f.1 a ∈ S.Nab a) → ∀ h, ∃ v ∈ nabAtr (labLL D) lam (Bridge.hLat V h), pres.ext f.1 h = c0 v) := by
  intro D V hStd c S J χ pres lam c0 pair del hMap hTie hJ hχ f
  obtain ⟨e, -, hcoef, -, hnab, -⟩ := hTie
  have hL := (_root_.GlobalTheory.HLatStd.hLat_props D V hStd).2.2
  have key : ∀ h, ∃ (z : 𝓞 D.what₂.LL) (γE : GL (Fin V.rank) D.host.E),
      Bridge.IsRatMat V (pres.decG h) γE ∧
      pres.ext f.1 h = c0 ((z : D.what₂.LL) • rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) := by
    intro h
    obtain ⟨z, hz⟩ := hχ (pres.decK h)
    obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V (pres.decG h) γE := by
      obtain ⟨g, hg⟩ := (pres.decG h).2
      exact ⟨g, hg.2.symm⟩
    refine ⟨z, γE, hγ, ?_⟩
    have a1 : pres.ext f.1 h = ((χ (pres.decK h) : ℂˣ) : ℂ) • c.coef.ρ (pres.decG h) (pres.coef (f.1 (pres.decC h))) := rfl
    have a2 : c.coef.ρ (pres.decG h) (pres.coef (f.1 (pres.decC h))) =
        c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) := by
      rw [hcoef]; exact (hMap.1 _ _ hγ _).symm
    have a3 : c0 ((z : D.what₂.LL) • rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) =
        D.what₂.embLL (z : D.what₂.LL) • c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) :=
      map_smulₛₗ c0 _ _
    refine a1.trans ((congrArg (fun w => ((χ (pres.decK h) : ℂˣ) : ℂ) • w) a2).trans ?_)
    refine Eq.trans ?_ a3.symm
    exact congrArg (fun s : ℂ => s • c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))))) hz.symm
  refine ⟨fun h => ?_, fun hf h => ?_⟩
  · obtain ⟨z, γE, -, hv⟩ := key h
    exact ⟨_, hv.symm⟩
  obtain ⟨z, γE, hγ, hv⟩ := key h
  refine ⟨_, ?_, hv⟩

  have hlat : Bridge.hLat V h = (Bridge.hLat V (pres.y (pres.decC h))).map
      ((Matrix.mulVecLin (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).restrictScalars (𝓞 D.host.E)) := by
    have h1 : Bridge.hLat V h = Bridge.hLat V (Bridge.ratF V (pres.decG h) * pres.y (pres.decC h)) := by
      conv_lhs => rw [pres.dec_spec h]
      exact hJ _ (pres.decK h).2 _
    rw [h1]
    ext x
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
    constructor
    · intro hx
      refine ⟨((γE⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x, ?_, ?_⟩
      · rw [hL _ _ hγ, Matrix.mulVec_mulVec]
        simpa using hx
      · rw [Matrix.mulVec_mulVec]
        simp
    · rintro ⟨y, hy, rfl⟩
      exact (hL _ _ hγ _ _).1 hy
  have hmem : e (f.1 (pres.decC h)) ∈ nabAtr (labLL D) lam (Bridge.hLat V (pres.y (pres.decC h))) := by
    rw [← hnab]
    exact ⟨_, hf _, rfl⟩
  have hga := Formalism.L2.Col.nabAtr_gmap (labLL D) lam ((Formalism.L2.Col.toGLm D.host.E V.rank).symm γE)
    (Bridge.hLat V (pres.y (pres.decC h)))
  rw [Formalism.L2.Col.gmap_eq_map, MulEquiv.apply_symm_apply] at hga
  rw [hlat, hga]
  have h2 : rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))) ∈ (nabAtr (labLL D) lam (Bridge.hLat V (pres.y (pres.decC h)))).map
      ((rhoVr (labLL D) lam γE).restrictScalars (𝓞 D.what₂.LL)) := ⟨_, hmem, rfl⟩
  first
    | exact Submodule.smul_mem _ z h2
    | exact (algebraMap_smul D.what₂.LL z _ ▸ Submodule.smul_mem _ z h2)
    | simpa [Algebra.smul_def] using Submodule.smul_mem _ z h2

end GlobalTheory.MtIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicWeilRepresentationWithRulesExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th

namespace GlobalTheory.Mem.WeilExists

theorem weilEx_of_weilRepresentation : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilEx D := fun h D =>
  weilEx_of
    (GlobalTheory.Mem.WeilTransport.weilCoreEx_of_datum D fun ψ hψ S T χS χT h1 h2 h3 h4 => h D ψ S T χS χT hψ h1 h2 h3 h4)
    (_root_.GlobalTheory.Mem.WeilRule.weilRules D)

end GlobalTheory.Mem.WeilExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BranchingNormIdentityTrueColumnsMembers
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem cTw_eq_mul (B : Base) :
    ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = (B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨b, hb⟩ := B.R.t_odd
  have h2 : B.R.t + 1 = 2 * (b + 1) := by omega
  rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  push_cast
  ring

theorem trueWeight_lastStep_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (τ : (I.rec7 l Z).what₂.Tau) : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = B.wts.lamTrue u B.R.m τ := by
  have h := cTw_eq_mul B
  show Formalism.MainNotions.product_first_zeroth_parts.wSh (Examples₂.lamOf (B.hcW u τ) B.R.m) (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
    Formalism.L2.Col.shiftW (Examples₂.lamOf (B.hcW u τ) B.R.m) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
  unfold Formalism.MainNotions.product_first_zeroth_parts.wSh Formalism.L2.Col.shiftW Formalism.MainNotions.product_first_zeroth_parts.cTw
  congr 1
  funext i
  rw [h]
  ring

theorem trueRowWeight_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (τ : (I.rec7 l Z).what₂.Tau) : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = B.wts.sgTrue τ := by
  have h := cTw_eq_mul B
  show Formalism.MainNotions.product_first_zeroth_parts.wSh (B.wts.row τ).sg (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
    Formalism.L2.Col.shiftW (B.wts.row τ).sg (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
  unfold Formalism.MainNotions.product_first_zeroth_parts.wSh Formalism.L2.Col.shiftW Formalism.MainNotions.product_first_zeroth_parts.cTw
  congr 1
  funext i
  rw [h]
  ring

end GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.Col2.TC

theorem branchingNorm_identity_trueColumns_members {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    BeOnTie (I.rec7 l Z) u := by
  intro τ
  have e1 := trueWeight_lastStep_trueColumns I l Z u τ
  have e2 := trueRowWeight_trueColumns I l Z u τ
  have n1 : (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ).natW = (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ).natW :=
    Formalism.MainNotions.product_first_zeroth_parts.natW_wSh _ _
  have n2 : (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ).natW = (((I.rec7 l Z).fm u).sg τ).natW := Formalism.MainNotions.product_first_zeroth_parts.natW_wSh _ _
  show fockOpNorm (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)) =
    fockOpNorm (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ) (((I.rec7 l Z).fm u).sg τ)
      (Formalism.L2.Ker.brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ))
  rw [e1, e2] at *
  exact fockOpNorm_congr _ n1 n2

theorem beOnTie_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)), ∀ u, BeOnTie (I.rec7 l Z) u :=
  fun I _ _ l Z u => branchingNorm_identity_trueColumns_members I l Z u

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepWeightArithmetic
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.IntegralityCompare

theorem weight_arith_step : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (μ : I.ι) (i : ℕ), i < B.R.m →
    ∃ k : (I.rec7 l Z).what₂.Tau → ℕ,
      (∀ τ, (k τ : ℤ) = shiftOf (lamTG (I.fm l u μ) i) τ + ((I.rec7 l Z).chTw u μ).sSharp i τ) ∧
      ∀ τ r, nuT (I.rec7 l Z) u i τ r = ((I.fm l u μ).lam i τ).natW r + k τ := by
  intro B X I hOk hPins l Z u μ i hi
  obtain ⟨n, h1, h2, -, -⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ (I.fm l u μ) i hi
  refine ⟨n, fun τ => ?_, fun τ r => ?_⟩
  · rw [← h2 τ]; rfl
  · rw [← h1 τ r]
    unfold lamTG
    rw [natW_shW]
    rfl

end GlobalTheory.IntegralityCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldFormValueMemPolynomialModel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.KerVal

theorem fm_succ_mem_valQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (x : (((I.tw l l0 Z).fm u μ).lat (i + 1)).V) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)), ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = ((I.tw l l0 Z).fm u μ).emb (i + 1) x c' := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hBs hUnf hJets u μ i hi x c'
  obtain ⟨n, hw, hn, hnat, hds⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  have hlam : ∀ j τ, Col2.lamT (B.hcW u) j τ = lamTG ((I.tw l l0 Z).fm u μ) j τ := by
    intro j τ
    unfold Col2.lamT lamTG
    show Col2.shW _ _ = Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) j) _
    obtain ⟨c, hc⟩ := B.R.t_odd
    have h1 : (B.R.t + 1) / 2 = c + 1 := by omega
    have h2 : j * (B.R.t + 1) / 2 = j * (c + 1) := by
      rw [show j * (B.R.t + 1) = 2 * (j * (c + 1)) by rw [hc]; ring]; omega
    simp only [Col2.shW, Formalism.L2.Forms.shW]
    congr 1
    funext r
    show _ + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)) = _ - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [h1, h2]
    push_cast
    ring
  have hP : ((x.1 c').1 : Formalism.L2.DIV.Pol B.LL (Tau B.R) (B.R.N (i + 1))) ∈ polV (I.rec7 l Z) u (i + 1) := by
    have h1 := VV_le_WtPol (K := B.LL) (Col2.lamT (B.hcW u) (i + 1)) (x.1 c').2
    have e : (fun τ r => (Col2.lamT (B.hcW u) (i + 1) τ).natW r) = extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
      funext τ r
      rw [hlam]
      refine (hnat τ r).trans ?_
      congr 1
      funext τ' r'
      exact hw τ' r'
    rw [e] at h1
    exact h1
  refine ⟨Submodule.Quotient.mk ⟨_, hP⟩, ?_⟩
  funext y
  show evP O u μ (i + 1) ⟨_, hP⟩ y = _
  show (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(((I.rec7 l Z).chTw u μ).sDiv i τ))) *
    GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL (x.1 c').1) ((O u μ).frm (i + 1) y) = _
  simp only [(O u μ).frm_de (i + 1) hi y]
  rw [hStd.frm u μ (i + 1) y]
  show _ = Formalism.L2.Col.evFr (gramC (1 : Matrix (Fin _) (Fin _) _) (embAt B.embLL B.tauLL)) (shiftOf (Col2.lamT (B.hcW u) (i + 1))) B.embLL (x.1 c').1 y
  refine Eq.trans ?_ (Formalism.L2.Col.evFr_apply _ _ _ _ _).symm
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    exact ((congrArg DomWeight.detShift (hlam (i + 1) τ)).trans (hds τ)).symm
  · exact GlobalTheory.PdvKm.evFr_map _ _ _ _

end GlobalTheory.Mem.KerVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompanionCrd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.MemLat

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem mem_N_iff (d : Deco E n ST SG) (hd : d.Ok) (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal)
    (hcop : IsCoprime π (cO E π)) (x : Sp E n) :
    x ∈ d.N ↔ ∃ a ∈ d.L, ∃ b ∈ d.Lsh, x = a + cO E π • b := by
  constructor
  · intro hx
    obtain ⟨s, t, hst⟩ := hcop
    refine ⟨s • (π • x), d.L.smul_mem s (hd.smul_N_mem_L hmem hx), t • x, d.Lsh.smul_mem t (hd.N_le_Lsh hx), ?_⟩
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (cO E π) t, hst, one_smul]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact d.N.add_mem (hd.L_le_N ha) (hd.smul_Lsh_mem_N (fun P => by rw [cO_cO]; exact hmem P) hb)

theorem std_of_gram (S : HSpace E) {m : ℕ} (h : S.rank = m) (hg : S.gram.reindex (finCongr h) (finCongr h) = 1) (x y : S.V) :
    stdH E m (Crd.co S h x) (Crd.co S h y) = S.hT x y := by
  subst h
  have hg' : ∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun hg a) b
    simpa [HSpace.gram, Matrix.one_apply] using this
  conv_rhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, LinearMap.sum_apply, hg',
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [stdH, Crd.co, starRingEnd_apply]

omit [NumberField E] in
theorem hStd_eq_stdH (x y : Fin n → E) : hStd E n x y = stdH E n x y := rfl

theorem mem_dual_crd (S : HSpace E) (co : S.V ≃ₗ[E] (Fin n → E)) (hco : ∀ x y, stdH E n (co x) (co y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (b : S.V) :
    b ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ co b ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) (L.map ((co : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) := by
  rw [mem_dual]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  constructor
  · intro H z hz
    obtain ⟨a, ha, rfl⟩ := hz
    have := H a ha
    simpa [hStd_eq_stdH, hco] using this
  · intro H a ha
    have := H (co a) ⟨a, ha, rfl⟩
    simpa [hStd_eq_stdH, hco] using this

theorem companion_crd (S : HSpace E) (co : S.V ≃ₗ[E] (Fin n → E)) (hco : ∀ x y, stdH E n (co x) (co y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (d : Deco E n ST SG) (hd : d.Ok)
    (hL : L.map ((co : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = d.L)
    (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal) (hcop : IsCoprime π (cO E π)) (y : S.V) :
    co y ∈ d.N ↔ ∃ a ∈ L, ∃ b ∈ Formalism.HermitianLatticesTheory.dual S.hT L, y = a + star (algebraMap (𝓞 E) E π) • b := by
  have hA : ∀ a, a ∈ L ↔ co a ∈ d.L := fun a => by
    rw [← hL]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨z, hz, e⟩ => co.injective e ▸ hz⟩
  have hB : ∀ b, b ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ co b ∈ d.Lsh := fun b => by
    rw [mem_dual_crd S co hco, hL]
    exact Iff.rfl
  have hc : ∀ v : Fin n → E, cO E π • v = star (algebraMap (𝓞 E) E π) • v := fun v => by
    rw [← algebraMap_smul E (cO E π) v, algebraMap_cO]
  rw [mem_N_iff d hd π hmem hcop]
  constructor
  · rintro ⟨a', ha', b', hb', e⟩
    refine ⟨co.symm a', (hA _).2 (by simpa using ha'), co.symm b', (hB _).2 (by simpa using hb'), co.injective ?_⟩
    rw [map_add (f := _), map_smul, co.apply_symm_apply, co.apply_symm_apply, e, hc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨co a, (hA a).1 ha, co b, (hB b).1 hb, ?_⟩
    rw [map_add (f := _), map_smul, hc]

end Gen

end GlobalTheory.Mem.Col2.MemLat


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mem.Col2.TC.memLatAt_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (O : GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).mem u).C), (∀ i c, (O.lat i c).1 = ((I.stp u I.mu0 i).rep c).1.1.deco.1.N) → MemLatAt O (X.piT u) := by
  intro B X I hI hP l Z u O hlat
  obtain ⟨-, -, -, hsp⟩ := spaces_in_coordinates I hI hP l Z
  intro i hi
  obtain ⟨hg, hl0, hL⟩ := hsp i hi
  have hL' := (hL u I.mu0).1
  set co := GlobalTheory.Mem.Col2.Crd.co ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) with hco
  have hiso := GlobalTheory.Mem.Col2.MemLat.std_of_gram _ _ hg
  refine ⟨co, hiso, ?_, ?_⟩
  · intro y
    rw [O.lattice_integral_coordinates]
    have h1 : co y ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ y ∈ ((I.rec7 l Z).sp.X i).L0 :=
      ⟨fun ⟨z, hz, e⟩ => co.injective e ▸ hz, fun h => ⟨y, h, rfl⟩⟩
    rw [← h1, hl0]
    refine forall_congr' fun k => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, ?_⟩
    rintro ⟨r, hr⟩
    rw [← hr]
    exact RingOfIntegers.isIntegral_coe r
  · intro c y
    rw [hlat i c]
    have hsep := sepElt_of_ok l.pr u
    have hmem : ∀ P : (B.primes X).vT u, (B.primes X).piT u ∈ P.1.asIdeal := fun P => by
      have := hsep.conj P
      rwa [cO_cO] at this
    have hLm : ((I.rec7 l Z).clsLat u i c).map ((co : ((I.rec7 l Z).sp.X i).V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) =
        (((I.stp u I.mu0 i).rep c).1.1.deco).1.L := hL' c
    refine (GlobalTheory.Mem.Col2.MemLat.companion_crd _ co hiso _ (((I.stp u I.mu0 i).rep c).1.1.deco).1 (((I.stp u I.mu0 i).rep c).1.1.deco).2
      hLm ((B.primes X).piT u) hmem (l.pr.piT_cop u) y).trans ?_
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmulEntry
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RedAdjCong

theorem conj_smul_entry {E R : Type} [CommRing E] [CommRing R] (φ : E →+* R) {m n : ℕ} (t : R) (d : E)
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (G : Matrix (Fin m) (Fin m) E)
    (H : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin m) (Fin n) E) (i : Fin m) (j : Fin n) :
    t * (A * (G * (d • M) * H).map φ * B) i j = φ d * (t * (A * (G * M * H).map φ * B) i j) := by
  have h2 : ∀ N : Matrix (Fin m) (Fin n) E, (d • N).map φ = φ d • N.map φ := by
    intro N
    ext b a
    simp
  rw [Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    mul_left_comm]

variable {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)

theorem adj_add (X Y : Fin S.rank → Fin T.rank → D.host.E) (i : Fin S.rank) (j : Fin T.rank) :
    uMat S T βS βT e (fun b => X b + Y b) i j = uMat S T βS βT e X i j + uMat S T βS βT e Y i j := by
  have h : (Matrix.of fun b a => D.sp.cm.sig ((X b + Y b) a) : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
      = (Matrix.of fun b a => D.sp.cm.sig (X b a)) + (Matrix.of fun b a => D.sp.cm.sig (Y b a)) := by
    ext b a
    simp
  unfold uMat
  rw [h, Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add (eToEAf D)), Matrix.mul_add, Matrix.add_mul,
    Matrix.add_apply, mul_add]

theorem adj_smul (c : D.host.E) (X : Fin S.rank → Fin T.rank → D.host.E) (i : Fin S.rank) (j : Fin T.rank) :
    uMat S T βS βT e (fun b => c • X b) i j = eToEAf D (D.sp.cm.sig c) * uMat S T βS βT e X i j := by
  have h : (Matrix.of fun b a => D.sp.cm.sig ((c • X b) a) : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
      = D.sp.cm.sig c • (Matrix.of fun b a => D.sp.cm.sig (X b a)) := by
    ext b a
    simp
  unfold uMat
  rw [h]
  exact conj_smul_entry (eToEAf D) _ _ _ _ _ _ _ i j

end GlobalTheory.RedAdjCong

namespace GlobalTheory


open GlobalTheory.RedAdjCong in
theorem redM_adj_congr : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)), (∀ x : Fin S.rank → La, IsIntM (uMat S T βS βT e fun b => ι (x b))) → ∀ (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E), (∀ a ∈ J, ∃ a' ∈ PP.asIdeal, (a' : D.host.E) = star (a : D.host.E)) → ∀ x x' : Fin S.rank → La, (∀ b, x b - x' b ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) → redM PP (uMat S T βS βT e fun b => ι (x' b)) = redM PP (uMat S T βS βT e fun b => ι (x b)) := by
  intro D S T βS βT e La _ _ ι hint J PP hJ x x' hx
  ext i j
  let f : (Fin S.rank → La) →+ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    AddMonoidHom.mk' (fun y => ⟨uMat S T βS βT e (fun b => ι (y b)) i j, hint y i j⟩) (by
      intro y z
      apply Subtype.ext
      show uMat S T βS βT e (fun b => ι (y b + z b)) i j = _ + _
      simp only [map_add (f := _)]
      exact adj_add S T βS βT e _ _ i j)
  let g : (Fin S.rank → La) →+ kP PP := (resS D.host.F PP).toAddMonoidHom.comp f
  have hg : ∀ y, redM PP (uMat S T βS βT e fun b => ι (y b)) i j = g y := by
    intro y
    unfold redM
    rw [dite_eq_left (hint y i j)]
    rfl
  have hs : ∀ a ∈ J, ∀ y : Fin S.rank → La, g (a • y) = 0 := by
    intro a ha y
    obtain ⟨a', ha', hc⟩ := hJ a ha
    have h1 : f (a • y) = oToS D.host.F D.host.E a' * f y := by
      apply Subtype.ext
      show uMat S T βS βT e (fun b => ι (a • y b)) i j = eToEAf D (a' : D.host.E) * uMat S T βS βT e (fun b => ι (y b)) i j
      rw [hc]
      simp only [map_smul]
      exact adj_smul S T βS βT e (a : D.host.E) (fun b => ι (y b)) i j
    show resS D.host.F PP (f (a • y)) = 0
    rw [h1, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', zero_mul]
  have h0 : ∀ (b : Fin S.rank) (l : La), l ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) → g (Pi.single b l) = 0 := by
    intro b l hl
    refine Submodule.smul_induction_on hl ?_ ?_
    · intro a ha m _
      rw [Pi.single_smul']
      exact hs a ha _
    · intro u v hu hv
      rw [Pi.single_add, map_add (f := _), hu, hv, add_zero]
  have h3 : g (x - x') = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.univ_sum_single (x - x'), map_sum]
    exact Finset.sum_eq_zero fun b _ => h0 b _ (hx b)
  rw [hg, hg]
  rw [map_sub, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory
end

