module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExistG2OfStandardLattices
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalProductsTendstoFrameStabiliser
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilVacuumEqResidueCharDetSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelFiniteVectorNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThPVecNe


set_option maxHeartbeats 1000000 in
theorem thPVec_ne_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (B : C.Bas), C.IsB B → ∀ ΛT : Lt D.host.E T.rank, IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsThPVecOf C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f → f ≠ 0 := by
  intro D S T C hn B hB ΛT hΛT βS βT hβS hβT Pg Q ξ f₀ f hf
  obtain ⟨hv, e, he, hth⟩ := hf
  have hS := GlobalTheory.Ker.Base.selfDualC_stdL (S := S) C.m.gS
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hidem : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hce : cA D e * cA D (cA D e) = 0 := by rw [← RingHom.map_mul, he.2, map_zero]
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hf0 : f₀ ≠ 0 := by
    intro h0
    obtain ⟨⟨p, hp⟩, hn1⟩ := hv.2.norm
    have h1 := hn1 p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hSB := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice S _ hS)
    (GlobalTheory.PlaceVec.selfDual_isFullLattice T _ hΛT) hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
    (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) (Pg ∪ Q)
    (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
      rw [GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
        GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)]
  obtain ⟨x, hx1, hx2, hx3⟩ := GlobalTheory.AdjDatumNe.exists_datum_ne_zero D S T βS βT Pg Q (Pg ∪ Q) ξ e hn he
    (fun PP hPP => Finset.mem_union_left _ hPP) (fun PP hPP => Finset.mem_union_right _ hPP)
  rw [hall Tm hTm]
  refine GlobalTheory.PlaceModelInj.placeModel_ne_zero D C.ψ S T (stdL D.host.E S.rank) ΛT (cA D e) f₀ _ Tm hv.1 hS hΛT hidem hce
    hinf hTm hf0 hSB ?_
  intro h0
  have := congrFun h0 x
  simp only [Pi.zero_apply] at this
  rw [if_pos ⟨hx1, hx2⟩] at this
  exact hx3 this

end GlobalTheory.ThPVecNe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalFunctionBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpArrowApprox

theorem ptF_eq_fock {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (p : GlobalTheory.Grid.Pol S T) :
    GlobalTheory.ChainFr.ptF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f p =
      GlobalTheory.Grid.fock ψ θ true S T f p := by
  have : (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS true S :=
    funext fun τ => GlobalTheory.PairLift.cart_frSgn true _ τ
  unfold GlobalTheory.ChainFr.ptF GlobalTheory.Grid.fock
  rw [this]
  rfl

theorem isFinVec_of_isVacF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D}
    {f : WO S.V T.V → ℂ}
    (h : GlobalTheory.ChainFr.IsVacF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f) :
    GlobalTheory.Grid.IsFinVec ψ θ true S T f :=
  ⟨h.1, fun τ => by have := h.2 τ; rwa [GlobalTheory.PairLift.cart_frSgn] at this⟩

end GlobalTheory.UpArrowApprox

namespace GlobalTheory.UpArrowApprox

end GlobalTheory.UpArrowApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecMemThetaSub
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVertexInv

theorem vec_mem_thetaSub : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    S.Z.vec d ∈ thetaSub W.ψ (G.pS p) (G.pT p) := by
  intro D T L sc G W U S t p hp d hv
  exact (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hv).1

end GlobalTheory.RowVertexInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexAtOfLevTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi Formalism.IndefR.Seed.Frm IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VertexFromTransport

theorem vertexAt_of_levTransport : ∀ {D : D7} {T : Type} (L : LevCh D T), (∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP) →
    ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Transport L.Pg (Wc D i) (Yc D 0) (L.βW i) (L.βY 0) →
    ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (Formalism.IndefR.Lev.EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf L.βY 0) (L.βW i) eW ι L.Pg := by
  intro D T L _ i ht
  have hr : (D.sp.Y 0).rank = (D.sp.W ((i : ℕ) + 1)).rank := by
    rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.W_rank _ (by omega) (by omega)]
    simp [Ranks.rankY]
  exact GlobalTheory.NormalFramesLevels.vertexAt_of_transport L.Pg _ hr _ _
    (GlobalTheory.NormalFramesLevels.transport_betaYOf L.Pg (Wc D i) (L.βW i) L.βY ht)

end GlobalTheory.VertexFromTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionVacuumEqResidueDetCharOfFrameStabilize
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacLaw

theorem redFn_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) (PP : Pl E) (a : Formalism.L2.Herm.intAf F E) (ha : resS F PP a = 1)
    {x y : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))} (hx : x ∈ St β) (hy : y ∈ St β)
    (h : ∀ i j, (a : TensorProduct F E (Formalism.L2.Herm.Af F)) * x.1 i j =
      (a : TensorProduct F E (Formalism.L2.Herm.Af F)) * y.1 i j) :
    redFn β PP x = redFn β PP y := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  rw [redFn_frGL, redFn_frGL]
  ext i j
  simp [frGL, intGL, Formalism.UG.bc] at h ⊢
  have hinv : (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))⁻¹ =
      ((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) :=
    (Matrix.coe_units_inv β).symm
  have hBiB : ((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) *
      (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) = 1 := Units.inv_mul β
  have back : ∀ Z : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)),
      ((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) *
        ((a : TensorProduct F E (Formalism.L2.Herm.Af F)) •
          ((β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) * Z *
            (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))⁻¹)) *
        (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) =
      (a : TensorProduct F E (Formalism.L2.Herm.Af F)) • Z := by
    intro Z
    rw [Matrix.mul_smul, Matrix.smul_mul, hinv]
    congr 1
    calc _ = (((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) *
            (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))) * Z *
          (((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) *
            (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))) := by
          simp only [Matrix.mul_assoc]
      _ = Z := by rw [hBiB, Matrix.one_mul, Matrix.mul_one]
  have hm : (a : TensorProduct F E (Formalism.L2.Herm.Af F)) •
        ((β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) * (x' : Matrix (Fin n) (Fin n) ↥(Formalism.L2.Herm.intAf F E)).map Subtype.val *
          (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))⁻¹) =
      (a : TensorProduct F E (Formalism.L2.Herm.Af F)) •
        ((β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) * (y' : Matrix (Fin n) (Fin n) ↥(Formalism.L2.Herm.intAf F E)).map Subtype.val *
          (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))⁻¹) := by
    ext k l
    simpa [Matrix.smul_apply] using h k l
  have hxy := congrArg (fun Z => Z i j) ((back _).symm.trans
    ((congrArg (fun W => ((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) * W *
      (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))) hm).trans (back _)))
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at hxy
  have hs : a * (x' : Matrix (Fin n) (Fin n) ↥(Formalism.L2.Herm.intAf F E)) i j = a * (y' : Matrix (Fin n) (Fin n) ↥(Formalism.L2.Herm.intAf F E)) i j :=
    Subtype.ext (by simpa using hxy)
  have hr := congrArg (resS F PP) hs
  simpa [map_mul, ha] using hr

variable {D : D7}

def detScal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (k : GA D V) : ℂˣ :=
  ∏ PP ∈ P, c PP (Matrix.GeneralLinearGroup.det (redFn β PP (finE V k)))

theorem detScal_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : detScal V β P c 1 = 1 := by
  simp [detScal, redFn, blockDiagonalExtendByOnePrimeField_one]

theorem detScal_mul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) {k l : GA D V} (hk : finE V k ∈ St β) (hl : finE V l ∈ St β) :
    detScal V β P c (k * l) = detScal V β P c k * detScal V β P c l := by
  unfold detScal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun PP _ => ?_
  simp only [map_mul]
  rw [show redFn β PP (finE V k * finE V l) = redFn β PP (finE V k) * redFn β PP (finE V l) from extendMatrixByIdentityAlongIndices_mul _ hk hl]
  simp only [map_mul]

theorem vacScal_eq {S T : HSp D} (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (P : Finset (Pl D.host.E)) (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (g : GA D S) (h : GA D T) :
    vacScal βS βT P cS cT g h =
      ((detScal S βS P (fun PP => (cT PP)⁻¹) g : ℂˣ) : ℂ) * ((detScal T βT P cS h : ℂˣ) : ℂ) := by
  simp [vacScal, detScal, Finset.prod_mul_distrib]

theorem law_of_local (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (e : AE D) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) {W : Type} (ρ : GA D V →* Module.End ℂ (W → ℂ)) (f : W → ℂ)
    (he : IsIdemSum e P) (hc : ∀ w, Continuous fun k => ρ k f w)
    (hloc : ∀ k ∈ GfC V, finE V k ∈ St β → ∀ v ε, IsPlaceIdem D v ε → SuppPl ε V k →
      ρ k f = ((detScal V β P c k : ℂˣ) : ℂ) • f) :
    ∀ g ∈ GfC V, finE V g ∈ St β → ρ g f = ((detScal V β P c g : ℂˣ) : ℂ) • f := by
  intro g hg hgS
  obtain ⟨γ, hγ, hs⟩ := _root_.GlobalTheory.LocalApprox.exists_local_approx D V β g hg hgS
  obtain ⟨⟨es, hes, rfl⟩, _⟩ := he

  have hfin : ∀ (k : GA D V) (i j : Fin V.rank),
      ((finE V k : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j =
        toEAf D (Formalism.L2.Theta.mt V k i j) := by
    intro k i j
    simp [finE, Formalism.UG.bc, finHom, Formalism.L2.Theta.mt, toEAf, swapAE, Formalism.L2.Theta.finPart]

  have hgen : ∀ k ∈ Subgroup.closure
      {k : GA D V | k ∈ GfC V ∧ finE V k ∈ St β ∧ ∃ v ε, IsPlaceIdem D v ε ∧ SuppPl ε V k},
      k ∈ GfC V ∧ finE V k ∈ St β ∧ ρ k f = ((detScal V β P c k : ℂˣ) : ℂ) • f := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨hk1, hk2, v, ε, hv, hsupp⟩ := hk
      exact ⟨hk1, hk2, hloc k hk1 hk2 v ε hv hsupp⟩
    | one =>
      refine ⟨(GfC V).one_mem, ?_, ?_⟩
      · rw [map_one]
        exact (St β).one_mem
      · simp [detScal_one]
    | mul k l _ _ hk hl =>
      obtain ⟨hk1, hk2, hk3⟩ := hk
      obtain ⟨hl1, hl2, hl3⟩ := hl
      refine ⟨(GfC V).mul_mem hk1 hl1, ?_, ?_⟩
      · rw [map_mul]
        exact (St β).mul_mem hk2 hl2
      · rw [detScal_mul V β P c hk2 hl2, ρ.map_mul, Module.End.mul_apply, hl3, LinearMap.map_smul, hk3, smul_smul,
          Units.val_mul, mul_comm]
    | inv k _ hk =>
      obtain ⟨hk1, hk2, hk3⟩ := hk
      have hk2' : finE V k⁻¹ ∈ St β := by
        rw [map_inv]
        exact (St β).inv_mem hk2
      refine ⟨(GfC V).inv_mem hk1, hk2', ?_⟩
      have hd : ((detScal V β P c k⁻¹ : ℂˣ) : ℂ) * ((detScal V β P c k : ℂˣ) : ℂ) = 1 := by
        rw [← Units.val_mul, ← detScal_mul V β P c hk2' hk2, inv_mul_cancel, detScal_one, Units.val_one]
      have h1 : f = ((detScal V β P c k : ℂˣ) : ℂ) • ρ k⁻¹ f := by
        calc f = ρ (k⁻¹ * k) f := by rw [inv_mul_cancel, ρ.map_one, Module.End.one_apply]
          _ = _ := by rw [ρ.map_mul, Module.End.mul_apply, hk3, LinearMap.map_smul]
      calc ρ k⁻¹ f = (((detScal V β P c k⁻¹ : ℂˣ) : ℂ) * ((detScal V β P c k : ℂˣ) : ℂ)) • ρ k⁻¹ f := by
            rw [hd, one_smul]
        _ = _ := by rw [mul_smul, ← h1]

  have hev : ∀ᶠ s in Filter.atTop, detScal V β P c (γ s) = detScal V β P c g := by
    have hP : ∀ PP ∈ P, ∀ᶠ s in Filter.atTop, redFn β PP (finE V (γ s)) = redFn β PP (finE V g) := by
      intro PP hPP
      obtain ⟨hsp, _⟩ := hes PP hPP
      obtain ⟨hee, hec, v, ε, hv, hsum⟩ := hsp
      obtain ⟨hint, hres⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hPP)
      have hfix : es PP * algebraMap (AF D.host.F) (AE D) ε = es PP := by
        rw [← hsum, mul_add, hee, hec, add_zero]
      filter_upwards [Filter.eventually_ge_atTop {v}] with s hsv
      have hvs : v ∈ s := Finset.singleton_subset_iff.mp hsv
      refine redFn_congr β PP ⟨toEAf D (es PP), hint⟩ hres (hgen (γ s) (hs s).1).2.1 hgS ?_
      intro i j
      have hij := (hs s).2 v hvs ε hv i j
      dsimp only
      rw [hfin, hfin, ← map_mul (toEAf D), ← map_mul (toEAf D), ← hfix, mul_assoc, mul_assoc, hij]
    filter_upwards [(Filter.eventually_all_finset P).2 hP] with s hs'
    unfold detScal
    exact Finset.prod_congr rfl fun PP hPP => by rw [hs' PP hPP]

  funext w
  have h1 : Filter.Tendsto (fun s => ρ (γ s) f w) Filter.atTop (nhds (ρ g f w)) :=
    ((hc w).tendsto g).comp hγ
  have h2 : Filter.Tendsto (fun s => ρ (γ s) f w) Filter.atTop
      (nhds ((((detScal V β P c g : ℂˣ) : ℂ) • f) w)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with s hs'
    rw [(hgen (γ s) (hs s).1).2.2, hs']
  exact tendsto_nhds_unique h1 h2

theorem suppPl_one (ε : AF D.host.F) (V : HSp D) : SuppPl ε V 1 := by
  intro i j
  simp [SuppPl, Formalism.L2.Theta.mt]

theorem vac_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (θ : InfFam D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (P : Finset (Pl D.host.E)) (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f : WO S T → ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e P → TameOn χS e P cS → TameOn χT e P cT → (∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε) → IsVacO ψ θ S T sS sT ΛS ΛT f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, finE S g ∈ St βS → finE T h ∈ St βT → om (g, h) f = vacScal βS βT P cS cT g h • f := by
  intro D ψ S T χS χT om θ sS sT ΛS ΛT βS βT e P cS cT f hW hθ hS hT hsS hsT hΛS hΛT hfS hfT he htS htT hfx hvac g hg h hh hgS hhT

  have loc := _root_.GlobalTheory.VacLoc.om_vacuum_eq_vacScal_smul D ψ S T χS χT om θ sS sT ΛS ΛT βS βT e P cS cT f hW hθ hS hT hsS hsT hΛS hΛT hfS hfT he
    htS htT hfx hvac

  have hcont : ∀ w, Continuous fun p : GA D S × GA D T => om p f w := hW.9 f hvac.2.2
  have hS1 : finE S 1 ∈ St βS := by
    rw [map_one]
    exact (St βS).one_mem
  have hT1 : finE T 1 ∈ St βT := by
    rw [map_one]
    exact (St βT).one_mem

  have lawS : ∀ k ∈ GfC S, finE S k ∈ St βS →
      om (k, 1) f = ((detScal S βS P (fun PP => (cT PP)⁻¹) k : ℂˣ) : ℂ) • f :=
    law_of_local S βS e P (fun PP => (cT PP)⁻¹) (om.comp (MonoidHom.inl (GA D S) (GA D T))) f he
      (fun w => (hcont w).comp (continuous_id.prodMk continuous_const)) (by
        intro k hk hkS v ε hv hsupp
        have hl := loc k hk 1 (GfC T).one_mem hkS hT1 v ε hv hsupp (suppPl_one ε T)
        rw [vacScal_eq, detScal_one, Units.val_one, mul_one] at hl
        exact hl)

  have lawT : ∀ k ∈ GfC T, finE T k ∈ St βT → om (1, k) f = ((detScal T βT P cS k : ℂˣ) : ℂ) • f :=
    law_of_local T βT e P cS (om.comp (MonoidHom.inr (GA D S) (GA D T))) f he
      (fun w => (hcont w).comp (continuous_const.prodMk continuous_id)) (by
        intro k hk hkT v ε hv hsupp
        have hl := loc 1 (GfC S).one_mem k hk hS1 hkT v ε hv (suppPl_one ε S) hsupp
        rw [vacScal_eq, detScal_one, Units.val_one, one_mul] at hl
        exact hl)

  have hsplit : ((g, h) : GA D S × GA D T) = (g, 1) * (1, h) := by
    simp
  rw [hsplit, om.map_mul, Module.End.mul_apply, lawT h hh hhT, LinearMap.map_smul, lawS g hg hgS, smul_smul, vacScal_eq,
    mul_comm]

end GlobalTheory.VacLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRealPointFockVectorPositiveDefiniteDet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealFockPos

variable {D : D7}

theorem det_ne_zero_of_frame {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) :
    G.det ≠ 0 ∧ B.det ≠ 0 := by
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h2
  exact ⟨right_ne_zero_of_mul (left_ne_zero_of_mul_eq_one h2), right_ne_zero_of_mul_eq_one h2⟩

theorem mul_eq_mul_conj {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.det ≠ 0) :
    A * B = B * (B⁻¹ * A * B) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.one_mul]

theorem scalar_identity (G H : ℂ) (hG : G ≠ 0) (hH : H ≠ 0) (e₁ e₂ : ℤ) (nS nT : ℕ) :
    (G ^ (-e₂ - (nT : ℤ)))⁻¹ * H ^ (e₁ - (nS : ℤ)) * (H ^ nS * G⁻¹ ^ nT) = G ^ e₂ * H ^ e₁ := by
  rw [inv_pow, ← zpow_natCast H, ← zpow_natCast G, ← zpow_neg G, ← zpow_neg G]
  calc G ^ (-(-e₂ - (nT : ℤ))) * H ^ (e₁ - (nS : ℤ)) * (H ^ (nS : ℤ) * G ^ (-(nT : ℤ)))
      = G ^ (-(-e₂ - (nT : ℤ))) * G ^ (-(nT : ℤ)) * (H ^ (e₁ - (nS : ℤ)) * H ^ (nS : ℤ)) := by ring
    _ = G ^ (-(-e₂ - (nT : ℤ)) + -(nT : ℤ)) * H ^ (e₁ - (nS : ℤ) + (nS : ℤ)) := by
      rw [← zpow_add₀ hG, ← zpow_add₀ hH]
    _ = G ^ e₂ * H ^ e₁ := by congr 2 <;> ring

theorem om_pureTensorO_pos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ + (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt S g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) (fun τ => (((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ)⁻¹)ᵀ) P) := by
  intro D ψ θ S T χS χT om hom hθ BS BT hBS hBT a b ha hb e₁ e₂ he₁ he₂ f hf hv g hg h hh P
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hψ := hom.std
  have dS : ∀ τ, (gramAt D S τ).det ≠ 0 ∧ (BS τ).det ≠ 0 := fun τ => det_ne_zero_of_frame (hBS τ)
  have dT : ∀ τ, (gramAt D T τ).det ≠ 0 ∧ (BT τ).det ≠ 0 := fun τ => det_ne_zero_of_frame (hBT τ)
  have cS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBS τ)
  have cT : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBT τ)
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (fun τ => (dS τ).1) g hg
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (fun τ => (dT τ).1) h hh
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ χS χT om η hη hom (fun _ => 1) (fun _ => 1)
    cS cT g hg h hh (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) x y hx hy f hf hv
  have expT : ∀ τ, HasInfExp D (χT * (η ^ T.rank)⁻¹) τ ((-e₂ τ - T.rank : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hb τ) (hη.2.2.2 τ) T.rank
    convert h1 using 1
    push_cast; rw [he₂]; ring
  have expS : ∀ τ, HasInfExp D (χS * (η ^ S.rank)⁻¹) τ ((e₁ τ - S.rank : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (ha τ) (hη.2.2.2 τ) S.rank
    convert h1 using 1
    push_cast; rw [he₁]; ring
  have vx := hxv _ (fun τ => -e₂ τ - T.rank) expT
  have vy := hyv _ (fun τ => e₁ τ - S.rank) expS
  have hmain := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ (fun _ => 1) (fun _ => 1) BS
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) (fun _ => 1) (fun _ => 1) BT
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) g h (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) (fun τ => rfl) f hf P).2
  have fS : (fun τ => compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) =
      fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) :=
    funext fun τ => mul_eq_mul_conj _ _ (dS τ).2
  have fT : (fun τ => compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) =
      fun τ => BT τ * ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) :=
    funext fun τ => mul_eq_mul_conj _ _ (dT τ).2
  rw [hmain, hvac, GlobalTheory.FiniteFock.pureTensorO_smul, fS, fT,
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ BS _ BT _ f hf P]
  congr 1
  rw [Circle.coe_mul, Circle.coe_inv, vx, vy, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g)
  rw [Matrix.det_mul, Matrix.det_one] at inv
  have g0 := left_ne_zero_of_mul_eq_one inv
  have inv' := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ h)
  rw [Matrix.det_mul, Matrix.det_one] at inv'
  have h0 := left_ne_zero_of_mul_eq_one inv'
  rw [GlobalTheory.KJReal.detPlus_one_one, eq_inv_of_mul_eq_one_right inv]
  exact scalar_identity _ _ g0 h0 (e₁ τ) (e₂ τ) S.rank T.rank

end GlobalTheory.RealFockPos

end
end

