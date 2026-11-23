module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0702
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0533
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0683
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepNoFormsOutsideLiftRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistDataLowerBlockUniversalCharacter
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0468
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionCompatibleAtReadIdentifications
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.divTied3_read : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → (Fintype.card G = D.what₂.restRowsFiniteGroupCard → Nat.card F.P0 = Nat.card F.P1 * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) → GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)) → DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C) ∧ (MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C)) := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C sEE Xd JM hP hH hGrp
  obtain ⟨hcard, hidx, hr, ht, hv0⟩ := GlobalTheory.Mem.R3.pins_card_index_ranks D G Pl0 I0 T A3 Ks R F cG hP
  obtain ⟨hsh, hba⟩ := GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  obtain ⟨hth, hthT⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  refine ⟨?_, ?_⟩
  · refine
      { ranks := ⟨rfl, hr, ht⟩
        grp := hGrp hcard hidx
        tup := ⟨Y.tup0, Y.muAt, hv0, Function.LeftInverse.injective (g := Y.tupT) Y.tupT_tup⟩
        mu1 := rfl
        sharp := hsh
        base := hba
        mt := ⟨Y.formsL, Y.latL⟩
        th := hth
        cols := ⟨C.bij, C.nu⟩ }
  · intro hMj hIdx hBu hBt
    obtain ⟨hRR1, hRR0⟩ := GlobalTheory.T.rowLattices_metrics_agree_of_realGroupTheorems hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
    exact
      { sharpRR := hRR1
        baseRR := hRR0
        divisionRows_rationalLift := GlobalTheory.T.zeroSubspace_spanned_by_dataZeroSubspace_lifts D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
        thTheta := hthT
        num := GlobalTheory.T.numbers_eq_concreteNumbers_at_baseLevel D G Pl0 I0 T A3 Ks R F cG X0 Y Z Xd JM hP hH hMj hIdx
        colsBk := GlobalTheory.T.rationalPairing_eq_columnPairing hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z C sEE hP hH hBu hBt }
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorEmbeddingKappaEqRowsKappaAtInfinitePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.KapRow

theorem kapR_eq_rows_kappa : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → (∀ σ, Xd.kapR σ = kapSharp D) → ∀ e : D.what₂.LL →+* ℂ, Xd.kapR e = (s1Of R F).κ (InfinitePlace.mk e) := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd hP hH hL hne hk e
  rw [hk e]
  exact GlobalTheory.T.kappaConstant_sharpLevel_eq_dataKappaConstant hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hne

end GlobalTheory.KapRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewTwistLamFull
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.SerCopy

def lamT {D : D7} (N : TwNew D) (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat N.toD7 := ⟨N.cf Z.C, Z.q0, Z.w0, Z.c, Z.chi⟩

theorem lamT_spec {D : D7} (N : TwNew D) {cf : Formalism.L2.Host.CharFrame D} {Z : GlobalTheory.LamTie.LamDat D}
    (h : Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull N.tw Z) :
    (lamT N Z).Ok ∧ (lamT N Z).Teich ∧ (lamT N Z).C = N.cf cf ∧ (lamT N Z).q0 = AbsolutelyIrreducibleSpan.q0 N.toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull N.toD7.ntw (lamT N Z) :=
  ⟨⟨(by with_unfolding_all exact (h.1.places :)), (by with_unfolding_all exact (h.1.aux :)), (by with_unfolding_all exact (h.1.big :))⟩, (by with_unfolding_all exact (h.2.1 :)), congrArg N.cf h.2.2.1, (by with_unfolding_all exact (h.2.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2.2 :))⟩

theorem exists_prepared (hA : GlobalTheory.Published.GlobalArtinReciprocity) {D : D7} {cf : Formalism.L2.Host.CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ) (hV : ValLL0 D cf)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) :
    ∃ N : TwNew D, (∀ Z : GlobalTheory.LamTie.LamDat D, GlobalTheory.LamTie.IsLamTieFull D.ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧
      (∀ i', ∃ i, N.tw.S0 i' = D.ntw.S0 i ∧ N.tw.l i' = D.ntw.l i) ∧ NoOff N.toD7 ∧ GlobalTheory.UnivChar.IsUnivChar N.toD7.nexp ∧
      ∃ Bs' : SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ, TauTrue Bs'.exp := by
  obtain ⟨N, h1, h2, h3, ⟨B1⟩⟩ := GlobalTheory.T.secondStep_no_forms_outside_liftRange D cf Rw low Pq S hL eig θ Bs
  obtain ⟨τ, hτ⟩ := GlobalTheory.TwInputs.exists_tau_family hA N.toD7 _ _ _ _ _ _ _ _ B1
    ⟨(by with_unfolding_all exact (hV.mu0 :)), (by with_unfolding_all exact (hV.eta :)), (by with_unfolding_all exact (hV.chiPsi :)), (by with_unfolding_all exact (hV.del :)), (by with_unfolding_all exact (hV.del' :))⟩ ((by with_unfolding_all exact (hr :)))
  obtain ⟨⟨tw, ex, h0, th, br, hbr⟩, e, g1, g2, B2, g3⟩ := _root_.GlobalTheory.TrueTau.exists_trueTau N.toD7 _ _ _ _ _ _ _ _ B1 τ hτ
  dsimp only at e
  subst e
  exact ⟨⟨N.tw, (by with_unfolding_all exact (ex :)), (by with_unfolding_all exact (h0 :)), (by with_unfolding_all exact (th :)), (by with_unfolding_all exact (br :)), (by with_unfolding_all exact (hbr :))⟩, h1, h2, (by with_unfolding_all exact ((g1 h3) :)), (by with_unfolding_all exact (g2 :)), (by with_unfolding_all exact (B2 :)), (by with_unfolding_all exact (g3 :))⟩

theorem sideB_tau_congr {D : D7} {cf cf' : Formalism.L2.Host.CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S S' : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S'.WL j)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (e1 : cf = cf') (e4 : Pq = Pq') (e5 : S = S') (e6 : HEq hL hL')
    (h : ∃ Bs : SideB D cf Rw low Pq S hL eig θ, TauTrue Bs.exp) : ∃ Bs : SideB D cf' Rw low Pq' S' hL' eig θ, TauTrue Bs.exp := by
  subst e1 e4 e5
  cases e6
  exact h

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def PreAt {Z : w.Lt} (z : Dat (w.st Z) w.I P.hX T P.Wt) (Rw : RowSide (w.st Z).toD7)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) → PlE (w.st Z).toD7.host) {α : Type} (h₀ : α)
    (eig : ℕ → (w.st Z).toD7.what₂.FT → ℕ → PlE (w.st Z).toD7.host → ↥(w.st Z).toD7.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.st Z).toD7.host.g kk)) →* (↥(w.st Z).toD7.LL0)ˣ) : Prop :=
  z.R.C = TC.cf w.I w.l Z ∧ ∃ kKs hk hL, HEq hL h₀ ∧
    ∃ (Bs : SideB (w.st Z).toD7 z.R.C Rw (lowAll (w.st Z).toD7) Pq (ratDatR z.R z.cG kKs hk) hL eig θ) (hF : _),
      TauTrue Bs.exp ∧ Nonempty (PreTie (ysOf Bs) z.geo.v₀ Bs.exp hF Pq)

theorem preAt_congr {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} {Rw Rw' Pq Pq'} {α α' : Type} {h₀ : α} {h₀' : α'}
    {eig eig' θ θ'} (e0 : z = z') (e1 : Rw = Rw') (e2 : Pq = Pq') (e3 : HEq h₀ h₀') (e4 : eig = eig') (e5 : θ = θ')
    (h : PreAt (P := P) z Rw Pq h₀ eig θ) : PreAt (P := P) z' Rw' Pq' h₀' eig' θ' := by
  subst e0 e1 e2 e4 e5
  obtain ⟨g1, k, hk, hf, g2, g3⟩ := h
  exact ⟨g1, k, hk, hf, g2.trans e3, g3⟩

section Install

variable {x : St P} {N₁ : TwNew (Dof x)}
  {kKs : (Up.datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y : (Up.datTw x N₁).core.Q.c.F,
    ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) =
      algebraMap (Up.datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {cf : Formalism.L2.Host.CharFrame (DN x N₁)} {Rw : RowSide (DN x N₁)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x N₁).host.E)) → PlE (DN x N₁).host}
  {hf : ∀ j, ℕ → PlE (DN x N₁).host →
    Module.End (DN x N₁).what₂.LL ((ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk).WL j)}
  {eig : ℕ → (DN x N₁).what₂.FT → ℕ → PlE (DN x N₁).host → ↥(DN x N₁).LL0}
  {θ : ∀ kk : Fin 2, Multiplicative (ZMod ((DN x N₁).host.g kk)) →* (↥(DN x N₁).LL0)ˣ}
  {Bs : SideB (DN x N₁) cf Rw (lowAll (DN x N₁)) Pq
    (ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk) hf eig θ}
  {hF : (DN x N₁).host.F = maximalRealSubfield (DN x N₁).host.E}

abbrev kwP (p : PreTie (ysOf Bs) (Up.datTw x N₁).geo.v₀ Bs.exp hF Pq) : TwNew (DN x N₁) :=
  keepTw (DN x N₁) p.Dat (PreTie.th (D := DN x N₁) p) p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth

def bsP (p : PreTie (ysOf Bs) (Up.datTw x N₁).geo.v₀ Bs.exp hF Pq) :
    SideB (kwP p).toD7 ((kwP p).cf cf) ((kwP p).row Rw)
      (lowAll (DN x (SerCopy.nP p))) Pq
      ((kwP p).rat (ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk)) hf eig θ := by
    exact keepSideB (DN x N₁) p.Dat (PreTie.th (D := DN x N₁) p) p.lev p.thPsi
      p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth p.hU cf Rw _ Pq _ hf eig θ Bs

end Install


end GlobalTheory.HeightCounting.SerCopy

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowFormsAdelicDecoratedLatticesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowForms_adelic_decoratedLattices : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ s : ∀ t, Seed.RowSideT (famR X I hX U Xg tr) L cX (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) t, (∀ t,       (∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
        eG ((s t).act_tie.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∧
      Bridge.CoefTie X.toD7.sp.X' cX.coef (s t).pres (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
        (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') (s t).pres ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1)) ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => (s t).pres.extL φ)  := by
  first | exact @GlobalTheory.Mem.R3.RowsRead.exists_rowSide | exact GlobalTheory.Mem.R3.RowsRead.exists_rowSide | (intros; apply GlobalTheory.Mem.R3.RowsRead.exists_rowSide <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lb1OfRestagingBound
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.SerCarry

open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr

theorem sideB_facts {D : D7} {cf Rw Pq} {S : RatDat D.ntw} {hL eig θ} (B : SideB D cf Rw (lowAll D) Pq S hL eig θ) {eF}
    (h : eF = B.eF) : HkLaw D S eF hL B.hs B.cHk ∧ LowIn D ∧ PqLaw B.exp Pq := by
  subst h
  refine ⟨B.hkEq, fun i p hp P hP => ?_, B.pq⟩
  rw [B.tw.ringSpec_excludedPlaces_eq i]
  exact Or.inr (B.tw.concreteTwistFrame_extraExcluded_over_smallPrimes i p hp hP)

end GlobalTheory.HeightCounting.SerCarry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsStandardChainData
section
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem underQ_iff {B : Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) (a : I.ι) (v : HeightOneSpectrum (𝓞 B.host.F)) :
    I.UnderQ a v ↔ ∃ w ∈ Formalism.L2.Host.aboveF (L := B.host.E) B.host.F v, ¬ (I.xi a).UnrAt w := by
  have hq := GlobalTheory.Mem.ReadTwist.mem_qprime_iff (hI.xi_reads a) v
  have hab : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w ∈ Formalism.L2.Host.aboveF (L := B.host.E) B.host.F v ↔ w.under (𝓞 B.host.F) = v := fun w => by
    unfold Formalism.L2.Host.aboveF
    rw [Set.Finite.mem_toFinset]
    rfl
  constructor
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨w, hw, hu⟩ := hq.1 ((GlobalTheory.TwistPlaces.mem_QE_iff hI.sel_ok (I.tup a)).1 hP).1
    exact ⟨w, (hab w).2 hw, hu⟩
  · rintro ⟨w, hw, hu⟩
    have hv := hq.2 ⟨w, (hab w).1 hw, hu⟩
    exact ⟨I.sel v, (Formalism.L2.Col.mem_QE I.sel (I.tup a) _).2 ⟨v, hv, rfl⟩, GlobalTheory.TwistPlaces.under_eq_iff.2 (hI.sel_ok v)⟩

theorem carH_of_cols {D : D7} (C : ColsTiedSym D) : CarH C.herm.base C.forms := by
  refine ⟨C.eV, ?_, C.car0, C.carC, C.carM, C.sp, C.fr0⟩
  intro u v a
  rw [C.res u]
  exact (C.herm.atT u).res_F v a

theorem colsTwPTiedS_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch) (C : ColsTiedSym (I.rec7 l Z)), tp.xi = I.xi → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → ∃ t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z), I.StdTw l Z l0 t := by
  intro B X I hI hP l Z l0 nch tp C hxi hC hLv
  have hQ : ∀ a v, tp.InQ' a v ↔ I.UnderQ a v := fun a v => by
    rw [underQ_iff hI a v]
    unfold Formalism.L2.Host.TupTied.InQ'
    rw [hxi]
    exact Iff.rfl
  have hF : ∀ u, I.StdF l Z u (C.forms u) ∧ I.StdLvC l Z u (C.forms u) := fun u => ⟨hC u, hLv u⟩
  obtain ⟨T, J, W, hM, hW, ⟨lvJ⟩, hPt⟩ := GlobalTheory.T.trueColumnChoice_exists_chainData_with_basePoints I hI hP l Z l0 (fun a v => tp.InQ' a v) C.herm.base C.forms hQ hF (carH_of_cols C)
  obtain ⟨⟨Lv, hL⟩, ⟨same⟩⟩ := _root_.GlobalTheory.Mem.Col2.TC.tw_lv_tied_and_same I hI hP l Z l0 (fun a v => tp.InQ' a v) C.herm.base C.forms T J W hF hW
  obtain ⟨Pt, E, hG, hS⟩ := GlobalTheory.T.tupleLayerCompatibilities_of_X_prime I hI hP l Z l0 (fun a v => tp.InQ' a v) C.herm.base C.forms T J W Lv hQ hF hW hL hPt
  exact ⟨{ ch := T, chJ := J, chM := hM, forms := W, lv := Lv, same := same, lvJ := lvJ, pt := Pt, ptG := hG, ptE := E }, hW, hL, hS⟩

end GlobalTheory.Mem.Col2.TC

end
end

