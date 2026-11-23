module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0301
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0416
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealisedE
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReTo0S
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df GlobalTheory.Mem.Db NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Db.DivTr

open Formalism.L2.Forms GlobalTheory.Mem.Top.ColOwe

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)


set_option maxHeartbeats 4000000 in
def atTTS {u : D.what₂.Word} (A : AtTTied (D := D) u) : AtTTied (D := setDiv D N h) u := { A with }


set_option maxHeartbeats 4000000 in
def forms0S {u : D.what₂.Word} (F : Forms0 D u) : Forms0 (setDiv D N h) u :=
  { F with
    atT := atTTS N h F.atT
    cls0 := { F.cls0 with }
    val0 := { F.val0 with }
    lv0 := { F.lv0 with } }


set_option maxHeartbeats 4000000 in
def herm0S (H : Formalism.L2.Herm.Herm0 D) : Formalism.L2.Herm.Herm0 (setDiv D N h) := { H with }


set_option maxHeartbeats 4000000 in
def fullS (X : Formalism.L2.Herm.FullTiedS D) : Formalism.L2.Herm.FullTiedS (setDiv D N h) :=
  { X with
    base := { X.base with }
    atT := fun u => { X.atT u with }
    ad := { X.ad with } }

set_option maxHeartbeats 4000000 in
theorem fullS_to0 (X : Formalism.L2.Herm.FullTiedS D) : (fullS N h X).to0 = herm0S N h X.to0 := rfl


set_option maxHeartbeats 4000000 in
def gS {Gt : GatTies D} {c : LatCmp D} (g : Formalism.L2.G.GroupCompatibilityAll D Gt c) :
    Formalism.L2.G.GroupCompatibilityAll (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) where
  herm := herm0S N h g.herm
  forms := fun u => forms0S N h (g.forms u)
  cmp := { g.cmp with }
  ring := g.ring
  gat := g.gat

end Gen

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

-- Build the transported records at the same index used by the column data.
set_option maxHeartbeats 4000000 in
def fullSZ (X : Formalism.L2.Herm.FullTiedS (w.D Z)) :
    Formalism.L2.Herm.FullTiedS (w.D (setDivZ Z N h)) :=
  { X with
    base := { X.base with }
    atT := fun u => { X.atT u with }
    ad := { X.ad with } }

set_option maxHeartbeats 4000000 in
def forms0SZ {u : B.Word} (F : Forms0 (w.D Z) u) :
    Forms0 (w.D (setDivZ Z N h)) u :=
  { F with
    atT := atTTRe (setDivZ Z N h) F.atT
    cls0 := clsRe (setDivZ Z N h) F.cls0
    val0 := valRe (setDivZ Z N h) F.val0
    lv0 := lvRe (setDivZ Z N h) F.lv0 }

set_option maxHeartbeats 4000000 in
theorem fullS_cols (X : Formalism.L2.Herm.FullTiedS (w.D Z)) :
    (fullSZ w Z N h X).cols = hermRe (setDivZ Z N h) X.cols := rfl

set_option maxHeartbeats 4000000 in
theorem colsRe_to0S (C : ColsTiedSym (w.D Z)) (u : B.Word) :
    ((colsRe (setDivZ Z N h) C).forms u).to0 = forms0SZ w Z N h (C.forms u).to0 := rfl


set_option maxHeartbeats 8000000 in
theorem stdC_tr (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C) :
    TC.StdC w.I w.l (setDivZ Z N h) (colsRe (setDivZ Z N h) C) := fun u =>
  { hC u with gl := { (hC u).gl with } }


set_option maxHeartbeats 8000000 in
def colTTr (t : ColT w Z) : ColT w (setDivZ Z N h) where
  C := colsRe (setDivZ Z N h) t.C
  std := stdC_tr w Z N h t.C t.std
  stdLv := fun u => t.stdLv u
  full := ⟨fullSZ w Z N h t.full.1,
    (fullS_cols w Z N h t.full.1).trans (congrArg (hermRe (setDivZ Z N h)) t.full.2)⟩
  stdDt := t.stdDt
  Gt := { t.Gt with }
  cmp := { t.cmp with }
  g :=
    { herm := { t.g.herm with }
      forms := fun u => forms0SZ w Z N h (t.g.forms u)
      cmp := { t.g.cmp with }
      ring := t.g.ring
      gat := t.g.gat }
  herm_eq := congrArg
    (fun H : Formalism.L2.Herm.Herm0 (w.D Z) =>
      ({ H with } : Formalism.L2.Herm.Herm0 (w.D (setDivZ Z N h)))) t.herm_eq
  forms_eq := funext fun u =>
    (congrArg (forms0SZ w Z N h) (congrFun t.forms_eq u)).trans (colsRe_to0S w Z N h t.C u).symm
  gpl := t.gpl

end GlobalTheory.Mem.Db.DivTr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruentAutomorphismsLiftStepGroupElements
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

set_option maxHeartbeats 1600000 in
private theorem mem_GLint_and_exists_liftsInv_of_congE : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K),
    MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
      ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' →
        ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := by
  classical
  intro B X I hI u a i hi b P g z hmid
  have hO := hI.idx_ok a
  have hpr := (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P
    ((I.idx a).h i (Idx.get b hi) P) g).mp ⟨z, hmid⟩
  have hgi : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 := hO.int i (Idx.get b hi) P hpr
  refine ⟨hgi, fun g' hg' hc => ?_⟩
  have hb : b.1 = some (Idx.get b hi) := (Option.some_get _).symm
  have hstd : ∀ (k : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) {x : Sp B.fields.E (B.R.N i)},
      x ∈ stdAt B.fields.E (B.R.N i) P.1 → k.1 x ∈ stdAt B.fields.E (B.R.N i) P.1 :=
    fun k _ hx => GlobalTheory.TopStep.glint_mem k hx
  refine ⟨⟨1, ⟨fun w => if h : w.1 = P.1 then
      (GlobalTheory.TopStep.redGL (B.R.N i) w.1 ⟨g, by rw [h]; exact hgi⟩)⁻¹ else 1, ?_⟩,
    ⟨fun w => if h : w.1 = P.1 then
      (⟨g', by rw [h]; exact hg'⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) w.1))⁻¹ else 1, ?_⟩⟩, ?_, ?_, ?_⟩
  · rw [LevFam.grp, Subgroup.mem_pi]
    intro w _
    simp only [levGAt, hb, Option.elim]
    by_cases hw : w.1 = P.1
    · rw [dite_eq_left hw]
      apply inv_mem
      rw [hO.grpG]
      obtain ⟨w, hwG⟩ := w
      simp only at hw
      subst hw
      exact ⟨g, hpr, fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hgi⟩ hx⟩
    · rw [dite_eq_right hw]
      exact one_mem _
  · rw [LevQFam.grp, Subgroup.mem_pi]
    intro w _
    simp only [levQAt, hb, Option.elim]
    by_cases hw : w.1 = P.1
    · rw [dite_eq_left hw]
      apply inv_mem
      obtain ⟨w, hwQ⟩ := w
      simp only at hw
      subst hw
      have hgQ : (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) ∈
          ((I.idx a).levQ i (Idx.get b hi) ⟨P.1, hwQ⟩).H := by
        rw [hO.grpQ, Subgroup.mem_subgroupOf]
        exact hpr
      set k := (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1))⁻¹ with hk
      have hkg : ∀ v, k.1 (g v) = v := by
        intro v
        have h1 : k * (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) = 1 := inv_mul_cancel _
        exact congrArg (fun m : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1) => m.1 v) h1
      have hdeep := levQ_deep I hI a i hi (Idx.get b hi) P hwQ (k * ⟨g', hg'⟩)
      obtain ⟨hd, -⟩ := hdeep (by
        intro x hx
        have hneg := Submodule.neg_mem _ (hstd k (hc x hx))
        rw [map_smul, map_sub, hkg, ← smul_neg, neg_sub] at hneg
        exact hneg)
      have e2 : (⟨g', hg'⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) = ⟨g, hgi⟩ * (k * ⟨g', hg'⟩) := by
        rw [hk, mul_inv_cancel_left]
      rw [e2]
      exact mul_mem hgQ hd
    · rw [dite_eq_right hw]
      exact one_mem _
  · exact map_one (ufGL B.fields.E (B.R.N i))
  · refine ⟨hg', ?_, ?_⟩
    · intro h x hx
      dsimp only
      rw [dite_eq_left rfl, inv_inv, ← GlobalTheory.TopStep.redV_redGL ⟨g, hgi⟩ hx]
      have hD : (I.cst a).D P = 1 := hO.depthG P h
      have hq := hc x hx
      rw [hD, pow_one] at hq
      funext l
      have h1 : IntAt P.1 (g x l) := GlobalTheory.TopStep.mem_stdAt.mp (hstd ⟨g, hgi⟩ hx) l
      have h2 : IntAt P.1 (g' x l) := GlobalTheory.TopStep.mem_stdAt.mp (hstd ⟨g', hg'⟩ hx) l
      have h3 : IntAt P.1 (((qOf P.1 : ℕ) : B.fields.E)⁻¹ * (g x l - g' x l)) := GlobalTheory.TopStep.mem_stdAt.mp hq l
      have h0 := GlobalTheory.TopStep.redP_eq_zero_of_div (P := P.1) (a := g x l - g' x l) (by rw [div_eq_inv_mul]; exact h3)
      rw [GlobalTheory.TopStep.reduction_sub h1 h2, sub_eq_zero] at h0
      exact h0.symm
    · intro h
      dsimp only
      rw [dite_eq_left rfl, inv_inv]
  · intro P' hP'
    have hne : P'.1 ≠ P.1 := fun e => hP' (Subtype.ext e)
    refine ⟨one_mem _, ?_, ?_⟩
    · intro h x hx
      dsimp only
      rw [dite_eq_right hne, inv_one]
      simp
    · intro h
      dsimp only
      rw [dite_eq_right hne, inv_one]
      all_goals rfl


open Classical in
theorem midAt_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K),
    MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
      ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' →
        ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := mem_GLint_and_exists_liftsInv_of_congE

end GlobalTheory.Mem.Col2.AdT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAllTiedEqTiedOnOfRealised
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem exists_allTied_eqTied_on_of_realised {D : D7} (ht : TypAdd D)
    (hW : ∀ ψ, IsStdChar D ψ (-1) → ∃ Wf : WeilFun D ψ, Wf.EqRank) (hT : Nonempty (Tow D)) (hX : RealisedExE D)
    (hA : ∃ A : ProvA, ProvisionCompatibility D A) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E)
    (U : Set D.what₂.Tup) (hr : RealTied D) (hR : (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y))) :
    ∃ X : ThetaX D, X.TieIo ∧ (∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j,
      X.petY μ j ((X.rowAF μ j x : X.cusp _) : X.AF _) (X.rowAF μ j y) = inner ℂ x y) ∧
      ∃ (A : ProvA) (a : AllTied D X A), WeilThetaCompatibility a.W ∧
      ∀ (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Tp.xi = xi →
        ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, Formalism.IndefR.Links.ChrEq (a.T.eChr c) (H.eChr c) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.StdAdelicChar.existsUnique_isStdChar D (-1) (Or.inr rfl)
  obtain ⟨Wf, hE⟩ := hW ψ hψ
  obtain ⟨Tw⟩ := hT
  obtain ⟨Rc, hc, hio, hi⟩ := hR θ hθ ψ hψ Wf
  obtain ⟨X, T, W, B, rfl, h⟩ := hX θ hθ ψ hψ Wf hE Tw Rc
  obtain ⟨A, hA⟩ := hA
  obtain ⟨K, -⟩ := h.kfin
  refine ⟨X, h.tieIo hio, fun μ hμ j hj x y => ?_, A, ⟨T, h.afTiedSm, h.typTied ht, W, h.weilUnrTied, K, h.phiUp, B, hr, hA⟩,
    h.eqTied, fun nch Tp e => ?_⟩
  · obtain ⟨⟨m, hm⟩, h2⟩ := hi μ hμ j hj x y
    have e := T.pet _ (D.sp.Y_sig j) m.1 m.2 hm (X.rowAF μ j x) (X.rowAF μ j y)
    unfold ThetaX.petY
    rw [e, (h2 m hm).2, h.row, h.row, h.mY, ← h.petC_eq]
    simp only [ThetaTied.petC, Complex.ofReal_mul, mul_assoc]
  · exact GlobalTheory.TowerCharRead.exists_thetaChrTied D C nch Tp X T (e ▸ h.chrRead hc)

theorem exists_allTied_eqTied_on : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup), RealTied D → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) → ∃ X : ThetaX D, X.TieIo ∧ (∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, X.petY μ j ((X.rowAF μ j x : X.cusp _) : X.AF _) (X.rowAF μ j y) = inner ℂ x y) ∧ ∃ (A : ProvA) (a : AllTied D X A), WeilThetaCompatibility a.W ∧ ∀ (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Tp.xi = xi → ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, Formalism.IndefR.Links.ChrEq (a.T.eChr c) (H.eChr c) := by
  intro hW hC hex huniq hds D C xi U hr hR
  exact exists_allTied_eqTied_on_of_realised (GlobalTheory.TypeSum.typAdd_of_discreteSeries D hex huniq)
    (GlobalTheory.Mem.WeilEqRank.exists_weilFun_eqRank D (_root_.GlobalTheory.Mem.WeilExists.weilEx_of_weilRepresentation hW D) (GlobalTheory.Mem.WeilEqRank.weilOnEqEx_of_weilRepresentation hW D)
      (GlobalTheory.Mem.WeilTwist.weilTwEq D))
    ((GlobalTheory.TowerSpaces.exists_tow D).elim fun Tw _ => ⟨Tw⟩)
    (GlobalTheory.Mem.TrueRecordEq.exists_realisedE D (petInt_of_cuspRapidDecay hC D) (GlobalTheory.Mem.TopIntegrand.topInt hC D)
      (GlobalTheory.Mem.BesselIntegrable.besInt hC D) (GlobalTheory.Mem.Lift.liftAut hC D) (GlobalTheory.Mem.Lift.liftAutEq hC D))
    (GlobalTheory.exists_realPlace_record_tied hds D) C xi U hr hR

end GlobalTheory.Mem.Th
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalModuleLocalisingToLattices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.KerGlob

theorem weak_approx {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (w : ι → HeightOneSpectrum (𝓞 F)) (hw : Function.Injective w) (y : ∀ i, (w i).adicCompletion F) (c : F) (hc : c ≠ 0) :
    ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤
      Valued.v (algebraMap F ((w i).adicCompletion F) c) :=
  _root_.GlobalTheory.exists_approx_finite_places w hw y c hc

theorem matrix_approx {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)]
    [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)]
    {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q) (hπ : ∀ q, Irreducible (π q)) (t : F)
    (ht : ∀ q, f q t = algebraMap (W q) (Q q) (π q))
    (hd : ∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z))
    {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)) (hg : ∀ q, IsUnit (g q).det) (q0 : ι) :
    ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧
      B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧
      ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) :=
  _root_.GlobalTheory.GlobApx.exists_glob_approx W Q f π hπ t ht hd g hg q0

theorem colSpan_mul_le {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (g : Matrix (Fin k) (Fin k) K)
    (u : Matrix (Fin k) (Fin k) R) :
    Formalism.MainNotions.G.colSpan R (g * u.map (algebraMap R K)) ≤ Formalism.MainNotions.G.colSpan R g := by
  rw [Formalism.MainNotions.G.colSpan, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : (fun i => (g * u.map (algebraMap R K)) i c) = ∑ j, u j c • fun i => g i j := by
    funext i
    simp [Matrix.mul_apply, Algebra.smul_def, mul_comm]
  change (fun i => (g * u.map (algebraMap R K)) i c) ∈ Formalism.MainNotions.G.colSpan R g
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem colSpan_mul_eq {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (g : Matrix (Fin k) (Fin k) K)
    (u : Matrix (Fin k) (Fin k) R) (hu : IsUnit u.det) :
    Formalism.MainNotions.G.colSpan R (g * u.map (algebraMap R K)) = Formalism.MainNotions.G.colSpan R g := by
  refine le_antisymm (colSpan_mul_le g u) ?_
  have := colSpan_mul_le (g * u.map (algebraMap R K)) u⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

theorem map_int {F E : Type} [Field F] [NumberField F] [Field E] (w : HeightOneSpectrum (𝓞 F))
    (φ : E →+* w.adicCompletion F) (x : 𝓞 E) : φ x ∈ w.adicCompletionIntegers F := by
  have h2 : IsIntegral (w.adicCompletionIntegers F) (φ x) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) φ (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.adicCompletionIntegers F)
    (K := w.adicCompletion F)).1 h2
  rw [← hy]
  exact y.2

theorem step {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {W Q : Type} [CommRing W] [Field Q]
    [Algebra W Q] (e : Q ≃+* w.adicCompletion F)
    (heW : ∀ x, x ∈ Set.range (algebraMap W Q) ↔ e x ∈ w.adicCompletionIntegers F) (p N : ℕ) (hp : (p : F) ≠ 0)
    (a : F) (y : W)
    (hv : Valued.v (algebraMap F (w.adicCompletion F) a - e (algebraMap W Q y)) ≤
      Valued.v (algebraMap F (w.adicCompletion F) ((p : F) ^ N))) :
    ∃ z : W, e.symm (algebraMap F (w.adicCompletion F) a) = algebraMap W Q (y + (p : W) ^ N * z) := by
  have hcc0 : algebraMap F (w.adicCompletion F) ((p : F) ^ N) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hp)
  have hz' : (algebraMap F (w.adicCompletion F) a - e (algebraMap W Q y)) / algebraMap F (w.adicCompletion F) ((p : F) ^ N) ∈
      w.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact div_le_one_of_le₀ hv zero_le
  obtain ⟨z, hz⟩ := (heW (e.symm _)).2 (by rw [e.apply_symm_apply]; exact hz')
  refine ⟨z, ?_⟩
  apply e.injective
  rw [e.apply_symm_apply, map_add (f := _), map_add (f := _), map_mul, hz, map_mul, e.apply_symm_apply, map_pow, map_pow, map_natCast,
    map_natCast]
  have hcc' : algebraMap F (w.adicCompletion F) ((p : F) ^ N) = (p : w.adicCompletion F) ^ N := by
    rw [map_pow, map_natCast]
  rw [← hcc', mul_div_cancel₀ _ hcc0]
  ring

variable {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (Gs : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v))

theorem splitPlaceEmbedding_integers_mem_localIntegers (q : Fin (D.gat u v hg).P.nV) (r : 𝓞 D.host.E) :
    KerOne.iw0 Gs u v hg q (algebraMap (𝓞 D.host.E) D.host.E r) ∈
      Set.range (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q)) := by
  refine ((Gs u v hg).completion_integers_iff q _ rfl _).2 ?_
  rw [KerOne.splitPlaceIdempotent_cmEmbedding_compat]
  exact map_int _ (((RingHom.fst _ _).comp ((Gs u v hg).spl _ ((Gs u v hg).pl q).2).toRingHom).comp
      (Formalism.UG.inclE (F := D.host.F) ((((Gs u v hg).pl q).1).adicCompletion D.host.F))) r

theorem splitPlaceEmbedding_baseField_eq_completion (q : Fin (D.gat u v hg).P.nV) (a : D.host.F) :
    KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E a) =
      ((Gs u v hg).eQ q _ rfl).symm (algebraMap D.host.F ((((Gs u v hg).pl q).1).adicCompletion D.host.F) a) := by
  apply ((Gs u v hg).eQ q _ rfl).injective
  rw [KerOne.splitPlaceIdempotent_cmEmbedding_compat]
  refine ((Gs u v hg).spl_F _ _ a).trans ?_
  exact (RingEquiv.apply_symm_apply _ _).symm

theorem pl_inj : Function.Injective (fun q : Fin (D.gat u v hg).P.nV => ((Gs u v hg).pl q).1) :=
  fun _ _ h => (Gs u v hg).pl.injective (Subtype.ext h)

theorem dense (y : ∀ q, (D.gat u v hg).P.W q) (N : ℕ) : ∃ x : D.host.F, ∀ q, ∃ z : (D.gat u v hg).P.W q,
    KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E x) =
      algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q)
        (y q + ((D.what₂.places.resChar v : ℕ) : (D.gat u v hg).P.W q) ^ N * z) := by
  rcases isEmpty_or_nonempty (Fin (D.gat u v hg).P.nV) with h | ⟨⟨q1⟩⟩
  · exact ⟨0, fun q => (IsEmpty.false q).elim⟩
  have hp0 : ((D.what₂.places.resChar v : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (((D.gat u v hg).P.setting q1).prime.ne_zero)
  obtain ⟨a, ha⟩ := weak_approx (fun q => ((Gs u v hg).pl q).1) (pl_inj Gs u v hg)
    (fun q => (Gs u v hg).eQ q _ rfl (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q) (y q)))
    (((D.what₂.places.resChar v : ℕ) : D.host.F) ^ N) (pow_ne_zero _ hp0)
  refine ⟨a, fun q => ?_⟩
  obtain ⟨z, hz⟩ := step _ ((Gs u v hg).eQ q _ rfl) ((Gs u v hg).completion_integers_iff q _ rfl) _ N hp0 a (y q) (ha q)
  exact ⟨z, (splitPlaceEmbedding_baseField_eq_completion Gs u v hg q a).trans hz⟩

theorem exists_global_lattice (n : ℕ)
    (L : ∀ q : Fin (D.gat u v hg).P.nV, Submodule ((D.gat u v hg).P.W q) (Fin n → (D.gat u v hg).P.Qq q)) :
    (∀ q, G.IsLattice ((D.gat u v hg).P.W q) (L q)) →
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∀ q,
      L q = Submodule.span ((D.gat u v hg).P.W q) {y | ∃ x ∈ Λ, y = fun i => KerOne.iw0 Gs u v hg q (x i)} := by
  intro hL
  choose g hgu hgL using hL
  have hfr : ∀ q, IsFractionRing ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q) :=
    fun q => ((D.gat u v hg).P.setting q).frac_alt
  let Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
    { carrier := {x | ∀ q, (fun i => KerOne.iw0 Gs u v hg q (x i)) ∈ L q}
      add_mem' := fun {x y} hx hy q => by
        have : (fun i => KerOne.iw0 Gs u v hg q ((x + y) i)) =
            (fun i => KerOne.iw0 Gs u v hg q (x i)) + fun i => KerOne.iw0 Gs u v hg q (y i) := by
          funext i; simp
        rw [this]; exact (L q).add_mem (hx q) (hy q)
      zero_mem' := fun q => by
        have : (fun i => KerOne.iw0 Gs u v hg q ((0 : Fin n → D.host.E) i)) = 0 := by funext i; simp
        rw [this]; exact (L q).zero_mem
      smul_mem' := fun r x hx q => by
        obtain ⟨c, hc⟩ := splitPlaceEmbedding_integers_mem_localIntegers Gs u v hg q r
        have : (fun i => KerOne.iw0 Gs u v hg q ((r • x) i)) = c • fun i => KerOne.iw0 Gs u v hg q (x i) := by
          funext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, ← hc, Algebra.smul_def]
        rw [this]; exact (L q).smul_mem c (hx q) }
  refine ⟨Λ, fun q0 => ?_⟩
  obtain ⟨B, w, hw, hB, hoff⟩ := matrix_approx (fun q => (D.gat u v hg).P.W q) (fun q => (D.gat u v hg).P.Qq q)
    (fun q => (KerOne.iw0 Gs u v hg q).comp (algebraMap D.host.F D.host.E))
    (fun q => ((D.what₂.places.resChar v : ℕ) : (D.gat u v hg).P.W q)) (fun q => ((D.gat u v hg).P.setting q).p_unif)
    ((D.what₂.places.resChar v : ℕ) : D.host.F) (fun q => by rw [map_natCast, map_natCast])
    (fun y N => dense Gs u v hg y N) g hgu q0
  have hcol : ∀ c, (fun i => algebraMap D.host.F D.host.E (B i c)) ∈ Λ := by
    intro c q
    by_cases hq : q = q0
    · subst hq
      have : (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) =
          fun i => (g q * w.map (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q))) i c := by
        funext i; exact congrFun (congrFun hB i) c
      show (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) ∈ L q
      rw [this, hgL q, ← colSpan_mul_eq (g q) w hw]
      exact Submodule.subset_span ⟨c, rfl⟩
    · show (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) ∈ L q
      rw [hgL q]; exact hoff q hq c
  apply le_antisymm
  · rw [hgL q0, ← colSpan_mul_eq (g q0) w hw, Formalism.MainNotions.G.colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    refine Submodule.subset_span ⟨_, hcol c, ?_⟩
    funext i; exact (congrFun (congrFun hB i) c).symm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx q0

end GlobalTheory.Mem.Top.KerGlob
end
end

