module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}

def CrdOver {L L' : Type} [Field L] [Field L'] (ι : L →+* L') {n n' : ℕ} (x : Fin n → L) (x' : Fin n' → L') : Prop :=
  n = n' ∧ ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = ι (x k)


set_option maxHeartbeats 4000000 in
def RSideW (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  HEq R'.ψ z.R.ψ ∧ HEq R'.θ z.R.θ ∧ HEq R'.βW z.R.βW ∧ HEq R'.βY z.R.βY ∧ HEq R'.ΛY z.R.ΛY ∧ HEq R'.nW z.R.nW ∧ HEq R'.βV z.R.βV ∧
  HEq R'.ΛV z.R.ΛV ∧ HEq R'.ΛW z.R.ΛW ∧ HEq R'.Pg z.R.Pg ∧ HEq R'.eG z.R.eG ∧ HEq R'.Sb z.R.Sb ∧
  (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.cV i').W (z.R.cV i).W ∧ HEq (R'.cV i').ρ (z.R.cV i).ρ ∧ HEq (R'.cV i').nW (z.R.cV i).nW ∧
    HEq (R'.cV i').iW (z.R.cV i).iW ∧ HEq (R'.vacP i') (z.R.vacP i) ∧ HEq (R'.ioP i') (z.R.ioP i) ∧
    HEq (R'.BV i') (z.R.BV i) ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).H (z.R.MW i (w.st Z).toD7.what₂.embLL).H ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).nacg (z.R.MW i (w.st Z).toD7.what₂.embLL).nacg ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).ips (z.R.MW i (w.st Z).toD7.what₂.embLL).ips ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).σ (z.R.MW i (w.st Z).toD7.what₂.embLL).σ ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).lam (z.R.MW i (w.st Z).toD7.what₂.embLL).lam ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).ε (z.R.MW i (w.st Z).toD7.what₂.embLL).ε ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).fr (z.R.MW i (w.st Z).toD7.what₂.embLL).fr ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).enum (z.R.MW i (w.st Z).toD7.what₂.embLL).enum ∧
    HEq (R'.HW i' (w'.st Z').toD7.what₂.embLL) (z.R.HW i (w.st Z).toD7.what₂.embLL) ∧
    HEq (R'.νW i') (z.R.νW i) ∧ HEq (R'.fdW i') (z.R.fdW i) ∧
    ∀ (ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL),
      (∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x) →
      (∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
        (HEq (R'.MW i' σ').H (z.R.MW i (σ'.comp ι)).H ∧
          HEq (R'.MW i' σ').nacg (z.R.MW i (σ'.comp ι)).nacg ∧
          HEq (R'.MW i' σ').ips (z.R.MW i (σ'.comp ι)).ips ∧
          HEq (R'.MW i' σ').σ (z.R.MW i (σ'.comp ι)).σ ∧
          HEq (R'.MW i' σ').lam (z.R.MW i (σ'.comp ι)).lam ∧
          HEq (R'.MW i' σ').ε (z.R.MW i (σ'.comp ι)).ε ∧
          HEq (R'.MW i' σ').fr (z.R.MW i (σ'.comp ι)).fr ∧
          HEq (R'.MW i' σ').enum (z.R.MW i (σ'.comp ι)).enum) ∧
        HEq (R'.HW i' σ') (z.R.HW i (σ'.comp ι)) ∧
        HEq (R'.gW i' σ') (z.R.gW i (σ'.comp ι)) ∧
        ∀ x x', CrdOver ι x x' → HEq ((R'.FW i').j σ' x') ((z.R.FW i).j (σ'.comp ι) x)) ∧
      ((∀ x x', CrdOver ι x x' → (x' ∈ (R'.FW i').WK ↔ x ∈ (z.R.FW i).WK)) ∧
        ∀ x' ∈ (R'.FW i').WK, ∃ x : Fin (z.R.nW i) → (w.st Z).toD7.what₂.LL, CrdOver ι x x') ∧
      (∀ g' g, HEq g' g → (((R'.FW i').chi g' : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) =
        ι (((z.R.FW i).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) ∧
      (∀ g' g, HEq g' g → ∀ x x', CrdOver ι x x' → CrdOver ι ((z.R.FW i).ρ g x) ((R'.FW i').ρ g' x')) ∧
      HEq (R'.FW i').Pt (z.R.FW i).Pt ∧
      (∀ lp' lp, HEq lp' lp → ∀ y' y, HEq y' y → ∀ (φ' : (R'.FW i').WK) (φ : (z.R.FW i).WK), CrdOver ι φ.1 φ'.1 →
        (R'.FW i').nrm lp' y' φ' = (z.R.FW i).nrm lp y φ)) ∧
  ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok)
      (ok' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).Ok)
      (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (φ' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).EqFun),
      (∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ'.1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 d).1)) →
      HEq (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok' φ' :))))
        (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))))


set_option maxHeartbeats 4000000 in
def RSide (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  RSideW z Wt' R' ∧ ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.ωP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (R'.vP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (R'.HV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (R'.thF i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (R'.thG i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (R'.νV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (R'.fdV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))))

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormsLiftRulesCorrespondExtendedData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.CuspExt


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem cusp_heq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {H H' : Host E} (hH : H' = H) {l : Level H} {l' : Level H'} (hl : HEq l' l)
    {c : Coeff l} {c' : Coeff l'} (hc : HEq c' c) {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} (hDw : HEq Dw' Dw)
    {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'} (hXo : HEq Xo' Xo)
    {U : ∀ j (σ : c.F →+* ℂ), Formalism.L2.Pj.Unf (Xo j) c σ r} {U' : ∀ j (σ : c'.F →+* ℂ), Formalism.L2.Pj.Unf (Xo' j) c' σ r}
    (hU : HEq U' U) {a a' : (E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) (j : ℕ) :
    Formalism.L2.Pj.Rul (Xo' j) c' = Formalism.L2.Pj.Rul (Xo j) c ∧
    (∀ (x : Formalism.L2.Pj.Rul (Xo j) c) (x' : Formalism.L2.Pj.Rul (Xo' j) c'), HEq x' x →
      (x' ∈ Formalism.L2.Pj.cusp (Xo' j) c' (U' j) a' n' ↔ x ∈ Formalism.L2.Pj.cusp (Xo j) c (U j) a n)) ∧
    (∀ (x : Formalism.L2.Pj.Rul (Xo j) c) (x' : Formalism.L2.Pj.Rul (Xo' j) c') (h : x ∈ Formalism.L2.Pj.cusp (Xo j) c (U j) a n)
      (h' : x' ∈ Formalism.L2.Pj.cusp (Xo' j) c' (U' j) a' n'), HEq x' x →
      HEq (⟨x', h'⟩ : Formalism.L2.Pj.cusp (Xo' j) c' (U' j) a' n') (⟨x, h⟩ : Formalism.L2.Pj.cusp (Xo j) c (U j) a n)) := by
  subst hH ha hn
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hDw
  obtain rfl := eq_of_heq hXo
  obtain rfl := eq_of_heq hU
  refine ⟨rfl, fun x x' hx => ?_, fun x x' h h' hx => ?_⟩
  · obtain rfl := eq_of_heq hx; exact Iff.rfl
  · obtain rfl := eq_of_heq hx; exact HEq.rfl


set_option maxHeartbeats 2000000 in
theorem cusp_ext : StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        z'.core.R ((j' : ℕ) + 1) = z.core.R ((j : ℕ) + 1) ∧
        (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r → (r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n ↔ r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) ∧
        (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)) (h : r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) (h' : r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n), HEq r' r →
          HEq (⟨r', h'⟩ : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) (⟨r, h⟩ : z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) := by
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj => ?_
  have hB := hE.1
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have e : j' = j := Fin.ext hj.symm
  subst e

  obtain ⟨h1, h2, h3⟩ := hx.κ j' j' rfl
  have e1 : (z'.geo.κ j').aP = (z.geo.κ j').aP := eq_of_heq h1
  have e2 : (z'.geo.κ j').aM = (z.geo.κ j').aM := eq_of_heq h2
  have hw : Formalism.L2.Pj.wtA (z'.geo.κ j') = Formalism.L2.Pj.wtA (z.geo.κ j') := by
    funext x
    unfold Formalism.L2.Pj.wtA
    rw [e1, e2]
    rfl
  obtain ⟨hR, hm, hs⟩ := cusp_heq (r := (w.st Z).toD7.R.r) (eq_of_heq hx.H) hx.l hx.c hx.Dw hx.Xo hx.U hw h3 ((j' : ℕ) + 1)
  exact ⟨hR, hm, hs⟩

end GlobalTheory.Mem.R3.CuspExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

section EnlAux

variable {B B' : Base}

def enlEmb (hR : Set.range B.embLL ⊆ Set.range B'.embLL) : B.LL →+* B'.LL :=
  (RingEquiv.ofBijective B'.embLL.rangeRestrict
      ⟨fun x y h => B'.embLL.injective (congrArg Subtype.val h), B'.embLL.rangeRestrict_surjective⟩).symm.toRingHom.comp
    ((Subring.inclusion fun x hx => RingHom.mem_range.2 (hR (RingHom.mem_range.1 hx))).comp B.embLL.rangeRestrict)

theorem enlEmb_spec (hR : Set.range B.embLL ⊆ Set.range B'.embLL) (x : B.LL) :
    B'.embLL (enlEmb hR x) = B.embLL x := by
  have h := congrArg Subtype.val ((RingEquiv.ofBijective B'.embLL.rangeRestrict
      ⟨fun x y h => B'.embLL.injective (congrArg Subtype.val h), B'.embLL.rangeRestrict_surjective⟩).apply_symm_apply
    ((Subring.inclusion fun x hx => RingHom.mem_range.2 (hR (RingHom.mem_range.1 hx))) (B.embLL.rangeRestrict x)))
  exact h

def ksEquiv (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) : B.Ks ≃ₐ[ℚ] B'.Ks :=
  (B.Ks.equivMap B.embLL.toRatAlgHom).trans ((IntermediateField.equivOfEq (F := ℚ) (E := ℂ) (S := B.Ks.map B.embLL.toRatAlgHom) (T := B'.Ks.map B'.embLL.toRatAlgHom) hK.symm).trans (B'.Ks.equivMap B'.embLL.toRatAlgHom).symm)

theorem ksEquiv_spec (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) (x : B.Ks) : B'.embLL ((ksEquiv hK x : B'.Ks) : B'.LL) = B.embLL (x : B.LL) := by
  have h3 : (B'.Ks.equivMap B'.embLL.toRatAlgHom) (ksEquiv hK x) =
      IntermediateField.equivOfEq (F := ℚ) (E := ℂ) (S := B.Ks.map B.embLL.toRatAlgHom) (T := B'.Ks.map B'.embLL.toRatAlgHom) hK.symm (B.Ks.equivMap B.embLL.toRatAlgHom x) := by
    exact (B'.Ks.equivMap B'.embLL.toRatAlgHom).apply_symm_apply _
  have h4 := congrArg Subtype.val h3
  rw [IntermediateField.coe_equivMap_apply] at h4
  rw [RingHom.toRatAlgHom_apply] at h4
  rw [h4]
  change ((B.Ks.equivMap B.embLL.toRatAlgHom x : B.Ks.map B.embLL.toRatAlgHom) : ℂ) = _
  rw [IntermediateField.coe_equivMap_apply]
  rfl

def oEquiv (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) : B.O ≃+* B'.O := RingOfIntegers.mapRingEquiv (ksEquiv hK).toRingEquiv

theorem oEquiv_spec (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) (x : B.O) : B'.embLL (B'.OtoLL (oEquiv hK x)) = B.embLL (B.OtoLL x) := by
  have h := RingOfIntegers.mapRingEquiv_apply (ksEquiv hK).toRingEquiv x
  change B'.embLL (((oEquiv hK x : B'.Ks)) : B'.LL) = B.embLL ((x : B.Ks) : B.LL)
  rw [show (oEquiv hK x : B'.Ks) = ksEquiv hK (x : B.Ks) from h]
  exact ksEquiv_spec hK x

end EnlAux

section EnlAux2

variable {B B' : Base}

theorem enlEmb_Ks (hR : Set.range B.embLL ⊆ Set.range B'.embLL)
    (hK : B'.embLL '' (B'.Ks : Set B'.LL) = B.embLL '' (B.Ks : Set B.LL)) {x : B'.LL} (hx : x ∈ B'.Ks) :
    ∃ x₀ ∈ B.Ks, enlEmb hR x₀ = x := by
  obtain ⟨x₀, hx₀, he⟩ : B'.embLL x ∈ B.embLL '' (B.Ks : Set B.LL) := hK ▸ ⟨x, hx, rfl⟩
  exact ⟨x₀, hx₀, B'.embLL.injective (by rw [enlEmb_spec, he])⟩

theorem coefficientFieldEnlarge_mem_larger_fixedField (hR : Set.range B.embLL ⊆ Set.range B'.embLL)
    (hL : B.embLL '' (B.LL0 : Set B.LL) ⊆ B'.embLL '' (B'.LL0 : Set B'.LL)) {x : B.LL} (hx : x ∈ B.LL0) :
    enlEmb hR x ∈ B'.LL0 := by
  obtain ⟨x', hx', he⟩ : B.embLL x ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := hL ⟨x, hx, rfl⟩
  have : enlEmb hR x = x' := B'.embLL.injective (by rw [enlEmb_spec, he])
  rw [this]
  exact hx'

end EnlAux2

section CdAux

abbrev withCd (D : D7) (c₀ : CDHaar) : D7 := { D with cd := c₀ }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {r : ℕ}

theorem finVol_withCd (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (V : HSp D) :
    Formalism.L2.Pj.FinVol (D := withCd D c₀) V ↔ Formalism.L2.Pj.FinVol (D := D) V := by
  subst h
  rfl

theorem cuspL2_withCd (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)
    (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ) :
    Formalism.L2.Pj.CuspL2 (D := withCd D c₀) U σ V dict mu ↔ Formalism.L2.Pj.CuspL2 (D := D) U σ V dict mu := by
  subst h
  rfl

theorem peterssonDefinite_iff_of_eq_compactDualHaar (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)
    (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)
    (h₁ : Formalism.L2.Pj.CuspL2 (D := withCd D c₀) U σ V dict mu) (h₂ : Formalism.L2.Pj.CuspL2 (D := D) U σ V dict mu) :
    Formalism.L2.Pj.L2DefiniteCuspForms (D := withCd D c₀) U σ V dict mu h₁ ↔ Formalism.L2.Pj.L2DefiniteCuspForms (D := D) U σ V dict mu h₂ := by
  subst h
  rfl

end CdAux

theorem exists_adelicCore_transport_enlargedCoefficientBase : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt),
    Enl0 B B' → HEq f' f → CoreP z →
    ∃ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) ∧
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) ∧
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) ∧
      HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota ∧
      Formalism.L2.Pj.LawsCore core'.toCore ∧ core'.Q.Canon ∧ (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) ∧ core'.pb = f'.P.pb := by
  intro B B' f f' T T' w w' Z Z' hX Wt z hE hf hC
  have hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom := SetLike.coe_injective hE.2.1
  obtain ⟨h1, hKs, hLL0, hR⟩ := hE
  have hι := enlEmb_spec hR
  have hι0 := fun x (hx : x ∈ B.LL0) => coefficientFieldEnlarge_mem_larger_fixedField hR hLL0 hx
  have hιK := fun x (hx : x ∈ B'.Ks) => enlEmb_Ks hR hKs hx
  have hO := oEquiv_spec hK
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hff := eq_of_heq hf
  subst hff
  obtain ⟨hL, hCa, hDim, hpb⟩ := hC
  have hcd : (w'.st Z').toD7.cd = (w.st Z).toD7.cd := Tr.cd_eq _ _
  let g : z.core.Q.c.F →+* _ := (enlEmb hR).comp ((algebraMap (↥z.core.Q.c.F) (w.st Z).toD7.what₂.LL) : z.core.Q.c.F →+* B.LL)
  let Q' : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := (z.core.Q.H), l := (z.core.Q.l), c := (z.core.Q.c), Dw := (z.core.Q.Dw), Xo := (z.core.Q.Xo),
      eO := (by with_unfolding_all exact ((z.core.Q.eO.trans (oEquiv hK)) :)) }
  let core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q', U := (z.core.U), V := (z.core.V), dict := (z.core.dict), mu := (z.core.mu),
          Kf := (z.core.Kf), pb := (z.core.pb) }
      cE := (z.core.cE), chiW := (z.core.chiW), x₀ := (z.core.x₀), iota := (z.core.iota) }
  refine ⟨core', (g.toAlgebra), ?_⟩

  refine ⟨fun y => (hι _).trans (z.alg_eq y), fun y => hι0 _ (z.fieldValues_mem_fixedField y), fun x hx => ?_,
    (HEq.refl z.core.Q.H), (HEq.refl z.core.Q.l), (HEq.refl z.core.Q.c), (HEq.refl z.core.Q.Dw),
    (HEq.refl z.core.Q.Xo), (HEq.refl z.core.U), (HEq.refl z.core.V), (HEq.refl z.core.dict),
    (HEq.refl z.core.mu), (HEq.refl z.core.Kf), (HEq.refl z.core.cE), (HEq.refl z.core.chiW),
    (HEq.refl z.core.x₀), (HEq.refl z.core.iota), ?_, (hCa), (hDim), (hpb)⟩
  · obtain ⟨x₀, hx₀, he⟩ := hιK x hx
    obtain ⟨y, hy⟩ := z.Ks_le x₀ hx₀
    exact ⟨y, (congrArg (enlEmb hR) hy).trans he⟩
  · have hPF : Q'.PinField := fun x => (hO (z.core.Q.eO x)).trans (hL.pins.2.2.1 x)
    exact
      { pins := ⟨(hL.pins.left), (hL.pins.right.left), hPF, (hL.pins.right.right.right)⟩
        half := (hL.half)
        evalWD := (hL.evalWD)
        unf := (hL.unf)
        unTest := (hL.unTest)
        chiTriv := (hL.chiTriv)
        dictU := (hL.dictU)
        spaceW := (hL.spaceW)
        levelK := (hL.levelK)
        xiAbs := (hL.xiAbs)
        muUnit := (hL.muUnit)
        muCont := (hL.muCont)
        finVol := fun j hj σ hσ => (finVol_withCd (w'.st Z').toD7 (w.st Z).toD7.cd hcd _).1 ((hL.finVol j hj σ hσ))
        cuspFD := (hL.cuspFD)
        supDef := (hL.supDef)
        cuspidalL2Subspace := fun j hj σ hσ => (cuspL2_withCd (w'.st Z').toD7 (w.st Z).toD7.cd hcd _ _ _ _ _).1 ((hL.cuspidalL2Subspace j hj σ hσ))
        l2Def := fun j hj σ hσ =>
          (peterssonDefinite_iff_of_eq_compactDualHaar (w'.st Z').toD7 (w.st Z).toD7.cd hcd _ _ _ _ _ ((hL.cuspidalL2Subspace j hj σ hσ)) _).1 ((hL.l2Def j hj σ hσ))
        unitIndep := (hL.unitIndep)
        ptNe := (hL.ptNe)
        cuspMul := (hL.cuspMul)
        latZ := (hL.latZ)
        cuNe := (hL.cuNe)
        expo := (hL.expo) }

end GlobalTheory.Mem.R3.Rw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenTors

theorem exists_torsMap_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∃ f : QkPt P.D.toPre F k → (TF (R := R) F ⟶ t.G),
      (∀ q v, GlobalTheory.FlatTors.IsImage P F k q v ↔ v = (f q).left) ∧ (∀ q, f q ^ k = 1) ∧ (∀ x, x ^ k = 1 → ∃ q, f q = x) ∧
      (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧
      (∀ p p' τ, p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        GlobalTheory.UU.CubWeil t.cub k (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y)))) ∧
      ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
  intro E _ _ _ H R _ _ _ t P _ hR F _ _ _ k hk
  letI := H.starRing
  obtain ⟨f₀, h1, h2, -, h4, -, h6⟩ := GlobalTheory.FlatTors.torsionIso_holds E H R (maximalIdeal R) hR t P F k hk
  obtain ⟨g₁, g₂, -⟩ := GlobalTheory.Ex.GenericFibre.unif_generic P
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv g₁ (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl
  have hpow : ∀ q, f₀ q ^ k = 1 := fun q => by
    obtain ⟨w, hw⟩ := P.U.toUnifPre.ext
    exact ((h1 q (f₀ q)).2 rfl w hw).1
  have hpow' : ∀ q, e (f₀ q) ^ k = 1 := fun q => by rw [← map_pow, hpow, map_one]
  refine ⟨fun q => e (f₀ q), ?_, hpow', ?_, ?_, ?_, ?_⟩
  · intro q v
    constructor
    · rintro ⟨a, ha, hq⟩
      rw [(h1 q a).1 hq] at ha
      rw [← ha, he]
    · intro hv
      exact ⟨f₀ q, by rw [hv, he], (h1 q (f₀ q)).2 rfl⟩
  · intro x hx
    obtain ⟨q, hq⟩ := h2 (e.symm x) (by rw [← map_pow, hx, map_one])
    exact ⟨q, by simp only [hq, MulEquiv.apply_symm_apply]⟩
  · intro p p' p'' h
    simp only [h4 p p' p'' h, map_mul]
  · intro p p' τ hy hτ
    have hw : WeilIs P.A.A P.A.L k (f₀ p) (f₀ p') (unitOn (τ (Multiplicative.ofAdd p'.y))) :=
      (h6 p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
    have hpr : IsProper (pullback.snd t.G.hom (jK R)) := by
      have := P.A.isAb.proper
      have := isIso_inv_left P.U.gen.symm
      have h : IsProper ((Over.pullback (jK R)).obj t.G).hom := by
        rw [← Over.w P.U.gen.symm.inv]; infer_instance
      exact h
    have one : ∀ c : Fˣ, GlobalTheory.UU.CubWeil t.cub k (e (f₀ p)) (e (f₀ p')) (unitOn c) →
        WeilIs P.A.A P.A.L (k : ℤ) (f₀ p) (f₀ p') (unitOn c) := fun c h =>
      (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ t.G P.A.A (jK R) _ t.PP.L P.A.L t.PP.isLB P.A.isLB g₁ g₂
        (TFK (R := R) F) k (f₀ p) (f₀ p') (e (f₀ p)) (e (f₀ p')) (unitOn c) (he _) (he _)).2
        (GlobalTheory.FlatTors.weilIs_of_cubWeil_of_proper (jK R) t.G t.semi hpr t.cub k (TFK (R := R) F) _ _ _ h)
    obtain ⟨ζ, hζ, -⟩ := (GlobalTheory.UU.cubWeil_basic _ t.G t.PP t.cub k _).1 (e (f₀ p)) (e (f₀ p')) (hpow' p) (hpow' p')
    obtain ⟨c, rfl⟩ : ∃ c : Fˣ, unitOn c = ζ :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom ζ,
        Units.ext ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _)⟩
    have ec : c = τ (Multiplicative.ofAdd p'.y) :=
      GlobalTheory.weilIs_unique_fieldPoint _ P.A.A P.A.L P.A.isLB F _ k (f₀ p) (f₀ p') c _ (one c hζ) hw
    exact ec ▸ hζ
  · intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR P.D P.A t.G t.semi P.U F F σ k hk p
    obtain ⟨x', hx'⟩ := hx (f₀ p)
    have e' : x' = f₀ p' := (h1 p' x').1 ((hiff p' (f₀ p) x' hpp' hx').1 ((h1 p (f₀ p)).2 rfl))
    subst e'
    rw [he, he, hx', Category.assoc]

end GlobalTheory.GenTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargementStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTupleLiftForms_pass_to_coeffEnlargement : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl), Enl B₁ B₂ → HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs → (∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K)) → ∀ j₁ j₂ : ℕ, j₁ = j₂ → (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).D = (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).D ∧ ∀ φ₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).EqFun, ∃ φ₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).EqFun, ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (φ₂.1 d₂).1) (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (φ₁.1 d₁).1) := by
  first | exact @GlobalTheory.Mem.R3.Tr.lift_refTuple_enl | exact GlobalTheory.Mem.R3.Tr.lift_refTuple_enl | (intros; apply GlobalTheory.Mem.R3.Tr.lift_refTuple_enl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapHilbertModelEqConcreteThetaMapFamilyThreStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) := by
  first | exact @GlobalTheory.Mem.ThetaRead3.thetaP_read | exact GlobalTheory.Mem.ThetaRead3.thetaP_read | (intros; apply GlobalTheory.Mem.ThetaRead3.thetaP_read <;> assumption)
end

