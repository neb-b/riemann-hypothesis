module

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
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePath
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SrcLat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable section
namespace GlobalTheory.MovedDict
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}

def srcLat (S : GridChoice W Set.univ) : ∀ p : GlobalTheory.ChiGrid.Pair T, FinPt G p.small → FinPt G p.big →
    Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E)
  | .chi i j, _, y => GlobalTheory.SumSize.latAt S (.grid (i + 1) j) y
  | .mu _ i j, x, _ => GlobalTheory.SumSize.latAt S (.grid i j) x
  | .core i, _, y => GlobalTheory.SumSize.latAt S (.core (i + 1)) y
  | .top _ j, x, _ => GlobalTheory.SumSize.latAt S (.top j) x

def tgtLat (S : GridChoice W Set.univ) : ∀ p : GlobalTheory.ChiGrid.Pair T, FinPt G p.small → FinPt G p.big →
    Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E)
  | .chi i j, x, _ => GlobalTheory.SumSize.latAt S (.grid i j) x
  | .mu _ i j, _, y => GlobalTheory.SumSize.latAt S (.grid i (j + 1)) y
  | .core i, x, _ => GlobalTheory.SumSize.latAt S (.core i) x
  | .top _ j, _, y => GlobalTheory.SumSize.latAt S (.top (j + 1)) y

end GlobalTheory.MovedDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppAtUnitaryGroupLocalToAdelicEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section

namespace GlobalTheory.SuppAtPlace

theorem suppAt_embV : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∀ g : Gv V v, SuppAt ε V (embV V v g) := by
  intro D V v w h ε he g
  have hP : IsPrimeIdem w ε (ε + cA D ε) := Or.inl ⟨he, rfl⟩
  exact (Supp.suppF_iff_of_isPrimeIdem V hP h _).2 ⟨g, rfl⟩

end GlobalTheory.SuppAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameAtOfUnrAt
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

variable {D : D7}

theorem isRes_one {χ : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} (h : χ.UnrAt PP) : IsRes χ PP 1 := by
  intro a k u hk hu
  have ha : a ∉ PP.asIdeal := by
    intro hmem
    have h0 : (u : kP PP) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact u.ne_zero h0
  have hv : Formalism.L2.Host.IsUnitAt PP (Formalism.L2.Host.atFin PP k) := by
    show Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (k : D.host.E)) = 1
    first
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
      | erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rw [hk, Algebra.algebraMap_self, RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).mpr ha
  have := h _ hv
  rw [MonoidHom.one_apply]
  exact this.symm

theorem tameAt_of_unrAt {χ : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} (h : χ.UnrAt PP) : χ.TameAt PP := by
  intro x hx _
  exact h x hx

theorem UnrOff.mul {b : AE D} {χ χ' : (AE D)ˣ →* Circle} (h : UnrOff b χ) (h' : UnrOff b χ') : UnrOff b (χ * χ') := by
  intro x h1 h2 h3 h4
  rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, one_mul]

theorem UnrOff.inv {b : AE D} {χ : (AE D)ˣ →* Circle} (h : UnrOff b χ) : UnrOff b χ⁻¹ := by
  intro x h1 h2 h3 h4
  rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

variable {T0 : Type} {L : LevCh D T0} {μ0 : T0}

theorem unrOff_mu (hL : L.Is μ0) (t : T0) (j : Fin D.R.m) {P : Finset (Pl D.host.E)} {e : AE D}
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) :
    UnrOff (e + cA D e) (L.mu t ((j : ℕ) + 1)) ∧ UnrOff (e + cA D e) L.eta := by
  obtain ⟨-, hQ, -, hoff⟩ := _root_.GlobalTheory.LevelRamif.ramif_at_levels D T0 L μ0 hL t j
  have hsub : ∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') →
      PP' ∉ L.Pg ∧ PP' ∉ L.Q t ∧ (∀ PP ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') ∧
        ∀ PP ∈ L.Q t, ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
    intro PP' hn hc
    exact ⟨fun hm => hn ((hP PP').mpr (Or.inl hm)), fun hm => hn ((hP PP').mpr (Or.inr hm)),
      fun PP hm => hc PP ((hP PP).mpr (Or.inl hm)), fun PP hm => hc PP ((hP PP).mpr (Or.inr hm))⟩
  have h0 : UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1)) :=
    _root_.GlobalTheory.ChrOff.unrOff_of_unrAt D _ (L.C.mu0 j) P e (hL.mu0 j) he
      (fun PP' hn hc => hoff PP' (hsub PP' hn hc).1 (hsub PP' hn hc).2.2.1)
  have h1 : UnrOff (e + cA D e) (L.xi t) := by
    refine _root_.GlobalTheory.ChrOff.unrOff_of_unrAt D _ (L.xiH t) P e (hL.xi t) he (fun PP' hn hc => ?_)
    by_contra hr
    rcases (hL.Q_ram t PP').mp hr with hm | ⟨PP, hm, hcj⟩
    · exact (hsub PP' hn hc).2.1 hm
    · exact (hsub PP' hn hc).2.2.2 PP hm hcj
  refine ⟨?_, _root_.GlobalTheory.ChrOff.unrOff_of_unrAt D _ L.C.eta P e hL.eta he
    (fun PP' _ _ => L.C.isEta.unr PP')⟩
  show UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1) * L.xi t)
  exact h0.mul h1

theorem mu_val (hL : L.Is μ0) (t : T0) (j : Fin D.R.m) {P : Finset (Pl D.host.E)} {e : AE D}
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) (x : (AE D)ˣ) (a : AE D)
    (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ) (hx : (x : AE D) = e * a + (1 - e))
    (ha : (a' : Lev.EAf D) = toEAf D a) (hu : ∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') :
    ((L.mu t ((j : ℕ) + 1) x : Circle) : ℂ) =
        (((∏ PP ∈ L.Pg, (L.chi ((j : ℕ) + 1) PP (u PP))⁻¹) * ∏ PP ∈ L.Q t, L.xiR t PP (u PP) : ℂˣ) : ℂ) ∧
      L.eta x = 1 := by
  classical
  obtain ⟨hdisj, hQ, hPg, -⟩ := _root_.GlobalTheory.LevelRamif.ramif_at_levels D T0 L μ0 hL t j
  have hPu : P = L.Pg ∪ L.Q t := by
    ext PP
    rw [hP PP, Finset.mem_union]
  have hA := _root_.GlobalTheory.TameSplitChar.char_eq_prod_res D (L.mu0 ((j : ℕ) + 1)) (L.C.mu0 j) P e
    (fun PP => if PP ∈ L.Pg then (L.chi ((j : ℕ) + 1) PP)⁻¹ else 1) (hL.mu0 j) he
    (fun PP hm => by
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg]
        exact ⟨(L.C.isMu0 j).tame PP, hL.chi j PP hg⟩
      · simp only [if_neg hg]
        have hq : PP ∈ L.Q t := ((hP PP).mp hm).resolve_left hg
        exact ⟨tameAt_of_unrAt (hQ PP hq), isRes_one (hQ PP hq)⟩) x a a' u hx ha hu
  have hB := _root_.GlobalTheory.TameSplitChar.char_eq_prod_res D (L.xi t) (L.xiH t) P e
    (fun PP => if PP ∈ L.Q t then L.xiR t PP else 1) (hL.xi t) he
    (fun PP hm => by
      by_cases hq : PP ∈ L.Q t
      · simp only [if_pos hq]
        exact ⟨hL.xi_tame t PP, hL.xiR t PP hq⟩
      · simp only [if_neg hq]
        have hg : PP ∈ L.Pg := ((hP PP).mp hm).resolve_right hq
        exact ⟨tameAt_of_unrAt (hPg PP hg), isRes_one (hPg PP hg)⟩) x a a' u hx ha hu
  have hC := _root_.GlobalTheory.TameSplitChar.char_eq_prod_res D L.eta L.C.eta P e (fun _ => 1) hL.eta he
    (fun PP _ => ⟨tameAt_of_unrAt (L.C.isEta.unr PP),
      isRes_one (L.C.isEta.unr PP)⟩) x a a' u hx ha hu
  rw [hPu, Finset.prod_union hdisj] at hA hB
  have hA' : ((L.mu0 ((j : ℕ) + 1) x : Circle) : ℂ) =
      ∏ PP ∈ L.Pg, (((L.chi ((j : ℕ) + 1) PP (u PP))⁻¹ : ℂˣ) : ℂ) := by
    rw [hA, Finset.prod_eq_one (s := L.Q t) (fun PP hm => ?_), mul_one]
    · exact Finset.prod_congr rfl (fun PP hm => by simp only [if_pos hm, MonoidHom.inv_apply])
    · simp only [if_neg (Finset.disjoint_right.mp hdisj hm), MonoidHom.one_apply, Units.val_one]
  have hB' : ((L.xi t x : Circle) : ℂ) = ∏ PP ∈ L.Q t, ((L.xiR t PP (u PP) : ℂˣ) : ℂ) := by
    rw [hB, Finset.prod_eq_one (s := L.Pg) (fun PP hm => ?_), one_mul]
    · exact Finset.prod_congr rfl (fun PP hm => by simp only [if_pos hm])
    · simp only [if_neg (Finset.disjoint_left.mp hdisj hm), MonoidHom.one_apply, Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.coe_prod, Units.coe_prod]
    show ((L.mu0 ((j : ℕ) + 1) x * L.xi t x : Circle) : ℂ) = _
    rw [Circle.coe_mul, hA', hB']
  · have hC' : ((L.eta x : Circle) : ℂ) = 1 := by
      rw [hC]
      exact Finset.prod_eq_one (fun PP _ => by simp only [MonoidHom.one_apply, Units.val_one])
    exact Circle.ext (by rw [hC', Circle.coe_one])

end GlobalTheory.VecInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}


open Classical in
def givenFn (B : Frames G) (t : T) (Φ : G.Datum) (e : AE D) (a : Arrow T) (x : WO (G.pS a.pair) (G.pT a.pair)) : ℂ :=
  if IsHalf e x then ∏ w ∈ locPl G t, givenDatum t w B Φ (edgeOf a) (locArg B t w a x) else 0

end GlobalTheory.FlipStart

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem tensor_given (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E)
    (y : ∀ j : Fin D.R.m, WO (G.pS (Arrow.down t 0 j).pair) (G.pT (Arrow.down t 0 j).pair))
    (x : ∀ i : Fin D.R.m, WO (G.pS (Arrow.right (T := T) i 0).pair) (G.pT (Arrow.right (T := T) i 0).pair)) :
    (givenStage t w B Φ).tensor (pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x))) =
      (∏ j : Fin D.R.m, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) (y j))) *
        ∏ i : Fin D.R.m, givenDatum t w B Φ (edgeOf (.right i 0)) (locArg B t w (.right i 0) (x i)) := by
  have pathArgs_down (i : ℕ) : ∀ (n : ℕ) (y : ∀ j : Fin n, WO (G.pS (Arrow.down t i j).pair) (G.pT (Arrow.down t i j).pair))
      (j : ℕ) (h : j < n), pathArgs B t w (downPath t i n) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n y) (.theta i j) =
        locArg B t w (.down t i j) (y ⟨j, h⟩) := by
    intro n
    induction n with
    | zero => intro y j h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro y j h
      have hc := GlobalTheory.OppConv.pathArgs_comp B t w (Path.one (.down t i n)) ((), y (Fin.last n)) (.theta i j) (downPath t i n)
        (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n fun j => y j.castSucc)
      by_cases hj : j < n
      · exact (hc.1 ((GlobalTheory.OppConv.mem_edges_down t i n _).2 ⟨j, hj, rfl⟩)).trans (ih _ j hj)
      · have hj' : j = n := by omega
        subst hj'
        refine (hc.2 fun h' => ?_).trans ?_
        · obtain ⟨k, hk, hk'⟩ := (GlobalTheory.OppConv.mem_edges_down t i j _).1 h'
          simp only [GlobalTheory.SplitFlip.Edge.theta.injEq] at hk'
          omega
        · exact dif_pos rfl
  have hθ : ∀ j : Fin D.R.m, pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x)) (.theta 0 j) = locArg B t w (.down t 0 j) (y j) := by
    intro j
    refine ((GlobalTheory.OppConv.pathArgs_comp B t w (downPath t 0 D.R.m) _ (.theta 0 j) (rowPath T 0 D.R.m) _).2 ?_).trans
      (pathArgs_down 0 D.R.m y j j.2)
    rw [GlobalTheory.OppConv.mem_edges_row]
    rintro ⟨i, -, h⟩
    cases h
  have hex : ∀ i : Fin D.R.m, pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x)) (.ex i 0) = locArg B t w (.right i 0) (x i) :=
    fun i => ((GlobalTheory.OppConv.pathArgs_comp B t w (downPath t 0 D.R.m) _ (.ex i 0) (rowPath T 0 D.R.m) _).1
      ((GlobalTheory.OppConv.mem_edges_row 0 D.R.m _).2 ⟨i, i.2, rfl⟩)).trans (GlobalTheory.OppConv.pathArgs_row B t w 0 D.R.m x i i.2)
  show ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b _).prod = _
  simp only [GlobalTheory.SplitFlip.givenPath, List.map_append, List.prod_append, List.map_map, List.map_reverse, List.prod_reverse]
  have hl : ∀ f : ℕ → ℂ, ((List.range D.R.m).map f).prod = ∏ i : Fin D.R.m, f i := fun f => by
    rw [← Finset.prod_range, Finset.prod_eq_multiset_prod]; rfl
  rw [hl, hl]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    rw [hθ j]
    rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    rw [hex i]
    rfl

end GlobalTheory.FlipStart

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem repFin_of (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j))
    (Φ : G.Datum) (e : AE D) (he : IsIdemSum e (locPl G t)) (c : Fin D.R.m → ℂ) (z : ℂ) (hz : z * ∏ j, c j = 1)
    (hcol : ∀ j : Fin D.R.m, IsLocVec W (.mu t 0 j) e (ρ.vT 0 j) (c j • givenFn B t Φ e (.down t 0 j)) (f j))
    (hrow : ∀ i : Fin D.R.m, IsLocVec W (.chi i 0) e (ρ.vX i 0) (givenFn B t Φ e (.right i 0)) (W.cosVec i (Φ i))) :
    RepFin B ρ t (givenPath t D.R.m) (Finsupp.single (givenFin W t f Φ) z) (fun w => (givenStage t w B Φ).tensor) := by
  have append_surj {S : Arrow T → Type} {X Y : Node} (p : Path T X Y) :
      ∀ {Z : Node} (q : Path T Y Z) (f : (p.comp q).Fam S), ∃ d e, Path.Fam.append (q := q) d e = f := by
    intro Z q
    induction q with
    | nil => intro f; exact ⟨f, (), rfl⟩
    | snoc a q ih =>
      intro f
      obtain ⟨d, e, h⟩ := ih f.1
      refine ⟨d, (e, f.2), ?_⟩
      show (Path.Fam.append (q := q) d e, f.2) = f
      rw [h]
      rfl
  have rowFam_surj {S : Arrow T → Type} (j : ℕ) : ∀ n (d : (rowPath T j n).Fam S), ∃ f, rowFam j n f = d := by
    intro n
    induction n with
    | zero => intro d; exact ⟨fun i => i.elim0, rfl⟩
    | succ n ih =>
      intro d
      obtain ⟨f, hf⟩ := ih d.1
      refine ⟨Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f, ?_⟩
      show (rowFam j n (fun i => Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f i.castSucc),
        Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f (Fin.last n)) = d
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hf]
      rfl
  have downFam_surj {S : Arrow T → Type} (i : ℕ) : ∀ n (d : (downPath t i n).Fam S), ∃ f, downFam t i n f = d := by
    intro n
    induction n with
    | zero => intro d; exact ⟨fun j => j.elim0, rfl⟩
    | succ n ih =>
      intro d
      obtain ⟨d0, e, he⟩ := append_surj (Path.one (.down t i n)) (downPath t i n) d
      obtain ⟨f, hf⟩ := ih e
      refine ⟨Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f, ?_⟩
      rw [← he]
      show Path.Fam.append (p := Path.one (.down t i n)) ((), Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f (Fin.last n))
        (downFam t i n fun j => Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f j.castSucc) = _
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hf]
      rfl
  refine ⟨e, he, fun _ => Path.Fam.append (q := rowPath T 0 D.R.m)
    (downFam t 0 D.R.m fun j => c j • givenFn B t Φ e (.down t 0 j)) (rowFam 0 D.R.m fun i => givenFn B t Φ e (.right i 0)),
    fun d hd => ?_, fun x hx => ?_⟩
  · rw [Finsupp.support_single_ne_zero _ (by rintro rfl; simp at hz), Finset.mem_singleton] at hd
    subst hd
    exact (GlobalTheory.OppConv.vecAll_append ρ e _ _ _ _ _ _).2
      ⟨(GlobalTheory.OppConv.vecAll_down ρ e t 0 _ _ _).2 hcol, (GlobalTheory.OppConv.vecAll_row ρ e 0 _ _ _).2 hrow⟩
  · rw [Finsupp.sum_single_index (by rw [zero_mul])]
    obtain ⟨x₁, x₂, rfl⟩ := append_surj (downPath t 0 D.R.m) (rowPath T 0 D.R.m) x
    obtain ⟨y, rfl⟩ := downFam_surj 0 D.R.m x₁
    obtain ⟨y', rfl⟩ := rowFam_surj 0 D.R.m x₂
    obtain ⟨h1, h2⟩ := (GlobalTheory.OppConv.halfAll_append e _ _ _ _).1 hx
    have hy := (GlobalTheory.OppConv.halfAll_down e t 0 _ _).1 h1
    have hy' := (GlobalTheory.OppConv.halfAll_row e 0 _ _).1 h2
    dsimp only
    rw [Finset.prod_congr rfl fun w _ => tensor_given B t Φ w y y']
    erw [GlobalTheory.OppConv.famProd_append (downPath t 0 D.R.m), GlobalTheory.OppConv.famProd_down, GlobalTheory.OppConv.famProd_row]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, givenFn, if_pos (hy _), if_pos (hy' _)]
    rw [Finset.prod_comm (s := Finset.univ) (t := locPl G t), Finset.prod_comm (s := Finset.univ) (t := locPl G t),
      ← mul_assoc, ← mul_assoc, hz, one_mul]

end GlobalTheory.FlipStart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridCommonDataPropertiesHold
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto

theorem comOK : ComOK := by
  intro D _ _ T L μ0 _ sc _ G W M _
  have hchi : ∀ k, k < D.R.m → ChrEq (G.ch.chi (D.R.m - k)) (G.ch.chiH (D.R.m - k)) :=
    fun k hk => G.ch.chi_eq _ (by omega) (by omega)
  refine ⟨W.θ_is, W.ψ_std, fun k (hk : k < D.R.m) => ?_, fun k (hk : k < D.R.m) τ => ?_, fun k (hk : k < D.R.m) => ?_,
    fun i k hik (hk : k < D.R.m) τ => ?_, ?_, ?_⟩
  · show IsHeckeChar D (G.ch.chi (D.R.m - k))⁻¹ ∧ Formalism.L2.Theta.ResEta D (G.ch.chi (D.R.m - k))⁻¹ 0
    have hw := W.om_is (.core k) (show k + 1 ≤ D.R.m by omega)
    have e := (G.chr_core (i := k) (by omega)).1
    have hr : (G.pS (.core k)).rank = rankP D (k + 1) := (G.sp.P_is _ (by omega)).rank
    have h1 := hw.hecS
    have h2 := hw.resS
    rw [e] at h1 h2
    rw [hr] at h2
    obtain ⟨a, ha⟩ := even_rankP D (k + 1)
    exact GlobalTheory.StdUnn.isHeckeChar_resEta_inv D _ 0 h1 (Formalism.L2.Theta.resEta_parity h2 (by omega))
  · show HasInfExp D (G.ch.chi (D.R.m - k))⁻¹ τ (-(cen D sc.cGap τ (D.R.m - k) : ℚ))
    have h := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - k) : ℚ)) (hchi k hk)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - k), fun τ => by push_cast; ring, G.ch.inf _ (by omega) (by omega)⟩ τ
    exact GlobalTheory.Chain.StepVac.hasInfExp_inv h
  · show GlobalTheory.LFun.UnrOff (G.ch.chi (D.R.m - k))⁻¹ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F)))
    intro w hw
    have hu : GlobalTheory.LFun.UnrAt (G.ch.chi (D.R.m - k)) w :=
      (GlobalTheory.LFun.unrAt_iff_of_chrEq (hchi k hk) w).2 (G.ch.unr _ (by omega) (by omega) w hw)
    intro x hx
    have := hu x hx
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv] at this ⊢
    rw [this, inv_one]
  · show -(cen D sc.cGap τ (D.R.m - i) : ℚ) ≠ -(cen D sc.cGap τ (D.R.m - k) : ℚ)
    intro h
    have hg : 0 < gap D sc.cGap := lt_of_le_of_lt (Nat.zero_le _) (sLen_lt_gap D sc.cGap)
    set g := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D sc.cGap) 0 with hgdef
    have hc : ∀ j, cen D sc.cGap τ j = ⌊g.mid j⌋ := fun j => rfl
    have hga : (g.ga : ℚ) = (gap D sc.cGap : ℚ) := rfl
    have e1 : ((D.R.m - i : ℕ) : ℚ) = ((D.R.m - k : ℕ) : ℚ) + ((k - i : ℕ) : ℚ) := by
      rw [← Nat.cast_add]; congr 1; omega
    have hmid : g.mid (D.R.m - k) = g.mid (D.R.m - i) + (((k - i) * gap D sc.cGap : ℕ) : ℤ) := by
      rw [g.mid_eq (by omega), g.mid_eq (by omega)]
      have := g.a_sub_a (D.R.m - k) (D.R.m - i)
      rw [e1, hga] at this
      push_cast
      linarith
    have hf : cen D sc.cGap τ (D.R.m - k) = cen D sc.cGap τ (D.R.m - i) + (((k - i) * gap D sc.cGap : ℕ) : ℤ) := by
      rw [hc, hc, hmid, Int.floor_add_intCast]
    have h' : cen D sc.cGap τ (D.R.m - i) = cen D sc.cGap τ (D.R.m - k) := by exact_mod_cast neg_inj.1 h
    have hpos : 0 < (k - i) * gap D sc.cGap := Nat.mul_pos (by omega) hg
    omega
  · show 1 ≤ D.R.r + 1
    omega
  · show D.R.r + 1 + 2 ≤ D.R.r + 6 - 1
    omega

end GlobalTheory.CoreOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecIsThetaFunO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem vec_isThetaFunO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (S.Z.vec d) := by
  intro D T L sc G W U S t p hp d hd
  have hIn : p.InRange D.R.m := by
    have hn := hp.nodes
    cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega
  exact GlobalTheory.LastVertexInv.vec_theta S hp hIn d hd

end GlobalTheory.TopZeroInv
end
end

