module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0402
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0005
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridFromLevelChoiceGrid
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

section Cast

variable {D : D7}

def hermitianOrthogonalExtensionDataCast {A A' B B' : GlobalTheory.Grid.Node D} {c : ℕ} (hA : A = A') (hB : B = B') (d : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c) :
    GlobalTheory.Grid.HermitianOrthogonalExtensionData A' B' c := hA ▸ hB ▸ d

theorem gridDecompositionCast_is_iff {A A' B B' : GlobalTheory.Grid.Node D} {c : ℕ} (hA : A = A') (hB : B = B') (d : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c)
    (g : Fin c → Fin c → D.host.E) (𝔟 : Fin c → GlobalTheory.Grid.FrId D) : (hermitianOrthogonalExtensionDataCast hA hB d).Is g 𝔟 ↔ d.Is g 𝔟 := by
  subst hA hB; rfl

def hermitianOrthogonalExtensionDataZero (A B : GlobalTheory.Grid.Node D) (c : ℕ) : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c := ⟨0, 0⟩

theorem joinStair {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (c : ℕ) :
    GlobalTheory.ChiGrid.stairId (P.stA sc) (P.stAbar sc) c = GlobalTheory.Grid.staircaseExtensionIdeal (P.modul sc) c := by
  funext p
  simp only [GlobalTheory.ChiGrid.stairId, GlobalTheory.ChiGrid.Places.stA, GlobalTheory.ChiGrid.Places.stAbar, GlobalTheory.ChiGrid.Places.modulBar,
    GlobalTheory.Grid.staircaseExtensionIdeal, mul_pow, inv_pow, mul_inv, inv_inv]

theorem joinStair_top (c : ℕ) :
    GlobalTheory.ChiGrid.stairId D.host.AA D.host.AAbar c = GlobalTheory.Grid.staircaseExtensionIdeal (D := D) ⊤ c := by
  funext p
  simp [GlobalTheory.ChiGrid.stairId, GlobalTheory.Grid.staircaseExtensionIdeal, Ideal.pointwise_smul_def, Ideal.map_top, mul_pow, inv_pow]

theorem joinGram_one : (fun p q : Fin 1 => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix 1 (1 : D.host.E) p q) = fun _ _ => 1 := by
  funext p q
  fin_cases p; fin_cases q; simp [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix]

theorem joinGram_neg (c : ℕ) : (fun p q : Fin c => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c (-1 : D.host.E) p q) = GlobalTheory.Grid.antiDiagonalSignGramMatrix D.host.E c := by
  funext p q
  rfl

end Cast

theorem exists_gridPre_spaces : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesUpqExists → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → (∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → (G'.Λ X : Set _) = L0c D (G'.V X)) → (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → (∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.grid i j)).rank → ℝ) (ε : Fin (G'.V (.grid i j)).rank → Bool), IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε ∧ (W.onb (.grid i j) τ)ᴴ * gramAt D (G'.V (.grid i j)) τ * W.onb (.grid i j) τ = Formalism.REAL.Jm ε) → (∀ i, i ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.core i)).rank → ℝ) (ε : Fin (G'.V (.core i)).rank → Bool), IsEnum (GlobalTheory.Grid.parP D i τ) lam ε ∧ (W.onb (.core i) τ)ᴴ * gramAt D (G'.V (.core i)) τ * W.onb (.core i) τ = Formalism.REAL.Jm ε) → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.top j)).rank → ℝ) (ε : Fin (G'.V (.top j)).rank → Bool), IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε ∧ (W.onb (.top j) τ)ᴴ * gramAt D (G'.V (.top j)) τ * W.onb (.top j) τ = Formalism.REAL.Jm ε) → W.cart (.top 0) = W.cart (.core D.R.m) → W.onb (.top 0) = W.onb (.core D.R.m) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ G : GlobalTheory.Grid.GridPre R, G.idem = e ∧ G.IsSpaces ∧ G.IsChars ∧ SpAgree G W := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDS hH F hR hsc G' W hW hL hPg hsplit hg hT hOV hOP hOX hcT hoT e he
  classical
  obtain ⟨Z, hZ, hq0, hw0, he0, hWZ, hlvl, hS0, hS1⟩ := _root_.GlobalTheory.GridJoin.placeDat_of_grid hR hPg hsplit hg hT e he
  let Sx : GlobalTheory.ChiGrid.Node → D.what₂.Tau → SPar := fun X => match X with
    | .grid i j => GlobalTheory.Grid.parV D i j
    | .core i => GlobalTheory.Grid.parP D i
    | .top j => GlobalTheory.Grid.parXp D j
  let good : GlobalTheory.ChiGrid.Node → Prop := fun X => match X with
    | .grid i j => 1 ≤ i ∧ i ≤ D.R.m ∧ j ≤ D.R.m
    | .core i => i ≤ D.R.m
    | .top j => 1 ≤ j ∧ j ≤ D.R.m
  have hgood : ∀ X, good X → X.InRange D.R.m ∧ ∀ j, X ≠ .grid 0 j := by
    intro X hX
    rcases X with ⟨i, j⟩ | i | j
    · exact ⟨⟨hX.2.1, hX.2.2⟩, fun j' h => by cases h; exact absurd hX.1 (by omega)⟩
    · exact ⟨hX, fun j' h => GlobalTheory.ChiGrid.Node.noConfusion h⟩
    · exact ⟨hX.2, fun j' h => GlobalTheory.ChiGrid.Node.noConfusion h⟩
  have hMod : ∀ X, good X → ∃ M : DSModel (G'.V X) (Sx X), cart M = W.cart X ∧ onb M = W.onb X := by
    intro X hX
    have hv := G'.isV (hgood X hX).1 (hgood X hX).2
    refine _root_.GlobalTheory.dsModel_of_onb_cart D hDS (G'.V X) (Sx X) (W.onb X) (W.cart X) ?_ (W.onb_is X (hgood X hX).1)
    intro τ
    rcases X with ⟨i, j⟩ | i | j
    · obtain ⟨lam, ε, h1, h2⟩ := hOV i j hX.1 hX.2.1 hX.2.2 τ
      exact ⟨lam, ε, h1, _root_.GlobalTheory.Grid.isHCParam_parV D hH i j hX.1 hX.2.1 hX.2.2 τ _ lam ε hv.rank h1, h2⟩
    · obtain ⟨lam, ε, h1, h2⟩ := hOP i hX τ
      exact ⟨lam, ε, h1, _root_.GlobalTheory.Grid.isHCParam_parP D hH i hX τ _ lam ε hv.rank h1, h2⟩
    · obtain ⟨lam, ε, h1, h2⟩ := hOX j hX.1 hX.2 τ
      exact ⟨lam, ε, h1, _root_.GlobalTheory.GridHC.isHCParam_parXp D hH j hX.1 hX.2 τ _ lam ε hv.rank h1, h2⟩
  have hFr : ∀ X, good X → ∃ β, IsSDFrame (G'.V X) β (G'.Λ X) 1 := fun X hX =>
    _root_.GlobalTheory.SDFrameCompletion.exists_isSDFrame_of_isSelfDualC D _ _ (hL X (hgood X hX).1 (hgood X hX).2) (G'.isV (hgood X hX).1 (hgood X hX).2).sd
  choose M hM using hMod
  choose β hβ using hFr
  let mk : ∀ X, good X → GlobalTheory.Grid.Node D := fun X h => ⟨G'.V X, Sx X, M X h, G'.Λ X, β X h⟩
  let node : GlobalTheory.ChiGrid.Node → GlobalTheory.Grid.Node D := fun X => if h : good X then mk X h else GlobalTheory.Grid.row0 R 0
  have node_pos : ∀ X (h : good X), node X = mk X h := fun X h => dif_pos h
  have mk_is : ∀ X (h : good X), (mk X h).Is (X.rank D) (X.neg D.R.m) (Sx X) := fun X h => by
    have hv := G'.isV (hgood X h).1 (hgood X h).2
    exact ⟨hv.rank, hv.sigOK, hv.sig, rfl, hβ X h⟩
  have mk_agree : ∀ X (h : good X), NodeAgree (mk X h) W X := fun X h =>
    ⟨rfl, HEq.rfl, heq_of_eq (hM X h).1, heq_of_eq (hM X h).2⟩
  let GS : GlobalTheory.Grid.GridSp D :=
    { toPlaceDat := Z, nV := fun i j => node (.grid (i + 1) j), P := fun i => node (.core i), nX := fun j => node (.top (j + 1)) }
  have vert_eq : ∀ n x, 1 ≤ n → GS.vert R n x = node (.grid n x) := by
    intro n x hn
    cases n with
    | zero => omega
    | succ n => rfl
  have Xp_eq : ∀ n, 1 ≤ n → GS.Xp n = node (.top n) := by
    intro n hn
    cases n with
    | zero => omega
    | succ n => rfl
  have gP : ∀ i, i ≤ D.R.m → good (.core i) := fun i h => h
  have gV : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → good (.grid i j) := fun i j h1 h2 h3 => ⟨h1, h2, h3⟩
  have gX : ∀ j, 1 ≤ j → j ≤ D.R.m → good (.top j) := fun j h1 h2 => ⟨h1, h2⟩
  have hm2 := D.R.two_le_m

  obtain ⟨dP, -, hdP⟩ := GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq (GlobalTheory.Grid.row0 R 0) (mk (.core 0) (gP 0 (by omega))) G'.sp.dec0 (fun _ => 1) (Or.inl rfl)
    G'.sp.lat0

  have exV : ∀ i (h : 1 ≤ i ∧ i ≤ D.R.m), ∃ d : GlobalTheory.Grid.HermitianOrthogonalExtensionData (mk (.core i) (gP i h.2)) (mk (.grid i 0) (gV i 0 h.1 h.2 (by omega))) (i - 1),
      d.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix (i - 1) (-1 : D.host.E) p q) (GlobalTheory.ChiGrid.stairId (G'.pl.stA sc) (G'.pl.stAbar sc) (i - 1)) :=
    fun i h => (GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq _ _ (G'.sp.colDec i h.1 h.2) _ (Or.inr rfl) (G'.sp.colLat i h.1 h.2)).imp fun _ h => h.2
  choose dV hdV using exV

  have exX : ∀ j (h : j + 1 < D.R.m), ∃ d : GlobalTheory.Grid.HermitianOrthogonalExtensionData (mk (.top (j + 1)) (gX (j + 1) (by omega) h.le))
      (mk (.grid D.R.m (j + 1)) (gV D.R.m (j + 1) (by omega) le_rfl h.le)) (D.R.m - 1 - (j + 1)),
      d.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix (D.R.m - 1 - (j + 1)) (-1 : D.host.E) p q)
        (GlobalTheory.ChiGrid.stairId D.host.AA D.host.AAbar (D.R.m - 1 - (j + 1))) :=
    fun j h => (GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq _ _ (G'.sp.rowDecS j h) _ (Or.inr rfl) (G'.sp.rowLat j h)).imp fun _ h => h.2
  choose dX hdX using exX

  obtain ⟨dZ, -, hdZ⟩ := GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq (mk (.grid D.R.m D.R.m) (gV D.R.m D.R.m (by omega) le_rfl le_rfl))
    (mk (.top D.R.m) (gX D.R.m (by omega) le_rfl)) G'.sp.topDec (fun _ => 1) (Or.inl rfl) G'.sp.topLat
  let G : GlobalTheory.Grid.GridPre R :=
    { toGridSp := GS
      idem := e
      chiH := G'.ch.chiH
      chi := G'.ch.chi
      decP := hermitianOrthogonalExtensionDataCast rfl (node_pos (.core 0) (gP 0 (by omega))).symm dP
      decV := fun i => if h : 1 ≤ i ∧ i ≤ D.R.m then
        hermitianOrthogonalExtensionDataCast (node_pos (.core i) (gP i h.2)).symm ((vert_eq i 0 h.1).trans (node_pos (.grid i 0) (gV i 0 h.1 h.2 (by omega)))).symm (dV i h) else hermitianOrthogonalExtensionDataZero _ _ _
      decX := fun j => if h : j + 1 < D.R.m then
        hermitianOrthogonalExtensionDataCast (node_pos (.top (j + 1)) (gX (j + 1) (by omega) h.le)).symm ((vert_eq D.R.m (j + 1) (by omega)).trans (node_pos (.grid D.R.m (j + 1)) (gV D.R.m (j + 1) (by omega) le_rfl h.le))).symm (dX j h) else hermitianOrthogonalExtensionDataZero _ _ _
      decZ := hermitianOrthogonalExtensionDataCast ((vert_eq D.R.m D.R.m (by omega)).trans (node_pos (.grid D.R.m D.R.m) (gV D.R.m D.R.m (by omega) le_rfl le_rfl))).symm
        ((Xp_eq D.R.m (by omega)).trans (node_pos (.top D.R.m) (gX D.R.m (by omega) le_rfl))).symm dZ
      X := fun _ _ => ⟨1, 0, 0⟩
      ωT := fun _ _ _ => 1
      vacT := fun _ _ => 0
      ItT := fun _ _ => 0
      ωC := fun _ _ => 1
      vacC := fun _ => 0
      ItC := fun _ => 0
      dn := fun _ => ⟨1, 0, 0⟩
      ItU := fun _ => 0
      m00 := ⟨0, ∅⟩
      mV := fun _ _ => ⟨0, ∅⟩
      mP := fun _ => ⟨0, ∅⟩
      mX := fun _ => ⟨0, ∅⟩
      vC := fun _ _ => 0 }
  refine ⟨G, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hi hj
      show (node (.grid (i + 1) j)).Is _ _ _
      rw [node_pos (.grid (i + 1) j) (gV (i + 1) j (by omega) hi hj)]
      exact mk_is _ _
    · intro i hi
      show (node (.core i)).Is _ _ _
      rw [node_pos (.core i) (gP i hi)]
      exact mk_is _ _
    · intro j hj
      show (node (.top (j + 1))).Is _ _ _
      rw [node_pos (.top (j + 1)) (gX (j + 1) (by omega) hj)]
      exact mk_is _ _
    · dsimp only [G]
      rw [gridDecompositionCast_is_iff, ← joinGram_one]
      exact hdP
    · intro i hi1 hi2
      dsimp only [G]
      rw [dif_pos ⟨hi1, hi2⟩, gridDecompositionCast_is_iff]
      have hl' : Z.ideal R.Pg = G'.pl.modul sc := hlvl
      have := hdV i ⟨hi1, hi2⟩
      rw [joinGram_neg, joinStair, ← hl'] at this
      exact this
    · intro j hj
      dsimp only [G]
      rw [dif_pos hj, gridDecompositionCast_is_iff]
      have := hdX j hj
      rw [joinGram_neg, joinStair_top] at this
      exact this
    · dsimp only [G]
      rw [gridDecompositionCast_is_iff, ← joinGram_one]
      exact hdZ
  · exact ⟨hZ, fun i h1 h2 => _root_.GlobalTheory.Grid.heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt (_root_.GlobalTheory.GridJoin.gap_eq_chiGap D) hsc Z hS0 hS1 hZ.Wd_over hw0 i h1 h2, fun i h1 h2 => G'.ch.chi_eq i h1 h2⟩
  · refine ⟨?_, ?_, ?_, hq0, hw0, he0, hWZ, hlvl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    · intro i j hi hj
      cases i with
      | zero => exact _root_.GlobalTheory.GridJoin.nodeAgree_grid0_of_weil_over W hW j hj
      | succ i =>
        show NodeAgree (node (.grid (i + 1) j)) W (.grid (i + 1) j)
        rw [node_pos (.grid (i + 1) j) (gV (i + 1) j (by omega) hi hj)]
        exact mk_agree _ _
    · intro i hi
      show NodeAgree (node (.core i)) W (.core i)
      rw [node_pos (.core i) (gP i hi)]
      exact mk_agree _ _
    · intro j hj
      cases j with
      | zero =>
        show NodeAgree (node (.core D.R.m)) W (.top 0)
        rw [node_pos (.core D.R.m) (gP D.R.m le_rfl)]
        exact ⟨rfl, HEq.rfl, heq_of_eq ((hM _ _).1.trans hcT.symm), heq_of_eq ((hM _ _).2.trans hoT.symm)⟩
      | succ j =>
        show NodeAgree (node (.top (j + 1))) W (.top (j + 1))
        rw [node_pos (.top (j + 1)) (gX (j + 1) (by omega) hj)]
        exact mk_agree _ _

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteTypeCarriesOnePart
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.CarriesOne

open GlobalTheory.Hk3

theorem heckePolyOf_coeff_inj : ∀ (n q : ℕ), q ≠ 0 → ∀ a b : ℕ → ℂ, Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b → ∀ k ≤ n, a k = b k := by
  intro n q hq a b h k hk
  have hc := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f k) h
  simp only [Formalism.L2.Col.heckePolyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk)),
    if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk))] at hc
  have h0 : ((-1 : ℂ) ^ k * (q : ℂ) ^ (k * (k - 1) / 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))
  exact mul_left_cancel₀ h0 hc

theorem parts_eq_of_rowLabels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (c c' : Pl D.host.E → List ℤ → ℂ), (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d)) → GlobalTheory.Hk3.EEc R SF c = GlobalTheory.Hk3.EEc R SF c' ∧ ∀ i, GlobalTheory.Hk3.Wcc R SF i c = GlobalTheory.Hk3.Wcc R SF i c' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF c c' key
  obtain ⟨hQ, hgood, hoff, -⟩ := _root_.GlobalTheory.GoodPrimes.good_primes R F hC.lev
  refine ⟨?_, fun i => ?_⟩
  · obtain ⟨n, hβ⟩ := hC.lev.βY 0 (by have := D.R.two_le_m; omega)
    have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
      _root_.GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) ((D.host.g 0 * D.host.g 1) ^ n) (R.dat0 R.triv) hβ P
        (by
          intro h
          push_cast at h
          exact (hgood A.μ0 P hP).1 (P.isPrime.mem_of_pow_mem _ (by exact_mod_cast h)))
        (by
          intro PP hPP
          refine hP PP (hPP.imp id ?_)
          intro h
          exact absurd h (Finset.notMem_empty _))
    unfold GlobalTheory.Hk3.EEc partDual
    congr 1
    ext U
    rw [LabDet.mem_partFull, LabDet.mem_partFull]
    refine and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_
    have hP : Good R A.μ0 P := by
      obtain ⟨_, _, _, _, ho, _⟩ := hB
      exact (hoff SF hSF P).1 ho
    rw [key P d hP ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩]
  · obtain ⟨n, hβ⟩ := hC.lev.βW i
    have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
      _root_.GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
        (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
        (by
          intro PP hPP
          refine hP PP (hPP.imp id ?_)
          intro h
          exact absurd h (Finset.notMem_empty _))
    have keyW : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Wc D i) P d → c P d = c' P d := by
      intro P hP d hd
      have h := key P (dualLab d) hP ((GlobalTheory.LabEq.isLab_W_iff R F (s := 0) hC i P d hP).1.1 hd)
      rwa [GlobalTheory.CarriedHecke.dualLab_dualLab] at h
    have hpf : partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c =
        partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c' := by
      ext U
      rw [LabDet.mem_partFull, LabDet.mem_partFull]
      refine and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_
      have hP : Good R A.μ0 P := by
        obtain ⟨_, _, _, _, ho, _⟩ := hB
        exact (hoff SF hSF P).1 ho
      rw [keyW P hP d ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩]
    unfold Wcc
    rw [hpf]

theorem parts_eq_of_carries : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → UpInj R.toRealDat → (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') := by

  intro hHowe hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hW e hInert hUp p c c' hc hc'
  obtain ⟨hC, hSF, hE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW e
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat
  have hL := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCusp D
  have hTwo := GlobalTheory.VmTwo.twoSided_goodInert hHowe R F hL hW e hS
  have hinj : ∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0 :=
    fun _ w _ h => hUp A3.A.μ0 (h.trans (map_zero _).symm)
  have hpol := GlobalTheory.CarriedHecke.hecke_polys_of_carries R F hL hok hW e hS hinj
  have hr : (Yc D 0).rank = D.R.r := by
    show (D.sp.Y (min 0 D.R.m)).rank = D.R.r
    rw [Nat.zero_min, D.sp.Y_rank 0 (Nat.zero_le _)]
    simp [Ranks.rankY, Ranks.r]
  have hs : ∀ P, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank,
      c P (dualLab (splitLab (Yc D 0).rank k)) = c' P (dualLab (splitLab (Yc D 0).rank k)) := by
    intro P hP hcP k hk
    obtain ⟨P0, h0, rfl, hq⟩ := _root_.GlobalTheory.GoodSplitFam.good_split_pl R F hW e P hP hcP
    have h1 := (hpol p c hc P0 h0).1
    have h2 := (hpol p c' hc' P0 h0).1
    rw [hr] at hk ⊢
    exact heckePolyOf_coeff_inj D.R.r _ hq _ _ (h1.symm.trans h2) k hk
  have hE0 : GlobalTheory.Hk3.EEc R.toRealDat R.SF c ≠ ⊥ := hE c ▸ hc.1
  have hE0' : GlobalTheory.Hk3.EEc R.toRealDat R.SF c' ≠ ⊥ := hE c' ▸ hc'.1
  have ksplit := _root_.GlobalTheory.Hk3.LabDetRows.dual_eq_of_split R.toRealDat F.lv2 hC R.SF hSF c c' hE0 hE0' hs
  let i0 : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩
  have kin := (GlobalTheory.InertValLab.inert_vals_iff_labels R F hL hok hW e hS hTwo hInert hinj i0 p p c c' hc hc').1 (fun _ => rfl)
  have key : ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d) := by
    intro P d hP hd
    by_cases hcP : Formalism.DivisionValues.conjPl P = P
    · apply kin P _ hP hcP
      rw [(GlobalTheory.LabEq.isLab_W_iff R.toRealDat F.lv2 (s := 0) hC i0 P _ hP).1, GlobalTheory.CarriedHecke.dualLab_dualLab]
      exact hd
    · exact ksplit P hP hcP d hd
  obtain ⟨h1, h2⟩ := parts_eq_of_rowLabels R.toRealDat F.lv2 hC R.SF hSF c c' key
  exact ⟨by rw [hE, hE, h1], fun i => by rw [hWc, hWc, h2 i]⟩

end GlobalTheory.CarriesOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableDiagonalModSmall
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

theorem flagV_pair_table : ∀ {M A : Type} [Zero M] [Ring A] (p : M → M → A) (sm : A → Prop) (ρ k n : ℕ), n = 2 * ρ + k + 1 → ∀ (e f : Fin ρ → M) (b b' : Fin k → M) (z : M), PairTable p sm e f b b' z → ∀ a c : Fin n, sm (p (flagV ρ k n f e b' z a) (flagV ρ k n e f b z c) - if a = c then sgnD ρ k a else 0) := by
  intro M A _ _ p sm ρ k n hn e f b b' z hT a c
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16⟩ := hT
  subst hn
  have ha := a.isLt
  have hc := c.isLt
  have d1 : ∀ (x y : Fin ρ), x.1 = y.1 → sm (p (f x) (e y) - 1) := by
    intro x y h; have := t1 x y; rwa [if_pos (Fin.ext h)] at this
  have o1 : ∀ (x y : Fin ρ), x.1 ≠ y.1 → sm (p (f x) (e y) - 0) := by
    intro x y h; have := t1 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d6 : ∀ (x y : Fin k), x.1 = y.1 → sm (p (b' x) (b y) - 1) := by
    intro x y h; have := t6 x y; rwa [if_pos (Fin.ext h)] at this
  have o6 : ∀ (x y : Fin k), x.1 ≠ y.1 → sm (p (b' x) (b y) - 0) := by
    intro x y h; have := t6 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d16 : ∀ (x y : Fin ρ), x.1 = y.1 → sm (p (e x) (f y) - 1) := by
    intro x y h; have := t16 x y; rwa [if_pos (Fin.ext h)] at this
  have o16 : ∀ (x y : Fin ρ), x.1 ≠ y.1 → sm (p (e x) (f y) - 0) := by
    intro x y h; have := t16 x y; rwa [if_neg (fun hh => h (congrArg Fin.val hh))] at this
  have d11 : sm (p z z - -1) := by rw [sub_neg_eq_add]; exact t11
  by_cases hac : a.1 = c.1
  · rw [if_pos (Fin.ext hac)]
    unfold flagV sgnD
    split_ifs <;> first
      | omega
      | exact d11
      | exact d1 _ _ (by dsimp only; omega)
      | exact d6 _ _ (by dsimp only; omega)
      | exact d16 _ _ (by dsimp only; omega)
  · rw [if_neg (fun hh => hac (congrArg Fin.val hh))]
    unfold flagV
    split_ifs <;> first
      | omega
      | exact o1 _ _ (by dsimp only; omega)
      | exact o6 _ _ (by dsimp only; omega)
      | exact o16 _ _ (by dsimp only; omega)
      | (rw [sub_zero]; first
          | exact t2 _ _ | exact t3 _ | exact t4 _ _ | exact t5 _ _ | exact t7 _ | exact t8 _ _
          | exact t9 _ | exact t10 _ | exact t12 _ | exact t13 _ _ | exact t14 _ _ | exact t15 _)

end GlobalTheory.SeeConjRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelEqOfUnipotentFrameChangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeKernel_eq_of_unipotent_frameChange : ∀ {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p → ∀ (k : U.Comp) (x : (U.X k).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ (C C' : hkKer (Xo := Xo) P p i (CAt σ) (U.un k x)) (z z' w : FrPt Xo c (CAt σ)) (t t' : Ix Dw → (CAt σ)ˣ),
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C z →
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C' z' →
        (∀ j, j ≠ none → t j = 1) → (∀ j, j ≠ none → t' j = 1) → FrBor t w z → FrBor t' w z' → C = C' := by
  first | exact @GlobalTheory.HeckeInj.eq_of_hkRelFr_frBor | exact GlobalTheory.HeckeInj.eq_of_hkRelFr_frBor | (intros; apply GlobalTheory.HeckeInj.eq_of_hkRelFr_frBor <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGlueBaseDataOfIsAdelicGlueVectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGlueBaseData_of_isAdelicGlueVector : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (X : HSp D) (L₀ : Lat X) (f : Fin X.rank → EAf D), Submodule.IsFullLattice D.host.E L₀ → IsGlueVec X u L₀ f → IsBasePair X u π L₀ fun w => idem w • f := by
  first | exact @GlobalTheory.AdIsom.GlueBase.isBasePair_of_isGlueVec | exact GlobalTheory.AdIsom.GlueBase.isBasePair_of_isGlueVec | (intros; apply GlobalTheory.AdIsom.GlueBase.isBasePair_of_isGlueVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymmetricPositionLevelFirstSpaceIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_symmetricPositionLevel_firstSpace_iff : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (κ : GA D (Yc D 0)), (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) ↔ κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β ∧ ∀ PP ∈ Lc.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧ (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) → levChi (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) κ = ∏ PP ∈ Lc.Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ))))) := by
  first | exact @GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff | exact GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff | (intros; apply GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff <;> assumption)
end

