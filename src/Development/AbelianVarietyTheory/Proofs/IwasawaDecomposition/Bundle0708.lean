module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDefiniteFormsGivenCoefficient
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParabolicCharacterEqProdSuperdiagonalSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0703
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseCoefficientSpacesIsometricMapsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlargedBase_coefficientSpaces_isometric_maps : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std → ∃ (cV' : ∀ i', CoefA (Vc (w'.st Z').toD7 i')) (c0L' : ∀ i' : Fin (w'.st Z').toD7.R.m, VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i').rank ((i' : ℕ) + 1) τ) →ₛₗ[(w'.st Z').toD7.what₂.embLL] (cV' i').W),
    (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (cV' i').W (z.R.cV i).W ∧ HEq (cV' i').ρ (z.R.cV i).ρ ∧ HEq (cV' i').nW (z.R.cV i).nW ∧ HEq (cV' i').iW (z.R.cV i).iW) ∧ (∀ i', (cV' i').Is) ∧
    (∀ i', Bridge.CoefMapTie (Vc (w'.st Z').toD7 i') (cV' i').coef (c0L' i') (rhoVr (labLL (w'.st Z').toD7) _)) ∧
    (∀ i' x y, inner ℂ (c0L' i' x) (c0L' i' y) = (w'.st Z').toD7.what₂.embLL (pairVr (labLL (w'.st Z').toD7) _
      (if (w'.st Z').toD7.sp.Vneg ((i' : ℕ) + 1) then -(Vc (w'.st Z').toD7 i').gram else (Vc (w'.st Z').toD7 i').gram) x y)) ∧
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok) (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (h : Bridge.Gf (Vc (w.st Z).toD7 i)) (v' : VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i').rank ((i' : ℕ) + 1) τ)),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 (LiftBrg.ptL (w.st Z) w.I (usedOf w.I T Wt) i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) 1 1 h)).1) →
      HEq (c0L' i' v') (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))) h) := by
  exact @GlobalTheory.Mem.RsCoef.rs_coef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDefiniteFormsGivenCoefficientStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicReading_definiteForms_given_coefficients : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (c0L : ∀ i : Fin X.toD7.R.m, VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W), (∀ i, (cV i).Is) → (∀ i, Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef (c0L i) (rhoVr (labLL X.toD7) _)) → (∀ i x y, inner ℂ (c0L i x) (c0L i y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _ (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) → ∃ (cX : CoefA X.toD7.sp.X') (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ (∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ) ∧ ∀ i : Fin X.toD7.R.m, ∀ (t : TupU I U) (φ : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i)) v', HEq v' (φ.1 (LiftBrg.ptL X I U i t 1 1 h)) → Bd.jL i t ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) φ :))) h = c0L i v' := by
  first | exact @GlobalTheory.Mem.R3.BrgAt.exists_brgL_at | exact GlobalTheory.Mem.R3.BrgAt.exists_brgL_at | (intros; apply GlobalTheory.Mem.R3.BrgAt.exists_brgL_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.FrameCaseLifts


open Formalism.IndefR.Seed Formalism.IndefR.Seed.Frm in
theorem frames_by_cases_lifts {D : D7} (hY : ∀ j, FrmC.StdLat (D.sp.Y j)) (hX : FrmC.StdLat D.sp.X')
    (hV : ∀ j, FrmC.StdLat (D.sp.V j)) (hW : ∀ j, 1 ≤ j → j ≤ D.R.m → FrmC.StdLat (D.sp.W j)) (Pg : Finset (Pl D.host.E)) :
    ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
      (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
      (βY : ∀ j, GL (Fin (Yc D j).rank) (Datum.EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (Datum.EAf D)),
      SDFrames ΛY (FrmP.coordL D.sp.X') (fun i => FrmP.coordL (Vc D i)) ΛW βY 1 (fun _ => 1) βW ∧
        (FramesExistDiagonal D Pg → NormalFrameConditionsDiagonal Pg βY βW) := by
  by_cases h : FramesExistDiagonal D Pg
  · obtain ⟨ΛY, -, -, ΛW, βY, -, -, βW, ⟨h1, -, -, h4⟩, h2⟩ := h
    exact ⟨ΛY, ΛW, βY, βW, ⟨h1, FrmP.isSDFrame_std _ hX 1, fun i => FrmP.isSDFrame_std _ (hV _) 1, h4⟩, fun _ => h2⟩
  · exact ⟨fun j => FrmP.coordL (Yc D j), fun i => FrmP.coordL (Wc D i), fun _ => 1, fun _ => 1,
      ⟨fun j _ => FrmP.isSDFrame_std _ (hY _) _, FrmP.isSDFrame_std _ hX 1, fun i => FrmP.isSDFrame_std _ (hV _) 1,
        fun i => FrmP.isSDFrame_std _ (hW _ (by omega) i.2) 1⟩, fun h' => absurd h' h⟩

theorem exists_levCh_tuples_of_lifts : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl), Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C → SelHalf I → X.B.host.ccK = ⊤ → (∀ j, Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Seed.FrmC.StdLat (X.toD7.sp.W j))) → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))) (mu : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → TupU I (usedOf I T Wt)) (twPl : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))), LevOf X I (usedOf I T Wt) L ∧ (Seed.Frm.FramesExistDiagonal X.toD7 L.Pg → Seed.Frm.NormalFrameConditionsDiagonal L.Pg L.βY L.βW) ∧ MuOf X I T Wt mu twPl ∧ (∀ Xg tr, Seed.TupL (famR X I hX (usedOf I T Wt) Xg tr) L mu twPl) ∧ ∀ t, ∀ P ∈ L.Q t, ((X.B.host.QS * X.B.host.q * Ideal.absNorm X.B.host.ccK : ℕ) : 𝓞 X.B.host.E) ∉ P.asIdeal := by
  intro X px I hX T Wt hWf hWc hI hrng hsel hcc hYVW hX'
  classical
  set U := usedOf I T Wt with hU
  have htw : ∀ a, Chr.IsTwist X.B.host I.S (I.xi a) := fun a =>
    (GlobalTheory.Mem.ReadTwist.isTwist_of_reads _ X.B.host _ _ _ (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have hram := GlobalTheory.Mem.Col2.RamQ.ram_iff X px I hI
  have hQr : ∀ a, ∀ PP ∈ I.Q a, ¬ (I.xi a).UnrAt PP := fun a PP h => (hram a PP).2 (Or.inl h)
  have hpl := fun a => GlobalTheory.Mem.TwistPlaces.twistPlaces X px I hI a (hQr a)
  obtain ⟨L0, h1, h2, h3, -, h4⟩ := GlobalTheory.LevelChoices.exists_levCh X.toD7 (Top.Fr.at X I.C) (TupU I U)
    (mu0F (X := X.B.fields) (tuOf I U)) (fun t => I.xi (ixOf I U t)) (fun t => I.Q (ixOf I U t))
    (hI.xi_inj.comp (ixOf_injective I U)) (by simp only [ixOf_mu0F]; exact hI.trueColumnChoices_heckeChar_reference_eq_one)
    (fun t => (htw _).1) (fun t => (htw _).2.1) (fun t => (htw _).2.2.1)
    (fun t => (hpl _).1) (fun t => (hpl _).2)
    (fun p hp => by
      have hpp : p.Prime := by
        rcases hp with rfl | rfl
        exacts [X.B.host.pde_prime, X.B.host.pde'_prime]
      obtain ⟨𝔭, h𝔭⟩ := GlobalTheory.Mem.R3.Model.exists_under_of_selHalf I hsel p hpp
      exact ⟨𝔭, fun t PP hPP hp' => h𝔭 _ PP hPP hp'⟩)
    (fun t PP => hram _ PP)
  have hPg : L0.Pg = (X.B.primes px).vGs := by
    refine Finset.ext fun P => (h4.Pg P).trans ?_
    rw [h1]
    exact (GlobalTheory.Mem.R3.Model.mem_vGs_iff I hI P).symm
  obtain ⟨ΛY, ΛW, βY, βW, hSD, hfr⟩ := frames_by_cases_lifts (D := X.toD7)
    (fun j => (hYVW j).1) hX' (fun j => (hYVW j).2.1) (fun j => (hYVW j).2.2) (X.B.primes px).vGs
  let L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U) :=
    { L0 with
      ΛY := ΛY
      ΛW := ΛW
      βY := βY
      βW := βW
      βX := 1
      βV := (fun _ => 1)
      ΛX := Formalism.IndefR.Seed.FrmP.coordL _
      ΛV := (fun _ => Formalism.IndefR.Seed.FrmP.coordL _) }
  have hLC : L.C = Top.Fr.at X I.C := h1
  have hLx : ∀ t, L.xiH t = I.xi (ixOf I U t) := fun t => congrFun h2 t
  obtain ⟨mu, twPl, hmu, htup⟩ := GlobalTheory.Mem.R3.tupL_of_twisted X px I hX T Wt L hWf hWc hI hrng hLC hLx
  refine ⟨L, mu, twPl, ⟨⟨h4.mu0, h4.eta, h4.xi, h4.xi_inj, h4.xi_base, h4.xi_fin, h4.xi_triv, h4.xi_tame, h4.Pg, h4.Q_pl,
      h4.Q_off, h4.Q_de, h4.Q_ram, h4.chi, h4.xiR, hSD.1, hSD.2.1, hSD.2.2.1, hSD.2.2.2⟩, h1, fun t => congrFun h2 t, hPg,
      fun t => congrFun h3 t, fun _ => rfl, rfl⟩, fun h => by
      show Seed.Frm.NormalFrameConditionsDiagonal L0.Pg βY βW
      rw [hPg]
      exact hfr (hPg ▸ h), hmu, htup, fun t P hP => ?_⟩
  have hP' : P ∈ I.Q (ixOf I U t) := by rw [← congrFun h3 t]; exact hP
  have hoff := ((hpl (ixOf I U t)).2 P hP').1
  intro hm
  apply hoff
  have e : Ideal.absNorm X.B.host.ccK = 1 := by rw [hcc, Ideal.absNorm_top]
  rw [e, mul_one] at hm
  have : ((X.toD7.host.QS * X.toD7.host.q * X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) =
      ((X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) * ((X.B.host.QS * X.B.host.q : ℕ) : 𝓞 X.toD7.host.E) := by
    rw [← Nat.cast_mul]
    congr 1
    change X.B.host.QS * X.B.host.q * X.B.host.d * X.B.sp.T = X.B.host.d * X.B.sp.T * (X.B.host.QS * X.B.host.q)
    ring
  rw [this]
  exact Ideal.mul_mem_left P.asIdeal _ hm


set_option maxHeartbeats 1000000 in
theorem exists_realDat_keep : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B)
    (Wt : Set X.B.places.Pl) (Ks' : Type) [Field Ks'] [NumberField Ks'] [Algebra Ks' X.toD7.what₂.LL],
    GlobalTheory.Published.DiscreteSeriesExists → Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C →
    SelHalf I → GrpAt X I → ValsIn I → HostHyp X.toD7 →
    (∀ j, Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Seed.FrmC.StdLat (X.toD7.sp.V j) ∧
      (1 ≤ j → j ≤ X.toD7.R.m → Seed.FrmC.StdLat (X.toD7.sp.W j))) → Seed.FrmC.StdLat X.toD7.sp.X' →
    (∀ i, (Vc X.toD7 i).IsPosDef) →
    (∀ x ∈ X.B.Ks, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = x) →
    (∀ x : X.toD7.host.E, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = X.toD7.embE x) →
    (∀ (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))), L.Is (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))) →
      L.C = Top.Fr.at X I.C → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 →
        ∃ y : Ks', ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap Ks' X.toD7.what₂.LL y)) →
    ∃ (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (R₀ : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt) Xg tr₀) Ks')
      (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd),
      LevOf X I (usedOf I T Wt) R₀.toRealDat.toLevCh ∧ IsPlacewiseIdentity X (px := px) R₀.eG ∧ GoodSet X (px := px) (R₀.eG.trans cG) Xg ∧
      MuOf X I T Wt R₀.mu R₀.twPl ∧ IdemClass (D := X.toD7) (famR X I hX (usedOf I T Wt) Xg tr₀).A ∧
      R₀.toRealDat.Pre0 (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧ R₀.AllPlaces ∧
      Keep R₀.toRealDat (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 cG ∧ BrgStd X I hX (usedOf I T Wt) Xg tr₀ R₀.toRealDat := by
  intro X px I hX T Wt Ks' _ _ _ hDS hWf hWc hI hrng hsel hgrp hval hhost hYVW hX' hpos hKs hE hmuKs
  obtain ⟨L, mu, twPl, hL, hfr, hmu, htup, hq⟩ :=
    exists_levCh_tuples_of_lifts X px I hX T Wt hWf hWc hI hrng hsel X.B.ccK_top hYVW hX'
  obtain ⟨eG, cG, Xg, hid, hgood, hpsi, hc1, hc2, hrest⟩ := GlobalTheory.T.exists_finite_group_goodSet_levels_characters X px I hX (usedOf I T Wt) L hI hgrp hL
  obtain ⟨hidem, hlv, plg, iso, hp1, hp2, hp3⟩ := hrest (fun _ g => g)
  obtain ⟨hMY, hMW⟩ := GlobalTheory.ChainModels.models_seed hDS X.toD7 hhost
  obtain ⟨MW, hMW1, hMW2⟩ := hMW Ks' hE
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar X.toD7
  obtain ⟨R, e1, e2, e3, e4, e5, e6, hpr, hpre, hin, htu, hall, hstd⟩ :=
    GlobalTheory.SeedChoices.seed_at_reading_keeping X.toD7 (Gc X.B px) (PlS X.B px) (PlI X.B px) (TupU I (usedOf I T Wt))
      (famR X I hX (usedOf I T Wt) Xg (fun _ g => g)) Ks' (face0 X I hX (usedOf I T Wt) Xg (fun _ g => g)) L eG mu twPl ψ MW
      hL.is (htup _ _) ⟨eG.trans cG, plg, iso, hgood.2, hp2, hp3⟩ hlv hMY hMW1 hpos hψ
      (fun cX cV jR jL => BrgStdR X I hX (usedOf I T Wt) Xg (fun _ g => g) L cX jR ∧
        ∀ i, BrgStdV X I hX (usedOf I T Wt) Xg (fun _ g => g) L i (cV i) (jL i))
      (GlobalTheory.T.exists_adelicReading_decoratedLatticeForms X px I hX (usedOf I T Wt) Xg (fun _ g => g) L eG hI hval hL hid hL.beta.2 hL.beta.1 hX' (fun i => (hYVW _).2.1))
  subst e1
  obtain rfl := eq_of_heq e4
  subst e3 e5 e6
  refine ⟨Xg, fun _ g => g, R, cG, hL, hid, hgood, hmu, hidem, hpre, hin, htu, hall,
    ⟨hpre.std, GlobalTheory.SignsAtTypePrimes.signsAtG _ _ _ _ _ _ R.toRealDat _ cG hpre.std hpsi ⟨plg, iso, hp1, hp2, hp3⟩, hfr, hL.beta,
      hpr, ⟨plg, iso, hp1, hgood.2, hp2, hp3⟩, hpsi, ⟨fun t P hP P' hP' h => ?_, hq⟩, hmuKs _ hL.is hL.C, hMW2,
      fun p => hKs _ (hc2 p), fun g => hKs _ (hc1 g)⟩, hstd⟩
  rw [hL.Q t] at hP hP'
  exact hsel _ _ P hP P' hP' h

end GlobalTheory.Mem.R3.FrameCaseLifts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceLevelsClassesComparisonMaps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.KerOne

theorem levels_cls_cmp_at_served : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg))
        (clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1))
        (up : Formalism.L2.G.Cmp.CmpUp t.cmp (w.tw Z) u v hg Lv),
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ (a a' : Lv.compS j) (L L' : ((Fl u v hg).Pj (j + 1)).Tup),
          ((Fl u v hg).Pj (j + 1)).IsLatTup L → ((Fl u v hg).Pj (j + 1)).IsLatTup L' →
          (clsS j a L = clsS j a' L' ↔ a = a' ∧ ∃ γ : (Lv.levS j a).Γ, L' = (Lv.levS j a).smul γ L)) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ x, ∃ a L, ((Fl u v hg).Pj (j + 1)).IsLatTup L ∧ clsS j a L = x) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → Submodule.span ((w.D Z).gat u v hg).O
          (up.cmpS j '' ((((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).L :
            Set (((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).V)) = Lv.Int (j + 1)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨Lv, I, H, hC, hX, hE0⟩ : ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
    by_cases hμ : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0
    · exact GlobalTheory.T.exists_comparisonData_steps_upTo_rank w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ
    · exact GlobalTheory.T.comparison_data_steps_non_reference_tuple w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ
  classical
  let S := Formalism.MainNotions.G.CmpJ.stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds t.Gt
  let clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1) :=
    fun j a L => if hj : j + 1 ≤ (w.D Z).R.m then
      Formalism.MainNotions.G.KAat.castCls (hC j hj) (j + 1) (Formalism.MainNotions.G.KAat.clsOf (S := (I.at' j hj).st) (H.core j hj) a L)
    else (hE0 j (by omega)).elim a
  have hcls : ∀ j (hj : j + 1 ≤ (w.D Z).R.m) a L, clsS j a L =
      Formalism.MainNotions.G.KAat.castCls (hC j hj) (j + 1) (Formalism.MainNotions.G.KAat.clsOf (S := (I.at' j hj).st) (H.core j hj) a L) :=
    fun j hj a L => dif_pos hj
  refine ⟨Lv, clsS, Formalism.L2.G.Cmp.CmpUp.ofRat S.cmpS S.injS S.ratS, ?_, ?_, ?_⟩
  · intro j hj a a' L L' hL hL'
    rw [hcls j hj, hcls j hj, (Formalism.MainNotions.G.KAat.castCls_inj _ _).eq_iff]
    exact Formalism.MainNotions.G.KAat.clsOf_iff (S := (I.at' j hj).st) (H.core j hj) (hX j hj) a a' L L' hL hL'
  · intro j hj x
    obtain ⟨x0, rfl⟩ := Formalism.MainNotions.G.KAat.castCls_surj (hC j hj) (j + 1) x
    obtain ⟨a, L, hL, e⟩ := Formalism.MainNotions.G.KAat.clsOf_surj (S := (I.at' j hj).st) (H.core j hj) x0
    exact ⟨a, L, hL, (hcls j hj a L).trans (congrArg _ e)⟩
  · intro j hj
    exact S.intS (Formalism.MainNotions.G.CmpJ.descUp H t.Gt) j hj

end GlobalTheory.Mem.Top.KerOne
end

