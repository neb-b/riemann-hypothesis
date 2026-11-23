module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumReads
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2975
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormsOfArchimedeanStatements
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtCalc

theorem arFormExists_arMix_heightProjection (hI : ArchInteg) (hR : ArchRecip) :
    GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  have hE := _root_.GlobalTheory.MixHt.exists_isMix_of_arch hI hR
  refine ⟨_root_.GlobalTheory.MixHt.arFormExists_of_isMix hI hE, _root_.GlobalTheory.MixHt.arMix_of_mixHt hI hE, ?_⟩
  intro k _ X Y _ p q D e hX hY π hπ _ _ L h hh
  obtain ⟨T, hT⟩ := hE k Y q (isAmb_of_isArithVar hY) (e + 1)
  obtain ⟨h', hh', -⟩ := _root_.GlobalTheory.MixHtDiag.exists_isArithHeight hI k Y q e hY T hT (L.pull π hπ)
  exact ⟨h', hh', _root_.GlobalTheory.MixHt.heightProj k X Y p q D e hX hY π hπ L h h' hh hh' (genericPoint Y)⟩

end GlobalTheory.MixHtCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotIntertw

open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)

variable {D : D7}

theorem xiN_of_reads {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {δ : ℂ} (hs : δ ≠ 0) {G : VC D a d → ℂ} {f : WO S T → ℂ}
    (h : Reads ψ θ hS hT ⊤ δ 1 G f) :
    GlobalTheory.AdForm.xiN θ S T hS hT (-δ) (area (lamOf D ⊤ δ))⁻¹ f = G := by
  funext z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hsp : ∀ Z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ,
      (GlobalTheory.AdForm.realPt θ Z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (GlobalTheory.AdForm.realPt θ Z) = Z τ := fun Z => by
    refine Classical.epsilon_spec (p := fun w : Mx D T.rank S.rank => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Z τ)
      ⟨Matrix.of fun i j => σ fun τ => Z τ i j, ?_, fun τ => ?_⟩
    · ext i j; exact hσ.fin _
    · ext i j; exact hσ.comp _ _
  unfold GlobalTheory.AdForm.xiN
  obtain ⟨h1, h2⟩ := hsp fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))
  have hY : GlobalTheory.NormExact.coordY θ hS hT δ 1 (GlobalTheory.AdForm.realPt θ
      fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))) = z := by
    funext τ i j
    unfold GlobalTheory.NormExact.coordY
    rw [h2, map_one, mul_one, Matrix.of_apply, inv_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    rfl
  rw [h.2 _ h1, hY, ← mul_assoc, ← Complex.exp_add]
  have hH : Formalism.L2.Ker.HV (area (lamOf D ⊤ δ))⁻¹ z z = Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D ⊤ δ) z z := by
    change (((area (lamOf D ⊤ δ))⁻¹ : ℝ) : ℂ) * _ = _ / ((area (lamOf D ⊤ δ) : ℝ) : ℂ)
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  rw [hH, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

theorem isFinPt_one (V : HSp D) {n : ℕ} (e : V.rank = n) :
    GlobalTheory.BotFormula.IsFinPt V 1 (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  subst e
  refine ⟨one_mem _, rfl, fun i j => ?_⟩
  rw [map_one]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

theorem reads_of_fock {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} (hset : Setup ψ θ S T cc δ r)
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) :
    ∃ G ∈ TT D (tor0 D cc δ) a d, Reads ψ θ hS hT cc δ r G f := by
  obtain ⟨G, hG, hR⟩ := GlobalTheory.VacLine.exists_reads hS hT hset hf hv
  have hRt : ∀ z, Reads ψ θ hS hT cc δ r (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G)
      (wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • heisO ψ S T (finPt hS hT r z) f) := fun z =>
    (GlobalTheory.NormExact.heisO_finPt_reads ψ θ S T hS hT cc δ r hset G f hR z).smul _
  obtain ⟨n, hn, hL⟩ := _root_.GlobalTheory.MovedTr.moved_translate ψ θ S T hS hT cc δ r hset χS χT om hom 1 1 1 1 (isFinPt_one S hS) (isFinPt_one T hT) f hf 0
  refine ⟨G, ⟨hG, n, hn, fun x hx => ?_⟩, hR⟩
  obtain ⟨z, rfl, hz⟩ := _root_.GlobalTheory.NormSum.exists_pt_of_mem_La_moved D (GlobalTheory.InducedType.induced_type D).1 cc δ hset.crv.1.1 a d 1 1 _ _
    (GlobalTheory.NormSum.VacMove.moves_one D a) (GlobalTheory.NormSum.VacMove.moves_one D d) x hx
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hz
  have hp : n • pt D (tor0 D cc δ) δ z = pt D (tor0 D cc δ) δ (n • z) := by
    funext τ i j
    simp [pt, embV, tor0]
    ring
  have h2 := hL (n • z) (fun i j => ⟨_, hz i j, by
    have h0 : (0 : Matrix (Fin d) (Fin a) D.host.E).map (inc D) = 0 := by ext; simp
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    simp⟩)
  have e1 : om (1, 1) = 1 := map_one om
  rw [e1, Module.End.one_apply, Module.End.one_apply] at h2
  have h3 := hRt (n • z)
  have h4 := hRt 0
  rw [GlobalTheory.NormSum.VacMove.pt_zero, GlobalTheory.NormSum.wd_zero] at h4
  rw [GlobalTheory.NormSum.VacMove.pt_zero] at h2
  rw [← h2] at h3
  rw [hp]
  exact GlobalTheory.VacLine.reads_inj hset h3 h4

theorem conj_datum {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (s : T) :
    IsThetaFunO W.ψ A WW (fun w => starRingEnd ℂ (X.f s w)) ∧
      ∀ τ, IsFockVacAt (heisO W.ψ A WW) W.θ τ (cplxO 1 1) (fun w => starRingEnd ℂ (X.f s w)) := by
  have hI := hX.is
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f s) := (GlobalTheory.ConstRatio.theta_f hI s).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem s)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f s) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst s)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  refine ⟨GlobalTheory.CjNeg.theta_negS' hψ (show IsThetaFunO W.ψ (GlobalTheory.ChiGrid.negSp A) WW (X.f s) from hf), fun τ => ?_⟩
  have h := hv τ
  rw [(hX.std.2.2 τ).1, (hX.stdW.2.2 τ).1] at h
  exact GlobalTheory.BotFormula.ConjJet.isFockVacAt_conj hψ hθ A WW _ hf τ h

theorem bottom_finParts {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀)
    {i j : Fin D.R.m} {s : T} {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q} {𝔪 : Ideal (𝓞 D.host.E)}
    (hB : IsBottom G s i j 𝔪 P P') :
    HasFinPart (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))⁻¹ P.W.chV P.W.ep ∧
    HasFinPart ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) /
      (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)))⁻¹ P.W.chV' (-P.W.ep') := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have h1 := _root_.GlobalTheory.FinIdlRead.chr_finIdl _ _ (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)) x y hxy
    have h2 := _root_.GlobalTheory.FinIdlRead.chr_finIdl _ _ hL.eta x y hxy
    have e : (betaH G i j)⁻¹.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) =
        ((G.ch.chiH (D.R.m - i)).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) *
          L.C.eta.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) ^ (rankV D i j % 2))⁻¹ := rfl
    rw [hB.chars.1 y, e, MonoidHom.inv_apply, Circle.coe_inv, MonoidHom.mul_apply, MonoidHom.pow_apply, Circle.coe_mul,
      Circle.coe_pow, h1, h2]
    simp
  · have eν : ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) /
        (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)))⁻¹ = G.nu s i (j + 1) := by
      rw [inv_div]; exact mul_div_mul_right_eq_div _ _ _
    have e : (nuH G s i j)⁻¹.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) =
        ((nuH G s i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y))⁻¹ := rfl
    rw [eν, zpow_neg, hB.chars.2 y, e, inv_inv]
    exact _root_.GlobalTheory.FinIdlRead.chr_finIdl _ _ (chrEq_nu G s i j hL) x y hxy

end GlobalTheory.BotIntertw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValueMemLocalUnitsMulSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

open GlobalTheory.Poinc.Sep.Coef (om tele root_mem prod_mem)

theorem chi_mem : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (a : D.X) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ χ : LB.Gen (LB.LinComb D.P.L ![(D.c a * b).left, (D.c a).left, b.left, (η[D.P.A]).left] DegPre.gtε),
      (χ.IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c a) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χ T.hom z J ^ N₁) →
    ∃ c ∈ k₀, (val χ (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ *
        GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ N₁ hN a b hb hbdef χ hχ
  obtain ⟨-, hM₀, hpb, hw, hc, -, -⟩ := hFB
  have h2 : spMap ev ≫ spMap ib = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hP : Coef.Idx.PowPts ib (fun _ : PUnit => β) := by
    intro T' g hg
    obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hpb T'.hom g hg
    exact ⟨e.trans (MulEquiv.piUnique fun _ : PUnit => (Over.mk g ⟶ B₀)).symm, fun x u => by cases u; exact he x⟩
  have hone : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (1 : Over.mk (spMap ev) ⟶ D.P.A).left := by
    intro _
    obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hpb (spMap ev) _ h2
    have e1 := he 1
    rw [map_one] at e1
    rw [← e1]
    exact defOver_comp k₀ (defOver_spMap k₀ (ev.comp ib) hk) _
  have H : Coef.Idx.Desc ib (fun _ : PUnit => β) ev k₀ w :=
    ⟨hk₀, hP, hk, hM₀, hw, fun _ _ _ h i => h i, hone⟩
  have pc : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c a).left := by
    intro _
    show DefOver k₀ ((spMap ev ≫ GlobalTheory.UChart.cpt D a) ≫ β)
    rw [Category.assoc, hc a, ← Category.assoc, h2]
    exact defOver_comp k₀ (defOver_spMap k₀ (ev.comp ib) hk) _
  have pb : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (toUnit (Over.mk (spMap ev)) ≫ b).left := by
    intro _
    show DefOver k₀ ((spMap ev ≫ b.left) ≫ β)
    rw [Category.assoc]; exact hbdef
  have pbi : ∀ i : ℕ, Coef.Idx.RatP (fun _ : PUnit => β) k₀ ((toUnit (Over.mk (spMap ev)) ≫ b) ^ i).left := by
    intro i
    induction i with
    | zero => rw [pow_zero]; exact hone
    | succ i ih => rw [pow_succ]; exact Coef.Idx.ratP_mul hP hk ih pb
  set x := toUnit (Over.mk (spMap ev)) ≫ D.c a with hx
  set y := toUnit (Over.mk (spMap ev)) ≫ b with hy
  have hyN : y ^ N₁ = 1 := by rw [hy, ← MonObj.comp_pow, hb, MonObj.comp_one]
  have hcub := hχ.2 (Over.mk (spMap ev)) z J hJ
  simp only [MonObj.comp_pow] at hcub
  choose c hc' ec using fun i : ℕ => Coef.Idx.cub_mem H x (y ^ i) y pc (pbi i) pb z J J₀ hJ hJ₀
  set h : (Over.mk (spMap ev) ⟶ D.P.A) → ((Sp K).presheaf.stalk z)ˣ := fun p => om (Z := Sp K) w z J J₀ p.left with hh
  set G := h (x * y) * (h x)⁻¹ * (h y)⁻¹ * h 1 with hG
  obtain ⟨c₁, hc₁, e₁⟩ := prod_mem (Finset.range N₁) (fun i => ⟨c i, hc' i, ec i⟩)
  have key : (∏ i ∈ Finset.range N₁, ((h (x * y ^ i * y) * (h (x * y ^ i))⁻¹ * (h (x * y))⁻¹ * (h (y ^ i * y))⁻¹ *
      h x * h (y ^ i) * h y * (h 1)⁻¹) * @id ((Sp K).presheaf.stalk z)ˣ (cubV D.cub (T := Over.mk (spMap ev)) z J x (y ^ i) y))) =
      (G⁻¹ * val χ (spMap ev) z J) ^ N₁ := by
    rw [Finset.prod_mul_distrib, tele h x y N₁ hyN]
    have e3 : (∏ i ∈ Finset.range N₁, @id ((Sp K).presheaf.stalk z)ˣ (cubV D.cub (T := Over.mk (spMap ev)) z J x (y ^ i) y)) =
        val χ (spMap ev) z J ^ N₁ := hcub
    have e4 : ∀ A B C E : ((Sp K).presheaf.stalk z)ˣ, A⁻¹ * B * C * E⁻¹ = (A * B⁻¹ * C⁻¹ * E)⁻¹ :=
      fun A B C E => by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
    rw [e3, e4, ← mul_pow]
  rw [key] at e₁
  obtain ⟨c₂, hc₂, e₂⟩ := root_mem hk₀ (z := z) (s := (G⁻¹ * val χ (spMap ev) z J).val) (n := N₁) (by omega) ⟨c₁, hc₁, by rw [← Units.val_pow_eq_pow_val]; exact e₁⟩
  refine ⟨c₂, hc₂, ?_⟩
  have hGe : G = gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
      (gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ * gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left) := by
    rw [hG, hh, hx, hy, ← MonObj.comp_mul]
    rfl
  rw [← hGe, ← e₂, ← Units.val_mul, mul_inv_cancel_left]

end GlobalTheory.USep.EvG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointOfValuesInSmallAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_of_values_in_small_algClosed : ∀ (F A R K : Type) [Field F] [NumberField F] [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Field K] (b : F →+* A), b.EssFiniteType → ∀ ψ : A →+* R, GlobalTheory.TChart.IsComplAt ψ → ∀ (ev : R →+* K) (k₀ : Subfield K), Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) → (∀ a, ev (ψ a) ∈ k₀) → (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀ := by
  first | exact @GlobalTheory.PointAlg.closed_point_of_values | exact GlobalTheory.PointAlg.closed_point_of_values | (intros; apply GlobalTheory.PointAlg.closed_point_of_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseStableUnderPullbackOfData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.DivFromPull

theorem divFrom_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (Q : DegPre R) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* R) (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (hD : IsPullDeg θ Q Q') (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ y, e' y = e (hD.xe y)) → (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (oQ.onB.act x)) → (∀ k, θ (s k) ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' (θ.comp iw) (fun k => θ (s k)) ε e' := by
  intro E _ _ _ H D' l c L R V _ _ _ _ Q _ oQ Q' _ oQ' iw θ I _ s ε e hD e' he' hact hs hdiv
  obtain ⟨g, hD0, hg, hxe, hac⟩ := hdiv
  have ψL : Nonempty (PsiOn (mulDeg L.D l.M') ⊤) := GlobalTheory.ArcPull.nonempty_psiOn_top _ (fun y => L.gen (l.M' • y))
  obtain ⟨hD1, hW1, hp1, hx1⟩ := _root_.GlobalTheory.PullDegWhole.exists_isPullDeg_top hD0 ψL
  have ψR : Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) := by
    have := GlobalTheory.PullDegUniq.nonempty_psiOn_pull hD1
    rw [hW1] at this
    simpa using this

  let n : Q'.X → I → ℤ := fun y k => (l.M' : ℤ) * ε k (e' y) (H.w0 • e' y)
  have hs0 : ∀ k, algebraMap V (FractionRing V) (θ (s k)) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs k)
  have hr0 : ∀ k, algebraMap R (FractionRing R) (s k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (fun h => hs k (by rw [h, map_zero]))
  let g' : Q'.X → (FractionRing V)ˣ := fun y =>
    (Units.mk0 (∏ k, algebraMap V (FractionRing V) (θ (s k)) ^ n y k)
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hs0 k)))⁻¹
  have hab : ∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧
      (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a) := by
    intro y
    have key : ∀ {K : Type} [Field K] (x : K), x ≠ 0 → ∀ m : ℤ, x ^ (-m) * x ^ m.toNat = x ^ (-m).toNat := by
      intro K _ x hx m
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
      congr 1
      omega
    have hgz : (g (hD.xe y) : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (s k) ^ (-n y k) := by
      have h := hg (hD.xe y)
      rw [Units.val_inv_eq_inv_val] at h
      rw [← inv_inv (g (hD.xe y) : FractionRing R), h, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg]
      simp only [n, he' y]
    have hg'y : (g' y : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (θ (s k)) ^ (-n y k) := by
      simp only [g', Units.val_inv_eq_inv_val, Units.val_mk0, ← Finset.prod_inv_distrib, zpow_neg]
    refine ⟨∏ k, s k ^ (-n y k).toNat, ∏ k, s k ^ (n y k).toNat, ?_, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 fun k _ => by rw [map_pow]; exact pow_ne_zero _ (hs k)
    · rw [hgz, map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_pow, map_pow]
      exact key _ (hr0 k) _
    · rw [hg'y, map_prod, map_prod, map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_pow, map_pow, map_pow, map_pow]
      exact key _ (hs0 k) _
  obtain ⟨h1, hp2, hx2⟩ := _root_.GlobalTheory.RescaleBoth.exists_isPullDeg_rescale hD g g' ψR hab
  obtain ⟨r, hpr, hxr⟩ := _root_.GlobalTheory.PullDegCompTop.exists_isPullDeg_comp_top hD1 h1 hW1
  refine ⟨g', r, fun y => ?_, fun y => ?_, fun x => ?_⟩
  · simp only [g', Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0, map_zpow]
    rfl
  · exact (hxr y).trans ((hx1 _).trans ((congrArg hD0.xe (hx2 y)).trans ((hxe _).trans (he' y).symm)))
  · letI := H.starRing
    have c₁ : (oQ'.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) =
        hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ≫ (oQ.onB.act x).left := by
      have := congrArg (fun m => m.left ≫ pullback.fst Q.P.A.hom (specOf θ)) (hact x)
      simpa only [Over.comp_left, Category.assoc, GlobalTheory.Mum.over_pullback_map_left_comp_pullbackFst_scheme] using this
    have hpr' : r.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf (θ.comp iw)) =
        (hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫ hD0.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) :=
      hpr.trans (by rw [hp1]; exact congrArg (· ≫ _) hp2)
    have key : (oQ'.onB.act x).left ≫ ((hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫ hD0.e.hom.left ≫
        pullback.fst L.D.P.A.hom (specOf iw)) = ((hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫
        hD0.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left := by
      simp only [Category.assoc] at c₁ hac ⊢
      rw [reassoc_of% c₁]
      exact congrArg _ (congrArg _ ((hac x).trans (Category.assoc _ _ _).symm))
    exact (congrArg _ hpr').trans (key.trans (congrArg (· ≫ _) hpr'.symm))

end GlobalTheory.UCanon.DivFromPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompBEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCanon.LowPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A]
    (f : L.W →+* A) :
    ∃ (o' : LowObj D' c (f.comp L.b)) (m : ObjMap o' L.o (spMap f)) (x : L.D.X → (Sp A ⟶ o'.t.G.left)),
      (∀ y, x y ≫ m.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  have hs : lowMap c (f.comp L.b) = spMap f ≫ lowMap c L.b := by
    simp only [lowMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨o', ⟨m⟩⟩ := (GlobalTheory.UCanon.obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).1
    (lowMap c L.b) L.o (spMap f) (lowMap c (f.comp L.b)) hs
  have hB := L.ab.1.1
  have u : ∀ y, ∃ u : Sp L.W ⟶ L.o.t.G.left, u ≫ L.φB = (L.D.c y).left ∧ u ≫ L.o.t.G.hom = 𝟙 _ := by
    intro y
    refine ⟨hB.lift (L.D.c y).left (𝟙 _) ?_, hB.lift_fst _ _ _, hB.lift_snd _ _ _⟩
    simpa using Over.w (L.D.c y)
  choose u hu₁ hu₂ using u
  have hm := m.toSABMap.cart.1
  refine ⟨o', m, fun y => hm.lift (spMap f ≫ u y) (𝟙 _) ?_, fun y => ?_, fun y => hm.lift_snd _ _ _⟩
  · rw [Category.assoc, hu₂, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, hm.lift_fst, Category.assoc, hu₁]

theorem exists_pull₂ {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A]
    (f₁ f₂ : L.W →+* A) (h : f₁ = f₂) :
    ∃ (o' : LowObj D' c (f₁.comp L.b)) (m₁ : ObjMap o' L.o (spMap f₁)) (m₂ : ObjMap o' L.o (spMap f₂))
      (x : L.D.X → (Sp A ⟶ o'.t.G.left)),
      (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f₁ ≫ (L.D.c y).left) ∧
      (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap f₂ ≫ (L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  subst h
  obtain ⟨o', m, x, hx, hxs⟩ := exists_pull L A f₁
  exact ⟨o', m, m, x, hx, hx, hxs⟩

end GlobalTheory.UCanon.LowPull

namespace GlobalTheory.UCanon.LowPull
theorem comp_b_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (F : Fam Xo c R)
    {V : Type} [CommRing V] [IsDomain V] (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R))
    (h₁ : κ₁ ≫ jK R = jK V ≫ spMap θ₁) (h₂ : κ₂ ≫ jK R = jK V ≫ spMap θ₂) (hy : κ₁ ≫ F.y = κ₂ ≫ F.y) :
    θ₁.comp F.b = θ₂.comp F.b := by
  have key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ →
      jK V ≫ spMap (θ.comp F.b) = κ ≫ F.y ≫ pullback.snd _ _ := by
    intro θ κ h
    rw [F.y_over, ← Category.assoc, h, Category.assoc, spMap_comp]
  have e : jK V ≫ spMap (θ₁.comp F.b) = jK V ≫ spMap (θ₂.comp F.b) := by
    rw [key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hy, Category.assoc]
  simp only [jK, spMap, ← Spec.map_comp] at e
  have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  ext r
  have := congrArg (fun f => f r) e2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  exact IsFractionRing.injective V (FractionRing V) this
end GlobalTheory.UCanon.LowPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsClassifyMarkedPeriodsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoints_classify_markedPeriods : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → FineAt (M.univ.fam h hL) σ ρ N (D.Cls N) := by
  first | (exact @GlobalTheory.UPel.HT.Model.fineAt_univ) | (exact GlobalTheory.UPel.HT.Model.fineAt_univ) | (intros; apply GlobalTheory.UPel.HT.Model.fineAt_univ <;> assumption)
end

