module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorePairIntegralPointPairsTriviallyHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto.IntDatum

theorem selfDual_core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.core i)) (G.latS (.core i)) ∧ IsSelfDualC (G.pT (.core i)) (G.latT (.core i)) := by
  have hV : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.core k)) (G.Λ (.core k)) := fun k hk =>
    (G.isV (X := .core k) hk (fun j h => Node.noConfusion h)).sd
  exact ⟨isSelfDualC_neg (hV (i + 1) hi), hV i hi.le⟩

theorem finPart_mul_inv_mem {D : D7} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (s : 𝓞 D.host.E)
    (hs : ∀ P ∈ S, s ∉ P.asIdeal) (hs0 : s ≠ 0) : finPart D (e * incA D ((s : D.host.E))⁻¹) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  by_contra h
  exact hs PP hPP (((hes PP hPP).2 s hs0).2 h)

end GlobalTheory.CoreOnto.IntDatum

open GlobalTheory.CoreOnto.IntDatum in
theorem GlobalTheory.CoreOnto.IntDatum.psi_int : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)), ∀ a ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True), IsHalf (cA D e) a → W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) a) = 1 := by
  intro D hQ T L μ₀ hL sc G W M hM i hi e he x₀ hx₀ a ha _
  classical
  obtain ⟨hS, hT⟩ := selfDual_core G i hi
  set N : ℕ := Ideal.absNorm D.host.ccK with hNdef
  have hN : ∀ P ∈ G.pl.W0, ((N : 𝓞 D.host.E)) ∉ P.asIdeal := by
    intro P hP h
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = P := by
      unfold Places.W0 at hP
      simpa using hP
    refine GlobalTheory.AAUnit.absNorm_cmIdeal_not_mem_gridPlaces G.pl hv ?_
    rw [← G.pl.under_w hv]
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ (G.pl.w v).asIdeal
    rwa [map_natCast]
  have hNn : N ≠ 0 := by
    rw [hNdef]
    exact fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hs0 : (N : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hNn
  have hN0 : ((N : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hNn
  have hα : ((N : 𝓞 D.host.E) : D.host.E) ∈ D.host.AA := by
    have := GlobalTheory.HostClear.absNorm_mem_AA D
    push_cast
    exact this
  have h1 := GlobalTheory.AscFinWit.rat_mem_latO (P := fun _ => True) hS hT x₀ (fun y hy => hx₀ y hy) hα
  have h2 := finPart_mul_inv_mem he (N : 𝓞 D.host.E) hN hs0
  have h3 := GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ h2 _ h1
  refine GlobalTheory.AscFinWit.psi_eq_one (P := fun _ => True) W.ψ_std hS hT ?_ ha
  convert h3 using 1
  have hu : incA D ((N : 𝓞 D.host.E) : D.host.E)⁻¹ * incA D ((N : 𝓞 D.host.E) : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hN0, map_one]
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.MixModel.rat, Matrix.map_apply, map_mul]
  linear_combination (GlobalTheory.FinPlLoc.idem D fun _ => True) * e * incA D (x₀ j k) * hu.symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitHeckeVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.RowEx.BottomHecke

variable {D : D7}

theorem thetaFunO_stdLatSp {ψ : AddChar (AF D.host.F) ℂ} {S V : HSp D} (hV : V.gram = 1) {f : WO S V → ℂ} :
    IsThetaFunO ψ S (GlobalTheory.SplitVacAlg.stdLatSp V hV) f ↔ IsThetaFunO ψ S V f :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem weilDatumO_stdLatSp {ψ : AddChar (AF D.host.F) ℂ} {S V : HSp D} (hV : V.gram = 1) {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)} (h : IsWeilDatumO ψ S V χS χT om) :
    IsWeilDatumO ψ S (GlobalTheory.SplitVacAlg.stdLatSp V hV) χS χT om :=
  { std := h.std,
    hecS := h.hecS,
    hecT := h.hecT,
    resS := h.resS,
    resT := h.resT,
    om_pres := fun p f hf => (thetaFunO_stdLatSp hV).2 (h.om_pres p f ((thetaFunO_stdLatSp hV).1 hf)),
    om_heis := fun g h' w f hf => h.om_heis g h' w f ((thetaFunO_stdLatSp hV).1 hf),
    om_aut := fun γ hγ γ' hγ' f hf => h.om_aut γ hγ γ' hγ' f ((thetaFunO_stdLatSp hV).1 hf),
    om_cont := fun f hf => h.om_cont f ((thetaFunO_stdLatSp hV).1 hf),
    om_unit := fun μ 𝓕 hμ h𝓕 p f hf => h.om_unit μ 𝓕 hμ h𝓕 p f ((thetaFunO_stdLatSp hV).1 hf),
    om_split := fun e he g h' hg hh x y hx hy => by
      obtain ⟨r, hr, H⟩ := h.om_split e he g h' hg hh x y hx hy
      exact ⟨r, hr, fun ℓ hℓ f hf => H ℓ (fun u hu f' hf' => hℓ u hu f' ((thetaFunO_stdLatSp hV).2 hf')) f
        ((thetaFunO_stdLatSp hV).1 hf)⟩ }

theorem vacuum_hecke : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW), Formalism.L2.NTheta.IsHeckeElt (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) e (ϖ : D.host.E) k α →
      ∃ Δ : Finset (WO (GlobalTheory.Grid.neg A) WW), (∀ u ∈ Δ, u.map (infPart D) = 0) ∧
        X.ω t (1, α) X.vac =
          ((((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW α) : Circle) : ℂ) *
            ((Real.sqrt (Δ.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ Δ, heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac := by
  intro D T L sc G W i j A A' WW X hX t e he ϖ k α hα
  obtain ⟨hg, hlat, -⟩ := hX.stdW
  have hS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := isSelfDualC_neg' hX.is.rigA.1
  have hT : IsSelfDualC (GlobalTheory.SplitVacAlg.stdLatSp WW hg) X.rW.Λ := hX.is.rigW.1
  have hL : (X.rW.Λ : Set (Fin WW.rank → D.host.E)) = L0c D (GlobalTheory.SplitVacAlg.stdLatSp WW hg) :=
    Set.ext fun y => (hlat y).trans (GlobalTheory.SplitVacAlg.mem_frameLattice_iff_integral_coords WW hg y).symm
  obtain ⟨Δ, hΔ⟩ := GlobalTheory.HeckeVacuum.exists_halfReps hS hT hL he hα
  refine ⟨Δ, fun x hx => GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj he) (hΔ.1 x hx).2, ?_⟩
  have hW := weilDatumO_stdLatSp hg (hX.is.weil t)
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) (GlobalTheory.SplitVacAlg.stdLatSp WW hg) X.vac :=
    (thetaFunO_stdLatSp hg).2 hX.is.isVac.2.theta
  have h := GlobalTheory.HeckeVacuum.om_elt hW hS hT hL he hα hf hX.is.isVac.2.lat hΔ
  have e1 : X.ω t (1, α) X.vac = ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm 1, α) X.vac := rfl
  rw [e1, map_one]
  exact h

end GlobalTheory.RowEx.BottomHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitPlaceStabiliserVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.StabVacSplit

open GlobalTheory.Grid (neg)


set_option maxHeartbeats 1000000 in
theorem stab_vac_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (k : GA D WW), k ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ → Formalism.L2.Theta.SuppAt e WW k →
      X.ω t (1, k) X.vac =
        (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac := by
  intro D T L sc G W i j A A' WW X hX t e he k hk hsupp
  set om' := (X.ω t).toSgn true with hom'
  have hW : IsWeilDatumO W.ψ (neg A) WW _ _ om' := hX.is.weil t
  have hsdS : IsSelfDualC (neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hLW : L0c D (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) = (X.rW.Λ : Set (Fin WW.rank → D.host.E)) := by
    ext y
    exact (GlobalTheory.SplitVacAlg.mem_frameLattice_iff_integral_coords WW hX.stdW.1 y).trans (hX.stdW.2.1 y).symm
  have fwd : ∀ h : GA D WW, h ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ →
      ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) →
        actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) := by
    intro h hh u hu
    have h1 : (1 : AE D) • actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) :=
      GlobalTheory.HeckeVacuum.smul_actO_mem _ _ 1 h (fun y hy => by
        rw [map_one, one_smul]
        have h2 := (hh.2.1 y).1 (by rw [hLW]; exact hy)
        rw [hLW] at h2
        exact h2) u hu
    rwa [one_smul] at h1
  have hinv : k⁻¹ ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ :=
    (GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k⁻¹).1
      (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k).2 hk))
  have hback : ∀ u : WO (neg A) WW, actO (neg A) WW 1 k⁻¹ (actO (neg A) WW 1 k u) = u := fun u => by
    rw [← GlobalTheory.HeckeVacuum.act_mul (S := neg A) (T := WW) k⁻¹ k u, inv_mul_cancel, GlobalTheory.HeckeVacuum.act_one]
  have hlat : ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) ↔
      actO (neg A) WW 1 k u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) :=
    fun u => ⟨fwd k hk u, fun hu => (hback u) ▸ fwd k⁻¹ hinv _ hu⟩
  have h1 : om' (1, k) X.vac = ((splitFacO _ _ (GlobalTheory.VecInv.detAt e he.1 (neg A) 1) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac :=
    _root_.GlobalTheory.VecInv.om_latVac_split D W.ψ (neg A) WW X.rA.Λ X.rW.Λ _ _ om' hW hsdS hsdT e he 1 k
      (GlobalTheory.SplitLinear.suppAt_one e _) hsupp hlat _ _ (GlobalTheory.VecInv.isDetAt_detAt e he.1 (neg A) 1)
      (GlobalTheory.VecInv.isDetAt_detAt e he.1 WW k) X.vac hX.is.isVac.2.theta hX.is.isVac.2.lat
  have e1 : X.ω t (1, k) = om' (1, k) := by
    rw [hom']
    show X.ω t (1, k) = X.ω t ((GlobalTheory.Grid.ofSgn true A) 1, k)
    rw [map_one]
  rw [e1, h1, splitFacO, map_one, map_one, inv_one, one_mul]

end GlobalTheory.StabVacSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.RowLoc

variable {D : D7}

theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j) : WO (negSp S) T) =
      -(Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) := by
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem mem_latO_negSp {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} {u : WO S T} : u ∈ latO (negSp S) T LS LT P ↔ u ∈ latO S T LS LT P := by
  constructor
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [gen_negSp]
      exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [← neg_neg (Matrix.of _), ← gen_negSp]
      exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx

theorem latRow_at : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0, ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)),
    MxAt (· = v) u → (u ∈ latRow G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  intro D _ T L μ0 _ sc G W M _ i _ v hv u hu
  have hoff : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u = 0 := by
    intro e he
    have he' := GlobalTheory.StepComb.idemSum_mem_idAt he
    have hev : e ∈ idOff D (· = v) := by
      rw [idOff, Ideal.mem_iInf]
      rintro ⟨w, rfl⟩
      rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at he'
      refine he'.2 ⟨w, ?_⟩
      rintro ⟨PP, hPP, hw⟩
      classical
      simp only [Places.W0, Finset.mem_image] at hPP
      obtain ⟨s, hs, rfl⟩ := hPP
      exact hv (by rw [hw, G.pl.under_w hs]; exact hs)
    refine Matrix.ext fun a b => ?_
    rw [Matrix.smul_apply, smul_eq_mul, mul_comm, Matrix.zero_apply]
    exact GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hu a b) hev
  have k1 : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔
      u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) := mem_latO_negSp
  have k2 : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔
      u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) :=
    GlobalTheory.AscFinWit.mem_latO_at (LS := G.Λ (.grid (i + 1) 0)) (LT := G.Λ (.grid i 0)) hu
  exact ⟨fun h => k2.1 (k1.1 h.1), fun h => ⟨k1.2 (k2.2 h), fun e he => by rw [hoff e he]; exact zero_mem _⟩⟩

end GlobalTheory.RowLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdeleConjugatedTopPointEqProdLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

namespace GlobalTheory.TopLevelInv

theorem det_kapAt_val {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
    ((gdet (kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) =
      GlobalTheory.StdFrames.cpt w (toEAf D (mt (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1))))).det) := by
  unfold kapAt GlobalTheory.FunObj.inBasis
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, GlobalTheory.SplitFlip.gdet, GlobalTheory.StepData.det_reGL]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  obtain ⟨X, hX⟩ : ∃ X, X = (MulAut.conj (S.βp (j + 1))⁻¹) ((finG (G.V (.top (j + 1)))) k) := ⟨_, rfl⟩
  rw [← hX]
  refine ((RingHom.map_det (StdFrames.cpt w) X.val).symm : _).trans (congrArg _ ?_)
  rw [hX, MulAut.conj_apply, Units.val_mul, Units.val_mul, det_mul, det_mul, inv_inv, mul_right_comm, ← det_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one, one_mul]
  show ((Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1))))).val).det = _
  rw [GlobalTheory.VecInv.finE_val, RingHom.map_det]
  rfl


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem detAt_conjPt_eq_prod {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {t : T} (_ht : t ∈ U) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1)))
    (e : AE D) (hI : IsIdemSum e (locPl G t)) :
    detAt e (G.V (.top (j + 1))) (conjPt S j k) =
      ∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w)) := by
  classical
  have he2 : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hI).idem
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hI
  have hcomp : ∀ Q, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = if Q ∈ locPl G t then 1 else 0 := by
    intro Q
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := hI
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum (toEAf D), map_sum (GlobalTheory.StdFrames.cpt (D := D) Q)]
    split_ifs with hQ
    · rw [Finset.sum_eq_single Q (fun P hP hPQ => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes P hP)).2 Q (Ne.symm hPQ))
        (fun h => absurd hQ h)]
      exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).1
    · exact Finset.sum_eq_zero fun P hP => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes P hP)).2 Q (fun h => hQ (h ▸ hP))
  have hloc : ∀ (w Q : Pl D.host.E) (y : (Kw w)ˣ),
      GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (GlobalTheory.LFun.locIdele D.host.F w y : AE D)) =
        (Neutral.B1.finiteSingle D.host.E w (y : Kw w)) Q := by
    intro w Q y
    rw [GlobalTheory.DepthFix.cpt_eq_finAd]
    exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y)
  have hdet : (mt (G.V (.top (j + 1))) (conjPt S j k)).det = (mt (G.V (.top (j + 1))) (k : GA D _)).det := by
    unfold Formalism.L2.Theta.mt
    rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
    congr 1
    simp only [conjPt, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [mul_right_comm, inv_mul_cancel, one_mul]
  apply Units.ext
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Units.coe_prod, hdet]
  apply GlobalTheory.FunObj.ae_ext
  · rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hinf, zero_mul, zero_add, sub_zero, map_prod]
    exact (Finset.prod_eq_one fun w _ => GlobalTheory.LFun.infTens_locIdele (F := D.host.F) w.1 _).symm
  · intro Q
    simp only [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, map_prod, hcomp, hloc]
    by_cases hQ : Q ∈ locPl G t
    · rw [if_pos hQ, one_mul, sub_self, add_zero, Finset.prod_eq_single ⟨Q, hQ⟩]
      · rw [GlobalTheory.LFun.finSingle_self, det_kapAt_val]
      · intro b _ hb
        exact GlobalTheory.LFun.finSingle_ne (fun h => hb (Subtype.ext h.symm)) _
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hQ, zero_mul, zero_add, sub_zero]
      exact (Finset.prod_eq_one fun w _ => GlobalTheory.LFun.finSingle_ne (fun h => hQ (by rw [h]; exact w.2)) _).symm

end GlobalTheory.TopLevelInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtSplitPlaceMovedGridNode
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
namespace GlobalTheory.RowDetLocal
variable {D : D7}

theorem toFinAd_eq (z : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    GlobalTheory.LFun.toFinAd D.host.F D.host.E z = GlobalTheory.StdFrames.toAd D (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Algebra.TensorProduct.comm_tmul, GlobalTheory.StdFrames.toAd_spec, mul_comm]
    rfl
  | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

theorem compAt_eq_cpt (w : Pl D.host.E) (a : AE D) :
    GlobalTheory.LFun.compAt D.host.F w (finPart D a) = GlobalTheory.StdFrames.cpt w (toEAf D a) := by
  show (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.E w) (GlobalTheory.LFun.toFinAd D.host.F D.host.E (finPart D a)) = _
  rw [toFinAd_eq]
  rfl

theorem gdet_inBasis_val (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) (k : GfC V) :
    ((gdet (inBasis h β w (finG V k)) : (Kw w)ˣ) : Kw w) =
      GlobalTheory.StdFrames.cpt w (toEAf D (Formalism.L2.Theta.mt V (k : GA D V)).det) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  rw [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, GlobalTheory.TopLevelInv.det_val_reGL, GlobalTheory.TopLevelInv.val_loc, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    GlobalTheory.TopLevelInv.det_val_conj_inv, GlobalTheory.TopLevelInv.val_finG, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem detIdl_eq_locIdele (V : HSp D) (g : GA D V) (w : Pl D.host.E) (hs : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w)
    (z : (Kw w)ˣ) (hz : (z : Kw w) = GlobalTheory.StdFrames.cpt w (toEAf D (Formalism.L2.Theta.mt V g).det)) :
    detIdl (idemAt w) V g = GlobalTheory.LFun.locIdele D.host.F w z := by
  have he : Formalism.L2.NTheta.IsIdemAt (idemAt w) w := Classical.epsilon_spec hs
  have hee : idemAt w * idemAt w = idemAt w := he.1.1
  have hP : Formalism.IndefR.Mult.IsPrimeIdem w (idemAt w) (idemAt w + cA D (idemAt w)) := Or.inl ⟨he, rfl⟩
  have hx := detIdl_val hee V g
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) (detIdl (idemAt w) V g) (by
      rw [hx]
      linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * hee)
  have hyz : y = z := by
    apply Units.ext
    rw [hy, hx, GlobalTheory.WeilAtPlace.compAt_cut (GlobalTheory.LFun.finPart_of_isPrimeIdem hP), compAt_eq_cpt]
    exact hz.symm
  rw [hxy, hyz]

theorem detIdl_conj_eq_locIdele (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (k u : GfC V)
    (w : Pl D.host.E) (hs : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) :
    detIdl (idemAt w) V ((u⁻¹ * k * u : GfC V) : GA D V) =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis h β w (finG V k))) :=
  detIdl_eq_locIdele V _ w hs _ (by rw [gdet_inBasis_val, GlobalTheory.TopLevelInv.det_mt_conj])
end GlobalTheory.RowDetLocal

theorem GlobalTheory.RowDetLocal.detIdl_moved_eq_locIdele : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E),
    (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩)
        (S.B.β (j + 1) D.R.m) w (finG (G.V (.grid (j + 1) D.R.m)) k))) := by
  intro D T L sc G W U S t j hj k w hs
  exact GlobalTheory.RowDetLocal.detIdl_conj_eq_locIdele _ _ _ k (S.N.u (.grid (j + 1) D.R.m)) w hs
end

