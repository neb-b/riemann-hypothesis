module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0940
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesTwistPlacesGoodPosition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftMultiplicitySpacesOfHyp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0905
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0939
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0812
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0826
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import GroundTheory.GlobalFields.TateThesis.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirichletSeriesExponentialSumConverges
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

namespace GlobalTheory.RSNonvan

theorem units_coe_multiset (A : Multiset ℂˣ) :
    (do let a ← A; pure (a : ℂ) : Multiset ℂ) = A.map (fun α : ℂˣ => (α : ℂ)) := by
  show A.bind (fun a => {(a : ℂ)}) = _
  exact Multiset.bind_singleton A _

theorem powSum_conj (B : Multiset ℂ) (r : ℕ) :
    (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum = starRingEnd ℂ ((B.map fun β => β ^ (r + 1)).sum) := by
  rw [map_multiset_sum, Multiset.map_map]
  simp [Function.comp_def, map_pow]

theorem natCast_cpow_eq_exp (q : ℕ) (hq : 1 < q) (r : ℕ) (x : ℝ) :
    (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) = Complex.exp (-((((r : ℝ) + 1) * Real.log q : ℝ) : ℂ) * (x : ℂ)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem four_terms (A B : Multiset ℂ) (q : ℕ) (hq : 1 < q) (r : ℕ) (x : ℝ) :
    (A.map fun α => α ^ (r + 1)).sum * (A.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (B.map fun α => α ^ (r + 1)).sum * (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (A.map fun α => α ^ (r + 1)).sum * (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (B.map fun α => α ^ (r + 1)).sum * (A.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) =
    ((‖((A + B).map (· ^ (r + 1))).sum‖ ^ 2 / ((r : ℝ) + 1) : ℝ) : ℂ) *
      Complex.exp (-((((r : ℝ) + 1) * Real.log q : ℝ) : ℂ) * (x : ℂ)) := by
  rw [powSum_conj A, powSum_conj B, natCast_cpow_eq_exp q hq, Multiset.map_add (f := _), Multiset.sum_add]
  set PA := (A.map fun α => α ^ (r + 1)).sum
  set PB := (B.map fun α => α ^ (r + 1)).sum
  have hn : ((‖PA + PB‖ ^ 2 : ℝ) : ℂ) = (PA + PB) * starRingEnd ℂ (PA + PB) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.ofReal_pow, hn, map_add (f := _)]
  ring

theorem fourProd_eq_exp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a)
    (σ' : CG E b) (hσ : σ.IsUnitary) (hσ' : σ'.IsUnitary) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hT : UnrOutside T σ) (hT' : UnrOutside T σ') (x : ℝ) (hx : 1 < x) :
    ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ =>
        ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧
      (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ' (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1) = Complex.exp g := by
  have L := GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E
  obtain ⟨s1, p1⟩ := L a a σ σ hσ hσ T hT hT x hx
  obtain ⟨s2, p2⟩ := L b b σ' σ' hσ' hσ' T hT' hT' x hx
  obtain ⟨s3, p3⟩ := L a b σ σ' hσ hσ' T hT hT' x hx
  obtain ⟨s4, p4⟩ := L b a σ' σ hσ' hσ T hT' hT x hx
  have h := (((s1.of_norm.hasSum.add s2.of_norm.hasSum).add s3.of_norm.hasSum).add s4.of_norm.hasSum)
  refine ⟨?g, ?hs, ?hp⟩
  case hp =>
    simp only [lfac]
    rw [p1.tprod_eq, p2.tprod_eq, p3.tprod_eq, p4.tprod_eq, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
  case hs =>
    refine (congrArg (fun f => HasSum f _) (funext fun p => ?_)).mpr h
    simp only [Pi.add_apply, units_coe_multiset]
    rw [four_terms _ _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1)]
    rfl

end GlobalTheory.RSNonvan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodBase
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist.BaseInhab

open GlobalTheory.ExportSeries

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (n : ℕ) (hn : 0 < n) :
    ChrEq (c ^ n) (χ ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using h
  | succ n _ ih => rw [pow_succ, pow_succ]; exact GlobalTheory.TowerCharRead.chrEq_mul ih h

end GlobalTheory.ConjTwist.BaseInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBaseDataIsGoodTwist
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.BaseGood

theorem base_good : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ (j : Fin D.R.m) (F : Frame (Vc D j) (Wc D j)) (hF : F.Good) (de : Twist D Circle), de.Good → PlacesOK Rl.Pg de.Q → ∃ (w : Weight D (Vc D j).rank) (mu : ResChars D Circle), (∀ τ, w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) ∧ (∀ τ, w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) ∧ ∀ P : LevelP Rl.Pg (Wc D j).rank ℂ, (⟨hF.rank_le, F, ⟨Rl.Pg, P, mu⟩, de, w, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩ : Base (Vc D j) (Wc D j)).Good := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC j F hF de hde hpl
  have hL := hC.lev
  have hS : SplitSet Rl.Pg := by
    obtain ⟨P, h1, -, hP⟩ := hpl.split
    exact hP.mono h1
  have hr : Odd D.R.r := Formalism.L2.NTheta.odd_r D.R
  have rV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  obtain ⟨Pa, hPa1, hPa2, hPa⟩ := hpl.split
  refine ⟨GlobalTheory.ConjTwist.liftWeight D j, fun PP => GlobalTheory.ConjTwist.toCircle (Rl.chi ((j : ℕ) + 1) PP)⁻¹,
    fun _ => rfl, fun _ => rfl, fun P => ?_⟩
  exact
    { even := rV ▸ hr.add_odd D.R.t_odd
      odd := rW ▸ hr
      frame := hF
      de := hde
      places := hpl
      wt := GlobalTheory.ConjTwist.liftWeight_good D j
      sig := fun _ => rfl
      sigOK := D.sp.W_sig _
      eta := GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq D Rl.C Rl.eta hL.eta (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL)
      hecke := (hL.mu0 j).1
      real := GlobalTheory.GridWeil.triv_base (hL.mu0 j) (Rl.C.isMu0 j).triv
      unram := _root_.GlobalTheory.TypePlaceUnram.unramOutside_mu0_of_splitSet D _ _ _ hL hS j
      tame := fun PP hPP x hx hi u hu => by
        have e1 := GlobalTheory.ConjTwist.eq_res_of_chrEq (hL.mu0 j) (hS.isIdemAt hPP) ((Rl.C.isMu0 j).tame PP) (hL.chi j PP hPP) x hx hi u hu
        have e2 := _root_.GlobalTheory.ConjTwist.isResAt_one_of_unram D Circle de.chi de.Q Pa hde.unram hPa hPa2 PP (hPa1 hPP)
          (Finset.disjoint_left.1 hpl.disj hPP) x hx hi u hu
        show Rl.mu0 ((j : ℕ) + 1) x * de.chi x = GlobalTheory.ConjTwist.toCircle (Rl.chi ((j : ℕ) + 1) PP)⁻¹ u
        rw [e2, MonoidHom.one_apply, mul_one]
        exact Circle.ext e1
      inf := fun τ => by
        have e : ((GlobalTheory.ConjTwist.liftWeight D j).c τ : ℚ) - (((GlobalTheory.ConjTwist.liftWeight D j).p τ : ℚ) -
            (GlobalTheory.ConjTwist.liftWeight D j).q τ) / 2 + 1 / 2 = -(D.hc τ).e j := by
          have h := GlobalTheory.ConjTwist.liftC_cast D j τ
          simp only [GlobalTheory.ConjTwist.liftWeight]
          linarith
        rw [e]
        exact GlobalTheory.ConjRefChar.reference_lift_character_exponent_neg_base hL j τ }

end GlobalTheory.SeriesTie.BaseGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelsWith
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 4000000 in
theorem models_with (h : R.IsModels) (ioY ioX Th thF thG) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th, thF := thF, thG := thG } : RealDat D A Ks).IsModels :=
  ⟨h.inf, h.vpos, h.cX, h.cV, h.prX, h.HX, h.HV, h.HE, h.HW, h.gE, h.gW, h.jX, h.jV, h.νY, h.νY', h.ν0, h.νX, h.νV, h.νW, h.BV,
    h.order⟩

set_option maxHeartbeats 4000000 in
theorem fam_with (h : R.IsFam) (ioY ioX Th thF thG) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th, thF := thF, thG := thG } : RealDat D A Ks).IsFam :=
  ⟨h.tie, h.Sb, h.roots, h.pl_onto, h.degR, h.degL, h.muVal, h.etaVal⟩

theorem chain_with (hωY : R.chain_ωY) (hωX : R.chain_ωX) (hvY : R.chain_vY) (hvX : R.chain_vX) (a : R.chain_ptY)
    (b : R.chain_ptX) (c : R.chain_ItY) (d : R.chain_ItX) (ioY ioX Th) (e : ({ R with ioY := ioY } : RealDat D A Ks).chain_ioY)
    (f : ({ R with ioX := ioX } : RealDat D A Ks).chain_ioX)
    (g : ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).chain_Th) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).IsChain :=
  ⟨hωY, hωX, hvY, hvX, a, b, c, d, e, f, g⟩

theorem exists_th (hL : R.toLevCh.Is A.μ0) (hr : R.grp_record) (hF : R.IsFam) (hM : R.IsModels) (ioY ioX) :
    ∃ Th, ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).chain_Th :=
  GlobalTheory.ProjectedLift.exists_chain_Th D G Pl0 T A Ks { R with ioY := ioY, ioX := ioX } hL
    (fam_with hF ioY ioX R.Th R.thF R.thG) (models_with hM ioY ioX R.Th R.thF R.thG) hr


set_option maxHeartbeats 800000 in
theorem exists_chain (h₁ : GlobalTheory.Published.DiscreteSeriesCover) (h₂ : GlobalTheory.Published.HarishChandraModules) (h₃ : GlobalTheory.Published.CuspRapidDecay)
    (h₄ : GlobalTheory.Published.CasselmanWallach) (hP : ∀ k, GlobalTheory.Chain.ChainPar D k) (hL : R.toLevCh.Is A.μ0) (hr : R.grp_record)
    (hF : R.IsFam) (hM : R.IsModels) (hωY : R.chain_ωY) (hωX : R.chain_ωX) (hvY : R.chain_vY) (hvX : R.chain_vX) (t₀ : T)
    (hY : ∀ k, k + 1 < D.R.m → IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t₀ k) (R.ptY t₀ k) (R.ItY k))
    (hX : IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t₀) (R.ptX t₀) R.ItX) :
    ∃ ioY ioX Th, ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).IsChain := by
  have hS := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  have hW := _root_.GlobalTheory.Chain.SourceLaw.lawsOK D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  have hIY : R.chain_ItY := fun t k hk =>
    GlobalTheory.Chain.ItAllTuples.pItY_of_one h₁ h₂ D G Pl0 T A Ks R hP hL hM hωY hωX hvY hvX k hk t₀ _ (hY k hk) t
  have hIX : R.chain_ItX := _root_.GlobalTheory.IntertwinerTransfer.pItX_of_one D G Pl0 T A Ks R hL hM hωX hvX t₀ _ hX
  have hpY : R.chain_ptY := fun t k hk P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO (hωY t k hk).std hM.inf _ _ _ _ (hS.1 t ⟨k, by omega⟩ hk).2.theta P
  have hpX : R.chain_ptX := (GlobalTheory.T.definite_lastStep_real_intertwiner D G Pl0 T A Ks R hL hF hM hωX hvX).1
  exact (GlobalTheory.Chain.InnerLift.exists_ioY_of_pair R (_root_.GlobalTheory.Chain.IoLift.ioPair_onObjects h₁ h₂ h₃ h₄ D) hP hS.1 hW.1 hM hIY).elim fun ioY hioY =>
    (GlobalTheory.T.exists_multiplicityLift_lastChainStep D G Pl0 T A Ks R hL hF hM hωX hvX hpX hIX).elim fun ioX hioX =>
    (exists_th hL hr hF hM ioY ioX).elim fun Th hTh =>
    ⟨ioY, ioX, Th, chain_with hωY hωX hvY hvX hpY hpX hIY hIX ioY ioX Th hioY hioX hTh⟩


set_option maxHeartbeats 4000000 in
theorem exists_thP (h₃ : GlobalTheory.Published.CuspRapidDecay) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (hM : R.IsModels) (hω : R.thP_ωP)
    (hv : R.thP_vP) (t₀ : T)
    (hI : ∀ i, IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t₀) (R.ptP i t₀) (RealDat.Delta i) (R.ioP i)) :
    ∃ thF thG, ({ R with thF := thF, thG := thG } : RealDat D A Ks).IsThP := by
  have hp : R.thP_pt_theta := (GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors D G Pl0 T A Ks R hL hF hM hω hv).1
  have hio : R.thP_ioP := fun i => GlobalTheory.IoAllTuples.ioP_of_isIoW_at D G Pl0 T A Ks R hL hF hM hω hv i t₀ _ (hI i)
  obtain ⟨thF, h1, h2⟩ := GlobalTheory.T.exists_thetaLift_linearMap_cuspFormMultiplicity h₃ D G Pl0 T A Ks R hL hF hM hω hv hp hio
  obtain ⟨thG, h3⟩ := GlobalTheory.GoodProjLift.exists_thG D G Pl0 T A Ks { R with thF := thF } hL
    (fam_with hF R.ioY R.ioX R.Th thF R.thG) (models_with hM R.ioY R.ioX R.Th thF R.thG) h1
  exact ⟨thF, thG, hω, hv, hp, hio, h1, h2, h3⟩

end GlobalTheory.ConjExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergSameDegreeMeromorphicContinuation
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.UnitaryBC
  GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.RSNonvan
open scoped nonZeroDivisors

theorem logNorm_eq_log_ideleModule (E : Type) [Field E] [NumberField E] (d : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) :=
  GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule E d

theorem natLat_iff (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : 0 < N) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (z : FiniteAdeleRing (𝓞 E) E) :
    z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J :=
  GlobalTheory.T.mem_natMultipleIntegralFiniteAdeles_iff_idealFiniteAdeles E N hN J hJ z

namespace GlobalTheory.RSNonvan

theorem detPow_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (x : ℝ) (g : GA E a) :
    GlobalTheory.RSJ.detPow E a x g = ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) := by
  have hpos := (ideleModule E (GeneralLinearGroup.det g)).2
  rw [Real.rpow_def_of_pos hpos, ← logNorm_eq_log_ideleModule]
  simp only [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, MonoidHom.coe_comp, Function.comp_apply]
  change ‖Complex.exp ((x : ℂ) * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det g) : ℂ))‖ = _
  rw [Complex.norm_exp]
  congr 1
  simp [mul_comm]

theorem secInv_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (hℓ : (ℓ : ℕ) + 1 = a)
    (u : Fin a → Cinf E) : GlobalTheory.RSJ.secInv u = (GlobalTheory.RSTheta.rowGL ℓ u)⁻¹ := by
  have hrow : GlobalTheory.RSJ.secRow u = GlobalTheory.RSTheta.rowMat ℓ u := by
    ext i j
    simp only [GlobalTheory.RSJ.secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
    have : ((i : ℕ) + 1 = a) ↔ i = ℓ := by
      constructor
      · intro h; exact Fin.ext (by omega)
      · intro h; subst h; exact hℓ
    by_cases h : i = ℓ
    · simp [h, hℓ]
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
  unfold GlobalTheory.RSJ.secInv
  by_cases hu : IsUnit (u ℓ)
  · have hd : IsUnit (GlobalTheory.RSJ.secRow u).det := by rw [hrow, GlobalTheory.RSTheta.det_rowMat]; exact hu
    rw [dite_eq_left hd]
    congr 1
    ext : 1
    rw [GlobalTheory.RSTheta.val_rowGL hu, ← hrow]
    rfl
  · have hd : ¬ IsUnit (GlobalTheory.RSJ.secRow u).det := by rw [hrow, GlobalTheory.RSTheta.det_rowMat]; exact hu
    rw [dite_eq_right hd, GlobalTheory.RSTheta.rowGL, dite_eq_right hu, inv_one]

theorem indN_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (N : ℕ) (hN : 0 < N) (ℓ : Fin a)
    (hℓ : (ℓ : ℕ) + 1 = a) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (v : Fin a → Af E) :
    GlobalTheory.RSJ.indN N v = (GlobalTheory.ThetaPoisson.latt a J).indicator 1 (v - Pi.single ℓ 1) := by
  have key : (∀ i : Fin a, v i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N) ↔
      v - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J := by
    simp only [GlobalTheory.ThetaPoisson.latt, Set.mem_setOf_eq, Pi.sub_apply]
    refine forall_congr' fun i => ?_
    have e : (if (i : ℕ) + 1 = a then (1 : Af E) else 0) = (Pi.single ℓ (1 : Af E) : Fin a → Af E) i := by
      by_cases h : i = ℓ
      · subst h; simp [hℓ]
      · have : ¬ ((i : ℕ) + 1 = a) := fun h' => h (Fin.ext (by omega))
        simp [this, h]
    rw [e, natLat_iff E N hN J hJ]
  unfold GlobalTheory.RSJ.indN
  by_cases h : ∀ i : Fin a, v i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N
  · rw [if_pos h, Set.indicator_of_mem (key.1 h)]; rfl
  · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (key.2 h'))]

theorem zint_eq_thetaZ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a))
    (𝓕 : Set (GA E a)) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (hN : 0 < N) (ℓ : Fin a)
    (hℓ : (ℓ : ℕ) + 1 = a) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (x : ℝ) :
    GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ φ' Φ J (Pi.single ℓ 1) x := by
  unfold GlobalTheory.RSJ.Zint GlobalTheory.RSPole.thetaZ
  congr 1
  funext g
  rw [detPow_eq]
  congr 1
  unfold GlobalTheory.RSJ.thetaSum
  refine tsum_congr fun ξ => ?_
  simp only [GlobalTheory.RSJ.Psi, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, GlobalTheory.RSJ.rowAct, secInv_eq ℓ hℓ, map_inv]
  rw [indN_eq N hN ℓ hℓ J hJ]
  rfl

open GlobalTheory.CuspRep.CuspidalL2GL in
theorem haarFD (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (latticeGL E a) 𝓕' μ := by
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
  obtain ⟨𝓕', -, -, h𝓕'⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (latticeGL E a)
  exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕', h𝓕 _, h𝓕' _⟩

theorem samedeg_continuation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), IsGood T → UnrOutside T σ → UnrOutside T σ' → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (σ ≠ σ' → F 1 = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => lfac σ σ' (x : ℂ) w.1) (F x / ((x : ℂ) - 1)) := by
  intro E _ _ _ a σ σ' ha hσ hσ' T hT hu hu'
  obtain ⟨N, Φ, π, π', φ, φ', hπ, hπ', hφ, hφ', -, -, hN, hΦc, hΦs, hΦr, hZ'⟩ := GlobalTheory.T.unfoldedThetaIntegral_eq_mul_partialRankinSelbergL E a σ σ' ha hσ hσ' T hT.1 hT.2 hu hu'
  obtain ⟨μ, hμ, 𝓕, 𝓕', h𝓕, h𝓕'⟩ := haarFD E a
  obtain ⟨H, hHd, hHpos, hZH⟩ := hZ' μ 𝓕 h𝓕
  obtain ⟨ω, hωu, hω⟩ := id hσ
  obtain ⟨ω', hωu', hω'⟩ := id hσ'
  rw [← hπ] at hω
  rw [← hπ'] at hω'
  rw [CG.hasCentChar_mk] at hω hω'
  set ℓ : Fin a := ⟨a - 1, by omega⟩ with hℓdef
  have hℓ : (ℓ : ℕ) + 1 = a := by simp [ℓ]; omega
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  set J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E))
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 hN0) with hJdef
  have hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) := rfl
  have hπu : π.IsUnitary := ⟨ω, hωu, CuspSub.hasCentral_iff.2 hω⟩
  have hπu' : π'.IsUnitary := ⟨ω', hωu', CuspSub.hasCentral_iff.2 hω'⟩
  obtain ⟨φs, -, hφs⟩ := GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπu hφ
  obtain ⟨φs', -, hφs'⟩ := GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπu' hφ'
  have hφs1 : φs.1 = φ := hφs
  have hφs1' : φs'.1 = φ' := hφs'
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.thetaIntegral_continuation_nearRealHalfLine_poleOne E a ℓ Φ hΦc hΦs (hΦr ℓ hℓ) J (Pi.single ℓ 1) μ 𝓕 𝓕' h𝓕 h𝓕'
  obtain ⟨Fz, hFa, hFx, hF1, hF1'⟩ := hc π π' ω ω' hωu hωu' hω hω' φs φs'
    (Or.inr (hφs1 ▸ hφ)) (Or.inr (hφs1' ▸ hφ'))
  have hH0 : ∀ x : ℝ, H x ≠ 0 := fun x h => by
    have := (hHpos x).1
    rw [h] at this
    simp at this
  refine ⟨fun s => Fz s / H s, fun x hx => (hFa x hx).div (hHd.analyticAt _) (hH0 x), fun hne => ?_, fun x hx => ?_⟩
  · have h1 : Fz 1 = 0 := by
      by_cases hωω : ω = ω'
      · subst hωω
        rw [hF1 rfl]
        have hne' : CG.mk π ≠ CG.mk π' := by rw [hπ, hπ']; exact hne
        have h0 := fun φ hφ φ'' hφ'' =>
          GlobalTheory.CuspOrth.pet_eq_zero_of_ne_of_hasCentChar E a μ π π' ω hωu hω hω' hne' φ hφ φ'' hφ''
        rw [GlobalTheory.MspanROrth.setIntegral_mspanR_eq_zero E a ha π π' ω hωu hω hω' μ h0 𝓕' h𝓕' φs.1
          (hφs1 ▸ hφ) φs'.1 (hφs1' ▸ hφ'), mul_zero]
      · exact hF1' hωω
    simp [h1]
  · obtain ⟨-, hprod⟩ := (GlobalTheory.T.localRankinSelberg_logarithm_formula).2 E a a σ σ' hσ hσ' T hu hu' x hx
    have hx1 : (x : ℂ) - 1 ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hx.ne'
    have e : Fz x / H x / ((x : ℂ) - 1) = ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1 := by
      rw [hFx x hx]
      have h2 := (hZH x hx).1
      rw [zint_eq_thetaZ μ 𝓕 φ φ' Φ N hN ℓ hℓ J hJ x] at h2
      simp only [GlobalTheory.RSPole.thetaZ] at h2
      rw [hφs1, hφs1', h2]
      simp only [lfac]
      have := hH0 x
      push_cast
      field_simp
    change HasProd _ (Fz x / H x / ((x : ℂ) - 1))
    rw [e]
    exact hprod.tprod_eq ▸ hprod

end GlobalTheory.RSNonvan
end

