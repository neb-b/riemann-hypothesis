module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Formalism.LocalToGlobal.AlgebraicTheory.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.PrvFOfOrbitLetterBounds
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeriesStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_orbit_series : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (σ : MaximalUnramifiedExtension Lc.l →+* MaximalUnramifiedExtension Lc.l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension Lc.l)) (om oms : Fin (Lc.d / 2) → MaximalUnramifiedExtension Lc.l) (ζ : MaximalUnramifiedExtension Lc.l), BeData Lc.l Lc.d σ F be0 om oms ζ → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) (beOf Lc.l Lc.d σ be0 om oms ζ) → ∃ U0 : MvPowerSeries (Bool × Fin (Lc.d / 2) × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l], Formalism.DworkPowerSeriesWeights.Integral U0 ∧ (MvPowerSeries.subst (fun v : ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1 => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l])) Lc.Th : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l]) = thetaInZ (d := Lc.d) Lc.l (MaximalUnramifiedExtension Lc.l).subtype σ om oms (Formalism.DworkPowerSeriesWeights.mvExp (-(sumE (MvPowerSeries.map (MaximalUnramifiedExtension Lc.l).subtype be0))) * U0) := by
  first | exact @GlobalTheory.KerStd.integral_cofactor_converse | exact GlobalTheory.KerStd.integral_cofactor_converse | (intros; apply GlobalTheory.KerStd.integral_cofactor_converse <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpSNegSumBivariatePairIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OrbitPair

open MvPowerSeries

theorem expS_neg_sum_bivariate_pair_integral : ∀ {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} [NeZero n'] (om om' : Fin (n' / 2) → ℂ_[p]) (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p]) (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), MvPowerSeries.constantCoeff b0 = 0 → MvPowerSeries.constantCoeff bv = 0 → (∀ s, MvPowerSeries.constantCoeff (t s) = 0) → (∀ r, Formalism.MainNotions.GL3Theta.IntegralW (x r) ∧ MvPowerSeries.constantCoeff (x r) = 0) → (∀ s, MvPowerSeries.subst t (GlobalTheory.ThStr.laS p n' s) = GlobalTheory.ThBe0.zOm σ om om' s) → (∀ s, MvPowerSeries.subst x (t s) = MvPowerSeries.X s) → Formalism.MainNotions.GL3Theta.SimeqW (MvPowerSeries.subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv) (∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r))) → ∃ V : MvPowerSeries (ZMod n') ℂ_[p], Formalism.MainNotions.GL3Theta.IntegralW V ∧ product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(MvPowerSeries.subst (GlobalTheory.ThStr.laS p n') bv)) := by
  intro p _ σ n' _ om om' b0 bv t x _hb0 hbv ht hx hlaS htx hsim
  classical
  have hxS : HasSubst x := hasSubst_of_constantCoeff_zero fun r => (hx r).2
  have htS : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have hzcc : ∀ s : ZMod n', constantCoeff (GlobalTheory.ThBe0.zOm (d := n') σ om om' s) = 0 := by
    intro s
    rw [← hlaS s]
    exact constantCoeff_subst_eq_zero htS ht (GlobalTheory.BeProps.constantCoeff_laS s)
  have hzS : HasSubst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) := hasSubst_of_constantCoeff_zero hzcc
  have hzOm : ∀ s : ZMod n', subst x (GlobalTheory.ThBe0.zOm (d := n') σ om om' s) = GlobalTheory.ThStr.laS p n' s := by
    intro s
    rw [← hlaS s, subst_comp_subst_apply htS hxS]
    have : (fun r => subst x (t r)) = (X : ZMod n' → MvPowerSeries (ZMod n') ℂ_[p]) := funext htx
    rw [this, subst_self]
    rfl
  have hFx : subst x (subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv) = subst (GlobalTheory.ThStr.laS p n') bv := by
    rw [subst_comp_subst_apply hzS hxS]
    congr 1
    funext s
    exact hzOm s
  have hGx : subst x (∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r))) =
      ∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← coe_substAlgHom hxS, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [coe_substAlgHom hxS, GlobalTheory.ThBe0.Inhab.subst_powerSeriesEvalTwoGroups hxS (GlobalTheory.ThBe0.Inhab.cc_lg _) (GlobalTheory.ThBe0.Inhab.cc_lg _)]
    simp only [GlobalTheory.ThBe0.lg]
    rw [GlobalTheory.ThBe0.Inhab.subst_psubst hxS (constantCoeff_X _), GlobalTheory.ThBe0.Inhab.subst_psubst hxS (constantCoeff_X _),
      subst_X hxS, subst_X hxS]
  obtain ⟨hD0, hDint⟩ := hsim
  set F := subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv with hF
  set G := ∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r)) with hG
  have ccL : constantCoeff (subst (GlobalTheory.ThStr.laS p n') bv) = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun s => GlobalTheory.BeProps.constantCoeff_laS s)
      (fun s => GlobalTheory.BeProps.constantCoeff_laS s) hbv
  have ccD : constantCoeff (subst x (F - G)) = 0 := constantCoeff_subst_eq_zero hxS (fun r => (hx r).2) hD0
  have hneg : -(subst x G) = subst x (F - G) + -(subst (GlobalTheory.ThStr.laS p n') bv) := by
    rw [subst_sub hxS, hFx]
    ring
  refine ⟨subst x (Formalism.MainNotions.TaylorLogMetric.expMv (F - G)), ?_, ?_⟩
  · exact GlobalTheory.SubringSeries.subst_mem (A := Formalism.MainNotions.GL3Theta.Wp p) hxS (fun r => (hx r).1) hDint
  · rw [← hGx, hneg]
    show PowerSeries.subst _ (PowerSeries.exp ℂ_[p]) = _ * PowerSeries.subst _ (PowerSeries.exp ℂ_[p])
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add ccD (by rw [map_neg, ccL, neg_zero]), GlobalTheory.BeProps.expMv_eq_subst hD0,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp x (fun r => (hx r).2) hD0]

end GlobalTheory.OrbitPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisRepQbarConjugateUnique
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.RepConjUniq

theorem main : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ' → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm := by
  intro D hAN i x ρ ρ' h1 h2
  obtain ⟨-, -, hCheb, hBN⟩ := hAN
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin : (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪ (D.nd.Q i : Set _)).Finite :=
    ((Formalism.MainNotions.SumRepresentations.placesOver_finite D.host.E (D.nd.l i) hl.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have hdense := hCheb _ hfin
  have hfrob : ∀ g ∈ {σ : G D.host.E D.nd.Om | ∃ w ∉ (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪
      (D.nd.Q i : Set _)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ},
      ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly := by
    rintro σ ⟨w, hw, hsp, B, hB', hσ⟩
    simp only [Set.mem_union, not_or] at hw
    obtain ⟨⟨hwl, hwS⟩, hwQ⟩ := hw
    replace hwS : w ∉ D.nd.S i := by simpa using hwS
    replace hwQ : w ∉ D.nd.Q i := by simpa using hwQ
    have hso : SplitOut D.nd i w := ⟨hsp, hwl, hwS, hwQ⟩
    rw [h1.2.2 w hso B σ hB' hσ, h2.2.2 w hso B σ hB' hσ]
  have hall := GlobalTheory.BaseChangeConj.charpoly_eq_of_dense' ρ ρ' h1.1 h2.1 _ hdense hfrob
  exact hBN _ _ ρ ρ' h1.2.1 h2.2.1 hall

end GlobalTheory.RepConjUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsCoefficientExtension
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec


open Classical in
theorem hodgeTateJumps_coefficientExtension : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → ∃ (ε : ℤˣ) (κ : D.host.E →+* ↥Cx.LL.1), JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) := by
  intro D L C₀ i r ρ π w hw Cx hR h7 hF hJ hP
  obtain ⟨ep, hep⟩ := hJ
  let C : Enl D i w hw := ⟨Cx.LL, Cx.inc⟩
  have hτ₀ : Nonempty (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1) :=
    ⟨((D.nbr i w hw).Kw.1.val).codRestrict Cx.LL.1.toSubalgebra
      (fun x => Cx.le ((D.nbr i w hw).LL_split (D.nbr i w hw).Kw.1.val x))⟩
  obtain ⟨τ₀⟩ := hτ₀
  obtain ⟨g₀, ρ₀, hr₀, -⟩ := hep i r hP.good w hw Cx τ₀
  obtain ⟨κ, hκ⟩ := exists_base_reads D.host (D.nbr i w hw).Kw Cx.LL (Br.cEw D.nbr i w hw)
    (D.naut.iotaQC i) τ₀ g₀ hr₀.1
  refine ⟨if ep then 1 else -1, κ, ?_⟩

  have hc : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), (Continuous fun g => M g) →
      Continuous (TruncatedSeriesCountingIdentities.locC Cx M) := by
    intro k M hM
    refine continuous_matrix fun a b => ?_
    have h1 := locC_cont D i M hM w hw Cx (Pi.single b 1)
    have h2 := (continuous_apply a).comp h1
    simpa [Function.comp_def, Matrix.mulVec_single] using h2
  have hW : Continuous fun g => WpO D.nd i ρ π g := by
    have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
      have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
          fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
        funext g
        rw [map_inv]
        rfl
      rw [e]
      exact (D.nd.chi_cont i 1).comp continuous_inv
    exact h1.smul hP.contρ
  refine GlobalTheory.T.jumps_of_crystalline_twist_block_decomposition L C₀ i w hw C r ρ π _ κ hR h7 (hF i w hw Cx).2.2.1
    (fun z => (IntermediateField.inclusion Cx.le).commutes z)
    (fun x => hc _ (rTwO_cont D i r hP.cont x)) (hc _ hW) (fun x => hP.crys w hw Cx x) hP.dec ?_
  intro τ
  obtain ⟨g, ρ', hrd, hx, hπ⟩ := hep i r hP.good w hw Cx τ
  have hup : (decide (LJ.TypeU D ep g) = true ↔ LJ.TypeU D ep g) := decide_eq_true_iff
  have hs := _root_.GlobalTheory.HTW.Rec.rat_jump_sets_eq_int_multisets D i ρ' g ep _ hrd.2 hup
  refine ⟨g, hκ τ g hrd.1, ?_, ?_⟩
  · intro x a ha
    exact ((hs a).1).1 (((hx x a).2.2.1).1 ha)
  · intro a
    refine ((hπ ρ π hP.mem hP.dec a).2.2.2).trans ?_
    by_cases h : a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep = true then 1 else -1) g)
    · rw [if_pos ((hs a).2.2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hs a).2.1 h')), if_neg h]

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalizationIntegralScalar
section
namespace GlobalTheory

open Formalism.L2.AlgTh

theorem tensorFourthPower_smul {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) (θ : (n → ℂ) → ℂ) :
    Formalism.L2.Th1.H.tens4 (c • θ) = c ^ 4 • Formalism.L2.Th1.H.tens4 θ := by
  funext z
  simp only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem locNormScale : LocNormScale := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hLN
  obtain ⟨g₁, ε, hiso, hp, hidx, hε, heq⟩ := hLN
  refine ⟨g₁, c ^ 4 * ε, hiso, hp, hidx, ?_, ?_⟩
  · rw [map_mul, map_pow, norm_mul, norm_pow]
    have h0 : 0 ≤ ‖ι c‖ := norm_nonneg _
    have h4 : ‖ι c‖ ^ 4 ≤ 1 := pow_le_one₀ h0 hc
    calc ‖ι c‖ ^ 4 * ‖ι ε‖ ≤ 1 * 1 := mul_le_mul h4 hε (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [tensorFourthPower_smul, heq, smul_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundOverSecondEmbeddingAnyBasePoint
section
noncomputable section

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical Formalism.MainNotions.OrbitPlaces PI.OrbBoundFW

namespace GlobalTheory.TwU

theorem orbitBound_overSecondEmbedding_anyBasePoint_alt : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D) (C6 C : ℝ), OrbitPlaces.OrbitLetterBoundsAll C6 C → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ (t : HH D) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) → product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be → OrbitPlaces.OrbGe E p h u i (true, t) ep sg be (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  intro D L X K ce E C6 C hA hS hC p _ h _hc0 _hP hp u i hi t ep sg be hep hsg h1 h2 h3 h4 Th hB0
  have hAdm := admissible_of_jet_bounds h u i (true, t) Th ep sg be hep hsg h1 h2 h3 h4 hB0
  have hCor := (hA.1 _ hAdm).2 (L.sc.a ^ 2) (setting_sq hS h hp u hi (true, t) Th) D.R.k (wOrb D p i (true, t))
    (eOrb E p u i (true, t)) (three_le_k D) (wOrb_pos hS p hi (true, t)) (eOrb_bounds hS p u hi (true, t))
    (dl_off h u i (true, t) Th) (dl_on h u i (true, t) Th)
  refine kvalGe_mono hCor ?_
  have hg : 0 ≤ ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, (orbLoc E p h u i (true, t) Th).baseTerm s :=
    Finset.sum_nonneg fun s _ => orbit_local_term_nonneg _ s
  have hw := sum_Wc_le hS h u hi (true, t) Th
  have hl := loss_le hS hC h hp hi (true, t)
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five
  have hgam : Formalism.MainNotions.product_zeroth_first_parts.gam p = Formalism.MainNotions.G.gam p := rfl
  have hgpos : 0 ≤ Formalism.MainNotions.G.gam p := by
    unfold Formalism.MainNotions.G.gam
    apply div_nonneg (by linarith)
    nlinarith
  have hsw : 0 ≤ ∑ s, wOrb D p i (true, t) s := Finset.sum_nonneg fun s _ => (wOrb_pos hS p hi (true, t) s).le
  have hc6 : C6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) ≤ ce.c6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_right hC.c6 hsw
  have hgw : Formalism.MainNotions.G.gam p * ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, ((orbLoc E p h u i (true, t) Th).Wc s : ℝ) ≤
      Formalism.MainNotions.G.gam p * (topsOrb D p (true, t) : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw hgpos
  have hi1 : i + 1 - 1 = i := by omega
  rw [hi1] at hl
  have hF : FOrb D (i + 1) p (true, t) = lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i (true, t) s) := rfl
  have hE : errF L K ce (i + 1) p (true, t) = Formalism.MainNotions.G.gam p * (topsOrb D p (true, t) : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
      ce.c6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) +
      ((nP D p : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
          (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
        (K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
          K.dl2 * (topsOrb D p (true, t) : ℝ) * Real.logb p (2 * L.sc.a) ^ 2)) := by
    unfold errF; simp only [wOrb]; ring
  rw [hi1] at hE
  show FOrb D (i + 1) p (true, t) - errF L K ce (i + 1) p (true, t) ≤
    (∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, (orbLoc E p h u i (true, t) Th).baseTerm s +
      lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i (true, t) s)) - C6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) -
      Formalism.MainNotions.product_zeroth_first_parts.gam p * ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, ((orbLoc E p h u i (true, t) Th).Wc s : ℝ) -
      C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1))
  rw [hF, hE, hgam]
  linarith

end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartnerPlaceInvolutiveNormConjEq
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

theorem eTau_tauSg (D : D7) (τ : D.what₂.Tau) :
    ((D.eTau (tauSg D τ) : D.R.Psi) : D.R.GG) =
      (D.eTau τ : D.R.GG) * sgm D := by
  have h : (D.eTau τ : D.R.GG) * sgm D ∈ D.R.Psi := by
    rw [Formalism.HC.Frame.mem_Psi_iff]
    have := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2
    simp [sgm, this]
  unfold tauSg
  rw [dite_eq_left h, Equiv.apply_symm_apply]

theorem sgm_mul_sgm (D : D7) : sgm D * sgm D = 1 := by
  simp [sgm, Prod.ext_iff]

theorem sgm_ne_one (D : D7) : sgm D ≠ 1 := by
  intro h
  have : (((sgm D).1.1 : ℤˣ) : ℤ) = 1 := by rw [h]; rfl
  simp [sgm] at this

theorem sgm_mul_cc (D : D7) : sgm D * D.R.cc = ((1, -1), 1) := by
  simp [sgm, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, Prod.ext_iff]

theorem tauSg_invol_norm_conj_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p = D.host.d →
    ∀ (τ : D.what₂.Tau), tauSg D (tauSg D τ) = τ ∧ tauSg D τ ≠ τ ∧
      ∀ y : D.host.E, ‖tauEmb D lam (tauSg D τ) (D.host.conj y)‖ = ‖tauEmb D lam τ y‖ := by
  intro D p _ lam hp τ
  subst hp
  refine ⟨?_, ?_, ?_⟩
  · apply D.eTau.injective
    apply Subtype.ext
    rw [eTau_tauSg, eTau_tauSg, mul_assoc, sgm_mul_sgm, mul_one]
  · intro h
    have h1 := congrArg (fun t => ((D.eTau t : D.R.Psi) : D.R.GG)) h
    simp only [eTau_tauSg] at h1
    exact sgm_ne_one D (mul_eq_left.mp h1)
  · intro y
    set g : D.R.GG := (D.eTau τ : D.R.GG) with hg
    let σ : D.host.E ≃ₐ[ℚ] D.host.E := D.host.sigmaOf ((1, -1), 1)
    have hgσ : D.host.galE σ = ((1, -1), 1) := by
      change D.host.galE
        ((D.host.gal).symm ((1, -1), 1)) = _
      exact D.host.gal.apply_symm_apply _
    have hemb : embT D (tauSg D τ) (D.host.conj y) = embT D τ (σ y) := by
      change D.host.emb _ (D.host.conj y) = D.host.emb g (σ y)
      rw [eTau_tauSg, ← hg]
      have e1 := emb_mul_galE D.host (g * sgm D) D.host.conj y
      have e2 := emb_mul_galE D.host g σ y
      have hc : D.host.galE D.host.conj = D.R.cc :=
        D.host.galE_conjE
      rw [hc] at e1
      rw [hgσ] at e2
      rw [← e1, ← e2, mul_assoc, sgm_mul_cc]
    have hsp : SamePrime (rhoH D lam τ) ((rhoH D lam τ).comp (σ : D.host.E →+* D.host.E)) := by
      intro a
      have hPp := primeOf_isPrime (rhoH D lam τ)
      have hd : (D.host.d : 𝓞 D.host.E) ∈ primeOf (rhoH D lam τ) := natCast_mem_primeOf _
      obtain ⟨z, hz, hze⟩ := (Formalism.MainNotions.GlobalTheoryTheory.jnt_inertiaD D _ hPp hd σ).2 (Or.inr hgσ) a
      have hz' : ‖rhoH D lam τ (σ (a : D.host.E)) - rhoH D lam τ (a : D.host.E)‖ < 1 := by
        rw [← map_sub, ← hze]
        exact hz
      change ‖rhoH D lam τ (a : D.host.E)‖ < 1 ↔ ‖rhoH D lam τ (σ (a : D.host.E))‖ < 1
      constructor
      · intro h
        rw [← sub_add_cancel (rhoH D lam τ (σ (a : D.host.E))) (rhoH D lam τ (a : D.host.E))]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hz' h)
      · intro h
        rw [← add_sub_cancel (rhoH D lam τ (σ (a : D.host.E))) (rhoH D lam τ (a : D.host.E))]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h (by rw [norm_sub_rev]; exact hz'))
    have h1 := SamePrime.norm_eq hsp y
    have h2 : tauEmb D lam (tauSg D τ) (D.host.conj y) = tauEmb D lam τ (σ y) := by
      unfold tauEmb
      rw [hemb]
    rw [h2, ← coe_rhoH, h1]
    rfl

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstInLettersJetLogG
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section
namespace GlobalTheory.OnePlace.Letters

theorem constantCoeff_jetLogG (p : ℕ) [Fact p.Prime] (n' : ℕ) {β : Type} (v : ZMod n' × β) :
    MvPowerSeries.constantCoeff (jetLogG p n' v) = 0 := by
  show jetLogG p n' v 0 = 0
  unfold jetLogG
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  intro h
  have h2 := congrArg (fun m : ZMod n' × β →₀ ℕ => m (v.1 - 2 * (e : ZMod n'), v.2)) h
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at h2
  exact (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)) h2.symm

def posEquiv (n r0 r1 : ℕ) [NeZero n] : Zidx n r0 r1 ≃ ZMod n × Fin r0 × Fin r1 where
  toFun z := (((z.1 : ℕ) : ZMod n), z.2)
  invFun v := (toFin v.1, v.2)
  left_inv z := by
    ext <;> simp [toFin, ZMod.val_natCast, Nat.mod_eq_of_lt z.1.2]
  right_inv v := by
    ext <;> simp [toFin, ZMod.natCast_zmod_val]

theorem coeff_inLetters {n r0 r1 : ℕ} [NeZero n] {R : Type} [Semiring R] (f : MvPowerSeries (Zidx n r0 r1) R)
    (m : ZMod n × Fin r0 × Fin r1 →₀ ℕ) :
    MvPowerSeries.coeff m (inLetters f) = MvPowerSeries.coeff (Finsupp.mapDomain (posEquiv n r0 r1).symm m) f := rfl

theorem inLetters_eq_rename {n r0 r1 : ℕ} [NeZero n] {R : Type} [CommRing R] (f : MvPowerSeries (Zidx n r0 r1) R) :
    inLetters f = MvPowerSeries.rename (posEquiv n r0 r1) f := by
  ext m
  have hm : m = Finsupp.mapDomain (posEquiv n r0 r1) (Finsupp.mapDomain (posEquiv n r0 r1).symm m) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have h1 := MvPowerSeries.coeff_embDomain_rename (posEquiv n r0 r1).toEmbedding f
    (Finsupp.mapDomain (posEquiv n r0 r1).symm m)
  rw [Finsupp.embDomain_eq_mapDomain] at h1
  rw [coeff_inLetters]
  conv_rhs => rw [hm]
  exact h1.symm

theorem map_inLetters {n r0 r1 : ℕ} [NeZero n] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries (Zidx n r0 r1) R) :
    MvPowerSeries.map φ (inLetters f) = inLetters (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, coeff_inLetters, coeff_inLetters, MvPowerSeries.coeff_map]

theorem subst_inLetters_jetLogG {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} [NeZero n'] (F : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p)) :
    (∀ z, MvPowerSeries.constantCoeff (jetZ p n' r0 r1 z) = 0) ∧
    MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v)
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters F)) =
    MvPowerSeries.subst (jetZ p n' r0 r1) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) F) := by
  refine ⟨fun z => constantCoeff_jetLogG p n' _, ?_⟩
  have ha : MvPowerSeries.HasSubst
      (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by
      rw [map_mul, constantCoeff_jetLogG, mul_zero]
  rw [map_inLetters, inLetters_eq_rename, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) ha]
  congr 1
  funext z
  rw [Function.comp_apply, MvPowerSeries.subst_X ha, map_one, one_mul]
  rfl

end GlobalTheory.OnePlace.Letters
end
end

