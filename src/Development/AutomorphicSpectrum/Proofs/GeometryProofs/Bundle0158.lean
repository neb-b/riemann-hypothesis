module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsFunctionOnChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsRingHomComplex
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0054

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingNoetherianNormalFraction
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chartRing_noetherian_normal_fraction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω :=
  @PositivityTheory.Xgn.exists_function_on_chart

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ClosedInProductProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Segre

theorem isProjOver_of_closed_product : ∀ (K : Type) [Field K] (M r : ℕ) (X' : Scheme.{0}) (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)), IsClosedImmersion j → IsProjOver (j ≫ pullback.fst _ _ ≫ PSpace.str K M) := by
  intro K _ M r X' j hj
  have := hj
  exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion j
    (GlobalTheory.ProjSpace.isProjOver_pullback_str K M r)

end GlobalTheory.CompanionTheory.Ar.SncBase.Segre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataAbelianPartBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert

open GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

section Field

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {L : Type} [Field L]

theorem centre_map (zL : Sp L ⟶ X) (e : L →+* ℂ) : centre (spMap e ≫ zL) = centre zL := by
  refine (Scheme.Hom.comp_apply (spMap e) zL _).trans ?_
  exact congrArg zL (Subsingleton.elim _ _)

theorem descend {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (zL : Sp L ⟶ X) (e : L →+* ℂ) {a : Ω} {r : ℂ}
    (h : ValAt ξ (spMap e ≫ zL) a r) : ∃ t : L, ValAt ξ zL a t ∧ e t = r := by
  have hc : centre zL = centre (spMap e ≫ zL) := (centre_map zL e).symm
  have h0 := h
  obtain ⟨h', s, hs, -⟩ := h
  have h'' : genPt ξ ⤳ centre zL := hc ▸ h'
  have hv : ValAt ξ zL a (Scheme.stalkClosedPointTo zL |>.hom (X.presheaf.stalkSpecializes (specializes_of_eq hc) s)) :=
    ⟨h'', _, (GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.genMap_stalkSpecializes ξ hc h' h'' s).trans hs, rfl⟩
  exact ⟨_, hv, ValAt.unique hξ (valAt_of_field_map ξ zL _ e rfl hv) h0⟩

theorem coords_map (ξ : Sp Ω ⟶ X) {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {zL : Sp L ⟶ X}
    {w : (Σ k, J k) → L} (hw : CoordsAt ξ y zL w) (e : L →+* ℂ) :
    CoordsAt ξ y (spMap e ≫ zL) (fun p => e (w p)) := by
  refine ⟨fun k => (hw.1 k).imp fun c hc => hc.map e, fun k c hc => ?_⟩
  have hne : w ⟨k, c⟩ ≠ 0 := fun h0 => by simp [h0] at hc
  obtain ⟨hy, hi⟩ := hw.2 k c (isUnit_iff_ne_zero.2 hne)
  refine ⟨hy, fun i => ?_⟩
  obtain ⟨ρ, hρ, hr⟩ := hi i
  exact ⟨e ρ, valAt_of_field_map ξ zL _ e rfl hρ, by simp only [hr, map_mul]⟩

variable {ξ : Sp Ω ⟶ X} {z : Sp L ⟶ X}

theorem val_inv {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  obtain ⟨u, rfl⟩ : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.2 hr)
  refine ⟨h1, (u⁻¹ : (X.presheaf.stalk (centre z))ˣ).1, eq_inv_of_mul_eq_one_left ?_, eq_inv_of_mul_eq_one_left ?_⟩
  · rw [← map_mul, Units.inv_mul, map_one]
  · refine ((Scheme.stalkClosedPointTo z).hom.map_mul _ _).symm.trans ?_
    exact (congrArg (Scheme.stalkClosedPointTo z).hom (Units.inv_mul u)).trans (Scheme.stalkClosedPointTo z).hom.map_one

theorem val_pow (h₀ : genPt ξ ⤳ centre z) {a : Ω} {r : L} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using RootHt.valAt_one h₀
  | succ n ih => simpa [pow_succ] using RootHt.valAt_mul ih h

theorem val_zpow (h₀ : genPt ξ ⤳ centre z) {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) :
    ValAt ξ z (a ^ n) (r ^ n) := by
  cases n with
  | ofNat n => simpa using val_pow h₀ h n
  | negSucc n =>
    simpa [zpow_negSucc] using val_inv (val_pow h₀ h (n + 1)) (pow_ne_zero _ hr)

theorem val_prod_zpow (h₀ : genPt ξ ⤳ centre z) {K : Type} (s : Finset K) {A : K → Ω} {r : K → L} (b : K → ℤ)
    (h : ∀ k, ValAt ξ z (A k) (r k)) (hr : ∀ k, r k ≠ 0) :
    ValAt ξ z (∏ k ∈ s, A k ^ b k) (∏ k ∈ s, r k ^ b k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RootHt.valAt_one h₀
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk]
    exact RootHt.valAt_mul (val_zpow h₀ (h k) (hr k) _) ih

end Field

theorem vertical_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ Or.𝔐.X) (w : (Σ k, J k) → L) (cc : (k : K) → J k) (p : ℕ), CoordsAt Or.𝔐.ξ Dc.y z w → (∀ k, w ⟨k, cc k⟩ ≠ 0) → p ∈ Dc.S → ∃ t : L, t ≠ 0 ∧ ValAt Or.𝔐.ξ z (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y cc (-Dc.vdeg p)) t ∧ ∀ e : L →+* ℂ, Dc.vertFactor p (fun i => e (w i)) = ‖e t‖ * ∏ k, ‖e (w ⟨k, cc k⟩)‖ ^ Dc.vdeg p k := by
  intro E _ _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or L _ _ z w cc p hw hcc hp
  classical
  obtain ⟨e₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  have hT := Or.𝔐.tie
  have hξ := hT.gen
  have hwe := fun e : L →+* ℂ => coords_map Or.𝔐.ξ hw e
  have hm : ∀ e : L →+* ℂ, (fun q => e (w q)) ∈ mcPts (mCoordIdeal Dc.y) := fun e =>
    (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt _ _ _ K J _ hT _).2 ⟨_, Or.𝔐.all _, hwe e⟩
  have tv : ∀ (e : L →+* ℂ) (a : Ω) (r : ℂ),
      ValAt Or.𝔐.ξ (spMap e ≫ z) a r ↔ IsValueAt Dc.y a (fun q => e (w q)) r :=
    fun e a r => _root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords _ _ _ K J _ hT _ _ (Or.𝔐.all _) (hwe e) a r
  have hne := GlobalTheory.CompanionTheory.Ar.ProvConj.valAt_ne_zero (Dc.S_prime p hp).ne_zero (Dc.vertical p hp) (hm e₀) cc
    (fun k => (map_ne_zero e₀).2 (hcc k)) Dc.arith.2.1.2.1
  have hex : ∃ v, IsValueAt Dc.y (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
      chartMono Dc.y cc (-Dc.vdeg p)) (fun q => e₀ (w q)) v := by
    by_contra h
    exact hne (by rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dite_eq_right h])
  obtain ⟨v, hv⟩ := hex
  rw [valAt_eq (hm e₀) hv] at hne
  obtain ⟨t, ht, het⟩ := descend hξ z e₀ ((tv e₀ _ _).2 hv)
  refine ⟨t, fun h0 => hne (by rw [← het, h0, map_zero]), ht, fun e => ?_⟩
  have hve := valAt_of_field_map Or.𝔐.ξ z _ e rfl ht
  have hccz : ∀ k, e (w ⟨k, cc k⟩) ≠ 0 := fun k => (map_ne_zero e).2 (hcc k)
  have hc : ∃ c : (k : K) → J k, ∀ k, (fun q => e (w q)) ⟨k, c k⟩ ≠ 0 := ⟨cc, hccz⟩
  unfold ComponentData.vertFactor
  rw [dite_eq_left hc]
  have hcs := hc.choose_spec
  generalize hc.choose = c at hcs ⊢
  have hcs' : ∀ k, e (w ⟨k, c k⟩) ≠ 0 := hcs
  have hy : ∀ k, Dc.y ⟨k, c k⟩ ≠ 0 := fun k => ((hwe e).2 k (c k) (isUnit_iff_ne_zero.2 (hcs' k))).1
  have hy' : ∀ k, Dc.y ⟨k, cc k⟩ ≠ 0 := fun k => ((hwe e).2 k (cc k) (isUnit_iff_ne_zero.2 (hccz k))).1
  have hr : ∀ k, ValAt Or.𝔐.ξ (spMap e ≫ z) (Dc.y ⟨k, cc k⟩ / Dc.y ⟨k, c k⟩)
      (e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩)) := fun k => by
    obtain ⟨ρ, h1, h2⟩ := ((hwe e).2 k (c k) (isUnit_iff_ne_zero.2 (hcs' k))).2 (cc k)
    have h3 : e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩) = ρ := by
      rw [div_eq_iff (hcs' k)]
      exact h2
    rw [h3]
    exact h1
  have hall := RootHt.valAt_mul hve (val_prod_zpow (Or.𝔐.all _) Finset.univ (Dc.vdeg p) hr
    (fun k => div_ne_zero (hccz k) (hcs' k)))
  have ha : MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
      chartMono Dc.y cc (-Dc.vdeg p) * ∏ k, (Dc.y ⟨k, cc k⟩ / Dc.y ⟨k, c k⟩) ^ Dc.vdeg p k =
      MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
        chartMono Dc.y c (-Dc.vdeg p) := by
    rw [_root_.mul_assoc]
    congr 1
    unfold chartMono
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.neg_apply, _root_.zpow_neg, _root_.zpow_neg, div_zpow, div_eq_mul_inv, ← _root_.mul_assoc,
      inv_mul_cancel₀ (zpow_ne_zero _ (hy' k)), _root_.one_mul]
  rw [ha] at hall
  rw [valAt_eq (hm e) ((tv e _ _).1 hall), ← norm_mul]
  have hid : e t * (∏ k, (e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩)) ^ Dc.vdeg p k) *
      zMono (fun q => e (w q)) c (Dc.vdeg p) = e t * ∏ k, e (w ⟨k, cc k⟩) ^ Dc.vdeg p k := by
    rw [_root_.mul_assoc]
    congr 1
    unfold zMono
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hcs' k)]
  rw [hid, norm_mul, norm_prod]
  simp only [norm_zpow]

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsMultihomogPrimeOfPlace
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre

section

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
  {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) {g : MRing J} {e : B → ℕ}
    (hg : IsMultiHomog g e) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  have hT : (∏ k, (X k : MvPolynomial B Ω) ^ e k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  rw [mCoordIdeal, RingHom.mem_ker]
  show mConeMap y g = 0 ↔ _
  rw [GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.mConeMap_form y hg, mul_eq_zero, or_iff_right hT, C_eq_zero]

variable (v : Place (ZMod p) K) (w : (Σ k, J k) → K) (c : ∀ k, J k)

def ratio (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hle : ∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩))
    (q : Σ k, J k) : v.ring :=
  ⟨w q / w ⟨q.1, c q.1⟩, by
    rw [← v.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hle q.1 q.2) zero_le'⟩

variable {v w c}
variable (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hle : ∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩))

include hc in
theorem prod_ne_zero (e : B → ℕ) : (∏ k, w ⟨k, c k⟩ ^ e k) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)

theorem coe_aeval_ratio {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    ((aeval (ratio v w c hc hle) g : v.ring) : K) = aeval w g * (∏ k, w ⟨k, c k⟩ ^ e k)⁻¹ := by
  rw [← GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue.aeval_div w c g e hg]
  exact MvPolynomial.comp_aeval_apply (φ := (algebraMap v.ring K).toIntAlgHom) _ g

theorem aeval_residue (g : MRing J) :
    aeval (fun q => residue v.ring (ratio v w c hc hle q)) g =
      residue v.ring (aeval (ratio v w c hc hle) g) :=
  (MvPolynomial.comp_aeval_apply (φ := (residue v.ring).toIntAlgHom) _ g).symm

theorem valuation_prod (e : B → ℕ) :
    v.valuation (∏ k, w ⟨k, c k⟩ ^ e k) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => map_pow _ _ _

include hc in
theorem prod_valuation_pos (e : B → ℕ) : 0 < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  rw [← valuation_prod]
  exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (prod_ne_zero hc e))


include hc hle in
theorem valuation_aeval_le {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    v.valuation (aeval w g) ≤ ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  have h := (v.valuation_le_one_iff _).2 (aeval (ratio v w c hc hle) g).2
  rw [coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod] at h
  rwa [mul_inv_le_iff₀ (prod_valuation_pos hc e), one_mul] at h

theorem mem_iff {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    g ∈ mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)) ↔
      v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  refine (mem_mCoordIdeal_iff _ hg).trans (Iff.trans (Eq.congr_left (aeval_residue hc hle g)) ?_)
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff, ← v.valuation_lt_one_iff,
    coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod,
    mul_inv_lt_iff₀ (prod_valuation_pos hc e), one_mul]

end

theorem exists_centre : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K) (v : Place (ZMod p) K)
    (c : ∀ k, J k), (∀ k, w ⟨k, c k⟩ ≠ 0) →
    (∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩)) →
    ∃ W : Ideal (MRing J), W.IsPrime ∧ IsMultiHomogIdeal W ∧ mCoordIdeal w ≤ W ∧
      (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) ∧ Dom v w W ∧
      ∀ (e : B → ℕ) (g : MRing J), IsMultiHomog g e →
        (g ∈ W ↔ v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k) := by
  intro B _ J _ p _ K _ _ _ w v c hc hle
  refine ⟨mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)), RingHom.ker_isPrime _,
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _, ?_, ?_, ?_, fun e g hg => mem_iff hc hle hg⟩
  · obtain ⟨S, hS, hSe⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
    have hSV : Ideal.span S ≤ mCoordIdeal w := hSe.ge
    rw [hSe, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have hf0 : aeval w f = 0 := (mem_mCoordIdeal_iff w ha).1 (hSV (Ideal.subset_span hf))
    refine (mem_iff hc hle ha).2 ?_
    rw [hf0, map_zero]
    exact prod_valuation_pos hc a
  · intro k h
    have h1 := (X_mem_iff _ k (c k)).1 h
    have h2 : ratio v w c hc hle ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
    rw [h2, map_one] at h1
    exact one_ne_zero h1
  · intro e g h hg hh hhW
    have hh' : v.valuation (aeval w h) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k :=
      le_antisymm (valuation_aeval_le hc hle hh) (not_lt.1 fun hlt => hhW ((mem_iff hc hle hh).2 hlt))
    rw [hh']
    exact ⟨valuation_aeval_le hc hle hg, (mem_iff hc hle hg).1⟩

end GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsResolutionGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GenRes

theorem genericFibre_closed {O K : Type} [CommRing O] [Field K] (β : O →+* K)
    (hinj : Function.Injective β) (hfr : ∀ x : K, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (P : Scheme.{0}) (s : P ⟶ Sp O) (hs : IsProjOver s) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme P) :
    IsReduced (pullback s (spMap β)) ∧ IsLocallyNoetherian (pullback s (spMap β)) ∧
      ∃ (M : ℕ) (i : pullback s (spMap β) ⟶ PSpace K M), IsClosedImmersion i ∧
        i ≫ PSpace.str K M = pullback.snd s (spMap β) := by
  letI : Algebra O K := β.toAlgebra
  haveI : IsDomain O := hinj.isDomain β
  haveI : IsFractionRing O K :=
    { map_units := fun y => by
        have hy : β y.1 ≠ 0 := fun h => nonZeroDivisors.ne_zero y.2 (hinj (by rw [h, map_zero]))
        exact (IsUnit.mk0 _ hy)
      surj := fun z => by
        obtain ⟨a, b, hb, h⟩ := hfr z
        have hb0 : b ≠ 0 := fun h0 => hb (by rw [h0, map_zero])
        exact ⟨⟨a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩⟩, h⟩
      exists_of_eq := fun {x y} h => ⟨1, by rw [hinj h]⟩ }
  have hp : IsProjOver (pullback.snd s (spMap β)) := GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hs
  have hb : IsPreimmersion (spMap β) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := K) (nonZeroDivisors O)
  have hbf : Flat (spMap β) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors O))
  have h1 : IsPreimmersion (pullback.fst s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hiso := GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap β))
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  refine ⟨?_, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β)), hp⟩
  have : ∀ x, _root_.IsReduced ((pullback s (spMap β)).presheaf.stalk x) := fun x => by
    have := hiso x
    have i := (asIso ((pullback.fst s (spMap β)).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨_, _⟩ := hn (pullback.fst s (spMap β) x)
    exact isReduced_of_injective i.symm i.symm.injective
  exact isReduced_of_isReduced_stalk _

theorem isProper_of_closed {K : Type} [Field K] {M r : ℕ} {X X' : Scheme.{0}} (i : X ⟶ PSpace K M)
    [IsClosedImmersion i] (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)) [IsClosedImmersion j]
    (f : X' ⟶ X) (h : f ≫ i = j ≫ pullback.fst _ _) : IsProper f ∧ IsProper (f ≫ i ≫ PSpace.str K M) := by
  have := isProper_str K M
  have := isProper_str K r
  have hfst : IsProper (pullback.fst (PSpace.str K M) (PSpace.str K r)) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _).flip inferInstance
  have hfi : IsProper (f ≫ i) := by rw [h]; infer_instance
  have hf : IsProper f := IsProper.of_comp f i
  refine ⟨hf, ?_⟩
  rw [← Category.assoc]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Flat.GenRes

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_resolution_genericFibre : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → IsLocallyNoetherian (pullback Y.s (spMap β)) ∧ ∃ (X' : Scheme.{0}) (f : X' ⟶ pullback Y.s (spMap β)) (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c), IsIso jW ∧ jW ≫ Y.jQ = W'.ι ≫ f ∧ IsProper f ∧ IsProper (f ≫ pullback.snd Y.s (spMap β)) ∧ SmoothOfRelativeDimension d (f ≫ pullback.snd Y.s (spMap β)) ∧ Geo.ResK.HasSncCoords (f ≫ pullback.snd Y.s (spMap β)) d (W' : Set X')ᶜ := by
  rintro hRes E _ _ _ H D l Xo c O _ β Y ⟨hinj, -, hfr⟩
  obtain ⟨hred, hln, M, i, hi, his⟩ := GenRes.genericFibre_closed β hinj hfr Y.X Y.s Y.proj Y.normal
  refine ⟨hln, ?_⟩
  have := Y.jQ_open
  let U : (pullback Y.s (spMap β)).Opens := Y.jQ.opensRange
  have hd : Dense (U : Set (pullback Y.s (spMap β) : Scheme.{0})) := by
    have : (U : Set (pullback Y.s (spMap β) : Scheme.{0})) = Set.range Y.jQ := Scheme.Hom.coe_opensRange _
    rw [this]; exact Y.jQ_dense
  have hιe : Y.jQ.isoOpensRange.inv ≫ Y.jQ = U.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hXF : SmoothOfRelativeDimension D.dim
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    have := Xo.smooth
    have := smoothOfRelativeDimension_isStableUnderBaseChange D.dim
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.dim)
      (IsPullback.of_hasPullback _ _) Xo.smooth
  have hU : SmoothOfRelativeDimension D.dim (U.ι ≫ pullback.snd Y.s (spMap β)) := by
    rw [← hιe, Category.assoc, Y.jQ_over]
    have := smoothOfRelativeDimension_isStableUnderBaseChange D.dim
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.dim)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ :
        IsPullback Y.jQ.isoOpensRange.inv (Y.jQ.isoOpensRange.inv ≫ pullback.snd _ _) (pullback.snd _ _) (𝟙 _)) hXF
  have hin : Geo.ResK.IsResInput M i U D.dim := ⟨hi, hred, hd, by rw [his]; exact hU⟩
  haveI : CharZero c.F := inferInstance
  obtain ⟨r, X', j, f, hj, hfj, hsm, hiso, hdense, hsnc⟩ := hRes c.F M D.dim _ i U hin
  obtain ⟨hp1, hp2⟩ := GenRes.isProper_of_closed i j f hfj
  rw [his] at hp2 hsm hsnc
  refine ⟨X', f, D.dim, f ⁻¹ᵁ U, (f ∣_ U) ≫ Y.jQ.isoOpensRange.inv, inferInstance, ?_, hp1, hp2, hsm, hsnc⟩
  rw [Category.assoc, hιe, morphismRestrict_ι]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermDimensionUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GermUniv

theorem germ_chart_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), (∀ (d₂ : ℕ) (_ : GermAt t x d₂), d = d₂) ∧ ∀ (J : Type) [Finite J] (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G), homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1 → ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m, (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m :=
  PositivityTheory.HtPt.Cd.germ_univ

end GlobalTheory.CompanionTheory.Ar.GermUniv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermLieBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GermLie

theorem germ_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (V : Type) [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V), ∃ e : V ≃ₗ[S] (Fin d → S), (∀ v, IsCombAtG t x g.tg (e v) (M.pt v).left) ∧ ∀ r : 𝓞 E →+* Module.End S V, M.IsActOf t.act.act r → ∀ a v, e (r a v) = (rho g.B a).mulVec (e v) :=
  PositivityTheory.HtPt.Cd.germ_lie

end GlobalTheory.CompanionTheory.Ar.GermLie
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleGeneratorCorrespondence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Nfold

theorem nfold_first_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (n : ℕ), ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (m : ℕ), ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x m (0 : Fin 2)) (jptG t x d g.x m (1 : Fin 2))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x d g.x g.e m ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (LB.invGen t.PP.L _ _ (genPowG t _ _ (g.e m) n)))) :=
  @PositivityTheory.HtPt.Ca.nfold_law

end GlobalTheory.CompanionTheory.Ar.Nfold
end

