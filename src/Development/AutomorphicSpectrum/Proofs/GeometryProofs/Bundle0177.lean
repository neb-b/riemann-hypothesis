module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0174
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import Development.WeilBound.CoreStatements.VolumeEquality.SheetPiecesComponent
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0173
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalLatticeHeightFormula
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0171
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IntegralPointExtendsModel

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmIntegersRegularAtComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem integers_mem_regAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : E →+* Z.Ω), (∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)) →
    ∀ (q : Cpt (Z.ξ₀ ≫ Y.j)) (a : 𝓞 E), σ (a : E) ∈ regAt (Z.ξ₀ ≫ Y.j) q := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ σ _ q a
  have hN : NormalCpt (Z.ξ₀ ≫ Y.j) := XR.normalCpt_of_isCptGen Z.gen Y.normal
  exact hN q _ ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)).tower_top)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpRatioUnramifiedOddPrime
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem integers_regular {F : Type} [Field F] [NumberField F] (hN : Flat.NormalCpt ξ) (σ : 𝓞 F →+* Ω) (q : Cpt ξ)
    (a : 𝓞 F) : σ a ∈ regAt ξ q := by
  refine hN q _ ?_
  have h : IsIntegral ℤ (σ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map σ.toIntAlgHom
  exact h.tower_top

theorem unitAt_nat {q : Cpt ξ} [CharZero Ω] (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simpa using Flat.ZUnit.one
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    rw [Nat.cast_mul]
    exact Flat.ZUnit.mul (ha (left_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_right b))
      (hb (right_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_left a))

theorem unitAt_natAbs_discr {F : Type} [Field F] [NumberField F] {q : Cpt ξ} [CharZero Ω]
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr F → unitAt ξ q (p : Ω)) :
    unitAt ξ q (((discr F).natAbs : ℕ) : Ω) :=
  unitAt_nat _ (Int.natAbs_ne_zero.2 (discr_ne_zero F)) fun p hp hd =>
    h p hp (Int.natCast_dvd.2 hd)

theorem natAbs_discr_mem_different (F : Type) [Field F] [NumberField F] :
    (((discr F).natAbs : ℕ) : 𝓞 F) ∈ differentIdeal ℤ (𝓞 F) := by
  have h := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 F))
  rwa [absNorm_differentIdeal F] at h

theorem htW_eq_htDual {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (L : Semi.LB G.left) (n : ℕ) {F : Type} [Field F] [NumberField F] (ρ : 𝓞 F →+* Module.End Ω Li)
    (σ : 𝓞 F →+* Ω) (q : Cpt ξ) (hσ : ∀ a, σ a ∈ regAt ξ q)
    (hu : unitAt ξ q (((discr F).natAbs : ℕ) : Ω)) :
    M.htW L n ρ σ (differentIdeal ℤ (𝓞 F)) q = M.htDual L n ρ σ q := by
  apply le_antisymm
  · refine Submodule.span_le.2 fun e he => ?_
    have h1 := he.2 _ (natAbs_discr_mem_different F)
    rw [map_natCast] at h1
    have h2 := Submodule.smul_mem _ (⟨_, hu.2.2⟩ : regAt ξ q) h1
    have h3 : (⟨_, hu.2.2⟩ : regAt ξ q) • (((discr F).natAbs : ℕ) : Ω) • e = e := by
      show (((discr F).natAbs : ℕ) : Ω)⁻¹ • (((discr F).natAbs : ℕ) : Ω) • e = e
      exact inv_smul_smul₀ hu.1 e
    rw [h3] at h2
    exact h2
  · intro e he
    refine Submodule.subset_span ⟨M.mem_eigSp_of_mem_htDual L n ρ σ he, fun d _ => ?_⟩
    exact Submodule.smul_mem _ (⟨σ d, hσ d⟩ : regAt ξ q) he

theorem exists_mul_of_isCp {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {κ w : Ω} (hκ : HT.IsCp p κ) (hw : HT.IsCp p w)
    (R : Subring Ω) (hR : w ∈ R) : ∃ u ∈ R, w = u * κ := by
  unfold HT.IsCp at hκ hw
  rw [if_neg h2] at hκ hw
  obtain ⟨z, hz, rfl⟩ := hκ
  obtain ⟨z', hz', rfl⟩ := hw
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨j, -, hj⟩ := hz'.eq_pow_of_pow_eq_one hz.pow_eq_one
  obtain ⟨k, -, hk⟩ := hz.eq_pow_of_pow_eq_one hz'.pow_eq_one
  have h1 : z' ∈ R := by simpa using R.add_mem hR R.one_mem
  have h3 : z ∈ R := hj ▸ R.pow_mem h1 j
  refine ⟨∑ i ∈ Finset.range k, z ^ i, R.sum_mem fun i _ => R.pow_mem h3 i, ?_⟩
  rw [geom_sum_mul, hk]

theorem sandwich_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ κ w : Ω, HT.IsCp p κ → HT.IsCp p w → HT.Sandwich 𝔐 p κ → ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → w ∈ regAt 𝔐.ξ q → ∀ t : CMType H ⊕ CMType H, 𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, w • e ∈ 𝔐.dR t q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 p hp _ h2 hd κ w hκ hw hS q hq hwq t
  haveI : CharZero Ω := ⟨fun a b h => by
    have h' : 𝔐.cst (a : c.F) = 𝔐.cst (b : c.F) := by rw [map_natCast, map_natCast, h]
    exact Nat.cast_injective (𝔐.cst.injective h')⟩
  have hN : Flat.NormalCpt 𝔐.ξ := GlobalTheory.CompanionTheory.Ar.XR.normalCpt_of_isCptGen 𝔐.tie.gen 𝔐.normal
  have hu : unitAt 𝔐.ξ q (((discr E).natAbs : ℕ) : Ω) := unitAt_natAbs_discr fun r hr hrd => by
    by_contra hn
    have : r = p := GlobalTheory.CompanionTheory.Ar.inFibre_unique hp.out hr hq hn
    exact hd (this ▸ hrd)
  have hHT : 𝔐.HT p t q = 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb t) q := by
    cases t with
    | inl τ => exact htW_eq_htDual 𝔐.M _ _ 𝔐.ρ _ q (integers_regular hN _ q) hu
    | inr τ => rfl
  obtain ⟨-, -, -, hs⟩ := hS q hq
  obtain ⟨h1, h3⟩ := hs t
  obtain ⟨u, huR, rfl⟩ := exists_mul_of_isCp hp.out h2 hκ hw (regAt 𝔐.ξ q) hwq
  rw [hHT]
  refine ⟨h1, fun e he => ?_⟩
  rw [mul_smul]
  exact Submodule.smul_mem _ (⟨u, huR⟩ : regAt 𝔐.ξ q) (h3 e he)

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeRight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem ptsIntegral_eq_sum_fundamental : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t :=
  SheetDecomposition.sheet_pieces_component

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormalGermLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem germAt_exists_of_isLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0), ∃ d, Nonempty (GermAt t x d) :=
  GermInh.germ_local

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceOfNotMemGenFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

section Local

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {F : Type} [Field F] [NumberField F]


omit [NumberField F] in
theorem int_mem_regAt (hN : NormalCpt ξ) (φ : F →+* Ω) (a : 𝓞 F) (q : Cpt ξ) : φ (a : F) ∈ regAt ξ q :=
  hN q _ ((map_isIntegral_int φ (RingOfIntegers.isIntegral_coe a)).tower_top)

theorem overInt_of_normalCpt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω}
    (ht : CoordTie ℤ ξ fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) (hN : NormalCpt ξ) (φ : F →+* Ω) :
    OverInt y φ := by
  refine ⟨fun k => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := ht.cover ⟨genPt ξ, specializes_rfl⟩
    exact ⟨c k, fun h0 => hc.1 (Finset.prod_eq_zero (Finset.mem_univ k) h0)⟩
  · have hc' : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
    have h1 := (ht.ring c hc' (φ (a : F))).2 fun p _ => int_mem_regAt hN φ a p
    refine Algebra.adjoin_le ?_ h1
    rintro _ ⟨j, rfl⟩
    show (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c k⟩) ∈ chartRingZ y c
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩

theorem cst_mem_regAt_of_genFibre (hN : NormalCpt ξ) (φ : F →+* Ω) {p : Cpt ξ} (hp : p ∈ genFibre ℤ ξ) (a : F) :
    φ a ∈ regAt ξ p := by
  have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hu := hp n hn
  have h1 : φ (n • a) ∈ regAt ξ p := int_mem_regAt hN φ (⟨n • a, hi⟩ : 𝓞 F) p
  have h2 : φ a = (algebraMap ℤ Ω n)⁻¹ * φ (n • a) := by
    rw [zsmul_eq_mul, map_mul, map_intCast, eq_intCast, inv_mul_cancel_left₀]
    simpa using hu.1
  rw [h2]
  exact mul_mem hu.2.2 h1

theorem exists_place_of_notMem_genFibre (hN : NormalCpt ξ) (φ : F →+* Ω) {p : Cpt ξ} (hp : p ∉ genFibre ℤ ξ) :
    ∃ v : HeightOneSpectrum (𝓞 F), ∀ a : F, v.valuation F a ≤ 1 → φ a ∈ regAt ξ p := by
  have := Centre.Sep.isLocalRing_regAt ξ p
  let f : 𝓞 F →+* regAt ξ p :=
    (φ.comp (algebraMap (𝓞 F) F)).codRestrict (regAt ξ p) fun a => int_mem_regAt hN φ a p
  have hf : ∀ a : 𝓞 F, ((f a : regAt ξ p) : Ω) = φ (a : F) := fun _ => rfl
  have hmem : ∀ a : 𝓞 F, a ∈ (IsLocalRing.maximalIdeal (regAt ξ p)).comap f ↔ ¬ unitAt ξ p (φ (a : F)) := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Centre.Sep.isUnit_regAt_iff, hf]
  obtain ⟨o, ho, hu⟩ : ∃ o : ℤ, o ≠ 0 ∧ ¬ unitAt ξ p (algebraMap ℤ Ω o) := by
    by_contra h
    push_neg at h
    exact hp h
  have hne : (IsLocalRing.maximalIdeal (regAt ξ p)).comap f ≠ ⊥ := by
    intro hbot
    have h1 : (o : 𝓞 F) ∈ (IsLocalRing.maximalIdeal (regAt ξ p)).comap f := by
      rw [hmem]
      simpa using hu
    rw [hbot, Ideal.mem_bot] at h1
    exact ho (by exact_mod_cast h1)
  refine ⟨⟨_, inferInstance, hne⟩, fun a ha => ?_⟩
  obtain ⟨n, d, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha
  have hd : unitAt ξ p (φ ((d : 𝓞 F) : F)) := by
    by_contra h
    exact d.2 ((hmem _).2 h)
  have h2 : φ a = φ (n : F) * (φ ((d : 𝓞 F) : F))⁻¹ := by
    have e' : a * ((d : 𝓞 F) : F) = (n : F) := e
    rw [← e', map_mul, mul_inv_cancel_right₀ hd.1]
  rw [h2]
  exact mul_mem (int_mem_regAt hN φ n p) hd.2.2

end Local

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteGroupSchemeSumExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_group_scheme_sum_extension : ∀ {X : Scheme.{0}} {M : LB X}, M.IsLB → ∀ {K : Type} [Field K] [NumberField K] (n : ℕ), 1 ≤ n → ∀ (xl : Sp K ⟶ X) (A : FG M (Sp K)), (∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), A.sum U h = (h xl ^ n)⁻¹) → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (e : FG M (Sp K')), (∀ (U : Type) [CommGroup U] (h : (Sp K' ⟶ X) → U), e.sum U h = h (spMap (algebraMap K K') ≫ xl)) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp K') (z : Z) (J), Good M z J → e.v r z J ^ n * A.v (r ≫ spMap (algebraMap K K')) z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeGeo

theorem exists_factor_XF_of_genericPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X), GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ genericPoints Y.X →
      ∃ y₀ : Sp Ω ⟶ Xo.XF c, ξ = y₀ ≫ Y.j := by
  intro E _ _ _ H D l Xo c Y Ω _ ξ hξ
  obtain ⟨K, _, _, n, x, y, ht, -, he⟩ := _root_.GlobalTheory.CompanionTheory.Ar.XR.exists_cpt_of_genericPoint E H D l Xo c Y _ hξ
  obtain ⟨i, hi⟩ := GlobalTheory.CompanionTheory.Ar.TowerOfTest.factor (y ≫ Y.j) ht.gen ξ he.symm
  exact ⟨Spec.map (CommRingCat.ofHom i) ≫ y, by rw [hi, Category.assoc]⟩

end GlobalTheory.CompanionTheory.Ar.ChangeGeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricConnectednessGeneralizes
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_isPullback_left {P Q X S T U : Scheme.{0}} {t : P ⟶ X} {v : P ⟶ U} {p : X ⟶ S}
    {g : U ⟶ T} {f : T ⟶ S} {t' : Q ⟶ X} {v' : Q ⟶ T}
    (h : IsPullback t v p (g ≫ f)) (h' : IsPullback t' v' p f) :
    ∃ u : P ⟶ Q, IsPullback u v v' g := by
  refine ⟨h'.lift t (v ≫ g) (by simpa using h.w), ?_⟩
  refine IsPullback.of_right (h₁₂ := t') (h₂₂ := f) (v₁₃ := p) ?_ (by simp) h'
  simpa using h

theorem spMap_comp_spMap {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem geometricallyConnected_of_local {k A E L K : Type} [CommRing k] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Field E] [Field L] [Field K] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (e : Sp k ⟶ X) (hs : e ≫ p = 𝟙 _) [Smooth p] [IsProper p] (φ : k →+* A) (a : k →+* E)
    (b : E →+* IsLocalRing.ResidueField A)
    (hb : b.comp a = (IsLocalRing.residue A).comp φ)
    (hE : GeometricallyConnected (pullback.snd p (spMap a)))
    (j : A →+* L) (hj : j.Flat) (c : k →+* K) (d : K →+* L) (hd : d.comp c = j.comp φ) :
    GeometricallyConnected (pullback.snd p (spMap c)) := by
  have hPA : IsPullback (pullback.fst p (spMap φ)) (pullback.snd p (spMap φ)) p (spMap φ) :=
    .of_hasPullback _ _
  haveI : Smooth (pullback.snd p (spMap φ)) := MorphismProperty.of_isPullback hPA ‹_›
  haveI : IsProper (pullback.snd p (spMap φ)) := MorphismProperty.of_isPullback hPA ‹_›
  haveI : Flat (pullback.snd p (spMap φ)) := inferInstance
  let eA : Sp A ⟶ pullback p (spMap φ) :=
    pullback.lift (spMap φ ≫ e) (𝟙 _) (by rw [Category.assoc, hs]; simp)
  have heA : eA ≫ pullback.snd p (spMap φ) = 𝟙 _ := pullback.lift_snd _ _ _

  have hW : IsPullback (pullback.fst (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)))
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)))
      (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)) := .of_hasPullback _ _
  have hbot : spMap (IsLocalRing.residue A) ≫ spMap φ = spMap b ≫ spMap a := by
    rw [spMap_comp_spMap, spMap_comp_spMap, hb]
  have hW' := hW.paste_horiz hPA
  rw [hbot] at hW'
  obtain ⟨u, hu⟩ := exists_isPullback_left hW' (.of_hasPullback p (spMap a))
  haveI : Smooth (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    MorphismProperty.of_isPullback hW ‹_›
  haveI : GeometricallyConnected
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    MorphismProperty.of_isPullback hu hE
  have hGI : GeometricallyIntegral
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    GlobalTheory.geometricallyIntegral_of_smooth _
  haveI hA : IsIso (pullback.snd p (spMap φ)).appTop :=
    isIso_appTop_of_closedFibre A _ _ eA heA inferInstance inferInstance hGI

  have hL : IsPullback (pullback.fst (pullback.snd p (spMap φ)) (spMap j))
      (pullback.snd (pullback.snd p (spMap φ)) (spMap j))
      (pullback.snd p (spMap φ)) (spMap j) := .of_hasPullback _ _
  haveI : Flat (spMap j) := Flat.SpecMap_iff.2 hj
  haveI hL1 : IsIso (pullback.snd (pullback.snd p (spMap φ)) (spMap j)).appTop :=
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback hL
  have hbot' : spMap j ≫ spMap φ = spMap d ≫ spMap c := by
    rw [spMap_comp_spMap, spMap_comp_spMap, hd]
  have hL' := hL.paste_horiz hPA
  rw [hbot'] at hL'
  obtain ⟨w, hw⟩ := exists_isPullback_left hL' (.of_hasPullback p (spMap c))
  haveI : Flat (spMap d) := Flat.SpecMap_iff.2 (by
    algebraize [d]
    exact RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : Surjective (spMap d) := by
    refine ⟨fun x => ?_⟩
    have y : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  haveI hK : IsIso (pullback.snd p (spMap c)).appTop :=
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback_of_surjective hw
  exact geometricallyConnected_of_isIso_appTop K _ _ inferInstance inferInstance hK

theorem geometricallyConnected_of_localDomain {k B A E K : Type} [CommRing k] [CommRing B]
    [IsDomain B] [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field E] [Field K]
    [Algebra B K] [IsFractionRing B K] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (e : Sp k ⟶ X) (hs : e ≫ p = 𝟙 _) [Smooth p] [IsProper p] (q : k →+* B) (ψ : B →+* A)
    (hψ : Function.Injective ψ) (a : k →+* E) (b : E →+* IsLocalRing.ResidueField A)
    (hb : b.comp a = (IsLocalRing.residue A).comp (ψ.comp q))
    (hE : GeometricallyConnected (pullback.snd p (spMap a))) :
    GeometricallyConnected (pullback.snd p (spMap ((algebraMap B K).comp q))) := by
  have hinj : Function.Injective ((algebraMap A (FractionRing A)).comp ψ) :=
    (IsFractionRing.injective A (FractionRing A)).comp hψ
  refine geometricallyConnected_of_local (A := A) (E := E) (L := FractionRing A) X p e hs (ψ.comp q)
    a b hb hE (algebraMap A (FractionRing A)) (RingHom.flat_algebraMap_iff.2 inferInstance) _
    (IsFractionRing.lift hinj) ?_
  ext r
  simp only [RingHom.comp_apply]
  exact IsFractionRing.lift_algebraMap hinj (q r)

theorem stableUnderGeneralization_geometricallyConnected_fibre :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
      (e : Sp k ⟶ X), e ≫ p = 𝟙 _ → Smooth p → IsProper p →
      StableUnderGeneralization {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ X p e hs _ _ x y hyx hx
  have hle : y.asIdeal ≤ x.asIdeal := (PrimeSpectrum.le_iff_specializes y x).2 hyx
  have hq : Function.Surjective (Ideal.Quotient.mk y.asIdeal) := Ideal.Quotient.mk_surjective
  obtain ⟨Q, hQ, hcomap⟩ : ∃ Q : Ideal (k ⧸ y.asIdeal), ∃ _ : Q.IsPrime,
      x.asIdeal = Q.comap (Ideal.Quotient.mk y.asIdeal) := by
    refine ⟨x.asIdeal.map (Ideal.Quotient.mk y.asIdeal),
      Ideal.map_isPrime_of_surjective hq (by rw [Ideal.mk_ker]; exact hle), ?_⟩
    rw [Ideal.comap_map_of_surjective _ hq, eq_comm, sup_eq_left]
    refine le_trans ?_ hle
    rw [show Ideal.comap (Ideal.Quotient.mk y.asIdeal) ⊥ = RingHom.ker (Ideal.Quotient.mk y.asIdeal)
      from rfl, Ideal.mk_ker]
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_localization Q.primeCompl_le_nonZeroDivisors
  have := geometricallyConnected_of_localDomain (K := y.asIdeal.ResidueField) X p e hs
    (Ideal.Quotient.mk y.asIdeal) (algebraMap (k ⧸ y.asIdeal) (Localization.AtPrime Q))
    (IsLocalization.injective _ Q.primeCompl_le_nonZeroDivisors)
    (algebraMap k x.asIdeal.ResidueField)
    (Ideal.ResidueField.map x.asIdeal Q (Ideal.Quotient.mk y.asIdeal) hcomap)
    (by
      ext r
      simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
      rfl) hx
  exact this

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointIntegralLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem model_point_extends_to_integers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : FiniteDimensional ℚ c.F) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (f : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f → ∃ yt : Sp (𝓞 F) ⟶ Y.X, spMap (algebraMap (𝓞 F) F) ≫ yt = y ≫ Y.j :=
  @PositivityTheory.Xgn.integral_point_extends_model

end GlobalTheory.CompanionTheory.Ar
end

