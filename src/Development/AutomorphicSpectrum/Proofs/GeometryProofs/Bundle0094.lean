module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JNormal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicConstantsInRange
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagConst

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem exists_C_eq_of_isAlgebraic {k I : Type} [Field k] (P : MvPolynomial I k) (h : IsAlgebraic k P) :
    ∃ p : k, MvPolynomial.C p = P := by
  by_cases h0 : P = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨r, hr, hd⟩ := h.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)
  have hu : IsUnit P := isUnit_of_dvd_unit hd ((IsUnit.mk0 r hr).map (algebraMap k _))
  obtain ⟨p, -, hp⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu
  exact ⟨p, hp.symm⟩

theorem mem_range_of_isAlgebraic {k L I : Type} [Field k] [Field L] [Algebra k L] (x : I → L)
    (hx : AlgebraicIndependent k x) (ht : IntermediateField.adjoin k (Set.range x) = ⊤) (a : L)
    (ha : IsAlgebraic k a) : a ∈ (algebraMap k L).range := by
  let g : MvPolynomial I k →ₐ[k] L := MvPolynomial.aeval x
  have hg : Function.Injective g := hx
  letI : Algebra (MvPolynomial I k) L := g.toRingHom.toAlgebra
  have hmap : ∀ P : MvPolynomial I k, algebraMap (MvPolynomial I k) L P = g P := fun _ => rfl
  haveI : IsScalarTower k (MvPolynomial I k) L := IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  haveI : FaithfulSMul (MvPolynomial I k) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  haveI : IsFractionRing (MvPolynomial I k) L := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    have hz : z ∈ IntermediateField.adjoin k (Set.range x) := ht ▸ IntermediateField.mem_top
    obtain ⟨r, s, e⟩ := (IntermediateField.mem_adjoin_range_iff k x z).1 hz
    exact ⟨r, s, e⟩
  have hi : IsIntegral (MvPolynomial I k) a := (ha.isIntegral).tower_top
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hPa : IsAlgebraic k P := by
    rw [← isAlgebraic_algHom_iff g hg, ← hmap, hP]
    exact ha
  obtain ⟨p, rfl⟩ := exists_C_eq_of_isAlgebraic P hPa
  refine ⟨p, ?_⟩
  rw [← hP, hmap]
  exact (g.commutes p).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_cst₀ {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
    {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) :
    ∃ cst₀ : c.F →+* 𝔐.Ω₀, 𝔐.fn.comp cst₀ = 𝔐.cst ∧
      𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  let b₀ : 𝓞 c.F →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀ := (Spec.map_preimage _).symm
  have hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      have hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over
      have hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀ := by
        rw [← Spec.map_comp]; rfl
      rw [hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]
    have := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    simpa using this
  have hinj : Function.Injective b₀ := by
    intro u v huv
    have h := congrArg 𝔐.fn huv
    have hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w) := fun w => RingHom.congr_fun hc w
    rw [hu, hu] at h
    exact IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)
  let cst₀ : c.F →+* 𝔐.Ω₀ := IsFractionRing.lift hinj
  have hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀ := by
    ext w
    exact IsFractionRing.lift_algebraMap hinj w
  refine ⟨cst₀, ?_, by rw [hl, hb]⟩
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
  rw [RingHom.comp_assoc, hl, hc]

theorem isAlgebraic_mem_cst_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), SplitComps Y → Fl.deg = 1 → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ 𝔐.cst.range := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 Fl hS hdeg a ha
  obtain ⟨cst₀, h1, h2⟩ := exists_cst₀ 𝔐
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  letI : Algebra 𝔐.Ω₀ Ω := 𝔐.fn.toAlgebra
  obtain ⟨-, u, -, -, -, -, hdiag, hup, -, hind, -, hfin⟩ := Fl.generic
  rw [hdeg] at hfin
  let x : (Σ q : CMType H ⊕ CMType H, {lk : Fin (labelRk D q) × Fin (labelRk D q) // lk.2 < lk.1}) → Ω :=
    fun q => u q.1 q.2.1.1 q.2.1.2
  let A := IntermediateField.adjoin 𝔐.Ω₀
    (Set.range fun q : Σ σ, Fin (labelRk D σ) × Fin (labelRk D σ) => u q.1 q.2.1 q.2.2)
  have hA : A = ⊤ := by
    have hb := Subalgebra.bot_eq_top_of_finrank_eq_one hfin
    refine eq_top_iff.2 fun z _ => ?_
    have hz : z ∈ (⊥ : Subalgebra A Ω) := hb ▸ Algebra.mem_top
    obtain ⟨w, rfl⟩ := Algebra.mem_bot.1 hz
    exact w.2
  have ht : IntermediateField.adjoin 𝔐.Ω₀ (Set.range x) = ⊤ := by
    refine eq_top_iff.2 (hA ▸ ?_)
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨σ, l', k⟩, rfl⟩
    rcases lt_trichotomy l' k with h | h | h
    · show u σ l' k ∈ _
      rw [hup σ l' k h]
      exact zero_mem _
    · subst h
      show u σ l' l' ∈ _
      rw [hdiag σ l']
      exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l', k), h⟩⟩, rfl⟩
  have hal : IsAlgebraic 𝔐.Ω₀ a := by
    haveI : CharZero 𝔐.Ω₀ := charZero_of_injective_ringHom cst₀.injective
    exact ha.extendScalars (RingHom.injective_int _)
  obtain ⟨a₀, rfl⟩ := mem_range_of_isAlgebraic x hind ht a hal
  have ha₀ : IsAlgebraic ℤ a₀ :=
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℤ 𝔐.Ω₀ Ω) (algebraMap 𝔐.Ω₀ Ω).injective).1 ha
  obtain ⟨k, rfl⟩ := hS 𝔐.Ω₀ 𝔐.ξ₀ cst₀ 𝔐.gen₀ h2 a₀ ha₀
  exact ⟨k, (RingHom.congr_fun h1 k).symm⟩

end GlobalTheory.CompanionTheory.Ar.FlagConst
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarCommonCover
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.JoinModel

theorem exists_normal_common_model : ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (y₁ : (Σ k, ι₁ k) → Ω₁) (y₂ : (Σ k, ι₂ k) → Ω₂) (d : ℕ) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), IsArithVar (mCoordIdeal y₁) d → IsArithVar (mCoordIdeal y₂) d → Birational y₁ → Birational y₂ → FiniteDimensional i₁.fieldRange Ω → FiniteDimensional i₂.fieldRange Ω → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → ι₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → ι₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (y : (Σ k, ι k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), IsBlockMap κ₁ v₁ ∧ IsBlockMap κ₂ v₂ ∧ y ∘ v₁ = (fun p => i₁ (y₁ p)) ∧ y ∘ v₂ = (fun p => i₂ (y₂ p)) ∧ IsArithVar (mCoordIdeal y) d ∧ Birational y ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂ ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = Module.finrank i₁.fieldRange Ω ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) = Module.finrank i₂.fieldRange Ω :=
  @PositivityTheory.UnitarySelfGeneration.j_normal_of GlobalTheory.T.finite_extension_coords_compare

end GlobalTheory.CompanionTheory.Ar.JoinModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordValuationBoundLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]

theorem valAt_mul {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} {a b : Ω} {r s : R}
    (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, t, rfl, rfl⟩ := ha
  obtain ⟨_, u, rfl, rfl⟩ := hb
  exact ⟨h, t * u, map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_one {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) : ValAt ξ z 1 1 :=
  ⟨h, 1, map_one _, map_one _⟩

theorem valAt_prod {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) {K : Type} (S : Finset K)
    (a : K → Ω) (r : K → R) (ha : ∀ k, ValAt ξ z (a k) (r k)) :
    ValAt ξ z (∏ k ∈ S, a k) (∏ k ∈ S, r k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using valAt_one h
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk]
    exact valAt_mul (ha k) ih

theorem inv_mem_regAt_of_isUnit {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω} {r : R}
    (ha : ValAt ξ z a r) (hr : IsUnit r) : a⁻¹ ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨_, s, rfl, rfl⟩ := ha
  obtain ⟨u, rfl⟩ : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s hr
  refine ⟨(u⁻¹ : (X.presheaf.stalk (centre z))ˣ).1, eq_inv_of_mul_eq_one_left ?_⟩
  rw [← map_mul, Units.inv_mul, map_one]

theorem bestChart_finite : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L)
    (v : FinitePlace L) (A : Type) [CommRing A] [IsLocalRing A] [Algebra A L] (zA : Sp A ⟶ X),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    (∀ r : A, v (algebraMap A L r) ≤ 1) → (∀ r : A, v (algebraMap A L r) = 1 → IsUnit r) →
    CoordsAt ξ y (spMap (algebraMap A L) ≫ zA) w →
    ∃ (c : (k : K) → J k) (h : genPt ξ ⤳ centre zA), (∀ k, w ⟨k, c k⟩ ≠ 0) ∧
      (∀ k i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c k⟩)) ∧
      InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zA, h⟩ := by
  intro X Ω _ ξ K _ J _ y L _ _ w v A _ _ _ zA hq hT hle hun hC

  have hmax : ∀ k, ∃ c : J k, w ⟨k, c⟩ ≠ 0 ∧ ∀ i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c⟩) := by
    intro k
    obtain ⟨u, hu⟩ := hC.1 k
    haveI : Nonempty (J k) := ⟨u⟩
    obtain ⟨c, hc⟩ := Finite.exists_max (fun i => v (w ⟨k, i⟩))
    refine ⟨c, ?_, hc⟩
    have h0 : 0 < v (w ⟨k, u⟩) := FinitePlace.pos_iff.2 hu.ne_zero
    exact FinitePlace.pos_iff.1 (h0.trans_le (hc u))
  choose c hc0 hcm using hmax
  have h := hq (centre zA)
  refine ⟨c, h, hc0, hcm, ?_⟩
  set x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩ with hx
  set zL : Sp L ⟶ X := spMap (algebraMap A L) ≫ zA with hzL
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hC.2 k (c k) (isUnit_iff_ne_zero.2 (hc0 k))).1
  have hxc : x c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k

  obtain ⟨c', hc', hreg⟩ := hT.cover ⟨centre zA, h⟩

  obtain ⟨s, hs⟩ := hreg c
  set r : A := (Scheme.stalkClosedPointTo zA).hom s with hr
  have hvA : ValAt ξ zA (x c / x c') r := ⟨h, s, hs, rfl⟩
  have hvL : ValAt ξ zL (x c / x c') (algebraMap A L r) := LieTangent.valAt_base hT.gen _ hvA

  have hL : genPt ξ ⤳ centre zL := hq _
  have hk : ∀ k, ∃ ρ : L, ValAt ξ zL (y ⟨k, c' k⟩ / y ⟨k, c k⟩) ρ ∧ w ⟨k, c' k⟩ = ρ * w ⟨k, c k⟩ :=
    fun k => (hC.2 k (c k) (isUnit_iff_ne_zero.2 (hc0 k))).2 (c' k)
  choose ρ hρ hρw using hk
  have hprod : ValAt ξ zL (x c' / x c) (∏ k, ρ k) := by
    have e : x c' / x c = ∏ k, y ⟨k, c' k⟩ / y ⟨k, c k⟩ := (Finset.prod_div_distrib _ _).symm
    rw [e]
    exact valAt_prod hL _ _ _ fun k => hρ k
  have hone : algebraMap A L r * ∏ k, ρ k = 1 := by
    have e : x c / x c' * (x c' / x c) = 1 := by field_simp
    have := valAt_mul hvL hprod
    rw [e] at this
    exact LieTangent.valAt_unique hT.gen this (valAt_one hL)

  have hρ1 : ∀ k, v (ρ k) ≤ 1 := by
    intro k
    have e := congrArg v (hρw k)
    rw [map_mul] at e
    have hp : 0 < v (w ⟨k, c k⟩) := FinitePlace.pos_iff.2 (hc0 k)
    have := hcm k (c' k)
    rw [e] at this
    exact le_of_mul_le_mul_right (by simpa using this) hp
  have hP : v (∏ k, ρ k) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one₀ (fun _ _ => by positivity) fun k _ => hρ1 k
  have hsize : v (algebraMap A L r) = 1 := by
    have e := congrArg v hone
    rw [map_mul, map_one] at e
    refine le_antisymm (hle r) ?_
    have h0 : 0 ≤ v (algebraMap A L r) := by positivity
    nlinarith
  have hinv : (x c / x c')⁻¹ ∈ regAt ξ ⟨centre zA, h⟩ :=
    inv_mem_regAt_of_isUnit h hvA (hun r hsize)
  refine ⟨hxc, fun d => ?_⟩
  have e : x d / x c = x d / x c' * (x c / x c')⁻¹ := by field_simp
  rw [e]
  exact mul_mem (hreg d) hinv

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtComplexEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {L L' : Type} [Field L] [Field L']

theorem centre_field (ψ : L →+* L') (z : Sp L ⟶ X) : centre (spMap ψ ≫ z) = centre z := by
  show z (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint L')) = z (IsLocalRing.closedPoint L)
  exact congrArg z (Subsingleton.elim _ _)

theorem centre_specializes (ψ : L →+* L') (z : Sp L ⟶ X) : centre (spMap ψ ≫ z) ⤳ centre z :=
  specializes_of_eq (centre_field ψ z)


set_option backward.isDefEq.respectTransparency false in
theorem stalk_comp (ψ : L →+* L') (z : Sp L ⟶ X) :
    X.presheaf.stalkSpecializes (centre_specializes ψ z) ≫ Scheme.stalkClosedPointTo (spMap ψ ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (spMap ψ ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

theorem valAt_field {ξ : Sp Ω ⟶ X} (ψ : L →+* L') {z : Sp L ⟶ X} {a : Ω} {r : L}
    (h : ValAt ξ z a r) : ValAt ξ (spMap ψ ≫ z) a (ψ r) := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  have h' : genPt ξ ⤳ centre (spMap ψ ≫ z) := by rw [centre_field]; exact h1
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalk_comp ψ z)

theorem coordsAt_field {ξ : Sp Ω ⟶ X} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (ψ : L →+* L')
    {z : Sp L ⟶ X} {w : (Σ k, J k) → L} (h : CoordsAt ξ y z w) :
    CoordsAt ξ y (spMap ψ ≫ z) fun p => ψ (w p) := by
  refine ⟨fun k => (h.1 k).imp fun c hc => hc.map ψ, fun k c hc => ?_⟩
  have hc' : IsUnit (w ⟨k, c⟩) := by
    rw [isUnit_iff_ne_zero] at hc ⊢
    exact fun h0 => hc (by simp [h0])
  refine ⟨(h.2 k c hc').1, fun i => ?_⟩
  obtain ⟨r, hr, e⟩ := (h.2 k c hc').2 i
  exact ⟨ψ r, valAt_field ψ hr, by simp only [e, map_mul]⟩

theorem coordsAt_embedding : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ),
    CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w →
    CoordsAt ξ y (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (fun p => σ (w p)) := by
  intro X Ω _ ξ K J y L _ _ w z σ h
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ z := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  rw [e]
  exact coordsAt_field σ h

end GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
  {z : Sp R ⟶ X}

theorem val_spec {a : Ω} {r : R} (h : ValAt ξ z a r) : ∃ hz : genPt ξ ⤳ centre z, a ∈ regAt ξ ⟨centre z, hz⟩ := by
  obtain ⟨hz, s, hs, -⟩ := h
  exact ⟨hz, s, hs⟩

theorem val_exists {a : Ω} {hz : genPt ξ ⤳ centre z} (h : a ∈ regAt ξ ⟨centre z, hz⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := h
  exact ⟨_, hz, s, hs, rfl⟩

theorem val_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hz, s, hs, rfl⟩ := h
  obtain ⟨hz', s', hs', rfl⟩ := h'
  have : s = s' := hξ.inj ⟨centre z, hz⟩ (hs.trans hs'.symm)
  rw [this]

theorem val_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, ht, rfl⟩ := h
  obtain ⟨hz', t', ht', rfl⟩ := h'
  exact ⟨hz, t * t', by rw [map_mul, ht]; rw [← ht'], map_mul _ _ _⟩

theorem val_add {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, t, ht, rfl⟩ := h
  obtain ⟨hz', t', ht', rfl⟩ := h'
  exact ⟨hz, t + t', by rw [map_add (f := _), ht]; rw [← ht'], map_add _ _ _⟩

theorem val_nat (hz : genPt ξ ⤳ centre z) (n : ℕ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_natCast _ n, map_natCast _ n⟩

theorem val_one (hz : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) := by
  simpa using val_nat (ξ := ξ) (z := z) hz 1

theorem val_zero (hz : genPt ξ ⤳ centre z) : ValAt ξ z (0 : Ω) (0 : R) := by
  simpa using val_nat (ξ := ξ) (z := z) hz 0

theorem val_inv {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : ValAt ξ z a⁻¹ (↑r⁻¹ : R) := by
  obtain ⟨hz, s, hs, hr⟩ := h
  have hu : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (hr ▸ r.isUnit)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨hz, ↑u⁻¹, ?_, ?_⟩
  · rw [← hs, map_units_inv]
  · have : (Units.map (Scheme.stalkClosedPointTo z).hom.toMonoidHom u) = r := Units.ext hr
    rw [← this]
    exact congrArg Units.val (map_inv (Units.map (Scheme.stalkClosedPointTo z).hom.toMonoidHom) u)

theorem val_ne_zero (hξ : IsCptGen ξ) [Nontrivial R] {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : a ≠ 0 := by
  rintro rfl
  obtain ⟨hz, -⟩ := val_spec h
  have := val_unique hξ h (val_zero hz)
  exact r.ne_zero this

theorem val_inv₀ {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hr : r ≠ 0) (h : ValAt ξ z a r) :
    ValAt ξ z a⁻¹ r⁻¹ := by
  have := val_inv (r := Units.mk0 r hr) h
  simpa using this

theorem val_zpow {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hr : r ≠ 0) (h : ValAt ξ z a r) (n : ℤ) :
    ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, -⟩ := val_spec h
  have hp : ∀ k : ℕ, ∀ {b : Ω} {s : F}, ValAt ξ z b s → ValAt ξ z (b ^ k) (s ^ k) := by
    intro k b s hb
    induction k with
    | zero => simpa using val_one hz
    | succ k ih => rw [pow_succ, pow_succ]; exact val_mul ih hb
  rcases n with k | k
  · simpa using hp k h
  · simpa [zpow_negSucc] using val_inv₀ (pow_ne_zero _ hr) (hp (k + 1) h)

theorem in_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
  have h1 := fun k => hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (h1 k).1, fun c' => ?_⟩
  simp only
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (h1 k).2 (c' k)
  obtain ⟨hz', s, hs, -⟩ := hr
  exact ⟨s, hs⟩

theorem coordsAt_smul {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (hw : CoordsAt ξ y z w) : CoordsAt ξ y z (fun p => c p.1 * w p) := by
  refine ⟨fun k => ?_, fun k c' hu => ?_⟩
  · obtain ⟨c', h'⟩ := hw.1 k
    exact ⟨c', (isUnit_iff_ne_zero.2 (hc k)).mul h'⟩
  · have hu' : IsUnit (w ⟨k, c'⟩) := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hu.ne_zero)
    obtain ⟨h1, h2⟩ := hw.2 k c' hu'
    refine ⟨h1, fun i => ?_⟩
    obtain ⟨r, hr, hr'⟩ := h2 i
    refine ⟨r, hr, ?_⟩
    show c k * w ⟨k, i⟩ = r * (c k * w ⟨k, c'⟩)
    rw [hr']; ring

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationHolUnifTangentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_hol_unif_tangent : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A] (z : Sp ℂ ⟶ Sp R) (φ : A.left ⟶ G.left) (_ : IsGrpPullback A G z φ) (g : ℕ) (Lb : LB A.left) (u : HolUnif A Lb g) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (c : Fin g → ℂ) (v' : epsR ℂ ⟶ A), v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left → u.IsDiff c v' → ∀ (V : G.left.Opens) (hV : IsAffineOpen V) (f : Γ(G.left, V)) (w : Fin g → ℂ), ⊤ ≤ ((u.ex w).left ≫ φ) ⁻¹ᵁ V → fderiv ℂ (fun x => valAt' ((u.ex x).left ≫ φ) V f) w c = valAt' ((u.ex w).left ≫ φ) V (der v₀ hv₀ hV f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der | exact GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der | (intros; apply GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusGeneratorCorrespondenceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_generator_correspondence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p) → ∀ (j : t.PP.L.ι) (h : pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j ≤ secZ t.G x p ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j)), ((secZ t.G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_one | exact GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_one <;> assumption)
end

