module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DegreeLatticePrimeScaling
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleFinitelyGenerated
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.Geo

theorem chartBundle_lat_fg : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)) (c : ι), x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k :=
  PositivityTheory.Xgn.chart_lattice_finitely_generated

end GlobalTheory.CompanionTheory.Ar.Geo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingMemAfterMonomialScaling
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap

theorem pow_mul_mem_chartRing_mseg : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (s t : ∀ k, J k), mseg y s ≠ 0 → mseg y t ≠ 0 → ∀ a ∈ chartRing o (mseg y) s, ∃ n : ℕ, (mseg y s / mseg y t) ^ n * a ∈ chartRing o (mseg y) t := by
  intro o _ Ω _ _ K _ J y s t hs _ a ha
  exact exists_pow_mul_mem_chartRing (mseg y) s t hs ha

end GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeHostAutPermutation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Label

theorem automorphism_permutes_labels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (g : HostAut H), ∃ π : CMType H ≃ CMType H, (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) ∧ ∀ s, labelEmb c (Sum.map π π s) = (labelEmb c s).comp g.s.toRingHom :=
  @PositivityTheory.UnitarySelfGeneration.cm_type_label_twist_permutation

end GlobalTheory.CompanionTheory.Ar.Label
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocks
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AddBlockMulti

open GlobalTheory.CompanionTheory.Ar.ProjCoord

section Reindex

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem inChart_comp_equiv (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ κ' : Type} (e : κ' ≃ κ) (x : κ → Ω) (c : κ')
    (p : Cpt ξ) : InChart ξ (x ∘ e) c p ↔ InChart ξ x (e c) p := by
  unfold InChart
  refine and_congr Iff.rfl ⟨fun h c' => ?_, fun h c' => h _⟩
  simpa using h (e.symm c')

theorem coordTie_comp_equiv {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type}
    (e : κ' ≃ κ) {x : κ → Ω} (h : CoordTie o ξ x) : CoordTie o ξ (x ∘ e) := by
  have hr : ∀ c : κ', (Set.range fun j => (x ∘ e) j / (x ∘ e) c) = Set.range fun j => x j / x (e c) := fun c =>
    e.surjective.range_comp (fun j => x j / x (e c))
  refine ⟨h.gen, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (inChart_comp_equiv ξ e x _ p).2 (by simpa using hc)⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) hc
    refine ⟨U, hU, fun q => ?_⟩
    rw [hq q]
    exact exists_congr fun hh => (inChart_comp_equiv ξ e x c ⟨q, hh⟩).symm
  · rw [hr c, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (inChart_comp_equiv ξ e x c p).symm Iff.rfl

end Reindex

section OpenImm

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
variable (ζ : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]

theorem specializes_of_openImm {y : Y} (h : genPt (ζ ≫ f) ⤳ f y) : genPt ζ ⤳ y := by
  have e2 : genPt (ζ ≫ f) = f (genPt ζ) := Scheme.Hom.comp_apply _ _ _
  rw [e2] at h
  exact f.isOpenEmbedding.isInducing.specializes_iff.1 h

theorem inChart_push {κ : Type} (x : κ → Ω) (c : κ) (p : Cpt ζ) :
    InChart (ζ ≫ f) x c (push ζ f p) ↔ InChart ζ x c p := by
  unfold InChart
  rw [regAt_push]

variable {ζ f}

theorem exists_push (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (q : Cpt (ζ ≫ f)) :
    ∃ p : Cpt ζ, push ζ f p = q := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨y, rfl⟩ := hR q hq
  exact ⟨⟨y, specializes_of_openImm ζ f hq⟩, rfl⟩

theorem coordTie_push {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (h : CoordTie o ζ x) : CoordTie o (ζ ≫ f) x := by
  refine ⟨⟨?_, fun q => ?_⟩, fun q => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · rw [Scheme.stalkClosedPointTo_comp ζ f]
    have hb : Function.Bijective (f.stalkMap (ζ (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    exact h.gen.bij.comp hb
  · obtain ⟨p, rfl⟩ := exists_push hR q
    exact genMap_push_injective ζ f p (h.gen.inj p)
  · obtain ⟨p, rfl⟩ := exists_push hR q
    obtain ⟨c, hc⟩ := h.cover p
    exact ⟨c, (inChart_push ζ f x c p).2 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    refine ⟨f ''ᵁ U, hU.image_of_isOpenImmersion f, fun q => ⟨?_, ?_⟩⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h1, h2⟩ := (hq y).1 hy
      exact ⟨(push ζ f ⟨y, h1⟩).2, (inChart_push ζ f x c ⟨y, h1⟩).2 h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := hR q h1
      have h1' := specializes_of_openImm ζ f h1
      exact ⟨y, (hq y).2 ⟨h1', (inChart_push ζ f x c ⟨y, h1'⟩).1 h2⟩, rfl⟩
  · rw [h.ring c hc a]
    constructor
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push hR q
      rw [regAt_push]
      exact H p ((inChart_push ζ f x c p).1 hq)
    · intro H p hp
      have := H (push ζ f p) ((inChart_push ζ f x c p).2 hp)
      rwa [regAt_push] at this

theorem coordTie_of_push {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (h : CoordTie o (ζ ≫ f) x) : CoordTie o ζ x := by
  refine ⟨⟨?_, fun p => ?_⟩, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · have hb : Function.Bijective (f.stalkMap (ζ (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    have h1 := h.gen.bij
    rw [Scheme.stalkClosedPointTo_comp ζ f] at h1
    exact (Function.Bijective.of_comp_iff _ hb).1 h1
  · have h1 := h.gen.inj (push ζ f p)
    rw [genMap_push] at h1
    have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
    exact (Function.Injective.of_comp_iff' _ hb).1 h1
  · obtain ⟨c, hc⟩ := h.cover (push ζ f p)
    exact ⟨c, (inChart_push ζ f x c p).1 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    have hle : U ≤ f.opensRange := fun q hqU => hR q ((hq q).1 hqU).1
    refine ⟨f ⁻¹ᵁ U, ?_, fun y => ⟨fun hy => ?_, ?_⟩⟩
    · have e : f ''ᵁ (f ⁻¹ᵁ U) = U := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
        exact inf_eq_right.2 hle
      rw [← f.isAffineOpen_iff_of_isOpenImmersion, e]
      exact hU
    · obtain ⟨h1, h2⟩ := (hq (f y)).1 hy
      have h1' := specializes_of_openImm ζ f h1
      exact ⟨h1', (inChart_push ζ f x c ⟨y, h1'⟩).1 h2⟩
    · rintro ⟨h1, h2⟩
      exact (hq (f y)).2 ⟨(push ζ f ⟨y, h1⟩).2, (inChart_push ζ f x c ⟨y, h1⟩).2 h2⟩
  · rw [h.ring c hc a]
    constructor
    · intro H p hp
      have := H (push ζ f p) ((inChart_push ζ f x c p).2 hp)
      rwa [regAt_push] at this
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push hR q
      rw [regAt_push]
      exact H p ((inChart_push ζ f x c p).1 hq)

end OpenImm

section Model

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem spec_int_hom_ext (g g' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of ℤ)) : g = g' := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage g']
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_int _ _)

theorem exists_openModel {κ : Type} {x : κ → Ω} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : CoordTie ℤ ξ x) :
    ∃ (Y : Scheme.{0}) (ζ : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (_ : IsOpenImmersion f), ζ ≫ f = ξ ∧
      (∀ q : X, genPt ξ ⤳ q → q ∈ Set.range f) ∧ ∀ q : Y, genPt ζ ⤳ q := by
  let W : X.Opens := sSup {U : X.Opens | ∀ q ∈ U, genPt ξ ⤳ q}
  have hW : ∀ q ∈ W, genPt ξ ⤳ q := by
    intro q hq
    obtain ⟨U, hU, hqU⟩ := TopologicalSpace.Opens.mem_sSup.1 hq
    exact hU q hqU
  have hC : ∀ q : X, genPt ξ ⤳ q → q ∈ W := by
    intro q hq
    obtain ⟨c, hc⟩ := h.cover ⟨q, hq⟩
    obtain ⟨U, -, hU⟩ := h.affine c hc.1
    refine TopologicalSpace.Opens.mem_sSup.2 ⟨U, fun r hr => ((hU r).1 hr).1, (hU q).2 ⟨hq, hc⟩⟩
  have hr : Set.range ξ ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    subst hz
    rw [Scheme.Opens.range_ι]
    exact hC _ specializes_rfl
  have e : IsOpenImmersion.lift W.ι ξ hr ≫ W.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  have hR : ∀ q : X, genPt ξ ⤳ q → q ∈ Set.range W.ι := fun q hq => by
    rw [Scheme.Opens.range_ι]
    exact hC q hq
  refine ⟨W, IsOpenImmersion.lift W.ι ξ hr, W.ι, inferInstance, e, hR, fun q => ?_⟩
  refine specializes_of_openImm _ W.ι ?_
  rw [e]
  exact hW _ q.2

theorem coordTie_join {κ κ' : Type} [Finite κ] [Finite κ'] {x : κ → Ω} {w : κ' → Ω}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : CoordTie ℤ ξ x) (hw : ∀ p : Cpt ξ, ∃ l, InChart ξ w l p) :
    CoordTie ℤ ξ (joinCo (RingHom.id Ω) x w) := by
  obtain ⟨Y, ζ, f, _, rfl, hR, hall⟩ := exists_openModel h
  let M : PModel ℤ x :=
    { X := Y
      ξ := ζ
      s := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Int.castRingHom _))
      hover := spec_int_hom_ext _ _
      all := hall
      tie := coordTie_of_push hR h }
  refine coordTie_push hR (_root_.GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts ℤ Ω κ x M κ' w fun p => ?_)
  obtain ⟨l, hl⟩ := hw (push ζ f p)
  exact ⟨l, (inChart_push ζ f w l p).1 hl⟩

end Model

theorem add_block_multi : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type)
    [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (K' : Type) [Fintype K']
    (J' : K' → Type) [∀ k, Fintype (J' k)] (s : (Σ k, J' k) → Ω),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    (∀ (k : K') (p : Cpt ξ), ∃ i, InChart ξ (fun i' : J' k => s ⟨k, i'⟩) i p) →
    CoordTie ℤ ξ fun c' : (k : K ⊕ K') → Sum.elim J J' k =>
      (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ := by
  intro X Ω _ ξ K _ J _ y K' _ J' _ s h hs
  have hw : ∀ p : Cpt ξ, ∃ i, InChart ξ (fun c : (k : K') → J' k => ∏ k, s ⟨k, c k⟩) i p := by
    intro p
    choose i hi using fun k => hs k p
    refine ⟨i, Finset.prod_ne_zero_iff.2 fun k _ => (hi k).1, fun c' => ?_⟩
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => (hi k).2 (c' k)
  have h2 := coordTie_join (κ := (k : K) → J k) (κ' := (k : K') → J' k) h hw
  exact coordTie_comp_equiv (Equiv.sumPiEquivProdPi (Sum.elim J J')) h2

end GlobalTheory.CompanionTheory.Ar.AddBlockMulti
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpElementDividesPrimeSq
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.KappaDvd

theorem kappa_dvd_sq : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [IsIntegrallyClosed A] [CharZero Ω] (p : ℕ) [Fact p.Prime] (κ : A),
    IsCp p (algebraMap A Ω κ) → κ ∣ (p : A) ^ 2 := by
  intro A Ω _ _ _ _ _ _ _ p hp κ h
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  unfold IsCp at h
  split_ifs at h with h2
  · subst h2
    have : κ = 4 := hinj (by rw [h]; exact (map_ofNat _ 4).symm)
    subst this
    exact ⟨1, by norm_num⟩
  · obtain ⟨ζ, hζ, hκ⟩ := h
    have hp1 : 1 < p := hp.out.one_lt
    have hint : IsIntegral A ζ := by
      refine ⟨Polynomial.X ^ p - 1, Polynomial.monic_X_pow_sub_C 1 hp.out.ne_zero, ?_⟩
      simp [hζ.pow_eq_one]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hz' : IsPrimitiveRoot z p := by
      rw [← hz] at hζ
      exact hζ.of_map_of_injective hinj
    have hκz : κ = z - 1 := hinj (by rw [hκ, map_sub, map_one, hz])
    have hsum : ∑ i ∈ Finset.range p, z ^ i = 0 := hz'.geom_sum_eq_zero hp1
    have hp_eq : (p : A) = ∑ i ∈ Finset.range p, (1 - z ^ i) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    have hdvd : κ ∣ (p : A) := by
      rw [hp_eq, hκz]
      refine Finset.dvd_sum fun i _ => ?_
      have := sub_dvd_pow_sub_pow z 1 i
      rw [one_pow] at this
      rw [show (1 : A) - z ^ i = -(z ^ i - 1) by ring]
      exact dvd_neg.mpr this
    exact hdvd.trans (dvd_pow_self _ two_ne_zero)

end GlobalTheory.CompanionTheory.Ar.HT.KappaDvd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeLatticesPrimeCompare
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem exists_pow_mul_mem_chart {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (m : ℕ) (τ : Ω)
    (hτ : ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q (m : Ω) → τ ∈ regAt ξ q) :
    ∃ n : ℕ, (m : Ω) ^ n * τ ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
  let B := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  let I : Ideal B :=
    { carrier := {r | (r : Ω) * τ ∈ B}
      add_mem' := by
        intro a b ha hb
        have ha' : (a : Ω) * τ ∈ B := ha
        have hb' : (b : Ω) * τ ∈ B := hb
        have h := add_mem ha' hb'
        rw [← add_mul] at h
        exact h
      zero_mem' := by
        show ((0 : B) : Ω) * τ ∈ B
        simp
      smul_mem' := by
        intro r a ha
        have ha' : (a : Ω) * τ ∈ B := ha
        have h := mul_mem r.2 ha'
        rw [← _root_.mul_assoc] at h
        exact h }
  have hmem : (m : B) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hIQ, hQ⟩
    by_contra hmQ
    obtain ⟨q, ⟨hqc, hq⟩, -⟩ := chart_point_of_prime X Ω ξ ℤ κ x T c hc Q hQ
    have hu : unitAt ξ q (((m : B) : B) : Ω) := (hq (m : B)).1 hmQ
    have hu' : unitAt ξ q (m : Ω) := by simpa using hu
    obtain ⟨s, hsB, hsu, hsτ⟩ :=
      (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x T c q hqc τ).1 (hτ q hqc hu')
    have hsQ : (⟨s, hsB⟩ : B) ∈ Q := hIQ hsτ
    exact (hq ⟨s, hsB⟩).2 hsu hsQ
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n, ?_⟩
  have h : (((m : B) ^ n : B) : Ω) * τ ∈ B := hn
  simpa using h

theorem unitAt_natCast_of_dvd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (q : Cpt ξ) {p m : ℕ} (hd : p ∣ m) (hm : unitAt ξ q (m : Ω)) : unitAt ξ q (p : Ω) := by
  obtain ⟨w, rfl⟩ := hd
  obtain ⟨h0, -, hinv⟩ := hm
  have hc : (((p * w : ℕ) : Ω)) = (p : Ω) * (w : Ω) := by push_cast; ring
  rw [hc] at h0 hinv
  have hp : (p : Ω) ≠ 0 := left_ne_zero_of_mul h0
  have hw : (w : Ω) ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨hp, natCast_mem _ p, ?_⟩
  have he : (p : Ω)⁻¹ = (w : Ω) * ((p : Ω) * (w : Ω))⁻¹ := by field_simp
  rw [he]
  exact mul_mem (natCast_mem _ w) hinv


variable {Ω' : Type} [Field Ω'] in
theorem div_mem_of_mem_span {R : Subring Ω'} {v w : Ω'} (hw : w ≠ 0) (h : v ∈ Submodule.span R {w}) :
    v / w ∈ R := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h
  have hr' : (r : Ω') * w = v := hr
  rw [← hr', mul_div_cancel_right₀ _ hw]
  exact r.2

theorem exists_pow_chart_quotients {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    {L L' : Lat ξ Ω} {a a' : K → ℤ} {e e' : Ω} (hL : L.IsDegOn Set.univ y a e)
    (hL' : L'.IsDegOn Set.univ y a' e') (S : Finset Nat.Primes)
    (hS : ∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q)
    (c : (k : K) → J k) (hc : ∏ k, y ⟨k, c k⟩ ≠ 0) :
    (∃ n : ℕ, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n *
        (((∏ k, y ⟨k, c k⟩ ^ a' k) * e') / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) ∈
        Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) ∧
      ∃ n : ℕ, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n *
        (((∏ k, y ⟨k, c k⟩ ^ a k) * e) / ((∏ k, y ⟨k, c k⟩ ^ a' k) * e')) ∈
        Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
  have key : ∀ q : Cpt ξ, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q →
      unitAt ξ q ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) →
      Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ a k) * e} =
        Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'} := by
    intro q hq hm
    have h1 := hL.2 q (Set.mem_univ q) c hq
    have h2 := hL'.2 q (Set.mem_univ q) c hq
    rw [smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
    refine hS q fun p hp hf => hf ?_
    exact unitAt_natCast_of_dvd q (Finset.dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hp) hm
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  have hu : (∏ k, y ⟨k, c k⟩ ^ a k) * e ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) hL.1
  have hu' : (∏ k, y ⟨k, c k⟩ ^ a' k) * e' ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) hL'.1
  constructor
  · refine exists_pow_mul_mem_chart T hc _ _ fun q hq hm => div_mem_of_mem_span hu ?_
    rw [key q hq hm]
    exact Submodule.mem_span_singleton_self _
  · refine exists_pow_mul_mem_chart T hc _ _ fun q hq hm => div_mem_of_mem_span hu' ?_
    rw [← key q hq hm]
    exact Submodule.mem_span_singleton_self _

theorem lat_vertOff : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (L L' : Lat ξ Ω) (a a' : K → ℤ) (e e' : Ω), L.IsDegOn Set.univ y a e → L'.IsDegOn Set.univ y a' e' → ∀ S : Finset Nat.Primes, (∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q) → ∃ f g : MvPolynomial (Σ k, J k) ℤ, (⟨fun _ => a, fun _ => a', fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y) S ∧ aeval y f = e' / e * aeval y g := by
  intro X Ω _ ξ K _ _ J _ y T d hA L L' a a' e e' hL hL' S hS
  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hA.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, h0]
  have hproj : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (pointIdeal ℤ y) :=
    GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim.isMultiProjPrime_pointIdeal y hrel
  have he : e ≠ 0 := hL.1
  have he' : e' ≠ 0 := hL'.1
  refine _root_.GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off K J Ω y hproj S a a' (e' / e) (div_ne_zero he' he) ?_ hA.2.2.1
  intro c hc
  have hc' : ∏ k, y ⟨k, c k⟩ ≠ 0 := hc
  obtain ⟨⟨n, hn⟩, ⟨n', hn'⟩⟩ := exists_pow_chart_quotients T hL hL' S hS c hc'
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)
  have hY : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hY' : (∏ k, y ⟨k, c k⟩ ^ a' k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  constructor
  · rintro t ⟨A, hAm, rfl⟩
    have hAm' : A ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
        (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := hAm
    refine ⟨n', _, ⟨_, mul_mem hn' hAm', rfl⟩, ?_⟩
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) = Y at hY
    generalize (∏ k, y ⟨k, c k⟩ ^ a' k) = Y' at hY'
    field_simp
  · rintro t ⟨A, hAm, rfl⟩
    have hAm' : A ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
        (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := hAm
    refine ⟨n, _, ⟨_, mul_mem hn hAm', rfl⟩, ?_⟩
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) = Y at hY
    generalize (∏ k, y ⟨k, c k⟩ ^ a' k) = Y' at hY'
    field_simp

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagDegree
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isDegOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H), Fl.RootLines xdeg e → (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsDegOn Set.univ y (∑ i, xdeg (τ, i)) (∏ i, e (τ, i)) :=
  PositivityTheory.Xgn.hodge_component_flag_degree
end

