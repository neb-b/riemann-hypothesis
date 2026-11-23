module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0534
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjModelBaseChangeStandardOpenAppSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem fnOf_app_const {Y Z : Scheme.{0}} [IsIntegral Y] {R₁ : Type} [CommRing R₁] (f : Y ⟶ Z) (c : Z ⟶ Sp R₁)
    (U : Z.Opens) (h : genericPoint Y ∈ f ⁻¹ᵁ U) (r : R₁) :
    fnOf (f ⁻¹ᵁ U) h ((f.app U).hom ((Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom r)))) = GlobalTheory.Desc.cst (f ≫ c) r := by
  have hn := congrArg (fun φ => φ.hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom r)))
    (f.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at hn
  rw [hn]
  exact fnOf_resG (X := Y) (le_top : f ⁻¹ᵁ U ≤ ⊤) h _

theorem app_surjective_of_factor {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F}
    {P : Scheme.{0}} [IsIntegral P] {p : P ⟶ Sp R} {ψ : P.functionField →+* F} {Dp : ℕ → F → P.Opens}
    (hP : IsModel c₀ N p ψ Dp) {R₁ : Type} [CommRing R₁] {Y Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    (f : Y ⟶ Z) (a : Z ⟶ P) (c : Z ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y)
    (hspan : ∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst (f ≫ c)) (θ '' N k)) (hff : PFF (𝟙 _) (f ≫ a) (θ.comp ψ))
    (k : ℕ) (hk : 1 ≤ k) (b : F) (hb : b ∈ N k) (hloc : ∀ y, (f ≫ a) y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) :
    Function.Surjective (f.app (a ⁻¹ᵁ Dp k b)) := by
  intro s
  by_cases hW : genericPoint Y ∈ f ⁻¹ᵁ a ⁻¹ᵁ Dp k b
  swap
  · exact ⟨0, fn_ext fun h => absurd h hW⟩

  have hgen : genericPoint Y ∈ locus D₁ k (θ b) := (hloc _).1 hW
  have hθb0 : θ b ≠ 0 := CartierDiv.GeneratesAt.ne_zero (D := k • D₁) hgen
  have hb0 : b ≠ 0 := fun e => hθb0 (by rw [e, map_zero])
  have hPg : genericPoint P ∈ Dp k b := (hP.gen k hk b hb).2 hb0

  have hreg : ∀ y ∈ locus D₁ k (θ b), RegAt y (fnOf (f ⁻¹ᵁ a ⁻¹ᵁ Dp k b) hW s) :=
    fun y hy => regAt_fnOf (U := f ⁻¹ᵁ a ⁻¹ᵁ Dp k b) (x := y) ((hloc y).2 hy) hW s
  have hbsec : θ b ∈ Sec D₁ k := by
    rw [hspan k]
    exact subset_spanBy _ _ ⟨b, hb, rfl⟩
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_mul_pow_mem_cartierMultiple_of_regular_locus Y D₁ k (θ b) hbsec _ hreg
  rw [hspan] at hn
  obtain ⟨M, r, t, ht, hsum⟩ := hn
  choose u hu hut using ht

  have hv : ∀ i, ∃ v, (∀ z ∈ Dp k b, RegAt z v) ∧ ψ v = u i / b ^ n :=
    fun i => (hP.ring k hk b hb hb0 (u i / b ^ n)).2 ⟨n, u i, hu i, rfl⟩
  choose v hvreg hvψ using hv
  have hA : ∀ i, ∃ A : Γ(P, Dp k b), fnOf (Dp k b) hPg A = v i := fun i => exists_fnOf_eq hPg (hvreg i)
  choose A hA using hA
  have hterm : ∀ i, fnOf (f ⁻¹ᵁ a ⁻¹ᵁ Dp k b) hW ((f.app (a ⁻¹ᵁ Dp k b)).hom
      ((Z.presheaf.map (homOfLE (le_top : a ⁻¹ᵁ Dp k b ≤ ⊤)).op).hom
        (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i))) * (a.app (Dp k b)).hom (A i))) =
      cst (f ≫ c) (r i) * t i / θ b ^ n := by
    intro i
    rw [map_mul, map_mul, fnOf_app_const f c _ hW (r i)]
    have e := _root_.GlobalTheory.Desc.fnOf_app_of_pff P Y (f ≫ a) (θ.comp ψ) hff (Dp k b) hPg hW (A i)
    rw [hA i, RingHom.comp_apply, hvψ i, map_div₀, map_pow, hut i] at e
    rw [mul_div_assoc, ← e]
    rfl
  refine ⟨∑ i, (Z.presheaf.map (homOfLE (le_top : a ⁻¹ᵁ Dp k b ≤ ⊤)).op).hom
      (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i))) * (a.app (Dp k b)).hom (A i),
    fnOf_injective _ hW ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← hsum, mul_div_assoc, div_self (pow_ne_zero n hθb0), _root_.mul_one]

theorem lift_app_surjective : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → ∀ (hm : m ≫ p = q ≫ spMap ρ) (k : ℕ), 1 ≤ k → ∀ b ∈ N k, Function.Surjective ((pullback.lift m q hm).app ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)) := by
  intro R F _ _ _ c₀ N _ P _ p ψ Dp hP R₁ _ _ ρ _ _ Y _ _ _ q θ D₁ _ _ _ hspan m hff hloc hm k hk b hb
  have hfc : pullback.lift m q hm ≫ pullback.snd p (spMap ρ) = q := pullback.lift_snd _ _ _
  have hfa : pullback.lift m q hm ≫ pullback.fst p (spMap ρ) = m := pullback.lift_fst _ _ _
  exact app_surjective_of_factor hP (pullback.lift m q hm) (pullback.fst p (spMap ρ)) (pullback.snd p (spMap ρ)) θ D₁
    (by rw [hfc]; exact hspan) (by rw [hfa]; exact hff) k hk b hb (by rw [hfa]; exact hloc k hk b hb)

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectivePointFlagHom
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagQ

theorem eq_genericPoint_of_krullDim_zero {X : Scheme.{0}} [IsIntegral X] (h : topologicalKrullDim X = 0) (x : X) :
    x = genericPoint X := by
  by_contra hx
  have hlt : (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ : TopologicalSpace.IrreducibleCloseds X) <
      ⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    refine lt_of_le_of_ne ?_ ?_
    · exact (specializes_iff_closure_subset.1 (genericPoint_specializes x))
    · intro he
      have : closure ({x} : Set X) = closure {genericPoint X} := congrArg TopologicalSpace.IrreducibleCloseds.carrier he
      exact hx ((specializes_iff_closure_subset.2 this.ge).antisymm (genericPoint_specializes x)).eq
  have : (0 : WithBot ℕ∞) < topologicalKrullDim X := Order.krullDim_pos_iff.2 ⟨_, _, hlt⟩
  rw [h] at this
  exact lt_irrefl _ this

end GlobalTheory.FlagQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSurjectiveAffineChartBijectiveSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FibOpen

theorem universallyOpen_of {X Y : Scheme.{0}} (f : X ⟶ Y) [UniversallyClosed f] [UniversallyInjective f]
    [Surjective f] : UniversallyOpen f := by
  constructor
  intro X' Y' i₁ i₂ f' hf
  have h1 : UniversallyClosed f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have h2 : UniversallyInjective f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have h3 : Surjective f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have hb : Function.Bijective f' := ⟨f'.injective, f'.surjective⟩
  show IsOpenMap f'
  intro U hU
  have e : f' '' U = (f' '' Uᶜ)ᶜ := by rw [Set.image_compl_eq hb, compl_compl]
  rw [e]
  exact (f'.isClosedMap _ hU.isClosed_compl).isOpen_compl

theorem fiber_hom_ext {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) {u v : T ⟶ f.fiber y}
    (h₁ : u ≫ f.fiberι y = v ≫ f.fiberι y)
    (h₂ : u ≫ f.fiberToSpecResidueField y = v ≫ f.fiberToSpecResidueField y) : u = v :=
  pullback.hom_ext h₁ h₂

@[reassoc]
theorem fiber_condition {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y) :
    f.fiberι y ≫ f = f.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y :=
  pullback.condition

def fiberLift {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : T ⟶ f.fiber y :=
  pullback.lift u v h

@[reassoc (attr := simp)]
theorem fiberLift_ι {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : fiberLift f y u v h ≫ f.fiberι y = u :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fiberLift_snd {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : fiberLift f y u v h ≫ f.fiberToSpecResidueField y = v :=
  pullback.lift_snd _ _ _

theorem range_comp_fromSpecResidueField {X T : Scheme.{0}} [Nonempty T] (x : X) (t : T ⟶ Spec (X.residueField x)) :
    Set.range (t ≫ X.fromSpecResidueField x) = {x} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    rfl
  · rintro rfl
    obtain ⟨z⟩ := ‹Nonempty T›
    exact ⟨z, by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩

theorem comp_fromSpecResidueField_apply {Y T : Scheme.{0}} (y : Y) (t : T ⟶ Spec (Y.residueField y)) (z : T) :
    (t ≫ Y.fromSpecResidueField y) z = y := by
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end GlobalTheory.FibOpen
end


set_option backward.isDefEq.respectTransparency.types false in
theorem GlobalTheory.FibOpen.fibre_universallyOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ φ : a.fiber x ⟶ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiber (τ x), φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) = a.fiberι x ≫ c → φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x) = a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x) → UniversallyOpen φ := by
  intro R _ _ _ _ S X π U a b g τ c hπp hπs hΓ hlft hsep hap haO hτ hc₁ hc₂ het x hxc hxcl hinj hsurj φ hφ₁ hφ₂
  let ψ : a.fiber x ⟶ pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) :=
    pullback.lift φ (a.fiberToSpecResidueField x) hφ₂
  have hψ₁ : ψ ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd _ _ = a.fiberToSpecResidueField x := pullback.lift_snd _ _ _
  have hSx : pullback.fst ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x) =
      pullback.snd _ _ ≫ (Spec.map (τ.residueFieldMap x)) := pullback.condition
  have hres : U.left.fromSpecResidueField x ≫ τ = (Spec.map (τ.residueFieldMap x)) ≫ 𝔸(Fin g; Sp R).fromSpecResidueField (τ x) :=
    (τ.SpecMap_residueFieldMap_fromSpecResidueField x).symm
  have hFc : (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) π ≫ π := pullback.condition
  have hb : a.fiberι x ≫ b = φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) ≫ pullback.snd _ _ := by
    rw [← hc₂, ← Category.assoc, ← hφ₁, Category.assoc]
  suffices h : UniversallyOpen ψ by
    rw [← hψ₁]; infer_instance
  haveI : IsProper a := hap
  haveI : IsProper π := hπp
  haveI : IsProper (a.fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ hap
  haveI : IsSeparated (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) := MorphismProperty.pullback_fst (P := @IsSeparated) _ _ inferInstance
  haveI : IsSeparated ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : IsProper (ψ ≫ pullback.snd _ _) := by rw [hψ₂]; infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ (pullback.snd ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)))
  haveI : UniversallyInjective ψ := by
    refine ((tfae_universallyInjective ψ).out 1 2).mpr ?_
    intro K _ q q' hq
    simp only at hq
    have e₂ : q ≫ a.fiberToSpecResidueField x = q' ≫ a.fiberToSpecResidueField x := by
      rw [← hψ₂, ← Category.assoc, hq, Category.assoc]
    have e₃ : q ≫ φ = q' ≫ φ := by rw [← hψ₁, ← Category.assoc, hq, Category.assoc]
    have ea : ∀ q : Spec (.of K) ⟶ a.fiber x, (q ≫ a.fiberι x) ≫ a =
        (q ≫ a.fiberToSpecResidueField x) ≫ U.left.fromSpecResidueField x := fun q => by
      rw [Category.assoc, Category.assoc, GlobalTheory.FibOpen.fiber_condition]
    have key := hinj K (q ≫ a.fiberι x) (q' ≫ a.fiberι x)
      (by rw [ea]; exact GlobalTheory.FibOpen.range_comp_fromSpecResidueField x _) (by rw [ea, ea, e₂])
      (by rw [Category.assoc, Category.assoc, hb, ← Category.assoc q, e₃, Category.assoc])
    exact GlobalTheory.FibOpen.fiber_hom_ext a x key e₂
  haveI : Surjective ψ := by
    constructor
    intro y
    let Ω := AlgebraicClosure ((pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).residueField y)
    let t : Sp Ω ⟶ pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) :=
      Spec.map (CommRingCat.ofHom (algebraMap ((pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).residueField y) Ω)) ≫
        (pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).fromSpecResidueField y
    let ξ := (t ≫ pullback.snd _ _) ≫ U.left.fromSpecResidueField x
    let s := t ≫ pullback.fst _ _ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) ≫ pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) π
    have hξ : ξ ≫ U.hom = s ≫ π := by
      simp only [ξ, s, Category.assoc]
      rw [← hτ, ← hFc, reassoc_of% hres, GlobalTheory.FibOpen.fiber_condition_assoc, reassoc_of% hSx]
    obtain ⟨p, hp₁, hp₂⟩ := hsurj Ω ξ s (GlobalTheory.FibOpen.range_comp_fromSpecResidueField x _) hξ
    let q : Sp Ω ⟶ a.fiber x := GlobalTheory.FibOpen.fiberLift a x p (t ≫ pullback.snd _ _) (by rw [hp₁])
    have hqt : q ≫ ψ = t := by
      apply pullback.hom_ext
      · rw [Category.assoc, hψ₁]
        apply GlobalTheory.FibOpen.fiber_hom_ext
        · rw [Category.assoc, hφ₁, GlobalTheory.FibOpen.fiberLift_ι_assoc]
          apply pullback.hom_ext
          · simp only [Category.assoc]
            rw [hc₁, reassoc_of% hp₁]
            simp only [ξ, Category.assoc]
            rw [hres, GlobalTheory.FibOpen.fiber_condition, reassoc_of% hSx]
          · simp only [Category.assoc]
            rw [hc₂, hp₂]
        · rw [Category.assoc, hφ₂, GlobalTheory.FibOpen.fiberLift_snd_assoc]
          simp only [Category.assoc]
          rw [hSx]
      · rw [Category.assoc, hψ₂, GlobalTheory.FibOpen.fiberLift_snd]
    obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
    refine ⟨q z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hqt]
    exact GlobalTheory.FibOpen.comp_fromSpecResidueField_apply y _ z
  exact GlobalTheory.FibOpen.universallyOpen_of ψ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtAlgCompRight
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.SumMulFacts

theorem ptAlg_comp_right {R D D' E : Type} [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    [CommRing E] [Algebra R E] (φ : D →ₐ[R] D') (y : Pt (SpAlg R D') E) :
    ptAlg (R := R) (D := D) (E := E) (y ≫ spOver φ) = (ptAlg y).comp φ := by
  conv_lhs => rw [← spOver_ptAlg y, spOver_comp]
  exact ptAlg_spOver _

theorem main : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R))
    (J : Type) [Fintype J] (d : J → D) (b : J → Fn1 B),
    ((∀ i, IsCoc (whole B) (b i)) → IsCoc (whole _) (sumMul d b)) ∧
      ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D'),
        (sumMul d b).pull (spOver φ ▷ B) = sumMul (fun i ↦ φ (d i)) b := by
  intro R D _ _ _ B J _ d b
  refine ⟨fun hb ↦ ?_, fun D' _ _ φ ↦ ?_⟩
  · unfold IsCoc at hb ⊢
    intro E _ _ E' _ _ E'' _ _ φ ψ z _
    have hα := ptAlg_comp (D := D) φ (z ≫ fst (SpAlg R D) B)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [sumMul, hα, map_sum, map_mul, AlgHom.comp_apply, Category.assoc]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := hb i E E' E'' φ ψ (z ≫ snd _ _) (sm_whole _)
    rw [h]
    ring
  · unfold Fn1
    funext E _ _ E' _ _ ψ y
    simp only [Fn1.pull, sumMul, Category.assoc, whiskerRight_fst, whiskerRight_snd]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [← Category.assoc, ptAlg_comp_right, AlgHom.comp_apply]

end GlobalTheory.PtExt.SumMulFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem lbIso_pull_pull_comp {X Y Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (F : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso ((M.pull F).pull g) (M.pull (g ≫ F)) :=
  Geo.Tor.LBIso.chartPull (h := g) (Geo.Tor.chartPullPull (M.pull F) g g rfl)
    (Geo.Tor.chartPullSame M (fun _ => g ≫ F) (fun _ => F) (fun _ => 1) g (fun _ => rfl))
    (GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_pull hM F))

theorem exists_gen_pull_pull_iff {X Y Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (F : Y ⟶ X) (g : Z ⟶ Y) :
    (∃ t : LB.Gen ((M.pull F).pull g), t.IsGen) ↔ ∃ t : LB.Gen (M.pull (g ≫ F)), t.IsGen := by
  have h₁ := LB.isLB_pull (LB.isLB_pull hM F) g
  have h₂ := LB.isLB_pull hM (g ≫ F)
  exact ⟨GlobalTheory.CM.PairingIso.exists_gen_of_lbIso h₁ h₂ (lbIso_pull_pull_comp hM F g),
    GlobalTheory.CM.PairingIso.exists_gen_of_lbIso h₂ h₁ (Geo.Tor.LBIso.symm (lbIso_pull_pull_comp hM F g))⟩

theorem left_tensor_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} (u v : Z ⟶ (X ⊗ Y).left)
    (h₁ : u ≫ (fst X Y).left = v ≫ (fst X Y).left) (h₂ : u ≫ (snd X Y).left = v ≫ (snd X Y).left) : u = v := by
  rw [Over.fst_left] at h₁
  rw [Over.snd_left] at h₂
  exact pullback.hom_ext h₁ h₂

theorem pull_gen_lam_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (inc : G ⟶ G'), IsMonHom inc → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → ∃ t : LB.Gen (letI := A'.isAb.comm; (abelian₂ A'.A A'.L).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.f) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 A'.A).left), t.IsGen := by
  intro R _ _ _ D D' F A' G' _ _ U' oA oG hlin G _ _ inc hinc κ₀ hκ T x ht
  letI := A'.isAb.comm
  haveI : IsMonHom U'.gen.hom := U'.gen_hom
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hQ : (abelian₂ G' U'.LG.L).IsLB := DVR.linComb_isLB _ hL' _ _
  have hA : A'.L.IsLB := A'.isLB
  have hQA : (abelian₂ A'.A A'.L).IsLB := DVR.linComb_isLB _ hA _ _
  obtain ⟨β₂, hβ₂, Hβ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (jK R) G' ((Over.pullback (jK R)).obj G')
    (pullback.fst G'.hom (jK R)) (Geo.Tor.isGrpPullback_pullback G' (jK R))
  have E₁ := Hβ U'.LG.L (U'.LG.L.pull (pullback.fst G'.hom (jK R))) _ (abelian₂ G' U'.LG.L) (𝟙 _) hL'
    (LB.isLB_pull hL' _) hQ (GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_pull hL' _))
    (Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl hQ))
  obtain ⟨γ₂, hγ₂, Hγ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (𝟙 _) A'.A ((Over.pullback (jK R)).obj G')
    U'.gen.hom.left (Geo.Tor.isGrpPullback_of_iso U'.gen)
  have E₂ := Hγ A'.L (U'.LG.L.pull (pullback.fst G'.hom (jK R))) _ (abelian₂ A'.A A'.L) (𝟙 _) hA
    (LB.isLB_pull hL' _) hQA (Geo.Tor.LBIso.symm U'.ext)
    (Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl hQA))
  have E₃ := Geo.Tor.LBIso.trans (LB.isLB_pull hQ _) (DVR.linComb_isLB _ (LB.isLB_pull hL' _) _ _)
    (LB.isLB_pull hQA _) (Geo.Tor.LBIso.symm E₁) E₂
  let m := (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x ≫ (Over.pullback (jK R)).map inc)
    (fst ((Over.pullback (jK R)).obj G) T ≫ (Over.pullback (jK R)).map inc ≫ (Over.pullback (jK R)).map (oG.act F.f))).left
  have E₄ := Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull _ m m rfl) (Geo.Tor.chartPullPull _ m m rfl) E₃
  obtain ⟨t, ht⟩ := ht
  let φl := (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  let ψl := (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left
  let χl := (lift (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ ((Over.pullback (jK R)).map inc) ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ (((Over.pullback (jK R)).map inc) ≫ U'.gen.hom) ≫ oA.act F.f) :
    ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 A'.A).left
  have hinc' : ((Over.pullback (jK R)).map inc).left ≫ pullback.fst G'.hom (jK R) = pullback.fst G.hom (jK R) ≫ inc.left :=
    pullback.lift_fst _ _ _
  have hf' : ((Over.pullback (jK R)).map (oG.act F.f)).left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ (oG.act F.f).left :=
    pullback.lift_fst _ _ _
  have hgen : ((Over.pullback (jK R)).map (oG.act F.f)).left ≫ U'.gen.hom.left = U'.gen.hom.left ≫ (oA.act F.f).left :=
    congrArg Over.Hom.left (hlin.ext F.f)
  have hφ1 : φl ≫ (fst G' G').left = (fst G G).left ≫ inc.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f))
  have hφ2 : φl ≫ (snd G' G').left = (snd G G).left ≫ inc.left ≫ (oG.act F.f).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_snd (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f))
  have hψ1 : ψl ≫ (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)).left = (snd ((Over.pullback (jK R)).obj G) T).left ≫ x.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T))
  have hψ2 : ψl ≫ (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)).left = (fst ((Over.pullback (jK R)).obj G) T).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_snd (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T))
  have hm1 : m ≫ (fst ((Over.pullback (jK R)).obj G') ((Over.pullback (jK R)).obj G')).left = (snd ((Over.pullback (jK R)).obj G) T).left ≫ x.left ≫ ((Over.pullback (jK R)).map inc).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (snd ((Over.pullback (jK R)).obj G) T ≫ x ≫ ((Over.pullback (jK R)).map inc)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc) ≫ ((Over.pullback (jK R)).map (oG.act F.f))))
  have hm2 : m ≫ (snd ((Over.pullback (jK R)).obj G') ((Over.pullback (jK R)).obj G')).left = (fst ((Over.pullback (jK R)).obj G) T).left ≫ ((Over.pullback (jK R)).map inc).left ≫ ((Over.pullback (jK R)).map (oG.act F.f)).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_snd (snd ((Over.pullback (jK R)).obj G) T ≫ x ≫ ((Over.pullback (jK R)).map inc)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc) ≫ ((Over.pullback (jK R)).map (oG.act F.f))))
  have hχ1 : χl ≫ (fst A'.A A'.A).left = (snd ((Over.pullback (jK R)).obj G) T).left ≫ x.left ≫ ((Over.pullback (jK R)).map inc).left ≫ U'.gen.hom.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ ((Over.pullback (jK R)).map inc) ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ (((Over.pullback (jK R)).map inc) ≫ U'.gen.hom) ≫ oA.act F.f))
  have hχ2 : χl ≫ (snd A'.A A'.A).left = (fst ((Over.pullback (jK R)).obj G) T).left ≫ ((Over.pullback (jK R)).map inc).left ≫ U'.gen.hom.left ≫ (oA.act F.f).left := by
    have := congrArg Over.Hom.left (lift_snd (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ ((Over.pullback (jK R)).map inc) ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ (((Over.pullback (jK R)).map inc) ≫ U'.gen.hom) ≫ oA.act F.f))
    simp only [Over.comp_left, Category.assoc] at this
    exact this
  have eq1 : ψl ≫ κ₀ ≫ φl = m ≫ β₂ ≫ 𝟙 _ := by
    apply left_tensor_ext
    · simp only [Category.assoc, Category.comp_id]
      rw [hφ1, reassoc_of% hκ.1]
      rw [reassoc_of% hψ1]
      rw [hβ₂.1]
      rw [reassoc_of% hm1]
      simp only [Category.assoc, hinc']
    · simp only [Category.assoc, Category.comp_id]
      rw [hφ2, reassoc_of% hκ.2]
      rw [reassoc_of% hψ2]
      rw [hβ₂.2]
      rw [reassoc_of% hm2]
      simp only [Category.assoc, hf']
      rw [reassoc_of% hinc']
  have eq2 : m ≫ γ₂ ≫ 𝟙 _ = χl := by
    apply left_tensor_ext
    · simp only [Category.assoc, Category.comp_id]
      rw [hγ₂.1]
      rw [reassoc_of% hm1, hχ1]
    · simp only [Category.assoc, Category.comp_id]
      rw [hγ₂.2]
      rw [reassoc_of% hm2, hχ2, hgen]
  have hP1 := LB.isLB_pull (LB.isLB_pull (LB.isLB_pull hQ φl) κ₀) ψl
  have hP2 := LB.isLB_pull (LB.isLB_pull hQ (κ₀ ≫ φl)) ψl
  have g₀ := GlobalTheory.CM.PairingIso.exists_gen_of_lbIso hP1 hP2
    (Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull _ ψl ψl rfl) (Geo.Tor.chartPullPull _ ψl ψl rfl)
      (lbIso_pull_pull_comp hQ φl κ₀)) ⟨t, ht⟩
  have g₁ := (exists_gen_pull_pull_iff hQ (κ₀ ≫ φl) ψl).1 g₀
  rw [eq1] at g₁
  have g₂ := (exists_gen_pull_pull_iff hQ (β₂ ≫ 𝟙 _) m).2 g₁
  have g₃ := GlobalTheory.CM.PairingIso.exists_gen_of_lbIso (LB.isLB_pull (LB.isLB_pull hQ _) _)
    (LB.isLB_pull (LB.isLB_pull hQA _) _) E₄ g₂
  have g₄ := (exists_gen_pull_pull_iff hQA (γ₂ ≫ 𝟙 _) m).1 g₃
  rw [eq2] at g₄
  exact g₄

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refining_degenerationData_tauCoordinate_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (hρ : Function.Injective ρ),
    Refines Q ρ D e → ∀ (a b : D.X) (k : (FractionRing R)ˣ), Q.TauCoord (e a) (e b) k →
      ∀ x : (FractionRing R')ˣ, IsTauCoord D a b x → ∃ u : R'ˣ, (x : FractionRing R') =
        algebraMap R' (FractionRing R') u * IsFractionRing.lift (A := R) (K := FractionRing R)
          (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) := by
  first | exact @GlobalTheory.RefTauCoord.main | exact GlobalTheory.RefTauCoord.main | (intros; apply GlobalTheory.RefTauCoord.main <;> assumption)
end

