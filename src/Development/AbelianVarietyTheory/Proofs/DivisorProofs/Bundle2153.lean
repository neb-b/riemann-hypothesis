module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorsDoubleFlagSpace
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.DivOn

theorem unitAt_of {Z : Scheme.{0}} [IsIntegral Z] {z : Z} {u : Z.functionField} (h0 : u ≠ 0)
    (h : u ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range)
    (h' : u⁻¹ ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range) : UnitAt z u :=
  (unitAt_iff h0).2 ⟨h, h'⟩

theorem key {F : Type} [Field F] {X Y : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : Refines E E' φ f) {gr : Root m → Y.Dv}
    {B : Mat m Y.Fn} (hB : B ∈ E'.S (genericPoint Y.X))
    (hgr : ∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t)
    (W : Dbl Y) (hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) {τ : ι} {a b : Fin (m τ)} (hab : (b : ℕ) = a + 1)
    (hC : AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹)) {D₁ D₂ : Root m → CartierDiv W.Z}
    (hD₁ : ∀ x, IsPull W.p₁ (D₁ x) (gr x)) (hD₂ : ∀ x, IsPull W.p₂ (D₂ x) (gr x)) (z : W.Z)
    {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) :
    ∃ t₁ t₂ : Root m → W.Z.functionFieldˣ, (∀ x, (D₁ x).IsEqn z (t₁ x)) ∧ (∀ x, (D₂ x).IsEqn z (t₂ x)) ∧
      AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) ∧
      (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ →
        UnitAt z ((t₁ x : W.Z.functionField)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) x.1 x.2 x.2 * t₂ x)) ∧
      UnitAt z ((t₁ ⟨τ, a⟩ : W.Z.functionField)⁻¹ * (t₁ ⟨τ, b⟩ : W.Z.functionField)⁻¹ *
        minor τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) * (t₂ ⟨τ, a⟩ * t₂ ⟨τ, b⟩)) ∧
      (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b =
        (t₁ ⟨τ, a⟩ : W.Z.functionField)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) τ a b * t₂ ⟨τ, b⟩ ∧
      RegAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) := by
  obtain ⟨hP₁, h₁⟩ := _root_.GlobalTheory.FlagPush.isEqn_diag_of_frame F Y ι m E' gr B hB hgr _ A₁ hA₁
  obtain ⟨hP₂, h₂⟩ := _root_.GlobalTheory.FlagPush.isEqn_diag_of_frame F Y ι m E' gr B hB hgr _ A₂ hA₂
  choose s₁ e₁ q₁ using h₁
  choose s₂ e₂ q₂ using h₂
  have hT₁ : Par m ⊤ ((B * A₁⁻¹).map W.α₁) := hP₁.map W.α₁ fun _ _ => trivial
  have hT₂ : Par m ⊤ ((B * A₂⁻¹).map W.α₂) := hP₂.map W.α₂ fun _ _ => trivial
  have hloc := _root_.GlobalTheory.FlagPush.Dbl.transition_par_stalk F X Y ι m E E' φ f hf W hα z A₁ hA₁ A₂ hA₂
  have dB₁ : ∀ σ, (B.map W.α₁ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hB σ)
  have dB₂ : ∀ σ, (B.map W.α₂ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hB σ)
  have dA₁ : ∀ σ, (A₁.map W.α₁ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hA₁ σ)
  have eg : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ =
      ((B * A₁⁻¹).map W.α₁)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) * (B * A₂⁻¹).map W.α₂ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, Mat.mul_inv_rev, Mat.inv_inv dA₁, mul_assoc, mul_assoc,
      mul_assoc, ← mul_assoc (B.map W.α₂)⁻¹, Mat.inv_mul dB₂, one_mul, ← mul_assoc (B.map W.α₁)⁻¹, Mat.inv_mul dB₁,
      one_mul]
  obtain ⟨hal, hd, hab', hmin⟩ := _root_.GlobalTheory.FlagPush.almostLow_mul_entries ι m τ a b hab _ _ _ _ hT₁.inv hT₂ hC
  rw [← eg] at hal hd hab' hmin
  obtain ⟨hu, hm0, hm1⟩ := _root_.GlobalTheory.FlagPush.almostLow_units ι m τ a b hab _ _ _ hal hloc
  have i₁ : ∀ x : Root m, ((B * A₁⁻¹).map W.α₁)⁻¹ x.1 x.2 x.2 = (W.α₁ (s₁ x))⁻¹ := fun x => by
    rw [(_root_.GlobalTheory.FlagPush.diag_of_par ι m _ ⊤ _ hT₁ x).2.2.1, ← e₁ x]; rfl
  have i₂ : ∀ x : Root m, ((B * A₂⁻¹).map W.α₂) x.1 x.2 x.2 = W.α₂ (s₂ x) := fun x => by
    rw [← e₂ x]; rfl
  refine ⟨fun x => Units.map W.α₁.toMonoidHom (s₁ x), fun x => Units.map W.α₂.toMonoidHom (s₂ x),
    fun x => hD₁ x _ _ (q₁ x) z rfl, fun x => hD₂ x _ _ (q₂ x) z rfl, hal, fun x hxa hxb => ?_, ?_, ?_,
    (hloc τ).1 a b⟩
  · have := unitAt_of (hu x hxa hxb).1 ((hloc x.1).1 x.2 x.2) (hu x hxa hxb).2
    rw [hd x hxa hxb, i₁, i₂] at this
    exact this
  · have hmem : minor τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) ∈
        (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range :=
      sub_mem (mul_mem ((hloc τ).1 _ _) ((hloc τ).1 _ _)) (mul_mem ((hloc τ).1 _ _) ((hloc τ).1 _ _))
    have := unitAt_of hm0 hmem hm1
    rw [hmin, i₁ ⟨τ, a⟩, i₁ ⟨τ, b⟩, i₂ ⟨τ, a⟩, i₂ ⟨τ, b⟩] at this
    exact this
  · rw [hab', i₁ ⟨τ, a⟩, i₂ ⟨τ, b⟩]
    rfl

theorem exists_divisors : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) → ∃ (D₁ D₂ : Root m → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ ⟨τ, a⟩) + toPic (D₁ ⟨τ, b⟩) = toPic (D₂ ⟨τ, a⟩) + toPic (D₂ ⟨τ, b⟩) ∧ toPic Θ = toPic (D₂ ⟨τ, b⟩) - toPic (D₁ ⟨τ, a⟩) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf gr B hB hgr W hα τ a b hab hC
  choose D₁ hD₁ using fun x => _root_.GlobalTheory.FlagPush.exists_isPull W.Z Y.X W.p₁ (gr x)
  choose D₂ hD₂ using fun x => _root_.GlobalTheory.FlagPush.exists_isPull W.Z Y.X W.p₂ (gr x)
  have hC0 : Par 0 ⊤ (B.map W.α₁ * (B.map W.α₂)⁻¹) := fun σ =>
    ⟨fun _ _ => trivial, hC.1 σ, trivial, fun i j hi => absurd hi (by simp)⟩
  obtain ⟨hCd, hCm, -⟩ := _root_.GlobalTheory.FlagPush.almostLow_units ι m τ a b hab _ ⊤ _ hC hC0
  have K := fun (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) =>
    key hf hB hgr W hα hab hC hD₁ hD₂ z hA₁ hA₂
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hΘ : ∀ (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)),
      ∃ g : W.Z.functionFieldˣ, (g : W.Z.functionField) = (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b ∧
        (D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1)).IsEqn z g := fun z A₁ A₂ hA₁ hA₂ => by
    obtain ⟨t₁, t₂, q₁, q₂, -, -, -, e, -⟩ := K z hA₁ hA₂
    refine ⟨_, ?_, ((q₂ ⟨τ, b⟩).sub (q₁ ⟨τ, a⟩)).add (CartierDiv.isEqn_principal _ z)⟩
    rw [e, Units.val_mul, Units.val_div_eq_div_val, Units.val_mk0]
    ring
  refine ⟨D₁, D₂, D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1), hD₁, hD₂, fun x hxa hxb => ?_,
    ?_, ?_, fun z => ?_, ?_⟩
  · have e : D₂ x + CartierDiv.principal (Units.mk0 _ (hCd x hxa hxb).1) = D₁ x :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, (q₂ x).add (CartierDiv.isEqn_principal _ z), (q₁ x).iff_unitAt.2 ?_⟩
        convert hu x hxa hxb using 1
        rw [Units.val_mul, Units.val_mk0]
        ring
    rw [← e, map_add (f := _), toPic_principal, add_zero]
  · have e : D₂ ⟨τ, a⟩ + D₂ ⟨τ, b⟩ + CartierDiv.principal (Units.mk0 _ hCm) = D₁ ⟨τ, a⟩ + D₁ ⟨τ, b⟩ :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, ((q₂ _).add (q₂ _)).add (CartierDiv.isEqn_principal _ z), ((q₁ _).add (q₁ _)).iff_unitAt.2 ?_⟩
        convert hu using 1
        simp only [Units.val_mul, Units.val_mk0]
        ring
    rw [← map_add (f := _), ← map_add (f := _), ← e, map_add _ (_ + _), toPic_principal, add_zero]
  · rw [map_add (f := _), toPic_principal, add_zero, map_sub]
  · obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
    obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
    obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
    obtain ⟨t₁, t₂, -, -, -, -, -, -, hr⟩ := K z hA₁ hA₂
    exact ⟨g, hg, by rw [one_mul, e]; exact hr⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
      obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
      obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
      obtain ⟨t₁, t₂, -, -, hal, -⟩ := K z hA₁ hA₂
      refine _root_.GlobalTheory.FlagPush.mem_range_section_of_not_unitAt F X Y ι m E E' φ f hf W hα τ a b z A₁ hA₁ A₂ hA₂ hal ?_
      rw [← e]
      exact hg.mem_supp_iff.1 hz
    · rintro ⟨y, rfl⟩
      obtain ⟨A, hA⟩ := E'.nonempty y
      have e₁ : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
      have e₂ : W.p₂ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₂]; rfl
      obtain ⟨g, e, hg⟩ := hΘ (W.δ y) (A₁ := A) (A₂ := A) (by rw [e₁]; exact hA) (by rw [e₂]; exact hA)
      refine hg.mem_supp_iff.2 ?_
      rw [e]
      exact _root_.GlobalTheory.FlagPush.not_unitAt_section F X Y ι m E E' φ f hf W hα τ a b hne y A hA

end GlobalTheory.FlagPush.DivOn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantGeometricGenericPointSpecDomain
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory

theorem exists_geomGeneric_dominant : ∀ (A : CommRingCat.{0}) [IsDomain A], ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ Spec A), (∀ x, (y x).asIdeal = ⊥) ∧ IsDominant y := by
  intro A _
  let Ω := AlgebraicClosure (FractionRing A)
  let φ : A →+* Ω := algebraMap A Ω
  have hφ : Function.Injective φ := by
    have h1 : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective A _
    have h2 : Function.Injective (algebraMap (FractionRing A) Ω) := (algebraMap (FractionRing A) Ω).injective
    have : φ = (algebraMap (FractionRing A) Ω).comp (algebraMap A (FractionRing A)) :=
      IsScalarTower.algebraMap_eq A (FractionRing A) Ω
    rw [this]; exact h2.comp h1
  refine ⟨Ω, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · intro x
    show Ideal.comap φ x.asIdeal = ⊥
    rw [show x.asIdeal = ⊥ from @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime x)]
    exact Ideal.comap_bot_of_injective _ hφ
  · rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantTuplePrescribedMemberLinearForm
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc.DomTuple

section Squares

variable {X : Type} [AddCommGroup X]

def IsSumSq (F : LinearMap.BilinForm ℤ X → ℤ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (x : ι → X), ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → F β = ∑ i, β (x i) (x i)

theorem IsSumSq.congr {F G : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F)
    (e : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → G β = F β) : IsSumSq G := by
  obtain ⟨ι, _, x, hx⟩ := h
  exact ⟨ι, _, x, fun β hβ => (e β hβ).trans (hx β hβ)⟩

theorem IsSumSq.add {F G : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F) (h' : IsSumSq G) :
    IsSumSq fun β => F β + G β := by
  obtain ⟨ι, _, x, hx⟩ := h
  obtain ⟨κ, _, y, hy⟩ := h'
  exact ⟨ι ⊕ κ, inferInstance, Sum.elim x y, fun β hβ => by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hx β hβ, hy β hβ]⟩

theorem IsSumSq.nsmul {F : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F) (n : ℕ) : IsSumSq fun β => n * F β := by
  obtain ⟨ι, _, x, hx⟩ := h
  exact ⟨Fin n × ι, inferInstance, fun p => x p.2, fun β hβ => by
    simp [Fintype.sum_prod_type, hx β hβ]⟩

theorem isSumSq_one (v : X) : IsSumSq fun β => β v v :=
  ⟨Unit, inferInstance, fun _ => v, fun β _ => by simp⟩

variable {m : ℕ} (a : Fin m → X)

def Absorbed (F : LinearMap.BilinForm ℤ X → ℤ) : Prop :=
  ∃ C : ℕ, IsSumSq fun β => C * ∑ i, β (a i) (a i) + F β

variable {a}

theorem Absorbed.congr {F G : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F)
    (e : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → G β = F β) : Absorbed a G := by
  obtain ⟨C, h⟩ := h
  exact ⟨C, h.congr fun β hβ => by rw [e β hβ]⟩

theorem Absorbed.add {F G : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F) (h' : Absorbed a G) :
    Absorbed a fun β => F β + G β := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  exact ⟨C + C', (h.add h').congr fun β _ => by push_cast; ring⟩

theorem Absorbed.nsmul {F : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F) (n : ℕ) : Absorbed a fun β => n * F β := by
  obtain ⟨C, h⟩ := h
  exact ⟨n * C, (h.nsmul n).congr fun β _ => by push_cast; ring⟩

theorem absorbed_sq (v : X) : Absorbed a fun β => β v v :=
  ⟨0, (isSumSq_one v).congr fun β _ => by simp⟩

theorem absorbed_zero : Absorbed a fun _ => 0 :=
  (absorbed_sq 0).congr fun β _ => by simp

theorem absorbed_sum {ι : Type} (S : Finset ι) (F : ι → LinearMap.BilinForm ℤ X → ℤ) (h : ∀ i, Absorbed a (F i)) :
    Absorbed a fun β => ∑ i ∈ S, F i β := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using absorbed_zero
  | insert i S hi ih => exact ((h i).add ih).congr fun β _ => Finset.sum_insert hi

theorem absorbed_neg_sq (ha : Submodule.span ℤ (Set.range a) = ⊤) (v : X) : Absorbed a fun β => - β v v := by
  have hv : v ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1, {i // i ≠ j}, inferInstance, fun i => a i.1, fun β _ => ?_⟩
    have := Fintype.sum_eq_add_sum_subtype_ne (fun i => β (a i) (a i)) j
    simp only [Nat.cast_one, one_mul]
    rw [this]; ring
  | zero => exact absorbed_zero.congr fun β _ => by simp
  | add x y _ _ hx hy =>
    refine (((hx.nsmul 2).add (hy.nsmul 2)).add (absorbed_sq (x - y))).congr fun β _ => ?_
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    push_cast; ring
  | smul n x _ hx =>
    refine (hx.nsmul (n.natAbs ^ 2)).congr fun β _ => ?_
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    push_cast; rw [sq_abs]; ring

theorem absorbed_two_mul_apply (ha : Submodule.span ℤ (Set.range a) = ⊤) (u v : X) : Absorbed a fun β => 2 * β u v := by
  refine (((absorbed_sq (u + v)).add (absorbed_neg_sq ha u)).add (absorbed_neg_sq ha v)).congr fun β hβ => ?_
  simp only [map_add (f := _), LinearMap.add_apply, hβ v u]
  ring

theorem absorbed_two_mul [Module.Free ℤ X] [Module.Finite ℤ X] (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) : Absorbed a fun β => 2 * F β := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let E : _ → _ → LinearMap.BilinForm ℤ X := fun i j => (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hE : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • E i j := fun β => by
    refine LinearMap.BilinForm.ext_basis b fun k l => ?_
    simp [E, LinearMap.sum_apply, Finsupp.single_apply]
  refine (absorbed_sum Finset.univ _ fun i => absorbed_sum Finset.univ _ fun j =>
    absorbed_two_mul_apply ha (F (E i j) • b i) (b j)).congr fun β _ => ?_
  conv_lhs => rw [hE β]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Squares

theorem exists_tuple {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : ℕ} {a₀ : Fin m → X}
    (ha : Submodule.span ℤ (Set.range a₀) = ⊤) {s : ℕ} (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) {w : ℕ} (hw : 1 ≤ w)
    (hW : W 0 0 = w) (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (μ : Fin (s + 1) → X) (D₀ : ℕ) :
    ∃ (D l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), D₀ < D ∧ (∀ u, a (i₀, u) = μ u) ∧
      Submodule.span ℤ (Set.range a) = ⊤ ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
        lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + (2 * w : ℕ) * lam β := by
  classical
  have h1 : Absorbed a₀ fun β => 2 * lam β + ∑ u, ∑ v, 2 * β (-W u v • μ u) (μ v) :=
    (absorbed_two_mul ha lam).add (absorbed_sum _ _ fun u => absorbed_sum _ _ fun v => absorbed_two_mul_apply ha _ _)
  obtain ⟨C, ι, _, x, hx⟩ := h1
  let κ := Fin (2 * w) ⊕ (Fin (D₀ + 1) × Fin m) ⊕ ι
  let t : κ → Fin (s + 1) → X :=
    Sum.elim (fun _ => μ) (Sum.elim (fun p => Pi.single 0 (a₀ p.2)) fun i => Pi.single 0 (x i))
  let e := (Fintype.equivFin κ).symm
  refine ⟨w * (C + D₀ + 1), _, fun p => t (e p.1) p.2, e.symm (Sum.inl ⟨0, by omega⟩), by nlinarith, fun u => by simp [t],
    ?_, fun β hβ => ?_⟩
  · rw [eq_top_iff, ← ha]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨(e.symm (Sum.inr (Sum.inl (0, i))), 0), by simp [t]⟩
  · have hs : ∀ v : X, qW W β (Pi.single 0 v) = w * β v v := fun v => by
      simp [qW, Fin.sum_univ_succ, hW]
    have h2 : lin W (fun p : _ × _ => t (e p.1) p.2) β = ∑ k, qW W β (t k) := e.sum_comp fun k => qW W β (t k)
    have h3 := hx β hβ
    have h4 : ∑ u, ∑ v, 2 * β (-W u v • μ u) (μ v) = -2 * qW W β μ := by
      simp only [qW, Finset.mul_sum, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [h4] at h3
    rw [h2]
    simp only [κ, t, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, hs, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← h3]
    push_cast; ring

theorem exists_dominant (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (hφ : IsPolFanOn bar φ X) (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X)
    (a₀ : Fin m → X) (hγ : IsCone bar φ γ) (hne : NoEquivRays O γ) (hpos : ∀ x, x ≠ 0 → ∃ j, 0 < γ j x x)
    (hs : Supports bar φ d γ a₀) (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) (hW : PosW W) (N₁ : ℕ) (hN : 3 ≤ N₁)
    (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hlam : ∀ j, 0 ≤ lam (γ j)) (μ : Fin (s + 1) → X) :
    ∃ (D D' l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), 1 ≤ D ∧ 1 ≤ D' ∧ (∀ u, a (i₀, u) = μ u) ∧
      Dominant bar φ (D * d) N₁ W γ a ∧
      ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + D' * lam β := by
  have hW0 : 0 < W 0 0 := by
    have h : (0 : ℝ) < ((W + W.transpose).map (Int.cast : ℤ → ℝ)) 0 0 := Matrix.PosDef.diag_pos hW
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_pos] at h
    omega
  obtain ⟨w, hw⟩ : ∃ w : ℕ, W 0 0 = w := ⟨_, (Int.toNat_of_nonneg hW0.le).symm⟩
  have hw1 : 1 ≤ w := by omega
  let lam' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ((2 * w : ℕ) : ℤ) • lam
  have hlam' : ∀ j, 0 ≤ lam' (γ j) := fun j => mul_nonneg (Int.natCast_nonneg _) (hlam j)
  obtain ⟨D₀, hD₀⟩ := _root_.GlobalTheory.Poinc.Gap.exists_gap O bar φ d X hφ r m γ a₀ hγ hs lam' hlam' (∑ j, lam' (γ j) + 1)
  obtain ⟨D, l, a, i₀, hD, hμ, hsp, hlin⟩ := exists_tuple hs.span W hw1 hw lam μ D₀
  obtain ⟨hle, hgap⟩ := hD₀ D hD.le
  have hlin' : ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + lam' β := fun β hβ => hlin β hβ.1
  have key : ∀ (e : X ≃ₗ[O] X) j, pull e.toLinearMap (γ j) = γ j ∨
      lin W a (γ j) < lin W (fun i => e (a i)) (γ j) := fun e j => by
    by_cases h : ∃ j', pull e.toLinearMap (γ j) = γ j'
    · obtain ⟨j', h⟩ := h
      exact Or.inl (hne e j j' h ▸ h)
    right
    have hc : IsCone bar φ ![pull e.toLinearMap (γ j)] := by
      have := (hφ.face _ 1 γ ⟨fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩ hγ).pull_equiv e
      have h0 : ![pull e.toLinearMap (γ j)] = fun _ : Fin 1 => pull e.toLinearMap (γ j) := funext fun i => by simp
      rw [h0]
      exact this
    have h1 := hgap _ hc fun j' hj => h ⟨j', hj⟩
    rw [← hlin' _ (pull_mem _ (hγ.mem j)), evalZ_pull φ (r := e.toLinearMap) e.surjective, mul_assoc, hs.eq j] at h1
    have h2 : D * ∑ i, γ j (a₀ i) (a₀ i) + (∑ j, lam' (γ j) + 1) ≤ lin W a (pull e.toLinearMap (γ j)) := by
      exact_mod_cast h1
    have h3 : lam' (γ j) ≤ ∑ j, lam' (γ j) := Finset.single_le_sum (fun j _ => hlam' j) (Finset.mem_univ j)
    change _ < lin W a (pull e.toLinearMap (γ j))
    rw [hlin' _ (hγ.mem j)]
    omega
  refine ⟨D, 2 * w, l, a, i₀, by omega, by omega, hμ, ⟨hsp, fun β hβ hp => ?_, fun e _ j => ?_, fun e he hx => ?_⟩,
    fun β hβ => hlin β hβ.1⟩
  · rw [hlin' β hβ, Nat.cast_mul]
    exact hle β hβ hp
  · rcases key e j with h | h
    · change _ ≤ lin W a (pull e.toLinearMap (γ j))
      rw [h]
    · exact h.le
  · by_contra hn
    have hfix : ∀ j, pull e.toLinearMap (γ j) = γ j := fun j => (key e j).resolve_right fun h => hn ⟨j, h⟩
    have := GlobalTheory.Poinc.eq_refl_of_isometry_congMod X (∑ j, γ j) (fun x hx => by
      obtain ⟨j, hj⟩ := hpos x hx
      simp only [LinearMap.sum_apply]
      exact Finset.sum_pos' (fun i _ => hγ.nonneg i x) ⟨j, Finset.mem_univ j, hj⟩) e.toAddEquiv.toIntLinearEquiv
      (fun x y => by
        simp only [LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun j _ => LinearMap.congr_fun₂ (hfix j) x y) N₁ hN he
    obtain ⟨x, hx⟩ := hx
    exact hx (LinearEquiv.congr_fun this x)

end GlobalTheory.Poinc.DomTuple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8FormValueCoprimeOddPrimePow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory
open Matrix

theorem exists_e8Form_value_not_dvd_prime (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (p : ℕ) (hp : p.Prime) :
    ∃ ε : Fin 8 → ℤ, ¬ (p : ℤ) ∣ ∑ u, ∑ v, W u v * ε u * ε v := by
  by_contra h
  push_neg at h
  have hQ : ∀ ε : Fin 8 → ℤ, ∑ u, ∑ v, W u v * ε u * ε v = ε ⬝ᵥ (W *ᵥ ε) := by
    intro ε
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have hA : ∀ i j, (p : ℤ) ∣ (W + W.transpose) i j := by
    intro i j
    have h1 := h (Pi.single i 1 + Pi.single j 1)
    have h2 := h (Pi.single i 1)
    have h3 := h (Pi.single j 1)
    rw [hQ] at h1 h2 h3
    have e : (Pi.single i 1 + Pi.single j 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ (Pi.single i 1 + Pi.single j 1))
        - (Pi.single i 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ Pi.single i 1)
        - (Pi.single j 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ Pi.single j 1) = (W + W.transpose) i j := by
      simp [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single_one,
        single_dotProduct]
      ring
    rw [← e]
    exact dvd_sub (dvd_sub h1 h2) h3
  set A := W + W.transpose
  have hB : A = (p : ℤ) • Matrix.of (fun i j => A i j / p) := by
    ext i j
    simp [Int.mul_ediv_cancel' (hA i j)]
  have hdet : A.det = 1 := hW.2
  rw [hB, Matrix.det_smul] at hdet
  have : (p : ℤ) ∣ 1 := by
    rw [← hdet]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by simp)) _
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact hp.one_lt.ne' (by exact_mod_cast this)

theorem exists_e8Form_value_coprime_oddPrimePow' : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (p k : ℕ), p.Prime → p ≠ 2 →
    ∃ ε : Fin 8 → ℤ, Nat.Coprime ((p ^ k) ^ 2) (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
  intro W hW p k hp hp2
  obtain ⟨ε, hε⟩ := exists_e8Form_value_not_dvd_prime W hW p hp
  refine ⟨ε, ?_⟩
  rw [← pow_mul]
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.mul_right
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact hp.one_lt.ne' h
    · exact hp2 h
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact hε (Int.natCast_dvd.2 hd)

end GlobalTheory
end

