module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGroupQuotientPullback
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace CosetQuotient

universe v u

theorem exists_grpObj {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [BraidedCategory C] {G T B : C} [GrpObj G] [IsCommMonObj G] [GrpObj T]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [Mono i]
    [EffectiveEpi q] [EffectiveEpi (q ⊗ₘ q)] [Epi ((q ⊗ₘ q) ⊗ₘ q)]
    (h : ∀ (Z : C) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ T, g' = (t ≫ i) * g) :
    ∃ (_ : GrpObj B), IsCommMonObj B ∧ IsMonHom q ∧ IsPullback i (toUnit _) q (η[B]) := by
  classical
  have same : ∀ {Z : C} (t : Z ⟶ T) (g : Z ⟶ G), ((t ≫ i) * g) ≫ q = g ≫ q :=
    fun t g => ((h _ _ _).2 ⟨t, rfl⟩).symm
  have hw2 : ∀ {Z : C} (g₁ g₂ : Z ⟶ G ⊗ G), g₁ ≫ (q ⊗ₘ q) = g₂ ≫ (q ⊗ₘ q) →
      g₁ ≫ μ[G] ≫ q = g₂ ≫ μ[G] ≫ q := by
    intro Z g₁ g₂ hg
    have h1 : (g₁ ≫ fst G G) ≫ q = (g₂ ≫ fst G G) ≫ q := by
      simpa using hg =≫ fst B B
    have h2 : (g₁ ≫ snd G G) ≫ q = (g₂ ≫ snd G G) ≫ q := by
      simpa using hg =≫ snd B B
    obtain ⟨t, ht⟩ := (h _ _ _).1 h1
    obtain ⟨s, hs⟩ := (h _ _ _).1 h2
    have e : ∀ g : Z ⟶ G ⊗ G, g ≫ μ[G] = (g ≫ fst G G) * (g ≫ snd G G) := by
      intro g
      rw [MonObj.mul_eq_mul, MonObj.comp_mul]
    rw [← Category.assoc, ← Category.assoc, e g₁, e g₂, ht, hs, _root_.mul_mul_mul_comm,
      ← MonObj.mul_comp, same]
  have hw1 : ∀ {Z : C} (g₁ g₂ : Z ⟶ G), g₁ ≫ q = g₂ ≫ q →
      g₁ ≫ ι[G] ≫ q = g₂ ≫ ι[G] ≫ q := by
    intro Z g₁ g₂ hg
    obtain ⟨t, ht⟩ := (h _ _ _).1 hg
    rw [← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def, ht, _root_.mul_inv,
      ← GrpObj.inv_comp, same]
  let mB : B ⊗ B ⟶ B := EffectiveEpi.desc (q ⊗ₘ q) (μ[G] ≫ q) hw2
  have hmB : (q ⊗ₘ q) ≫ mB = μ[G] ≫ q := EffectiveEpi.fac _ _ _
  let iB : B ⟶ B := EffectiveEpi.desc q (ι[G] ≫ q) hw1
  have hiB : q ≫ iB = ι[G] ≫ q := EffectiveEpi.fac _ _ _
  let eB : 𝟙_ C ⟶ B := η[G] ≫ q
  have key : ∀ {Z : C} (a b : Z ⟶ G), lift (a ≫ q) (b ≫ q) ≫ mB = (a * b) ≫ q := by
    intro Z a b
    rw [← CartesianMonoidalCategory.lift_map, Category.assoc, hmB, ← Category.assoc]
    rfl
  have keyL : ∀ {Z : C} (f : Z ⟶ 𝟙_ C) (b : Z ⟶ G), lift (f ≫ eB) (b ≫ q) ≫ mB = b ≫ q := by
    intro Z f b
    have e : f ≫ eB = (f ≫ η[G]) ≫ q := (Category.assoc _ _ _).symm
    rw [e, key, toUnit_unique f (toUnit Z), ← Hom.one_def, _root_.one_mul]
  have keyR : ∀ {Z : C} (a : Z ⟶ G) (f : Z ⟶ 𝟙_ C), lift (a ≫ q) (f ≫ eB) ≫ mB = a ≫ q := by
    intro Z a f
    have e : f ≫ eB = (f ≫ η[G]) ≫ q := (Category.assoc _ _ _).symm
    rw [e, key, toUnit_unique f (toUnit Z), ← Hom.one_def, _root_.mul_one]
  have epiL : Epi (𝟙_ C ◁ q) := by
    have e : 𝟙_ C ◁ q = (λ_ G).hom ≫ q ≫ (λ_ B).inv := by
      rw [← Category.assoc, ← MonoidalCategory.leftUnitor_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  have epiR : Epi (q ▷ 𝟙_ C) := by
    have e : q ▷ 𝟙_ C = (ρ_ G).hom ≫ q ≫ (ρ_ B).inv := by
      rw [← Category.assoc, ← MonoidalCategory.rightUnitor_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  have invL : lift (ι[G] ≫ q) q ≫ mB = (ι[G] * 𝟙 G) ≫ q := by
    have e := key ι[G] (𝟙 G)
    rwa [Category.id_comp] at e
  have invR : lift q (ι[G] ≫ q) ≫ mB = (𝟙 G * ι[G]) ≫ q := by
    have e := key (𝟙 G) ι[G]
    rwa [Category.id_comp] at e
  let inst : GrpObj B :=
    { one := eB
      mul := mB
      inv := iB
      one_mul := by
        apply (cancel_epi (𝟙_ C ◁ q)).1
        have e : 𝟙_ C ◁ q = lift (fst _ _) (snd _ _ ≫ q) := by
          ext
          simp [CartesianMonoidalCategory.leftUnitor_hom]
        rw [e, lift_whiskerRight_assoc, keyL, lift_leftUnitor_hom]
      mul_one := by
        apply (cancel_epi (q ▷ 𝟙_ C)).1
        have e : q ▷ 𝟙_ C = lift (fst _ _ ≫ q) (snd _ _) := by
          ext
          simp [CartesianMonoidalCategory.rightUnitor_hom]
        rw [e, lift_whiskerLeft_assoc, keyR, lift_rightUnitor_hom]
      mul_assoc := by
        apply (cancel_epi ((q ⊗ₘ q) ⊗ₘ q)).1
        have e : (q ⊗ₘ q) ⊗ₘ q = lift (lift ((fst _ _ ≫ fst _ _) ≫ q) ((fst _ _ ≫ snd _ _) ≫ q))
            (snd _ _ ≫ q) := by ext <;> simp
        rw [e]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc,
          lift_whiskerLeft_assoc, key]
        rw [_root_.mul_assoc]
      left_inv := by
        apply (cancel_epi q).1
        rw [← Category.assoc, comp_lift, hiB, Category.comp_id, invL, ← Category.assoc q,
          toUnit_unique (q ≫ toUnit B) (toUnit G), GrpObj.inv_eq_inv, inv_mul_cancel,
          Hom.one_def, Category.assoc]
      right_inv := by
        apply (cancel_epi q).1
        rw [← Category.assoc, comp_lift, hiB, Category.comp_id, invR, ← Category.assoc q,
          toUnit_unique (q ≫ toUnit B) (toUnit G), GrpObj.inv_eq_inv, mul_inv_cancel,
          Hom.one_def, Category.assoc] }
  refine ⟨inst, ⟨?_⟩, ⟨rfl, hmB.symm⟩, ?_⟩
  · show (β_ B B).hom ≫ mB = mB
    apply (cancel_epi (q ⊗ₘ q)).1
    have e : q ⊗ₘ q = lift (fst G G ≫ q) (snd G G ≫ q) := by ext <;> simp
    rw [e, ← Category.assoc, lift_braiding_hom, key, key, _root_.mul_comm]
  · have hsq : i ≫ q = toUnit T ≫ eB := by
      have e := same (𝟙 T) 1
      rw [Category.id_comp, _root_.mul_one] at e
      rw [e, Hom.one_def, Category.assoc]
    have ex : ∀ s : PullbackCone q eB, ∃ t : s.pt ⟶ T, s.fst = t ≫ i := by
      intro s
      have hs : (1 : s.pt ⟶ G) ≫ q = s.fst ≫ q := by
        rw [s.condition, Hom.one_def, toUnit_unique s.snd (toUnit s.pt), Category.assoc]
      obtain ⟨t, ht⟩ := (h _ _ _).1 hs
      exact ⟨t, by rw [ht, _root_.mul_one]⟩
    exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq (fun s => Classical.choose (ex s))
      (fun s => (Classical.choose_spec (ex s)).symm) (fun s => toUnit_unique _ _)
      (fun s m hm _ => by
        rw [← cancel_mono i, hm]
        exact Classical.choose_spec (ex s)))

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}}

lemma effectiveEpi_of_left {X Y : Over S} (f : X ⟶ Y) [EffectiveEpi f.left] :
    EffectiveEpi f := by
  have hw : ∀ {W : Over S} (e : X ⟶ W),
      (∀ {Z : Over S} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) →
      ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ X.left), g₁ ≫ f.left = g₂ ≫ f.left →
        g₁ ≫ e.left = g₂ ≫ e.left := by
    intro W e he Z g₁ g₂ hg
    have h2 : g₂ ≫ X.hom = g₁ ≫ X.hom := by
      rw [← Over.w f, ← Category.assoc, ← hg, Category.assoc]
    have := he (Over.homMk g₁ rfl : Over.mk (g₁ ≫ X.hom) ⟶ X) (Over.homMk g₂ h2)
      (by ext; simpa using hg)
    exact congrArg CommaMorphism.left this
  exact ⟨⟨{
    desc := fun {W} e he => Over.homMk (EffectiveEpi.desc f.left e.left (hw e he)) (by
      rw [← cancel_epi f.left, ← Category.assoc, EffectiveEpi.fac, Over.w e, Over.w f])
    fac := fun {W} e he => by
      ext
      simp [EffectiveEpi.fac]
    uniq := fun {W} e he m hm => by
      ext
      exact EffectiveEpi.uniq f.left e.left (hw e he) m.left (by rw [← Over.comp_left, hm]) }⟩⟩

lemma flat_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hg : Flat g.left] : Flat (f ⊗ₘ g).left := MorphismProperty.pullbackMap (P := @Flat) hf hg (Over.w f).symm (Over.w g).symm

lemma surjective_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Surjective f.left] [hg : Surjective g.left] : Surjective (f ⊗ₘ g).left := by
  have hc : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Surjective :=
    ⟨fun _ _ hf hg => by
      have := hf
      have := hg
      infer_instance⟩
  exact MorphismProperty.pullbackMap (P := @AlgebraicGeometry.Surjective) hf hg (Over.w f).symm
    (Over.w g).symm

lemma quasiCompact_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : QuasiCompact f.left] [hg : QuasiCompact g.left] : QuasiCompact (f ⊗ₘ g).left := MorphismProperty.pullbackMap (P := @QuasiCompact) hf hg (Over.w f).symm (Over.w g).symm

end CosetQuotient

attribute [local instance] Over.cartesianMonoidalCategory

theorem grpObj_of_flat_coset_quotient :
    ∀ (S : Scheme.{0}) (G T B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj T] (i : T ⟶ G)
      (q : G ⟶ B), IsMonHom i → Mono i → Flat q.left → Surjective q.left →
      QuasiCompact q.left →
      (∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ T, g' = (t ≫ i) * g) →
      ∃ (_ : GrpObj B), IsCommMonObj B ∧ IsMonHom q ∧ IsPullback i (toUnit _) q (η[B]) := by
  intro S G T B _ _ _ i q hi hm hf hs hc h
  have e1 : EffectiveEpi q := CosetQuotient.effectiveEpi_of_left q
  have f2 := CosetQuotient.flat_tensorHom q q
  have s2 := CosetQuotient.surjective_tensorHom q q
  have c2 := CosetQuotient.quasiCompact_tensorHom q q
  have e2 : EffectiveEpi (q ⊗ₘ q) := CosetQuotient.effectiveEpi_of_left _
  have f3 := CosetQuotient.flat_tensorHom (q ⊗ₘ q) q
  have s3 := CosetQuotient.surjective_tensorHom (q ⊗ₘ q) q
  have c3 := CosetQuotient.quasiCompact_tensorHom (q ⊗ₘ q) q
  have e3 : EffectiveEpi ((q ⊗ₘ q) ⊗ₘ q) := CosetQuotient.effectiveEpi_of_left _
  exact CosetQuotient.exists_grpObj i q h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionKernel

theorem mem_map_of_flat {R B : Type} [CommRing R] [CommRing B] (c : R →+* B) (hf : c.Flat)
    {I : Ideal R} {ε : R} (h : ∀ x, ε * x = 0 → x ∈ I) (b : B) (hb : c ε * b = 0) :
    b ∈ I.map c := by
  letI := c.toAlgebra
  haveI : Module.Flat R B := hf
  obtain ⟨l, d, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := B)
    (f := fun _ : Unit => ε) (x := fun _ => b)
    (by rw [Fintype.sum_unique, Algebra.smul_def]; exact hb)
  have : b = ∑ j, d () j • y j := hy ()
  rw [this]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem c (h _ ?_))
  have h := hc j
  rwa [Fintype.sum_unique] at h

variable {X Y : Scheme.{0}}

theorem app_rs (i : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (i.app V).hom (rs X h a) = rs Y (i.preimage_mono h) ((i.app U).hom a) := by
  have := congr(($(i.naturality (homOfLE h).op)).hom a)
  exact this

theorem gs_sub (r : Y ⟶ X) (z : Y) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq r z U h, map_sub]

theorem gs_of_app_eq_zero (r : Y ⟶ X) (z : Y) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U))
    (ha : (r.app U).hom a = 0) : gs r z U a = 0 := by rw [gs_eq r z U h, ha, map_zero]

theorem exists_rs_eq_zero {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U))
    (h : (X.presheaf.germ U x hx).hom a = 0) :
    ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ rs X hV a = 0 := by
  obtain ⟨V, hxV, i, i', e⟩ := X.presheaf.germ_eq x hx hx a 0 (h.trans (map_zero _).symm)
  exact ⟨V, i.le, hxV, e.trans (map_zero _)⟩

variable {A A₀ : Type} [CommRing A] [CommRing A₀] {g₀ : A →+* A₀} {a : A}
  {f : X ⟶ Spec (CommRingCat.of A)} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} {j : Y ⟶ X}

theorem cst_eq (f : X ⟶ Spec (CommRingCat.of A)) (W : X.Opens) :
    SmallExtLift.cst f W = cst f W := rfl

theorem mul_eq_zero_iff_app (hg : Function.Surjective g₀)
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) [Flat f]
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) {V : X.Opens} (hV : IsAffineOpen V)
    (u : Γ(X, V)) : cst f V a * u = 0 ↔ (j.app V).hom u = 0 := by
  rw [← cst_eq]
  constructor
  · intro h
    have h := mem_map_of_flat _ (SmallExtLift.cst_flat f hV) (fun x hx => (ha x).1 hx) u h
    refine (show _ ≤ RingHom.ker (j.app V).hom from Ideal.map_le_iff_le_comap.2 fun r hr => ?_) h
    rw [Ideal.mem_comap, RingHom.mem_ker, SmallExtLift.app_cst P.w, RingHom.mem_ker.1 hr, map_zero]
  · intro h
    exact SmallExtLift.mul_eq_zero_of_mem _ (fun x hx => (mul_comm _ _).trans ((ha x).2 hx))
      (SmallExtLift.mem_of_app_eq_zero hg P hV u h)

theorem gs_mul_eq_zero_iff (hg : Function.Surjective g₀)
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) [Flat f]
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) {W : X.Opens} (z : Y) (hz : j z ∈ W)
    (u : Γ(X, W)) : gs (𝟙 X) (j z) W (cst f W a * u) = 0 ↔ gs j z W u = 0 := by
  constructor
  · intro h
    rw [gs_eq (𝟙 X) (j z) W hz] at h
    obtain ⟨V, hV, hx, e⟩ := exists_rs_eq_zero hz (cst f W a * u) h
    obtain ⟨V', hA, hx', hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    have e' := congrArg (rs X hle) e
    rw [rs_rs, map_mul, rs_cst, map_zero] at e'
    rw [← gs_res j z (hle.trans hV) hx']
    exact gs_of_app_eq_zero j z V' hx' _ ((mul_eq_zero_iff_app hg ha P hA _).1 e')
  · intro h
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g₀)) :=
      IsClosedImmersion.spec_of_surjective _ hg
    have : IsClosedImmersion j := MorphismProperty.of_isPullback P.flip this
    rw [gs_eq _ _ W hz] at h
    obtain ⟨O, hO, hx, e⟩ := exists_rs_eq_zero (U := j ⁻¹ᵁ W) hz _ h
    obtain ⟨D, hD, hD'⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp O.isOpen
    have hx₁ : j z ∈ W ⊓ ⟨D, hD⟩ := ⟨hz, show z ∈ j ⁻¹' D from hD' ▸ hx⟩
    obtain ⟨V', hA, hx', hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx₁
    have l : j ⁻¹ᵁ V' ≤ O := fun y hy => by
      have : y ∈ j ⁻¹' D := (hle hy).2
      rwa [hD'] at this
    have e' := congrArg (rs Y l) e
    rw [rs_rs, map_zero] at e'
    have h₂ := (mul_eq_zero_iff_app hg ha P hA (rs X (hle.trans inf_le_left) u)).2
      ((app_rs j _ u).trans e')
    rw [← gs_res (𝟙 X) (j z) (hle.trans inf_le_left) hx']
    refine gs_of_app_eq_zero (𝟙 X) (j z) V' hx' _ ?_
    change rs X _ _ = 0
    rw [map_mul, rs_cst, h₂]

theorem surjective_of_isNilpotent (hg : Function.Surjective g₀)
    (hn : IsNilpotent (RingHom.ker g₀))
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) : Function.Surjective j := by
  have h2 : Surjective (Spec.map (CommRingCat.ofHom g₀)) := ⟨fun x => by
    obtain ⟨n, hn⟩ := hn
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g₀ : Set A) := fun a ha =>
      x.isPrime.mem_of_pow_mem n (by
        have := Ideal.pow_mem_pow ha n
        rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
        rw [this]
        exact zero_mem _)
    rw [← range_comap_of_surjective _ g₀ hg] at hx
    exact hx⟩
  have : Surjective j := MorphismProperty.of_isPullback P.flip h2
  exact j.surjective

theorem exists_sec_of_local {N : LB X} {N₀ : LB Y} (w : LB.Iso N₀ (N.pull j)) (hN₀ : N₀.IsLB)
    (hw : w.IsGen) {I : Type} (V : I → X.Opens) (c : I → N.ι) (hc : ∀ q, V q ≤ N.U (c q))
    (cov : ∀ z : Y, ∃ q, j z ∈ V q) (u : ∀ q, Γ(X, V q))
    (hu : ∀ q q' z, j z ∈ V q → j z ∈ V q' →
      gs j z _ (u q) = (gm j z _ (N.g (c q) (c q'))).val * gs j z _ (u q')) :
    ∃ τ₀ : LB.Sec N₀, ∀ q k' z, j z ∈ V q → z ∈ N₀.U k' →
      (gw w (𝟙 _) z (c q) k').val * gs (𝟙 _) z _ (τ₀.f k') = gs j z _ (u q) := by
  have tr : ∀ q q' k' l' z, j z ∈ V q → j z ∈ V q' → z ∈ N₀.U k' → z ∈ N₀.U l' →
      (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) =
        (gm (𝟙 _) z _ (N₀.g k' l')).val * ((gw w (𝟙 _) z (c q') l')⁻¹.val * gs j z _ (u q')) := by
    intro q q' k' l' z h h' hk hl
    have e := (isGen_iff w).1 hw _ (𝟙 Y) z (c q) (c q') k' l' (hc q h) (hc q' h') hk hl
    rw [Category.id_comp] at e
    rw [hu q q' z h h', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    congr 2
    generalize gm j z _ (N.g (c q) (c q')) = B
    generalize gm (𝟙 Y) z _ (N₀.g k' l') = C
    generalize gw w (𝟙 Y) z (c q') l' = D
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ k' : N₀.ι, ∃ s : Γ(Y, N₀.U k'), ∀ q z, j z ∈ V q → z ∈ N₀.U k' →
      gs (𝟙 _) z _ s = (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) := by
    intro k'
    let O : I → Y.Opens := fun q => j ⁻¹ᵁ V q ⊓ N₀.U k'
    have l₁ : ∀ q, O q ≤ (N.pull j).U (fun _ => c q) ⊓ N₀.U k' := fun q x hx =>
      ⟨mem_pull.2 (hc q hx.1), hx.2⟩
    obtain ⟨b, hb⟩ : ∃ b : ∀ q, Γ(Y, O q), ∀ q z, z ∈ O q →
        gs (𝟙 _) z (O q) (b q) = (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) :=
      ⟨fun q => rs Y (l₁ q) (w.s (fun _ => c q, k'))⁻¹.val *
          rs Y (inf_le_left : O q ≤ j ⁻¹ᵁ V q) ((j.app (V q)).hom (u q)), fun q z hz =>
        (gs_mul (𝟙 Y) z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_res (𝟙 Y) z _ hz _).trans ((gs_unit (𝟙 Y) z _ (l₁ q hz) _).trans
            (congrArg Units.val (map_inv _ _))))
          ((gs_res (𝟙 Y) z _ hz _).trans ((gs_pull (𝟙 Y) j z _ hz.1 _).trans
            (by rw [Category.id_comp]))))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' O (N₀.U k')
      (fun q => homOfLE inf_le_right) (fun z hz => by
        obtain ⟨q, hq⟩ := cov z
        exact Opens.mem_iSup.2 ⟨q, hq, hz⟩) b
      (fun q q' => fn_ext (V := O q ⊓ O q') fun z hz => by
        refine (gs_res (𝟙 Y) z inf_le_left hz _).trans
          (Eq.trans ?_ (gs_res (𝟙 Y) z inf_le_right hz _).symm)
        rw [hb q z hz.1, hb q' z hz.2, tr q q' k' k' z hz.1.1 hz.2.1 hz.1.2 hz.1.2,
          gm_self hN₀ (𝟙 Y) z hz.1.2, Units.val_one, _root_.one_mul])
    refine ⟨s, fun q z h₁ h₂ => ?_⟩
    have hz : z ∈ O q := ⟨h₁, h₂⟩
    exact (gs_res (𝟙 Y) z inf_le_right hz s).symm.trans
      ((congrArg (gs (𝟙 Y) z (O q)) (hs q)).trans (hb q z hz))
  choose s hs using glue
  refine ⟨⟨s, fun k' l' => fn_ext fun z hz => ?_⟩, fun q k' z h₁ h₂ => ?_⟩
  · obtain ⟨q, hq⟩ := cov z
    refine (gs_res (𝟙 Y) z _ hz _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 Y) z _ hz _) (gs_res (𝟙 Y) z _ hz _))).symm)
    rw [hs k' q z hq hz.1, hs l' q z hq hz.2]
    exact tr q q k' l' z hq hq hz.1 hz.2
  · change _ * gs (𝟙 Y) z _ (s k') = _
    rw [hs k' q z h₁ h₂, Units.mul_inv_cancel_left]

theorem exists_sec_of_vanishing : ∀ (A A₀ A' : Type) [CommRing A] [CommRing A₀] [CommRing A'] (g₀ : A →+* A₀) (g' : A →+* A') (a : A), Function.Surjective g₀ → Function.Surjective g' → IsNilpotent (RingHom.ker g₀) → RingHom.ker g' = Ideal.span {a} → a ∈ RingHom.ker g₀ → (∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) → ∀ (X X₀ X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f' : X' ⟶ Spec (CommRingCat.of A')) (j₀ : X₀ ⟶ X) (β : X' ⟶ X), Flat f → IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → ∀ (N : LB X) (N₀ : LB X₀) (w₀ : LB.Iso N₀ (N.pull j₀)), N.IsLB → N₀.IsLB → w₀.IsGen → ∀ σ : LB.Sec N, (∀ k, (β.app (N.U k)).hom (σ.f k) = 0) → ∃ τ₀ : LB.Sec N₀, ∀ τ : LB.Sec N, (∀ z (k : (N).ι) (k' : (N₀).ι), (j₀) z ∈ (N).U k → z ∈ (N₀).U k' → gs (j₀) z _ ((τ).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ₀).f k')) → ∀ k, σ.f k = cst f (N.U k) a * τ.f k := by
  intro A A₀ A' _ _ _ g₀ g' a hg hg' hn hk _ ha X Y X' f f₀ f' j β _ P P' N N₀ w hN hN₀ hw σ hσ
  let I := {q : Σ (_ : N.ι) (W : X.Opens), Γ(X, W) //
    ∃ h : q.2.1 ≤ N.U q.1, rs X h (σ.f q.1) = cst f q.2.1 a * q.2.2}
  let V : I → X.Opens := fun q => q.1.2.1
  let c : I → N.ι := fun q => q.1.1
  let u : ∀ q, Γ(X, V q) := fun q => q.1.2.2
  have hc : ∀ q, V q ≤ N.U (c q) := fun q => q.2.1
  have hu : ∀ q, rs X (hc q) (σ.f (c q)) = cst f (V q) a * u q := fun q => q.2.2
  have loc : ∀ k x, x ∈ N.U k → ∃ q, c q = k ∧ x ∈ V q := by
    intro k x hx
    obtain ⟨W, hW, hxW, hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    have h := SmallExtLift.mem_of_app_eq_zero hg' P' hW (rs X hle (σ.f k))
      (by rw [app_rs, hσ, map_zero])
    rw [hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨⟨⟨k, W, b⟩, hle, hb⟩, rfl, hxW⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_sec_of_local w hN₀ hw V c hc (fun z => by
      obtain ⟨k, hk⟩ := exists_chart hN (j z)
      obtain ⟨q, -, hq⟩ := loc k _ hk
      exact ⟨q, hq⟩) u (fun q q' z h h' => by
      have hm : j z ∈ V q ⊓ V q' := ⟨h, h'⟩
      have e := (gs_mul_eq_zero_iff hg ha P z hm (rs X inf_le_left (u q) -
        rs X (inf_le_inf (hc q) (hc q')) (N.g (c q) (c q')).val * rs X inf_le_right (u q'))).1 (by
          refine gs_of_app_eq_zero (𝟙 X) (j z) _ hm _ ?_
          change (_ : Γ(X, V q ⊓ V q')) = 0
          have e₁ := congrArg (rs X (inf_le_left : V q ⊓ V q' ≤ _)) (hu q)
          have e₂ := congrArg (rs X (inf_le_right : V q ⊓ V q' ≤ _)) (hu q')
          have e₃ := congrArg (rs X (inf_le_inf (hc q) (hc q'))) (σ.compat (c q) (c q'))
          simp only [map_mul, rs_rs, rs_cst] at e₁ e₂ e₃
          change cst f (V q ⊓ V q') a * (_ - _ * _) = 0
          linear_combination e₃ - e₁ + rs X (inf_le_inf (hc q) (hc q')) (N.g (c q) (c q')).val * e₂)
      rw [gs_sub _ _ _ hm, gs_mul _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm,
        gs_unit j z (N.U (c q) ⊓ N.U (c q')) ⟨hc q h, hc q' h'⟩, sub_eq_zero] at e
      exact e)
  refine ⟨τ₀, fun τ hτ k => fn_ext fun x hx => ?_⟩
  obtain ⟨z, rfl⟩ := surjective_of_isNilpotent hg hn P x
  obtain ⟨q, rfl, hq⟩ := loc k _ hx
  obtain ⟨k', hk'⟩ := exists_chart hN₀ z
  have e := (gs_mul_eq_zero_iff hg ha P z hq (u q - rs X (hc q) (τ.f (c q)))).2 (by
    rw [gs_sub _ _ _ hq, gs_res _ _ _ hq, hτ z (c q) k' hx hk', hτ₀ q k' z hq hk', sub_self])
  rw [mul_sub, ← hu, ← rs_cst f (hc q), ← map_mul, gs_sub (𝟙 X) (j z) _ hq, gs_res (𝟙 X) (j z) _ hq,
    gs_res (𝟙 X) (j z) _ hq, sub_eq_zero] at e
  exact e

end GlobalTheory.SectionKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OpenEqTopOfContainsSpecialPartUniversallyClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem eq_top_of_special_part : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y : Over (Spec (CommRingCat.of R))) [UniversallyClosed Y.hom] (U : Y.left.Opens), (∀ z : (thickObj R I 0 Y).left, pullback.fst Y.hom (thick R I 0) z ∈ U) → U = ⊤ := by
  intro R _ I hI Y _ U hU
  by_contra hne
  have hcl : IsClosed (Y.hom '' ((U : Set Y.left)ᶜ)) :=
    Y.hom.isClosedMap _ U.isOpen.isClosed_compl
  have hne' : ((U : Set Y.left)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    exact hne (TopologicalSpace.Opens.ext h)
  obtain ⟨y, hy⟩ := hne'
  let p : PrimeSpectrum R := Y.hom y
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have hspec : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 hpm
  have hq : q ∈ Y.hom '' ((U : Set Y.left)ᶜ) :=
    hspec.mem_closed hcl ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hyq⟩ := hq
  have hr : q ∈ Set.range (thick R I 0) := by
    have h1 : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        PrimeSpectrum.mem_zeroLocus]
      intro x hx
      have hx' : x ∈ I := by simpa using hx
      exact (Ideal.mem_sInf.1 (hI hx')) ⟨bot_le, hm⟩
    exact h1
  have h2 : y' ∈ Set.range (pullback.fst Y.hom (thick R I 0)) := by
    rw [Scheme.Pullback.range_fst]
    show Y.hom y' ∈ Set.range (thick R I 0)
    rw [hyq]; exact hr
  obtain ⟨z, rfl⟩ := h2
  exact hy' (hU z)

end GlobalTheory.Unif
end

