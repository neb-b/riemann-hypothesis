module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory

theorem isLocalization_away_of_isInvariant (G : Type*) [Group G] [Finite G] {B B' : Type*}
    (A A' : Type*) [CommRing B] [CommRing B'] [CommRing A] [CommRing A'] [Algebra B A]
    [Algebra B' A'] [Algebra B B'] [Algebra A A'] [MulSemiringAction G A] [MulSemiringAction G A']
    [SMulCommClass G B A] [SMulCommClass G B' A'] [FaithfulSMul B A] [FaithfulSMul B' A']
    [Algebra.IsInvariant B A G] [Algebra.IsInvariant B' A' G]
    (hc : ∀ b, algebraMap B' A' (algebraMap B B' b) = algebraMap A A' (algebraMap B A b))
    (he : ∀ (g : G) (a : A), algebraMap A A' (g • a) = g • algebraMap A A' a)
    (r : B) [IsLocalization.Away (algebraMap B A r) A'] : IsLocalization.Away r B' := by
  classical
  have hι : Function.Injective (algebraMap B' A') := FaithfulSMul.algebraMap_injective B' A'
  have hBA : Function.Injective (algebraMap B A) := FaithfulSMul.algebraMap_injective B A
  have hinvA : ∀ (g : G) (b : B), g • algebraMap B A b = algebraMap B A b := fun g b ↦ by
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  have hinvA' : ∀ (g : G) (b : B'), g • algebraMap B' A' b = algebraMap B' A' b := fun g b ↦ by
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  have : Fintype G := Fintype.ofFinite G
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    apply IsUnit.pow
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := A') (algebraMap B A r)
    have hinv : ∀ g : G, g • (↑u⁻¹ : A') = ↑u⁻¹ := fun g ↦ by
      have h2 : g • (↑u : A') = ↑u := by rw [hu, ← he, hinvA]
      have h3 : g • (↑u⁻¹ : A') * ↑u = 1 := by
        rw [← h2, ← smul_mul', Units.inv_mul, smul_one]
      exact Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h3)
    obtain ⟨b, hb⟩ := Algebra.IsInvariant.isInvariant (A := B') (G := G) (↑u⁻¹ : A') hinv
    have hb1 : algebraMap B B' r * b = 1 :=
      hι (by rw [map_mul, hb, hc, ← hu, Units.mul_inv, map_one])
    exact ⟨⟨algebraMap B B' r, b, hb1, by rw [mul_comm]; exact hb1⟩, rfl⟩
  · intro z
    obtain ⟨⟨a0, ⟨_, n, rfl⟩⟩, hz⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap B A r)) (algebraMap B' A' z)
    dsimp only at hz
    have hg : ∀ g : G, algebraMap A A' (g • a0) = algebraMap A A' a0 := fun g ↦ by
      rw [he, ← hz, smul_mul', hinvA', ← map_pow, ← he, hinvA]
    choose k hk using fun g : G ↦
      IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap B A r)) (hg g)
    have hcg : ∀ g : G, (∏ h, (k h : A)) * (g • a0) = (∏ h, (k h : A)) * a0 := fun g ↦ by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), mul_assoc, mul_assoc, hk g]
    obtain ⟨K, hK⟩ : (∏ h, (k h : A)) ∈ Submonoid.powers (algebraMap B A r) :=
      Submonoid.prod_mem _ fun h _ ↦ (k h).2
    dsimp only at hK
    have hinv0 : ∀ g : G, g • ((∏ h, (k h : A)) * a0) = (∏ h, (k h : A)) * a0 := fun g ↦ by
      rw [smul_mul', ← hK, smul_pow', hinvA, hK, hcg]
    obtain ⟨b, hb⟩ := Algebra.IsInvariant.isInvariant (A := B) (G := G) _ hinv0
    refine ⟨⟨b, ⟨r ^ (n + K), n + K, rfl⟩⟩, hι ?_⟩
    show algebraMap B' A' (z * algebraMap B B' (r ^ (n + K))) = algebraMap B' A' (algebraMap B B' b)
    rw [map_mul, hc, hc, hb, map_pow, pow_add, map_mul (algebraMap A A') (algebraMap B A r ^ n),
      ← mul_assoc, hz, hK, ← map_mul, mul_comm a0]
  · intro x y hxy
    have h1 : algebraMap A A' (algebraMap B A x) = algebraMap A A' (algebraMap B A y) := by
      rw [← hc, ← hc, hxy]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
      IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap B A r)) h1
    refine ⟨⟨r ^ n, n, rfl⟩, hBA ?_⟩
    simpa only [map_mul, map_pow] using hn

variable {G : Type v} [Group G] {X Y Z : Scheme.{u}}

theorem IsAffineQuotient.of_forall_exists_isOpenImmersion [Finite G] {ρ : G →* Aut X} {π : X ⟶ Y}
    (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    (h : ∀ y : Y, ∃ (X' Y' : Scheme.{u}) (ρ' : G →* Aut X') (π' : X' ⟶ Y') (p : X' ⟶ X)
      (j : Y' ⟶ Y) (_ : IsOpenImmersion p) (_ : IsOpenImmersion j), y ∈ j.opensRange ∧
      p ≫ π = π' ≫ j ∧ π ⁻¹ᵁ j.opensRange = p.opensRange ∧
      (∀ g, (ρ' g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) ∧ IsAffineQuotient ρ' π') :
    IsAffineQuotient ρ π := by
  refine IsAffineQuotient.of_cover hπ fun y ↦ ?_
  obtain ⟨X', Y', ρ', π', p, j, _, _, ⟨y', rfl⟩, hcomm, hpre, hequiv, h'⟩ := h y
  have := h'.isAffineHom
  obtain ⟨W', hW', hyW', -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : Y'.Opens)) (x := y') trivial
  have hWj : j ''ᵁ W' ≤ j.opensRange := j.image_le_opensRange W'
  have hjW : j ⁻¹ᵁ j ''ᵁ W' = W' := j.preimage_image_eq W'
  have hpreW : π ⁻¹ᵁ j ''ᵁ W' ≤ p.opensRange := (π.preimage_mono hWj).trans hpre.le
  have hV : p ⁻¹ᵁ π ⁻¹ᵁ j ''ᵁ W' = π' ⁻¹ᵁ j ⁻¹ᵁ j ''ᵁ W' := by
    change (p ≫ π) ⁻¹ᵁ j ''ᵁ W' = (π' ≫ j) ⁻¹ᵁ j ''ᵁ W'
    rw [hcomm]
  have hπW : π ⁻¹ᵁ j ''ᵁ W' = p ''ᵁ (π' ⁻¹ᵁ W') := by
    rw [show π' ⁻¹ᵁ W' = p ⁻¹ᵁ π ⁻¹ᵁ j ''ᵁ W' by rw [hV, hjW],
      p.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hpreW]
  have hres : ∀ {Z : Scheme.{u}} {A B : Z.Opens} (hAB : A ≤ B) (_ : B ≤ A),
      Function.Bijective (Z.presheaf.map (homOfLE hAB).op) := by
    intro Z A B hAB hBA
    obtain rfl : A = B := le_antisymm hAB hBA
    rw [Subsingleton.elim (homOfLE hAB) (𝟙 A), op_id, Z.presheaf.map_id]
    exact ConcreteCategory.bijective_of_isIso (𝟙 _)
  have hle : π' ⁻¹ᵁ j ⁻¹ᵁ j ''ᵁ W' ≤ p ⁻¹ᵁ π ⁻¹ᵁ j ''ᵁ W' := hV.ge
  have hge : p ⁻¹ᵁ π ⁻¹ᵁ j ''ᵁ W' ≤ π' ⁻¹ᵁ j ⁻¹ᵁ j ''ᵁ W' := hV.le
  have key : π.app (j ''ᵁ W') ≫ p.appLE (π ⁻¹ᵁ j ''ᵁ W') _ hle =
      j.app (j ''ᵁ W') ≫ π'.app (j ⁻¹ᵁ j ''ᵁ W') := by
    rw [Scheme.Hom.app_eq_appLE π, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE j,
      Scheme.Hom.app_eq_appLE π', Scheme.Hom.appLE_comp_appLE]
    congr 1
  have := j.isIso_app (j ''ᵁ W') hWj
  have := p.isIso_app (π ⁻¹ᵁ j ''ᵁ W') hpreW
  refine ⟨j ''ᵁ W', hW'.image_of_isOpenImmersion j, ⟨y', hyW', rfl⟩, ?_, ?_, ?_⟩
  · rw [hπW]
    exact (IsAffineHom.isAffine_preimage W' hW').image_of_isOpenImmersion p
  · intro a b hab
    apply (ConcreteCategory.bijective_of_isIso (j.app (j ''ᵁ W'))).1
    apply h'.app_injective (j ⁻¹ᵁ j ''ᵁ W')
    have e1 := congr($key a)
    have e2 := congr($key b)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at e1 e2
    rw [← e1, ← e2, hab]
  · intro s hs
    have hΦinv : IsInvariantSection ρ' (π' ⁻¹ᵁ j ⁻¹ᵁ j ''ᵁ W')
        (p.appLE (π ⁻¹ᵁ j ''ᵁ W') _ hle s) := by
      intro g
      obtain ⟨e, he⟩ := hs g
      refine ⟨h'.preimage_le (j ⁻¹ᵁ j ''ᵁ W') g, ?_⟩
      have k2 : p.appLE (π ⁻¹ᵁ j ''ᵁ W') _ hle ≫
            (ρ' g).asIso.hom.appLE _ _ (h'.preimage_le (j ⁻¹ᵁ j ''ᵁ W') g) =
          (ρ g).asIso.hom.appLE _ _ e ≫ p.appLE (π ⁻¹ᵁ j ''ᵁ W') _ hle := by
        rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        congr 1
        exact hequiv g
      have := congr($k2 s)
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply, he] at this
      exact this
    obtain ⟨u, hu⟩ := h'.mem_range_app (j ⁻¹ᵁ j ''ᵁ W') _ hΦinv
    obtain ⟨v, rfl⟩ := (ConcreteCategory.bijective_of_isIso (j.app (j ''ᵁ W'))).2 u
    refine ⟨v, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (p.app (π ⁻¹ᵁ j ''ᵁ W'))).1
    apply (hres hle hge).1
    have e1 := congr($key v)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at e1
    exact e1.trans hu

section Diagram

variable (ρ : G →* Aut X)

noncomputable def invariantSections (U : X.Opens) (hU : ∀ g, U ≤ (ρ g).asIso.hom ⁻¹ᵁ U) :
    Subring Γ(X, U) :=
  letI := sectionsAction ρ U hU
  FixedPoints.subring Γ(X, U) G


variable {ρ} in
theorem mem_invariantSections {U : X.Opens} {hU : ∀ g, U ≤ (ρ g).asIso.hom ⁻¹ᵁ U} {s : Γ(X, U)} :
    s ∈ invariantSections ρ U hU ↔ IsInvariantSection ρ U s := by
  constructor
  · intro h g
    have h' : (ρ g⁻¹⁻¹).asIso.hom.appLE U U (hU _) s = s := h g⁻¹
    simp only [inv_inv] at h'
    exact ⟨hU g, h'⟩
  · intro h g
    obtain ⟨_, hg⟩ := h g⁻¹
    exact hg

noncomputable def invariantSectionsRes {U V : X.Opens} (hU : ∀ g, U ≤ (ρ g).asIso.hom ⁻¹ᵁ U)
    (hV : ∀ g, V ≤ (ρ g).asIso.hom ⁻¹ᵁ V) (e : U ≤ V) :
    invariantSections ρ V hV →+* invariantSections ρ U hU :=
  (X.presheaf.map (homOfLE e).op).hom.restrict _ _ fun _ hs ↦
    (mem_invariantSections (ρ := ρ)).mpr (((mem_invariantSections (ρ := ρ)).mp hs).res hU e)

@[simp]
theorem coe_invariantSectionsRes {U V : X.Opens} (hU : ∀ g, U ≤ (ρ g).asIso.hom ⁻¹ᵁ U)
    (hV : ∀ g, V ≤ (ρ g).asIso.hom ⁻¹ᵁ V) (e : U ≤ V) (s : invariantSections ρ V hV) :
    (invariantSectionsRes ρ hU hV e s : Γ(X, U)) = X.presheaf.map (homOfLE e).op s := rfl

private theorem invariantSections_of_stable_open (U : X.Opens) (hU : ∀ g, U ≤ (ρ g).asIso.hom ⁻¹ᵁ U) :
    letI := sectionsAction ρ U hU
    SMulCommClass G (invariantSections ρ U hU) Γ(X, U) ∧
      FaithfulSMul (invariantSections ρ U hU) Γ(X, U) ∧
      Algebra.IsInvariant (invariantSections ρ U hU) Γ(X, U) G := by
  letI := sectionsAction ρ U hU
  refine ⟨⟨fun g s b ↦ ?_⟩, ⟨fun {b₁ b₂} h ↦ Subtype.ext (by simpa [Subring.smul_def] using h 1)⟩,
    ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩⟩
  show g • ((s : Γ(X, U)) * b) = (s : Γ(X, U)) * (g • b)
  rw [smul_mul', s.2 g]

theorem isLocalization_invariantSections [Finite G] {U V : X.Opens}
    (hU : ∀ g, U ≤ (ρ g).asIso.hom ⁻¹ᵁ U) (hV : ∀ g, V ≤ (ρ g).asIso.hom ⁻¹ᵁ V) (e : U ≤ V)
    (hV' : IsAffineOpen V) (r : invariantSections ρ V hV) (hr : X.basicOpen (r : Γ(X, V)) = U) :
    letI := (invariantSectionsRes ρ hU hV e).toAlgebra
    IsLocalization.Away r (invariantSections ρ U hU) := by
  letI := (invariantSectionsRes ρ hU hV e).toAlgebra
  let _ := sectionsAction ρ V hV
  let _ := sectionsAction ρ U hU
  let _ : Algebra Γ(X, V) Γ(X, U) := (X.presheaf.map (homOfLE e).op).hom.toAlgebra
  obtain ⟨_, _, _⟩ := invariantSections_of_stable_open ρ V hV
  obtain ⟨_, _, _⟩ := invariantSections_of_stable_open ρ U hU
  have hloc : IsLocalization.Away (r : Γ(X, V)) Γ(X, U) := by
    subst hr
    exact hV'.isLocalization_basicOpen (r : Γ(X, V))
  have he : ∀ (g : G) (a : Γ(X, V)),
      algebraMap Γ(X, V) Γ(X, U) (g • a) = g • algebraMap Γ(X, V) Γ(X, U) a := by
    intro g a
    change (X.presheaf.map (homOfLE e).op) ((ρ g⁻¹).asIso.hom.appLE V V (hV g⁻¹) a) =
      (ρ g⁻¹).asIso.hom.appLE U U (hU g⁻¹) ((X.presheaf.map (homOfLE e).op) a)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
      Scheme.Hom.map_appLE]
  have : IsLocalization.Away (algebraMap (invariantSections ρ V hV) Γ(X, V) r) Γ(X, U) := hloc
  exact isLocalization_away_of_isInvariant (B := invariantSections ρ V hV)
    (B' := invariantSections ρ U hU) G Γ(X, V) Γ(X, U)
    (fun b ↦ by exact coe_invariantSectionsRes ρ hU hV e b) he r

structure StableAffineOpens : Type u where

  toOpens : X.Opens

  isAffineOpen : IsAffineOpen toOpens

  stable : ∀ g, toOpens ≤ (ρ g).asIso.hom ⁻¹ᵁ toOpens

instance StableAffineOpens.preorder : Preorder (StableAffineOpens ρ) where
  le U V := ∃ f : Γ(X, V.toOpens), X.basicOpen f = U.toOpens
  le_refl U := ⟨1, Scheme.basicOpen_of_isUnit _ isUnit_one⟩
  le_trans U V W h h' := le_trans (α := X.AffineZariskiSite) (a := ⟨_, U.isAffineOpen⟩)
    (b := ⟨_, V.isAffineOpen⟩) (c := ⟨_, W.isAffineOpen⟩) h h'


variable {ρ} in
theorem StableAffineOpens.toOpens_le {U V : StableAffineOpens ρ} (f : U ⟶ V) :
    U.toOpens ≤ V.toOpens := by
  obtain ⟨s, hs⟩ := f.le
  rw [← hs]
  exact X.basicOpen_le s

noncomputable def quotientDiagram : StableAffineOpens ρ ⥤ Scheme.{u} where
  obj U := Spec (.of (invariantSections ρ U.toOpens U.stable))
  map {U V} f := Spec.map (CommRingCat.ofHom
    (invariantSectionsRes ρ U.stable V.stable (StableAffineOpens.toOpens_le f)))
  map_id U := by
    rw [← Spec.map_id]
    congr 1
    ext s
    exact congr($(X.presheaf.map_id (op U.toOpens)) s)
  map_comp {_ _ W} f g := by
    rw [← Spec.map_comp]
    congr 1
    ext s
    exact congr($(X.presheaf.map_comp (homOfLE (StableAffineOpens.toOpens_le g)).op
      (homOfLE (StableAffineOpens.toOpens_le f)).op) (s : Γ(X, W.toOpens)))

namespace StableAffineOpens

variable {ρ}

def basicOpen (U : StableAffineOpens ρ) (r : invariantSections ρ U.toOpens U.stable) :
    StableAffineOpens ρ :=
  ⟨X.basicOpen (r : Γ(X, U.toOpens)), U.isAffineOpen.basicOpen _,
    ((mem_invariantSections (ρ := ρ)).mp r.2).basicOpen_le⟩

noncomputable def toChart (U : StableAffineOpens ρ) :
    Spec Γ(X, U.toOpens) ⟶ (quotientDiagram ρ).obj U :=
  Spec.map (CommRingCat.ofHom (algebraMap (invariantSections ρ U.toOpens U.stable) Γ(X, U.toOpens)))

@[reassoc]
theorem toChart_map {U V : StableAffineOpens ρ} (f : U ⟶ V) :
    U.toChart ≫ (quotientDiagram ρ).map f =
      Spec.map (X.presheaf.map (homOfLE (StableAffineOpens.toOpens_le f)).op) ≫
        V.toChart := by
  dsimp only [toChart, quotientDiagram]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

variable [Finite G]

theorem isAffineQuotient_toChart (U : StableAffineOpens ρ) :
    letI := sectionsAction ρ U.toOpens U.stable
    IsAffineQuotient (specAction G Γ(X, U.toOpens)) U.toChart := by
  letI := sectionsAction ρ U.toOpens U.stable
  have : SMulCommClass G (invariantSections ρ U.toOpens U.stable) Γ(X, U.toOpens) :=
    ⟨fun g s b ↦ by
      show g • ((s : Γ(X, U.toOpens)) * b) = (s : Γ(X, U.toOpens)) * (g • b)
      rw [smul_mul', s.2 g]⟩
  have : FaithfulSMul (invariantSections ρ U.toOpens U.stable) Γ(X, U.toOpens) :=
    ⟨fun {b₁ b₂} h ↦ Subtype.ext (by simpa [Subring.smul_def] using h 1)⟩
  have : Algebra.IsInvariant (invariantSections ρ U.toOpens U.stable) Γ(X, U.toOpens) G :=
    ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩
  exact isAffineQuotient_spec _ _

theorem exists_basicOpen_eq {U V : StableAffineOpens ρ} (h : U ≤ V) :
    ∃ r : invariantSections ρ V.toOpens V.stable, X.basicOpen (r : Γ(X, V.toOpens)) = U.toOpens := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨t, ht, hte⟩ :=
    exists_isInvariantSection_basicOpen_eq V.stable f (by rw [hf]; exact U.stable)
  exact ⟨⟨t, (mem_invariantSections (ρ := ρ)).mpr ht⟩, hte.trans hf⟩

instance isOpenImmersion_map {U V : StableAffineOpens ρ} (f : U ⟶ V) :
    IsOpenImmersion ((quotientDiagram ρ).map f) := by
  obtain ⟨r, hr⟩ := exists_basicOpen_eq f.le
  have e := StableAffineOpens.toOpens_le f
  let := (invariantSectionsRes ρ U.stable V.stable e).toAlgebra
  have := isLocalization_invariantSections ρ U.stable V.stable e V.isAffineOpen r hr
  exact IsOpenImmersion.of_isLocalization r

theorem range_map {U V : StableAffineOpens ρ} (f : U ⟶ V) (r : invariantSections ρ V.toOpens V.stable)
    (hr : X.basicOpen (r : Γ(X, V.toOpens)) = U.toOpens) :
    Set.range ((quotientDiagram ρ).map f) =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (invariantSections ρ V.toOpens V.stable))) := by
  letI := (invariantSectionsRes ρ U.stable V.stable (toOpens_le f)).toAlgebra
  have := isLocalization_invariantSections ρ U.stable V.stable (toOpens_le f) V.isAffineOpen r hr
  exact PrimeSpectrum.localization_away_comap_range (invariantSections ρ U.toOpens U.stable) r

instance isLocallyDirected : (quotientDiagram ρ ⋙ Scheme.forget).IsLocallyDirected where
  cond {U V W} fU fV xU xV e := by
    obtain ⟨r, hr⟩ := exists_basicOpen_eq fU.le
    obtain ⟨s, hs⟩ := exists_basicOpen_eq fV.le
    have e : (quotientDiagram ρ).map fU xU = (quotientDiagram ρ).map fV xV := e
    have hrs : X.basicOpen ((r * s : invariantSections ρ W.toOpens W.stable) : Γ(X, W.toOpens)) =
        U.toOpens ⊓ V.toOpens := by
      rw [Subring.coe_mul, Scheme.basicOpen_mul, hr, hs]
    have hU : W.basicOpen (r * s) ≤ U :=
      ⟨X.presheaf.map (homOfLE (StableAffineOpens.toOpens_le fU)).op s.1,
        (X.basicOpen_res _ _).trans ((congrArg _ hs).trans hrs.symm)⟩
    have hV : W.basicOpen (r * s) ≤ V :=
      ⟨X.presheaf.map (homOfLE (StableAffineOpens.toOpens_le fV)).op r.1,
        (X.basicOpen_res _ _).trans ((congrArg _ hr).trans ((inf_comm _ _).trans hrs.symm))⟩
    obtain ⟨x, hx⟩ : (quotientDiagram ρ).map fU xU ∈
        Set.range ((quotientDiagram ρ).map (homOfLE hU ≫ fU)) := by
      rw [range_map _ (r * s) rfl, PrimeSpectrum.basicOpen_mul]
      exact ⟨(range_map fU r hr).le ⟨_, rfl⟩, (range_map fV s hs).le ⟨_, e.symm⟩⟩
    refine ⟨_, homOfLE hU, homOfLE hV, x,
      ((quotientDiagram ρ).map fU).isOpenEmbedding.injective ?_,
      ((quotientDiagram ρ).map fV).isOpenEmbedding.injective ?_⟩
    · exact congr($((quotientDiagram ρ).map_comp (homOfLE hU) fU) x).symm.trans hx
    · exact congr($((quotientDiagram ρ).map_comp (homOfLE hV) fV) x).symm.trans (hx.trans e)

theorem exists_le_le (U V : StableAffineOpens ρ) {x : X} (hU : x ∈ U.toOpens) (hV : x ∈ V.toOpens) :
    ∃ W : StableAffineOpens ρ, W ≤ U ∧ W ≤ V ∧ x ∈ W.toOpens := by
  obtain ⟨t, ht, hxt, htO⟩ := exists_isInvariantSection_basicOpen_le U.isAffineOpen U.stable hU
    (U.toOpens ⊓ V.toOpens) (fun g ↦ ⟨U.stable g hU, V.stable g hV⟩)
  let U' : StableAffineOpens ρ := ⟨X.basicOpen t, U.isAffineOpen.basicOpen t, ht.basicOpen_le⟩
  obtain ⟨t', ht', hxt', ht'O⟩ := exists_isInvariantSection_basicOpen_le V.isAffineOpen V.stable hV
    U'.toOpens (fun g ↦ ht.basicOpen_le g hxt)
  have hU'V : U'.toOpens ≤ V.toOpens := htO.trans inf_le_right
  refine ⟨⟨X.basicOpen t', V.isAffineOpen.basicOpen t', ht'.basicOpen_le⟩,
    le_trans (b := U') ⟨X.presheaf.map (homOfLE hU'V).op t', ?_⟩ ⟨t, rfl⟩, ⟨t', rfl⟩, hxt'⟩
  rw [Scheme.basicOpen_res]
  exact inf_eq_right.mpr ht'O

theorem exists_le_le_pullback (U V : StableAffineOpens ρ)
    (x : ↑(pullback U.isAffineOpen.fromSpec V.isAffineOpen.fromSpec)) :
    ∃ (W : StableAffineOpens ρ) (hU : W ≤ U) (_ : W ≤ V) (y : Spec Γ(X, W.toOpens)),
      Spec.map (X.presheaf.map (homOfLE (toOpens_le (homOfLE hU))).op) y =
        pullback.fst U.isAffineOpen.fromSpec V.isAffineOpen.fromSpec x := by
  have hU : U.isAffineOpen.fromSpec (pullback.fst U.isAffineOpen.fromSpec V.isAffineOpen.fromSpec x)
      ∈ U.toOpens := U.isAffineOpen.range_fromSpec.le ⟨_, rfl⟩
  have hV : U.isAffineOpen.fromSpec (pullback.fst U.isAffineOpen.fromSpec V.isAffineOpen.fromSpec x)
      ∈ V.toOpens := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact V.isAffineOpen.range_fromSpec.le ⟨_, rfl⟩
  obtain ⟨W, hWU, hWV, hxW⟩ := U.exists_le_le V hU hV
  obtain ⟨y, hy⟩ := W.isAffineOpen.range_fromSpec.ge hxW
  refine ⟨W, hWU, hWV, y, U.isAffineOpen.fromSpec.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, IsAffineOpen.map_fromSpec U.isAffineOpen W.isAffineOpen, hy]

end StableAffineOpens

variable [Finite G] [OrbitsInAffineOpens ρ]

noncomputable abbrev stableAffineCover : X.OpenCover where
  I₀ := StableAffineOpens ρ
  X U := Spec Γ(X, U.toOpens)
  f U := U.isAffineOpen.fromSpec
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨V, hV, hst, hx⟩ := exists_stable_isAffineOpen (ρ := ρ) x
    exact ⟨⟨V, hV, hst⟩, hV.range_fromSpec.ge hx⟩


set_option backward.isDefEq.respectTransparency false in
noncomputable instance locallyDirected_stableAffineCover : (stableAffineCover ρ).LocallyDirected where
  trans f := Spec.map (X.presheaf.map (homOfLE (StableAffineOpens.toOpens_le f)).op)
  trans_id U := by rw [← Spec.map_id]; congr 1; exact X.presheaf.map_id _
  trans_comp f g := by rw [← Spec.map_comp, ← Functor.map_comp]; rfl
  w {U V} f := IsAffineOpen.map_fromSpec V.isAffineOpen U.isAffineOpen _
  property_trans {U V} f :=
    have : IsOpenImmersion (Spec.map (X.presheaf.map
        (homOfLE (StableAffineOpens.toOpens_le f)).op) ≫ V.isAffineOpen.fromSpec) := by
      rw [IsAffineOpen.map_fromSpec V.isAffineOpen U.isAffineOpen]; infer_instance
    .of_comp _ V.isAffineOpen.fromSpec
  directed {U V} x := by
    obtain ⟨W, hU, hV, y, hy⟩ := U.exists_le_le_pullback V x
    refine ⟨W, homOfLE hU, homOfLE hV, y, ?_⟩
    apply (pullback.fst U.isAffineOpen.fromSpec V.isAffineOpen.fromSpec).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hy

end Diagram

noncomputable def finiteQuotient (ρ : G →* Aut X) [Finite G] [OrbitsInAffineOpens ρ] :
    Scheme.{u} :=
  colimit (quotientDiagram ρ)

namespace finiteQuotient

variable (ρ : G →* Aut X) [Finite G] [OrbitsInAffineOpens ρ]

noncomputable def chart (U : StableAffineOpens ρ) :
    (quotientDiagram ρ).obj U ⟶ finiteQuotient ρ :=
  colimit.ι (quotientDiagram ρ) U

instance isOpenImmersion_chart (U : StableAffineOpens ρ) : IsOpenImmersion (chart ρ U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (quotientDiagram ρ) U))

theorem exists_mem_opensRange_chart (y : finiteQuotient ρ) : ∃ U, y ∈ (chart ρ U).opensRange := by
  obtain ⟨U, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (quotientDiagram ρ) y
  exact ⟨U, x, hx⟩

theorem map_chart {U V : StableAffineOpens ρ} (f : U ⟶ V) :
    (quotientDiagram ρ).map f ≫ chart ρ V = chart ρ U := by exact colimit.w (quotientDiagram ρ) f

theorem trans_toChart_chart {U V : StableAffineOpens ρ} (f : U ⟶ V) :
    (stableAffineCover ρ).trans f ≫ V.toChart ≫ chart ρ V = U.toChart ≫ chart ρ U := by
  rw [← map_chart ρ f, StableAffineOpens.toChart_map_assoc]
  rfl

noncomputable def π : X ⟶ finiteQuotient ρ :=
  (stableAffineCover ρ).glueMorphismsOfLocallyDirected (fun U ↦ U.toChart ≫ chart ρ U)
    (trans_toChart_chart ρ)

theorem fromSpec_π (U : StableAffineOpens ρ) : U.isAffineOpen.fromSpec ≫ π ρ = U.toChart ≫ chart ρ U := by exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (stableAffineCover ρ) _ _ U

theorem π_preimage_opensRange_chart (U : StableAffineOpens ρ) :
    π ρ ⁻¹ᵁ (chart ρ U).opensRange = U.toOpens := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨V, hV, hst, hxV⟩ := exists_stable_isAffineOpen (ρ := ρ) x
    let V' : StableAffineOpens ρ := ⟨V, hV, hst⟩
    obtain ⟨x', hx'⟩ := hV.range_fromSpec.ge hxV
    have e : π ρ x = chart ρ V' (V'.toChart x') := by
      rw [← hx', ← Scheme.Hom.comp_apply, fromSpec_π ρ V', Scheme.Hom.comp_apply]
    rw [e] at hy
    obtain ⟨W, fU, fV, w, hwU, hwV⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (quotientDiagram ρ)).mp hy
    obtain ⟨r, hr⟩ := StableAffineOpens.exists_basicOpen_eq fV.le
    have h1 : V'.toChart x' ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (invariantSections ρ V'.toOpens V'.stable))) := by
      rw [← hwV]
      exact (StableAffineOpens.range_map fV r hr).le ⟨w, rfl⟩
    have h2 : x' ∈ PrimeSpectrum.basicOpen (r : Γ(X, V)) := h1
    have h3 : x ∈ X.basicOpen (r : Γ(X, V)) := by
      rw [← hx', ← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen]
      exact h2
    rw [hr] at h3
    exact StableAffineOpens.toOpens_le fU h3
  · intro hx
    obtain ⟨x', rfl⟩ := U.isAffineOpen.range_fromSpec.ge hx
    refine ⟨U.toChart x', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, fromSpec_π]

theorem comp_π (g : G) : (ρ g).asIso.hom ≫ π ρ = π ρ := by
  refine (stableAffineCover ρ).hom_ext _ _ fun U ↦ ?_
  change U.isAffineOpen.fromSpec ≫ (ρ g).asIso.hom ≫ π ρ = U.isAffineOpen.fromSpec ≫ π ρ
  letI := sectionsAction ρ U.toOpens U.stable
  rw [← Category.assoc, ← specAction_fromSpec ρ U.isAffineOpen U.stable g, Category.assoc,
    fromSpec_π, ← Category.assoc, (U.isAffineQuotient_toChart).comp_eq g]

theorem isAffineQuotient : IsAffineQuotient ρ (π ρ) := by
  refine IsAffineQuotient.of_forall_exists_isOpenImmersion (comp_π ρ) fun y ↦ ?_
  obtain ⟨U, hy⟩ := exists_mem_opensRange_chart ρ y
  letI := sectionsAction ρ U.toOpens U.stable
  refine ⟨Spec Γ(X, U.toOpens), (quotientDiagram ρ).obj U, specAction G Γ(X, U.toOpens), U.toChart,
    U.isAffineOpen.fromSpec, chart ρ U, inferInstance, inferInstance, hy, fromSpec_π ρ U, ?_,
    specAction_fromSpec ρ U.isAffineOpen U.stable, U.isAffineQuotient_toChart⟩
  rw [π_preimage_opensRange_chart, U.isAffineOpen.opensRange_fromSpec]

instance surjective_π : Surjective (π ρ) := (isAffineQuotient ρ).surjective

noncomputable def desc (f : X ⟶ Z) (hf : ∀ g, (ρ g).asIso.hom ≫ f = f) : finiteQuotient ρ ⟶ Z :=
  (isAffineQuotient ρ).desc f hf

theorem π_desc (f : X ⟶ Z) (hf : ∀ g, (ρ g).asIso.hom ≫ f = f) : π ρ ≫ desc ρ f hf = f := by exact (isAffineQuotient ρ).comp_desc f hf

theorem hom_ext {a b : finiteQuotient ρ ⟶ Z} (e : π ρ ≫ a = π ρ ≫ b) : a = b := by exact (isAffineQuotient ρ).hom_ext e

theorem comp_π_eq_iff {k : Type u} [Field k] (x y : Spec (.of k) ⟶ X) :
    x ≫ π ρ = y ≫ π ρ ↔ ∃ g, x ≫ (ρ g).asIso.hom = y := by exact (isAffineQuotient ρ).comp_eq_comp_iff x y

section Free

variable {ρ}

theorem isFinite_π_of_isFreeAction (hρ : IsFreeAction ρ) : IsFinite (π ρ) := by exact (isAffineQuotient ρ).isFinite_of_isFreeAction hρ

theorem etale_π (hρ : IsFreeAction ρ) : Etale (π ρ) := by exact (isAffineQuotient ρ).etale_of_isFreeAction hρ

theorem finrank_π (hρ : IsFreeAction ρ) (y : finiteQuotient ρ) : (π ρ).finrank y = Nat.card G := by exact (isAffineQuotient ρ).finrank_of_isFreeAction hρ y

end Free

section Base

variable {S S' : Scheme.{u}} (f : X ⟶ S) (hf : ∀ g, (ρ g).asIso.hom ≫ f = f)


instance locallyOfFiniteType_desc [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    LocallyOfFiniteType (desc ρ f hf) :=
  have : LocallyOfFiniteType (π ρ ≫ desc ρ f hf) := by rwa [π_desc]
  (isAffineQuotient ρ).locallyOfFiniteType _

instance quasiCompact_desc [QuasiCompact f] : QuasiCompact (desc ρ f hf) :=
  have : QuasiCompact (π ρ ≫ desc ρ f hf) := by rwa [π_desc]
  (isAffineQuotient ρ).quasiCompact _

instance isSeparated_desc [IsSeparated f] : IsSeparated (desc ρ f hf) :=
  have : IsSeparated (π ρ ≫ desc ρ f hf) := by rwa [π_desc]
  (isAffineQuotient ρ).isSeparated _

variable (t : S' ⟶ S)

end Base

section Functoriality

variable {H : Type w} [Group H] [Finite H] (τ : H →* Aut Y) [OrbitsInAffineOpens τ]

noncomputable def map (p : X ⟶ Y) (hp : ∀ g, ∃ k, (ρ g).asIso.hom ≫ p = p ≫ (τ k).asIso.hom) :
    finiteQuotient ρ ⟶ finiteQuotient τ :=
  desc ρ (p ≫ π τ) fun g ↦ by
    obtain ⟨k, hk⟩ := hp g
    rw [reassoc_of% hk, comp_π]

@[reassoc (attr := simp)]
theorem π_map (p : X ⟶ Y) (hp : ∀ g, ∃ k, (ρ g).asIso.hom ≫ p = p ≫ (τ k).asIso.hom) :
    π ρ ≫ map ρ τ p hp = p ≫ π τ := by
  unfold map
  exact π_desc ρ _ _

@[simp]
theorem map_id (hp) : map ρ ρ (𝟙 X) hp = 𝟙 _ := by
  apply hom_ext
  simp

theorem map_comp {K : Type*} [Group K] [Finite K] (σ : K →* Aut Z) [OrbitsInAffineOpens σ]
    (p : X ⟶ Y) (q : Y ⟶ Z) (hp hq hpq) :
    map ρ σ (p ≫ q) hpq = map ρ τ p hp ≫ map τ σ q hq := by
  apply hom_ext
  simp

end Functoriality

noncomputable def specIso (B A : Type u) [CommRing B] [CommRing A]
    [MulSemiringAction G A] [Algebra B A] [SMulCommClass G B A] [FaithfulSMul B A]
    [Algebra.IsInvariant B A G] : finiteQuotient (specAction G A) ≅ Spec (.of B) :=
  (isAffineQuotient _).uniqueIso (isAffineQuotient_spec B A)

end finiteQuotient

theorem exists_isAffineQuotient_iff [Finite G] (ρ : G →* Aut X) :
    (∃ (Y : Scheme.{u}) (π : X ⟶ Y), IsAffineQuotient ρ π) ↔ OrbitsInAffineOpens ρ := by
  constructor
  · rintro ⟨Y, π, h⟩
    exact h.orbitsInAffineOpens
  · intro _
    exact ⟨_, _, finiteQuotient.isAffineQuotient ρ⟩

theorem IsAffineQuotient.isAffineOpen_of_preimage [Finite G] {ρ : G →* Aut X} {π : X ⟶ Y}
    (h : IsAffineQuotient ρ π) {W : Y.Opens} (hW : IsAffineOpen (π ⁻¹ᵁ W)) : IsAffineOpen W := by
  classical
  let _ := sectionsAction ρ (π ⁻¹ᵁ W) (h.preimage_le W)
  let _ : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
  obtain ⟨_, _, _⟩ := h.isInvariant W
  have : Algebra.IsIntegral Γ(Y, W) Γ(X, π ⁻¹ᵁ W) :=
    Algebra.IsInvariant.isIntegral (A := Γ(Y, W)) (B := Γ(X, π ⁻¹ᵁ W)) (G := G)
  have := h.surjective
  apply isAffineOpen_of_isAffineOpen_basicOpen W {b : Γ(Y, W) | IsAffineOpen (Y.basicOpen b)} ?_
    fun b hb ↦ hb
  by_contra hne
  obtain ⟨P, hPmax, hsP⟩ := Ideal.exists_le_maximal _ hne
  have := hPmax.isPrime
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P ⊥
    (Ideal.comap_bot_le_of_injective _ (by exact h.app_injective W))
  have hxW : hW.fromSpec ⟨Q, hQ⟩ ∈ π ⁻¹ᵁ W := hW.range_fromSpec.le ⟨_, rfl⟩
  obtain ⟨W0, hW0, hyW0, hW0W⟩ := exists_isAffineOpen_mem_and_subset (x := π (hW.fromSpec ⟨Q, hQ⟩))
    (U := W) hxW
  have hO : ∀ g, (ρ g).asIso.hom (hW.fromSpec ⟨Q, hQ⟩) ∈ π ⁻¹ᵁ W0 := fun g ↦ by
    show π ((ρ g).asIso.hom (hW.fromSpec ⟨Q, hQ⟩)) ∈ W0
    rw [← Scheme.Hom.comp_apply, h.comp_eq g]
    exact hyW0
  obtain ⟨t, ht, hxt, htO⟩ :=
    exists_isInvariantSection_basicOpen_le hW (h.preimage_le W) hxW (π ⁻¹ᵁ W0) hO
  obtain ⟨b, rfl⟩ := h.mem_range_app W t ht
  have hDb : π ⁻¹ᵁ Y.basicOpen b = X.basicOpen (π.app W b) := Scheme.preimage_basicOpen π b
  have hbW0 : Y.basicOpen b ≤ W0 := by
    intro z hz
    obtain ⟨x', rfl⟩ := π.surjective z
    have hx' : x' ∈ π ⁻¹ᵁ Y.basicOpen b := hz
    rw [hDb] at hx'
    exact htO hx'
  have hbs : IsAffineOpen (Y.basicOpen b) := by
    have := hW0.basicOpen (Y.presheaf.map (homOfLE (show W0 ≤ W from hW0W)).op b)
    rwa [Scheme.basicOpen_res, inf_eq_right.mpr hbW0] at this
  have hbP : b ∈ P := hsP (Ideal.subset_span hbs)
  have hbQ : algebraMap Γ(Y, W) Γ(X, π ⁻¹ᵁ W) b ∈ Q := by
    rw [← Ideal.mem_under, hQP]
    exact hbP
  have hx2 : hW.fromSpec ⟨Q, hQ⟩ ∈ X.basicOpen (π.app W b) := hxt
  have hx3 : (⟨Q, hQ⟩ : PrimeSpectrum Γ(X, π ⁻¹ᵁ W)) ∈
      hW.fromSpec ⁻¹ᵁ X.basicOpen (π.app W b) := hx2
  rw [hW.fromSpec_preimage_basicOpen] at hx3
  exact hx3 hbQ

section Stages

variable {H : Type w} [Group H] {ρ : G →* Aut X} {φ : H →* G} {π : X ⟶ Y}

theorem IsAffineQuotient.comp (h : IsAffineQuotient (ρ.comp φ) π) {τ : G →* Aut Y}
    (hτ : ∀ g, π ≫ (τ g).asIso.hom = (ρ g).asIso.hom ≫ π) {π' : Y ⟶ Z} (h' : IsAffineQuotient τ π') :
    IsAffineQuotient ρ (π ≫ π') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    rw [← Category.assoc, ← hτ g, Category.assoc, h'.comp_eq g]
  · have := h.isAffineHom
    have := h'.isAffineHom
    infer_instance
  · intro W a b e
    apply h'.app_injective W
    apply h.app_injective (π' ⁻¹ᵁ W)
    exact e
  · intro W s hs
    obtain ⟨s₁, rfl⟩ := h.mem_range_app (π' ⁻¹ᵁ W) s fun k ↦ hs (φ k)
    have hs₁ : IsInvariantSection τ (π' ⁻¹ᵁ W) s₁ := by
      intro g
      refine ⟨h'.preimage_le W g, ?_⟩
      apply h.app_injective (π' ⁻¹ᵁ W)
      obtain ⟨e, he⟩ := hs g
      have e' : π ⁻¹ᵁ π' ⁻¹ᵁ W ≤ (ρ g).asIso.hom ⁻¹ᵁ π ⁻¹ᵁ π' ⁻¹ᵁ W := e
      have key : (τ g).asIso.hom.appLE (π' ⁻¹ᵁ W) (π' ⁻¹ᵁ W) (h'.preimage_le W g) ≫ π.app (π' ⁻¹ᵁ W) =
          π.app (π' ⁻¹ᵁ W) ≫ (ρ g).asIso.hom.appLE (π ⁻¹ᵁ π' ⁻¹ᵁ W) (π ⁻¹ᵁ π' ⁻¹ᵁ W) e' := by
        rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        congr 1
        exact hτ g
      have := congr($key s₁)
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at this
      exact this.trans he
    obtain ⟨s₂, rfl⟩ := h'.mem_range_app W s₁ hs₁
    exact ⟨s₂, rfl⟩

end Stages

section Over

variable {S : Scheme.{u}} {X : Over S}

def overAction (ρ : G →* Aut X) : G →* Aut X.left :=
  ((Over.forget S).mapAut X).comp ρ

variable (ρ : G →* Aut X) [Finite G] [OrbitsInAffineOpens (overAction ρ)]

end Over



end GlobalTheory
