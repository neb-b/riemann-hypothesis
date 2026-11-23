module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoFibreOfPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.NearFibreIso

open GlobalTheory.DenseFibreIso

variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)

def Near (Q : MorphismProperty Scheme.{0}) (x : X) : Prop :=
  ∃ (T T' : Scheme.{0}) (g : T ⟶ X) (g' : T' ⟶ Y) (f' : T' ⟶ T),
    IsPullback f' g' g f ∧ IsOpenImmersion g ∧ x ∈ Set.range g ∧ Q f'

theorem Near.of_pullback {Q : MorphismProperty Scheme.{0}} {T T' : Scheme.{0}} {g : T ⟶ X}
    {g' : T' ⟶ Y} {f' : T' ⟶ T} (H : IsPullback f' g' g f) [IsOpenImmersion g] {y : T}
    (h : Near f' Q y) : Near f Q (g y) := by
  obtain ⟨T₀, T₀', g₀, g₀', f₀, H₀, hg₀, ⟨z, rfl⟩, hQ⟩ := h
  have := hg₀
  refine ⟨T₀, T₀', g₀ ≫ g, g₀' ≫ g', f₀, H₀.paste_vert H, inferInstance, ⟨z, ?_⟩, hQ⟩
  simp

theorem isIso_fibre_of_pullback {S : Scheme.{0}} (t : S ⟶ Sp R)
    [IsIso (pullback.snd f (pullback.fst s t))] {T T' : Scheme.{0}} {g : T ⟶ X} {g' : T' ⟶ Y}
    {f' : T' ⟶ T} (H : IsPullback f' g' g f) :
    IsIso (pullback.snd f' (pullback.fst (g ≫ s) t)) := by
  have H' : IsPullback (pullback.snd f' (pullback.fst (g ≫ s) t))
      (pullback.fst f' (pullback.fst (g ≫ s) t) ≫ g') (pullback.fst (g ≫ s) t ≫ g) f :=
    (IsPullback.of_hasPullback _ _).flip.paste_vert H
  refine DenseFibreIso.isIso_of_fibre s f t H' (pullback.snd _ _) ?_
  rw [Category.assoc, pullback.condition]

variable (K : Type) [Field K] [Algebra R K]

theorem near_isFinite [IsProper f]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) : Near f @IsFinite x := by
  have hsub : (f ⁻¹' {x}).Subsingleton := by
    let k : Sp K := IsLocalRing.closedPoint K
    have hk : s x = spMap (algebraMap R K) k := by
      apply PrimeSpectrum.ext
      rw [← hx, RingHom.ker_eq_comap_bot, ← Ideal.eq_bot_of_prime k.asIdeal]
      rfl
    obtain ⟨x', hx', -⟩ := Scheme.Pullback.exists_preimage_pullback x k hk
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨z₁, hz₁, hz₁'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := pullback.fst s (spMap (algebraMap R K))) y₁ x' (hy₁.trans hx'.symm)
    obtain ⟨z₂, hz₂, hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := pullback.fst s (spMap (algebraMap R K))) y₂ x' (hy₂.trans hx'.symm)
    have hz : z₁ = z₂ :=
      (pullback.snd f (pullback.fst s (spMap (algebraMap R K)))).isOpenEmbedding.injective
        (hz₁'.trans hz₂'.symm)
    rw [← hz₁, ← hz₂, hz]
  obtain ⟨V, hxV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hsub.finite
  refine ⟨V, f ⁻¹ᵁ V, V.ι, (f ⁻¹ᵁ V).ι, f ∣_ V, isPullback_morphismRestrict f V, inferInstance, ?_, hV⟩
  simpa using hxV

theorem near_isClosedImmersion [hfin : IsFinite f]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f @IsClosedImmersion x := by
  refine DenseFibreIso.local_of_ring s f @IsClosedImmersion K ?_ x hx
  intro A B _ _ _ _ _ _ j j' _ H _ hbij m
  have hf : IsFinite (spMap (algebraMap A B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) H.flip hfin
  have : Module.Finite A B := RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hf)
  obtain ⟨a, ha, hsurj⟩ := DenseFibreIso.exists_away_surjective (A ⊗[R] K) hbij.2 m
  exact ⟨a, ha, IsClosedImmersion.spec_of_surjective _ hsurj⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem near_isIso [hcl : IsClosedImmersion f] [IsLocallyNoetherian X] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  refine DenseFibreIso.local_of_ring s f (MorphismProperty.isomorphisms _) K ?_ x hx
  intro A B _ _ _ _ _ _ j j' hj H hjs hbij m
  have : IsOpenImmersion j' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hj
  have hci : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h1 := (spMap (algebraMap A B)).app_surjective ⊤ (isAffineOpen_top _)
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    intro b
    obtain ⟨c, hc⟩ := h1 ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom c, ?_⟩
    have h3 := congr_arg (fun k => (ConcreteCategory.hom k) c) h2
    simp only [CategoryTheory.comp_apply, CommRingCat.hom_ofHom] at h3
    rw [← h3]
    change (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((spMap (algebraMap A B)).app ⊤ c) = b
    rw [hc]
    simp
  have : IsLocallyNoetherian (Sp A) := isLocallyNoetherian_of_isOpenImmersion j
  have : IsNoetherian (Sp A) := {}
  have : IsNoetherianRing A := isNoetherian_Spec.mp this
  have hflat : Flat (spMap (algebraMap R B)) := by
    have e : spMap (algebraMap R B) = spMap (algebraMap A B) ≫ spMap (algebraMap R A) := by
      change Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rw [e, ← hjs, reassoc_of% H.w]
    infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflat)
  obtain ⟨a, ha, hb⟩ := DenseFibreIso.exists_away_bijective R K hs hbij.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.mpr hb⟩

theorem near_isIso_of_isProper [IsProper f] [IsLocallyNoetherian X] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  obtain ⟨T, T', g, g', f', H, hg, ⟨y, rfl⟩, hQ⟩ := near_isFinite s f K x hx
  have := hg
  have : IsFinite f' := hQ
  have : IsIso (pullback.snd f' (pullback.fst (g ≫ s) (spMap (algebraMap R K)))) :=
    isIso_fibre_of_pullback s f _ H
  have hy : RingHom.ker (algebraMap R K) = ((g ≫ s) y).asIdeal := by simpa using hx
  obtain ⟨T₂, T₂', g₂, g₂', f₂, H₂, hg₂, ⟨y₂, rfl⟩, hQ₂⟩ := near_isClosedImmersion (g ≫ s) f' K y hy
  have := hg₂
  have : IsClosedImmersion f₂ := hQ₂
  have : IsIso (pullback.snd f₂ (pullback.fst (g₂ ≫ g ≫ s) (spMap (algebraMap R K)))) :=
    isIso_fibre_of_pullback (g ≫ s) f' _ H₂
  have : IsLocallyNoetherian T₂ := isLocallyNoetherian_of_isOpenImmersion (g₂ ≫ g)
  have : IsOpenImmersion g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hg
  have : IsOpenImmersion g₂' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H₂ hg₂
  have : Flat (f₂ ≫ g₂ ≫ g ≫ s) := by
    rw [reassoc_of% H₂.w, reassoc_of% H.w]
    infer_instance
  have hy₂ : RingHom.ker (algebraMap R K) = ((g₂ ≫ g ≫ s) y₂).asIdeal := by simpa using hy
  exact Near.of_pullback f H (Near.of_pullback f' H₂ (near_isIso (g₂ ≫ g ≫ s) f₂ K y₂ hy₂))

theorem isOpen_near (Q : MorphismProperty Scheme.{0}) : IsOpen {x : X | Near f Q x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨T, T', g, g', f', H, hg, hx, hQ⟩
  have := hg
  exact ⟨Set.range g, fun z hz => ⟨T, T', g, g', f', H, hg, hz, hQ⟩, g.isOpenEmbedding.isOpen_range, hx⟩

theorem isIso_of_near {S : Scheme.{0}} (t : S ⟶ X)
    (h : ∀ y : S, Near f (MorphismProperty.isomorphisms _) (t y)) : IsIso (pullback.snd f t) := by
  choose T T' g g' f' H hg hx hQ using h
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun y => t ⁻¹ᵁ (g y).opensRange) ?_ fun y => ?_
  · refine eq_top_iff.mpr fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, ?_⟩
    simpa using hx z
  · have := hg y
    have : IsIso (f' y) := hQ y
    have hle : Set.range (Scheme.Opens.ι (t ⁻¹ᵁ (g y).opensRange) ≫ t) ⊆ Set.range (g y) := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    have hu := IsOpenImmersion.lift_fac (g y) _ hle
    have big := (isPullback_morphismRestrict (pullback.snd f t) (t ⁻¹ᵁ (g y).opensRange)).paste_vert
      (IsPullback.of_hasPullback f t).flip
    rw [← hu] at big
    rw [MorphismProperty.isomorphisms.iff]
    exact (big.of_bot' (H y)).isIso_fst_of_isIso

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y X : Scheme.{0}) (s : X ⟶ Sp R) (φ : Y ⟶ X) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → IsProper φ → Flat (φ ≫ s) → IsIso (pullback.snd φ (pullback.fst s (spMap x))) → ∃ f : R, x f ≠ 0 ∧ IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R (Localization.Away f))))) := by
  intro R _ _ Y X s φ K _ x hs _ hφ hflat hiso
  let : Algebra R K := x.toAlgebra
  have : IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R K)))) := hiso
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hU : IsOpen {z : X | Near φ (MorphismProperty.isomorphisms _) z} := isOpen_near φ _
  have hZ : IsClosed (s '' {z : X | Near φ (MorphismProperty.isomorphisms _) z}ᶜ) :=
    s.isClosedMap _ hU.isClosed_compl
  let p : PrimeSpectrum R := ⟨RingHom.ker x, RingHom.ker_isPrime x⟩
  have hp : p ∉ s '' {z : X | Near φ (MorphismProperty.isomorphisms _) z}ᶜ := by
    rintro ⟨z, hz, hsz⟩
    refine hz (near_isIso_of_isProper s φ K z ?_)
    rw [hsz]
    rfl
  obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hZ.isOpen_compl
  refine ⟨f, fun h0 => (PrimeSpectrum.mem_basicOpen _ _).mp hpf (RingHom.mem_ker.mpr h0), ?_⟩
  refine isIso_of_near φ _ fun y => ?_
  by_contra hy
  have hmem : s (pullback.fst s (spMap (algebraMap R (Localization.Away f))) y) ∈
      PrimeSpectrum.basicOpen f := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    refine (PrimeSpectrum.mem_basicOpen _ _).mpr fun hf => ?_
    have hf' : algebraMap R (Localization.Away f) f ∈
        (pullback.snd s (spMap (algebraMap R (Localization.Away f))) y).asIdeal := hf
    exact (pullback.snd s (spMap (algebraMap R (Localization.Away f))) y).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hf' (IsLocalization.Away.algebraMap_isUnit f))
  exact hsub hmem ⟨_, hy, rfl⟩

end GlobalTheory.NearFibreIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullbackFlatOfTame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.TameDescent

theorem specMap_fromSpec_comp_eq_iff {X : Scheme.{0}} (t : X ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : U ≤ t ⁻¹ᵁ U) {k : CommRingCat.{0}} (a : Γ(X, U) ⟶ k) :
    (Spec.map a ≫ hU.fromSpec) ≫ t = Spec.map a ≫ hU.fromSpec ↔
      ∀ b, a.hom ((t.appLE U U h).hom b - b) = 0 := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec t hU hU h, ← Category.assoc,
    cancel_mono, ← Spec.map_comp, Spec.map_injective.eq_iff]
  simp only [map_sub, sub_eq_zero]
  exact ⟨fun e b => congr(($e).hom b), fun e => CommRingCat.hom_ext (RingHom.ext e)⟩

theorem appLE_sub_mem_map {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] (t : Y ⟶ Y) {U : X.Opens}
    {W : Y.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U)
    (h : W ≤ t ⁻¹ᵁ W) {k : Type} [Field k] (a : Γ(X, U) →+* k)
    (ht : pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec) ≫ t =
      pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec)) (c : Γ(Y, W)) :
    (t.appLE W W h).hom c - c ∈ (RingHom.ker a).map (p.appLE U W e).hom := by
  let := a.toAlgebra
  let := (p.appLE U W e).hom.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, W) := p.flat_appLE hU hW e
  refine mem_map_ker_of_one_tmul_eq_zero_of_flat Γ(X, U) Γ(Y, W) k _ ?_
  let r : Γ(Y, W) ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let l : CommRingCat.of k ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  have w : (Spec.map r ≫ hW.fromSpec) ≫ p =
      Spec.map l ≫ Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec := by
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hU hW e,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    exact (CommRingCat.isPushout_tensorProduct Γ(X, U) k Γ(Y, W)).w.symm
  refine (specMap_fromSpec_comp_eq_iff t hW h r).1 ?_ c
  rw [← pullback.lift_fst _ _ w, Category.assoc, ht]

theorem isPullback_specMap_app {X X' : Scheme.{0}} (π : X ⟶ X') [IsAffineHom π] {V : X'.Opens}
    (hV : IsAffineOpen V) :
    IsPullback (Spec.map (π.app V)) (hV.preimage π).fromSpec hV.fromSpec π :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec]) (by simp)

theorem isPullback_of_isPushout_app {X X' Y Y' : Scheme.{0}} (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsAffineHom π] [IsAffineHom φ] (w : φ ≫ p' = p ≫ π)
    (H : ∀ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V → IsAffineOpen W →
      ∀ (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V),
      IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e')) :
    IsPullback φ p p' π := by
  have h : ∀ y : Y', ∃ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V ∧ IsAffineOpen W ∧
      y ∈ W ∧ W ≤ p' ⁻¹ᵁ V := fun y => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p' y)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hy, hle⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ p' ⁻¹ᵁ V from hx) (p' ⁻¹ᵁ V).isOpen
    exact ⟨V, W, hV, hW, hy, hle⟩
  choose V W hV hW hy hle using h
  let 𝒰 : Y'.OpenCover := Scheme.Cover.mkOfCovers Y' (fun y => Spec Γ(Y', W y))
    (fun y => (hW y).fromSpec) (fun y => ⟨y, by
      have : y ∈ Set.range (hW y).fromSpec := by
        rw [IsAffineOpen.range_fromSpec]; exact hy y
      exact this⟩)
  refine Scheme.isPullback_of_openCover φ p p' π 𝒰 fun y => ?_
  have e' : φ ⁻¹ᵁ W y ≤ p ⁻¹ᵁ π ⁻¹ᵁ V y := by
    rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
    exact φ.preimage_mono (hle y)
  have H1 := isPullback_specMap_app φ (hW y)
  have H2 := (isPullback_SpecMap_of_isPushout _ _ _ _
    (H _ _ (hV y) (hW y) (hle y) e')).paste_vert (isPullback_specMap_app π (hV y)).flip.flip
  rw [IsAffineOpen.SpecMap_appLE_fromSpec p _ ((hW y).preimage φ),
    IsAffineOpen.SpecMap_appLE_fromSpec p' _ (hW y)] at H2
  refine H2.of_iso H1.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by simp)
  · exact (Category.comp_id _).trans (H1.flip.isoPullback_hom_snd).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    congr 1
    exact (H1.flip.isoPullback_hom_fst).symm

theorem isPushout_and_flat {Γ : Type} [Group Γ] [Finite Γ] {X X' Y Y' : Scheme.{0}}
    [IsLocallyNoetherian Y'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsFinite π] [IsFinite φ] [Flat p]
    (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    (hπ' : ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
      (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (π.app V).hom)
    (hφ : ∀ g, (τ g).asIso.hom ≫ φ = φ)
    (hφ' : ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    (w : φ ≫ p' = p ≫ π) (hp : ∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom)
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X),
      (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x →
      pullback.fst p x ≫ (τ g).asIso.hom = pullback.fst p x)
    (V : X'.Opens) (W : Y'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V) :
    IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e') ∧
      (p'.appLE V W e).hom.Flat := by
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hU' : IsAffineOpen (φ ⁻¹ᵁ W) := hW.preimage φ
  have hst := preimage_le_of_invariant ρ π hπ V
  have hst' := preimage_le_of_invariant τ φ hφ W
  let := sectionsAction ρ _ hst
  let := sectionsAction τ _ hst'
  let := (π.app V).hom.toAlgebra
  let := (φ.app W).hom.toAlgebra
  let := (p'.appLE V W e).hom.toAlgebra
  let := (p.appLE _ _ e').hom.toAlgebra
  let := (p'.appLE V W e ≫ φ.app W).hom.toAlgebra
  have sq : p'.appLE V W e ≫ φ.app W = π.app V ≫ p.appLE _ _ e' := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, w]
  have : IsScalarTower Γ(X', V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) :=
    .of_algebraMap_eq' congr(($sq).hom)
  have : SMulCommClass Γ Γ(X', V) Γ(X, π ⁻¹ᵁ V) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(X', V) Γ(X, π ⁻¹ᵁ V) a = algebraMap _ _ a :=
      (isInvariantSection_app ρ π hπ V a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : SMulCommClass Γ Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) a = algebraMap _ _ a :=
      (isInvariantSection_app τ φ hφ W a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ := ⟨fun s hs ↦
    (hπ' V).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).asIso.hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩
  have : Algebra.IsInvariant Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    (hφ' W).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (τ g⁻¹⁻¹).asIso.hom.appLE _ _ (hst' _) s = s from hs g⁻¹)⟩
  have heq : ∀ (g : Γ) (b : Γ(X, π ⁻¹ᵁ V)), g • algebraMap _ Γ(Y, φ ⁻¹ᵁ W) b =
      algebraMap _ Γ(Y, φ ⁻¹ᵁ W) (g • b) := fun g b => by
    change (τ g⁻¹).asIso.hom.appLE _ _ (hst' _) (p.appLE _ _ e' b) =
      p.appLE _ _ e' ((ρ g⁻¹).asIso.hom.appLE _ _ (hst _) b)
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hp]
  have hflat : Module.Flat Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) := p.flat_appLE hU hU' e'
  have key : ∀ q : Ideal Γ(X, π ⁻¹ᵁ V), q.IsPrime → ((Nat.card (q.inertia Γ) : Γ(X, π ⁻¹ᵁ V)) ∉ q) ∧
      ∀ g ∈ q.inertia Γ, ∀ c : Γ(Y, φ ⁻¹ᵁ W), g • c - c ∈ q.map (algebraMap _ Γ(Y, φ ⁻¹ᵁ W)) := by
    intro q hq
    let k := AlgebraicClosure q.ResidueField
    let a : Γ(X, π ⁻¹ᵁ V) →+* k := (algebraMap q.ResidueField k).comp (algebraMap _ _)
    have ha : ∀ b, a b = 0 ↔ b ∈ q := fun b => by
      simp [a]
    have hker : RingHom.ker a = q := Ideal.ext ha
    let x : Sp k ⟶ X := Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec
    have hx : ∀ g, x ≫ (ρ g⁻¹).asIso.hom = x ↔ g ∈ q.inertia Γ := fun g =>
      (specMap_fromSpec_comp_eq_iff _ hU (hst _) _).trans (forall_congr' fun b => ha _)
    refine ⟨fun h => htame k x ?_, fun g hg c => ?_⟩
    · rw [← Nat.card_congr ((Equiv.inv Γ).subtypeEquiv (p := fun g => g ∈ q.inertia Γ)
        (q := fun g => x ≫ (ρ g).asIso.hom = x) fun g => (hx g).symm), ← map_natCast a]
      exact (ha _).2 h
    · rw [← hker]
      exact appLE_sub_mem_map p _ hU hU' e' (hst' _) a (hfix k x _ ((hx g).2 hg)) c
  have hpo : Algebra.IsPushout Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) :=
    _root_.GlobalTheory.isPushout_of_tame Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq
      (IsLocallyNoetherian.component_noetherian ⟨W, hW⟩) (π.finite_app V hV) (φ.finite_app W hW)
      hflat (fun q hq => (key q hq).1) (fun q hq => (key q hq).2)
  refine ⟨CommRingCat.isPushout_iff_isPushout.2 hpo.symm, ?_⟩
  exact flat_of_tame_descent Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq hpo hflat
    (exists_finsum_smul_eq_one_of_tame Γ _ fun q hq => (key q hq).1)

theorem isPullback_flat_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → φ ≫ p' = p ≫ π → (∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) → IsFinite π → Flat p → LocallyOfFiniteType p → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst p x ≫ (τ g).asIso.hom = pullback.fst p x) → IsPullback φ p p' π ∧ Flat p' ∧ LocallyOfFiniteType p' := by
  intro Γ _ _ X X' Y Y' _ ρ τ π φ p p' hπ hφ w hp _ _ _ htame hfix
  obtain ⟨_, _, -⟩ := _root_.GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend Γ Y Y' τ φ hφ X' p' (by rw [w]; infer_instance)
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p'
  have H := isPushout_and_flat ρ τ π φ p p' hπ.2.1 hπ.2.2 hφ.2.1 hφ.2.2 w hp htame hfix
  refine ⟨isPullback_of_isPushout_app π φ p p' w fun V W hV hW e e' => (H V W hV hW e e').1,
    ⟨fun {V} hV {W} hW e => (H V W hV hW e ?_).2⟩, inferInstance⟩
  rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  exact φ.preimage_mono e

end GlobalTheory.TameDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppTopPullbackSndOfApp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

private theorem surjective_comp_isIso_of_surjective {A B C : CommRingCat} (a : A ⟶ B) (b : B ⟶ C) [IsIso b]
    (ha : Function.Surjective a.hom) : Function.Surjective (a ≫ b).hom := by
  intro y
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso b).2 y
  obtain ⟨w, rfl⟩ := ha z
  exact ⟨w, rfl⟩

theorem surjective_appTop_pullback_snd_of_app {X S : Scheme.{0}} (f : X ⟶ S) (V : S.Opens)
    (h : ∀ U : S.Opens, Function.Surjective (f.app U).hom) :
    Function.Surjective (pullback.snd f V.ι).appTop.hom := by
  have hr : Function.Surjective (f ∣_ V).appTop.hom := by
    rw [morphismRestrict_appTop]
    exact @surjective_comp_isIso_of_surjective _ _ _ _ _ (Functor.map_isIso _ _) (h _)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V, Scheme.Hom.comp_appTop]
  exact @surjective_comp_isIso_of_surjective _ _ _ _ _
    (inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f V).hom.app ⊤))) hr

theorem exists_gen_of_local_of_section : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (σ : S ⟶ X) (N : LB X), N.IsLB →
    σ ≫ f = 𝟙 S → (∀ U : S.Opens, Function.Surjective (f.app U).hom) →
    (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (N.pull (f ⁻¹ᵁ U).ι).Gen, t.IsGen) →
    (∃ t : (N.pull σ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro X S f σ N hN hσ hf hl hg
  obtain ⟨c, hc⟩ := hg
  have hp : ∀ V : S.Opens, Function.Surjective (pullback.snd f V.ι).appTop.hom :=
    fun V => surjective_appTop_pullback_snd_of_app f V hf
  have e : σ ≫ f ≫ σ = σ := by rw [← Category.assoc, hσ, Category.id_comp]
  have h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U),
      ∏ k, h (σ ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 := by
    intro U _ h
    simp [Fin.prod_univ_two, e]
  have hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb N (fun k => (f ⁻¹ᵁ U).ι ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k)
        (![1, -1] : Fin 2 → ℤ)), t.IsGen := by
    intro s
    obtain ⟨U, hsU, t, ht⟩ := hl s
    refine ⟨U, hsU, ?_⟩
    let c₁ := LB.pullGen N (fun _ : PUnit => σ) (fun _ => 1) c ((f ⁻¹ᵁ U).ι ≫ f)
    have hc₁ : c₁.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ c hc _
    let c₂ := LB.invGen N _ _ c₁
    have hc₂ : c₂.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ c₁ hc₁
    let m := LB.mulGen N (fun _ : PUnit => (f ⁻¹ᵁ U).ι) (fun _ => 1) _ _ t c₂
    have hm : m.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ t c₂ ht hc₂
    obtain ⟨g, hg, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
      (φ' := fun k => (f ⁻¹ᵁ U).ι ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k) (ε' := (![1, -1] : Fin 2 → ℤ))
      (by intro V _ h; simp [Fintype.prod_sum_type, Fin.prod_univ_two]) m hm
    exact ⟨g, hg⟩
  obtain ⟨u, hu⟩ := exists_gen_of_local_on_base hN (K := Fin 2) ![𝟙 X, f ≫ σ] ![1, -1] f σ hσ hp h0 hloc
  let c₃ := LB.pullGen N (fun _ : PUnit => σ) (fun _ => 1) c f
  have hc₃ : c₃.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ c hc f
  let m₂ := LB.mulGen N _ _ _ _ u c₃
  have hm₂ : m₂.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ u c₃ hu hc₃
  obtain ⟨g, hg, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN (φ' := fun _ : PUnit => 𝟙 X) (ε' := fun _ => 1)
    (by intro V _ h; simp [Fintype.prod_sum_type, Fin.prod_univ_two]) m₂ hm₂
  exact BoxTheta.exists_gen_of_section N (𝟙 X) (𝟙 X) (Category.id_comp _) g hg

end GlobalTheory
end
end

