module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LeOfZpowMulUnitEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.PowCmp
section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

def cstR (M : Model R A) (U : M.Y.left.Opens) : R →+* Γ(M.Y.left, U) :=
  (M.Y.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem j_cstR (M : Model R A) (U : M.Y.left.Opens) (r : R) :
    (M.j.app U).hom (cstR M U r) = cstK A _ (algebraMap R K r) := by
  have e := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  have h1 : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U = (M.j ≫ M.Y.hom).appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h2 : (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top
      = (A.hom ≫ spMap (algebraMap R K)).appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    exact (Scheme.Hom.comp_appLE A.hom (spMap (algebraMap R K)) ⊤ _ _).symm
  have h3 : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U = (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [h1, h2]; simp only [M.j_hom]
  have h4 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) h3
  exact h4.trans (congrArg (A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top).hom e.symm)

theorem not_isUnit_cstR [IsLocalRing R] (M : Model R A) (U : M.Y.left.Opens) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty)
    {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) : ¬ IsUnit (cstR M U π) := by
  intro hu
  obtain ⟨y, hy, hs⟩ := h
  have h1 : M.Y.left.basicOpen (cstR M U π) = U := M.Y.left.basicOpen_of_isUnit hu
  have h2 : M.Y.left.basicOpen (cstR M U π) = U ⊓ M.Y.hom ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π) :=
    Scheme.basicOpen_appLE M.Y.hom U ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)
  rw [h1, basicOpen_eq_of_affine (R := CommRingCat.of R) π] at h2
  have h4 := (h2.le hy).2
  have h6 : M.Y.hom y = IsLocalRing.closedPoint R := hs
  have h7 : π ∉ PrimeSpectrum.asIdeal (M.Y.hom y) := h4
  rw [h6] at h7
  exact h7 hπ

theorem j_app_injective [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens) :
    Function.Injective (M.j.app U).hom := by
  have := M.smooth
  have : IsDominant (spMap (algebraMap R K)) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  have : IsSchemeTheoreticallyDominant (pullback.fst M.Y.hom (spMap (algebraMap R K))) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K))).flip
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : IsSchemeTheoreticallyDominant M.j := by unfold Model.j; infer_instance
  have : QuasiCompact M.j := by unfold Model.j; infer_instance
  exact M.j.app_injective U

end

theorem le_of_zpow_mul_unit_eq : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) (M : Model R A) (W : M.Y.left.Opens), ((W : Set M.Y.left) ∩ M.sp).Nonempty → ∀ (σ s : Γ(M.Y.left, W)) (a b : ℤ), IsUnit σ → cstK A (M.j ⁻¹ᵁ W) (algebraMap R K π ^ a) * (M.j.app W).hom σ = cstK A (M.j ⁻¹ᵁ W) (algebraMap R K π ^ b) * (M.j.app W).hom s → b ≤ a := by
  intro R K _ _ _ _ _ _ π hirr A M U hU σ s a b hs e'
  by_contra hlt
  have hπ : π ∈ IsLocalRing.maximalIdeal R := hirr.not_isUnit
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + (k + 1 : ℕ) := ⟨(b - a - 1).toNat, by omega⟩
  have hp : algebraMap R K π ≠ 0 := by simpa using hirr.ne_zero
  have hu : IsUnit (cstK A (M.j ⁻¹ᵁ U) (algebraMap R K π ^ a)) := (IsUnit.mk0 _ (zpow_ne_zero a hp)).map _
  rw [hk, zpow_add₀ hp, map_mul, _root_.mul_assoc, zpow_natCast, ← map_pow, ← j_cstR, ← map_mul] at e'
  have := j_app_injective M U (hu.mul_left_cancel e')
  rw [this, pow_succ, map_mul] at hs
  exact not_isUnit_cstR M U hU hπ (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hs))

end GlobalTheory.SS.PowCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuasiFiniteAtAffineSpaceHomOfVectorOfCoord
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem isOpen_singleton_of_isClosed_of_generization {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X)
    (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → y = x) : IsOpen ({x} : Set X) := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  have hemb := (X.affineCover.f i).isOpenEmbedding
  rw [← Set.image_singleton, ← hemb.isOpen_iff_image_isOpen]
  have hN : IsLocallyNoetherian (X.affineCover.X i) := isLocallyNoetherian_of_isOpenImmersion (X.affineCover.f i)
  have hA : IsAffine (X.affineCover.X i) := inferInstance
  have : IsNoetherian (X.affineCover.X i) := {}
  have hcl : IsClosed ({y} : Set (X.affineCover.X i)) := by
    have := hx.preimage hemb.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ hemb.injective] at this
  have hgen : ∀ z, z ⤳ y → z = y := fun z hz => hemb.injective (h _ (hz.map hemb.continuous))
  clear hx h hemb
  generalize X.affineCover.X i = Y at *
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hc : IsClosed (⋃ Z ∈ {Z ∈ irreducibleComponents Y | y ∉ Z}, Z) :=
    (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  convert hc.isOpen_compl using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
  constructor
  · rintro rfl Z hZ hz
    exact hZ.2 hz
  · intro H
    have hm := irreducibleComponent_mem_irreducibleComponents z
    have hy : y ∈ irreducibleComponent z := by
      by_contra hy
      exact H _ ⟨hm, hy⟩ mem_irreducibleComponent
    have hg := (isIrreducible_irreducibleComponent (x := z)).isGenericPoint_genericPoint
      isClosed_irreducibleComponent
    have e := hgen _ (hg.specializes hy)
    rw [e] at hg
    have : z ∈ closure {y} := by
      rw [hg.def]; exact mem_irreducibleComponent
    rwa [hcl.closure_eq] at this

theorem quasiFiniteAt_of_isClosed_of_generization {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → f y = f x → y = x) : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  have hemb := (f.fiberι (f x)).isEmbedding
  have hx' : f.fiberι (f x) (f.asFiber x) = x := by simp
  apply isOpen_singleton_of_isClosed_of_generization
  · have := hx.preimage hemb.continuous
    convert this using 1
    ext z
    exact ⟨fun hz => by rw [hz]; exact hx', fun hz => hemb.injective (hz.trans hx'.symm)⟩
  · intro y hy
    apply hemb.injective
    rw [hx']
    apply h
    · have := hy.map hemb.continuous
      rwa [hx'] at this
    · have : f.fiberι (f x) y ∈ f ⁻¹' {f x} := by
        rw [← f.range_fiberι]; exact ⟨y, rfl⟩
      exact this

theorem eq_of_specializes_of_basicOpen {X : Scheme.{0}} {y x : X} (h : y ⤳ x)
    (H : ∀ (U : X.Opens) (_ : x ∈ U) (s : Γ(X, U)), y ∈ X.basicOpen s → x ∈ X.basicOpen s) : y = x := by
  refine (h.antisymm ?_).eq
  rw [specializes_iff_forall_open]
  intro V hV hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  obtain ⟨s, hs, hys⟩ := IsAffineOpen.exists_basicOpen_le hU (V := ⟨V, hV⟩) ⟨y, hy⟩ hyU
  exact hs (H U hxU s hys)

theorem quasiFiniteAt_homOfVector_of_coord : ∀ (C : Core) (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsClosed ({w} : Set C.G.toScheme) → C.Coord w W hw u → (AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i))).QuasiFiniteAt ⟨w, hw⟩ := by
  intro C w W hw u hcl hco
  have := C.proper
  have hlft : LocallyOfFiniteType C.GG.hom := inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom))
  unfold Core.Coord at hco
  change IsLocalRing.maximalIdeal (C.GG.left.presheaf.stalk w) = _ at hco
  set f := AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i)) with hf
  have hover : f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z) = W.ι ≫ C.GG.hom := AffineSpace.homOfVector_over _ _
  have : LocallyOfFiniteType (f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z)) := by
    rw [hover]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (𝔸(Fin C.g; C.Z) ↘ C.Z)
  have hemb := W.ι.isOpenEmbedding
  apply quasiFiniteAt_of_isClosed_of_generization
  · have := hcl.preimage hemb.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff
  intro y hy hfy
  have hy' : y.1 ⤳ w := hy.map hemb.continuous
  have hg : C.GG.hom y.1 = C.GG.hom w := by
    have e : ∀ t : W.toScheme, C.GG.hom t.1 = (𝔸(Fin C.g; C.Z) ↘ C.Z) (f t) := by
      intro t
      rw [← Scheme.Hom.comp_apply, hover]; rfl
    rw [e y, hfy, ← e ⟨w, hw⟩]
  apply Subtype.ext
  let P : Ideal (C.G.toScheme.presheaf.stalk w) :=
    (IsLocalRing.maximalIdeal _).comap (C.G.toScheme.presheaf.stalkSpecializes hy').hom
  have hP : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)),
      (C.G.toScheme.presheaf.germ U w hU).hom s ∈ P ↔ y.1 ∉ C.G.toScheme.basicOpen s := by
    intro U hU s
    rw [C.G.toScheme.mem_basicOpen s y.1 (hy'.mem_open U.2 hU), Ideal.mem_comap,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← CommRingCat.comp_apply,
      TopCat.Presheaf.germ_stalkSpecializes]
  have hm : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)),
      (C.G.toScheme.presheaf.germ U w hU).hom s ∈ IsLocalRing.maximalIdeal _ ↔
        w ∉ C.G.toScheme.basicOpen s := by
    intro U hU s
    rw [C.G.toScheme.mem_basicOpen s w hU, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hle : IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w) ≤ P := by
    refine hco.le.trans (sup_le ?_ ?_)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : w ∉ C.G.toScheme.basicOpen (u i) := by
        rw [← hm W hw]
        exact hco.ge (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      have e : ∀ t : W.toScheme, t.1 ∈ C.G.toScheme.basicOpen (u i) ↔
          f t ∈ Scheme.basicOpen _ (AffineSpace.coord C.Z i) := by
        intro t
        have e1 : f ⁻¹ᵁ Scheme.basicOpen _ (AffineSpace.coord C.Z i) =
            W.toScheme.basicOpen (W.topIso.inv.hom (u i)) := by
          rw [Scheme.preimage_basicOpen_top, hf, AffineSpace.homOfVector_appTop_coord]
        have e2 := W.ι_image_basicOpen_topIso_inv (u i)
        rw [← e2, ← e1]
        exact Scheme.Hom.apply_mem_image_iff W.ι (x := t)
      refine (hP W hw (u i)).2 ?_
      rw [e y, hfy, ← e ⟨w, hw⟩]
      exact h1
    · refine (Ideal.IsPrime.radical_le_iff inferInstance).2 ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨V, hV, s, rfl⟩ := C.Z.presheaf.exists_germ_eq a
      rw [Ideal.mem_comap, Scheme.Hom.germ_stalkMap_apply]
      refine (hP _ _ _).2 ?_
      have h1 : C.GG.hom w ∉ C.Z.basicOpen s := by
        rw [C.Z.mem_basicOpen s _ hV]
        exact ha
      rw [← hg] at h1
      intro h2
      apply h1
      have e := Scheme.preimage_basicOpen C.GG.hom s
      exact e.ge h2
  apply eq_of_specializes_of_basicOpen hy'
  intro U hU s hs
  by_contra hn
  exact (hP U hU s).1 (hle ((hm U hU s).2 hn)) hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestCartOfSpecialFibreSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem eq_of_injective_baseChange {S S' H X H' X' : Scheme.{0}} {q : S' ⟶ S} {s : X ⟶ S} {h : H ⟶ X}
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') (h ≫ s) q) (w : a ≫ h = h' ≫ b)
    (hinj : Function.Injective h') {x y : H} (hxy : h x = h y) (hx : s (h x) ∈ Set.range q) : x = y := by
  have sq : IsPullback a h' h b := IsPullback.of_bot hH w hX
  obtain ⟨t, ht⟩ := hx
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback hX (h x) t ht.symm
  obtain ⟨x', rfl, hx'⟩ := Scheme.exists_preimage_of_isPullback sq x z hz.symm
  obtain ⟨y', rfl, hy'⟩ := Scheme.exists_preimage_of_isPullback sq y z (hxy.symm.trans hz.symm)
  rw [hinj (hx'.trans hy'.symm)]

theorem mem_range_of_surjective_baseChange {S S' H X H' X' : Scheme.{0}} {q : S' ⟶ S} {s : X ⟶ S} {h : H ⟶ X}
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (w : a ≫ h = h' ≫ b)
    (hsurj : Function.Surjective h') {z : X} (hz : s z ∈ Set.range q) : z ∈ Set.range h := by
  obtain ⟨t, ht⟩ := hz
  obtain ⟨z', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hX z t ht.symm
  obtain ⟨x, rfl⟩ := hsurj z'
  exact ⟨a x, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩

theorem surjective_of_isClosedImmersion_of_points {k : Type} [Field k] [IsAlgClosed k] {H X : Scheme.{0}}
    (h : H ⟶ X) [IsClosedImmersion h] (s : X ⟶ Sp k) [LocallyOfFiniteType s]
    (hs : ∀ x : Sp k ⟶ X, x ≫ s = 𝟙 _ → ∃ c : Sp k ⟶ H, c ≫ h = x) : Function.Surjective h := by
  have hJ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  rw [← Set.range_eq_univ]
  by_contra hne
  obtain ⟨x, hx, hx'⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
    h.isClosedEmbedding.isClosed_range.isOpen_compl.isLocallyClosed
  obtain ⟨c, hc⟩ := hs _ (pointOfClosedPoint_comp s x hx')
  let a : Sp k := IsLocalRing.closedPoint k
  refine hx ⟨c a, ?_⟩
  rw [← Scheme.Hom.comp_apply, hc]
  exact pointOfClosedPoint_apply s x hx' _

theorem eq_closedPoint_or_mem_range (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (x : Sp T) :
    x = IsLocalRing.closedPoint T ∨ x ∈ Set.range (spMap (algebraMap T K)) := by
  by_cases hx : PrimeSpectrum.asIdeal x = ⊥
  · refine Or.inr ⟨(⊥ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [hx]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)
  · refine Or.inl (PrimeSpectrum.ext ?_)
    exact IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isPrime x).isMaximal hx)

theorem isIso_of_genericFibre_of_specialFibre (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K]
    {H X S' H' X' : Scheme.{0}} (h : H ⟶ X) (s : X ⟶ Sp T) (u : H ⟶ Sp T) (hu : h ≫ s = u)
    [Smooth s] [IsSeparated s] [Smooth u] [IsSeparated u] [QuasiCompact u]
    [ConnectedSpace ↥(pullback u (spMap (algebraMap T K)))]
    (hK : IsPullback (pullback.fst u (spMap (algebraMap T K)) ≫ h) (pullback.snd u (spMap (algebraMap T K)))
      s (spMap (algebraMap T K)))
    {q : S' ⟶ Sp T} (hq : IsLocalRing.closedPoint T ∈ Set.range q)
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') u q) (w : a ≫ h = h' ≫ b)
    (hbij : Function.Bijective h') : IsIso h := by
  subst hu
  let t := spMap (algebraMap T K)
  have : IsOpenImmersion t := isOpenImmersion_spMap_of_isDiscreteValuationRing T K
  have : ConnectedSpace ↥(pullback s t) :=
    hK.isoPullback.hom.surjective.connectedSpace hK.isoPullback.hom.continuous
  obtain ⟨hXi, hN⟩ := isIntegral_and_isNormalScheme_of_smooth T K s
  obtain ⟨hHi, -⟩ := isIntegral_and_isNormalScheme_of_smooth T K (h ≫ s)
  have : IsSeparated h := IsSeparated.of_comp h s
  have : QuasiCompact h := QuasiCompact.of_comp h s
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h s
  let j := pullback.fst (h ≫ s) t
  have hj : IsPullback j (𝟙 _ ≫ pullback.snd (h ≫ s) t) (h ≫ s) t := by
    rw [Category.id_comp]; exact .of_hasPullback _ _
  have hinj : Function.Injective h := fun x y hxy ↦ by
    rcases eq_closedPoint_or_mem_range T K (s (h x)) with hx | hx
    · exact eq_of_injective_baseChange hX hH w hbij.1 hxy (hx ▸ hq)
    · exact eq_of_injective_baseChange hK hj (Category.id_comp _).symm
        (fun _ _ e ↦ e) hxy hx
  have hsurj : Function.Surjective h := fun z ↦ by
    rcases eq_closedPoint_or_mem_range T K (s z) with hx | hx
    · exact mem_range_of_surjective_baseChange hX w hbij.2 (hx ▸ hq)
    · exact mem_range_of_surjective_baseChange (h' := 𝟙 _) hK (Category.id_comp _).symm
        (fun e ↦ ⟨e, rfl⟩) hx
  have : LocallyQuasiFinite h := LocallyQuasiFinite.of_injective hinj
  have : IsOpenImmersion (j ≫ h) := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hK.flip ‹_›
  have : IsOpenImmersion (j.opensRange.ι ≫ h) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance
  have : IsOpenImmersion h :=
    isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict h (fun y ↦ (hN y).2)
      j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩
  exact (isIso_iff_isOpenImmersion_and_surjective h).mpr ⟨this, ⟨hsurj⟩⟩

theorem isPullback_of_comp_mono {𝒞 : Type*} [Category 𝒞] {A G P U Z : 𝒞} {a : A ⟶ G} {i : G ⟶ P} [Mono i]
    {s : A ⟶ U} {t : P ⟶ Z} {u : U ⟶ Z} (h : IsPullback (a ≫ i) s t u) : IsPullback a s (i ≫ t) u :=
  ⟨⟨by rw [← Category.assoc, h.w]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ h.lift (c.fst ≫ i) c.snd (by rw [Category.assoc, c.condition]))
    (fun c ↦ by rw [← cancel_mono i, Category.assoc, h.lift_fst]) (fun c ↦ h.lift_snd _ _ _)
    (fun c m h₁ h₂ ↦ h.hom_ext (by rw [h.lift_fst, ← Category.assoc, h₁]) (by rw [h.lift_snd, h₂]))⟩⟩

theorem isAlgClosed_residueField_OO (p : ℕ) [Fact p.Prime] : IsAlgClosed (kb p) :=
  GlobalTheory.NormIntegers.isAlgClosed_residueField
    (Valuation.valuationSubring.integers (Valued.v : Valuation (PadicAlgCl p) NNReal))

theorem Core.testCart_of_fib :
    ∀ C : Core, C.Fib → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart := by
  intro C hF hS p _ y τ
  have := isAlgClosed_residueField_OO p
  have := C.proper
  have := τ.smooth
  have := τ.sep
  have := τ.qc
  have := τ.j_loc
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  have : IsSeparated C.GG.hom := inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))
  let K := FractionRing τ.V
  let t : Sp K ⟶ Sp τ.V := spMap (algebraMap τ.V K)
  let q : Sp (kb p) ⟶ Sp τ.V := rPt p ≫ spMap τ.j
  have hqy : q ≫ τ.y₀ = rPt p ≫ y := by rw [Category.assoc, τ.fac]
  let h : τ.H.left ⟶ pullback C.GG.hom τ.y₀ := pullback.lift τ.f τ.H.hom τ.f_over
  have h₁ : h ≫ pullback.fst _ _ = τ.f := pullback.lift_fst _ _ _
  have h₂ : h ≫ pullback.snd _ _ = τ.H.hom := pullback.lift_snd _ _ _

  have hA : IsPullback C.a C.A.hom C.GG.hom C.U.ι :=
    isPullback_of_comp_mono C.cart
  have hφ : IsPullback τ.φ (pullback.snd τ.H.hom t) C.A.hom τ.yK := τ.φ_cart.1
  have := C.ab.geomConnected
  have : ConnectedSpace ↥(pullback τ.H.hom t) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ hφ
  have hK : IsPullback (pullback.fst τ.H.hom t ≫ h) (pullback.snd τ.H.hom t) (pullback.snd C.GG.hom τ.y₀) t := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, h₂, pullback.condition])
      (IsPullback.of_hasPullback C.GG.hom τ.y₀)
    have := hφ.paste_horiz hA
    rw [τ.φ_f, τ.yK_fac] at this
    rw [Category.assoc, h₁]
    exact this

  let h' : pullback τ.H.hom q ⟶ pullback C.GG.hom (rPt p ≫ y) :=
    pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by
      rw [Category.assoc, τ.f_over, pullback.condition_assoc, hqy])
  have h₁' : h' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h₂' : h' ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion h' := τ.imm h' h₁' h₂'
  let b : pullback C.GG.hom (rPt p ≫ y) ⟶ pullback C.GG.hom τ.y₀ :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ q) (by
      rw [Category.assoc, hqy, pullback.condition])
  have b₁ : b ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have b₂ : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q := pullback.lift_snd _ _ _
  have hX : IsPullback b (pullback.snd _ _) (pullback.snd C.GG.hom τ.y₀) q := by
    refine IsPullback.of_right ?_ b₂ (IsPullback.of_hasPullback C.GG.hom τ.y₀)
    rw [b₁, hqy]
    exact .of_hasPullback _ _
  have hsurj : Function.Surjective h' := by
    refine surjective_of_isClosedImmersion_of_points h' (pullback.snd _ _) fun x hx ↦ ?_
    obtain ⟨c, hc₁, hc₂⟩ := hF p y τ (x ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])
    refine ⟨pullback.lift c (𝟙 _) (by rw [Category.id_comp]; exact hc₁), pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, h₁', pullback.lift_fst_assoc, hc₂]
    · rw [Category.assoc, h₂', pullback.lift_snd, hx]
  have hq : IsLocalRing.closedPoint τ.V ∈ Set.range q := by
    refine ⟨IsLocalRing.closedPoint (kb p), ?_⟩
    exact IsLocalRing.comap_closedPoint ((IsLocalRing.residue (OO p)).comp τ.j)
  have : IsIso h := isIso_of_genericFibre_of_specialFibre τ.V K h (pullback.snd _ _) τ.H.hom h₂ hK hq hX
    (a := pullback.fst _ _) (h' := h') (by rw [h₂']; exact .of_hasPullback _ _)
    (pullback.hom_ext (by simp only [Category.assoc, h₁, b₁, h₁'])
      (by simp only [Category.assoc, h₂, b₂, reassoc_of% h₂', pullback.condition]))
    ⟨h'.isClosedEmbedding.injective, hsurj⟩
  exact IsPullback.of_iso_pullback ⟨τ.f_over⟩ (asIso h) h₁ h₂

end GlobalTheory.ZJ
end

