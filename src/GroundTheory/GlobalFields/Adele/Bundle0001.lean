module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.GlobalFields.Adele.IntegersLattice
section
namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing

theorem discreteTopology_of_isOpen_of_forall_mem {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (H : AddSubgroup G) (U : Set G) (hU : IsOpen U) (h0 : (0 : G) ∈ U)
    (hH : ∀ x ∈ H, x ∈ U → x = 0) : DiscreteTopology H := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert hU.preimage continuous_subtype_val
  ext ⟨x, hx⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · intro h
    have hx0 : x = 0 := by simpa using congrArg Subtype.val h
    rw [hx0]
    exact h0
  · intro h
    exact Subtype.ext (hH x hx h)

variable (K : Type*) [Field K]


open scoped Classical in
noncomputable def homeomorphMixedSpace : K∞ ≃ₜ mixedEmbedding.mixedSpace K :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace K => IsReal v)
      (fun v => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight fun v => (isometryEquivRealOfIsReal v.2).toHomeomorph)
      ((Homeomorph.piCongrRight fun v =>
          (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex))))

theorem homeomorphMixedSpace_apply (x : K∞) :
    homeomorphMixedSpace K x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := rfl

theorem homeomorphMixedSpace_algebraMap (k : K) :
    homeomorphMixedSpace K (algebraMap K K∞ k) = mixedEmbedding K k := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]

theorem homeomorphMixedSpace_sub (x y : K∞) :
    homeomorphMixedSpace K (x - y) = homeomorphMixedSpace K x - homeomorphMixedSpace K y := by
  simp only [homeomorphMixedSpace_apply, map_sub]

variable [NumberField K]

theorem eq_zero_of_forall_infinitePlace_lt_one (z : 𝓞 K) (h : ∀ w : InfinitePlace K, w z < 1) :
    z = 0 := by
  by_contra hz
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact (one_le_of_lt_one hz fun w' _ => h w').not_gt (h w)

omit [NumberField K] in
theorem norm_algebraMap_apply (k : K) (w : InfinitePlace K) :
    ‖algebraMap K K∞ k w‖ = w k := by
  rw [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe]
  rfl

open scoped Classical

noncomputable def fundamentalSetInfinite : Set K∞ :=
  homeomorphMixedSpace K ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)

theorem isCompact_closure_fundamentalSetInfinite :
    IsCompact (closure (fundamentalSetInfinite K)) := by
  rw [fundamentalSetInfinite, ← Homeomorph.preimage_closure, Homeomorph.isCompact_preimage]
  exact (ZSpan.fundamentalDomain_isBounded _).isCompact_closure

theorem existsUnique_sub_mem_fundamentalSetInfinite (x : K∞) :
    ∃! z : 𝓞 K, x - algebraMap (𝓞 K) K∞ z ∈ fundamentalSetInfinite K := by
  set b := mixedEmbedding.latticeBasis K
  have hmem : ∀ z : 𝓞 K, mixedEmbedding K (z : K) ∈ Submodule.span ℤ (Set.range b) := by
    intro z
    rw [mixedEmbedding.mem_span_latticeBasis]
    exact ⟨z, rfl⟩
  have himg : ∀ z : 𝓞 K, homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z) =
      homeomorphMixedSpace K x - mixedEmbedding K (z : K) := by
    intro z
    rw [homeomorphMixedSpace_sub, IsScalarTower.algebraMap_apply (𝓞 K) K K∞,
      homeomorphMixedSpace_algebraMap]
  have hinj : Function.Injective fun z : 𝓞 K => mixedEmbedding K (z : K) :=
    (mixedEmbedding K).injective.comp RingOfIntegers.coe_injective
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 K, mixedEmbedding K (z : K) =
      (ZSpan.floor b (homeomorphMixedSpace K x) : mixedEmbedding.mixedSpace K) := by
    have := (ZSpan.floor b (homeomorphMixedSpace K x)).2
    rw [mixedEmbedding.mem_span_latticeBasis] at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hz⟩
  refine ⟨z, ?_, fun z' hz' => ?_⟩
  · change homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z) ∈ ZSpan.fundamentalDomain b
    rw [himg, hz]
    exact ZSpan.fract_mem_fundamentalDomain b _
  · replace hz' : homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z') ∈
        ZSpan.fundamentalDomain b := hz'
    rw [himg] at hz'
    have h1 : homeomorphMixedSpace K x - mixedEmbedding K (z : K) ∈ ZSpan.fundamentalDomain b := by
      rw [hz]
      exact ZSpan.fract_mem_fundamentalDomain b _
    rw [← ZSpan.fract_eq_self] at h1 hz'
    have heq : ZSpan.fract b (homeomorphMixedSpace K x - mixedEmbedding K (z' : K)) =
        ZSpan.fract b (homeomorphMixedSpace K x - mixedEmbedding K (z : K)) := by
      rw [ZSpan.fract_eq_fract]
      have : -(homeomorphMixedSpace K x - mixedEmbedding K (z' : K)) +
          (homeomorphMixedSpace K x - mixedEmbedding K (z : K)) =
          mixedEmbedding K (z' : K) - mixedEmbedding K (z : K) := by abel
      rw [this]
      exact Submodule.sub_mem _ (hmem z') (hmem z)
    rw [hz', h1] at heq
    exact hinj (sub_right_injective heq)

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.Adele.WeakApprox
section
namespace GroundTheory.Global

open IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]

section AbsoluteValues

theorem adicAbv_lt_one_iff_mem (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K x) < 1 ↔ x ∈ v.asIdeal := by
  rw [← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem K v x

theorem adicAbv_isNontrivial (v : HeightOneSpectrum (𝓞 K)) : (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · simpa using hx0
  · exact ((adicAbv_lt_one_iff_mem v x).2 hxv).ne

theorem not_isEquiv_adicAbv {v v' : HeightOneSpectrum (𝓞 K)} (h : v ≠ v') :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv (NumberField.HeightOneSpectrum.adicAbv K v') := by
  intro he
  have hle : ¬ v.asIdeal ≤ v'.asIdeal := fun hle ↦
    h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle))
  obtain ⟨x, hxv, hxv'⟩ := Set.not_subset.1 hle
  have h1 := (adicAbv_lt_one_iff_mem v x).2 hxv
  rw [he.lt_one_iff] at h1
  exact hxv' ((adicAbv_lt_one_iff_mem v' x).1 h1)

theorem not_isEquiv_adicAbv_infinitePlace (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro he
  have h1 : NumberField.HeightOneSpectrum.adicAbv K v (2 : K) ≤ 1 := by
    simpa using NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2
  rw [he.le_one_iff] at h1
  have h2 : w.1 (2 : K) = 2 := by
    have h := w.map_natCast 2
    rw [Nat.cast_ofNat, Nat.cast_ofNat] at h
    exact h
  linarith

end AbsoluteValues

section Density

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))

noncomputable def placeAbv : S ⊕ T → AbsoluteValue K ℝ :=
  Sum.elim (fun v ↦ NumberField.HeightOneSpectrum.adicAbv K v.1) (fun w ↦ w.1.1)

theorem placeAbv_isNontrivial : ∀ i, (placeAbv S T i).IsNontrivial
  | .inl v => adicAbv_isNontrivial v.1
  | .inr w => w.1.isNontrivial

theorem placeAbv_pairwise_not_isEquiv :
    Pairwise fun i j ↦ ¬ (placeAbv S T i).IsEquiv (placeAbv S T j) := by
  rintro (⟨v, hv⟩ | ⟨w, hw⟩) (⟨v', hv'⟩ | ⟨w', hw'⟩) hij he
  · exact not_isEquiv_adicAbv (fun h ↦ hij (by subst h; rfl)) he
  · exact not_isEquiv_adicAbv_infinitePlace v w' he
  · exact not_isEquiv_adicAbv_infinitePlace v' w he.symm
  · exact hij (by
      have : w = w' := InfinitePlace.eq_iff_isEquiv.2 he
      subst this; rfl)

theorem isometry_algebraMap_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    Isometry ((algebraMap K (v.adicCompletion K)).comp
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v)).toRingHom) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_
  rw [WithAbs.norm_eq_apply_ofAbs, ← FinitePlace.norm_embedding]
  rfl

theorem denseRange_algebraMap_prod_pi :
    DenseRange (fun x : K ↦ ((fun v : S ↦ algebraMap K (v.1.adicCompletion K) x),
      (fun w : T ↦ algebraMap K w.1.Completion x))) := by
  classical
  let φ : ∀ v : S, WithAbs (placeAbv S T (.inl v)) → v.1.adicCompletion K := fun v ↦
    (algebraMap K (v.1.adicCompletion K)).comp
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).toRingHom
  let ψ : ∀ w : T, WithAbs (placeAbv S T (.inr w)) → w.1.Completion := fun w y ↦
    ((show WithAbs w.1.1 from y) : w.1.Completion)
  have hφc : ∀ v, Continuous (φ v) := fun v ↦ (isometry_algebraMap_adicCompletion v.1).continuous
  have hφd : ∀ v, DenseRange (φ v) := by
    intro v
    have h := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v.1
    unfold DenseRange at h ⊢
    convert h using 1
    show Set.range (⇑(algebraMap K (v.1.adicCompletion K)) ∘
      ⇑(WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1))) = _
    exact (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).surjective.range_comp _
  have hψc : ∀ w, Continuous (ψ w) := fun w ↦ InfinitePlace.Completion.continuous_coe w.1
  have hψd : ∀ w, DenseRange (ψ w) := fun w ↦ InfinitePlace.Completion.denseRange_coe w.1
  let e := Homeomorph.sumPiEquivProdPi S T (fun i ↦ WithAbs (placeAbv S T i))
  have hc : Continuous (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e) :=
    ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap
      (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w))).comp e.continuous
  have hg : DenseRange (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e) :=
    ((DenseRange.piMap hφd).prodMap (DenseRange.piMap hψd)).comp e.surjective.denseRange
      ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap
        (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w)))
  have hd := AbsoluteValue.denseRange_algebraMap_pi (placeAbv_isNontrivial S T)
    (placeAbv_pairwise_not_isEquiv S T)
  convert hg.comp hd hc using 1
  funext x
  simp [φ, ψ, e, Function.comp_apply, Homeomorph.sumPiEquivProdPi]
  constructor
  · funext v
    simp [Pi.map, WithAbs.equiv, placeAbv]
    rfl
  · funext w
    simp [Pi.map, placeAbv]
    exact AbsoluteValue.Completion.algebraMap_def (R := K) (v := w.1.1) x

end Density

end GroundTheory.Global
end

