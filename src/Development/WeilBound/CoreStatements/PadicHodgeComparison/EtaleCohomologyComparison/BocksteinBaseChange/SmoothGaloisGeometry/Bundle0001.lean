module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponent

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompactSpaceOfIsProjOver
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison

namespace GeoD


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isProper_pspace (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  have : IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have : IsClosedImmersion (spMap (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) := by
    apply IsClosedImmersion.spec_of_surjective
    rintro ⟨p, hp⟩
    have h0 : p.totalDegree = 0 := Nat.le_zero.1 (MvPolynomial.IsHomogeneous.totalDegree_le hp)
    exact ⟨p.coeff 0, Subtype.ext (MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 h0).symm⟩
  unfold PSpace.str
  infer_instance

theorem compactSpace_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_pspace R N
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)

end GeoD

theorem geoMain : GeometricGenericComponents := by
  intro l _ K M hM d hC
  obtain ⟨hconn, hsm⟩ := hC
  have : Smooth M.q := SmoothOfRelativeDimension.smooth d M.q
  have : CompactSpace M.X := GeoD.compactSpace_of_isProjOver hM.1
  have : QuasiCompact M.p := quasiCompact_of_compactSpace M.p
  have : CompactSpace M.gen := inferInstance
  obtain ⟨r, U, hint, hcov, hdisj, hperm, htrans⟩ := GeoC.exists_components (Ω := PadicAlgCl l) M.q
  have hne : ∀ s, (U s : Set (GlobalTheory.Et.geom (PadicAlgCl l) M.q)).Nonempty := fun s => by
    obtain ⟨⟨y, hy⟩⟩ := (hint s).nonempty
    exact ⟨y, hy⟩
  refine ⟨r, fun s => (U s).toScheme, fun s => (U s).ι, ⟨fun s => inferInstance, fun y => ?_, fun s s' h => ?_⟩,
    hint, fun σ => ?_, fun s s' => ?_⟩
  · obtain ⟨s, hs⟩ := hcov y
    exact ⟨s, by rw [Scheme.Opens.range_ι]; exact hs⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact hdisj s s' h
  · set g := GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ)
    choose f hf using hperm (IntermediateField.fixingSubgroupEquiv K σ)
    have hginj : Function.Injective g := (GeoC.galHomeo M.q (IntermediateField.fixingSubgroupEquiv K σ)).injective
    have hinj : Function.Injective f := by
      intro s s' hss'
      by_contra h
      have h1 : (U s : Set _) = U s' :=
        Set.image_injective.2 hginj ((hf s).trans (hss' ▸ (hf s').symm))
      obtain ⟨y, hy⟩ := hne s
      exact Set.disjoint_left.1 (hdisj s s' h) hy (h1 ▸ hy)
    let π := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
    have hr : ∀ s, Set.range ((U s).ι ≫ g) = Set.range (U (π s)).ι := fun s => by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact hf s
    exact ⟨π, fun s => IsOpenImmersion.isoOfRangeEq ((U s).ι ≫ g) (U (π s)).ι (hr s),
      fun s => (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩
  · obtain ⟨τ, hτ⟩ := htrans s s'
    refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm τ, ?_⟩
    rw [MulEquiv.apply_symm_apply]
    have hr : Set.range ((U s).ι ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ) = Set.range (U s').ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact hτ
    exact ⟨(IsOpenImmersion.isoOfRangeEq _ _ hr).hom, (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩

end CrystallineSemistableComparison
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponentOfNoetherianSpace
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

theorem isOpen_connectedComponent_of_noetherianSpace {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (x : X) : IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have h : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
        isIrreducible_singleton
      refine ⟨Z, ⟨hZ, fun hsub ↦ hy (hsub (hyZ rfl))⟩, hyZ rfl⟩
    · rintro ⟨Z, ⟨hZ, hnot⟩, hyZ⟩ hy
      apply hnot
      have h1 : Z ⊆ connectedComponent y :=
        IsPreconnected.subset_connectedComponent (IsPreirreducible.isPreconnected hZ.1.2) hyZ
      rwa [← connectedComponent_eq hy] at h1
  have hc : IsClosed (connectedComponent x)ᶜ := by
    rw [h]
    exact (hfin.subset (by exact fun Z hZ ↦ hZ.1)).isClosed_biUnion fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1
  exact isClosed_compl_iff.mp hc

theorem finite_connectedComponents_of_noetherianSpace (X : Type*) [TopologicalSpace X] [NoetherianSpace X] :
    Finite (_root_.ConnectedComponents X) := by
  have : DiscreteTopology (_root_.ConnectedComponents X) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage, connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent_of_noetherianSpace x
  have : CompactSpace (_root_.ConnectedComponents X) := inferInstance
  exact finite_of_compact_of_discrete

theorem exists_isSum_components (X : Scheme.{0}) [NoetherianSpace X] :
    ∃ (r : ℕ) (U : Fin r → X.Opens), IsSum (fun a ↦ (U a).ι) ∧ ∀ a, ConnectedSpace (U a).toScheme := by
  have := finite_connectedComponents_of_noetherianSpace X
  let e := Finite.equivFin (_root_.ConnectedComponents X)
  have hopen : ∀ c : _root_.ConnectedComponents X, IsOpen (_root_.ConnectedComponents.mk ⁻¹' {c} : Set X) := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent_of_noetherianSpace x
  let U : Fin (Nat.card (_root_.ConnectedComponents X)) → X.Opens := fun a ↦ ⟨_, hopen (e.symm a)⟩
  refine ⟨_, U, ⟨fun a ↦ inferInstance, fun x ↦ ⟨e (_root_.ConnectedComponents.mk x), ?_⟩, fun a b hab ↦ ?_⟩, fun a ↦ ?_⟩
  · rw [Scheme.Opens.range_ι]
    show _root_.ConnectedComponents.mk x = e.symm (e (_root_.ConnectedComponents.mk x))
    simp
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    refine Set.disjoint_left.mpr fun y hy hy' ↦ hab (e.symm.injective ?_)
    exact (hy : _root_.ConnectedComponents.mk y = _).symm.trans hy'
  · obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e.symm a)
    have hU : ((U a : X.Opens) : Set X) = connectedComponent x := by
      show _root_.ConnectedComponents.mk ⁻¹' {e.symm a} = _
      rw [← hx, connectedComponents_preimage_singleton]
    have : ConnectedSpace ((U a : X.Opens) : Set X) := by
      rw [hU]; exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    exact this

end CrystallineSemistableComparison
end
end

