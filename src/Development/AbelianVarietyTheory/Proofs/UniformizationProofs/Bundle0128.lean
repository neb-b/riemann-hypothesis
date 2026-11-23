module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleProductAcyclicOfAffineBaseAcyclic
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProductAcyclic

theorem acyclic_of_homology_equiv {R : Type} [CommRing R] {C C' : CochainComplex (ModuleCat.{0} R) ℕ}
    (e : ∀ n, Nonempty (C.homology n ≃ₗ[R] C'.homology n)) (h : C.Acyclic) : C'.Acyclic := by
  intro n
  obtain ⟨e⟩ := e n
  have h₁ := h n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
  exact e.symm.injective.subsingleton

theorem exists_cover (X : Scheme.{0}) [CompactSpace X] {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀)
    (O : X.Opens) (h : ∀ x, x ∉ V₀ → x ∈ O) :
    ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      V 0 = V₀ ∧ ∀ j, j ≠ 0 → V j ≤ O := by
  have hc : IsCompact (V₀ : Set X)ᶜ := V₀.isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : {W : X.Opens // IsAffineOpen W ∧ W ≤ O} => (W.1 : Set X)) (fun W => W.1.isOpen) (by
      intro x hx
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (h x hx) O.isOpen
      exact Set.mem_iUnion.2 ⟨⟨W, hW, hWo⟩, hxW⟩)
  refine ⟨s.card, Fin.cons V₀ fun j => (s.equivFin.symm j).1.1, fun j => ?_, ?_, rfl, fun j hj => ?_⟩
  · refine Fin.cases hV₀ (fun j => ?_) j
    exact (s.equivFin.symm j).1.2.1
  · refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hx : x ∈ V₀
    · exact ⟨0, hx⟩
    · obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.1 (hs hx)
      refine ⟨(s.equivFin ⟨W, hW⟩).succ, ?_⟩
      simpa using hxW
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hj
    exact (s.equivFin.symm j).1.2.2

variable {K : Type} [Field K] {Z T X : Scheme.{0}} {p : Z ⟶ T} {g : T ⟶ Spec (CommRingCat.of K)}
  {q : Z ⟶ X} {h : X ⟶ Spec (CommRingCat.of K)} {F : LB Z}

theorem over_affineOpen (sq : IsPullback p q g h) [IsSeparated h] (hF : F.IsLB)
    {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ T} [IsOpenImmersion t] {Y : Scheme.{0}}
    {π : Y ⟶ Z} {f : Y ⟶ Spec (CommRingCat.of R)} (H : IsPullback π f p t)
    {V : T.Opens} (hV : t.opensRange = V) {ν : Type} [LinearOrder ν] [Fintype ν]
    (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i)) (hc : ⨆ i, B i = ⊤) :
    (∀ i, IsAffineOpen (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V)) ∧
    ((∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → (cechLB f (F.pull π) D).Acyclic) ↔
      (cechLB (p ≫ g) F fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V).Acyclic) := by
  have H' : IsPullback (π ≫ q) f h (t ≫ g) := H.paste_horiz sq.flip
  have : IsOpenImmersion π := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H.flip ‹_›
  have hq : IsAffineHom (π ≫ q) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) H'.flip inferInstance
  have hsep : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) H' ‹_›
  have hr : π.opensRange = p ⁻¹ᵁ V := by
    subst hV
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact ⟨f y, by rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]⟩
    · rintro x ⟨y, hy⟩
      obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback H x y hy.symm
      exact ⟨w, hw⟩
  have hE (i : ν) : π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) = (π ≫ q) ⁻¹ᵁ B i := by
    rw [← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq,
      Scheme.Hom.comp_preimage]
  have hA (i : ν) : IsAffineOpen ((π ≫ q) ⁻¹ᵁ B i) := (hB i).preimage _
  have hA' (i : ν) : IsAffineOpen (π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V)) :=
    (congrArg IsAffineOpen (hE i)).mpr (hA i)
  have hc' : ⨆ i, π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) = ⊤ := by
    simp only [hE]
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  obtain ⟨e⟩ := cechLB_pull_iso_of_isOpenImmersion K _ (p ≫ g) F _ π ν
    (fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) hF fun i => hr ▸ inf_le_right
  refine ⟨fun i => ?_, fun h₁ n => ?_, fun h₁ κ _ _ D hD hDc => ?_⟩
  · have h₁ := (hA i).image_of_isOpenImmersion π
    rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm] at h₁
  · exact (MumfordCohom.acyclic_cechLB_of_acyclic _ _ _ _ (h₁ ν _ hA' hc') n).of_iso e
  · exact acyclic_of_homology_equiv (cechLB_homology_equiv_of_affine_covers R Y f _ ν _ κ D
      (LB.isLB_pull hF π) hsep hA' hc' hD hDc)
      (MumfordCohom.acyclic_cechLB_of_acyclic _ _ _ _ fun n => (h₁ n).of_iso e.symm)

theorem isAffineOpen_prod (sq : IsPullback p q g h) [IsSeparated h] (hF : F.IsLB) {V : T.Opens}
    (hV : IsAffineOpen V) {ν : Type} [LinearOrder ν] [Fintype ν]
    (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i)) (hc : ⨆ i, B i = ⊤) (i : ν) :
    IsAffineOpen (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) :=
  (over_affineOpen (R := Γ(T, V)) sq hF (IsPullback.of_hasPullback p hV.fromSpec)
    hV.opensRange_fromSpec B hB hc).1 i

theorem homology_equiv_over (sq : IsPullback p q g h) [IsSeparated g] [IsSeparated h] (hF : F.IsLB)
    {σ : Type} [LinearOrder σ] [Fintype σ] (V : σ → T.Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hVc : ⨆ j, V j = ⊤) (k : σ)
    (H : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z)
      (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t →
      ∀ j, j ≠ k → (∀ y, t y ∈ V j) →
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → (cechLB f (F.pull π) D).Acyclic)
    {ν : Type} [LinearOrder ν] [Fintype ν] (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i))
    (hBc : ⨆ i, B i = ⊤) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens)
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) (n : ℕ) :
    Nonempty ((cechLB (p ≫ g) F D).homology n ≃ₗ[K]
      (cechLB (p ≫ g) F fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V k).homology n) := by
  have : T.IsSeparated := ⟨by
    rw [← terminal.comp_from g]
    infer_instance⟩
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from h]
    infer_instance⟩
  have : IsSeparated p := MorphismProperty.of_isPullback (P := @IsSeparated) sq.flip ‹_›
  obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ K _ (p ≫ g) F κ D _
    (fun i => q ⁻¹ᵁ B i) _ (fun j => p ⁻¹ᵁ V j) hF inferInstance hD hc
    (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
    (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
    (fun i _ hW => MumfordCohom.isAffineOpen_preimage_inf _ (hB i) hW)
    (fun j _ hW => MumfordCohom.isAffineOpen_preimage_inf _ (hV j) hW)
    (fun i j => isAffineOpen_prod sq hF (hV j) B hB hBc i) n
  have e₂ := trunc₂HomologyIsoFstSingleton k (secCube (p ≫ g) F fun u : ν ⊕ₗ σ =>
      Sum.elim (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) (ofLex u))
    (fun s hs hs' => by
      have hVs : IsAffineOpen (⨅ j ∈ s, V j) :=
        IsAffineOpen.biInf _ s.finite_toSet hs fun j _ => hV j
      obtain ⟨j, hj, hjk⟩ : ∃ j ∈ s, j ≠ k := by
        by_contra! h₀
        exact hs' (Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨hs, h₀⟩)
      have H₀ := IsPullback.of_hasPullback p hVs.fromSpec
      have h₁ := (over_affineOpen (R := Γ(T, ⨅ j ∈ s, V j)) sq hF H₀ hVs.opensRange_fromSpec
        B hB hBc).2.1 (H Γ(T, ⨅ j ∈ s, V j) _ _ _ _ H₀ inferInstance j hjk
          fun y => biInf_le V hj (hVs.range_fromSpec.le ⟨y, rfl⟩))
      obtain ⟨i₂⟩ := MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
        (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) s _ (preimage_biInf V p s)
      exact fun m => (h₁ m).of_iso i₂) n
  obtain ⟨i₂⟩ := MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
    (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) {k} (p ⁻¹ᵁ V k) (by simp)
  exact ⟨e₁ ≪≫ₗ (e₂ ≪≫ (HomologicalComplex.homologyMapIso i₂ n).symm).toLinearEquiv⟩

theorem acyclic_of_over_affine_and_converse : ∀ (K : Type) [Field K] (Z T : Scheme.{0}) (p : Z ⟶ T) (g : T ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0}) (q : Z ⟶ X) (h : X ⟶ Spec (CommRingCat.of K)), IsPullback p q g h → IsSeparated g → QuasiCompact g → IsSeparated h → QuasiCompact h → ∀ F : LB Z, F.IsLB → ((∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic)) ∧ ∀ t₀ : T, IsClosed ({t₀} : Set T) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ y, t y ≠ t₀) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) := by
  intro K _ Z T p g X q h sq _ _ _ _ F hF
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  obtain ⟨m, B, hB, hBc, -, -⟩ := exists_cover X (isAffineOpen_bot X) ⊤ fun _ _ => trivial
  refine ⟨fun H κ _ _ D hD hc => ?_, fun t₀ ht₀ H hac R _ t Y π f H₀ ht => ?_⟩
  · obtain ⟨r, V, hV, hVc, -, -⟩ := exists_cover T (isAffineOpen_bot T) ⊤ fun _ _ => trivial
    have H₀ := IsPullback.of_hasPullback p (hV 0).fromSpec
    refine acyclic_of_homology_equiv (fun n => ?_) ((over_affineOpen (R := Γ(T, V 0)) sq hF H₀
      (hV 0).opensRange_fromSpec B hB hBc).2.1 (H Γ(T, V 0) _ _ _ _ H₀ inferInstance))
    exact (homology_equiv_over sq hF V hV hVc 0
      (fun R _ t Y π f H₁ ht _ _ _ => H R t Y π f H₁ ht) B hB hBc D hD hc n).map fun e => e.symm
  · by_cases h₀ : t₀ ∈ t.opensRange
    swap
    · exact H R t Y π f H₀ ht fun y hy => h₀ ⟨y, hy⟩
    obtain ⟨r, V, hV, hVc, hV₀, hV₁⟩ := exists_cover T (isAffineOpen_opensRange t)
      ⟨{t₀}ᶜ, ht₀.isOpen_compl⟩ fun x hx hx' => hx ((show x = t₀ from hx') ▸ h₀)
    let P : Fin (m + 1) ×ₗ Fin (r + 1) → Z.Opens := fun u =>
      q ⁻¹ᵁ B (ofLex u).1 ⊓ p ⁻¹ᵁ V (ofLex u).2
    have hP (u) : IsAffineOpen (P u) := isAffineOpen_prod sq hF (hV _) B hB hBc _
    have hPc : ⨆ u, P u = ⊤ := by
      refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hBc.ge (Set.mem_univ (q x)))
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hVc.ge (Set.mem_univ (p x)))
      exact ⟨toLex (i, j), hi, hj⟩
    refine (over_affineOpen sq hF H₀ hV₀.symm B hB hBc).2.2 ?_
    exact acyclic_of_homology_equiv (homology_equiv_over sq hF V hV hVc 0
      (fun R _ t Y π f H₁ ht j hj hy => H R t Y π f H₁ ht fun y e => hV₁ j hj (hy y) e)
      B hB hBc P hP hPc) (hac _ P hP hPc)

end GlobalTheory.ProductAcyclic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ThetaSum

theorem exists_gen_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
    (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hσ : σ.IsGen) (m : ℕ) (a : G ⟶ G)
    (ha : a = 𝟙 G ^ m) :
    ∃ β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 _, a.left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), β.IsGen := by
  subst ha
  have hL := L.isLB
  have hcube : MulPull.HasGen L.L (thφ G (x3 G)) thε := ⟨c.t, c.isGen⟩
  have hrig : MulPull.HasGen L.L (K := PUnit) (fun _ => eSec G) (fun _ => 1) := ⟨L.rig, L.rigGen⟩
  have hsym : MulPull.HasGen L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] := ⟨σ, hσ⟩
  have h := MulPull.hasGen_pow hL hcube (𝟙 G) ((hrig.pull G.hom).of_formEq hL (fun U _ h => by
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl))
    (hsym.inv.of_formEq hL (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
      rfl)) m
  refine h.of_formEq hL fun U _ h => ?_
  rw [Fin.prod_univ_two, Fin.prod_univ_two, Nat.cast_pow]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem coef_congr {k : ℕ} (g : GtPtF D F) {w w' : Frm D F k g.b} (hw : w.IsGen)
    (h : ∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J) (s : Fam D F k) (χ : D.X) :
    coef s g w' χ = coef s g w χ := by
  refine CoefBasic.coef_eq fun z J hJ => ?_
  rw [h z J hJ]
  exact CoefBasic.isCoef_coef g hw χ s z J hJ

theorem zero_isAdd {o : GtPtF D F} (ho : o.IsZero) (g : GtPtF D F) : o.IsAdd g g := by
  obtain ⟨hb, hv⟩ := (isZero_iff o).1 ho
  refine (isAdd_iff _ _ _).2 ⟨by rw [hb, _root_.one_mul], fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [hv χ y J hJ, hb, C.face₂, _root_.mul_one, _root_.one_mul]

theorem theta_const_sum : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → ∀ w, TXFrame (m ^ 2) p w → ∀ (g' : GtPtF D.toPre F), GtPtF.IsNsmul m p.g g' → ∀ (κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ m) (m ^ 2) 1)), Normd κ → ∀ w' : Frm D.toPre F 1 g'.b, w'.IsGen → (∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J * val κ p.g.b.left z J = val w' (𝟙 _) z J) → SumF I F (coef ϑ g' w') c ∧ ∀ s, U.ExpandsF F (m ^ 2) w₀ t s → ∀ (o : GtPtF D.toPre F) (w₁ : Frm D.toPre F (m ^ 2) o.b), o.IsZero → FrmOne w₁ → (∀ χ, coef s o w₁ (m • χ + p.y) = coef ϑ g' w' χ) ∧ ∀ β, (∀ χ, β ≠ m • χ + p.y) → coef s o w₁ β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ w₀ ρ hN th ϑ hϑ m hm p x t c hx hc w hw g' hg' κ hκ w' hw' hv
  obtain ⟨α, s₁, θ, hα, hαn, htw, hθ, hact, hval⟩ := hc
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hm0)
  have hbij := (expBijF_and_expandsF_lin hL R I hI D A G hG U).1 F (m ^ 2) hm2 w₀ hN.1
  obtain ⟨σ₁, hσ₁, -⟩ := hbij.1 s₁
  obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U).1 m
  have hsm : Function.Injective fun χ : D.toPre.X => m • χ := fun a b h => by
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
    exact smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 hm0) h'
  have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
  have hpull := (GlobalTheory.T.expansion_pullback_section_endomorphism hL R I hI D A G hG U F E hinj (m ^ 2) 1 le_rfl hm2
    (exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _)
    (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α hα hαn th s₁ ϑ σ₁ hϑ hσ₁ htw
  rw [hEB] at hpull
  obtain ⟨q₁, q₂⟩ := hpull κ hκ p.g g' ((hEact F p.g g').2 hg') w w' hw.1 hw' hv
  have main : ∀ s, U.ExpandsF F (m ^ 2) w₀ t s → ∀ (o : GtPtF D.toPre F) (w₁ : Frm D.toPre F (m ^ 2) o.b), o.IsZero →
      FrmOne w₁ → (∀ χ, coef s o w₁ (m • χ + p.y) = coef ϑ g' w' χ) ∧
        ∀ β, (∀ χ, β ≠ m • χ + p.y) → coef s o w₁ β = 0 := by
    intro s hs o w₁ ho hw₁
    have hΦ := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hL R I hI D A G hG U F (m ^ 2) hm.pow p x hx θ hθ w₀ hN.1 w hw s₁ t σ₁ s hσ₁ hs hact
    obtain ⟨ω₁, hω₁, hωv, hco⟩ := CoefPhi.coef_phi hL R I hI D F (m ^ 2) hm2 p w hw.1 o p.g (zero_isAdd ho p.g) w₁ hw₁.1
    have key : ∀ a, coef s o w₁ (a + p.y) = coef σ₁ p.g w a := fun a =>
      (hco 1 (m ^ 2) le_rfl (Nat.mul_one _).symm p (one_nsmul _).symm rfl w w₁ ω₁
        ⟨hw.1, fun _ _ _ => (pow_one _).symm⟩ ⟨hw₁.1, fun _ _ _ => (pow_one _).symm⟩
        ⟨hω₁, fun _ _ _ => (pow_one _).symm⟩ σ₁ s hΦ a).trans (coef_congr p.g hw.1 (hωv ho hw₁) σ₁ a)
    refine ⟨fun χ => by rw [key, ← hEh, q₁], fun β hβ => ?_⟩
    rw [← sub_add_cancel β p.y, key]
    refine q₂ _ ?_
    rintro ⟨χ, e⟩
    exact hβ χ (by rw [← hEh, e, sub_add_cancel])
  refine ⟨?_, main⟩
  obtain ⟨s, hs, -⟩ := hbij.1 t
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨w₁, hw₁⟩ := (CoefBasic.coef_basic R D.toPre F (m ^ 2) o).2.1 ((isZero_iff o).1 ho).1
  obtain ⟨r₁, r₂⟩ := main s hs o w₁ ho hw₁
  have hsum := (EvalZero.value_at_origin hL R I hI D A G hG U F).2.2 w₀ ρ hN (m ^ 2) t s hs o w₁ ho hw₁ c hval
  have := ((AdicSum.sumF_calculus R I hI F D.toPre.X (coef s o w₁) (coef s o w₁) c c).2.2 D.toPre.X
    (fun χ => m • χ + p.y) (fun a b h => hsm (add_right_cancel h))
    (fun β hβ => r₂ β fun χ e => hβ ⟨χ, e.symm⟩)).2 hsum
  rwa [show (coef s o w₁ ∘ fun χ => m • χ + p.y) = coef ϑ g' w' from funext r₁] at this

end GlobalTheory.UT.ThetaSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.TorsionIso

theorem translT_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] {T : Over S} (x y : T ⟶ A) :
    translT A x ≫ translT A y = translT A (x * y) := by
  have h : ∀ z : T ⟶ A, translPt A z = snd T A * (fst T A ≫ z) := fun z => by
    rw [mul_comm]; rfl
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, lift_snd, h, MonObj.comp_mul, lift_fst_assoc, _root_.mul_assoc]

theorem torsion_eq : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ f, Tors U.toUnifPre F k f := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ k hk
  have hqk := GlobalTheory.T.inducesFrobeniusOnSections_translation_iff_image hL R I hI D A G hG U F k hk
  have hcomp := GlobalTheory.T.indAt_comp_equiv_unique_id hL R I hI D A G hG U F k hk
  have huniq := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hinj := GlobalTheory.TorsionMapInj.qkToAk_injective hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hex : ∀ p : QkPt D.toPre F k, ∃ x, QkToAkU U.toUnifPre F k p x := fun p => by
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_inducedTranslation_frobeniusOnSections hL R I hI D A G hG U F k hk p
    exact ⟨x, (hqk p x).1 (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩
  choose f hf using hex
  have hwd : ∀ p p', QkPt.Equiv D.toPre F p p' → f p = f p' := fun p p' h =>
    huniq p' _ _ ((hqk _ _).1 ((hcomp p p' p' _ (𝟙 _) ((hqk _ _).2 (hf p))).2.1 h)) (hf p')
  have hpow : ∀ p, f p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U.ext
    exact (hf p w hw).1
  refine ⟨f, fun p x => ⟨fun h => huniq p _ _ h (hf p), fun h => h ▸ hf p⟩, ?_,
    fun p p' => ⟨fun h => hinj p p' (f p) (hf p) (h ▸ hf p'), hwd p p'⟩, ?_,
    fun p p' z => _root_.GlobalTheory.UT.weilQkIs_iff_weilIs hL R I hI D A G hG U F k hk p p' _ _ (hf p) (hf p') z⟩
  · haveI : CharZero (FractionRing R) := inferInstance
    haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
    have hA := (hL.1.mulN _ A k hk).2.2.2.2 F (jFK (R := R) F) (Nat.cast_ne_zero.2 (by omega))
    have hQ := GlobalTheory.T.card_quotient_kTorsion_pairs hL R I hI D F k hk
    have hd := _root_.GlobalTheory.UT.dim_eq_rank_add_dim hL R I hI D A G hG U
    let φ : Quot (QkPt.Equiv D.toPre F (k := k)) → {x : TFK (R := R) F ⟶ A.A // x ^ k = 1} :=
      Quot.lift (fun p => ⟨f p, hpow p⟩) (fun p p' h => Subtype.ext (hwd p p' h))
    have hφ : Function.Injective φ := by
      rintro ⟨p⟩ ⟨p'⟩ h
      have h' : f p = f p' := congrArg Subtype.val h
      exact Quot.sound (hinj p p' (f p) (hf p) (h' ▸ hf p'))
    haveI : Finite {x : TFK (R := R) F ⟶ A.A // x ^ k = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hA]; positivity)
    have hb : Function.Bijective φ := hφ.bijective_of_nat_card_le (by rw [hA, hQ, hd])
    intro x hx
    obtain ⟨⟨p⟩, hp⟩ := hb.2 ⟨x, hx⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  · intro p p' p'' h
    have := (hcomp p p' p'' _ _ ((hqk _ _).2 (hf p))).1 ((hqk _ _).2 (hf p')) h
    rw [translT_comp] at this
    exact huniq p'' _ _ (hf p'') ((hqk _ _).1 this)

end GlobalTheory.TorsionIso
end

