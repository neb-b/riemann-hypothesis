module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0790

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CompactSpaceOfProjectiveAndOfFinite
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem UpperTheory.Cb.adjoin_degree_zero_variables_eq_top (N : ℕ) :
    Algebra.adjoin (↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))
      (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0 :=
      MvPolynomial.isHomogeneous_C _ a
    exact Subalgebra.algebraMap_mem _ (⟨_, hC⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p i hp =>
    exact Subalgebra.mul_mem _ (hp trivial) (Algebra.subset_adjoin ⟨i, rfl⟩)

private theorem UpperTheory.Cb.compactSpace_projective_space (N : ℕ) : CompactSpace (PSpace ℂ N) := by
  have hX : ∀ i : Fin (N + 1), (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 1 :=
    fun i => MvPolynomial.isHomogeneous_X ℂ i
  have hcov := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ) (fun i => ⟨1, hX i⟩)
    (UpperTheory.Cb.adjoin_degree_zero_variables_eq_top N)
  refine ⟨?_⟩
  have huniv : (Set.univ : Set (PSpace ℂ N)) =
      ⋃ i, ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
        (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) : (PSpace ℂ N).Opens) : Set (PSpace ℂ N)) := by
    have := congrArg (fun U : (PSpace ℂ N).Opens => (U : Set (PSpace ℂ N))) hcov
    simpa using this.symm
  rw [huniv]
  exact isCompact_iUnion fun i =>
    (Proj.isAffineOpen_basicOpen _ _ (hX i) Nat.one_pos).isCompact

theorem UpperTheory.Cb.compactSpace_of_projective_and_of_finite :
    (∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ), IsProjOver s → CompactSpace Z) ∧ ∀ (Y Z : Scheme.{0}) (c : Y ⟶ Z), IsFinite c → CompactSpace Z → CompactSpace Y := by
  refine ⟨?_, ?_⟩
  · rintro Z s ⟨N, i, hi, -⟩
    haveI := UpperTheory.Cb.compactSpace_projective_space N
    exact QuasiCompact.compactSpace_of_compactSpace i
  · intro Y Z c hc hZ
    exact QuasiCompact.compactSpace_of_compactSpace c
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EquivOfStalkwiseBaseChange
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

private def covE (S : Scheme.{0}) : MorphismProperty (S.Etale)ᵒᵖ := fun _ _ g => Surjective g.unop.left

private instance (S : Scheme.{0}) : (covE S).IsStableUnderComposition where
  comp_mem f g hf hg := by
    have hf' : Surjective f.unop.left := hf
    have hg' : Surjective g.unop.left := hg
    change Surjective (f ≫ g).unop.left
    have : (f ≫ g).unop.left = g.unop.left ≫ f.unop.left := rfl
    rw [this]
    infer_instance

private noncomputable def etHom {S : Scheme.{0}} (U : (S.Etale)ᵒᵖ) (V : Over S) (hV : Etale V.hom)
    (h : V ⟶ (Scheme.Etale.forget S).obj U.unop) :
    U ⟶ op (@Scheme.Etale.mk S _ V.hom hV) :=
  ((Scheme.Etale.forget S).preimage
    (X := @Scheme.Etale.mk S _ V.hom hV) (Y := U.unop) h).op

private theorem etHom_map {S : Scheme.{0}} (U : (S.Etale)ᵒᵖ) (V : Over S) (hV : Etale V.hom)
    (h : V ⟶ (Scheme.Etale.forget S).obj U.unop) :
    (Scheme.Etale.forget S).map (etHom U V hV h).unop = h :=
  (Scheme.Etale.forget S).map_preimage
    (X := @Scheme.Etale.mk S _ V.hom hV) (Y := U.unop) h

private theorem etHom_left {S : Scheme.{0}} (U : (S.Etale)ᵒᵖ) (V : Over S) (hV : Etale V.hom)
    (h : V ⟶ (Scheme.Etale.forget S).obj U.unop) : (etHom U V hV h).unop.left = h.left := by
  exact congrArg (fun k => k.left) (etHom_map U V hV h)

private theorem fst_iso (E : Spc) (S : Scheme.{0}) (p : E ⟶ sch.obj S) :
    IsIso (pullback.fst p (sch.map (Over.mk (𝟙 S)).hom)) := by
  have : IsIso (sch.map (Over.mk (𝟙 S)).hom) := by
    change IsIso (sch.map (𝟙 S))
    rw [sch.map_id]
    infer_instance
  infer_instance

theorem UpperTheory.Cb.equiv_of_stalkwise_base_change :
    ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → Eqv R α F := by
  intro R _ F S E E' α p hF hq hq' hst
  have key := GlobalTheory.T.etale_cohomology_equivalence_of_strictly_henselian_stalks R F S E E' α p hF hq hq' hst
  have basic := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  let Φ : (S.Etale)ᵒᵖ ⥤ Spcᵒᵖ := (Scheme.Etale.forget S ⋙ bc (α ≫ p)).op
  let Φ' : (S.Etale)ᵒᵖ ⥤ Spcᵒᵖ := (Scheme.Etale.forget S ⋙ bc p).op
  let β : Φ' ⟶ Φ := NatTrans.op (Functor.whiskerLeft (Scheme.Etale.forget S) (bcMap α p))
  have hall : ∀ U, Eqv R (β.app U).unop F := by
    refine GlobalTheory.T.etaleSpace_descent_local_equivalence R F (S.Etale)ᵒᵖ (covE S) Φ Φ' β ?_ ?_ ?_
    · refine GlobalTheory.T.coveringsRefine_of_cechConerve_property (S.Etale)ᵒᵖ (covE S) _ ?_
      intro U V g hg
      exact ⟨GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective R S E (α ≫ p) U V g hg, GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective R S E' p U V g hg⟩
    · intro U n x
      obtain ⟨V, h, y, hV, hs, hy⟩ := (key ((Scheme.Etale.forget S).obj U.unop) U.unop.prop n).1 x
      refine ⟨op (@Scheme.Etale.mk S _ V.hom hV), etHom U V hV h, ?_, y, ?_⟩
      · change Surjective (etHom U V hV h).unop.left
        rw [etHom_left]
        exact hs
      · have hm : (Φ.map (etHom U V hV h)).unop = (bc (α ≫ p)).map h := by
          change (bc (α ≫ p)).map ((Scheme.Etale.forget S).map (etHom U V hV h).unop) = _
          rw [etHom_map]
          rfl
        rw [hm]
        exact hy
    · intro U n y hy
      obtain ⟨V, h, hV, hs, hz⟩ := (key ((Scheme.Etale.forget S).obj U.unop) U.unop.prop n).2 y hy
      refine ⟨op (@Scheme.Etale.mk S _ V.hom hV), etHom U V hV h, ?_, ?_⟩
      · change Surjective (etHom U V hV h).unop.left
        rw [etHom_left]
        exact hs
      · have hm : (Φ'.map (etHom U V hV h)).unop = (bc p).map h := by
          change (bc p).map ((Scheme.Etale.forget S).map (etHom U V hV h).unop) = _
          rw [etHom_map]
          rfl
        rw [hm]
        exact hz
  have hid : Eqv R ((bcMap α p).app (Over.mk (𝟙 S))) F :=
    hall (op (@Scheme.Etale.mk S S (𝟙 S) inferInstance))
  have i1 := fst_iso E S (α ≫ p)
  have i2 := fst_iso E' S p
  have hsq : (bcMap α p).app (Over.mk (𝟙 S)) ≫ pullback.fst p (sch.map (Over.mk (𝟙 S)).hom) =
      pullback.fst (α ≫ p) (sch.map (Over.mk (𝟙 S)).hom) ≫ α := by
    exact pullback.lift_fst _ _ _
  have e1 : Eqv R (pullback.fst (α ≫ p) (sch.map (Over.mk (𝟙 S)).hom)) F := basic.1 _ _ _ i1
  have e2 : Eqv R (pullback.fst p (sch.map (Over.mk (𝟙 S)).hom)) F := basic.1 _ _ _ i2
  have e3 := (basic.2.1 _ _ _ _ _).1 hid e2
  rw [hsq] at e3
  exact (basic.2.1 _ _ _ _ _).2.1 e1 e3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsFiniteEtaleRestrictClopen
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.exists_finite_etale_restrict_clopen :
    ∀ (Y Z : Scheme.{0}) (c : Y ⟶ Z) (V : Z.Opens) (W : Y.Opens), IsClosed (W : Set Y) → W ≤ c ⁻¹ᵁ V → IsFinite c → Etale c → ∃ c' : W.toScheme ⟶ V.toScheme, c' ≫ V.ι = W.ι ≫ c ∧ IsFinite c' ∧ Etale c' := by
  intro Y Z c V W hWc hWV hfin het
  haveI := het
  haveI := hfin
  refine ⟨c.resLE V W hWV, c.resLE_comp_ι hWV, ?_, inferInstance⟩
  haveI hWι : IsClosedImmersion W.ι := .of_isPreimmersion _ (by simpa using hWc)
  haveI h1 : IsClosedImmersion (Y.homOfLE hWV ≫ (c ⁻¹ᵁ V).ι) := by
    rw [Scheme.homOfLE_ι]
    exact hWι
  haveI h2 : IsClosedImmersion (Y.homOfLE hWV) := .of_comp _ ((c ⁻¹ᵁ V).ι)
  haveI h3 : IsFinite (c ∣_ V) := by infer_instance
  show IsFinite (Y.homOfLE hWV ≫ c ∣_ V)
  infer_instance
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUniqueComplexPointLiftClopenCover
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.existsUnique_complexPoint_lift_clopen_cover :
    ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (M : Type) [Fintype M] (W : M → Y.Opens), (∀ i j, i ≠ j → W i ⊓ W j = ⊥) → iSup W = ⊤ → ∀ y : CxPts s' (RingHom.id ℂ), ∃! m : M, ∃! y' : CxPts ((W m).ι ≫ s') (RingHom.id ℂ), y'.1 ≫ (W m).ι = y.1 := by
  intro Y s' M _ W hd hc y
  let x0 : (Sp ℂ : Scheme.{0}) := IsLocalRing.closedPoint ℂ
  have hone : ∀ a : (Sp ℂ : Scheme.{0}), a = x0 := fun a => Subsingleton.elim a x0
  obtain ⟨m, hm⟩ : ∃ m, y.1 x0 ∈ W m := by
    have h : y.1 x0 ∈ iSup W := by
      rw [hc]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h
  have hr : Set.range y.1 ⊆ Set.range (W m).ι := by
    rintro _ ⟨a, rfl⟩
    rw [hone a, Scheme.Opens.range_ι]
    exact hm
  refine ⟨m, ?_, ?_⟩
  · refine ⟨⟨IsOpenImmersion.lift (W m).ι y.1 hr, ?_⟩, ?_, ?_⟩
    · rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact y.2
    · exact IsOpenImmersion.lift_fac _ _ _
    · intro z hz
      apply Subtype.ext
      rw [← cancel_mono (W m).ι, hz]
      exact (IsOpenImmersion.lift_fac _ _ _).symm
  · rintro m' ⟨z, hz, -⟩
    by_contra hne
    have h1 : y.1 x0 ∈ W m' := by
      have hz' : z.1 ≫ (W m').ι = y.1 := hz
      rw [← hz', Scheme.Hom.comp_apply]
      exact (z.1 x0).2
    have h2 : y.1 x0 ∈ W m' ⊓ W m := ⟨h1, hm⟩
    rw [hd m' m hne] at h2
    exact h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GermComapEqAlgebraMapGermOfFiniteEtale
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GlobalTheory.HodgeCoh GlobalTheory.CechDR ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace UpperTheory.Cb

section Alg

variable {B B' K L : Type} [CommRing B] [CommRing B'] [IsDomain B] [IsDomain B'] [Field K] [Field L]
  [Algebra B B'] [Algebra B K] [Algebra K L] [Algebra B' L] [Algebra B L]
  [IsScalarTower B K L] [IsScalarTower B B' L] [IsFractionRing B K] [IsFractionRing B' L]

include K L in
private theorem injective_algebraMap : Function.Injective (algebraMap B B') := by
  have h : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective B K)
  rw [IsScalarTower.algebraMap_eq B B' L] at h
  exact Function.Injective.of_comp (f := algebraMap B' L) h

include K L in
private theorem isLocalization_of_integral [Algebra.IsIntegral B B'] :
    IsLocalization (Algebra.algebraMapSubmonoid B' (nonZeroDivisors B)) L := by
  have hinj : Function.Injective (algebraMap B B') := injective_algebraMap (K := K) (L := L)
  have hL : Function.Injective (algebraMap B' L) := IsFractionRing.injective B' L
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨_, r, hr, rfl⟩
    refine IsUnit.mk0 _ ?_
    exact (map_ne_zero_iff _ hL).2 ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hr))
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B') z
    obtain ⟨r, hr, t, ht⟩ := (Algebra.IsIntegral.isIntegral (R := B) b).isAlgebraic.exists_nonzero_dvd hb
    refine ⟨⟨a * t, ⟨algebraMap B B' r, r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩⟩, ?_⟩
    have hb0 : algebraMap B' L b ≠ 0 := (map_ne_zero_iff _ hL).2 (nonZeroDivisors.ne_zero hb)
    have e : algebraMap B' L (algebraMap B B' r) = algebraMap B' L b * algebraMap B' L t := by
      rw [ht, map_mul]
    change algebraMap B' L a / algebraMap B' L b * algebraMap B' L (algebraMap B B' r) =
      algebraMap B' L (a * t)
    rw [e, map_mul]
    field_simp
  · intro x y h
    exact ⟨1, by rw [hL h]⟩

include K L in
private theorem isPushout_of_integral [Algebra.IsIntegral B B'] : Algebra.IsPushout B K B' L := by
  have h1 := isLocalization_of_integral (B := B) (B' := B') (K := K) (L := L)
  have h2 := (isLocalizedModule_iff_isLocalization (S := nonZeroDivisors B) (A := B') (Aₛ := L)).2 h1
  exact ⟨(isLocalizedModule_iff_isBaseChange (nonZeroDivisors B) K _).1 h2⟩

private theorem algebraMap_etTrace [Module.Finite B B'] [Algebra.Etale B B'] (b : B') :
    algebraMap B K (etTrace B B' b) = Algebra.trace K L (algebraMap B' L b) := by
  haveI := projective_of_etale B B'
  haveI hp := isPushout_of_integral (B := B) (B' := B') (K := K) (L := L)
  haveI : Module.Finite K L := Module.Finite.equiv hp.out.equiv
  rw [← algTrace_eq_trace, algTrace_of_isPushout (B := B) (B' := B') b]
  rfl

end Alg

theorem germ_comap_eq_algebraMap_germ_of_finite_etale : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ)
    (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] [Algebra Z.functionField Y.functionField],
    (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
      (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) =
        algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) →
    ∀ (V : Z.Opens) (hV : IsAffineOpen V) (hg : genericPoint Z ∈ V)
      (hg' : genericPoint Y ∈ c ⁻¹ᵁ V) (b' : Γ(Y, c ⁻¹ᵁ V)),
      (Z.presheaf.germ V (genericPoint Z) hg).hom (secTrace (f := c) p p' hV b') =
        Algebra.trace Z.functionField Y.functionField
          ((Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hg').hom b') := by
  intro Z Y _ _ p p' c _ _ _ _ hg V hVa hV hV' b'
  haveI : Nonempty V := ⟨⟨_, hV⟩⟩
  haveI : Nonempty (c ⁻¹ᵁ V : Y.Opens) := ⟨⟨_, hV'⟩⟩
  letI := secAlg p p' c V
  haveI := sec_finite (s := p) (s' := p') (f := c) hVa
  haveI := sec_etale (s := p) (s' := p') (f := c) hVa
  letI : Algebra (Sec p V) Z.functionField := (Z.germToFunctionField V).hom.toAlgebra
  letI : Algebra (Sec p' (c ⁻¹ᵁ V)) Y.functionField := (Y.germToFunctionField (c ⁻¹ᵁ V)).hom.toAlgebra
  letI : Algebra (Sec p V) Y.functionField :=
    ((algebraMap Z.functionField Y.functionField).comp (algebraMap (Sec p V) Z.functionField)).toAlgebra
  haveI : IsScalarTower (Sec p V) Z.functionField Y.functionField := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (Sec p V) (Sec p' (c ⁻¹ᵁ V)) Y.functionField :=
    .of_algebraMap_eq fun g ↦ (hg V hV hV' g).symm
  haveI : IsDomain (Sec p V) := inferInstanceAs (IsDomain Γ(Z, V))
  haveI : IsDomain (Sec p' (c ⁻¹ᵁ V)) := inferInstanceAs (IsDomain Γ(Y, c ⁻¹ᵁ V))
  haveI : IsFractionRing (Sec p V) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z V hVa
  haveI : IsFractionRing (Sec p' (c ⁻¹ᵁ V)) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y (c ⁻¹ᵁ V) (hVa.preimage c)
  exact algebraMap_etTrace (B := Sec p V) (B' := Sec p' (c ⁻¹ᵁ V)) (K := Z.functionField)
    (L := Y.functionField) b'

end UpperTheory.Cb
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsProjOverRestrictClopen
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.isProjOver_restrict_clopen :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (V : Z.Opens), IsClosed (V : Set Z) → IsProjOver s → IsProjOver (V.ι ≫ s) := by
  rintro Z s V hV ⟨N, i, hi, rfl⟩
  have hc : IsClosedImmersion V.ι := by
    apply IsClosedImmersion.of_isPreimmersion
    simpa using hV
  exact ⟨N, V.ι ≫ i, inferInstance, by simp⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothOfRelativeDimensionCompEtale
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.smoothOfRelativeDimension_comp_etale :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → ∀ (d : ℕ) [SmoothOfRelativeDimension d s], Etale c → SmoothOfRelativeDimension d s' := by
  intro Z Y s s' c h d _ hc
  subst h
  have h0 : SmoothOfRelativeDimension 0 c := (Etale.iff_smoothOfRelativeDimension_zero c).1 hc
  have h1 : SmoothOfRelativeDimension (0 + d) (c ≫ s) := smoothOfRelativeDimension_comp 0 d c s
  rwa [Nat.zero_add] at h1
end

