module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle0002
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0022
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0013
public import Development.EtaleCohomology.EtaleSheaves.Bundle0041
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0005
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafCore
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsCoveringPairOfIsOpenImmersionOfJointlySurjecti
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace UpperTheory.CoverSieveFree

private def coverSieve {Y A B T : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y) (x : T ⟶ Y) : Sieve T where
  arrows V g := (∃ u : V ⟶ A, u ≫ a = g ≫ x) ∨ ∃ v : V ⟶ B, v ≫ b = g ≫ x
  downward_closed := by
    rintro V W g (⟨u, hu⟩ | ⟨v, hv⟩) h
    · exact Or.inl ⟨h ≫ u, by simp [hu]⟩
    · exact Or.inr ⟨h ≫ v, by simp [hv]⟩

private theorem coverSieve_mem {Y A B T : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y) [IsOpenImmersion a]
    [IsOpenImmersion b] (hc : ∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b) (x : T ⟶ Y) :
    coverSieve a b x ∈ Scheme.etaleTopology.{0} T := by
  let Xs : Bool → Scheme.{0} := fun i => Bool.casesOn i B A
  let fs : ∀ i, Xs i ⟶ Y := fun i => Bool.casesOn (motive := fun i => Xs i ⟶ Y) i b a
  have hmem : Presieve.ofArrows Xs fs ∈ Scheme.precoverage @Etale Y := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun y => ?_, fun i => ?_⟩
    · rcases hc y with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    · cases i <;> dsimp [fs] <;> infer_instance
  have hS := Precoverage.generate_mem_toGrothendieck hmem
  refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.pullback_stable x hS)
  rintro V g ⟨W, h, k, hk, e⟩
  rcases hk with ⟨i⟩
  cases i
  · exact Or.inr ⟨h, e⟩
  · exact Or.inl ⟨h, e⟩

private theorem free_hom_ext (R : Type) [CommRing R] {Y A B : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b] (hc : ∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b)
    {G : Shv R} (φ ψ : (free R).obj (yoneda.obj Y) ⟶ G)
    (ha : (free R).map (yoneda.map a) ≫ φ = (free R).map (yoneda.map a) ≫ ψ)
    (hb : (free R).map (yoneda.map b) ≫ φ = (free R).map (yoneda.map b) ≫ ψ) : φ = ψ := by
  apply free_ext
  intro U x
  refine G.isSeparated _ (coverSieve a b x) (coverSieve_mem a b hc x) _ _ ?_
  intro V g hg
  change Sec.res g (Sec.map φ _) = Sec.res g (Sec.map ψ _)
  rw [map_res, map_res, freeGen_res]
  rcases hg with ⟨u, hu⟩ | ⟨v, hv⟩
  · have e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x =
        (ConcreteCategory.hom ((yoneda.map a).app (op V))) u := hu.symm
    rw [e, ← freeGen_map]
    change Sec.map ((free R).map (yoneda.map a) ≫ φ) _ = Sec.map ((free R).map (yoneda.map a) ≫ ψ) _
    rw [ha]
  · have e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x =
        (ConcreteCategory.hom ((yoneda.map b).app (op V))) v := hv.symm
    rw [e, ← freeGen_map]
    change Sec.map ((free R).map (yoneda.map b) ≫ φ) _ = Sec.map ((free R).map (yoneda.map b) ≫ ψ) _
    rw [hb]

end UpperTheory.CoverSieveFree

open UpperTheory.CoverSieveFree in
theorem UpperTheory.isCovering_pair_of_isOpenImmersion_of_jointly_surjective :
    ∀ (R : Type) [CommRing R] {Y A B : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y), IsOpenImmersion a → IsOpenImmersion b →
       (∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b) → Cover2 R (sch.map a) (sch.map b) := by
  intro R _ Y A B a b ha hb hc
  have hy : ∀ {Z : Scheme.{0}} (f : Z ⟶ Y) [Mono f], Mono (sch.map f) := by
    intro Z f _
    have h1 : ∀ X, Mono ((yoneda.map f).app X) := fun X =>
      (mono_iff_injective _).2 (fun g h e => (cancel_mono f).1 (by simpa using e))
    have h2 : Mono (yoneda.map f) := NatTrans.mono_of_mono_app _
    have h3 : ∀ n, Mono ((sch.map f).app n) := fun n => h2
    exact NatTrans.mono_of_mono_app _
  refine ⟨hy a, hy b, fun n => ⟨fun {G} φ ψ h => ?_⟩⟩
  apply free_hom_ext R a b hc φ ψ
  · have e := congrArg (fun k => biprod.inl ≫ k) h
    simp only [biprod.inl_desc_assoc] at e
    exact e
  · have e := congrArg (fun k => biprod.inr ≫ k) h
    simp only [biprod.inr_desc_assoc] at e
    exact e
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LeafCurveOfLeafH0
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.Cb.CurveInd

private theorem sp_facts (hH0 : H0TwistOverClosedField) (hH : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (hq : IsUnit (q : Ω)) (i : ℤ)
    (hB : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B],
      Finite (Ht q (sp B) 1 i))
    (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B] :
    (∀ m : ℤ, Finite (Ht q (sp B) m i)) ∧ ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sp B) m i) := by
  have hH' := hH
  obtain ⟨a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b7, c1, c2, c3, c4, c5, d1, d2, d3, e1, e2, e3⟩ := hH'
  have hsub : ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sp B) m i) := fun m hm => c2 q Ω B hq m i hm
  refine ⟨fun m => ?_, hsub⟩
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · haveI : Subsingleton (Ht q (sp B) m i) := (a9 (ZMod q) (tw q i)).1 (sp B) m hm
    infer_instance
  · obtain ⟨hfin, hbij⟩ := hH0 hH q Ω hq i
    haveI := hfin
    exact Finite.of_surjective _ (hbij (Spec.map (CommRingCat.ofHom (algebraMap Ω B)))).2
  · rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
    · exact hB B
    · haveI := hsub m hm2
      infer_instance

private theorem aff_facts (hH0 : H0TwistOverClosedField) (hH : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (hq : IsUnit (q : Ω)) (i : ℤ)
    (hB : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B],
      Finite (Ht q (sp B) 1 i))
    {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c) (U : C.Opens) (hU : IsAffineOpen U)
    {Y : Scheme.{0}} (j : Y ⟶ C) [IsOpenImmersion j] (hj : j.opensRange ≤ U) :
    (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sch.obj Y) m i) := by
  by_cases hne : (j.opensRange : Set C).Nonempty
  · have hUne : (U : Set C).Nonempty := hne.mono hj
    have hcur := UpperTheory.isDedekindDomain_affine_sections_of_isCurve Ω c hc
    haveI : IsDedekindDomain (Γ(C, U) : Type) := (hcur.1 U hU hUne).1
    have hWa : IsAffineOpen j.opensRange := by
      have h1 : IsAffineOpen (hU.fromSpec ⁻¹ᵁ j.opensRange) := UpperTheory.dedekind_spec_open_isAffine (Γ(C, U) : Type) _
      have h2 := h1.image_of_isOpenImmersion hU.fromSpec
      rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, IsAffineOpen.opensRange_fromSpec,
        inf_eq_right.mpr hj] at h2
    haveI : IsDedekindDomain (Γ(C, j.opensRange) : Type) := (hcur.1 _ hWa hne).1
    have e : j.opensRange ≤ c ⁻¹ᵁ ⊤ := by simp
    letI : Algebra Ω (Γ(C, j.opensRange) : Type) :=
      ((c.appLE ⊤ j.opensRange e).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).toAlgebra
    haveI : LocallyOfFiniteType c := by
      haveI : IsProper c := hc.2.1
      infer_instance
    haveI : Algebra.FiniteType Ω (Γ(C, j.opensRange) : Type) := by
      have hft := HasRingHomProperty.appLE @LocallyOfFiniteType c inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨j.opensRange, hWa⟩ e
      exact RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _
        (fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom x, by simp⟩))
    obtain ⟨h1, h2⟩ := sp_facts hH0 hH q Ω hq i hB (Γ(C, j.opensRange) : Type)
    have iso : Y ≅ Spec (CommRingCat.of (Γ(C, j.opensRange) : Type)) := j.isoOpensRange ≪≫ hWa.isoSpec
    refine ⟨fun m => ?_, fun m hm => ?_⟩
    · haveI := h1 m
      exact Finite.of_equiv _ (CurveCut.isoH (ZMod q) (tw q i) iso m)
    · haveI := h2 m hm
      exact (CurveCut.isoH (ZMod q) (tw q i) iso m).symm.subsingleton
  · have hr : Set.range j.base = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have iso : Y ≅ ((⊥ : C.Opens) : Scheme.{0}) := IsOpenImmersion.isoOfRangeEq j (⊥ : C.Opens).ι (by
      rw [Scheme.Opens.range_ι]
      simpa using hr)
    have hs : ∀ m : ℤ, Subsingleton (Ht q (sch.obj Y) m i) := fun m =>
      haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := C) (tw q i) m
      (CurveCut.isoH (ZMod q) (tw q i) iso m).symm.subsingleton
    refine ⟨fun m => ?_, fun m _ => hs m⟩
    haveI := hs m
    infer_instance

end UpperTheory.Cb.CurveInd

open UpperTheory.Cb.CurveInd in
theorem UpperTheory.leafCurve_of_leafH0 :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.E4.LeafCurve := by
  intro hH0 hH q _ Ω _ _ hq i hB C c hc
  have hMV := UpperTheory.Cb.curve_mayer_vietoris_of_degree_zero hH0
  haveI : IsProper c := hc.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  have key : ∀ (Y : Scheme.{0}) (j : Y ⟶ C) [IsOpenImmersion j], j.opensRange ≤ ⊤ →
      (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj Y) m i) := by
    refine compact_open_induction_on (P := fun W : C.Opens => ∀ (Y : Scheme.{0}) (j : Y ⟶ C) [IsOpenImmersion j],
      j.opensRange ≤ W →
      (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj Y) m i)) ⊤ ?_ ?_ ?_
    · simpa using (isCompact_univ : IsCompact (Set.univ : Set C))
    · intro Y j _ hj
      obtain ⟨h1, h2⟩ := aff_facts hH0 hH q Ω hq i hB c hc ⊥ (isAffineOpen_bot C) j hj
      exact ⟨h1, fun m hm => h2 m (by omega)⟩
    · intro S _ U ih Y j _ hj
      have hAB : j ⁻¹ᵁ S ⊔ j ⁻¹ᵁ (U : C.Opens) = ⊤ := by
        refine top_le_iff.mp fun y _ => ?_
        have hy : j.base y ∈ S ⊔ (U : C.Opens) := hj ⟨y, rfl⟩
        rcases (TopologicalSpace.Opens.mem_sup).mp hy with h | h
        · exact (TopologicalSpace.Opens.mem_sup).mpr (Or.inl h)
        · exact (TopologicalSpace.Opens.mem_sup).mpr (Or.inr h)
      obtain ⟨fA, sA⟩ := ih (j ⁻¹ᵁ S) ((j ⁻¹ᵁ S).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2)
      obtain ⟨fB, sB⟩ := aff_facts hH0 hH q Ω hq i hB c hc U U.2 ((j ⁻¹ᵁ (U : C.Opens)).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2)
      obtain ⟨fI, sI⟩ := aff_facts hH0 hH q Ω hq i hB c hc U U.2
        ((j ⁻¹ᵁ S ⊓ j ⁻¹ᵁ (U : C.Opens)).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2.2)
      refine ⟨fun m => ?_, fun m hm => ?_⟩
      · obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
        exact CurveCut.finite_of_mv hMV hH (ZMod q) (tw q i) Y _ _ hAB n (fI n) (fA (n + 1)) (fB (n + 1))
      · obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
        exact CurveCut.subsingleton_of_mv hMV hH (ZMod q) (tw q i) Y _ _ hAB n (sI n (by omega))
          (sA (n + 1) hm) (sB (n + 1) (by omega))
  obtain ⟨h1, h2⟩ := key C (𝟙 C) le_top
  exact ⟨h1 1, h1 2, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveLineStdOpensBasicOpenGenerators
section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsMultivariableHensel

namespace UpperTheory.ProjectiveLineClosure

open GroundTheory.Arith.SchemeCoh ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem closure_chart (i j : Fin 2) (hij : i ≠ j) :
    Subring.closure {chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j)} = ⊤ := by
  have hiso : IsIso (Proj.awayToSection (grading ℤ 1) (MvPolynomial.X i)) := by
    rw [← Proj.basicOpenIsoAway_hom (grading ℤ 1) (MvPolynomial.X i) (X_mem i) one_pos]
    infer_instance
  have hsurj := (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (grading ℤ 1) (MvPolynomial.X i))).2
  have hpoly : ∀ a : MvPolynomial (Fin (1 + 1)) ℤ,
      chartHom (A := ℤ) (n := 1) i a ∈ Subring.closure {chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j)} := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      rw [show (MvPolynomial.C c : MvPolynomial (Fin (1 + 1)) ℤ) = (c : MvPolynomial (Fin (1 + 1)) ℤ) from
        eq_intCast MvPolynomial.C c, map_intCast]
      exact intCast_mem _ c
    | add p q hp hq =>
      rw [map_add (f := _)]
      exact add_mem hp hq
    | mul_X p n hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      by_cases hn : n = i
      · subst hn
        rw [chartHom_X_self]
        exact one_mem _
      · have hnj : n = j := by
          fin_cases n <;> fin_cases i <;> fin_cases j <;> simp_all
        subst hnj
        exact Subring.subset_closure rfl
  rw [eq_top_iff]
  intro s _
  obtain ⟨y, rfl⟩ := hsurj s
  obtain ⟨k, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem i) y
  have ha' : a ∈ grading ℤ 1 k := by simpa using ha
  convert hpoly a using 1
  exact (chartHom_of_mem i ha').symm

private theorem chartHom_eq_ratio (i j : Fin 2) :
    chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j) =
      ProjTwist.ratio (grading ℤ 1) (X_mem i) (X_mem j) := by
  rw [chartHom_of_mem i (X_mem j)]
  unfold ProjTwist.ratio
  congr 1
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk]

private theorem mul_res :
    resR (inf_le_left : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 0)
        (chartHom (A := ℤ) (n := 1) 0 (MvPolynomial.X 1)) *
      resR (inf_le_right : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 1)
        (chartHom (A := ℤ) (n := 1) 1 (MvPolynomial.X 0)) = 1 := by
  letI : CommRing (ringOn (projectiveSpace ℤ 1) (stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1)) :=
    inferInstanceAs (CommRing Γ(projectiveSpace ℤ 1, stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1))
  have h := ProjTwist.ratio_mul_ratio' (𝒜 := grading ℤ 1) (X_mem (A := ℤ) (n := 1) 0)
    (X_mem (A := ℤ) (n := 1) 1) (X_mem (A := ℤ) (n := 1) 0)
  rw [ProjTwist.ratio_self, map_one] at h
  rw [← chartHom_eq_ratio, ← chartHom_eq_ratio] at h
  change resR (inf_le_right : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 1)
      (chartHom (A := ℤ) (n := 1) 1 (MvPolynomial.X 0)) *
    resR (inf_le_left : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 0)
      (chartHom (A := ℤ) (n := 1) 0 (MvPolynomial.X 1)) = 1 at h
  exact (mul_comm _ _).trans h

end UpperTheory.ProjectiveLineClosure

open GroundTheory.Arith.SchemeCoh ProjSpace UpperTheory.ProjectiveLineClosure in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem UpperTheory.projectiveLine_std_opens_basicOpen_generators :
    ∃ (τ : Γ(P1, stdOpen 0)) (σ : Γ(P1, stdOpen 1)),
        IsAffineOpen (stdOpen 0) ∧ IsAffineOpen (stdOpen 1) ∧
        Subring.closure {τ} = ⊤ ∧ Subring.closure {σ} = ⊤ ∧
        P1.basicOpen τ = stdOpen 0 ⊓ stdOpen 1 ∧ P1.basicOpen σ = stdOpen 0 ⊓ stdOpen 1 ∧
        P1.presheaf.map (homOfLE (inf_le_left : stdOpen 0 ⊓ stdOpen 1 ≤ stdOpen 0)).op τ *
          P1.presheaf.map (homOfLE (inf_le_right : stdOpen 0 ⊓ stdOpen 1 ≤ stdOpen 1)).op σ = 1 := by
  refine ⟨chartHom (A := ℤ) (n := 1) 0 (MvPolynomial.X 1),
    chartHom (A := ℤ) (n := 1) 1 (MvPolynomial.X 0),
    isAffineOpen_stdOpen (A := ℤ) (n := 1) 0, isAffineOpen_stdOpen (A := ℤ) (n := 1) 1,
    closure_chart 0 1 (by decide), closure_chart 1 0 (by decide),
    basicOpen_chartHom_X (A := ℤ) (n := 1) 0 1, ?_, ?_⟩
  · refine (basicOpen_chartHom_X (A := ℤ) (n := 1) 1 0).trans ?_
    exact inf_comm _ _
  · exact mul_res
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCohomologyIsTotalModelOfImage
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.VanishingEvaluation

variable {R : Type} [CommRing R]

private noncomputable abbrev pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) :
    Cochain ((chains R).obj E) K n :=
  (Cochain.ofHom ((chains R).map f)).comp α (zero_add n)

private theorem pb_sub {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E') K n) :
    pb f (α - β) = pb f α - pb f β :=
  Cochain.comp_sub _ _ _ _

private theorem ev_pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (pb f α) p s h U x = ev (R := R) α p s h U (x.map f) :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.2.1 f α p s h U x

private theorem ev_zero {E : Spc} {K : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (R := R) (0 : Cochain ((chains R).obj E) K n) p s h U x = 0 :=
  ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 0 0 p s h U x).2.2.1

private theorem pb_eq_zero {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev (R := R) α p s h U (x.map f) = 0) :
    pb f α = 0 :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h' U x => by rw [ev_pb, h, ev_zero]

private theorem δ_pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) (n' : ℤ) :
    δ n n' (pb f α) = pb f (δ n n' α) := by
  by_cases h : n + 1 = n'
  · rw [δ_comp _ _ (zero_add n) 1 n' n' h (zero_add 1) h]; simp
  · simp [δ_shape _ _ h]

private theorem δ_van {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) (n' : ℤ)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev (R := R) α p s h U (x.map f) = 0)
    (p : ℕ) (s : ℤ) (h' : -(p : ℤ) + n' = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (δ n n' α) p s h' U (x.map f) = 0 := by
  rw [← ev_pb, ← δ_pb, pb_eq_zero f α h, δ_zero, ev_zero]

private theorem dbl_ext (P : Arrow Spc) {K : Cx R} {N : ℤ} (α β : Cochain ((chains R).obj (dbl P)) K N)
    (hl : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := R) α p s h U (z.map (dbl.inl P)) = ev (R := R) β p s h U (z.map (dbl.inl P)))
    (hr : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := R) α p s h U (z.map (dbl.inr P)) = ev (R := R) β p s h U (z.map (dbl.inr P))) : α = β :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α β fun p s h U w => by
    rcases (UpperTheory.doubleMappingCylinder_cochain_extension R P).1 p U w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact hl p s h U z
    · exact hr p s h U z

private theorem map_map {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    (x.map f).map g = x.map (f ≫ g) := rfl

private theorem map_id {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : x.map (𝟙 E) = x := rfl

private theorem van_img (P : Arrow Spc) {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj (dbl P)) K n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := R) α p s h U (z.map (dbl.inr P)) = 0)
    (p : ℕ) (s : ℤ) (h' : -(p : ℤ) + n = s) (U : Scheme.{0}) (z : Sx P.right p U)
    (hz : (Sub.img P.hom).mem p U z) : ev (R := R) α p s h' U (z.map (dbl.inl P)) = 0 := by
  obtain ⟨y, rfl⟩ := hz
  have e : (y.map P.hom).map (dbl.inl P) = (y.map P.hom).map (dbl.inr P) := by
    rw [map_map, map_map]
    exact congrArg (fun f => Sx.map f y) (pushout.condition : P.hom ≫ pushout.inl P.hom P.hom = P.hom ≫ pushout.inr P.hom P.hom)
  rw [e]
  exact h p s h' U _

private theorem pb_fold (P : Arrow Spc) {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj P.right) K n) :
    pb (dbl.inr P) (pb (dbl.fold P) α) = α :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h U x => by
    rw [ev_pb, ev_pb, map_map, dbl.inr_fold, map_id]

private theorem comp_eq {E E' : Spc} {j : E ⟶ E'} {Z : Sub E} {K : Cx R} {m N : ℤ}
    {γ γ' : Cochain ((chains R).obj E') K N} {x : (famDC Z K m).Tot} (h : Comp j γ x) (h' : Comp j γ' x)
    (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx E p U) :
    ev (R := R) γ p s hs U (z.map j) = ev (R := R) γ' p s hs U (z.map j) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + m := ⟨s - m, by omega⟩
  exact (h p t hs U z).symm.trans (h' p t hs U z)

private theorem comp_zero {E E' : Spc} (j : E ⟶ E') (Z : Sub E) (K : Cx R) (m N : ℤ) :
    Comp j (0 : Cochain ((chains R).obj E') K N) (0 : (famDC Z K m).Tot) := by
  intro p s h U z
  exact (ev_zero p _ h U (z.map j)).symm

private theorem pull_inr (q : ℕ) (P : Arrow Spc) (i N : ℤ) (g : Cocycle ((chains (ZMod q)).obj (dbl P)) (res _ (tw q i)) N)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := ZMod q) g.1 p s h U (z.map (dbl.inr P)) = 0) :
    pull _ (dbl.inr P) (tw q i) N (CohomologyClass.mk g) = 0 := by
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g (zero_add N)) = 0
  have e : zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g (zero_add N) = 0 :=
    Cocycle.ext (pb_eq_zero _ _ h)
  rw [e, CohomologyClass.mk_zero]

end UpperTheory.VanishingEvaluation

open UpperTheory.VanishingEvaluation in
theorem UpperTheory.relativeCohomology_isTotalModel_of_image :
    ∀ (q : ℕ) (P : Arrow Spc) (i m n N : ℤ), n + m = N → TModel (famDC (Sub.img P.hom) (res _ (tw q i)) m) n (fun x (c : Hs q P N i) => SRel (N := N) x c.1) := by
  intro q P i m n N hN
  have C := fun n N h => UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain (ZMod q) (dbl.inl P) (Sub.img P.hom) (res _ (tw q i)) m n N h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hD
    obtain ⟨γ, hγ, hv⟩ := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) P).2 (res _ (tw q i)) m N x
    have h0 : δ N (N + 1) γ = 0 := by
      have hc := (C n N hN).2.2.1 γ x hγ
      rw [hD] at hc
      refine dbl_ext P _ _ (comp_eq hc (comp_zero _ _ _ _ _)) fun p s h U z => ?_
      rw [δ_van _ _ _ hv, ev_zero]
    refine ⟨⟨CohomologyClass.mk (Cocycle.mk γ (N + 1) rfl h0), ?_⟩, Cocycle.mk γ (N + 1) rfl h0, rfl, hγ, hv⟩
    exact pull_inr q P i N _ hv
  · rintro ⟨c, hc⟩
    obtain ⟨g₀, rfl⟩ := CohomologyClass.mk_surjective c
    have hc' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g₀ (zero_add N)) = 0 := hc
    rw [CohomologyClass.mk_eq_zero_iff] at hc'
    obtain ⟨N', hN', β, hβ⟩ := hc'
    have hβ' : δ N' N β = pb (dbl.inr P) g₀.1 := hβ
    let e : Cocycle ((chains (ZMod q)).obj (dbl P)) (res _ (tw q i)) N :=
      Cocycle.mk (δ N' N (pb (dbl.fold P) β)) (N + 1) rfl (δ_δ _ _ _ _)
    have he : CohomologyClass.mk e = 0 := by
      rw [CohomologyClass.mk_eq_zero_iff]
      exact ⟨N', hN', _, rfl⟩
    have hm : CohomologyClass.mk (g₀ - e) = CohomologyClass.mk g₀ := by
      rw [CohomologyClass.mk_sub, he, sub_zero]
    have hp : pb (dbl.inr P) (g₀ - e).1 = 0 := by
      change pb (dbl.inr P) (g₀.1 - δ N' N (pb (dbl.fold P) β)) = 0
      rw [pb_sub, ← δ_pb, pb_fold, hβ', sub_self]
    have hv : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
        ev (R := ZMod q) (g₀ - e).1 p s h U (z.map (dbl.inr P)) = 0 := fun p s h U z => by
      rw [← ev_pb, hp, ev_zero]
    obtain ⟨x, hd, hx⟩ := (C n N hN).1 (g₀ - e).1 (van_img P _ hv)
    refine ⟨x, hd, ?_, g₀ - e, hm, hx, hv⟩
    refine (C (n + 1) (N + 1) (by omega)).2.1 (δ N (N + 1) (g₀ - e).1) _ 0 ((C n N hN).2.2.2.2 x hd)
      (fun _ _ _ => rfl) ((C n N hN).2.2.1 _ x hx) ?_
    rw [(g₀ - e).δ_eq_zero]
    exact comp_zero _ _ _ _ _
  · rintro x c x' c' ⟨g, hg, hc, hv⟩ ⟨g', hg', hc', hv'⟩
    refine ⟨g - g', ?_, (C n N hN).2.2.2.1 _ _ _ _ hc hc', fun p s h U z => ?_⟩
    · rw [CohomologyClass.mk_sub, hg, hg']; rfl
    · have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 g.1 g'.1 p s h U (z.map (dbl.inr P))).2.1
      rw [hv, hv', sub_zero] at this
      exact this
  · rintro x c hd ⟨g, hg, hc, hv⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hN' : n' + m = N' := by omega
    simp only [add_sub_cancel_right]
    constructor
    · intro h0
      have hz : CohomologyClass.mk g = 0 := by rw [hg, h0]; rfl
      rw [CohomologyClass.mk_eq_zero_iff] at hz
      obtain ⟨M, hM, β, hβ⟩ := hz
      obtain rfl : M = N' := by omega
      have hβ' : δ M (M + 1) β = g.1 := hβ
      have hp : pb (dbl.inr P) g.1 = 0 := pb_eq_zero _ _ hv
      have hb : δ M (M + 1) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) = g.1 := by
        rw [δ_sub, δ_pb, δ_pb, hβ', hp]
        simp
      have hp' : pb (dbl.inr P) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) = 0 := by
        rw [pb_sub, pb_fold, sub_self]
      have hv' : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + M = s) (U : Scheme.{0}) (z : Sx P.right p U),
          ev (R := ZMod q) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) p s h U (z.map (dbl.inr P)) = 0 := fun p s h U z => by
        rw [← ev_pb, hp', ev_zero]
      obtain ⟨y, hy, hcy⟩ := (C n' M hN').1 _ (van_img P _ hv')
      refine ⟨y, hy, ?_⟩
      have h1 := (C n' M hN').2.2.1 _ y hcy
      rw [hb] at h1
      exact (C (n' + 1) (M + 1) (by omega)).2.1 g.1 _ x ((C n' M hN').2.2.2.2 y hy) hd h1 hc
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨β, hβ, hvβ⟩ := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) P).2 (res _ (tw q i)) m N' y
      have e : g.1 = δ N' (N' + 1) β :=
        dbl_ext P _ _ (comp_eq hc ((C n' N' hN').2.2.1 β y hβ)) fun p s h U z => by
          rw [hv, δ_van _ _ _ hvβ]
      apply Subtype.ext
      change c.1 = 0
      rw [← hg, CohomologyClass.mk_eq_zero_iff]
      exact ⟨N', rfl, β, e.symm⟩
end

