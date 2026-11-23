module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CechNervePullbackRepresentableOfIsPullback
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.cechNerve_pullback_representable_of_isPullback :
    ∀ {Y X Y' X' Z Z' : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X') (b : X' ⟶ X) (m : cech f' ⟶ cech f), IsPullback m (cechAug f') (cechAug f) (sch.map b) → ∀ (k : SimplexCategoryᵒᵖ) (e : yoneda.obj Z ≅ (cech f).obj k) (g : Z ⟶ X) (c : Z' ⟶ Z) (g' : Z' ⟶ X'), e.hom ≫ (cechAug f).app k = yoneda.map g → IsPullback c g' g b → ∃ e' : yoneda.obj Z' ≅ (cech f').obj k, e'.hom ≫ m.app k = yoneda.map c ≫ e.hom := by
  intro Y X Y' X' Z Z' f f' b m hm k e g c g' he hc
  have h1 : IsPullback (m.app k) ((cechAug f').app k) ((cechAug f).app k) (yoneda.map b) :=
    hm.map ((evaluation _ _).obj k)
  have h2 : IsPullback (m.app k ≫ e.inv) ((cechAug f').app k) (yoneda.map g) (yoneda.map b) := by
    refine h1.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [← he]
      exact Category.comp_id _
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have h3 : IsPullback (yoneda.map c) (yoneda.map g') (yoneda.map g) (yoneda.map b) :=
    hc.map yoneda
  refine ⟨IsPullback.isoIsPullback _ _ h3 h2, ?_⟩
  have h4 := IsPullback.isoIsPullback_hom_fst _ _ h3 h2
  calc (IsPullback.isoIsPullback _ _ h3 h2).hom ≫ m.app k
      = ((IsPullback.isoIsPullback _ _ h3 h2).hom ≫ (m.app k ≫ e.inv)) ≫ e.hom := by simp
    _ = yoneda.map c ≫ e.hom := by rw [h4]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectedSpaceSpecLocalAndLaurent
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem conn_of_idem (R : Type) [CommRing R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace (PrimeSpectrum R) := by
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun s hs => ?_⟩
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases h e he with rfl | rfl
  · left
    simp
  · right
    simp

private theorem idem_local (O : Type) [CommRing O] [IsLocalRing O] (e : O)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right
    have h1 : e * e = e * 1 := by rw [he.eq, mul_one]
    exact h.mul_left_cancel h1
  · left
    have h1 : (1 - e) * e = (1 - e) * 0 := by rw [mul_zero, sub_mul, one_mul, he.eq, sub_self]
    exact h.mul_left_cancel h1

private theorem idem_zero (O : Type) [CommRing O] [IsLocalRing O] (e : LaurentPolynomial O)
    (he : IsIdempotentElem e) (hm : ∀ n, e.coeff n ∈ IsLocalRing.maximalIdeal O) : e = 0 := by
  classical
  set I : Ideal O := Ideal.span ((e.coeff.support.image e.coeff : Finset O) : Set O) with hI
  have hfg : I.FG := ⟨_, rfl⟩
  have hmem : ∀ n, e.coeff n ∈ I := by
    intro n
    by_cases hn : n ∈ e.coeff.support
    · exact Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn))
    · rw [Finsupp.notMem_support_iff.1 hn]
      exact zero_mem _
  have hsq : I ≤ I * I := by
    rw [hI, Ideal.span_le]
    intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    have h2 : e.coeff n = (e * e).coeff n := by rw [he.eq]
    rw [← hI, h2, AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    split_ifs
    · exact Ideal.mul_mem_mul (hmem i) (hmem j)
    · exact zero_mem _
  have hidem : IsIdempotentElem I := le_antisymm Ideal.mul_le_right hsq
  obtain ⟨f, hf, hIf⟩ := (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hidem
  have hfI : f ∈ I := hIf ▸ Submodule.mem_span_singleton_self f
  have hIm : I ≤ IsLocalRing.maximalIdeal O := by
    rw [hI, Ideal.span_le]
    intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact hm n
  have hf0 : f = 0 := by
    rcases idem_local O f hf with h | h
    · exact h
    · exfalso
      have := hIm hfI
      rw [h] at this
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  apply AddMonoidAlgebra.ext
  ext n
  have hn := hmem n
  rw [hIf, hf0] at hn
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hn
  rw [← ha, smul_zero]
  rfl

private theorem idem_laurent (O : Type) [CommRing O] [IsLocalRing O] (e : LaurentPolynomial O)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  set φ := AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O) with hφ
  have key : ∀ x : LaurentPolynomial O, φ x = 0 → ∀ n, x.coeff n ∈ IsLocalRing.maximalIdeal O := by
    intro x hx n
    have := congrArg (fun y => AddMonoidAlgebra.coeff y n) hx
    simp only [hφ, AddMonoidAlgebra.coeff_mapRingHom] at this
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa using this
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 (he.map φ) with h | h
  · left
    exact idem_zero O e he (key e h)
  · right
    have h1 : 1 - e = 0 := idem_zero O (1 - e) he.one_sub (key _ (by rw [map_sub, map_one, h, sub_self]))
    exact (sub_eq_zero.1 h1).symm

theorem UpperTheory.connectedSpace_spec_local_and_laurent :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ConnectedSpace (Spec (CommRingCat.of O)) ∧ ConnectedSpace (Spec (CommRingCat.of (LaurentPolynomial O))) := by
  intro O _ _
  exact ⟨conn_of_idem O (idem_local O), conn_of_idem _ (idem_laurent O)⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ContinuousSectionsBijectiveAdditiveNatural
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

private theorem cPre_isSheaf (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [ContinuousConstSMul R T] :
    Presheaf.IsSheaf Scheme.proetaleTopology.{0} (cPre R T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{1} (ULift.{1} R))),
    isSheaf_iff_isSheaf_of_type]
  have h := Presieve.isSheaf_of_le _ Scheme.proetaleTopology_le_fpqcTopology
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_fpqcTopology_continuousMapPresheaf.{0, 0} T))
  have h' : Presieve.IsSheaf Scheme.proetaleTopology
      (continuousMapPresheaf.{0} T ⋙ uliftFunctor.{1}) :=
    (Presieve.isSheaf_comp_uliftFunctor_iff _).2 h
  exact Presieve.isSheaf_iso _
    (NatIso.ofComponents (fun U => Iso.refl _) (by intros; rfl) :
      continuousMapPresheaf.{0} T ⋙ uliftFunctor.{1} ≅ cPre R T ⋙ forget _) h'

theorem UpperTheory.continuousSections_bijective_additive_natural :
    ∀ (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (U : Scheme.{0}),
    Function.Bijective (cSec R T (U := U)) ∧ (∀ a b : C(U, T), cSec R T (a + b) = cSec R T a + cSec R T b) ∧ (∀ (V : Scheme.{0}) (g : V ⟶ U) (a : C(U, T)), rs _ g (cSec R T a) = cSec R T (a.comp g.base.hom)) ∧
    ∀ (T' : Type) [AddCommGroup T'] [Module R T'] [TopologicalSpace T'] [IsTopologicalAddGroup T'] [ContinuousConstSMul R T'] (u : T →L[R] T') (a : C(U, T)), ap (cMap u).hom (cSec R T a) = cSec R T' ((⟨u, u.continuous⟩ : C(T, T')).comp a) := by
  intro R _ T _ _ _ _ _ U
  haveI : IsIso (toSheafify Scheme.proetaleTopology (cPre R T)) :=
    isIso_toSheafify _ (cPre_isSheaf R T)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hb := ConcreteCategory.bijective_of_isIso
      ((toSheafify Scheme.proetaleTopology (cPre R T)).app (op U))
    exact hb.comp Equiv.ulift.symm.bijective
  · intro a b
    exact map_add (ModuleCat.Hom.hom ((toSheafify Scheme.proetaleTopology (cPre R T)).app (op U)))
      (ULift.up a) (ULift.up b)
  · intro V g a
    exact (congrArg (fun f => ModuleCat.Hom.hom f (ULift.up a))
      ((toSheafify Scheme.proetaleTopology (cPre R T)).naturality g.op)).symm
  · intro T' _ _ _ _ _ u a
    exact congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) (ULift.up a))
      (toSheafify_naturality Scheme.proetaleTopology (cPreMap u)).symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCyclotomicRootOfStrictHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.exists_cyclotomic_root_of_strictHenselian :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O], SH O → IsUnit (q : O) → ∃ ζ : O, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  intro q _ O _ hO hq
  obtain ⟨hH, hsep⟩ := hO
  have key : ∀ (p : Polynomial O) (x : O), IsLocalRing.residue O (p.eval x) =
      (p.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O x) := by
    intro p x
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hqk : ((q : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (q : O)).2 hq
    simpa using this
  haveI : NeZero ((q : ℕ) : IsLocalRing.ResidueField O) := ⟨hqk⟩
  have hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField O)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg
    (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O))
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective r
  have h1 : (Polynomial.cyclotomic q O).eval a₀ ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, key, Polynomial.map_cyclotomic]
    exact hr
  have h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q O)).eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key, ← Polynomial.derivative_map,
      Polynomial.map_cyclotomic]
    have h0 := (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O)).aeval_derivative_ne_zero
      (x := IsLocalRing.residue O a₀) (by simpa [Polynomial.coe_aeval_eq_eval] using hr)
    simpa [Polynomial.coe_aeval_eq_eval] using h0
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic q O)
    (Polynomial.cyclotomic.monic q O) a₀ h1 h2
  refine ⟨a, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ha
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionOfIntegralSurjectiveAlgClosed
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.exists_section_of_integral_surjective_algClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of K)) [IsIntegralHom g] [Surjective g], ∃ s : Spec (CommRingCat.of K) ⟶ Y, s ≫ g = 𝟙 _ := by
  intro K _ _ Y g _ _
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  obtain ⟨y, -⟩ := g.surjective (IsLocalRing.closedPoint K)
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := Y)).exists_closed_singleton ⟨y, trivial⟩
  haveI : IsIntegralHom (Y.fromSpecResidueField x ≫ g) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hx
    infer_instance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = Y.fromSpecResidueField x ≫ g :=
    ⟨_, Spec.map_preimage _⟩
  haveI : IsIso φ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, hφ]
    infer_instance
  refine ⟨Spec.map (inv φ) ≫ Y.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  simp
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUniqueIdempotentLiftTensorFieldStrictHense
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private lemma algebraMap_eq_zero_of_mem (O K : Type) [CommRing O] [IsLocalRing O] [Field K]
    [Algebra O K] [Algebra.IsIntegral O K] {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    algebraMap O K a = 0 := by
  have hm : Ideal.comap (algebraMap O K) ⊥ = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) (⊥ : Ideal K))
  have h : a ∈ Ideal.comap (algebraMap O K) ⊥ := hm ▸ ha
  simpa using h

private noncomputable def resMap (O K : Type) [CommRing O] [IsLocalRing O] [Field K]
    [Algebra O K] [Algebra.IsIntegral O K] : IsLocalRing.ResidueField O →+* K :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) (algebraMap O K)
    (fun _ ha ↦ algebraMap_eq_zero_of_mem O K ha)

private theorem mem_maximal_of_includeLeft_eq_zero (O R K : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Field K]
    [Algebra O R] [Algebra O K] [Algebra.IsIntegral O R] [Algebra.IsIntegral O K]
    (M : Ideal R) [M.IsMaximal] (x : R)
    (hx : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) x = 0) : x ∈ M := by
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Algebra.IsIntegral O (R ⧸ M) := inferInstance
  letI : Algebra (IsLocalRing.ResidueField O) K := (resMap O K).toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) (AlgebraicClosure (R ⧸ M)) :=
    ((algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).comp (resMap O (R ⧸ M))).toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) K :=
    Algebra.IsIntegral.tower_top O
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) K := inferInstance
  let g : K →ₐ[IsLocalRing.ResidueField O] AlgebraicClosure (R ⧸ M) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let fR : R →+* AlgebraicClosure (R ⧸ M) :=
    (algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).comp (Ideal.Quotient.mk M)
  have hc : ∀ o : O, g (algebraMap O K o) = fR (algebraMap O R o) := by
    intro o
    have h1 : algebraMap O K o =
        algebraMap (IsLocalRing.ResidueField O) K (IsLocalRing.residue O o) := rfl
    rw [h1, g.commutes]
    rfl
  letI : Algebra O (AlgebraicClosure (R ⧸ M)) := (fR.comp (algebraMap O R)).toAlgebra
  let FR : R →ₐ[O] AlgebraicClosure (R ⧸ M) := { fR with commutes' := fun _ ↦ rfl }
  let G : K →ₐ[O] AlgebraicClosure (R ⧸ M) :=
    { g.toRingHom with commutes' := fun o ↦ hc o }
  have h2 := congrArg (Algebra.TensorProduct.productMap FR G) hx
  have h3 : fR x = 0 := by
    simpa [FR, G] using h2
  have h4 : Ideal.Quotient.mk M x = 0 :=
    (algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).injective (by simpa [fR] using h3)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h4

private theorem exists_includeLeft_eq_pow_expChar_pow (O R K : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Field K]
    [Algebra O R] [Algebra O K] [Algebra.IsIntegral O K]
    [IsSepClosed (IsLocalRing.ResidueField O)] (q : ℕ) [ExpChar (IsLocalRing.ResidueField O) q]
    (t : R ⊗[O] K) :
    ∃ n : ℕ, ∃ r : R, (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) r = t ^ q ^ n := by
  letI : Algebra (IsLocalRing.ResidueField O) K := (resMap O K).toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) K :=
    Algebra.IsIntegral.tower_top O
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) K := inferInstance
  haveI : IsPurelyInseparable (IsLocalRing.ResidueField O) K := inferInstance
  haveI : ExpChar K q :=
    expChar_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField O) K).injective q
  rcases subsingleton_or_nontrivial (R ⊗[O] K) with hs | hs
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  haveI : ExpChar (R ⊗[O] K) q :=
    expChar_of_injective_ringHom
      (f := (Algebra.TensorProduct.includeRight : K →ₐ[O] R ⊗[O] K).toRingHom)
      (RingHom.injective _) q
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r y =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem (IsLocalRing.ResidueField O) q y
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨n, algebraMap O R o * r ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc, Algebra.TensorProduct.includeLeftRingHom_apply]
    show (algebraMap O R o * r ^ q ^ n) ⊗ₜ[O] (1 : K) = (r ^ q ^ n) ⊗ₜ[O] (algebraMap O K o)
    rw [← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add a b ha hb =>
    obtain ⟨n1, r1, h1⟩ := ha
    obtain ⟨n2, r2, h2⟩ := hb
    refine ⟨n1 + n2, r1 ^ q ^ n2 + r2 ^ q ^ n1, ?_⟩
    rw [map_add (f := _), map_pow, map_pow, h1, h2, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
      add_comm n2 n1, add_pow_expChar_pow]

theorem UpperTheory.existsUnique_idempotent_lift_tensor_field_strictHenselian :
    ∀ (O R K : Type) [CommRing O] [CommRing R] [Field K] [Algebra O R] [Algebra O K] [Algebra.IsIntegral O R] [Algebra.IsIntegral O K], SH O → ∀ e' : R ⊗[O] K, IsIdempotentElem e' → ∃! e : R, IsIdempotentElem e ∧ (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) e = e' := by
  intro O R K _ _ _ _ _ _ _ hO e' he'
  obtain ⟨hH, hsep⟩ := hO
  obtain ⟨q, hq⟩ := ExpChar.exists (IsLocalRing.ResidueField O)
  have hjac : ∀ y : R, (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) y = 0 →
      ∀ Q : Ideal R, Q.IsMaximal → y ∈ Q := fun y hy Q hQ ↦ by
    haveI := hQ
    exact mem_maximal_of_includeLeft_eq_zero O R K Q y hy
  obtain ⟨n, x, hx⟩ := exists_includeLeft_eq_pow_expChar_pow O R K q e'
  have hx' : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) x = e' := by
    have hpos : 0 < q ^ n := pow_pos (expChar_pos (IsLocalRing.ResidueField O) q) n
    obtain ⟨m, hm⟩ : ∃ m, q ^ n = m + 1 := ⟨q ^ n - 1, by omega⟩
    rw [hx, hm, he'.pow_succ_eq]
  refine existsUnique_of_exists_of_unique ?_ ?_
  · let S := Algebra.adjoin O {x}
    haveI : Module.Finite O S :=
      Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral x)
    let ψ : S →+* R ⊗[O] K :=
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K).comp S.val.toRingHom
    have hxS : x ∈ S := Algebra.subset_adjoin (Set.mem_singleton x)
    let c : ψ.range := ⟨e', ⟨⟨x, hxS⟩, hx'⟩⟩
    have hc : IsIdempotentElem c := Subtype.ext he'
    have hker : RingHom.ker ψ.rangeRestrict ≤ Ideal.jacobson ⊥ := by
      rw [RingHom.ker_rangeRestrict]
      intro s hs
      rw [RingHom.mem_ker] at hs
      refine Ideal.mem_sInf.mpr ?_
      rintro P ⟨-, hP⟩
      haveI := hP
      haveI : Algebra.IsIntegral S R := Algebra.IsIntegral.tower_top O
      obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := R) P (by
        intro z hz
        rw [RingHom.mem_ker] at hz
        have : z = 0 := Subtype.ext hz
        simp [this])
      rw [← hQP, Ideal.mem_comap]
      exact hjac _ hs Q hQ
    obtain ⟨e, ⟨he, hec⟩, -⟩ := GlobalTheory.existsUnique_idempotent_lift_of_henselian O ψ.rangeRestrict
      ψ.rangeRestrict_surjective hker hc
    refine ⟨(e : R), he.map S.val, ?_⟩
    exact congrArg Subtype.val hec
  · rintro y z ⟨hy, hyc⟩ ⟨hz, hzc⟩
    have hy2 : y * y = y := hy
    have hz2 : z * z = z := hz
    have he2 : e' * e' = e' := he'
    have hf0 : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) (y + z - 2 * y * z) = 0 := by
      rw [map_sub, map_add (f := _), map_mul, map_mul, hyc, hzc, map_ofNat]
      linear_combination (-2 : R ⊗[O] K) * he2
    have hfj : ∀ Q : Ideal R, Q.IsMaximal → y + z - 2 * y * z ∈ Q := hjac _ hf0
    have hmem : y + z - 2 * y * z ∈ Ideal.jacobson (⊥ : Ideal R) :=
      Ideal.mem_sInf.mpr (fun Q hQ ↦ hfj Q hQ.2)
    have hu := Ideal.mem_jacobson_bot.mp hmem (-1)
    have hfid : (y + z - 2 * y * z) * (y + z - 2 * y * z) = y + z - 2 * y * z := by
      linear_combination (1 + 4 * z * z - 4 * z) * hy2 + hz2
    have hff : (y + z - 2 * y * z) * ((y + z - 2 * y * z) * -1 + 1) = 0 := by
      linear_combination (-1 : R) * hfid
    have hf : y + z - 2 * y * z = 0 := (hu.mul_left_eq_zero).mp hff
    linear_combination (-1 + 2 * z) * hy2 + (1 - 2 * y) * hz2 + (y - z) * hf
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyConstantComapBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

private theorem clopen_pre_inj {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    (h : ∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e')
    {C D : Set (PrimeSpectrum B)} (hC : IsClopen C) (hD : IsClopen D)
    (hCD : PrimeSpectrum.comap φ ⁻¹' C = PrimeSpectrum.comap φ ⁻¹' D) : C = D := by
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hC
  obtain ⟨d, hd, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hD
  have h1 : φ e = φ d := by
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem (he.map φ) (hd.map φ)
    apply SetLike.coe_injective
    rw [← PrimeSpectrum.comap_basicOpen, ← PrimeSpectrum.comap_basicOpen]
    exact hCD
  rw [(h (φ e) (he.map φ)).unique ⟨he, rfl⟩ ⟨hd, h1.symm⟩]

private theorem clopen_pre_surj {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    (h : ∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e')
    {C' : Set (PrimeSpectrum B')} (hC' : IsClopen C') :
    ∃ C : Set (PrimeSpectrum B), IsClopen C ∧ PrimeSpectrum.comap φ ⁻¹' C = C' := by
  obtain ⟨e', he', rfl⟩ := PrimeSpectrum.isClopen_iff.1 hC'
  obtain ⟨e, ⟨he, rfl⟩, -⟩ := h e' he'
  exact ⟨_, PrimeSpectrum.isClopen_iff.2 ⟨e, he, rfl⟩, rfl⟩

theorem UpperTheory.locallyConstant_comap_bijective :
    ∀ (B B' : Type) [CommRing B] [CommRing B'] (φ : B →+* B') (Y : Type), (∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e') → Function.Bijective (fun a : LocallyConstant (PrimeSpectrum B) Y => a.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩) := by
  intro B B' _ _ φ Y h
  constructor
  · intro a b hab
    have hfib : ∀ y, (a : PrimeSpectrum B → Y) ⁻¹' {y} = (b : PrimeSpectrum B → Y) ⁻¹' {y} := by
      intro y
      apply clopen_pre_inj φ h (a.isLocallyConstant.isClopen_fiber y)
        (b.isLocallyConstant.isClopen_fiber y)
      ext q
      have hq : a (PrimeSpectrum.comap φ q) = b (PrimeSpectrum.comap φ q) :=
        DFunLike.congr_fun hab q
      change a (PrimeSpectrum.comap φ q) = y ↔ b (PrimeSpectrum.comap φ q) = y
      rw [hq]
    ext p
    have hp : p ∈ (b : PrimeSpectrum B → Y) ⁻¹' {a p} := by
      rw [← hfib]
      rfl
    exact hp.symm
  · intro a'
    choose C hCc hC using fun y =>
      clopen_pre_surj φ h (a'.isLocallyConstant.isClopen_fiber y)
    have hdisj : ∀ y z, y ≠ z → C y ∩ C z = ∅ := by
      intro y z hyz
      apply clopen_pre_inj φ h ((hCc y).inter (hCc z)) isClopen_empty
      rw [Set.preimage_inter, hC, hC, Set.preimage_empty]
      ext q
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h1 h2 => hyz (h1.symm.trans h2)
    have hcov : (⋃ y ∈ Set.range a', C y) = Set.univ := by
      apply clopen_pre_inj φ h
        (a'.range_finite.isClopen_biUnion fun y _ => hCc y) isClopen_univ
      rw [Set.preimage_iUnion₂, Set.preimage_univ]
      ext q
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨a' q, ⟨q, rfl⟩, by rw [hC]; rfl⟩
    have hex : ∀ p, ∃ y, p ∈ C y := by
      intro p
      have hp : p ∈ ⋃ y ∈ Set.range a', C y := hcov ▸ Set.mem_univ p
      obtain ⟨y, -, hy⟩ := Set.mem_iUnion₂.1 hp
      exact ⟨y, hy⟩
    choose a ha using hex
    have hiff : ∀ p y, a p = y ↔ p ∈ C y := by
      intro p y
      constructor
      · rintro rfl
        exact ha p
      · intro hy
        by_contra hne
        have : p ∈ C (a p) ∩ C y := ⟨ha p, hy⟩
        rw [hdisj _ _ hne] at this
        exact this
    have hlc : IsLocallyConstant a := by
      refine (IsLocallyConstant.iff_isOpen_fiber).2 fun y => ?_
      have : a ⁻¹' {y} = C y := by
        ext p
        exact hiff p y
      rw [this]
      exact (hCc y).isOpen
    refine ⟨⟨a, hlc⟩, ?_⟩
    ext q
    have hq : q ∈ PrimeSpectrum.comap φ ⁻¹' C (a' q) := by
      rw [hC]
      rfl
    exact (hiff _ _).2 hq
end

