module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.EtaleCohomology.EtaleSheaves.Bundle0047
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.AcyMiddleOfShortExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.acy_middle_of_shortExact :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → Acy Q S.X₃ → Acy Q S.X₂ := by
  intro Q S hS h1 h3 P hP n hn
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) n).1
  haveI := h1 P hP n hn
  haveI := h3 P hP n hn
  refine ⟨fun y y' => ?_⟩
  have hy : ∀ u : HK ℤ (sgl ((free ℤ).obj P)) S.X₂ n, u = 0 := by
    intro u
    obtain ⟨v, hv⟩ := (e u).1 (Subsingleton.elim _ _)
    rw [← hv, Subsingleton.elim v 0, map_zero]
  rw [hy y, hy y']
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.AcyRightOfShortExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.acy_right_of_shortExact :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → Acy Q S.X₂ → Acy Q S.X₃ := by
  intro Q S hS h1 h2 P hP n hn
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) n).2.1
  haveI := h1 P hP (n + 1) (by omega)
  haveI := h2 P hP n hn
  refine ⟨fun y y' => ?_⟩
  have hy : ∀ u : HK ℤ (sgl ((free ℤ).obj P)) S.X₃ n, u = 0 := by
    intro u
    obtain ⟨v, hv⟩ := (e u).1 (Subsingleton.elim _ _)
    rw [← hv, Subsingleton.elim v 0, map_zero]
  rw [hy y, hy y']
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveClHypercohomologySingletonZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private lemma sec_comp {A B C : Shv ℤ} (p : A ⟶ B) (q : B ⟶ C) {V : Scheme.{0}} (x : Sec A V) :
    Sec.map (p ≫ q) x = Sec.map q (Sec.map p x) := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma exists_lift {M F : Shv ℤ} (g : M ⟶ (res ℤ F).X 0) (hg : g ≫ (res ℤ F).d 0 1 = 0) :
    ∃ f : M ⟶ F, f ≫ resι ℤ F = g := by
  classical
  have hinj : ∀ U : Scheme, Function.Injective (Sec.map (resι ℤ F) (U := U)) :=
    fun U => (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ F U).2.1
  have hex : ∀ (U : Scheme) (x : Sec M U), ∃ a : Sec F U, Sec.map (resι ℤ F) a = Sec.map g x := by
    intro U x
    refine ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ F U).1 _).1 ?_
    rw [← sec_comp, hg]
    rfl
  let φ : ∀ U : Scheme, Sec M U → Sec F U := fun U x => (hex U x).choose
  have hφ : ∀ U x, Sec.map (resι ℤ F) (φ U x) = Sec.map g x := fun U x => (hex U x).choose_spec
  let η : M.obj ⟶ F.obj :=
    { app := fun U => ModuleCat.ofHom
        { toFun := φ U.unop
          map_add' := fun x y => hinj _ (by
            rw [hφ]
            show (ModuleCat.Hom.hom _) (x + y) = (ModuleCat.Hom.hom _) (φ _ x + φ _ y)
            rw [map_add (f := _), map_add (f := _)]
            exact congrArg₂ (· + ·) (hφ _ x).symm (hφ _ y).symm)
          map_smul' := fun r x => hinj _ (by
            rw [hφ, RingHom.id_apply]
            have e1 := (ModuleCat.Hom.hom (g.hom.app U)).map_smul r x
            have e2 := (ModuleCat.Hom.hom ((resι ℤ F).hom.app U)).map_smul r (φ _ x)
            exact e1.trans ((congrArg _ (hφ _ x).symm).trans e2.symm)) }
      naturality := by
        intro U V h
        ext x
        apply hinj
        have n1 := congrArg (fun k => ModuleCat.Hom.hom k x) (g.hom.naturality h)
        have n2 := congrArg (fun k => ModuleCat.Hom.hom k (φ _ x)) ((resι ℤ F).hom.naturality h)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at n1 n2
        show Sec.map (resι ℤ F) (φ _ ((ModuleCat.Hom.hom (M.obj.map h)) x)) =
          Sec.map (resι ℤ F) ((ModuleCat.Hom.hom (F.obj.map h)) (φ _ x))
        rw [hφ]
        refine n1.trans ?_
        refine Eq.trans ?_ n2.symm
        exact congrArg _ (hφ _ x).symm }
  refine ⟨⟨η⟩, (GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (⟨η⟩ ≫ resι ℤ F)).2.2.2 g (fun U a => ?_)⟩
  rw [sec_comp]
  exact hφ U a

set_option backward.isDefEq.respectTransparency false in
private lemma sgl_f {M F : Shv ℤ} (f : M ⟶ F) :
    sglι M ≫ ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F).f 0 = f ≫ resι ℤ F := by
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  have h : sglι M ≫ ((CochainComplex.singleFunctor (Shv ℤ) 0).map f).f 0 = f ≫ sglι F := by
    simp [sglι, CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self]
  rw [h, Category.assoc, (_root_.GlobalTheory.EtC.ResBasic.res_basic ℤ F).2.2.2.2.1]

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.bijective_cl_hypercohomology_singleton_zero :
    ∀ (M F : Shv ℤ), Function.Bijective (cl : (M ⟶ F) → HK ℤ (sgl M) F 0) := by
  intro M F
  have hz : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl M).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hp
  have hL : IsZero ((res ℤ F).X (-1)) := by
    haveI := (_root_.GlobalTheory.EtC.ResBasic.res_basic ℤ F).2.2.1
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 (-1) (by norm_num)
  have hβ0 : ∀ β : Cochain (sgl M) (res ℤ F) (-1), β = 0 := by
    intro β
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = -1 := by omega
      exact hL.eq_of_tgt _ _
    · exact (hz p hp).eq_of_src _ _
  have hcob : ∀ x : Cocycle (sgl M) (res ℤ F) 0, x ∈ coboundaries (sgl M) (res ℤ F) 0 → x = 0 := by
    intro x hx
    obtain ⟨β, hβ⟩ := (mem_coboundaries_iff x (-1) (by norm_num)).1 hx
    apply Cocycle.ext
    rw [← hβ, hβ0 β, δ_zero]
    rfl
  have hmono : Mono (resι ℤ F) := (_root_.GlobalTheory.EtC.ResBasic.res_basic ℤ F).2.2.2.2.2.1
  have hsg : IsIso (sglι M) := by
    dsimp [sglι]
    infer_instance
  constructor
  · intro f f' h
    have h1 : Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F)
        = Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f' ≫ resAug F) := by
      have := hcob _ ((CohomologyClass.mk_eq_zero_iff _).1
        (by rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 h))
      exact sub_eq_zero.1 this
    have h2 := congrArg (fun x : Cocycle (sgl M) (res ℤ F) 0 =>
      (x : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0)) h1
    simp only [Cocycle.ofHom_coe, Cochain.ofHom_v] at h2
    apply (cancel_mono (resι ℤ F)).1
    rw [← sgl_f, ← sgl_f, h2]
  · intro c
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
    have hz1 : (z : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0) ≫ (res ℤ F).d 0 1 = 0 := by
      have e := congrArg (fun w : Cochain (sgl M) (res ℤ F) 1 => w.v 0 1 (zero_add 1))
        ((Cocycle.mem_iff 0 1 (zero_add 1) _).1 z.2)
      simp only [δ_zero_cochain_v, Cochain.zero_v] at e
      rwa [(hz 1 one_ne_zero).eq_of_tgt ((sgl M).d 0 1) 0, zero_comp, sub_zero] at e
    obtain ⟨f, hf⟩ := exists_lift (sglι M ≫ (z : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0))
      (by rw [Category.assoc, hz1, comp_zero])
    refine ⟨f, ?_⟩
    show CohomologyClass.mk _ = CohomologyClass.mk z
    congr 1
    apply Cocycle.ext
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [add_zero] at hpq
    subst hpq
    by_cases hp : p = 0
    · subst hp
      rw [Cocycle.ofHom_coe, Cochain.ofHom_v, ← cancel_epi (sglι M), sgl_f, hf]
    · exact (hz p hp).eq_of_src _ _
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EpiFreeBiprodDescOfZariskiLocallySurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private def sumP (P₁ P₂ : PSh) : PSh where
  obj U := P₁.obj U ⊕ P₂.obj U
  map h := TypeCat.ofHom (Sum.map (P₁.map h) (P₂.map h))
  map_id U := by
    ext x
    rcases x with x | x <;> simp
  map_comp a b := by
    ext x
    rcases x with x | x <;> simp

private def sumD {P₁ P₂ Q : PSh} (f : P₁ ⟶ Q) (g : P₂ ⟶ Q) : sumP P₁ P₂ ⟶ Q where
  app U := TypeCat.ofHom (Sum.elim (f.app U) (g.app U))
  naturality U V k := by
    ext x
    rcases x with x | x
    · exact congrFun (congrArg (fun t => t.hom) (f.naturality k)) x
    · exact congrFun (congrArg (fun t => t.hom) (g.naturality k)) x

theorem UpperTheory.epi_freeBiprodDesc_of_zariskiLocally_surjective :
    ∀ (R : Type) [CommRing R] {P₁ P₂ Q : PSh} (f : P₁ ⟶ Q) (g : P₂ ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V h => (∃ x, f.app (op V) x = Q.map h.op y) ∨ ∃ x, g.app (op V) x = Q.map h.op y) → Epi (biprod.desc ((free R).map f) ((free R).map g)) := by
  intro R _ P₁ P₂ Q f g h
  have mc : ∀ {P : PSh} (c : P ⟶ Q) {M : Shv R} (p : (free R).obj Q ⟶ M) (T : Scheme.{0})
      (x : P.obj (op T)),
      Sec.map ((free R).map c ≫ p) (freeGen R P T x) = Sec.map p (freeGen R Q T (c.app (op T) x)) := by
    intro P c M p T x
    have h4 := (GlobalTheory.T.free_sections_ext_res_map R P M).2.2.2 Q c T x
    show Sec.map p (Sec.map ((free R).map c) (freeGen R P T x)) = _
    rw [h4]
  have hE : Epi ((free R).map (sumD f g)) := by
    apply (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (sumD f g)).2.1
    intro T y
    obtain ⟨S, hS, hP⟩ := h T y
    refine ⟨S, hS, fun W k hk => ?_⟩
    rcases hP W k hk with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr x, hx⟩
  constructor
  intro Z u v huv
  have ha : (free R).map f ≫ u = (free R).map f ≫ v := by
    simpa using congrArg (biprod.inl ≫ ·) huv
  have hb : (free R).map g ≫ u = (free R).map g ≫ v := by
    simpa using congrArg (biprod.inr ≫ ·) huv
  rw [← cancel_epi ((free R).map (sumD f g))]
  apply (GlobalTheory.T.free_sections_ext_res_map R (sumP P₁ P₂) Z).2.1
  intro T z
  rw [mc, mc]
  cases z with
  | inl x =>
    have e := mc f u T x
    have e' := mc f v T x
    rw [ha] at e
    exact e.symm.trans e'
  | inr x =>
    have e := mc g u T x
    have e' := mc g v T x
    rw [hb] at e
    exact e.symm.trans e'
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtalePurityFreeCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

private lemma sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change (φ.hom.app (op U) ≫ G.obj.map g.op).hom x = (F.obj.map g.op ≫ φ.hom.app (op V)).hom x
  rw [φ.hom.naturality]

private lemma sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (a : F ⟶ G) (b : G ⟶ H)
    {U : Scheme.{0}} (x : Sec F U) : Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

private lemma sec_map_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

private lemma res_univ_eq_zero {R : Type} [CommRing R] {A W : Scheme.{0}} (i : A ⟶ W) {Z : Shv R}
    (h : (free R).obj (yoneda.obj W) ⟶ Z) (h0 : (free R).map (yoneda.map i) ≫ h = 0) :
    Sec.res i (Sec.map h (freeGen R (yoneda.obj W) W (𝟙 W))) = 0 := by
  rw [sec_map_res, CupSpec.freeGen_res]
  have e : (ConcreteCategory.hom ((yoneda.obj W).map i.op)) (𝟙 W) =
      (ConcreteCategory.hom ((yoneda.map i).app (op A))) (𝟙 A) := by simp
  rw [e, ← CupSpec.freeGen_map, ← sec_map_comp, h0, sec_map_zero]

theorem UpperTheory.etale_purity_free_cover :
    LateralTheory.CohomologicalPurity.Thom.LeafFreeCov := by
  intro R _ X U V
  apply Preadditive.epi_of_cancel_zero
  intro Z g hg
  let ι := {O : X.Opens // O = U ∨ O = V}
  have hle : ∀ i : ι, i.1 ≤ U ⊔ V := by
    rintro ⟨O, rfl | rfl⟩
    · exact le_sup_left
    · exact le_sup_right
  have gz : ∀ i : ι, (free R).map (yoneda.map (X.homOfLE (hle i))) ≫ g = 0 := by
    rintro ⟨O, rfl | rfl⟩
    · have := congrArg (biprod.inl ≫ ·) hg
      simpa using this
    · have := congrArg (biprod.inr ≫ ·) hg
      simpa using this
  have cover : ∀ (O : X.Opens) (hO : O ≤ U ⊔ V) (y : (U ⊔ V : X.Opens).toScheme),
      (U ⊔ V).ι y ∈ O → ∃ z, X.homOfLE hO z = y := by
    intro O hO y hy
    have hy' : (U ⊔ V).ι y ∈ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      exact hy
    obtain ⟨z, hz⟩ := hy'
    refine ⟨z, (U ⊔ V).ι.isOpenEmbedding.injective ?_⟩
    change (X.homOfLE hO ≫ (U ⊔ V).ι) z = _
    rw [Scheme.homOfLE_ι, hz]
  refine CupSpec.free_ext g 0 (fun T x => ?_)
  change Sec.map g (freeGen R _ T x) = 0
  let xx : T ⟶ (U ⊔ V : X.Opens).toScheme := x
  obtain ⟨hsep, -⟩ := sec_sep_glue_of_points R Z T ι (fun i => pullback x (X.homOfLE (hle i)))
    (fun i => pullback.fst x (X.homOfLE (hle i))) (fun i => inferInstance) (by
      intro t
      have hy : (U ⊔ V).ι (xx t) ∈ ((U ⊔ V : X.Opens) : Set X) := by
        rw [← Scheme.Opens.range_ι]
        exact ⟨xx t, rfl⟩
      rw [TopologicalSpace.Opens.coe_sup] at hy
      rcases hy with hU | hV
      · obtain ⟨z, hz⟩ := cover U le_sup_left (xx t) hU
        have ht : t ∈ Set.range (pullback.fst x (X.homOfLE (hle ⟨U, Or.inl rfl⟩))) := by
          rw [Scheme.Pullback.range_fst]
          exact ⟨z, hz⟩
        obtain ⟨v, hv⟩ := ht
        exact ⟨⟨U, Or.inl rfl⟩, v, hv⟩
      · obtain ⟨z, hz⟩ := cover V le_sup_right (xx t) hV
        have ht : t ∈ Set.range (pullback.fst x (X.homOfLE (hle ⟨V, Or.inr rfl⟩))) := by
          rw [Scheme.Pullback.range_fst]
          exact ⟨z, hz⟩
        obtain ⟨v, hv⟩ := ht
        exact ⟨⟨V, Or.inr rfl⟩, v, hv⟩)
  apply hsep
  intro i
  have z : Sec.map g (freeGen R (yoneda.obj (U ⊔ V : X.Opens).toScheme) i.1.toScheme (X.homOfLE (hle i))) = 0 := by
    have := res_univ_eq_zero (X.homOfLE (hle i)) g (gz i)
    rwa [sec_map_res, CupSpec.freeGen_res, show (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (X.homOfLE (hle i)).op)) (𝟙 _) = X.homOfLE (hle i) by simp] at this
  rw [sec_map_res, CupSpec.freeGen_res]
  have e : (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (pullback.fst x (X.homOfLE (hle i))).op)) x =
      (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (pullback.snd x (X.homOfLE (hle i))).op)) (X.homOfLE (hle i)) := by
    simp [pullback.condition]
  rw [e, ← CupSpec.freeGen_res, ← sec_map_res, z]
  exact map_zero _
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteEtaleFaithfullyFlatCoverOfEtaleLocal
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private lemma exists_local (A : Type) [CommRing A]
    (P : ∀ V : Scheme.{0}, (V ⟶ Spec (CommRingCat.of A)) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of A)) (k : W ⟶ V), P V g → P W (k ≫ g))
    (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of A)) (hV : IsAffine V) (hg : Etale g)
    (hPV : P V g) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.Etale A B ∧
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap A B))) = Set.range g ∧
      P (Spec (CommRingCat.of B)) (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  haveI := hg
  let φ : CommRingCat.of A ⟶ Γ(V, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appTop
  letI : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra
  have hg' : g = V.isoSpec.hom ≫ Spec.map φ := by
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hinv : Spec.map φ = V.isoSpec.inv ≫ g := by
    rw [hg', Iso.inv_hom_id_assoc]
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))) = Spec.map φ := rfl
  refine ⟨Γ(V, ⊤), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · have he : Etale (Spec.map φ) := by
      rw [hinv]
      infer_instance
    exact RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp he)
  · rw [hmap, hg']
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨V.isoSpec.inv z, by simp⟩
    · rintro ⟨z, rfl⟩
      exact ⟨V.isoSpec.hom z, rfl⟩
  · rw [hmap, hinv]
    exact hP V _ g V.isoSpec.inv hPV

theorem UpperTheory.exists_finite_etale_faithfullyFlat_cover_of_etaleLocal_affine :
    ∀ (A : Type) [CommRing A] (P : ∀ V : Scheme.{0}, (V ⟶ Spec (CommRingCat.of A)) → Prop),
        (∀ (V W : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of A)) (k : W ⟶ V), P V g → P W (k ≫ g)) →
        Loc (Spec (CommRingCat.of A)) P →
        ∃ (n : ℕ) (C : Fin n → Type) (_ : ∀ i, CommRing (C i)) (_ : ∀ i, Algebra A (C i)),
          Algebra.Etale A (∀ i, C i) ∧ Module.FaithfullyFlat A (∀ i, C i) ∧
          ∀ i, P (Spec (CommRingCat.of (C i))) (Spec.map (CommRingCat.ofHom (algebraMap A (C i)))) := by
  intro A _ P hP hL
  have hx := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover _ P hP).1 hL
  choose V g hVa hge hxm hPx using hx
  have h1 := fun x => exists_local A P hP (V x) (g x) (hVa x) (hge x) (hPx x)
  choose B iB aB hBe hBr hBP using h1
  letI : ∀ x, CommRing (B x) := iB
  letI : ∀ x, Algebra A (B x) := aB
  have hopen : ∀ x, IsOpen (Set.range (g x)) := fun x => by
    haveI := hge x
    exact IsOpenMap.isOpen_range (g x).isOpenMap
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => Set.range (g x)) hopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxm x⟩)
  let e : Fin t.card ≃ t := t.equivFin.symm
  haveI : ∀ i, Algebra.Etale A (B (e i)) := fun i => hBe _
  refine ⟨t.card, fun i => B (e i), fun i => inferInstance, fun i => inferInstance,
    inferInstance, ?_, fun i => hBP _⟩
  refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
  obtain ⟨x, hxt, hpx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
  obtain ⟨i, hi⟩ := e.surjective ⟨x, hxt⟩
  have hpi : p ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (B (e i))))) := by
    rw [hBr, hi]
    exact hpx
  obtain ⟨q, hq⟩ := hpi
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j => B (e j)) i) q, ?_⟩
  rw [← hq]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LiftIdempotentFactorizationHolds
section
noncomputable section

theorem UpperTheory.liftIdempotentFactorization_holds :
    LateralTheory.E.LIdemLiftPf.LFact := by
  intro A _ I _ g hg n m h
  exact UpperTheory.exists_monic_factor_lift_of_pow_mul_sub_one_pow A I g hg n m h

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.PicUnit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

namespace UpperTheory.PicD

theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec ofRings.sec
  exact map_add (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)))
    (⟨Additive.ofMul u⟩ : ULift.{1, 0} (Additive (Γ(U, ⊤))ˣ)) ⟨Additive.ofMul v⟩

theorem unitSec_one {U : Scheme.{0}} : unitSec (1 : (Γ(U, ⊤))ˣ) = 0 := by
  unfold unitSec ofRings.sec
  exact map_zero (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)))

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have h := congrArg (fun f => (ModuleCat.Hom.hom f)
    (⟨Additive.ofMul u⟩ : ULift.{1, 0} (Additive (Γ(U, ⊤))ˣ)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)
  exact h.symm

end UpperTheory.PicD
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TotalHomComplexIsKInjectiveOfBoundedInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

theorem UpperTheory.totalHomComplex_isKInjective_of_bounded_injective :
    ∀ (q : ℕ) {B : Scheme.{0}} (C : B.Etale ⥤ Cx (ZMod q)) (I : Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)), (∀ n, Injective (⟨TP C I n, h n⟩ : SShv B q)) → (∀ (U : B.Etale) (n : ℤ), 0 < n → IsZero ((C.obj U).X n)) → (∀ n : ℤ, n < 0 → IsZero (I.X n)) → (TC C I h).IsKInjective := by
  intro q B C I h hinj hC hI
  have hcoch : ∀ (U : B.Etale) (n : ℤ), n < 0 → ∀ α : Cochain (C.obj U) I n, α = 0 := by
    intro U n hn α
    refine Cochain.ext _ _ fun p r hpr => ?_
    rcases lt_or_ge 0 p with hp | hp
    · exact (hC U p hp).eq_of_src _ _
    · exact (hI r (by omega)).eq_of_tgt _ _
  haveI : (TC C I h).IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    rw [IsZero.iff_id_eq_zero]
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun α => ?_)))
    exact (hcoch U.unop n hn α).trans (hcoch U.unop n hn _).symm
  haveI : ∀ n, Injective ((TC C I h).X n) := hinj
  exact CochainComplex.isKInjective_of_injective _ 0
end

