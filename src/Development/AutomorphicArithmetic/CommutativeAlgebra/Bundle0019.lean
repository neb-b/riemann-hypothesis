module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.BlowupCategories.AffC
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0014
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0015
public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0010
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductPairOfBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.InverseDerivation

variable {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c) (A : CommRingCat.{0})

private abbrev BD : Prop :=
  Function.Bijective (fun x : a.D.obj A => ((ρ.d.app A x, σ.d.app A x) : b.D.obj A × c.D.obj A))

private abbrev BG : Prop :=
  Function.Bijective (fun g : a.G.obj A => ((ρ.g.app A g, σ.g.app A g) : b.G.obj A × c.G.obj A))

variable {ρ σ A}

private noncomputable def invD (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : a.D.obj A :=
  (Equiv.ofBijective _ hd).symm p

private noncomputable def invG (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : a.G.obj A :=
  (Equiv.ofBijective _ hg).symm p

private theorem invD_fst (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : ρ.d.app A (invD hd p) = p.1 := by
  exact congrArg Prod.fst (Equiv.ofBijective_apply_symm_apply _ hd p)

private theorem invD_snd (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : σ.d.app A (invD hd p) = p.2 := by
  exact congrArg Prod.snd (Equiv.ofBijective_apply_symm_apply _ hd p)

private theorem invG_fst (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : ρ.g.app A (invG hg p) = p.1 := by
  exact congrArg Prod.fst (Equiv.ofBijective_apply_symm_apply _ hg p)

private theorem invG_snd (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : σ.g.app A (invG hg p) = p.2 := by
  exact congrArg Prod.snd (Equiv.ofBijective_apply_symm_apply _ hg p)

private theorem invD_eq (hd : BD ρ σ A) {x : a.D.obj A} {p : b.D.obj A × c.D.obj A}
    (h1 : ρ.d.app A x = p.1) (h2 : σ.d.app A x = p.2) : invD hd p = x := by
  apply hd.1
  refine (Equiv.ofBijective_apply_symm_apply _ hd p).trans ?_
  exact Prod.ext h1.symm h2.symm

private theorem invG_eq (hg : BG ρ σ A) {x : a.G.obj A} {p : b.G.obj A × c.G.obj A}
    (h1 : ρ.g.app A x = p.1) (h2 : σ.g.app A x = p.2) : invG hg p = x := by
  apply hg.1
  refine (Equiv.ofBijective_apply_symm_apply _ hg p).trans ?_
  exact Prod.ext h1.symm h2.symm

private noncomputable def lift (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) : J ⥤ Ob a A where
  obj j := ⟨invD hd ((y.obj j).pt, (z.obj j).pt)⟩
  map {i j} f := ⟨invG hg ((y.map f).1, (z.map f).1), by
    refine hd.1 (Prod.ext ?_ ?_)
    · change ρ.d.app A _ = ρ.d.app A (a.smul A _ _)
      rw [ρ.eq, invD_fst, invD_fst, invG_fst]
      exact (y.map f).2
    · change σ.d.app A _ = σ.d.app A (a.smul A _ _)
      rw [σ.eq, invD_snd, invD_snd, invG_snd]
      exact (z.map f).2⟩
  map_id j := by
    refine Subtype.ext (invG_eq hg ?_ ?_)
    · change ρ.g.app A 1 = (y.map (𝟙 j)).1
      rw [y.map_id]
      exact map_one (ρ.g.app A).hom
    · change σ.g.app A 1 = (z.map (𝟙 j)).1
      rw [z.map_id]
      exact map_one (σ.g.app A).hom
  map_comp {i j l} f g := by
    refine Subtype.ext (invG_eq hg ?_ ?_)
    · change ρ.g.app A (invG hg _ * invG hg _) = (y.map (f ≫ g)).1
      rw [y.map_comp]
      refine (map_mul (ρ.g.app A).hom _ _).trans ?_
      change ρ.g.app A _ * ρ.g.app A _ = _
      rw [invG_fst, invG_fst]
      rfl
    · change σ.g.app A (invG hg _ * invG hg _) = (z.map (f ≫ g)).1
      rw [z.map_comp]
      refine (map_mul (σ.g.app A).hom _ _).trans ?_
      change σ.g.app A _ * σ.g.app A _ = _
      rw [invG_snd, invG_snd]
      rfl

private theorem lift_fst (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) :
    lift hd hg y z ⋙ ρ.fn A = y := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨ρ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob b A) = y.obj j
    rw [invD_fst]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨ρ.d.app A (invD hd ((y.obj i).pt, (z.obj i).pt))⟩ : Ob b A) = y.obj i
      rw [invD_fst]
    · change (⟨ρ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob b A) = y.obj j
      rw [invD_fst]
    · change ρ.g.app A (invG hg ((y.map f).1, (z.map f).1)) = (y.map f).1
      rw [invG_fst]

private theorem lift_snd (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) :
    lift hd hg y z ⋙ σ.fn A = z := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨σ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob c A) = z.obj j
    rw [invD_snd]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨σ.d.app A (invD hd ((y.obj i).pt, (z.obj i).pt))⟩ : Ob c A) = z.obj i
      rw [invD_snd]
    · change (⟨σ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob c A) = z.obj j
      rw [invD_snd]
    · change σ.g.app A (invG hg ((y.map f).1, (z.map f).1)) = (z.map f).1
      rw [invG_snd]

private theorem lift_comp (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (w : J ⥤ Ob a A) :
    lift hd hg (w ⋙ ρ.fn A) (w ⋙ σ.fn A) = w := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨invD hd (ρ.d.app A (w.obj j).pt, σ.d.app A (w.obj j).pt)⟩ : Ob a A) = w.obj j
    rw [invD_eq hd rfl rfl]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨invD hd (ρ.d.app A (w.obj i).pt, σ.d.app A (w.obj i).pt)⟩ : Ob a A) = w.obj i
      rw [invD_eq hd rfl rfl]
    · change (⟨invD hd (ρ.d.app A (w.obj j).pt, σ.d.app A (w.obj j).pt)⟩ : Ob a A) = w.obj j
      rw [invD_eq hd rfl rfl]
    · change invG hg (ρ.g.app A (w.map f).1, σ.g.app A (w.map f).1) = (w.map f).1
      exact invG_eq hg rfl rfl

private theorem comp_inj (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] {w w' : J ⥤ Ob a A}
    (h1 : w ⋙ ρ.fn A = w' ⋙ ρ.fn A) (h2 : w ⋙ σ.fn A = w' ⋙ σ.fn A) : w = w' := by
  calc w = lift hd hg (w ⋙ ρ.fn A) (w ⋙ σ.fn A) := (lift_comp hd hg w).symm
    _ = lift hd hg (w' ⋙ ρ.fn A) (w' ⋙ σ.fn A) := by rw [h1, h2]
    _ = w' := lift_comp hd hg w'

end UpperTheory.InverseDerivation

open UpperTheory.InverseDerivation in
theorem UpperTheory.isIso_stackProductPair_of_bijective :
    ∀ (E : Spc) {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c),
        (∀ A, Function.Bijective (fun x : a.D.obj A => ((ρ.d.app A x, σ.d.app A x) : b.D.obj A × c.D.obj A))) →
        (∀ A, Function.Bijective (fun g : a.G.obj A => ((ρ.g.app A g, σ.g.app A g) : b.G.obj A × c.G.obj A))) →
        IsIso (Sp.pair E ρ σ) := by
  intro E a b c ρ σ hd hg
  refine isIso_of_bijective_on_simplices _ (fun k T => ?_)
  let A : CommRingCat := Scheme.Γ.obj (op T)
  change Function.Bijective
    (fun p : (E.obj (op (SimplexCategory.mk k))).obj (op T) × (Fin (k+1) ⥤ Ob a A) =>
      (((p.1, p.2 ⋙ ρ.fn A), p.2 ⋙ σ.fn A) :
        ((E.obj (op (SimplexCategory.mk k))).obj (op T) × (Fin (k+1) ⥤ Ob b A)) × (Fin (k+1) ⥤ Ob c A)))
  refine ⟨fun p q h => ?_, fun q => ?_⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact Prod.ext h1 (comp_inj (hd A) (hg A) h2 h3)
  · refine ⟨(q.1.1, lift (hd A) (hg A) q.1.2 q.2), ?_⟩
    simp only [lift_fst, lift_snd]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MemRangeOfProperGenericFibreSeparated
section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

set_option maxHeartbeats 400000 in
theorem UpperTheory.mem_range_of_proper_generic_fibre_separated :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω], Function.Injective (algebraMap R Ω) → ∀ {B Y D C : Scheme.{0}} (ι : Sp R ⟶ B) [IsOpenImmersion ι] (π : Y ⟶ B) [IsSeparated π] [IrreducibleSpace Y] (j : D ⟶ Y) [IsOpenImmersion j], Dense (Set.range j) → ∀ (q : D ⟶ Sp R), j ≫ π = q ≫ ι → ∀ (c : C ⟶ Sp Ω) [IsProper c] (v : C ⟶ D), IsPullback v c q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) → ∀ (y : Y), π y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) → y ∈ Set.range j := by
  intro R Ω _ _ _ _ hinj B Y D C ι _ π _ _ j _ hd q hq c _ v hpb y hy
  set g := Spec.map (CommRingCat.ofHom (algebraMap R Ω)) with hg
  let U' : Y.Opens := π ⁻¹ᵁ ι.opensRange
  have hjU : Set.range j ⊆ Set.range U'.ι := by
    rintro _ ⟨d, rfl⟩
    rw [Scheme.Opens.range_ι]
    show π (j d) ∈ ι.opensRange
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let jU : D ⟶ U' := IsOpenImmersion.lift U'.ι j hjU
  have hjUf : jU ≫ U'.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hπU : Set.range (U'.ι ≫ π) ⊆ Set.range ι := by
    rintro _ ⟨z, rfl⟩
    exact z.2
  let w : (U' : Scheme) ⟶ Sp R := IsOpenImmersion.lift ι (U'.ι ≫ π) hπU
  have hw : w ≫ ι = U'.ι ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hjw : jU ≫ w = q := by
    rw [← cancel_mono ι, Category.assoc, hw, ← Category.assoc, hjUf, hq]
  haveI : IsSeparated (w ≫ ι) := by rw [hw]; infer_instance
  haveI : IsSeparated w := IsSeparated.of_comp w ι
  let m : C ⟶ pullback w g := pullback.lift (v ≫ jU) c (by rw [Category.assoc, hjw, hpb.w])
  have hm : m ≫ pullback.snd w g = c := pullback.lift_snd _ _ _
  haveI : UniversallyClosed (m ≫ pullback.snd w g) := by rw [hm]; infer_instance
  haveI : UniversallyClosed m := UniversallyClosed.of_comp_of_isSeparated m (pullback.snd w g)
  have hleft : IsPullback m v (pullback.fst w g) jU := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback w g).flip
    rw [hm, hjw]
    exact hpb.flip
  have hI : hleft.isoPullback.inv ≫ m = pullback.fst (pullback.fst w g) jU :=
    (Iso.inv_comp_eq _).mpr hleft.isoPullback_hom_fst.symm
  have hrange : (pullback.fst w g) ⁻¹' Set.range jU ⊆ Set.range m := by
    intro z hz
    have e := IsOpenImmersion.range_pullbackFst jU (pullback.fst w g)
    have hz' : z ∈ Set.range (pullback.fst (pullback.fst w g) jU) := by
      rw [e]
      exact hz
    obtain ⟨t, rfl⟩ := hz'
    refine ⟨hleft.isoPullback.inv t, ?_⟩
    rw [← Scheme.Hom.comp_apply, hI]
  obtain ⟨p, hp⟩ := hy
  have hyU : y ∈ U' := by
    show π y ∈ ι.opensRange
    rw [← hp, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let yU : U' := ⟨y, hyU⟩
  have e1 : ι (w yU) = π y := by
    show (w ≫ ι) yU = π y
    rw [hw]
    rfl
  have hwy : w yU = g p := by
    apply ι.isOpenEmbedding.injective
    rw [e1, ← hp]
    rfl
  obtain ⟨y', hy'1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := g) yU p hwy
  have hξ : genericPoint Y ∈ Set.range j := by
    rw [(genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range, Set.univ_inter]
    exact hd.nonempty
  obtain ⟨d, hdξ⟩ := hξ
  have hsp : jU d ⤳ yU := by
    apply (U'.ι.isOpenEmbedding.isInducing.specializes_iff).mp
    have e2 : U'.ι (jU d) = genericPoint Y := by
      rw [← Scheme.Hom.comp_apply, hjUf, hdξ]
    rw [e2]
    exact (genericPoint_spec Y).specializes (Set.mem_univ _)
  obtain ⟨x', hx'sp, hx'fst⟩ := UpperTheory.exists_specializes_lift_generic_base_change R Ω hinj w y' (jU d) (by rw [hy'1]; exact hsp)
  have hx'm : x' ∈ Set.range m := hrange ⟨d, hx'fst.symm⟩
  have hy'm : y' ∈ Set.range m := hx'sp.mem_closed m.isClosedMap.isClosed_range hx'm
  obtain ⟨c0, hc0⟩ := hy'm
  refine ⟨v c0, ?_⟩
  have h1 : pullback.fst w g (m c0) = jU (v c0) := by
    rw [← Scheme.Hom.comp_apply, hleft.w, Scheme.Hom.comp_apply]
  rw [← hjUf, Scheme.Hom.comp_apply, ← h1, hc0, hy'1]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SheafConnectedOfLevelwiseConnected
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

section SlopeTestRemainingChoices
variable {R : Type} [CommRing R]

private theorem cpull_comp' {A B C : Cx R} (f : A ⟶ B) (g : B ⟶ C) (I : Cx R) (n : ℤ)
    (x : CohomologyClass C I n) : cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private theorem cpull_id' {A : Cx R} (I : Cx R) (n : ℤ) (x : CohomologyClass A I n) :
    cpull (𝟙 A) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private theorem cpull_homotopy {A B : Cx R} {f g : A ⟶ B} (h : Homotopy f g) (I : Cx R) (n : ℤ)
    (x : CohomologyClass B I n) : cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  rw [cpre_mk, cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • z.comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp z x.1 _ 0 (n + 1) n (by omega) (by omega) rfl]
  simp [zcomp, smul_smul, hz, Cochain.add_comp]

private theorem cpull_bij {A B : Cx R} (e : HomotopyEquiv A B) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp', cpull_homotopy e.homotopyInvHomId, cpull_id']
  · rw [← cpull_comp', cpull_homotopy e.homotopyHomInvId, cpull_id']

private theorem transfer {A B A' B' : Cx R} (g : A ⟶ B) (g' : A' ⟶ B') (a : HomotopyEquiv A A')
    (b : HomotopyEquiv B B') (w : g ≫ b.hom = a.hom ≫ g') (I : Cx R) (n : ℤ) :
    (Function.Bijective (cpull g' I n) → Function.Bijective (cpull g I n)) ∧
      (Function.Injective (cpull g' I n) → Function.Injective (cpull g I n)) := by
  have ha := cpull_bij a I n
  have hb := cpull_bij b I n
  have key : ⇑(cpull g I n) = cpull a.hom I n ∘ cpull g' I n ∘ (Equiv.ofBijective _ hb).symm := by
    funext x
    obtain ⟨y, rfl⟩ := hb.2 x
    have : (Equiv.ofBijective _ hb).symm (cpull b.hom I n y) = y :=
      (Equiv.ofBijective _ hb).symm_apply_apply y
    simp only [Function.comp_apply, this]
    rw [← cpull_comp', ← cpull_comp', w]
  rw [key]
  exact ⟨fun h => ha.comp (h.comp (Equiv.bijective _)),
    fun h => ha.1.comp (h.comp (Equiv.injective _))⟩

private theorem subsingleton_of_isZero {A : Cx R} (h : IsZero A) (I : Cx R) (n : ℤ) :
    Subsingleton (CohomologyClass A I n) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext (Cochain.ext _ _ fun p q hpq => ?_))
  exact ((HomologicalComplex.eval _ _ p).map_isZero h).eq_of_src _ _

private theorem bij_of_isZero {A B : Cx R} (hA : IsZero A) (hB : IsZero B) (g : A ⟶ B) (I : Cx R)
    (n : ℤ) : Function.Bijective (cpull g I n) := by
  have := subsingleton_of_isZero hA I n
  have := subsingleton_of_isZero hB I n
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

private theorem core (R : Type) [CommRing R] (F : Shv R) {E' E : Spc} (p : E' ⟶ E) (m : ℤ)
    (e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)))
    (he : ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) =
      (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom)
    (h : ∀ k : ℕ, UpperTheory.RedSh.Conn (disc.map (p.app (op (SimplexCategory.mk k)))) F (m - k)) :
    UpperTheory.RedSh.Conn p F m := by
  obtain ⟨-, hinj, hge, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic R F
  obtain ⟨hle, hnat, -⟩ := GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R
  have := hle E
  have := hle E'
  refine UpperTheory.cochainPullback_bijective_of_termwise_bijective_injective R (res R F) hinj ((chains R).map p) m fun q => ?_
  rcases lt_or_ge 0 q with hq | hq
  · have hz : ∀ K : Cx R, K.IsStrictlyLE 0 →
        IsZero ((CochainComplex.singleFunctor (Shv R) 0).obj (K.X q)) := fun K _ =>
      (CochainComplex.singleFunctor (Shv R) 0).map_isZero (K.isZero_of_isStrictlyLE 0 q hq)
    exact ⟨fun n _ => bij_of_isZero (hz _ (hle E')) (hz _ (hle E)) _ _ _,
      (bij_of_isZero (hz _ (hle E')) (hz _ (hle E)) _ _ _).1⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = -(k : ℤ) := ⟨(-q).toNat, by omega⟩
    let S := CochainComplex.singleFunctor (Shv R) 0
    let φ := p.app (op (SimplexCategory.mk k))
    let a : HomotopyEquiv (S.obj (((chains R).obj E').X (-(k : ℤ)))) _ :=
      (HomotopyEquiv.ofIso (S.mapIso (chainsXIso R E' k))).trans (e _)
    let b : HomotopyEquiv (S.obj (((chains R).obj E).X (-(k : ℤ)))) _ :=
      (HomotopyEquiv.ofIso (S.mapIso (chainsXIso R E k))).trans (e _)
    have w : S.map (((chains R).map p).f (-(k : ℤ))) ≫ b.hom =
        a.hom ≫ (chains R).map (disc.map φ) := by
      change S.map _ ≫ S.map (chainsXIso R E k).hom ≫ (e _).hom =
        (S.map (chainsXIso R E' k).hom ≫ (e _).hom) ≫ _
      rw [Category.assoc, he, ← Category.assoc, ← S.map_comp, hnat, S.map_comp, Category.assoc]
    have hm : m + -(k : ℤ) = m - k := by ring
    rw [hm]
    refine ⟨fun n hn => (transfer _ _ a b w _ n).1 ((h k).1 n hn),
      (transfer _ _ a b w _ _).2 (h k).2⟩

end SlopeTestRemainingChoices

theorem UpperTheory.sheafConnected_of_levelwise_connected :
    ∀ (R : Type) [CommRing R] (F : Shv R) {E' E : Spc} (p : E' ⟶ E) (m : ℤ), (∀ k : ℕ, UpperTheory.RedSh.Conn (disc.map (p.app (op (SimplexCategory.mk k)))) F (m - k)) → UpperTheory.RedSh.Conn p F m := by
  intro R _ F E' E p m h
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  exact core R F p m e he h
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.StackProductIsPullbackOfActionPullback
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.PbSp

private theorem hom_val {c : Act} {A : CommRingCat.{0}} {J : Type} [SmallCategory J] {F G : J ⥤ Ob c A} (h : F = G)
    {i j : J} (f : i ⟶ j) : (F.map f).1 = (G.map f).1 := by
  subst h
  rfl

private theorem law_id {P a : Act} (φ : Act.Hom P a) {A : CommRingCat.{0}} {J : Type} [SmallCategory J] (x : J ⥤ Ob a A)
    (j : J) : φ.g.app A 1 = (x.map (𝟙 j)).1 := by
  rw [x.map_id]
  exact map_one _

private theorem law_comp {P a : Act} (φ : Act.Hom P a) {A : CommRingCat.{0}} {J : Type} [SmallCategory J] (x : J ⥤ Ob a A)
    {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (p q : P.G.obj A) (hp : φ.g.app A p = (x.map f).1)
    (hq : φ.g.app A q = (x.map g).1) : φ.g.app A (p * q) = (x.map (f ≫ g)).1 := by
  rw [x.map_comp]
  change _ = (x.map f).1 * (x.map g).1
  rw [map_mul, hp, hq]

private theorem fn_square {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c)
    (A : CommRingCat.{0})
    (h1 : ∀ z : P.D.obj A, r.d.app A (t.d.app A z) = u.d.app A (l.d.app A z))
    (h2 : ∀ z : P.G.obj A, r.g.app A (t.g.app A z) = u.g.app A (l.g.app A z)) :
    t.fn A ⋙ r.fn A = l.fn A ⋙ u.fn A := by
  have ho : ∀ z : Ob P A, (t.fn A ⋙ r.fn A).obj z = (l.fn A ⋙ u.fn A).obj z :=
    fun z => congrArg Ob.mk (h1 z.pt)
  refine Functor.hext ho (fun z w f => ?_)
  exact Ob.hom_heq (ho z) (ho w) _ _ (h2 f.1)

private theorem lift_chain {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c)
    (A : CommRingCat.{0})
    (h3 : ∀ (x : a.D.obj A) (y : b.D.obj A), r.d.app A x = u.d.app A y → ∃! z : P.D.obj A, t.d.app A z = x ∧ l.d.app A z = y)
    (h4 : ∀ (g : a.G.obj A) (h : b.G.obj A), r.g.app A g = u.g.app A h → ∃! z : P.G.obj A, t.g.app A z = g ∧ l.g.app A z = h)
    {J : Type} [SmallCategory J] (x : J ⥤ Ob a A) (y : J ⥤ Ob b A) (h : x ⋙ r.fn A = y ⋙ u.fn A) :
    ∃! z : J ⥤ Ob P A, z ⋙ t.fn A = x ∧ z ⋙ l.fn A = y := by
  have hobj : ∀ j, r.d.app A (x.obj j).pt = u.d.app A (y.obj j).pt :=
    fun j => congrArg (fun F : J ⥤ Ob c A => (F.obj j).pt) h
  have hmap : ∀ (i j : J) (f : i ⟶ j), r.g.app A (x.map f).1 = u.g.app A (y.map f).1 :=
    fun i j f => hom_val h f
  choose zo hzo hzu using fun j => h3 (x.obj j).pt (y.obj j).pt (hobj j)
  choose zg hzg hzgu using fun (i j : J) (f : i ⟶ j) => h4 (x.map f).1 (y.map f).1 (hmap i j f)
  let F : J ⥤ Ob P A :=
    { obj := fun j => Ob.mk (zo j)
      map := fun {i j} f => ⟨zg i j f, by
        refine (hzu i _ ⟨?_, ?_⟩).symm
        · change t.d.app A (P.smul A (zg i j f) (zo j)) = _
          rw [t.eq, (hzg i j f).1, (hzo j).1]
          exact (x.map f).2.symm
        · change l.d.app A (P.smul A (zg i j f) (zo j)) = _
          rw [l.eq, (hzg i j f).2, (hzo j).2]
          exact (y.map f).2.symm⟩
      map_id := fun j => by
        apply Subtype.ext
        exact (hzgu j j (𝟙 j) 1 ⟨law_id t x j, law_id l y j⟩).symm
      map_comp := fun {i j k} f g => by
        apply Subtype.ext
        exact (hzgu i k (f ≫ g) (zg i j f * zg j k g)
          ⟨law_comp t x f g _ _ (hzg i j f).1 (hzg j k g).1,
            law_comp l y f g _ _ (hzg i j f).2 (hzg j k g).2⟩).symm }
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · have ho : ∀ j, (F ⋙ t.fn A).obj j = x.obj j := fun j => congrArg Ob.mk (hzo j).1
    exact Functor.hext ho (fun i j f => Ob.hom_heq (ho i) (ho j) _ _ (hzg i j f).1)
  · have ho : ∀ j, (F ⋙ l.fn A).obj j = y.obj j := fun j => congrArg Ob.mk (hzo j).2
    exact Functor.hext ho (fun i j f => Ob.hom_heq (ho i) (ho j) _ _ (hzg i j f).2)
  · rintro w ⟨hw1, hw2⟩
    have ho : ∀ j, w.obj j = F.obj j := fun j =>
      congrArg Ob.mk (hzu j (w.obj j).pt
        ⟨congrArg (fun G : J ⥤ Ob a A => (G.obj j).pt) hw1,
          congrArg (fun G : J ⥤ Ob b A => (G.obj j).pt) hw2⟩)
    exact Functor.hext ho (fun i j f =>
      Ob.hom_heq (ho i) (ho j) _ _ (hzgu i j f (w.map f).1 ⟨hom_val hw1 f, hom_val hw2 f⟩))

private abbrev Ch (a : Act) (k : ℕ) (T : Scheme.{0}) : Type := Fin (k + 1) ⥤ Ob a (Scheme.Γ.obj (op T))

private def pr1 {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (s : Sx (Sp E a) k T) : Sx E k T :=
  Prod.fst (α := Sx E k T) (β := Ch a k T) s

private def pr2 {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (s : Sx (Sp E a) k T) : Ch a k T :=
  Prod.snd (α := Sx E k T) (β := Ch a k T) s

private def mkS {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (e : Sx E k T) (x : Ch a k T) : Sx (Sp E a) k T :=
  Prod.mk (α := Sx E k T) (β := Ch a k T) e x

end UpperTheory.PbSp

open UpperTheory.PbSp in
theorem UpperTheory.stackProduct_isPullback_of_actionPullback :
    ∀ (E : Spc) {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c),
        (∀ A (z : P.D.obj A), r.d.app A (t.d.app A z) = u.d.app A (l.d.app A z)) →
        (∀ A (z : P.G.obj A), r.g.app A (t.g.app A z) = u.g.app A (l.g.app A z)) →
        (∀ A (x : a.D.obj A) (y : b.D.obj A), r.d.app A x = u.d.app A y → ∃! z : P.D.obj A, t.d.app A z = x ∧ l.d.app A z = y) →
        (∀ A (g : a.G.obj A) (h : b.G.obj A), r.g.app A g = u.g.app A h → ∃! z : P.G.obj A, t.g.app A z = g ∧ l.g.app A z = h) →
        IsPullback (Sp.map E t) (Sp.map E l) (Sp.map E r) (Sp.map E u) := by
  intro E P a b c t l r u h1 h2 h3 h4
  have hsq : ∀ A, t.fn A ⋙ r.fn A = l.fn A ⋙ u.fn A := fun A => fn_square t l r u A (h1 A) (h2 A)
  apply isPullback_of_unique_simplices_pullback
  · ext k T s
    refine Prod.ext rfl ?_
    exact congrArg (fun F => s.2 ⋙ F) (hsq _)
  · intro k T x y hxy
    have e1 : pr1 x = pr1 y := congrArg pr1 hxy
    have e2 : pr2 x ⋙ r.fn _ = pr2 y ⋙ u.fn _ := congrArg pr2 hxy
    obtain ⟨z, ⟨hz1, hz2⟩, hzu⟩ := lift_chain t l r u _ (h3 _) (h4 _) (pr2 x) (pr2 y) e2
    refine ⟨mkS (pr1 x) z, ⟨?_, ?_⟩, ?_⟩
    · change mkS (pr1 x) (z ⋙ t.fn _) = x
      rw [hz1]
      rfl
    · change mkS (pr1 x) (z ⋙ l.fn _) = y
      rw [hz2, e1]
      rfl
    · rintro w ⟨hw1, hw2⟩
      have f1 : pr1 w = pr1 x := congrArg pr1 hw1
      have f2 : pr2 w = z := hzu _ ⟨congrArg pr2 hw1, congrArg pr2 hw2⟩
      change mkS (pr1 w) (pr2 w) = mkS (pr1 x) z
      rw [f1, f2]
end

