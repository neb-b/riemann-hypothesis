module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartProjectionMatrixMapMulVecOfEigenvector
section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

section Scal

variable {B K : Type} [CommRing B] [CommRing K] {n : ℕ} (g : B →+* K) (v : Fin n → K)

theorem algebraMap_map_mulVec (x : B) :
    (algebraMap B (Matrix (Fin n) (Fin n) B) x).map g *ᵥ v = g x • v := by
  ext k
  simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

theorem map_mul_mulVec_of_scal {X Y : Matrix (Fin n) (Fin n) B} {c d : K}
    (hX : X.map g *ᵥ v = c • v) (hY : Y.map g *ᵥ v = d • v) : (X * Y).map g *ᵥ v = (c * d) • v := by
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hY, Matrix.mulVec_smul, hX, smul_smul, mul_comm]

theorem map_sub_mulVec_of_scal {X Y : Matrix (Fin n) (Fin n) B} {c d : K}
    (hX : X.map g *ᵥ v = c • v) (hY : Y.map g *ᵥ v = d • v) : (X - Y).map g *ᵥ v = (c - d) • v := by
  rw [Matrix.map_sub _ (map_sub g), Matrix.sub_mulVec, hX, hY, sub_smul]

theorem map_sum_mulVec_of_scal {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin n) (Fin n) B) (c : ι → K)
    (h : ∀ x ∈ s, (X x).map g *ᵥ v = c x • v) : (∑ x ∈ s, X x).map g *ᵥ v = (∑ x ∈ s, c x) • v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.map_add _ (map_add g), Matrix.add_mulVec,
      h a (Finset.mem_insert_self _ _), ih (fun x hx => h x (Finset.mem_insert_of_mem hx)), add_smul]

theorem map_list_prod_mulVec_of_fix (L : List (Matrix (Fin n) (Fin n) B))
    (h : ∀ X ∈ L, X.map g *ᵥ v = v) : L.prod.map g *ᵥ v = v := by
  induction L with
  | nil => rw [List.prod_nil, Matrix.map_one _ (map_zero g) (map_one g), Matrix.one_mulVec]
  | cons X L ih =>
    rw [List.prod_cons, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      ih (fun Y hY => h Y (List.mem_cons_of_mem _ hY)), h X (by simp)]

end Scal

theorem projMat_map_mulVec_of_eig : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K)
    (i : Fin D.a) (v : Fin n → K), (∀ c : 𝓞 D.F, (M c).map g *ᵥ v = g (βB (b.t i c)) • v) →
      (projMat b βB M i).map g *ᵥ v = v := by
  intro p _ D R _ b B _ βB n M K _ g i v hv
  have hα : ∀ j, j ≠ i → (alphaMat b βB M i j).map g *ᵥ v = v := by
    intro j hj
    have hij : i ≠ j := fun h => hj h.symm
    unfold alphaMat
    rw [Finsupp.sum, map_sum_mulVec_of_scal g v _ _
      (fun x => g (βB (comaxC b i j x)) * (g (βB (b.t i x)) - g (βB (b.t j x))))
      (fun x _ => map_mul_mulVec_of_scal g v (algebraMap_map_mulVec g v _)
        (map_sub_mulVec_of_scal g v (hv x) (algebraMap_map_mulVec g v _)))]
    have hs := congrArg (fun y => g (βB y)) (comaxC_spec b hij)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.sum, map_sum, map_mul, map_sub, map_one] at hs
    rw [hs, one_smul]
  have hlast := map_mul_mulVec_of_scal g v (algebraMap_map_mulVec g v (βB (uInv b)))
    (map_sub_mulVec_of_scal g v (hv D.ω) (algebraMap_map_mulVec g v (βB ((D.tr : R) - b.ρ))))
  have h1 : g (βB (uInv b)) * (g (βB (b.t i D.ω)) - g (βB ((D.tr : R) - b.ρ))) = 1 := by
    have hu := congrArg (fun y => g (βB y)) (uInv_mul b)
    simp only [map_mul, map_sub, map_one, map_intCast, map_ofNat] at hu ⊢
    rw [b.t_ω]
    linear_combination hu
  rw [h1, one_smul] at hlast
  unfold projMat
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hlast]
  refine map_list_prod_mulVec_of_fix g v _ ?_
  intro X hX
  rw [List.mem_ofFn] at hX
  obtain ⟨j, rfl⟩ := hX
  split_ifs with h
  · rw [Matrix.map_one _ (map_zero g) (map_one g), Matrix.one_mulVec]
  · exact hα j h

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem eqv_basic : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E E' : Spc) (f : E ⟶ E'), IsIso f → Eqv R f F) ∧ (∀ (E E' E'' : Spc) (f : E ⟶ E') (g : E' ⟶ E''), (Eqv R f F → Eqv R g F → Eqv R (f ≫ g) F) ∧ (Eqv R f F → Eqv R (f ≫ g) F → Eqv R g F) ∧ (Eqv R g F → Eqv R (f ≫ g) F → Eqv R f F)) ∧ (∀ (E E' : Spc) (f : E ⟶ E'), QuasiIso ((chains R).map f) → Eqv R f F) ∧ ∀ (E E' : Spc) (f : E ⟶ E'), Eqv R f F → (AcycF R E F ↔ AcycF R E' F) := by
  intro R _ F
  have hc : ∀ {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n : ℤ),
      ⇑(pull R (f ≫ g) F n) = ⇑(pull R f F n) ∘ ⇑(pull R g F n) := by
    intro E E' E'' f g n
    funext x
    exact pull_comp R f g F n x
  have hid : ∀ (E : Spc) (n : ℤ), ⇑(pull R (𝟙 E) F n) = id := by
    intro E n
    funext x
    exact pull_id R E F n x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' f hf n
    haveI := hf
    have h1 : Function.LeftInverse (pull R (inv f) F n) (pull R f F n) := by
      intro x
      have := congrFun (hc (inv f) f n) x
      rw [IsIso.inv_hom_id, hid] at this
      exact this.symm
    have h2 : Function.RightInverse (pull R (inv f) F n) (pull R f F n) := by
      intro x
      have := congrFun (hc f (inv f) n) x
      rw [IsIso.hom_inv_id, hid] at this
      exact this.symm
    exact ⟨h1.injective, h2.surjective⟩
  · intro E E' E'' f g
    refine ⟨?_, ?_, ?_⟩
    · intro hf hg n
      rw [hc]
      exact (hf n).comp (hg n)
    · intro hf hfg n
      have := hfg n
      rw [hc] at this
      exact (Function.Bijective.of_comp_iff' (hf n) _).mp this
    · intro hg hfg n
      have := hfg n
      rw [hc] at this
      exact (Function.Bijective.of_comp_iff _ (hg n)).mp this
  · intro E E' f hq n
    exact GlobalTheory.T.quasiIso_hypercohomology_bijective R ((chains R).map f) F n
  · intro E E' f hf
    constructor
    · intro h n hn
      haveI := h n hn
      exact (hf n).1.subsingleton
    · intro h n hn
      haveI := h n hn
      exact (Equiv.ofBijective _ (hf n)).symm.subsingleton

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeSequenceExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.MVExact
open GlobalTheory.EtC.FreeMonoEpi

variable {R : Type} [CommRing R]

theorem sec_map_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem sec_map_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (-φ) x = -Sec.map φ x := rfl

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_biprod_ext {M N : Shv R} {U : Scheme.{0}} (x y : Sec (M ⊞ N) U)
    (h1 : Sec.map biprod.fst x = Sec.map biprod.fst y) (h2 : Sec.map biprod.snd x = Sec.map biprod.snd y) : x = y := by
  have e : ∀ z : Sec (M ⊞ N) U, z = Sec.map (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) z := fun z => by
    rw [biprod.total]; rfl
  rw [e x, e y, sec_map_add, sec_map_add, sec_map_comp, sec_map_comp, sec_map_comp, sec_map_comp, h1, h2]

theorem gsum_add (P : PSh) (V : Scheme.{0}) (a b : P.obj (op V) →₀ ULift.{1} R) :
    gsum R P V (a + b) = gsum R P V a + gsum R P V b :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem gsum_neg (P : PSh) (V : Scheme.{0}) (a : P.obj (op V) →₀ ULift.{1} R) :
    gsum R P V (-a) = -gsum R P V a := by
  rw [gsum, Finsupp.sum_neg_index (h := fun x r => r • freeGen R P V x) (fun _ => zero_smul _ _)]
  simp only [neg_smul]
  rw [Finsupp.sum, Finset.sum_neg_distrib]; rfl

theorem md_comp {M : Type 1} [AddCommMonoid M] (X : Scheme.{0}) {W' W V : Scheme.{0}} (k'' : W' ⟶ W) (k' : W ⟶ V)
    (c : (V ⟶ X) →₀ M) :
    Finsupp.mapDomain (fun x : W ⟶ X => k'' ≫ x) (Finsupp.mapDomain ((yoneda.obj X).map k'.op) c) =
      Finsupp.mapDomain ((yoneda.obj X).map (k'' ≫ k').op) c := by
  rw [← Finsupp.mapDomain_comp]
  congr 1

theorem exact_abstract (R : Type) [CommRing R] {X₁ X₂ X₃ X₄ : Scheme.{0}} (u : X₁ ⟶ X₂) (v : X₁ ⟶ X₃) (c : X₂ ⟶ X₄)
    (d : X₃ ⟶ X₄) (G : ∀ V : Scheme.{0}, (V ⟶ X₄) → Prop) (hsq : u ≫ c = v ≫ d) [Mono c]
    (hc : ∀ V (x : V ⟶ X₂), G V (x ≫ c)) (hd : ∀ V (y : V ⟶ X₃), G V (y ≫ d) → ∃ x, x ≫ v = y)
    (hp : ∀ T (y y' : T ⟶ X₃), y ≫ d = y' ≫ d → Loc T fun V k => k ≫ y = k ≫ y' ∨ G V (k ≫ y ≫ d))
    (w : biprod.lift ((free R).map (yoneda.map u)) (-(free R).map (yoneda.map v)) ≫
      biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) = 0) :
    (ShortComplex.mk _ _ w).Exact := by
  classical
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro T b hb
  have h2 := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₂) T).1 (Sec.map biprod.fst b)
  have h3 := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₃) T).1 (Sec.map biprod.snd b)
  apply FreeMonoEpi.loc_trans
  refine FreeMonoEpi.loc_mono (GlobalTheory.EtC.loc_and T _ _ h2 h3) ?_
  rintro V k ⟨⟨c2, hc2⟩, ⟨c3, hc3⟩⟩
  change Sec.res k (Sec.map biprod.fst b) = gsum R _ V c2 at hc2
  change Sec.res k (Sec.map biprod.snd b) = gsum R _ V c3 at hc3
  have key : gsum R (yoneda.obj X₄) V (Finsupp.mapDomain ((yoneda.map c).app (op V)) c2 +
      Finsupp.mapDomain ((yoneda.map d).app (op V)) c3) = 0 := by
    have e0 : Sec.res k (Sec.map (biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d))) b) = 0 := by
      have : Sec.map (biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d))) b = 0 := hb
      rw [this]; exact map_zero _
    rw [gsum_add, ← map_gsum, ← map_gsum, ← hc2, ← hc3, ← map_res, ← map_res, ← sec_map_comp, ← sec_map_comp,
      ← sec_map_add, ← biprod.desc_eq, map_res, e0]
  apply FreeMonoEpi.loc_trans
  refine FreeMonoEpi.loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₄) V).2 _ key) ?_
  intro W k' hk'
  set c2' := Finsupp.mapDomain ((yoneda.obj X₂).map k'.op) c2 with hc2'
  set c3' := Finsupp.mapDomain ((yoneda.obj X₃).map k'.op) c3 with hc3'
  have rel : Finsupp.mapDomain (fun x : W ⟶ X₂ => x ≫ c) c2' + Finsupp.mapDomain (fun y : W ⟶ X₃ => y ≫ d) c3' = 0 := by
    rw [← hk', Finsupp.mapDomain_add, hc2', hc3', ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp,
      ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 2 <;> (funext x; simp)
  have hl : Loc W fun W' k'' => ∀ i : c3'.support × c3'.support, i.1.1 ≫ d = i.2.1 ≫ d →
      k'' ≫ i.1.1 = k'' ≫ i.2.1 ∨ G W' (k'' ≫ i.1.1 ≫ d) :=
    FreeMonoEpi.loc_fin _ fun i => by
      by_cases h : i.1.1 ≫ d = i.2.1 ≫ d
      · exact FreeMonoEpi.loc_mono (hp W _ _ h) fun _ _ e _ => e
      · exact FreeMonoEpi.loc_all fun _ _ e => absurd e h
  refine FreeMonoEpi.loc_mono hl ?_
  intro W' k'' hk''
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.mapDomain_relation_lift_commuting_square (ULift.{1} R) (W ⟶ X₂) (W ⟶ X₃) (W ⟶ X₄) (W' ⟶ X₁) (W' ⟶ X₂) (W' ⟶ X₃) (W' ⟶ X₄)
    (· ≫ c) (· ≫ d) (· ≫ u) (· ≫ v) (· ≫ c) (· ≫ d) (k'' ≫ ·) (k'' ≫ ·) (k'' ≫ ·) (G W')
    (fun x => by simp) (fun y => by simp) (fun x => by simp [hsq]) (fun x y h => (cancel_mono c).1 h) (hc W') (hd W')
    c2' c3' rel (fun y hy y' hy' h => by
      rcases hk'' (⟨y, hy⟩, ⟨y', hy'⟩) h with e | e
      · exact Or.inl e
      · exact Or.inr (by simpa using e))
  refine ⟨gsum R (yoneda.obj X₁) W' a, ?_⟩
  apply sec_biprod_ext
  · rw [← sec_map_comp, biprod.lift_fst, map_gsum, map_res, res_comp, hc2, res_gsum']
    congr 1
    change Finsupp.mapDomain (fun x : W' ⟶ X₁ => x ≫ u) a = _
    rw [ha1, hc2', md_comp]
  · rw [← sec_map_comp, biprod.lift_snd, sec_map_neg, map_gsum, map_res, res_comp, hc3, res_gsum']
    have ha2' : Finsupp.mapDomain ((yoneda.map v).app (op W')) a =
        -Finsupp.mapDomain ((yoneda.obj X₃).map (k'' ≫ k').op) c3 := by
      refine ha2.trans ?_
      rw [hc3', md_comp]
    rw [ha2', gsum_neg, neg_neg]

theorem rho_comp {B C : CommRingCat.{0}} (h : B ⟶ C) {V : Scheme.{0}} (y : V ⟶ Spec C) :
    (Scheme.ΓSpecIso B).inv ≫ (y ≫ Spec.map h).appTop = h ≫ (Scheme.ΓSpecIso C).inv ≫ y.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

theorem rho_toSpec {B : CommRingCat.{0}} {V : Scheme.{0}} (φ : B ⟶ Γ(V, ⊤)) :
    (Scheme.ΓSpecIso B).inv ≫ (V.toSpecΓ ≫ Spec.map φ).appTop = φ := by
  rw [rho_comp, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

theorem eq_toSpec {B : Type} [CommRing B] {V : Scheme.{0}} (y : V ⟶ Spec (CommRingCat.of B)) :
    y = V.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ y.appTop) :=
  ext_to_Spec (by simp only [Scheme.Γ_map_op]; exact (rho_toSpec _).symm)

theorem unit_of_away {B : Type} [CommRing B] (g : B) {V : Scheme.{0}}
    (x : V ⟶ Spec (CommRingCat.of (Localization.Away g))) :
    IsUnit (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (x ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))).appTop).hom g) := by
  rw [rho_comp, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit g).map _

theorem lift_away {B : Type} [CommRing B] (g : B) {V : Scheme.{0}} (y : V ⟶ Spec (CommRingCat.of B))
    (hy : IsUnit (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ y.appTop).hom g)) :
    ∃ x : V ⟶ Spec (CommRingCat.of (Localization.Away g)),
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) = y := by
  let ψ := IsLocalization.Away.lift (S := Localization.Away g) g hy
  refine ⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ : CommRingCat.of _ ⟶ Γ(V, ⊤)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, eq_toSpec y]
  congr 2
  ext b
  simp [ψ]

theorem mv_exact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∃ w, (ShortComplex.mk (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) w).Exact := by
  intro R _ A A' _ _ _ _ f h1 h2
  obtain ⟨e, u, he, hu⟩ := GlobalTheory.T.etale_tensor_diagonal_complement_over_basicOpen A A' f h1 h2
  have hsq : Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) =
      Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A A')) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫ biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, hsq, add_neg_cancel]
  refine ⟨w, exact_abstract R _ _ _ _
    (fun V z => IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ z.appTop).hom f)) hsq
    (fun V x => unit_of_away f x) (fun V y hy => ?_) (fun T y y' h => GlobalTheory.T.locally_equal_or_unit A A' f e u he hu T y y' h) w⟩
  rw [rho_comp, CommRingCat.hom_comp, RingHom.comp_apply] at hy
  exact lift_away (algebraMap A A' f) y hy

end GlobalTheory.EtC.MVExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitary
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency false in
theorem finite_etale_family {A : CommRingCat.{0}} (P : ∀ B : CommRingCat.{0}, (A ⟶ B) → Prop)
    (h : ∀ p : Spec A, ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (v : Spec B), g.hom.Etale ∧ Spec.map g v = p ∧ P B g) :
    ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i),
      (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, P (B i) (g i) := by
  choose B g v he hv hP using h
  have ho : ∀ p, IsOpen (Set.range (Spec.map (g p))) := fun p => by
    have : Etale (Spec.map (g p)) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 (he p)
    exact (Spec.map (g p)).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun p => Set.range (Spec.map (g p))) ho
    (fun p _ => Set.mem_iUnion.2 ⟨p, v p, hv p⟩)
  refine ⟨s, inferInstance, fun i => B i, fun i => g i, fun i => he i, fun p => ?_, fun i => hP i⟩
  obtain ⟨i, hi, w, hw⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ p))
  exact ⟨⟨i, hi⟩, w, hw⟩


set_option backward.isDefEq.respectTransparency false in
noncomputable def ofRingsUnit (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) :
    M ⟶ onRings (ofRings R M) where
  app A := M.map (Scheme.ΓSpecIso A).inv ≫ (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op (Spec A))
  naturality A B f := by
    have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality (Spec.map f).op
    rw [← Category.assoc, ← M.map_comp, Scheme.ΓSpecIso_inv_naturality, M.map_comp, Category.assoc, Category.assoc]
    congr 1


set_option backward.isDefEq.respectTransparency false in
theorem etale_affine_ring {A : CommRingCat.{0}} {V : Scheme.{0}} [IsAffine V] (j : V ⟶ Spec A) [Etale j] (v : V) :
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (k : Spec B ⟶ V) (w : Spec B), g.hom.Etale ∧ Spec.map g = k ≫ j ∧ k w = v := by
  refine ⟨Γ(V, ⊤), Spec.preimage (V.isoSpec.inv ≫ j), V.isoSpec.inv, V.isoSpec.hom v, ?_, Spec.map_preimage _, ?_⟩
  · refine (HasRingHomProperty.Spec_iff (P := @Etale)).1 ?_
    rw [Spec.map_preimage]
    infer_instance
  · rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem ofRings_finitary : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), PreservesFilteredColimitsOfSize.{0, 0} M → Finitary (ofRings R M) := by
  intro R _ M hM
  refine GlobalTheory.T.finitary_of_locally_bijective_from_filtered_functor R M (ofRings R M) (ofRingsUnit R M) hM (fun A x => ?_) (fun A m hm => ?_)
  · obtain ⟨ι, hι, B, g, he, hc, hP⟩ := finite_etale_family (A := A)
      (fun B g => ∃ m : M.obj B, ((ofRingsUnit R M).app B).hom m = ((onRings (ofRings R M)).map g).hom x) (fun p => by
        obtain ⟨V, j, v, m, hV, hj, hv, hm⟩ := (ofRings_loc R M (Spec A)).1 x p
        obtain ⟨B, g, k, w, hg, hk, hw⟩ := etale_affine_ring j v
        refine ⟨B, g, w, hg, by rw [hk, Scheme.Hom.comp_apply, hw, hv],
          (M.map (k.appTop ≫ (Scheme.ΓSpecIso B).hom)).hom m, ?_⟩
        have h1 : (M.map (Scheme.ΓSpecIso B).inv).hom ((M.map (k.appTop ≫ (Scheme.ΓSpecIso B).hom)).hom m) =
            (M.map k.appTop).hom m := by
          rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← M.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        change ofRings.sec M (Spec B) ((M.map (Scheme.ΓSpecIso B).inv).hom _) = Sec.res (F := ofRings R M) (Spec.map g) x
        rw [h1, ← (ofRings_loc R M V).2.2 _ k m, hm, hk]
        simp [Sec.res])
    choose m hm using hP
    exact ⟨ι, hι, B, g, m, he, hc, hm⟩
  · refine finite_etale_family (A := A) (fun B g => (M.map g).hom m = 0) (fun p => ?_)
    obtain ⟨V, j, v, hV, hj, hv, h0⟩ := (ofRings_loc R M (Spec A)).2.1 ((M.map (Scheme.ΓSpecIso A).inv).hom m) hm p
    obtain ⟨B, g, k, w, hg, hk, hw⟩ := etale_affine_ring j v
    refine ⟨B, g, w, hg, by rw [hk, Scheme.Hom.comp_apply, hw, hv], ?_⟩
    have h1 : g = (Scheme.ΓSpecIso A).inv ≫ j.appTop ≫ k.appTop ≫ (Scheme.ΓSpecIso B).hom := by
      rw [← Category.assoc j.appTop, ← Scheme.Hom.comp_appTop, ← hk, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rw [h1, M.map_comp, M.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, h0, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (P : PSh) (g : disc.obj P ⟶ E), IsIso (g.app (op ⦋0⦌)) →
  ∀ (n : ℕ) (x : H R E F n), pull R g F n x = 0 →
  (∀ p : ℕ, p + 1 ≤ n → RowExact R E F ((n : ℤ) - ((p + 1 : ℕ) : ℤ)) p) → x = 0 := by
  first | (exact @GlobalTheory.EtC.vanish_of_rowExact) | (exact GlobalTheory.EtC.vanish_of_rowExact) | (intros; apply GlobalTheory.EtC.vanish_of_rowExact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocyclesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ cl : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 → H R (disc.obj P) F n, (∀ P n x, ∃ t ht, cl P n t ht = x) ∧ (∀ P n t ht t' ht', cl P n t ht = cl P n t' ht' ↔ ∃ y : (free R).obj P ⟶ (res R F).X (n - 1), t = t' + y ≫ (res R F).d (n - 1) n) ∧ (∀ P n, cl P n 0 zero_comp = 0) ∧ ∀ (P P' : PSh) (f : P ⟶ P') n t ht, ∃ h, pull R (disc.map f) F n (cl P' n t ht) = cl P n ((free R).map f ≫ t) h := by
  first | (exact @GlobalTheory.EtC.disc_elt_cls) | (exact GlobalTheory.EtC.disc_elt_cls) | (intros; apply GlobalTheory.EtC.disc_elt_cls <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyStalkLocalClassesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_stalk_local_classes : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (Θ Θ' : Over S ⥤ Spc) (α : Θ ⟶ Θ'), (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((Θ).mapCone c)) → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((Θ').mapCone c)) → ∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (α.app (Over.mk s)) F → ∀ (U : Over S), Etale U.hom → ∀ (g : Over.mk s ⟶ U) (n : ℤ), (∀ x : H R (Θ.obj U) F n, ∃ (V : Over S) (g' : Over.mk s ⟶ V) (h : V ⟶ U) (y : H R (Θ'.obj V) F n), Etale V.hom ∧ g' ≫ h = g ∧ pull R (α.app V) F n y = pull R (Θ.map h) F n x) ∧ ∀ y : H R (Θ'.obj U) F n, pull R (α.app U) F n y = 0 → ∃ (V : Over S) (g' : Over.mk s ⟶ V) (h : V ⟶ U), Etale V.hom ∧ g' ≫ h = g ∧ pull R (Θ'.map h) F n y = 0 := by
  first | (exact @GlobalTheory.EtC.stalk_local_classes) | (exact GlobalTheory.EtC.stalk_local_classes) | (intros; apply GlobalTheory.EtC.stalk_local_classes  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceDescentLocalEquivalence
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.Descent

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  intro R _ F T _ Cov _ Φ Φ' α hRef hS hI U
  obtain ⟨hneg, cl, hcl_surj, hcl_eq, hcl_zero, hpull⟩ := _root_.GlobalTheory.EtC.HCElements.main R F
  have key := GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent T Cov (Φ' ⋙ HC R F) (Φ ⋙ HC R F) (Functor.whiskerRight α (HC R F)) ?_ ?_ ?_ ?_ U
  · exact (GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise R F _ _ (α.app U).unop).2 key
  · exact ⟨0, fun n hn V => ⟨hneg _ n hn, hneg _ n hn⟩⟩
  · intro U' V' g hg
    obtain ⟨X, a, h, hga, h1, h2⟩ := hRef U' V' g hg
    exact ⟨X, a, h, hga, fun n => ⟨GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ' U' X a h2 n, GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ U' X a h1 n⟩⟩
  · intro n U' z hz
    obtain ⟨V, g, hg, y, hy⟩ := hS U' n (cl (Φ.obj U').unop n z hz)
    obtain ⟨c, hc, rfl⟩ := hcl_surj (Φ'.obj V).unop n y
    obtain ⟨h1, e1⟩ := hpull _ _ (α.app V).unop n c hc
    obtain ⟨h2, e2⟩ := hpull _ _ (Φ.map g).unop n z hz
    rw [e1, e2, hcl_eq] at hy
    obtain ⟨y', hy'⟩ := hy
    exact ⟨V, g, hg, c, y', hc, hy'⟩
  · intro n U' c hc ⟨y, hy⟩
    have h0 : pull R (α.app U').unop F n (cl (Φ'.obj U').unop n c hc) = 0 := by
      obtain ⟨h1, e1⟩ := hpull _ _ (α.app U').unop n c hc
      rw [e1, hcl_zero]
      exact ⟨y, hy⟩
    obtain ⟨V, g, hg, hV⟩ := hI U' n _ h0
    obtain ⟨h2, e2⟩ := hpull _ _ (Φ'.map g).unop n c hc
    rw [e2, hcl_zero] at hV
    obtain ⟨b, hb⟩ := hV
    exact ⟨V, g, hg, b, hb.symm⟩

end GlobalTheory.EtC.Descent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNeStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_pair_eq_on_subfield_ne_of_not_mem_range : ∀ (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] [CharZero L] (a : Ω), a ∉ Set.range (algebraMap L Ω) → ∃ (F : Type) (_ : Field F) (i₁ i₂ : Ω →+* F), i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ a ≠ i₂ a := by
  first | exact @GlobalTheory.exists_embeddings_agree_on_subfield_ne | exact GlobalTheory.exists_embeddings_agree_on_subfield_ne | (intros; apply GlobalTheory.exists_embeddings_agree_on_subfield_ne <;> assumption)
end

