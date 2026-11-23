module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpHqBij
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.Mod

private theorem pullHl_bijective (l : ℕ) [Fact l.Prime] {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (h : ∀ k : ℕ, Function.Bijective (pull _ f (tw (l ^ k) i) n)) :
    Function.Bijective (pullHl l f n i) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext k
    apply (h k).1
    exact congrFun (congrArg Subtype.val hxy) k
  · intro y
    choose g hg using fun k => (h k).2 (y.1 k)
    refine ⟨⟨g, fun k => (h k).1 ?_⟩, Subtype.ext (funext hg)⟩
    refine (pull_red _ _ f n i (g (k + 1))).trans ?_
    refine (congrArg _ (hg (k + 1))).trans ?_
    exact (y.2 k).trans (hg k).symm

theorem spHqBij : ∀ (l : ℕ) [Fact l.Prime] {E E' : Spc} (f : E ⟶ E') (n i : ℤ),
    (∀ k : ℕ, Function.Bijective (pull _ f (tw (l ^ k) i) n)) →
      Function.Bijective (pullHQ l f n i) := by
  intro l _ E E' f n i h
  let e := LinearEquiv.ofBijective (pullHl l f n i) (pullHl_bijective l f n i h)
  have h1 : (pullHl l f n i) ∘ₗ (e.symm : Hl l E n i →ₗ[ℤ_[l]] Hl l E' n i) = LinearMap.id :=
    LinearMap.ext fun x => e.apply_symm_apply x
  have h2 : (e.symm : Hl l E n i →ₗ[ℤ_[l]] Hl l E' n i) ∘ₗ (pullHl l f n i) = LinearMap.id :=
    LinearMap.ext fun x => e.symm_apply_apply x
  have k1 : (pullHQ l f n i) ∘ₗ ((e.symm : Hl l E n i →ₗ[ℤ_[l]] Hl l E' n i).baseChange ℚ_[l]) = LinearMap.id := by
    unfold pullHQ
    rw [← LinearMap.baseChange_comp, h1, LinearMap.baseChange_id]
  have k2 : ((e.symm : Hl l E n i →ₗ[ℤ_[l]] Hl l E' n i).baseChange ℚ_[l]) ∘ₗ (pullHQ l f n i) = LinearMap.id := by
    unfold pullHQ
    rw [← LinearMap.baseChange_comp, h2, LinearMap.baseChange_id]
  exact Function.bijective_iff_has_inverse.mpr
    ⟨_, fun x => LinearMap.congr_fun k2 x, fun x => LinearMap.congr_fun k1 x⟩

end UpperTheory.Gal.Mod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpPaste
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.Mod

theorem spPaste : ∀ {Y S A B C : Scheme.{0}} (p : Y ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : C ⟶ A) (d : C ⟶ B), c ≫ a = d ≫ b → ∀ φ : pullback (pullback.snd p b) d ⟶ pullback p a, φ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ → φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ c → IsPullback φ (pullback.snd _ _) (pullback.snd _ _) c := by
  intro Y S A B C p a b c d h φ h1 h2
  have big : IsPullback (pullback.fst (pullback.snd p b) d ≫ pullback.fst p b)
      (pullback.snd (pullback.snd p b) d) p (d ≫ b) :=
    (IsPullback.of_hasPullback (pullback.snd p b) d).paste_horiz
      (IsPullback.of_hasPullback p b)
  have big' : IsPullback (φ ≫ pullback.fst p a)
      (pullback.snd (pullback.snd p b) d) p (c ≫ a) := by
    rw [h1, h]; exact big
  exact IsPullback.of_right big' h2 (IsPullback.of_hasPullback p a)

end UpperTheory.Gal.Mod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpPbEqv
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.Mod

theorem spPbEqv : ∀ (R : Type) [CommRing R] (F : Shv R) {W X Y Z : Scheme.{0}} (f : W ⟶ X) (g : W ⟶ Y)
    (h : X ⟶ Z) (k : Y ⟶ Z), IsPullback f g h k → Eqv R (sch.map (pullback.fst h k)) F →
    Eqv R (sch.map f) F := by
  intro R _ F W X Y Z f g h k hpb hE n
  have hf : sch.map f = sch.map hpb.isoPullback.hom ≫ sch.map (pullback.fst h k) := by
    rw [← CategoryTheory.Functor.map_comp, IsPullback.isoPullback_hom_fst]
  have hl : ∀ x, pull R (sch.map hpb.isoPullback.inv) F n (pull R (sch.map hpb.isoPullback.hom) F n x) = x := by
    intro x
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  have hr : ∀ x, pull R (sch.map hpb.isoPullback.hom) F n (pull R (sch.map hpb.isoPullback.inv) F n x) = x := by
    intro x
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  have hb : Function.Bijective (pull R (sch.map hpb.isoPullback.hom) F n) :=
    Function.bijective_iff_has_inverse.mpr ⟨_, hl, hr⟩
  have hc : (pull R (sch.map f) F n : _ → _) =
      (pull R (sch.map hpb.isoPullback.hom) F n) ∘ (pull R (sch.map (pullback.fst h k)) F n) := by
    funext x
    rw [hf, pull_comp]
    rfl
  rw [hc]
  exact hb.comp (hE n)

end UpperTheory.Gal.Mod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpUnit
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.Mod

theorem spUnit : ∀ (A k : Type) [CommRing A] [IsLocalRing A] [Field k] (r : A →+* k),
    Function.Surjective r → ∀ q : ℕ, IsUnit (q : k) → IsUnit (q : A) := by
  intro A k _ _ _ r hr q hq
  have hmax : (RingHom.ker r).IsMaximal := RingHom.ker_isMaximal_of_surjective r hr
  have heq : RingHom.ker r = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  by_contra hn
  have hmem : (q : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 hn
  rw [← heq, RingHom.mem_ker, map_natCast] at hmem
  exact hq.ne_zero hmem

end UpperTheory.Gal.Mod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.SpecializationEqvOfProperOfStrictlyHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

private theorem eqv_of_isIso_comp {R : Type} [CommRing R] {E E' E'' : Spc} (a : E ⟶ E') [IsIso a]
    (b : E' ⟶ E'') (F : Shv R) (h : Eqv R b F) : Eqv R (a ≫ b) F := by
  intro n
  have hl : Function.LeftInverse (pull R (inv a) F n) (pull R a F n) := fun x => by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have hr : Function.RightInverse (pull R (inv a) F n) (pull R a F n) := fun x => by
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  have ha : Function.Bijective (pull R a F n) := ⟨hl.injective, hr.surjective⟩
  have he : (pull R (a ≫ b) F n : H R E'' F n → H R E F n) = pull R a F n ∘ pull R b F n := by
    funext x
    exact pull_comp R a b F n x
  rw [he]
  exact ha.comp (h n)

theorem UpperTheory.Gal.Mod.specialization_eqv_of_proper_of_strictly_henselian :
    GlobalTheory.EtC.E2 → ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) → ∀ (k : Type) [Field k] (r : A →+* k), Function.Surjective r → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p] (i : ℤ), Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom r)))) (tw q i) := by
  intro hE2 q A _ _ hSH hq k _ r hr X p _ i
  have hker : RingHom.ker r = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr)

  let e0 : (A ⧸ RingHom.ker r) ≃+* k := RingHom.quotientKerEquivOfSurjective hr
  let e1 : IsLocalRing.ResidueField A ≃+* (A ⧸ RingHom.ker r) :=
    Ideal.quotEquivOfEq hker.symm
  let e : IsLocalRing.ResidueField A ≃+* k := e1.trans e0
  have hfac : (e : IsLocalRing.ResidueField A →+* k).comp (IsLocalRing.residue A) = r := by
    ext x
    rfl
  have hcomp : CommRingCat.ofHom r =
      CommRingCat.ofHom (IsLocalRing.residue A) ≫ CommRingCat.ofHom (e : IsLocalRing.ResidueField A →+* k) := by
    rw [← CommRingCat.ofHom_comp, hfac]
  let s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField A)) :=
    Spec.map (CommRingCat.ofHom (e : IsLocalRing.ResidueField A →+* k))
  have hIso : IsIso (CommRingCat.ofHom (e : IsLocalRing.ResidueField A →+* k)) :=
    (e.toCommRingCatIso).isIso_hom
  haveI : IsIso s := by
    dsimp only [s]
    infer_instance
  let f := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  have hg : Spec.map (CommRingCat.ofHom r) = s ≫ f := by
    dsimp only [s, f]
    rw [hcomp, Spec.map_comp]
  let φ : pullback p (Spec.map (CommRingCat.ofHom r)) ⟶ pullback p f :=
    pullback.map _ _ _ _ (𝟙 _) s (𝟙 _) (by simp) (by simp [hg])
  haveI : IsIso φ := by
    dsimp only [φ]
    infer_instance
  have hφ : pullback.fst p (Spec.map (CommRingCat.ofHom r)) = φ ≫ pullback.fst p f := by
    simp only [φ, pullback.map, pullback.lift_fst, Category.comp_id]
  rw [hφ, Functor.map_comp]
  exact eqv_of_isIso_comp (sch.map φ) _ _ (hE2 q A hSH hq p i)
end

