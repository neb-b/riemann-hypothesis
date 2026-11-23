module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanish
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.PrimitivePullback

variable {R : Type} [CommRing R]

theorem pullHO1_congr {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ ψ : X' ⟶ X} (e : φ = ψ)
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (h' : ψ ≫ s = s' ≫ spMap (RingHom.id R)) (c : HO1 s) :
    pullHO1 h c = pullHO1 h' c := by
  subst e; rfl

theorem isPullO_congr {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ ψ : X' ⟶ X} (e : φ = ψ)
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (h' : ψ ≫ s = s' ≫ spMap (RingHom.id R)) {c : HO1 s} {c' : HO1 s'} :
    IsPullO h c c' ↔ IsPullO h' c c' := by
  subst e; rfl

theorem pullHO1_self {X : Scheme.{0}} {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HO1 s) :
    pullHO1 h c = c :=
  (IsPullO.eq_pullHO1 h
    (CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X) (fun _ _ ↦ rfl) c)).symm

theorem pullHO1_comp {A B C : Over (Sp R)} (f : B ⟶ C) (g : A ⟶ B) (a : HO1 C.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = pullHO1 (overW (g ≫ f)) a := by
  have h'' : (g.left ≫ f.left) ≫ C.hom = A.hom ≫ spMap (RingHom.id R) := by
    rw [← Over.comp_left]; exact overW (g ≫ f)
  have k := (_root_.GlobalTheory.Obs.pullO_basic R C.left B.left C.hom B.hom f.left (overW f)).2.2 A.left A.hom g.left (overW g) h'' a _ _
    (isPullO_pullHO1 _ a) (isPullO_pullHO1 _ _)
  exact IsPullO.eq_pullHO1 _ ((isPullO_congr (show g.left ≫ f.left = (g ≫ f).left from rfl) _ _).1 k)

theorem pullHO1_pull_self {A B : Over (Sp R)} (f : B ⟶ A) (g : A ⟶ B) (e : g ≫ f = 𝟙 A) (a : HO1 A.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = a := by
  rw [pullHO1_comp]
  have h' : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id R) := by
    rw [← Over.id_left]; exact overW (𝟙 A)
  rw [pullHO1_congr (show (g ≫ f).left = 𝟙 A.left by rw [e]; rfl) _ h', pullHO1_self]

theorem pullHO1_pull_one {A B : Over (Sp R)} [GrpObj A] (f : B ⟶ A) (g : A ⟶ B) (e : g ≫ f = 1) (a : HO1 A.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = 0 := by
  rw [pullHO1_comp]
  have h' : (toUnit A ≫ η[A]).left ≫ A.hom = A.hom ≫ spMap (RingHom.id R) := overW _
  rw [pullHO1_congr (show (g ≫ f).left = (toUnit A ≫ η[A]).left by rw [e, Hom.one_def]) _ h', ← pullHO1_comp]
  have : pullHO1 (overW η[A]) a = 0 := by
    haveI : IsAffine (𝟙_ (Over (Sp R))).left := by change IsAffine (Sp R); infer_instance
    exact (_root_.GlobalTheory.Obs.sq_abelian_and_affine_H1 R).2 _ _ _
  rw [this, map_zero]

variable (A : Over (Sp R)) [GrpObj A]

def sumPull : HO1 A.hom × HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom :=
  (pullHO1 (overW (fst A A))).coprod (pullHO1 (overW (snd A A)))

def axesPull : HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
  (pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A)))).prod (pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))))

theorem axesPull_sumPull (x : HO1 A.hom × HO1 A.hom) : axesPull A (sumPull A x) = x := by
  obtain ⟨a, b⟩ := x
  refine Prod.ext ?_ ?_
  · change pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) (pullHO1 (overW (fst A A)) a + pullHO1 (overW (snd A A)) b) = a
    rw [map_add (f := _), pullHO1_pull_self _ _ (lift_fst _ _), pullHO1_pull_one _ _ (lift_snd _ _), add_zero]
  · change pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) (pullHO1 (overW (fst A A)) a + pullHO1 (overW (snd A A)) b) = b
    rw [map_add (f := _), pullHO1_pull_one _ _ (lift_fst _ _), pullHO1_pull_self _ _ (lift_snd _ _), zero_add]

theorem axesPull_injective (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Injective (axesPull A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h1 : pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) x = 0 := congrArg Prod.fst hx
  have h2 : pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) x = 0 := congrArg Prod.snd hx
  refine hax R A g hA hg x ?_ ?_
  · have := isPullO_pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) x; rwa [h1] at this
  · have := isPullO_pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) x; rwa [h2] at this

theorem pullHO1_mul (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (a : HO1 A.hom) : pullHO1 (overW μ[A]) a = sumPull A (a, a) := by
  apply axesPull_injective A hax g hA hg
  rw [axesPull_sumPull]
  refine Prod.ext ?_ ?_
  · change pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) (pullHO1 (overW μ[A]) a) = a
    exact pullHO1_pull_self _ _ (by rw [Hom.one_def, lift_comp_one_right]) a
  · change pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) (pullHO1 (overW μ[A]) a) = a
    exact pullHO1_pull_self _ _ (by rw [Hom.one_def, lift_comp_one_left]) a

theorem sumPull_bijective (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Bijective (sumPull A) :=
  ⟨Function.LeftInverse.injective (axesPull_sumPull A), fun c ↦
    ⟨axesPull A c, axesPull_injective A hax g hA hg (axesPull_sumPull A _)⟩⟩

end GlobalTheory.Obs.PrimitivePullback

namespace GlobalTheory.Obs.PrimitivePullback

variable {R : Type} [CommRing R] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
  {h : φ ≫ s = s' ≫ spMap (RingHom.id R)}

theorem isPullO2_zero : IsPullbackH2Structure h (0 : CatCoh.H2 (OAff s)) (0 : CatCoh.H2 (OAff s')) := by
  unfold IsPullbackH2Structure; rw [map_zero, map_zero]

theorem isPullO2_add {a b : CatCoh.H2 (OAff s)} {a' b' : CatCoh.H2 (OAff s')} (ha : IsPullbackH2Structure h a a')
    (hb : IsPullbackH2Structure h b b') : IsPullbackH2Structure h (a + b) (a' + b') := by
  unfold IsPullbackH2Structure at *; rw [map_add (f := _), map_add (f := _), ha, hb]

theorem isPullO2_smul {a : CatCoh.H2 (OAff s)} {a' : CatCoh.H2 (OAff s')} (ha : IsPullbackH2Structure h a a') (r : R) :
    IsPullbackH2Structure h (r • a) (r • a') := by
  unfold IsPullbackH2Structure at *; rw [map_smulₛₗ, map_smulₛₗ, ha]

theorem isPullO2_unique {c : CatCoh.H2 (OAff s)} {x y : CatCoh.H2 (OAff s')} (hx : IsPullbackH2Structure h c x)
    (hy : IsPullbackH2Structure h c y) : x = y :=
  (_root_.GlobalTheory.Obs.pullO_basic R X X' s s' φ h).1.1 (hx.symm.trans hy)

theorem pullback_wedge_cup_square (h : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (e : ⋀[R]^2 (HO1 s) ≃ₗ[R] CatCoh.H2 (OAff s))
    (he : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = CatCoh.cup (OAff s) a b)
    (e' : ⋀[R]^2 (HO1 s') ≃ₗ[R] CatCoh.H2 (OAff s'))
    (he' : ∀ a b, e' (exteriorPower.ιMulti R 2 ![a, b]) = CatCoh.cup (OAff s') a b) (t : ⋀[R]^2 (HO1 s)) :
    IsPullbackH2Structure h (e t) (e' (exteriorPower.map 2 (pullHO1 h) t)) := by
  have key : ∀ a b : HO1 s, IsPullbackH2Structure h (e (exteriorPower.ιMulti R 2 ![a, b]))
      (e' (exteriorPower.map 2 (pullHO1 h) (exteriorPower.ιMulti R 2 ![a, b]))) := by
    intro a b
    have hc : (pullHO1 h) ∘ ![a, b] = ![pullHO1 h a, pullHO1 h b] := by
      funext i; fin_cases i <;> try rfl
    rw [exteriorPower.map_apply_ιMulti, hc, he, he']
    exact (_root_.GlobalTheory.Obs.pullO_basic R X X' s s' φ h).2.1 a b _ _ (isPullO_pullHO1 h a) (isPullO_pullHO1 h b)
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> try rfl
    have := key (v 0) (v 1)
    rwa [← hv] at this
  | zero => simp only [map_zero]; exact isPullO2_zero
  | add x y _ _ hx hy => simp only [map_add (f := _)]; exact isPullO2_add hx hy
  | smul r x _ hx => simp only [map_smul]; exact isPullO2_smul hx r

end GlobalTheory.Obs.PrimitivePullback


open GlobalTheory.Obs.PrimitivePullback in
theorem GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso
    (H : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom →
      (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
      ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom),
        ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) : PrimitiveStructureSheafDegTwoVanish := by
  intro R _ A _ g hA hg c c₁ c₂ hm h1 h2
  have hax : AxesVanishingStructureSheafDegOne := GlobalTheory.T.axesO1_of_projective_rank_cup H
  obtain ⟨hAA, hgg⟩ := (_root_.GlobalTheory.Obs.sq_abelian_and_affine_H1 R).1 A g hA hg
  obtain ⟨⟨_, hproj, _⟩, e, he⟩ := H R A g hA hg
  obtain ⟨_, e', he'⟩ := H R (A ⊗ A) (g + g) hAA hgg
  obtain ⟨t, rfl⟩ := e.surjective c
  have km := pullback_wedge_cup_square (overW μ[A]) e he e' he' t
  have k1 := pullback_wedge_cup_square (overW (fst A A)) e he e' he' t
  have k2 := pullback_wedge_cup_square (overW (snd A A)) e he e' he' t
  have E : exteriorPower.map 2 (pullHO1 (overW μ[A])) t =
      exteriorPower.map 2 (pullHO1 (overW (fst A A))) t + exteriorPower.map 2 (pullHO1 (overW (snd A A))) t := by
    apply e'.injective
    rw [map_add (f := _), ← isPullO2_unique hm km, ← isPullO2_unique h1 k1, ← isPullO2_unique h2 k2]
  let P := LinearEquiv.ofBijective (sumPull A) (sumPull_bijective A hax g hA hg)
  have hμ : (pullHO1 (overW μ[A]) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ (LinearMap.inl R (HO1 A.hom) (HO1 A.hom) + LinearMap.inr R (HO1 A.hom) (HO1 A.hom)) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk,
      add_zero, zero_add]
    exact pullHO1_mul A hax g hA hg a
  have h₁ : (pullHO1 (overW (fst A A)) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ LinearMap.inl R (HO1 A.hom) (HO1 A.hom) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.inl_apply]
    simp only [sumPull, LinearMap.coprod_apply, map_zero, add_zero]
  have h₂ : (pullHO1 (overW (snd A A)) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ LinearMap.inr R (HO1 A.hom) (HO1 A.hom) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.inr_apply]
    simp only [sumPull, LinearMap.coprod_apply, map_zero, zero_add]
  simp only [hμ, h₁, h₂, exteriorPower.map_comp, LinearMap.comp_apply] at E
  rw [← map_add (exteriorPower.map 2 (sumPull A))] at E
  have hid : P.symm.toLinearMap ∘ₗ sumPull A = LinearMap.id :=
    LinearMap.ext fun x ↦ P.symm_apply_apply x
  have hinj : Function.Injective (exteriorPower.map 2 (sumPull A)) := by
    intro x y hxy
    have k : ∀ z, exteriorPower.map 2 P.symm.toLinearMap (exteriorPower.map 2 (sumPull A) z) = z := by
      intro z
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hid, exteriorPower.map_id, LinearMap.id_apply]
    rw [← k x, ← k y, hxy]
  haveI := hproj
  rw [_root_.GlobalTheory.WedgeDiag.eq_zero_of_diag_additive R (HO1 A.hom) t (hinj E), map_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionEquivariantEquivOfLevelIsos
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.InvAlg.Levels

abbrev red {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k n : ℕ} (h : k ≤ n) :
    A ⧸ I ^ n →ₐ[R] A ⧸ I ^ k :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)

theorem red_red {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k l n : ℕ} (h₁ : k ≤ l)
    (h₂ : l ≤ n) (z : A ⧸ I ^ n) : red (R := R) I h₁ (red (R := R) I h₂ z) = red (R := R) I (h₁.trans h₂) z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem red_refl {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {n : ℕ}
    (z : A ⧸ I ^ n) : red (R := R) I (le_refl n) z = z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem red_evalₐ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k n : ℕ} (h : k ≤ n)
    (x : AdicCompletion I A) :
    red (R := R) I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x :=
  GlobalTheory.InvAlg.factorPow_evalₐ I h x

theorem compat_le {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (β : ∀ n : ℕ, A ⧸ I ^ (n + 1) →ₐ[R] B ⧸ J ^ (n + 1))
    (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z))
    {k n : ℕ} (h : k ≤ n) (z : A ⧸ I ^ (n + 1)) :
    red (R := R) J (Nat.succ_le_succ h) (β n z) = β k (red (R := R) I (Nat.succ_le_succ h) z) := by
  induction n, h using Nat.le_induction with
  | base => rw [red_refl, red_refl]
  | succ n hkn ih =>
    rw [← red_red (R := R) J (Nat.succ_le_succ hkn) (Nat.le_succ (n + 1)), hβ, ih, red_red]

theorem exists_equiv {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (β : ∀ n : ℕ, (A ⧸ I ^ (n + 1)) ≃ₐ[R] (B ⧸ J ^ (n + 1)))
    (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z)) :
    ∃ Ψ : AdicCompletion I A ≃ₐ[R] AdicCompletion J B,
      ∀ n y, AdicCompletion.evalₐ J (n + 1) (Ψ y) = β n (AdicCompletion.evalₐ I (n + 1) y) := by
  have hβ' : ∀ n z, red (R := R) I (Nat.le_succ (n + 1)) ((β (n + 1)).symm z) =
      (β n).symm (red (R := R) J (Nat.le_succ (n + 1)) z) := by
    intro n z
    apply (β n).injective
    rw [AlgEquiv.apply_symm_apply, ← hβ, AlgEquiv.apply_symm_apply]
  have key : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (I : Ideal A) (J : Ideal B)
      (β : ∀ n : ℕ, A ⧸ I ^ (n + 1) →ₐ[R] B ⧸ J ^ (n + 1))
      (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z)),
      ∃ Φ : AdicCompletion I A →ₐ[R] AdicCompletion J B,
        ∀ n y, AdicCompletion.evalₐ J (n + 1) (Φ y) = β n (AdicCompletion.evalₐ I (n + 1) y) := by
    intro A B _ _ _ _ I J β hβ
    let f : ∀ n, AdicCompletion I A →ₐ[R] B ⧸ J ^ n := fun n =>
      (red (R := R) J (Nat.le_succ n)).comp ((β n).comp ((AdicCompletion.evalₐ I (n + 1)).restrictScalars R))
    have hf : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f k := by
      intro k n hle
      refine AlgHom.ext fun y => ?_
      change red (R := R) J hle (red (R := R) J (Nat.le_succ n) (β n (AdicCompletion.evalₐ I (n + 1) y))) =
        red (R := R) J (Nat.le_succ k) (β k (AdicCompletion.evalₐ I (k + 1) y))
      rw [red_red, ← red_red (R := R) J (Nat.le_succ k) (Nat.succ_le_succ hle), compat_le I J β hβ hle, red_evalₐ]
    refine ⟨AdicCompletion.liftAlgHom J f hf, fun n y => ?_⟩
    rw [AdicCompletion.evalₐ_liftAlgHom]
    change red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) (AdicCompletion.evalₐ I (n + 1 + 1) y)) = _
    rw [hβ, red_evalₐ]
  obtain ⟨Φ, hΦ⟩ := key I J (fun n => (β n).toAlgHom) hβ
  obtain ⟨Φ', hΦ'⟩ := key J I (fun n => (β n).symm.toAlgHom) hβ'
  have ev : ∀ {A : Type} [CommRing A] [Algebra R A] (I : Ideal A) (x y : AdicCompletion I A),
      (∀ n, AdicCompletion.evalₐ I (n + 1) x = AdicCompletion.evalₐ I (n + 1) y) → x = y := by
    intro A _ _ I x y h
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [← red_evalₐ (R := R) I (Nat.le_succ n) x, ← red_evalₐ (R := R) I (Nat.le_succ n) y, h]
  refine ⟨AlgEquiv.ofAlgHom Φ Φ' ?_ ?_, hΦ⟩
  · refine AlgHom.ext fun y => ?_
    refine ev J _ _ fun n => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [hΦ, hΦ']
    exact AlgEquiv.apply_symm_apply _ _
  · refine AlgHom.ext fun y => ?_
    refine ev I _ _ fun n => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [hΦ', hΦ]
    exact AlgEquiv.symm_apply_apply _ _

end GlobalTheory.InvAlg.Levels

namespace GlobalTheory.InvAlg.Levels

theorem levels_equiv : ∀ (R : Type) [CommRing R] (m : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C']
    [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (act : GlobalTheory.Mum.Gal (algebraMap R R') →* (C' ≃ₐ[R] C')),
    (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) →
    ∀ (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C')),
    (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) →
    (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) →
    (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧
      RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) =
        (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) →
    ∀ (IT : Ideal (TensorProduct R O R')) (IC : Ideal C'), IT = m.map (algebraMap R (TensorProduct R O R')) →
      IC = m.map (algebraMap R C') →
    ∀ (hT : ∀ σ, IT.map (GlobalTheory.InvAlg.galTensor O σ).toRingHom ≤ IT)
      (hC : ∀ σ, IC.map (act σ).toRingEquiv.toRingHom ≤ IC),
    ∃ Ψ : AdicCompletion IT (TensorProduct R O R') ≃ₐ[R] AdicCompletion IC C',
      (∀ σ y, Ψ (GlobalTheory.InvAlg.cmap (GlobalTheory.InvAlg.galTensor O σ).toRingHom
          IT IT (hT σ) y) = GlobalTheory.InvAlg.cmap (act σ).toRingEquiv.toRingHom IC IC (hC σ) (Ψ y)) ∧
      ∀ e (x : O) (y : C'), Ideal.Quotient.mk ((m ^ (e + 1)).map (algebraMap R C')) y = i e x →
        AdicCompletion.evalₐ IC (e + 1) (Ψ (AdicCompletion.of IT _ (x ⊗ₜ[R] (1 : R')))) =
          Ideal.Quotient.mk (IC ^ (e + 1)) y := by
  intro R _ m R' _ _ C' _ _ _ _ act hact O _ _ i hi1 hi2 hi3 IT IC hIT hIC hT hC
  subst hIT hIC
  let L : ∀ e, TensorProduct R O R' →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C') := fun e =>
    Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C'))
      fun _ _ => Commute.all _ _
  have hCpow : ∀ e, (m ^ (e + 1)).map (algebraMap R C') = (m.map (algebraMap R C')) ^ (e + 1) :=
    fun e => Ideal.map_pow _ _ _
  have hTpow : ∀ e, (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R')) =
      (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1) :=
    fun e => Ideal.map_pow _ _ _
  let E : ∀ e, (C' ⧸ (m ^ (e + 1)).map (algebraMap R C')) ≃ₐ[R] (C' ⧸ (m.map (algebraMap R C')) ^ (e + 1)) :=
    fun e => Ideal.quotientEquivAlgOfEq R (hCpow e)
  let L' : ∀ e, TensorProduct R O R' →ₐ[R] C' ⧸ (m.map (algebraMap R C')) ^ (e + 1) := fun e =>
    (E e).toAlgHom.comp (L e)
  have hsurj : ∀ e, Function.Surjective (L' e) := fun e => (E e).surjective.comp (hi3 e).1
  have hker : ∀ e, RingHom.ker (L' e) = (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1) := by
    intro e
    ext t
    rw [RingHom.mem_ker, ← hTpow, ← (hi3 e).2, RingHom.mem_ker]
    exact map_eq_zero_iff (E e) (E e).injective
  let β : ∀ e, (TensorProduct R O R' ⧸ (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1)) ≃ₐ[R]
      (C' ⧸ (m.map (algebraMap R C')) ^ (e + 1)) := fun e =>
    (Ideal.quotientEquivAlgOfEq R (hker e).symm).trans (Ideal.quotientKerAlgEquivOfSurjective (hsurj e))
  have hβmk : ∀ e t, β e (Ideal.Quotient.mk _ t) = L' e t := fun e t => rfl
  have hL : ∀ e x r y, Ideal.Quotient.mk _ y = i e x →
      L' e (x ⊗ₜ[R] r) = Ideal.Quotient.mk _ (y * algebraMap R' C' r) := by
    intro e x r y hy
    change E e (L e (x ⊗ₜ[R] r)) = _
    rw [Algebra.TensorProduct.lift_tmul, ← hy]
    change E e (Ideal.Quotient.mk _ y * Ideal.Quotient.mk _ (algebraMap R' C' r)) = _
    rw [← map_mul]
    exact Ideal.quotientEquivAlgOfEq_mk _ _ _
  have hred : ∀ n z, red (R := R) (m.map (algebraMap R C')) (Nat.le_succ (n + 1)) (β (n + 1) z) =
      β n (red (R := R) (m.map (algebraMap R (TensorProduct R O R'))) (Nat.le_succ (n + 1)) z) := by
    intro n z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    change red (R := R) (m.map (algebraMap R C')) (Nat.le_succ (n + 1)) (L' (n + 1) t) = L' n t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r =>
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i (n + 1) x)
      rw [hL (n + 1) x r y hy, hL n x r y (hi1 n x y hy)]
      rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  obtain ⟨Ψ, hΨ⟩ := exists_equiv _ _ β hred
  have ev : ∀ {A : Type} [CommRing A] (I : Ideal A) (x y : AdicCompletion I A),
      (∀ n, AdicCompletion.evalₐ I (n + 1) x = AdicCompletion.evalₐ I (n + 1) y) → x = y := by
    intro A _ I x y h
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [← GlobalTheory.InvAlg.factorPow_evalₐ I (Nat.le_succ n) x, ← GlobalTheory.InvAlg.factorPow_evalₐ I (Nat.le_succ n) y, h]
  refine ⟨Ψ, fun σ y => ev _ _ _ fun n => ?_, fun e x y hy => ?_⟩
  · rw [hΨ, GlobalTheory.InvAlg.evalₐ_cmap, GlobalTheory.InvAlg.evalₐ_cmap, hΨ]
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ (n + 1) y)
    rw [← ht, Ideal.quotientMap_mk, hβmk, hβmk]
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r =>
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i n x)
      have h1 : (GlobalTheory.InvAlg.galTensor O σ).toRingHom (x ⊗ₜ[R] r) = x ⊗ₜ[R] σ.1 r := rfl
      rw [h1, hL n x _ y hy, hL n x r y hy, Ideal.quotientMap_mk]
      change _ = Ideal.Quotient.mk _ (act σ (y * algebraMap R' C' r))
      rw [map_mul (act σ), hact, map_mul (Ideal.Quotient.mk _), map_mul (Ideal.Quotient.mk _)]
      congr 1
      have h2 := hi2 n σ x y hy
      rw [← hy, Ideal.Quotient.eq, hCpow] at h2
      rw [Ideal.Quotient.eq, ← neg_sub]
      exact neg_mem h2
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  · rw [hΨ, AdicCompletion.evalₐ_of, hβmk, hL e x 1 y hy, map_one, _root_.mul_one]

end GlobalTheory.InvAlg.Levels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmul
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

theorem app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G),
      g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a ∈ kerIdeal (f.app 1), g.app 1 a = 0 := by
  intro p _ R _ G H f g hgf a ha
  have hle : kerIdeal (f.app 1) ≤ RingHom.ker (g.app 1 : G.A 1 →ₐ[R] H.A 1) := by
    rw [kerIdeal, Ideal.map_le_iff_le_comap]
    intro c hc
    have hc' : counit (R := R) c = 0 := hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e : g.app 1 (f.app 1 c) = Hom.app (g ≫ f) 1 c := rfl
    change g.app 1 (f.app 1 c) = 0
    rw [e, hgf, prime_smul_id_app]
    have h1 := H.mulBy_pow_self 1 c
    rw [pow_one] at h1
    rw [h1, hc', map_zero]
  exact hle ha

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceEverywhere
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem archEx_continuous_det {r : ℕ} {Ψ : Finset (E →+* ℂ)} (τ : Ψ) :
    Continuous fun y : Frame Ψ r => (mat y τ).det :=
  Continuous.matrix_det (continuous_apply τ)

theorem archEx_continuousOn_horizGen {r : ℕ} (X : Data E r) (τ : X.Ψ) : ContinuousOn (horizGen τ) X.dom :=
  (archEx_continuous_det τ).continuousOn.inv₀ fun _ hy => (hy τ).1

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem archEx_relab_mem {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (τ : Psi H) (k : U.Comp) :
    relab c σ τ.1 ∈ (U.X k).Ψ := by
  refine ((hU.2.1 k).2 _).2 ?_
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  exact (congrArg σ (Subtype.ext τ.2)).trans hσ0

end SlopeTestRemainingChoices

end GlobalTheory.FlatCore

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingMulImageEqOfFieldPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s : Sp Ω ⟶ M.S) (a b c : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (ca cb : Over.mk (spMap (io.comp κ)) ⟶ E.Y), ca.left ≫ E.j = spMap io ≫ a ≫ fU ∧ cb.left ≫ E.j = spMap io ≫ b ≫ fU ∧ (ca * cb).left ≫ E.j = spMap io ≫ c ≫ fU := by
  first | exact @GlobalTheory.Mum.closed_product_image | exact GlobalTheory.Mum.closed_product_image | (intros; apply GlobalTheory.Mum.closed_product_image <;> assumption)
end

