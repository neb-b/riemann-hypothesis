module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.LevelStructureForms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelCompare

theorem rel_of_basis {G U J : Type} [CommGroup G] [CommGroup U] [Fintype J] [DecidableEq J]
    (W : G → G → U → Prop) (φ : (J → ℤ) → G) (hφ : ∀ a b, φ (a + b) = φ a * φ b)
    (ex : ∀ a b, ∃! c, W (φ a) (φ b) c)
    (mul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (skew : ∀ x y c, W x y c → W y x c⁻¹)
    (β : (J → ℤ) → (J → ℤ) → ℤ) (β₁ : ∀ a a' b, β (a + a') b = β a b + β a' b)
    (β₂ : ∀ a b b', β a (b + b') = β a b + β a b') (ζ : U)
    (h : ∀ i j, W (φ (Pi.single i 1)) (φ (Pi.single j 1)) (ζ ^ β (Pi.single i 1) (Pi.single j 1)))
    (a b : J → ℤ) : W (φ a) (φ b) (ζ ^ β a b) := by
  choose e he hu using ex
  have e₁ : ∀ a a' b, e (a + a') b = e a b * e a' b := fun a a' b =>
    (hu _ _ _ (by rw [hφ]; exact mul _ _ _ _ _ (he a b) (he a' b))).symm
  have es : ∀ a b, e b a = (e a b)⁻¹ := fun a b => (hu _ _ _ (skew _ _ _ (he a b))).symm
  have e₂ : ∀ a b b', e a (b + b') = e a b * e a b' := fun a b b' => by
    rw [es, e₁, mul_inv, ← es, ← es]
  let E : (J → ℤ) →+ (J → ℤ) →+ Additive U :=
    AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => Additive.ofMul (e a b))
      (fun b b' => congrArg Additive.ofMul (e₂ a b b')))
      (fun a a' => AddMonoidHom.ext fun b => congrArg Additive.ofMul (e₁ a a' b))
  let F : (J → ℤ) →+ (J → ℤ) →+ Additive U :=
    AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => Additive.ofMul (ζ ^ β a b))
      (fun b b' => by rw [β₂, zpow_add]; rfl))
      (fun a a' => AddMonoidHom.ext fun b => by
        show Additive.ofMul (ζ ^ β (a + a') b) = _
        rw [β₁, zpow_add]; rfl)
  have hEF : E = F := AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int <|
    AddMonoidHom.functions_ext' _ _ _ fun j => AddMonoidHom.ext_int <|
      congrArg Additive.ofMul (hu _ _ _ (h i j)).symm
  have : e a b = ζ ^ β a b := congrArg (fun H : (J → ℤ) →+ (J → ℤ) →+ Additive U => (H a b).toMul) hEF
  exact this ▸ he a b

variable {S : Scheme.{0}}

theorem eq_section_of_range {X T : Over S} (t : 𝟙_ (Over S) ⟶ X) [IsOpenImmersion t.left]
    (u : T ⟶ X) (h : Set.range u.left ⊆ Set.range t.left) : toUnit T ≫ t = u := by
  have hl := IsOpenImmersion.lift_fac t.left u.left h
  have e : t.left ≫ X.hom = 𝟙 S := Over.w t
  let l : T ⟶ 𝟙_ (Over S) := Over.homMk (IsOpenImmersion.lift t.left u.left h) (by
    change _ ≫ 𝟙 S = T.hom
    rw [← Over.w u, ← e]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.hom) hl))
  rw [toUnit_unique (toUnit _) l]
  exact Over.OverMorphism.ext hl

theorem exists_geomPoint (X : Over S) (x : X.left) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (s : Spec (CommRingCat.of K) ⟶ S)
      (u : Over.mk s ⟶ X), Set.range u.left = {x} := by
  let K := AlgebraicClosure (X.left.residueField x)
  let u : Spec (CommRingCat.of K) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.left.residueField x) K)) ≫
      X.left.fromSpecResidueField x
  refine ⟨K, inferInstance, inferInstance, u ≫ X.hom, Over.homMk u rfl, ?_⟩
  have hu : ∀ p, u p = x := fun p =>
    (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply x _)
  ext z
  exact ⟨fun ⟨p, hp⟩ => hp.symm.trans (hu p), fun hz => ⟨(⊥ : PrimeSpectrum K), (hu _).trans hz.symm⟩⟩

def ListsGeomPoints {I : Type} {X : Over S} (t : I → (𝟙_ (Over S) ⟶ X)) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) (u : Over.mk s ⟶ X),
    ∃! i, toUnit _ ≫ t i = u

theorem isIso_desc_iff {I : Type} {X : Over S} (t : I → (𝟙_ (Over S) ⟶ X)) :
    IsIso (Sigma.desc t) ↔ IsIso (Sigma.desc (f := fun _ : I => S) fun i => (t i).left) := by
  refine (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk X t)).symm.trans (Iff.trans ?_
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk (f := fun _ : I => S) X.left fun i => (t i).left)))
  constructor
  · rintro ⟨h⟩
    exact ⟨isColimitMapCoconeCofanMkEquiv (Over.forget S) _ t (isColimitOfPreserves (Over.forget S) h)⟩
  · rintro ⟨h⟩
    exact ⟨isColimitOfReflects (Over.forget S)
      ((isColimitMapCoconeCofanMkEquiv (Over.forget S) _ t).symm h)⟩

theorem isIso_desc_of_lists {I : Type} {X : Over S} (t : I → (𝟙_ (Over S) ⟶ X))
    [FormallyUnramified X.hom] [LocallyOfFiniteType X.hom] (h : ListsGeomPoints t) :
    IsIso (Sigma.desc t) := by
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 le_rfl
  have ho : ∀ i, IsOpenImmersion (t i).left := fun i =>
    MorphismProperty.of_postcomp (W := @IsOpenImmersion)
      (W' := MorphismProperty.diagonal @IsOpenImmersion) (t i).left X.hom
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal X.hom)))
      (by rw [Over.w (t i)]; exact inferInstanceAs (IsOpenImmersion (𝟙 S)))
  rw [isIso_desc_iff]
  refine (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk (f := fun _ : I => S) X.left fun i => (t i).left)).1
    (@nonempty_isColimit_cofanMk_of _ _ (fun _ : I => S) _ (fun i => (t i).left) ho ?_ ?_)
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨K, _, _, s, u, hu⟩ := exists_geomPoint X x
    obtain ⟨i, hi, -⟩ := h K s u
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    obtain ⟨p, hp⟩ : x ∈ Set.range u.left := hu ▸ rfl
    rw [← hi, Over.comp_left, Scheme.Hom.comp_apply] at hp
    exact ⟨_, hp⟩
  · intro i j hij U hi hj x hx
    obtain ⟨K, _, _, s, u, hu⟩ := exists_geomPoint X x
    exact (hij ((h K s u).unique
      (eq_section_of_range (t i) u (hu ▸ Set.singleton_subset_iff.2 (hi hx)))
      (eq_section_of_range (t j) u (hu ▸ Set.singleton_subset_iff.2 (hj hx))))).elim

open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms (mulBy constOver stdForm reduce)

abbrev Ker (A : Over S) [GrpObj A] (k : ℕ) : Over S := pullback (mulBy A k) η[A]

theorem comp_mulBy {A T : Over S} [GrpObj A] (x : T ⟶ A) (k : ℕ) : x ≫ mulBy A k = x ^ k := by
  rw [mulBy, MonObj.comp_pow, Category.comp_id]

def kerPt {A T : Over S} [GrpObj A] {k : ℕ} (x : T ⟶ A) (hx : x ^ k = 1) : T ⟶ Ker A k :=
  pullback.lift x (toUnit _) (by rw [comp_mulBy, hx, Hom.one_def])

theorem kerPt_fst {A T : Over S} [GrpObj A] {k : ℕ} (x : T ⟶ A) (hx : x ^ k = 1) :
    kerPt x hx ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _

theorem ker_ext {A T : Over S} [GrpObj A] {k : ℕ} {u v : T ⟶ Ker A k}
    (h : u ≫ pullback.fst _ _ = v ≫ pullback.fst _ _) : u = v :=
  pullback.hom_ext h (toUnit_unique _ _)

theorem isKer_iff {A : Over S} [GrpObj A] {k : ℕ} {I : Type} (x : I → (𝟙_ (Over S) ⟶ A))
    (hx : ∀ i, x i ^ k = 1) :
    IsPullback (Sigma.desc x : constOver S I ⟶ A) (toUnit _) (mulBy A k) η[A] ↔
      IsIso (Sigma.desc fun i => kerPt (x i) (hx i)) := by
  have e : (Sigma.desc fun i => kerPt (x i) (hx i)) ≫ pullback.fst _ _ = Sigma.desc x :=
    Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_desc_assoc, kerPt_fst, Sigma.ι_desc]
  constructor
  · intro h
    rw [show (Sigma.desc fun i => kerPt (x i) (hx i)) = h.isoPullback.hom from
      ker_ext (e.trans h.isoPullback_hom_fst.symm)]
    infer_instance
  · intro h
    exact (IsPullback.of_hasPullback (mulBy A k) η[A]).of_iso'
      (asIso (Sigma.desc fun i => kerPt (x i) (hx i))) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using e) (toUnit_unique _ _) (by simp) (by simp)

theorem locallyOfFiniteType_ker (A : Over S) [GrpObj A] [LocallyOfFiniteType A.hom] (k : ℕ) :
    LocallyOfFiniteType (Ker A k).hom := by
  have h := (IsPullback.of_hasPullback (mulBy A k) η[A]).map (Over.forget S)
  have : LocallyOfFiniteType (η[A].left ≫ A.hom) := by
    rw [Over.w η[A]]; exact inferInstanceAs (LocallyOfFiniteType (𝟙 S))
  have h₁ : LocallyOfFiniteType η[A].left := locallyOfFiniteType_of_comp _ A.hom
  have h₂ : LocallyOfFiniteType (pullback.fst (mulBy A k) η[A]).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h.flip h₁
  rw [← Over.w (pullback.fst (mulBy A k) η[A])]
  infer_instance

theorem formallyUnramified_ker (A : Over S) [GrpObj A] [IsCommMonObj A] {k : ℕ}
    (hk : IsUnit (k : Γ(S, ⊤))) : FormallyUnramified (Ker A k).hom := by
  have h := (IsPullback.of_hasPullback (mulBy A k) η[A]).map (Over.forget S)
  have h₁ : FormallyUnramified (mulBy A k).left := GlobalTheory.formallyUnramified_mulA S A k hk
  have h₂ : FormallyUnramified (pullback.snd (mulBy A k) η[A]).left :=
    MorphismProperty.of_isPullback (P := @FormallyUnramified) h h₁
  rw [← Over.w (pullback.snd (mulBy A k) η[A])]
  exact MorphismProperty.comp_mem @FormallyUnramified _ _ h₂
    (inferInstanceAs (FormallyUnramified (𝟙 S)))

theorem weil_existsUnique (P : PolAV S) (k : ℕ) {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1)
    (hy : y ^ k = 1) : ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L k x y c :=
  GlobalTheory.CommutatorPairing.existsUnique_weilIs GlobalTheory.laws_without_cohomology.1
    (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_gen).1).2.2
    S P k T x y hx hy

theorem weil_skew_natural (P : PolAV S) (k : ℕ) (T : Over S) :
    (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧
    ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c →
      WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) :=
  (GlobalTheory.weilIs_alternating_skew_natural GlobalTheory.laws_without_cohomology.1
    (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_gen).1).2.2
    S P k T).2

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) :=
  finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem halves_inl (g : ℕ) (i : Fin g) : (halves g (.inl i) : ℕ) = i := rfl

theorem halves_inr (g : ℕ) (i : Fin g) : (halves g (.inr i) : ℕ) = g + i := rfl

theorem stdForm_single (g : ℕ) (i j : Fin g ⊕ Fin g) :
    stdForm (Pi.single i 1) (Pi.single j 1) = stdSymp g (halves g i) (halves g j) := by
  rcases i with i | i <;> rcases j with j | j <;> have := i.2 <;> have := j.2 <;>
    simp only [stdSymp, halves_inl, halves_inr] <;>
    simp [stdForm, Pi.single_apply] <;> split_ifs <;> omega

theorem stdForm_add_left {g : ℕ} (a a' b : Fin g ⊕ Fin g → ℤ) :
    stdForm (a + a') b = stdForm a b + stdForm a' b := by
  simp only [stdForm, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem stdForm_add_right {g : ℕ} (a b b' : Fin g ⊕ Fin g → ℤ) :
    stdForm a (b + b') = stdForm a b + stdForm a b' := by
  simp only [stdForm, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem reduce_add {g : ℕ} (k : ℕ) (a b : Fin g ⊕ Fin g → ℤ) :
    reduce k (a + b) = reduce k a + reduce k b := funext fun j => by simp [reduce]

theorem reduce_single {g : ℕ} (k : ℕ) (i : Fin g ⊕ Fin g) (n : ℤ) :
    reduce k (Pi.single i n) = Pi.single i (n : ZMod k) := funext fun j => by
  simp only [reduce, Pi.single_apply]
  split_ifs <;> simp

def basisHom {G J : Type} [CommGroup G] [Fintype J] {k : ℕ} [NeZero k] (y : J → G)
    (hy : ∀ i, y i ^ k = 1) : Multiplicative (J → ZMod k) →* G :=
  MonoidHom.mk' (fun a => ∏ i, y i ^ (a.toAdd i).val) fun a b => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hy i), pow_add]

theorem basisHom_single {G J : Type} [CommGroup G] [Fintype J] [DecidableEq J] {k : ℕ} [NeZero k]
    (y : J → G) (hy : ∀ i, y i ^ k = 1) (i : J) :
    basisHom y hy (Multiplicative.ofAdd (Pi.single i 1)) = y i := by
  change ∏ j, y j ^ ((Pi.single i (1 : ZMod k) : J → ZMod k) j).val = y i
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp),
    Pi.single_eq_same, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (hy i), pow_one]

theorem hom_pow {G J : Type} [Monoid G] {k : ℕ} (φ : Multiplicative (J → ZMod k) →* G)
    (a : Multiplicative (J → ZMod k)) : φ a ^ k = 1 := by
  rw [← map_pow, ← map_one φ]
  congr 1
  exact funext fun i => by
    change (k • a.toAdd) i = 0
    simp

variable {P : PolAV S} {k : ℕ} {ζ : Γ(S, ⊤)ˣ}

local instance isComm (P : PolAV S) : IsCommMonObj P.A := P.isAb.comm

theorem torsion_halves (lev : Out.Level P k ζ) (i : Fin P.g ⊕ Fin P.g) :
    (lev.pt (halves P.g i) : 𝟙_ (Over S) ⟶ P.A) ^ k = 1 := lev.torsion _

def homOfBasis [NeZero k] (lev : Out.Level P k ζ) :
    Multiplicative (Fin P.g ⊕ Fin P.g → ZMod k) →* (𝟙_ (Over S) ⟶ P.A) :=
  basisHom (fun i => lev.pt (halves P.g i)) (torsion_halves lev)

theorem homOfBasis_single [NeZero k] (lev : Out.Level P k ζ) (i : Fin P.g ⊕ Fin P.g) :
    homOfBasis lev (Multiplicative.ofAdd (Pi.single i 1)) = lev.pt (halves P.g i) :=
  basisHom_single _ _ i

theorem pairing_of_basis [NeZero k] (lev : Out.Level P k ζ) (a b : Fin P.g ⊕ Fin P.g → ℤ) :
    WeilIs P.A P.L (k : ℤ) (T := 𝟙_ (Over S))
      (homOfBasis lev (Multiplicative.ofAdd (reduce k a)))
      (homOfBasis lev (Multiplicative.ofAdd (reduce k b))) (ζ ^ stdForm a b : Γ(S, ⊤)ˣ) := by
  refine rel_of_basis (U := Γ(S, ⊤)ˣ) (fun x y c => WeilIs P.A P.L (k : ℤ) (T := 𝟙_ (Over S)) x y c)
    (fun a => homOfBasis lev (Multiplicative.ofAdd (reduce k a)))
    (fun a b => by rw [reduce_add, ofAdd_add, map_mul])
    (fun a b => weil_existsUnique P k (T := 𝟙_ (Over S)) _ _ (hom_pow (homOfBasis lev) _)
      (hom_pow (homOfBasis lev) _))
    (GlobalTheory.weilIs_mul_left GlobalTheory.laws_without_cohomology.1 S P k _) (weil_skew_natural P k _).1
    stdForm stdForm_add_left stdForm_add_right ζ (fun i j => ?_) a b
  simp only [reduce_single, Int.cast_one, homOfBasis_single, stdForm_single]
  exact lev.pairing _ _

end GlobalTheory.LevelCompare
