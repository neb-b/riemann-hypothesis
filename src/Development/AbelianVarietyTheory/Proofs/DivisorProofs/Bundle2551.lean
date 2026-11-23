module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismLocalDescentsGlueUnion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDescent

theorem descend_glue : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (I : Type) (V : I → Y.Opens) (hV : ∀ i, p ⁻¹ᵁ V i ≤ O) (h₀ : ∀ i, (V i).toScheme ⟶ W), (∀ i, (p ∣_ V i) ≫ h₀ i = Z.homOfLE (hV i) ≫ h) → ∃ (hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O) (m : (⨆ i, V i).toScheme ⟶ W), (p ∣_ (⨆ i, V i)) ≫ m = Z.homOfLE hV' ≫ h ∧ ∀ (W' : Scheme.{0}) (g g' : (⨆ i, V i).toScheme ⟶ W'), (p ∣_ (⨆ i, V i)) ≫ g = (p ∣_ (⨆ i, V i)) ≫ g' → g = g' := by
  intro R _ _ _ _ S Y Z W π y p q hπp hπs hSi hy hpb O h I V hV h₀ hh
  have hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O := by
    rw [Scheme.Hom.preimage_iSup]; exact iSup_le hV
  haveI := hy
  have hflat : Flat ((⨆ i, V i).ι ≫ y) := inferInstance
  have hsq : IsPullback (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) ((⨆ i, V i).ι ≫ y) π :=
    (isPullback_morphismRestrict p (⨆ i, V i)).paste_vert hpb
  have loc : ∀ (i : I) (T : Scheme.{0}) (k : T ⟶ (p ⁻¹ᵁ (⨆ i, V i)).toScheme) (t : T ⟶ (V i).toScheme),
      k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι ≫ p = t ≫ (V i).ι → k ≫ Z.homOfLE hV' ≫ h = t ≫ h₀ i := by
    intro i T k t hkt
    have sq := isPullback_morphismRestrict p (V i)
    have w : t ≫ (V i).ι = (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) ≫ p := by rw [Category.assoc]; exact hkt.symm
    have h1 : sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ (p ∣_ V i) = t := sq.lift_fst _ _ _
    have h2 : sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ (p ⁻¹ᵁ V i).ι = k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι :=
      sq.lift_snd _ _ _
    have h3 : k ≫ Z.homOfLE hV' = sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ Z.homOfLE (hV i) := by
      rw [← cancel_mono O.ι]; simp [h2]
    rw [reassoc_of% h3, ← hh i, reassoc_of% h1]
  have heq : pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (Z.homOfLE hV' ≫ h) =
      pullback.snd (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (Z.homOfLE hV' ≫ h) := by
    let a : pullback (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ⟶ Y :=
      pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (p ∣_ (⨆ i, V i)) ≫ (⨆ i, V i).ι
    have hcov : TopologicalSpace.IsOpenCover (fun i => a ⁻¹ᵁ V i) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, eq_top_iff]
      intro x _
      have hx : a.base x ∈ Set.range (⨆ i, V i).ι.base := by
        have ha : a = (pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (p ∣_ (⨆ i, V i))) ≫ (⨆ i, V i).ι :=
          (Category.assoc _ _ _).symm
        rw [ha]
        first
          | exact ⟨_, rfl⟩
          | (rw [Scheme.comp_base]; exact ⟨_, rfl⟩)
          | exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rw [Scheme.Opens.range_ι] at hx
      exact hx
    refine Scheme.Cover.hom_ext ((pullback (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i))).openCoverOfIsOpenCover _ hcov)
      _ _ fun i => ?_
    change (a ⁻¹ᵁ V i).ι ≫ _ = (a ⁻¹ᵁ V i).ι ≫ _
    rw [← Category.assoc, loc i _ _ (a ∣_ V i), ← Category.assoc, loc i _ _ (a ∣_ V i)]
    · rw [morphismRestrict_ι]
      simp only [a, Category.assoc, ← morphismRestrict_ι, pullback.condition_assoc]
    · rw [morphismRestrict_ι]
      simp only [a, Category.assoc, ← morphismRestrict_ι]
  obtain ⟨m, hm, -⟩ := _root_.GlobalTheory.MorDescent.descend R S (⨆ i, V i).toScheme (p ⁻¹ᵁ (⨆ i, V i)).toScheme W π ((⨆ i, V i).ι ≫ y)
    (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) hπp hπs hSi hflat hsq (Z.homOfLE hV' ≫ h) heq
  refine ⟨hV', m, hm, fun W' g g' hg => ?_⟩
  have key := _root_.GlobalTheory.MorDescent.descend R S (⨆ i, V i).toScheme (p ⁻¹ᵁ (⨆ i, V i)).toScheme W' π ((⨆ i, V i).ι ≫ y)
    (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) hπp hπs hSi hflat hsq ((p ∣_ (⨆ i, V i)) ≫ g)
    (by rw [pullback.condition_assoc])
  exact key.unique rfl hg.symm

end GlobalTheory.MorDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCartesianSquareTrivialFirstAxis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

open GlobalTheory.LamRigid GlobalTheory.LamBiext GlobalTheory.MumRigidZero

noncomputable section

namespace GlobalTheory.MumRigidZeroPull

theorem lamVal_one_left_pull : ∀ {S S' : Scheme.{0}} (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') y).left z J J' = 1 := by
  intro S S' B B' _ _ _ _ M M' hM hM' hB' f β β₂ w hβ hsq hw hn T y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hL' : (abelian₂ B' M').IsLB := DVR.linComb_isLB _ hM' _ _
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have pt_one : ∀ T₀ : Over S', toBase hw₀ (1 : T₀ ⟶ B') = 1 := fun T₀ =>
    mul_eq_left.1 ((pt_mul 1 1).symm.trans (congrArg (toBase hw₀) (mul_one 1)))
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h
  let φ1 : Fin 1 → (B'.left ⟶ (G2 B').left) := fun _ => (lift (1 : B' ⟶ B') (𝟙 B')).left
  let ε1 : Fin 1 → ℤ := fun _ => 1
  have fe' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B') φ1) (flatε lamε ε1) := fun U _ h => by
    rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
    show 1 = (∏ i, h ((lift (1 : B' ⟶ B') (𝟙 B')).left ≫ lamφ B' i) ^ lamε i) ^ (1 : ℤ)
    rw [prod_lam, _root_.one_mul (𝟙 B')]
    apply Additive.ofMul.injective
    simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have fe : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) :=
    fun U _ h => by
      rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
      show 1 = (∏ i, h (((lift (1 : B' ⟶ B') (𝟙 B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)
      rw [Hlam, pt_one, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
  obtain ⟨g', hg', hv'⟩ := exists_gen hM' fe' (LB.oneGen M') (oneGen_isGen _)
  obtain ⟨g, hg, hv⟩ := exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M' z₀ J₀ →
      val (L := abelian₂ B' M') (nest M' (lamφ B') lamε φ1 ε1 g') r z₀ (ind B' J₀) = 1 := fun r z₀ J₀ hJ₀ => by
    refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
    simp only [adj_ind hM' hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
  have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M z₀ J₀ →
      val (L := abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 :=
    fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
  have Fp : ∀ {T₀ : Over S'} (c : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι)
      (J₀' : (T₀.left ⟶ B'.left) → M'.ι),
      pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B' J₀' (c.left ≫ φ1 k)) =
        lamVal w (lift (1 : T₀ ⟶ B') c).left z₀ J₀ J₀' := by
    intro T₀ c z₀ J₀ J₀'
    rw [pw_eq, Fin.prod_univ_one]
    show lamVal w (c ≫ lift (1 : B' ⟶ B') (𝟙 B')).left z₀ J₀ J₀' ^ (1 : ℤ) = _
    rw [comp_lift, comp_one_pt, Category.comp_id, zpow_one]
  have he : (1 : 𝟙_ (Over S') ⟶ B').left ≫ B'.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over S') ⟶ B')
  have E := rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B'.hom _ he (hG _ _ hB').2
    (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' y₀
      refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
      rw [Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S') ⟶ B'), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S')) y₀ J₁ J₁' hJ₁ hJ₁',
        _root_.mul_one])
    T.left y.left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
  rw [Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one] at E
  exact E.symm

end GlobalTheory.MumRigidZeroPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCartesianSquareTrivialSecondAxis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.LamRigid GlobalTheory.LamBiext GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumRigidZero

theorem lamVal_one_right_base : ∀ {S S' : Scheme.{0}} (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift y (1 : T ⟶ B')).left z J J' = 1 := by
  intro S S' B B' _ _ _ _ M M' hM hM' hB f β β₂ w hβ hsq hw hn T y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hL' : (abelian₂ B' M').IsLB := DVR.linComb_isLB _ hM' _ _
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have pt_one : ∀ T₀ : Over S', toBase hw₀ (1 : T₀ ⟶ B') = 1 := fun T₀ =>
    mul_eq_left.1 ((pt_mul 1 1).symm.trans (congrArg (toBase hw₀) (_root_.mul_one 1)))
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h
  let φ1 : Fin 1 → (B'.left ⟶ (G2 B').left) := fun _ => (lift (𝟙 B') (1 : B' ⟶ B')).left
  let ε1 : Fin 1 → ℤ := fun _ => 1
  have fe' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B') φ1) (flatε lamε ε1) := fun U _ h => by
    rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
    show 1 = (∏ i, h ((lift (𝟙 B') (1 : B' ⟶ B')).left ≫ lamφ B' i) ^ lamε i) ^ (1 : ℤ)
    rw [prod_lam, _root_.mul_one (𝟙 B')]
    apply Additive.ofMul.injective
    simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have fe : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) :=
    fun U _ h => by
      rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
      show 1 = (∏ i, h (((lift (𝟙 B') (1 : B' ⟶ B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)
      rw [Hlam, pt_one, _root_.mul_one (toBase hw₀ (𝟙 B'))]
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
  obtain ⟨g', hg', hv'⟩ := exists_gen hM' fe' (LB.oneGen M') (oneGen_isGen _)
  obtain ⟨g, hg, hv⟩ := exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M' z₀ J₀ →
      val (L := abelian₂ B' M') (nest M' (lamφ B') lamε φ1 ε1 g') r z₀ (ind B' J₀) = 1 := fun r z₀ J₀ hJ₀ => by
    refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
    simp only [adj_ind hM' hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
  have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M z₀ J₀ →
      val (L := abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 :=
    fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
  have Fp : ∀ {T₀ : Over S'} (c : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι)
      (J₀' : (T₀.left ⟶ B'.left) → M'.ι),
      pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B' J₀' (c.left ≫ φ1 k)) =
        lamVal w (lift c (1 : T₀ ⟶ B')).left z₀ J₀ J₀' := by
    intro T₀ c z₀ J₀ J₀'
    rw [pw_eq, Fin.prod_univ_one]
    show lamVal w (c ≫ lift (𝟙 B') (1 : B' ⟶ B')).left z₀ J₀ J₀' ^ (1 : ℤ) = _
    rw [comp_lift, comp_one_pt, Category.comp_id, zpow_one]
  have he : (1 : 𝟙_ (Over S') ⟶ B').left ≫ B'.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over S') ⟶ B')
  have E := rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B'.hom _ he (hG _ _ hB).2
    (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' y₀
      refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
      rw [Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S') ⟶ B'), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S')) y₀ J₁ J₁' hJ₁ hJ₁',
        _root_.mul_one])
    T.left y.left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
  rw [Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one] at E
  exact E.symm

end GlobalTheory.MumRigidZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericFibreExtendsUniformisedGr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_lam_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → ∀ (a : G₁ ⟶ G₂) (cA : A₁.A ⟶ A₂.A), IsMonHom a → IsMonHom cA → Gen₀ U₁ U₂ a cA → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA) (snd A₁.A A₁.A ≫ cA) : G2 A₁.A ⟶ G2 A₂.A).left) → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ a) (snd G₁ G₁ ≫ a) : G2 G₁ ⟶ G2 G₂).left) := by
  intro R _ _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ hS a cA ha hcA hgen hA
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G₁ G₁
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G₁ G₁
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ {D : DegData R J} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre J D A G) (x y : G₁ ⟶ G) (cx cy : A₁.A ⟶ A.A), Gen₀ U₁ U x cx → Gen₀ U₁ U y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U.LG.L U.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A.L A.isLB))) := by
    intro D A G _ _ U x y cx cy hx hy
    have hL := U.LG.isLB
    have hA := A.isLB
    have hgen := U.gen_hom
    have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hA₁ := A₁.isLB
  have hA₂ := A₂.isLB
  have lG₁ : (abelian₂ G₁ U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have lG₂ : (abelian₂ G₂ U₂.LG.L).IsLB := LB.isLB_linComb hL₂ _ _
  have lA₁ : (abelian₂ A₁.A A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have lA₂ : (abelian₂ A₂.A A₂.L).IsLB := LB.isLB_linComb hA₂ _ _
  have g₁ : Gen₀ U₁ U₁ (𝟙 G₁) (𝟙 A₁.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have cG₁ : cls (abelian₂ G₁ U₁.LG.L) lG₁ = cubeCls G₁ ![fst G₁ G₁ ≫ 𝟙 G₁, snd G₁ G₁ ≫ 𝟙 G₁] (cls _ hL₁) := by
    refine (cls_cubeLB G₁ (x2 G₁) hL₁).trans ?_
    congr 1
  have cA₁ : cls (abelian₂ A₁.A A₁.L) lA₁ = cubeCls A₁.A ![fst A₁.A A₁.A ≫ 𝟙 A₁.A, snd A₁.A A₁.A ≫ 𝟙 A₁.A] (cls _ hA₁) := by
    refine (cls_cubeLB A₁.A (x2 A₁.A) hA₁).trans ?_
    congr 1
  have cG₂ : cls ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ a) (snd G₁ G₁ ≫ a) : G2 G₁ ⟶ G2 G₂).left) (pull_isLB lG₂ _) =
      cubeCls G₂ ![fst G₁ G₁ ≫ a, snd G₁ G₁ ≫ a] (cls _ hL₂) := by
    rw [cls_pull lG₂ _ (pull_isLB lG₂ _)]
    refine (congrArg _ (cls_cubeLB G₂ (x2 G₂) hL₂)).trans ?_
    exact pull_cubeCls G₂ _ _ _ (fun i => by fin_cases i <;> simp [x2]) _
  have cA₂ : cls ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA) (snd A₁.A A₁.A ≫ cA) : G2 A₁.A ⟶ G2 A₂.A).left)
      (pull_isLB lA₂ _) = cubeCls A₂.A ![fst A₁.A A₁.A ≫ cA, snd A₁.A A₁.A ≫ cA] (cls _ hA₂) := by
    rw [cls_pull lA₂ _ (pull_isLB lA₂ _)]
    refine (congrArg _ (cls_cubeLB A₂.A (x2 A₂.A) hA₂)).trans ?_
    exact pull_cubeCls A₂.A _ _ _ (fun i => by fin_cases i <;> simp [x2]) _
  have eA : cubeCls A₁.A ![fst A₁.A A₁.A ≫ 𝟙 A₁.A, snd A₁.A A₁.A ≫ 𝟙 A₁.A] (cls _ hA₁) =
      cubeCls A₂.A ![fst A₁.A A₁.A ≫ cA, snd A₁.A A₁.A ≫ cA] (cls _ hA₂) :=
    cA₁.symm.trans (((cls_eq_iff lA₁ (pull_isLB lA₂ _)).2 hA).trans cA₂)
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G₁ ⊗ G₁) (η[G₁ ⊗ G₁]).left (Over.w _) _ _ lG₁ (pull_isLB lG₂ _) ?_
  refine (cls_eq_iff (pull_isLB lG₁ _) (pull_isLB (pull_isLB lG₂ _) _)).1 ?_
  rw [cls_pull lG₁ _ (pull_isLB lG₁ _), cls_pull (pull_isLB lG₂ _) _ (pull_isLB (pull_isLB lG₂ _) _), cG₁, cG₂,
    key U₁ (𝟙 G₁) (𝟙 G₁) (𝟙 A₁.A) (𝟙 A₁.A) g₁ g₁, key U₂ a a cA cA hgen hgen, eA]

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericOriginOneTautologicalBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem degPre_c_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) : D.c 0 = 1 := by
  have h : D.c 0 * D.c 0 = D.c 0 := by
    have := D.c_add 0 0
    rw [add_zero] at this
    exact this.symm
  exact mul_eq_left.1 h

theorem val_tau_zero_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (hT : D.TauBimult)
    (z : (TK V).left) (J : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val (D.tau 0 0) (𝟙 _) z J = 1 := by
  have h := (val_mul hJ _ _ (𝟙 _)).symm.trans ((val_corr hJ (hT 0 0 0) (𝟙 _)).trans (val_mul hJ _ _ (𝟙 _)))
  have e : ∀ a : D.X, a = 0 → val (D.tau a 0) (𝟙 _) z J = val (D.tau 0 0) (𝟙 _) z J := by
    rintro a rfl; rfl
  rw [e _ (add_zero 0)] at h
  have f : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) (𝟙 _) z J = 1 := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
    show cubV D.cub z J (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0) = 1
    rw [degPre_c_zero, MonObj.comp_one]
    exact (isCub_cubV D.cub hJ).face _ _
  rw [f, _root_.mul_one] at h
  exact mul_eq_left.1 h.symm

theorem tautBase_c₀_zero {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) : T.c₀ 0 = 1 :=
  mul_eq_left.1 ((T.c₀_add 0 0).symm.trans (by rw [add_zero]))

theorem val_τ₀_zero_zero {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W)
    (z : (𝟙_ (Over (Sp W))).left) (J) (hJ : Good T.M.L z J) : val (T.τ₀ 0 0) (𝟙 _) z J = 1 := by
  have h := T.τ₀_add 0 0 0 z J hJ
  have f : cubV T.cub z J (T.c₀ 0) (T.c₀ 0) (T.c₀ 0) = 1 := by
    rw [tautBase_c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
  rw [f, _root_.mul_one, add_zero] at h
  exact mul_eq_left.1 h.symm

theorem val_τ₀_zero_at {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {Z : Scheme.{0}}
    (r : Z ⟶ (𝟙_ (Over (Sp W))).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (hJ : Good T.M.L z J) :
    val (T.τ₀ 0 0) r z J = 1 := by
  have c : LB.Gen.Corr T.M.L _ _ _ _ (T.τ₀ 0 0) (LB.oneGen T.M.L) :=
    corr_of_val T.M.isLB fun y J' hJ' => (val_τ₀_zero_zero T y J' hJ').trans (val_one _).symm
  exact (val_corr hJ c r).trans (val_one r)

theorem lamVal_origin_of_from : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (z : (TK V).left) (J : ((TK V).left ⟶ T.B.left) → T.M.L.ι) (J' : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι), Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : TK V ⟶ D.P.A) (1 : TK V ⟶ D.P.A)).left z J J' = 1 := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hT hF z J J' hJ hJ'
  obtain ⟨k, hk, hv⟩ := hF.2.2.2.2 0 0
  have h := hv z J J' hJ hJ'
  have k1 : k = 1 := by
    ext
    rw [hk]
    simp
  have e0 : ((n : ℤ) • e 0) = 0 := by rw [map_zero, smul_zero]
  rw [k1, val_tau_zero_zero D hT z J' hJ', e0, val_τ₀_zero_at T _ z J hJ, degPre_c_zero, MonObj.comp_one] at h
  have u1 : unitOn (1 : (FractionRing V)ˣ) = 1 := map_one _
  simp only [u1, map_one, _root_.one_mul, _root_.mul_one] at h
  exact h.symm

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftPresystemSquareZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem pre_nonempty : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀), (∀ T, Algebra.Smooth R₀ (F.obj T)) → Nonempty (Pre I π F) := by
  intro R R₀ _ _ I hI π hπ hk C _ F hF
  have h := fun T => _root_.GlobalTheory.smooth_lifts_over_sqZero R R₀ I hI π hπ hk (F.obj T) (hF T)
  choose B iB aB p hs hp hker hsm using h
  letI := iB
  letI := aB
  have hl : ∀ {T T' : C} (a : T ⟶ T'), ∃ ρ : B T →ₐ[R] B T', ∀ b, p T' (ρ b) = mp F a (p T b) :=
    fun {T T'} a => homLift R R₀ I hI π hπ hk (B T) (F.obj T) (p T) (hs T) (hp T) (hker T)
      (B T') (F.obj T') (p T') (hs T') (hp T') (hker T') (mp F a)
  exact ⟨{ B := fun T => CommAlgCat.of R (B T)
           p := p
           semi := hs
           surj := hp
           ker := hker
           smooth := hsm
           ρ := fun a => (hl a).choose
           nat := fun a b => (hl a).choose_spec b }⟩

end GlobalTheory.Obs
end
end

