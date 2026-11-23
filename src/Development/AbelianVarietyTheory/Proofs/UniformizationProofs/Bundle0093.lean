module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyGtCoordOfIsGt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedStabiliser
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Stabiliser

theorem comp_eq_iff_range_subset {S : Scheme.{0}} {T X Z : Over S} [IsReduced T.left]
    [IsSeparated Z.hom] (f g : X ⟶ Z) (x : T ⟶ X) :
    x ≫ f = x ≫ g ↔ Set.range x.left ⊆ Set.range (equalizer.ι f g).left := by
  constructor
  · intro h
    rintro _ ⟨t, rfl⟩
    refine ⟨(equalizer.lift x h).left t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  · intro h
    have hs : Surjective (pullback.fst x.left (equalizer.ι f g).left) := by
      refine ⟨Set.range_eq_univ.1 ?_⟩
      rw [Scheme.Pullback.range_fst]
      exact Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩
    have hc : (equalizer.ι f g).left ≫ f.left = (equalizer.ι f g).left ≫ g.left :=
      congrArg CommaMorphism.left (equalizer.condition f g)
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated Z.hom
      ((Over.w _).trans (Over.w _).symm) (pullback.fst x.left (equalizer.ι f g).left) ?_)
    rw [Over.comp_left, Over.comp_left, pullback.condition_assoc, pullback.condition_assoc, hc]

def stab {S : Scheme.{0}} {B Z : Over S} [GrpObj B] (φ : B ⟶ Z) : Subgroup (𝟙_ (Over S) ⟶ B) :=
  have key : ∀ a b : 𝟙_ (Over S) ⟶ B, (toUnit B ≫ (b * a)) * 𝟙 B =
      ((toUnit B ≫ a) * 𝟙 B) ≫ ((toUnit B ≫ b) * 𝟙 B) := fun a b => by
    rw [MonObj.comp_mul, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      toUnit_unique (_ ≫ toUnit B) (toUnit B), _root_.mul_assoc]
  have one : (toUnit B ≫ (1 : 𝟙_ (Over S) ⟶ B)) * 𝟙 B = 𝟙 B := by
    rw [MonObj.comp_one, _root_.one_mul]
  { carrier := {x | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}
    mul_mem' := fun {a b} ha hb => by
      rw [Set.mem_ofPred_eq] at ha hb ⊢
      rw [key, Category.assoc, ha, hb]
    one_mem' := by rw [Set.mem_ofPred_eq, one, Category.id_comp]
    inv_mem' := fun {a} ha => by
      rw [Set.mem_ofPred_eq] at ha ⊢
      conv_lhs => rw [← ha]
      rw [← Category.assoc, ← key, mul_inv_cancel, one, Category.id_comp] }

theorem exists_closed_stabiliser : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] (φ : B ⟶ Z), ∃ (C : Subgroup (𝟙_ _ ⟶ B)) (W : Set B.left), IsClosed W ∧ (∀ x, x ∈ C ↔ ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ) ∧ ∀ x, x ∈ C ↔ Set.range x.left ⊆ W := by
  intro K _ _ B _ _ hB Z _ φ
  have := hB.smooth
  have : IsReduced B.left := GlobalTheory.isReduced_of_smooth_of_isReduced B.hom
  have : IsReduced (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  refine ⟨stab φ, ⋂ z : 𝟙_ _ ⟶ B, Set.range
    (equalizer.ι ((𝟙 B * (toUnit B ≫ z)) ≫ φ) (toUnit B ≫ z ≫ φ)).left,
    isClosed_iInter fun z => (Scheme.Hom.isClosedEmbedding _).isClosed_range,
    fun _ => Iff.rfl, fun x => ?_⟩
  have e₁ : ∀ z : 𝟙_ _ ⟶ B, x ≫ (𝟙 B * (toUnit B ≫ z)) ≫ φ = z ≫ ((toUnit B ≫ x) * 𝟙 B) ≫ φ := by
    intro z
    simp only [← Category.assoc, MonObj.comp_mul, Category.comp_id]
    rw [toUnit_unique (x ≫ toUnit B) (𝟙 _), toUnit_unique (z ≫ toUnit B) (𝟙 _),
      Category.id_comp, Category.id_comp]
  have e₂ : ∀ z : 𝟙_ _ ⟶ B, x ≫ toUnit B ≫ z ≫ φ = z ≫ φ := by
    intro z
    rw [← Category.assoc, toUnit_unique (x ≫ toUnit B) (𝟙 _), Category.id_comp]
  rw [Set.subset_iInter_iff]
  simp only [← comp_eq_iff_range_subset, e₁, e₂]
  refine ⟨fun h z => congrArg (z ≫ ·) h, fun h => ?_⟩
  refine Over.OverMorphism.ext (GlobalTheory.ComplexPoints.hom_ext_of_points B.hom Z.hom
    ((Over.w _).trans (Over.w _).symm) fun y hy => ?_)
  exact congrArg CommaMorphism.left (h (Over.homMk y hy))

end GlobalTheory.Stabiliser
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinsetPointExtendsValuationSubalgebra
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_finset_point_extends_valuationSubalgebra (V F : Type) [CommRing V] [Field F]
    [Algebra V F] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f]
    (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W →
      (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) →
      ∃ y : Spec (CommRingCat.of W) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V W)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ y = x := by
  first
  | exact @_root_.GlobalTheory.AffineFactorExists.exists_finset_extends
  | exact _root_.GlobalTheory.AffineFactorExists.exists_finset_extends
  | (apply _root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> assumption)
  | (intros; apply _root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AffineFactorExists.exists_finset_extends ..)

theorem exists_finset_points_extend_valuationSubalgebra : ∀ (V F : Type) [CommRing V] [Field F] [Algebra V F] (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom] (s : Set (Spec (CommRingCat.of F) ⟶ B.left)), s.Finite → (∀ x ∈ s, x ≫ B.hom = (Spec.map (CommRingCat.ofHom (algebraMap V F)))) → ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W → (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) → ∀ x ∈ s, ∃ y : Spec (CommRingCat.of W) ⟶ B.left, y ≫ B.hom = (Spec.map (CommRingCat.ofHom (algebraMap V W))) ∧ (Spec.map (CommRingCat.ofHom (algebraMap W F))) ≫ y = x := by
  intro V F _ _ _ B _ s hs hx
  classical
  choose t ht using fun x : s =>
    exists_finset_point_extends_valuationSubalgebra V F B.hom x.1 (hx x.1 x.2)
  haveI := hs.fintype
  refine ⟨Finset.univ.biUnion t, fun W hW h x hxs => ht ⟨x, hxs⟩ W hW fun a ha => h a ?_⟩
  exact Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, ha⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtCoordOfTorusQuotient
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotCoord

open WeightGen

theorem exists_flat {X B Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (B ⟶ X)} {ε : K → ℤ}
    (f : Y ⟶ B) (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => f ≫ φ k) j →
        r z ∈ ((LB.LinComb L φ ε).pull f).U (fun _ => j) ∧
        gm r z (LB.wchart L (fun k => f ≫ φ k) j) (t.s j) =
          gm r z (((LB.LinComb L φ ε).pull f).U (fun _ => j)) (u.s fun _ => j) := by
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => f ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull f).U (fun _ => j) :=
    fun _ _ hy => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (u.s fun _ => j)⟩, fun j j' => unit_ext fun y hy => ?_,
    fun Z r z j hj => ⟨le j hj, gm_res r z (le j) hj _⟩⟩
  refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 Y) y (le j) hy.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)
        ((gm_res _ y _ hy _).trans (gm_res (𝟙 Y) y (le j') hy.2 _)))).symm)
  refine (gm_gen hu (𝟙 Y) y (le j hy.1) (le j' hy.2)).trans (congrArg (· * _) ?_)
  refine (gm_pull_g _ f (𝟙 Y) y _ _ (le j hy.1) (le j' hy.2)).trans
    ((gm_linComb L φ ε (𝟙 Y ≫ f) y j j' (mem_pull.1 (le j hy.1)) (mem_pull.1 (le j' hy.2))).trans ?_)
  simp only [Category.assoc]

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

noncomputable abbrev tact (i : splitTorus S X ⟶ G) : splitTorus S X ⊗ G ⟶ G :=
  lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]

theorem comp_tact (i : splitTorus S X ⟶ G) {Z : Over S} (ρ : Z ⟶ splitTorus S X ⊗ G) :
    ρ ≫ tact i = ((ρ ≫ fst _ _) ≫ i) * (ρ ≫ snd _ _) := by
  rw [Hom.mul_def, comp_lift_assoc, Category.assoc]

theorem exists_wt_gen (i : splitTorus S X ⟶ G) {Y B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K]
    {φ : K → (B ⟶ Y)} {ε : K → ℤ} (f : G.left ⟶ B)
    (hf : (tact i).left ≫ f = (snd (splitTorus S X) G).left ≫ f) (χ : X)
    (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen) (hw : ∀ j, IsWt i _ (u.s j).val χ) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X ⊗ G).left) (z : Z) (J), Good L z J →
        val t (r ≫ (tact i).left) z J = wt X G χ Z r z * val t (r ≫ (snd (splitTorus S X) G).left) z J := by
  obtain ⟨t, ht, hv⟩ := exists_flat f u hu
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  have m := hJ.mem (fun k => f ≫ φ k) (r ≫ (snd (splitTorus S X) G).left)
  have m' := hJ.mem (fun k => f ≫ φ k) (r ≫ (tact i).left)
  have e : ∀ k, J ((r ≫ (tact i).left) ≫ f ≫ φ k) = J ((r ≫ (snd (splitTorus S X) G).left) ≫ f ≫ φ k) :=
    fun k => by rw [Category.assoc, Category.assoc, reassoc_of% hf]
  rw [funext e] at m'
  rw [val_of _ (r ≫ (tact i).left) z J _ e]
  obtain ⟨n, v⟩ := hv Z _ z _ m
  obtain ⟨n', v'⟩ := hv Z _ z _ m'
  refine v'.trans (Eq.trans ?_ (congrArg _ v).symm)
  let Z' : Over S := Over.mk (r ≫ (splitTorus S X ⊗ G).hom)
  let ρ : Z' ⟶ splitTorus S X ⊗ G := Over.homMk r rfl
  have k := WtBundle.gm_of_isWt (hw fun _ => fun k => J ((r ≫ (snd (splitTorus S X) G).left) ≫ f ≫ φ k))
    (ρ ≫ fst _ _) (ρ ≫ snd _ _) z (by rw [← comp_tact]; exact n') n
  rw [← comp_tact, ← gm_charUnit] at k
  exact k

variable (Q : TQ G X)

theorem tact_q : tact Q.i ≫ Q.q = snd _ _ ≫ Q.q := WtBundle.act_comp Q (fst _ _) (snd _ _)

theorem exists_const (hG : GlobalFnsSt) (f : Γ(G.left, ⊤))
    (hf : (tact Q.i).left.appTop.hom f = (snd (splitTorus S X) G).left.appTop.hom f) :
    ∃ c, G.hom.appTop.hom c = f := by
  have := Q.q_affine
  obtain ⟨b, hb⟩ := (invariant_functions_descend S G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat
    Q.q_surj inferInstance Q.isKernel ⊤).2.2 f (fun Z t g h₁ h₂ => by
      have e₁ : (t ≫ Q.i) * g = lift t g ≫ tact Q.i := by
        rw [comp_tact, lift_fst, lift_snd]
      have key : ((t ≫ Q.i) * g).left.appTop.hom f = g.left.appTop.hom f := by
        rw [e₁, Over.comp_left, FunDescent.comp_appTop_apply, hf, ← FunDescent.comp_appTop_apply,
          ← Over.comp_left, lift_snd]
      rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.app_eq_appLE] at key
      exact key)
  obtain ⟨c, hc⟩ := (hG S Q.B Q.isAb).2 b
  refine ⟨c, ?_⟩
  rw [← Over.w Q.q, FunDescent.comp_appTop_apply, hc]
  exact hb

end

theorem exists_iso_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    ∃ e : G' ≅ (Over.pullback f).obj G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst G.hom f = F := by
  let e : G' ≅ (Over.pullback f).obj G := Over.isoMk h.1.isoPullback h.1.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst G.hom f = F := h.1.isoPullback_hom_fst
  refine ⟨e, isMonHom_of_mul _ fun T x y => ?_, he⟩
  have h₁ := h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl
  have h₂ := (isGrpPullback_pullback G f).2 T (x ≫ e.hom) (y ≫ e.hom) (pushPt h.1.w x) (pushPt h.1.w y)
    (by rw [Over.comp_left, Category.assoc, he]; rfl) (by rw [Over.comp_left, Category.assoc, he]; rfl)
  refine Over.OverMorphism.ext ((isGrpPullback_pullback G f).1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  rw [← h₂, h₁, Over.comp_left, Category.assoc, he]

section
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem prod_transl {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 2, h (p.left ≫ ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] k) ^
      (![-1, 1] : Fin 2 → ℤ) k = (h ((toUnit T ≫ D.c χ) * p).left)⁻¹ * h p.left := by
  have e : p ≫ ((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A) = (toUnit T ≫ D.c χ) * p := by
    rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]
  rw [Fin.prod_univ_two, ← e]
  show h (p ≫ ((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A)).left ^ (-1 : ℤ) * h (p.left ≫ 𝟙 _) ^ (1 : ℤ) = _
  rw [Category.comp_id, zpow_one, zpow_neg, zpow_one]

theorem exists_four {T : Over (Spec (CommRingCat.of R))} (q : T ⟶ D.P.A) (σ : T ⟶ T) (hσ : σ ≫ q = 1) (χ : D.X)
    (f : T.left ⟶ D.P.A.left) (hf : q.left = f)
    (t₀ : LB.Gen (LB.LinComb D.P.L (K := Fin 2)
      (fun k => f ≫ ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] k) ![-1, 1])) (g₀ : t₀.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val t₀ r z J * (val t₀ (r ≫ σ.left) z J)⁻¹ := by
  subst hf
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := D.Oφ q χ) (ε' := Oinvε) (fun U _ h => by
      have a := prod_transl D (σ ≫ q) χ h
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_transl D q χ h) (DVR.prod_neg _ _
          ((Finset.prod_congr rfl fun k _ =>
            congrArg (fun g => h g ^ (![-1, 1] : Fin 2 → ℤ) k) (Category.assoc _ _ _).symm).trans a))) ?_
      rw [prod_Oφ, hσ, _root_.mul_one, mul_comm q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen D.P.L _ _ _ _ t₀ (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ t₀ σ.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ g₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ g₀ _)))
  exact ⟨t, ht, fun Z r z J hJ => by rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ]⟩

end

end GlobalTheory.QuotCoord

namespace GlobalTheory

open WeightGen QuotCoord

theorem exists_gtCoord_of_torusQuotient : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (Q : TQ (thickObj R I e G) D.X) (b : Q.B.left ⟶ D.P.A.left), IsGrpPullback Q.B D.P.A (thick R I e) b → (∀ χ, ∃ u : LB.Gen ((LB.LinComb D.P.L (K := Fin 2) ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] ![-1, 1]).pull (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ) → ∃ g : GtCoord I D e G, g.i = Q.i ∧ g.pG.left = Q.q.left ≫ b := by
  intro hG R _ _ _ I D e G _ _ Q b hb hu
  obtain ⟨β, hβ, hβb⟩ : ∃ β : Q.B ≅ thickObj R I e D.P.A, IsMonHom β.hom ∧
    β.hom.left ≫ pullback.fst D.P.A.hom (thick R I e) = b := exists_iso_pullback hb
  have hL := D.P.isLB
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  let F := Over.map (thick R I e)
  have hp : (F.map (Q.q ≫ β.hom) ≫ D.prBe I e).left = Q.q.left ≫ b := by
    rw [← hβb, ← Category.assoc]
    rfl
  have unit_q : F.map η[thickObj R I e G] ≫ F.map (Q.q ≫ β.hom) ≫ D.prBe I e = 1 := by
    rw [← F.map_comp_assoc, IsMonHom.one_hom]
    exact Over.OverMorphism.ext (unit_fst (thick R I e) D.P.A)
  have hπ : F.map (tact Q.i) ≫ F.map (toUnit _) = F.map (snd _ _) ≫ F.map (toUnit _) := by
    rw [← F.map_comp, ← F.map_comp, comp_toUnit, comp_toUnit]
  obtain ⟨t, g, m, u, w⟩ := exists_normalised D (F.map (Q.q ≫ β.hom) ≫ D.prBe I e)
    (F.map (toUnit _)) (F.map η[thickObj R I e G])
    (by rw [← F.map_comp, comp_toUnit, toUnit_unit, F.map_id]) unit_q
    (F.map (tact Q.i)) (F.map (snd _ _))
    (by rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← Category.assoc (tact Q.i), tact_q Q,
      Category.assoc])
    hπ (QuotCoord.exists_const Q hG) (fun χ => wt D.X (thickObj R I e G) χ)
    (fun χ χ' Z r z => wt_add _ _ _ _ Z r z)
    (fun χ => by
      obtain ⟨u, gu, wu⟩ := hu χ
      obtain ⟨t₀, g₀, w₀⟩ := exists_wt_gen Q.i (Q.q.left ≫ b) (by
        rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, tact_q]) χ u gu wu
      obtain ⟨t, g, v⟩ := exists_four D (F.map (Q.q ≫ β.hom) ≫ D.prBe I e)
        (F.map (toUnit _) ≫ F.map η[thickObj R I e G])
        (by rw [Category.assoc, unit_q, MonObj.comp_one]) χ _ hp t₀ g₀
      refine ⟨t, g, fun Z r z J hJ => ?_⟩
      have k : (F.map (tact Q.i)).left ≫ (F.map (toUnit _) ≫ F.map η[thickObj R I e G]).left =
          (F.map (snd _ _)).left ≫ (F.map (toUnit _) ≫ F.map η[thickObj R I e G]).left :=
        congrArg (fun g => g.left) (show F.map (tact Q.i) ≫ F.map (toUnit _) ≫ F.map η[thickObj R I e G] =
          F.map (snd _ _) ≫ F.map (toUnit _) ≫ F.map η[thickObj R I e G] by rw [reassoc_of% hπ])
      rw [v _ _ z J hJ, v _ _ z J hJ, Category.assoc, Category.assoc, k, ← _root_.mul_assoc]
      exact congrArg (· * _) (w₀ Z r z J hJ))
  refine ⟨{ q := Q.q ≫ β.hom
            q_hom := inferInstance
            q_flat := by rw [Over.comp_left]; infer_instance
            q_surj := by rw [Over.comp_left]; infer_instance
            q_affine := by rw [Over.comp_left]; infer_instance
            i := Q.i
            i_hom := inferInstance
            isKernel := Q.isKernel.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) β (by simp)
              (toUnit_unique _ _) (by simp) (by simp)
            t := t
            t_gen := g
            t_mul := m
            t_unit := fun χ => corr_of_val hL fun y J hJ => ?_
            t_weight := fun χ => corr_of_val hL fun y J hJ => ?_ }, rfl, hp⟩
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact u χ y J hJ
  · exact (val_pull hJ _ _ _).trans ((w χ _ (𝟙 _) y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueAbelianPartImageAdicCompletePoint
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.PointImage

def levelHom {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (n : ℕ) :
    R ⧸ I ^ n →+* W ⧸ (I.map f) ^ n :=
  Ideal.quotientMap _ f (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)

theorem isPushout_level {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (n : ℕ) :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))
      (CommRingCat.ofHom (Ideal.Quotient.mk ((I.map f) ^ n))) (CommRingCat.ofHom (levelHom f I n)) := by
  have w : CommRingCat.ofHom f ≫ CommRingCat.ofHom (Ideal.Quotient.mk ((I.map f) ^ n)) =
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)) ≫ CommRingCat.ofHom (levelHom f I n) := rfl
  have hk : ∀ s : PushoutCocone (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))),
      ∀ a ∈ (I.map f) ^ n, s.inl.hom a = 0 := by
    intro s a ha
    rw [← Ideal.map_pow] at ha
    have : (I ^ n).map f ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      have h := congrArg (fun φ => φ.hom y) s.condition
      change s.inl.hom (f y) = s.inr.hom (Ideal.Quotient.mk _ y) at h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero] at h
      exact h
    exact this ha
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (hk s))) (fun s => rfl)
    (fun s => ?_) (fun s m h _ => ?_)⟩⟩
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom s.condition
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom h

theorem isPullback_level {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (e : ℕ) :
    IsPullback (adicLevelι (I.map f) (e + 1)) (Spec.map (CommRingCat.ofHom (levelHom f I (e + 1))))
      (Spec.map (CommRingCat.ofHom f)) (thick R I e) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_level f I (e + 1))

theorem thick_mono' (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem existsUnique_image {R W : Type} [CommRing R] [CommRing W] [IsLocalRing W] (f : R →+* W)
    (I : Ideal R) [IsAdicComplete (I.map f) W] {G B : Scheme.{0}}
    (pG : G ⟶ Spec (CommRingCat.of R)) (pB : B ⟶ Spec (CommRingCat.of R))
    {P : ℕ → Scheme.{0}} (fst : ∀ e, P e ⟶ G)
    (snd : ∀ e, P e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (hP : ∀ e, IsPullback (fst e) (snd e) pG (thick R I e))
    (τ : ∀ e, P e ⟶ P (e + 1)) (hm : ∀ e, τ e ≫ fst (e + 1) = fst e)
    (φ : ∀ e, P e ⟶ B) (hφ : ∀ e, φ e ≫ pB = snd e ≫ thick R I e)
    (hc : ∀ e, τ e ≫ φ (e + 1) = φ e)
    (x : Spec (CommRingCat.of W) ⟶ G) (hx : x ≫ pG = Spec.map (CommRingCat.ofHom f)) :
    ∃! b : Spec (CommRingCat.of W) ⟶ B, b ≫ pB = Spec.map (CommRingCat.ofHom f) ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ P e),
        xe ≫ fst e = r ≫ x → xe ≫ φ e = r ≫ b := by
  have hw : ∀ e, (adicLevelι (I.map f) (e + 1) ≫ x) ≫ pG =
      Spec.map (CommRingCat.ofHom (levelHom f I (e + 1))) ≫ thick R I e := fun e => by
    rw [← (isPullback_level f I e).w, Category.assoc, hx]
  choose y hy hy2 using fun e => (hP e).exists_lift _ _ (hw e)
  have hmono : ∀ e, Mono (fst e) := fun e =>
    (MorphismProperty.monomorphisms Scheme).of_isPullback (hP e).flip (thick_mono' R I e)
  have hfam : IsAdicFamily (I.map f) (fun e => y e ≫ φ e) := by
    intro e
    have : adicLevelMap (I.map f) (Nat.le_succ (e + 1)) ≫ y (e + 1) = y e ≫ τ e := by
      rw [← cancel_mono (fst (e + 1)), Category.assoc, hy,
        adicLevelMap_ι_assoc, Category.assoc, hm, hy]
    change _ ≫ y (e + 1) ≫ φ (e + 1) = y e ≫ φ e
    rw [← hc e, ← Category.assoc, this, Category.assoc]
  obtain ⟨g, ⟨hg, hg'⟩, hu⟩ := existsUnique_over_of_isAdicFamily (Spec.map (CommRingCat.ofHom f))
    pB hfam (fun e => by
      rw [(isPullback_level f I e).w, ← hy2, Category.assoc, hφ, Category.assoc])
  refine ⟨g, ⟨hg, fun e Z r xe h => ?_⟩, fun b hb => ?_⟩
  · have hr : r ≫ Spec.map (CommRingCat.ofHom f) = (xe ≫ snd e) ≫ thick R I e := by
      rw [← hx, ← Category.assoc, ← h, Category.assoc, (hP e).w, Category.assoc]
    obtain ⟨l, hl, -⟩ := (isPullback_level f I e).exists_lift _ _ hr
    have hxe : xe = l ≫ y e := by
      rw [← cancel_mono (fst e), h, ← hl, Category.assoc, Category.assoc, hy]
    rw [hxe, ← hl, Category.assoc, Category.assoc, hg']
  · exact hu b ⟨hb.1, fun e => (hb.2 e _ _ (y e) (hy e)).symm⟩

theorem main : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, ∃! b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ x
  obtain ⟨g, ⟨hg, hg'⟩, hu⟩ := existsUnique_image (algebraMap V W) (IsLocalRing.maximalIdeal V)
    G.hom a.B.hom (P := fun e => (thickObj V (IsLocalRing.maximalIdeal V) e G).left)
    (fun e => (fstG _ e G).left) (fun e => (thickObj V (IsLocalRing.maximalIdeal V) e G).hom)
    (fun e => IsPullback.of_hasPullback G.hom (thick V _ e)) (fun e => thickMap V _ e G)
    (fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _))
    (fun e => (t.l e).Q.q.left ≫ a.b e)
    (fun e => by
      obtain ⟨h, -⟩ := a.b_pb e
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    (fun e => by rw [← a.b_β e, ← Category.assoc, ← t.β_q e, Category.assoc])
    x.left (Over.w x)
  exact ⟨Over.homMk g hg, hg', fun b hb => Over.OverMorphism.ext (hu b.left ⟨Over.w b, hb⟩)⟩

end GlobalTheory.UU.PointImage
end
end

