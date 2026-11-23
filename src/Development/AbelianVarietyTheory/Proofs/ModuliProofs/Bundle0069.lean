module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CocycleGlue

theorem exists_desc (D : Scheme.GlueData.{0}) {S : Scheme.{0}} (p : ∀ i, D.U i ⟶ S)
    (h : ∀ i j, D.f i j ≫ p i = (D.t i j ≫ D.f j i) ≫ p j) :
    ∃ F : D.glued ⟶ S, ∀ i, D.ι i ≫ F = p i := by
  exact GlobalTheory.CoverGlue.exists_hom (ψ := D.ι) (fun i => inferInstance)
    (fun x => by
      obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
      exact ⟨i, y, hy⟩)
    p (B := fun i j => D.V (i, j)) (a := fun i j => D.f i j) (b := fun i j => D.t i j ≫ D.f j i)
    (fun i j => IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)) h

theorem exists_glue {S : Scheme.{0}} {I : Type} (V X : I → Scheme.{0}) (κ : ∀ i, V i ⟶ S)
    (hκ : ∀ i, IsOpenImmersion (κ i)) (g : ∀ i, X i ⟶ V i) (B : I → I → Scheme.{0})
    (a : ∀ i j, B i j ⟶ X i) (b : ∀ i j, B i j ⟶ X j)
    (ha : ∀ i j, IsPullback (a i j) (b i j ≫ g j) (g i ≫ κ i) (κ j))
    (hb : ∀ i j, IsPullback (b i j) (a i j ≫ g i) (g j ≫ κ j) (κ i))
    (hc : ∀ i j k (T : Scheme.{0}) (x : T ⟶ B i j) (y : T ⟶ B j k) (z : T ⟶ B i k),
      x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) :
    ∃ (A : Scheme.{0}) (F : A ⟶ S) (ψ : ∀ i, X i ⟶ A),
      (∀ i, IsPullback (ψ i) (g i) F (κ i)) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  classical
  have hma : ∀ i j, IsOpenImmersion (a i j) := fun i j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (ha i j).flip (hκ j)
  have mono_a : ∀ i j, Mono (a i j) := fun i j => by
    have := hma i j
    infer_instance
  have mono_κ : ∀ i, Mono (κ i) := fun i => by
    have := hκ i
    infer_instance
  have ext_a : ∀ i j {T : Scheme.{0}} (x y : T ⟶ B i j), x ≫ a i j = y ≫ a i j → x = y :=
    fun i j _ x y h => (mono_a i j).right_cancellation x y h
  have ext_κ : ∀ i {T : Scheme.{0}} (x y : T ⟶ V i), x ≫ κ i = y ≫ κ i → x = y :=
    fun i _ x y h => (mono_κ i).right_cancellation x y h
  have hbw : ∀ i j, b i j ≫ g j ≫ κ j = a i j ≫ g i ≫ κ i := fun i j => by
    simpa only [Category.assoc] using (hb i j).w
  have iso_a : ∀ i, IsIso (a i i) := fun i => by
    have hw : a i i ≫ g i = b i i ≫ g i := ext_κ i _ _ (by
      rw [Category.assoc]
      exact (ha i i).w)
    refine ⟨⟨(ha i i).lift (𝟙 _) (g i) (by simp), ?_, (ha i i).lift_fst _ _ _⟩⟩
    apply ext_a i i
    rw [Category.assoc, (ha i i).lift_fst, Category.comp_id, Category.id_comp]
  have iso_b : ∀ i, IsIso (b i i) := fun i => by
    have hw : b i i ≫ g i = a i i ≫ g i := ext_κ i _ _ (by
      rw [Category.assoc]
      exact (hb i i).w)
    have hmb : Mono (b i i) := by
      have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hb i i).flip (hκ i)
      infer_instance
    refine ⟨⟨(hb i i).lift (𝟙 _) (g i) (by simp), ?_, (hb i i).lift_fst _ _ _⟩⟩
    apply hmb.right_cancellation
    rw [Category.assoc, (hb i i).lift_fst, Category.comp_id, Category.id_comp]
  have diag : ∀ i, a i i = b i i := fun i => by
    have := iso_a i
    have := iso_b i
    have h := hc i i i (B i i) (𝟙 _) (b i i ≫ inv (a i i)) (𝟙 _) (by simp) (by simp)
    have h2 : inv (a i i) ≫ b i i = 𝟙 _ := by
      rw [← cancel_epi (b i i)]
      simpa using h
    rw [IsIso.inv_comp_eq, Category.comp_id] at h2
    exact h2.symm
  have ht : ∀ i j, ∃ t : B i j ⟶ B j i, t ≫ a j i = b i j ∧ t ≫ b j i = a i j := fun i j => by
    have := iso_a i
    refine ⟨(ha j i).lift (b i j) (a i j ≫ g i) (hb i j).w, (ha j i).lift_fst _ _ _, ?_⟩
    have h := hc i j i (B i j) (𝟙 _) ((ha j i).lift (b i j) (a i j ≫ g i) (hb i j).w)
      (a i j ≫ inv (a i i)) (by rw [IsPullback.lift_fst, Category.id_comp]) (by simp)
    rw [h, ← diag i]
    simp
  choose t ht_a ht_b using ht
  have t_id : ∀ i, t i i = 𝟙 _ := fun i =>
    ext_a i i _ _ (by rw [ht_a, Category.id_comp, diag])
  have t_inv : ∀ i j, t i j ≫ t j i = 𝟙 _ := fun i j =>
    ext_a i j _ _ (by rw [Category.assoc, ht_a, ht_b, Category.id_comp])
  have ht' : ∀ i j k, ∃ τ : pullback (a i j) (a i k) ⟶ pullback (a j k) (a j i),
      τ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j ∧
        τ ≫ pullback.fst _ _ ≫ a j k = pullback.fst _ _ ≫ b i j := fun i j k => by
    have w : (pullback.fst (a i j) (a i k) ≫ b i j) ≫ g j ≫ κ j =
        (pullback.snd (a i j) (a i k) ≫ b i k ≫ g k) ≫ κ k := by
      calc (pullback.fst (a i j) (a i k) ≫ b i j) ≫ g j ≫ κ j
          = pullback.fst (a i j) (a i k) ≫ a i j ≫ g i ≫ κ i := by rw [Category.assoc, hbw]
        _ = pullback.snd (a i j) (a i k) ≫ a i k ≫ g i ≫ κ i := by rw [pullback.condition_assoc]
        _ = (pullback.snd (a i j) (a i k) ≫ b i k ≫ g k) ≫ κ k := by
          rw [← hbw]
          simp only [Category.assoc]
    refine ⟨pullback.lift ((ha j k).lift _ _ w) (pullback.fst _ _ ≫ t i j) ?_, pullback.lift_snd _ _ _, ?_⟩
    · rw [IsPullback.lift_fst, Category.assoc, ht_a]
    · rw [pullback.lift_fst_assoc, IsPullback.lift_fst]
  choose t' ht'_snd ht'_fst using ht'
  have cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _ := fun i j k => by
    have c1 := hc i j k _ (pullback.fst (a i j) (a i k)) (t' i j k ≫ pullback.fst _ _)
      (pullback.snd (a i j) (a i k)) (by rw [Category.assoc, ht'_fst]) pullback.condition
    have c2 : (t' i j k ≫ t' j k i) ≫ pullback.fst _ _ = pullback.snd (a i j) (a i k) ≫ t i k := by
      apply ext_a k i
      simp only [Category.assoc, ht'_fst, ht_a]
      simpa only [Category.assoc] using c1
    have c2' : ∀ {Z : Scheme.{0}} (h : B k i ⟶ Z),
        t' i j k ≫ t' j k i ≫ pullback.fst _ _ ≫ h = pullback.snd (a i j) (a i k) ≫ t i k ≫ h := by
      intro Z h
      simp only [← Category.assoc, c2]
    apply pullback.hom_ext
    · apply ext_a i j
      simp only [Category.assoc, Category.id_comp, ht'_fst]
      rw [c2' (b k i), ht_b]
      exact pullback.condition.symm
    · simp only [Category.assoc, Category.id_comp, ht'_snd]
      rw [c2' (t k i), t_inv, Category.comp_id]
  let D : Scheme.GlueData.{0} :=
    { J := I, U := X, V := fun p => B p.1 p.2, f := a, f_mono := mono_a,
      f_hasPullback := fun _ _ _ => inferInstance, f_id := iso_a, t := t, t_id := t_id,
      t' := t', t_fac := ht'_snd, cocycle := cocycle, f_open := hma }
  obtain ⟨F, hF⟩ := exists_desc D (fun i => g i ≫ κ i) (fun i j => by
    change a i j ≫ g i ≫ κ i = (t i j ≫ a j i) ≫ g j ≫ κ j
    rw [ht_a]
    exact (hbw i j).symm)
  have hV : ∀ i j, IsPullback (a i j) (b i j) (D.ι i) (D.ι j) := fun i j => by
    have h : IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
      IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)
    have e : D.t i j ≫ D.f j i = b i j := ht_a i j
    rw [e] at h
    exact h
  refine ⟨D.glued, F, fun i => D.ι i, fun i => ?_, hV⟩
  have hw : D.ι i ≫ F = g i ≫ κ i := hF i
  have hιi : IsOpenImmersion (D.ι i) := D.ι_isOpenImmersion i
  have hr : ∀ {T : Scheme.{0}} (u : T ⟶ D.glued) (v : T ⟶ V i), u ≫ F = v ≫ κ i →
      Set.range u ⊆ Set.range (D.ι i) := by
    intro T u v huv x hx
    obtain ⟨t0, rfl⟩ := hx
    obtain ⟨j, y, hy⟩ := D.ι_jointly_surjective (u t0)
    have e1 : (g j ≫ κ j) y = κ i (v t0) := by
      have h1 := congrArg (fun φ : T ⟶ S => φ t0) huv
      have h2 := congrArg (fun φ : D.U j ⟶ S => φ y) (hF j)
      simp only [Scheme.Hom.comp_apply] at h1 h2 ⊢
      rw [← h2, hy]
      exact h1
    obtain ⟨z', hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g j ≫ κ j) (g := κ i) y (v t0) e1
    refine ⟨b j i ((ha j i).isoPullback.inv z'), ?_⟩
    have h3 := congrArg (fun φ : pullback (g j ≫ κ j) (κ i) ⟶ D.glued => φ z')
      (congrArg (fun φ => (ha j i).isoPullback.inv ≫ φ) (hV j i).w)
    simp only [Scheme.Hom.comp_apply] at h3
    rw [← h3, ← hy, ← hz1, ← IsPullback.isoPullback_inv_fst (ha j i), Scheme.Hom.comp_apply]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (D.ι i) s.fst (hr s.fst s.snd s.condition)) ?_ ?_ ?_)
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    apply ext_κ i
    rw [Category.assoc, ← hw, ← Category.assoc, IsOpenImmersion.lift_fac, s.condition]
  · intro s m h1 _
    apply (cancel_mono (D.ι i)).1
    rw [h1, IsOpenImmersion.lift_fac]

theorem glue_over_opens : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (G : ∀ i, Over (U i).toScheme) (B : ∀ i j, Over (U i ⊓ U j).toScheme) (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i j, IsPullback (a i j) (B i j).hom (G i).hom (S.homOfLE inf_le_left)) → (∀ i j, IsPullback (b i j) (B i j).hom (G j).hom (S.homOfLE inf_le_right)) → (∀ i j k (T : Scheme.{0}) (x : T ⟶ (B i j).left) (y : T ⟶ (B j k).left) (z : T ⟶ (B i k).left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) → ∃ (A : Over S) (ψ : ∀ i, (G i).left ⟶ A.left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  intro S I U G B a b h1 h2 h3
  have ha : ∀ i j, IsPullback (a i j) (b i j ≫ (G j).hom) ((G i).hom ≫ (U i).ι) (U j).ι := by
    intro i j
    have h := (h1 i j).paste_vert (isPullback_opens_inf (U i) (U j))
    rw [← (h2 i j).w] at h
    exact h
  have hb : ∀ i j, IsPullback (b i j) (a i j ≫ (G i).hom) ((G j).hom ≫ (U j).ι) (U i).ι := by
    intro i j
    have h := (h2 i j).paste_vert (isPullback_opens_inf (U i) (U j)).flip
    rw [← (h1 i j).w] at h
    exact h
  obtain ⟨A, F, ψ, hψ, hab⟩ := exists_glue (fun i => (U i).toScheme) (fun i => (G i).left)
    (fun i => (U i).ι) (fun i => inferInstance) (fun i => (G i).hom) (fun i j => (B i j).left)
    a b ha hb h3
  exact ⟨Over.mk F, ψ, hψ, hab⟩

end GlobalTheory.CocycleGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GroupLawsOnCoverAgreeOnCommonPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverOpCompat

section
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

private lemma isGrpPullback_one_left (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (ρ : T ⟶ S') :
    (1 : Over.mk (ρ ≫ f) ⟶ G).left = (1 : Over.mk ρ ⟶ G').left ≫ φ := by

  have hw : ((1 : Over.mk ρ ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (ρ ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let u : Over.mk (ρ ≫ f) ⟶ G := Over.homMk _ hw
  have huu : (u * u).left = ((1 : Over.mk ρ ⟶ G') * 1).left ≫ φ := h.2 (Over.mk ρ) 1 1 u u rfl rfl
  rw [_root_.mul_one] at huu
  have hsq : u * u = u := Over.OverMorphism.ext huu
  have hu : u = 1 := by
    calc u = u * u * u⁻¹ := (_root_.mul_inv_cancel_right u u).symm
      _ = 1 := by rw [hsq, _root_.mul_inv_cancel]
  rw [← hu]
  rfl

theorem push_mul (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p q : Over.mk ρ ⟶ G') (x y : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) (hy : y.left = q.left ≫ φ) :
    (x * y).left = (p * q).left ≫ φ := by
  subst e
  exact h.2 (Over.mk ρ) p q x y hx hy

theorem push_inv (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p : Over.mk ρ ⟶ G') (x : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) :
    (x⁻¹).left = (p⁻¹).left ≫ φ := by
  subst e

  have hw : ((p⁻¹).left ≫ φ) ≫ G.hom = (Over.mk (ρ ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let z : Over.mk (ρ ≫ f) ⟶ G := Over.homMk _ hw
  have hxz : (x * z).left = (p * p⁻¹).left ≫ φ := push_mul h rfl p p⁻¹ x z hx rfl
  rw [_root_.mul_inv_cancel, ← isGrpPullback_one_left h ρ] at hxz
  have hxz' : x * z = 1 := Over.OverMorphism.ext hxz
  have hz : x⁻¹ = z := (_root_.eq_inv_of_mul_eq_one_right hxz').symm
  rw [hz]
  rfl

theorem push_one (h : IsGrpPullback G' G f φ) :
    f ≫ (1 : Out.baseOver S ⟶ G).left = (1 : Out.baseOver S' ⟶ G').left ≫ φ := by

  let c : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
    Over.homMk f (by simp [Out.baseOver])
  have hc : c ≫ (1 : Out.baseOver S ⟶ G) = 1 := MonObj.comp_one c
  have hl : f ≫ (1 : Out.baseOver S ⟶ G).left = (1 : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ G).left := by
    rw [← hc]
    rfl
  rw [hl]
  exact isGrpPullback_one_left h (Out.baseOver S').hom

end

theorem opCompat : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (B : ∀ i j, Over (U i ⊓ U j).toScheme) [∀ i j, GrpObj (B i j)] (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j, IsGrpPullback (B i j) (G i) (S.homOfLE inf_le_left) (a i j)) → (∀ i j, IsGrpPullback (B i j) (G j) (S.homOfLE inf_le_right) (b i j)) → (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (x * y).left ≫ ψ i = (x' * y').left ≫ ψ j ∧ (x⁻¹).left ≫ ψ i = (x'⁻¹).left ≫ ψ j) ∧ ∀ i j, S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (1 : Out.baseOver (U j).toScheme ⟶ G j).left ≫ ψ j := by
  intro S I U A G _ ψ B _ a b _ ha hb hsq
  refine ⟨fun i j T r r' x y x' y' hx hy => ?_, fun i j => ?_⟩
  ·
    let p : T ⟶ (B i j).left := (hsq i j).lift x.left x'.left hx
    let q : T ⟶ (B i j).left := (hsq i j).lift y.left y'.left hy
    have hpa : p ≫ a i j = x.left := (hsq i j).lift_fst _ _ _
    have hpb : p ≫ b i j = x'.left := (hsq i j).lift_snd _ _ _
    have hqa : q ≫ a i j = y.left := (hsq i j).lift_fst _ _ _
    have hqb : q ≫ b i j = y'.left := (hsq i j).lift_snd _ _ _
    let ρ : T ⟶ (U i ⊓ U j).toScheme := p ≫ (B i j).hom
    have er : r = ρ ≫ S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) := by
      show r = (p ≫ (B i j).hom) ≫ _
      rw [Category.assoc, ← (ha i j).1.w, ← Category.assoc, hpa]
      exact (Over.w x).symm
    have er' : r' = ρ ≫ S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) := by
      show r' = (p ≫ (B i j).hom) ≫ _
      rw [Category.assoc, ← (hb i j).1.w, ← Category.assoc, hpb]
      exact (Over.w x').symm
    have eq : q ≫ (B i j).hom = ρ := by
      apply (cancel_mono (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).1
      rw [Category.assoc, ← (ha i j).1.w, ← Category.assoc, hqa]
      exact (Over.w y).trans er
    let P : Over.mk ρ ⟶ B i j := Over.homMk p rfl
    let Q : Over.mk ρ ⟶ B i j := Over.homMk q eq
    have m1 := push_mul (ha i j) er P Q x y hpa.symm hqa.symm
    have m2 := push_mul (hb i j) er' P Q x' y' hpb.symm hqb.symm
    have i1 := push_inv (ha i j) er P x hpa.symm
    have i2 := push_inv (hb i j) er' P x' hpb.symm
    refine ⟨?_, ?_⟩
    · rw [m1, m2]
      simp only [Category.assoc]
      rw [(hsq i j).w]
    · rw [i1, i2]
      simp only [Category.assoc]
      rw [(hsq i j).w]
  ·
    have e1 := congrArg (· ≫ ψ i) (push_one (ha i j))
    have e2 := congrArg (· ≫ ψ j) (push_one (hb i j))
    simp only [Category.assoc] at e1 e2
    rw [e1, e2, (hsq i j).w]

end GlobalTheory.CoverOpCompat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjDescendsToLargeSubfield
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.GrpDescent

open GrpDense

variable {Z U : Scheme.{0}} {j : U ⟶ Z}

theorem hom_ext_of_points (j : U ⟶ Z) [Flat j] [Surjective j] {X Y : Over Z} {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have : Epi (pullback.fst X.hom j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))

variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}

def sq (w : φ ≫ G.hom = A.hom ≫ j) : (A ⊗ A).left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left

theorem isSquare_sq (w : φ ≫ G.hom = A.hom ≫ j) : IsSquare φ (sq w) := by
  constructor
  · rw [sq, ← Over.comp_left, lift_fst]; rfl
  · rw [sq, ← Over.comp_left, lift_snd]; rfl

theorem sq_ext {W : Scheme.{0}} {a b : W ⟶ (G ⊗ G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem eq_sq (w : φ ≫ G.hom = A.hom ≫ j) {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) :
    φ₂ = sq w :=
  sq_ext (h.1.trans (isSquare_sq w).1.symm) (h.2.trans (isSquare_sq w).2.symm)

theorem isPullback_sq (hA : IsPullback φ A.hom G.hom j) :
    IsPullback (sq hA.w) (A ⊗ A).hom (G ⊗ G).hom j := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := (isSquare_sq hA.w).1
  have h₂ := (isSquare_sq hA.w).2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply sq_ext
    · rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem exists_grpObj (j : U ⟶ Z) [Flat j] [Surjective j] [GrpObj A] (h : IsPullback φ A.hom G.hom j)
    (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G)
    (hm : sq h.w ≫ m.left = (μ[A]).left ≫ φ) (hi : φ ≫ i.left = (ι[A]).left ≫ φ)
    (he : j ≫ e.left = (η[A]).left ≫ φ) : ∃ _ : GrpObj G, IsGrpPullback A G j φ := by
  have hM := fun {T : Over U} => pushPt_mul h.w (fun φ₂ h₂ => by rw [eq_sq h.w h₂, hm]) (T := T)
  have hI := fun {T : Over U} => pushPt_inv h.w hi (T := T)
  have hE := pushPt_one h.w he
  letI : MonObj G :=
    { one := e
      mul := m
      one_mul := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (toUnit _) (pushPt h.w x) :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        rw [lift_whiskerRight_assoc, hE, hM, _root_.one_mul, lift_leftUnitor_hom]
      mul_one := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
        obtain rfl : t = lift (pushPt h.w x) (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [lift_whiskerLeft_assoc, hE, hM, _root_.mul_one, lift_rightUnitor_hom]
      mul_assoc := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          ext <;> simp [hx, hy, hz]
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hM, hM, hM, hM,
          _root_.mul_assoc] }
  letI : GrpObj G :=
    { inv := i
      left_inv := hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, inv_mul_cancel, comp_toUnit_assoc, hE]
      right_inv := hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, mul_inv_cancel, comp_toUnit_assoc, hE] }
  refine ⟨inferInstance, h, fun T x y x₀ y₀ hx hy => ?_⟩
  obtain rfl : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
  obtain rfl : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
  exact congrArg (fun z => z.left) (hM x y)

theorem flat_spMap {k K : Type} [Field k] [Field K] (β : k →+* K) : Flat (spMap β) := by
  rw [Flat.SpecMap_iff]
  letI := β.toAlgebra
  exact (inferInstance : Module.Flat k K)

theorem surjective_spMap {k K : Type} [Field k] [Field K] (β : k →+* K) : Surjective (spMap β) :=
  ⟨fun _ => ⟨default, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩

theorem spMap_subtype {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GrpDescent

namespace GlobalTheory

open GrpDescent

theorem grpObj_descends_to_large_subfield :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ A₀.left) [QuasiCompact A₀.hom] [QuasiSeparated A₀.hom] [LocallyOfFinitePresentation A₀.hom], IsPullback φ A.hom A₀.hom (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (A₁ : Over (Sp K₁)) (φ₁ : A₁.left ⟶ A₀.left) (ψ : A.left ⟶ A₁.left), IsPullback φ₁ A₁.hom A₀.hom (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype → ∃ _ : GrpObj A₁, IsGrpPullback A A₁ (spMap K₁.subtype) ψ := by
  intro K _ K₀ A₀ A _ φ _ _ _ hφ
  have hw := hφ.w
  have hq : QuasiCompact (A₀ ⊗ A₀).hom := by
    rw [← Over.w (fst A₀ A₀)]
    exact (inferInstance : QuasiCompact (pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  have hs : QuasiSeparated (A₀ ⊗ A₀).hom := by
    rw [← Over.w (fst A₀ A₀)]
    exact (inferInstance : QuasiSeparated (pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  obtain ⟨s₁, H₁⟩ := _root_.GlobalTheory.morphisms_descend_to_large_subfield K K₀ _ _ (A₀ ⊗ A₀).hom (A ⊗ A).hom (sq hw) _ A₀.hom Unit
    (fun _ => (μ[A]).left ≫ φ) (isPullback_sq hφ) (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w, (isPullback_sq hφ).w])
  obtain ⟨s₂, H₂⟩ := _root_.GlobalTheory.morphisms_descend_to_large_subfield K K₀ _ _ A₀.hom A.hom φ _ A₀.hom Unit
    (fun _ => (ι[A]).left ≫ φ) hφ (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w])
  obtain ⟨s₃, H₃⟩ := _root_.GlobalTheory.morphisms_descend_to_large_subfield K K₀ _ _ (𝟙 _) (𝟙 _) (spMap K₀.subtype) _ A₀.hom Unit
    (fun _ => (η[A]).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩) (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; simp)
  classical
  refine ⟨s₁ ∪ s₂ ∪ s₃, fun K₁ h hs A₁ φ₁ ψ hφ₁ hψ hψw => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hs
  have hψp : IsPullback ψ A.hom A₁.hom (spMap K₁.subtype) :=
    IsPullback.of_right (by rwa [hψ, spMap_subtype]) hψw hφ₁
  obtain ⟨m, hm⟩ := H₁ K₁ h hs.1.1 _ (A₁ ⊗ A₁).hom (sq hφ₁.w) (sq hψw) (isPullback_sq hφ₁)
    (eq_sq hw ⟨by rw [Category.assoc, (isSquare_sq _).1, reassoc_of% (isSquare_sq hψw).1, hψ],
      by rw [Category.assoc, (isSquare_sq _).2, reassoc_of% (isSquare_sq hψw).2, hψ]⟩) (isPullback_sq hψp).w
  obtain ⟨i, hi⟩ := H₂ K₁ h hs.1.2 _ A₁.hom φ₁ ψ hφ₁ hψ hψw
  obtain ⟨e, he⟩ := H₃ K₁ h hs.2 _ (𝟙 _) (spMap (Subfield.inclusion h)) (spMap K₁.subtype)
    (IsPullback.of_vert_isIso ⟨by simp⟩) (spMap_subtype h) (by simp)
  have := flat_spMap K₁.subtype
  have := surjective_spMap K₁.subtype
  refine exists_grpObj _ hψp
    (Over.homMk (hφ₁.lift (m ()) (A₁ ⊗ A₁).hom ((hm ()).2.trans (isPullback_sq hφ₁).w)) (hφ₁.lift_snd _ _ _))
    (Over.homMk (hφ₁.lift (i ()) A₁.hom ((hi ()).2.trans hφ₁.w)) (hφ₁.lift_snd _ _ _))
    (Over.homMk (hφ₁.lift (e ()) (𝟙 _) ((he ()).2.trans (by simp))) (hφ₁.lift_snd _ _ _)) ?_ ?_ ?_
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (hm ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [(isPullback_sq hψp).w, ← Category.assoc, Over.w]
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (hi ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [← Category.assoc, Over.w]
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (he ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [← Category.assoc, Over.w]; simp

end GlobalTheory
end
end

