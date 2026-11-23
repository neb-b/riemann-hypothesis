module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusIsOpenOfOpenImmersionCover
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.AbLocusLocal

private theorem isProper_of_isPullback_of_pullback_snd {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (H : IsProper (pullback.snd f g)) : IsProper snd := by
  rw [← h.isoPullback_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.hom (pullback.snd f g)).2 H

private theorem isProper_pullback_snd_of_isPullback {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (H : IsProper snd) : IsProper (pullback.snd f g) := by
  rw [← h.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.inv snd).2 H

private theorem isProper_snd_of_isPullback_of_isProper {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (hf : IsProper f) : IsProper snd :=
  isProper_of_isPullback_of_pullback_snd h inferInstance

theorem isProper_restrict_of_cover {X Z : Scheme.{0}} (p : X ⟶ Z) {I : Type} {Y X' : I → Scheme.{0}}
    (f : ∀ i, Y i ⟶ Z) [∀ i, IsOpenImmersion (f i)] (p' : ∀ i, X' i ⟶ Y i) (F : ∀ i, X' i ⟶ X)
    (h : ∀ i, IsPullback (F i) (p' i) p (f i)) (V : ∀ i, (Y i).Opens) (hV : ∀ i, IsProper (p' i ∣_ V i))
    (U : Z.Opens) (hle : ∀ i, Set.range ((V i).ι ≫ f i) ⊆ Set.range U.ι)
    (hc : ∀ z ∈ U, ∃ i, z ∈ Set.range ((V i).ι ≫ f i)) : IsProper (p ∣_ U) := by
  have hsq : ∀ i, IsPullback (((p' i) ⁻¹ᵁ V i).ι ≫ F i) (p' i ∣_ V i) p ((V i).ι ≫ f i) := fun i =>
    (isPullback_morphismRestrict (p' i) (V i)).flip.paste_horiz (h i)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => U.ι ⁻¹ᵁ ((V i).ι ≫ f i).opensRange) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨i, hi⟩ := hc (U.ι x) x.2
    exact ⟨i, by simpa [Scheme.Hom.coe_opensRange] using hi⟩
  · intro i
    let W : U.toScheme.Opens := U.ι ⁻¹ᵁ ((V i).ι ≫ f i).opensRange
    have hr : Set.range (W.ι ≫ U.ι) ⊆ Set.range ((V i).ι ≫ f i) := by
      rintro _ ⟨x, rfl⟩
      have hx : U.ι x.val ∈ ((V i).ι ≫ f i).opensRange := x.2
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at hx
      exact hx
    let e := IsOpenImmersion.lift ((V i).ι ≫ f i) (W.ι ≫ U.ι) hr
    have he : e ≫ ((V i).ι ≫ f i) = W.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
    have big := (isPullback_morphismRestrict (p ∣_ U) W).flip.paste_horiz (isPullback_morphismRestrict p U).flip
    rw [← he] at big
    have hw : ((((p ∣_ U) ⁻¹ᵁ W).ι ≫ (p ⁻¹ᵁ U).ι)) ≫ p = ((p ∣_ U) ∣_ W ≫ e) ≫ ((V i).ι ≫ f i) := by
      rw [big.w, Category.assoc]
    have sq : IsPullback ((hsq i).lift _ _ hw) ((p ∣_ U) ∣_ W) (p' i ∣_ V i) e := by
      refine IsPullback.of_right ?_ ((hsq i).lift_snd _ _ hw) (hsq i)
      rw [(hsq i).lift_fst]
      exact big
    exact isProper_snd_of_isPullback_of_isProper sq (hV i)

private theorem mem_abLocus_of_map_mem_of_isPullback {Y Z : Scheme.{0}} {A : Over Y} {B : Over Z} {g : Y ⟶ Z}
    {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom g) (y : Y) (hy : g y ∈ abLocus B) :
    y ∈ abLocus A := by
  simp only [abLocus, Set.mem_setOf_eq] at hy ⊢
  intro K _ _ s hs
  obtain ⟨x, rfl⟩ := hs
  have big := (IsPullback.of_hasPullback A.hom s).paste_horiz h
  exact isProper_of_isPullback_of_pullback_snd big (hy K (s ≫ g) ⟨x, by rw [Scheme.Hom.comp_apply]⟩)

private theorem map_mem_abLocus_of_isPullback {Y Z : Scheme.{0}} {A : Over Y} {B : Over Z} {g : Y ⟶ Z}
    [IsOpenImmersion g] {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom g) (y : Y)
    (hy : y ∈ abLocus A) : g y ∈ abLocus B := by
  simp only [abLocus, Set.mem_setOf_eq] at hy ⊢
  intro K _ _ s hs
  obtain ⟨x0, hx0⟩ := hs
  have hr : Set.range s ⊆ Set.range g := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x x0, hx0]
    exact ⟨y, rfl⟩
  have hs' : IsOpenImmersion.lift g s hr ≫ g = s := IsOpenImmersion.lift_fac g s hr
  have big := (IsPullback.of_hasPullback A.hom (IsOpenImmersion.lift g s hr)).paste_horiz h
  rw [hs'] at big
  have hy' : y ∈ Set.range (IsOpenImmersion.lift g s hr) := by
    refine ⟨x0, g.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hs', hx0]
  exact isProper_pullback_snd_of_isPullback big (hy K _ hy')

theorem abOpen_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, AbOpen (u i).G) → AbOpen t.G := by
  intro E _ _ _ H Z t I Y f u m hf hc hab
  unfold AbOpen at hab ⊢
  choose V hVs hVp using hab
  have hpb : ∀ i, IsPullback (m i).φ (u i).G.hom t.G.hom (f i) := fun i => (m i).cart.1
  refine ⟨⨆ i, ((V i).ι ≫ f i).opensRange, ?_, ?_⟩
  · ext z
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, Scheme.Hom.coe_opensRange]
    constructor
    · rintro ⟨i, v, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact map_mem_abLocus_of_isPullback (hpb i) _ (by rw [← hVs i]; exact v.2)
    · intro hz
      obtain ⟨i, y, rfl⟩ := hc z
      have hy := mem_abLocus_of_map_mem_of_isPullback (hpb i) y hz
      rw [← hVs i] at hy
      exact ⟨i, ⟨y, hy⟩, rfl⟩
  · refine isProper_restrict_of_cover t.G.hom f (fun i => (u i).G.hom) _ hpb V hVp _ ?_ ?_
    · intro i z hz
      rw [Scheme.Opens.range_ι]
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]; exact hz⟩
    · intro z hz
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at hi
      exact ⟨i, hi⟩

end GlobalTheory.AbLocusLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ActCommOfClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleTheta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g k : ℕ} {J : Type}
  {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {o : Type} [CommRing o] {b : TBase o k} {S S' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

def Under (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La)
    (T : TObj g k J b s) : Prop :=
  ∃ φ : t.G ≅ T.A, IsMonHom φ.hom ∧ LBIso t.PP.L (T.L.pull φ.hom.left) ∧
    (∀ j, t.act.act (a j) ≫ φ.hom = φ.hom ≫ T.act j) ∧
    ∀ i, (lv (bas (Pi.single i 1))).left ≫ φ.hom.left = (T.pt i).left

theorem lbIso_of_sabMap {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem inv_hom_left {A B : Over S} (φ : A ≅ B) : φ.inv.left ≫ φ.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]

theorem hom_inv_left {A B : Over S} (φ : A ≅ B) : φ.hom.left ≫ φ.inv.left = 𝟙 _ := inv_hom_left φ.symm

theorem lbIso_inv {A B : Over S} (φ : A ≅ B) {L : LB A.left} {M : LB B.left}
    (h : LBIso L (M.pull φ.hom.left)) : LBIso M (L.pull φ.inv.left) :=
  (LBIso.chartPull (chartPullId _) (chartPullUnpull M (𝟙 _) rfl)
    (PELPull.lbIso_pull h φ.inv.left (inv_hom_left φ).symm)).symm

theorem tmap_of_sabMap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    (h' : Under t' lv' a bas T') {f : S' ⟶ S} (m : SABMap t' t f) (hl : ∀ x, (lv' x).left ≫ m.φ = f ≫ (lv x).left) :
    TMap T' T f := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hψa, hψp⟩ := h'
  have : IsMonHom ψ.symm.hom := inferInstanceAs (IsMonHom ψ.inv)
  refine ⟨ψ.inv.left ≫ m.φ ≫ φ.hom.left, ?_, ?_, fun i => ?_, fun j => ?_⟩
  · exact ((isGrpPullback_of_iso ψ.symm).comp (m.cart.comp (isGrpPullback_of_iso φ))).congr (by simp) rfl
  · refine (lbIso_inv ψ hψL).trans T'.isLB (pull_isLB t'.PP.isLB _) (pull_isLB T.isLB _) (PELPull.lbIso_pull ?_ _ rfl)
    exact (lbIso_of_sabMap m).trans t'.PP.isLB (pull_isLB t.PP.isLB _) (pull_isLB T.isLB _)
      (PELPull.lbIso_pull hφL m.φ rfl)
  · rw [← hψp, ← hφp, Category.assoc, reassoc_of% hom_inv_left ψ, reassoc_of% hl]
  · have h₁ : (t.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (T.act j).left := congrArg (fun z => z.left) (hφa j)
    have h₂ : (T'.act j).left ≫ ψ.inv.left = ψ.inv.left ≫ (t'.act.act (a j)).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      rw [Iso.comp_inv_eq, Category.assoc, hψa, Iso.inv_hom_id_assoc]
    have h₃ : (t'.act.act (a j)).left ≫ m.φ = m.φ ≫ (t.act.act (a j)).left := m.act _
    rw [reassoc_of% h₂, reassoc_of% h₃, h₁, Category.assoc, Category.assoc]

theorem under_of_tmap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    {f : S' ⟶ S} (h' : TMap T' T f) (m : SABMap t' t f) (hl : ∀ x, (lv' x).left ≫ m.φ = f ≫ (lv x).left) :
    Under t' lv' a bas T' := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hpt, hact⟩ := h'
  have hc : IsGrpPullback t'.G T.A f (m.φ ≫ φ.hom.left) :=
    (IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl
  obtain ⟨e, he, heF⟩ := grpPullback_iso hc hψ
  refine ⟨e, he, ?_, fun j => ?_, fun i => ?_⟩
  · exact ((lbIso_of_sabMap m).trans t'.PP.isLB (pull_isLB t.PP.isLB _) (pull_isLB T.isLB _)
      (PELPull.lbIso_pull hφL m.φ rfl)).trans
      t'.PP.isLB (pull_isLB T.isLB _) (pull_isLB T'.isLB _) (PELPull.lbIso_pull hψL e.hom.left heF.symm).symm
  · apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · have h₁ : (t.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (T.act j).left :=
        congrArg (fun z => z.left) (hφa j)
      have h₂ : (t'.act.act (a j)).left ≫ m.φ = m.φ ≫ (t.act.act (a j)).left := m.act _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂,
        Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]
    · rw [Over.w, Over.w]
  · apply hψ.1.hom_ext
    · rw [Category.assoc, heF, reassoc_of% hl, hφp, hpt]
    · rw [Category.assoc, Over.w, Over.w, Over.w]; rfl

theorem act_zero {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) : act.act 0 = 1 := by
  have := act.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem act_neg {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (c : O) :
    act.act (-c) = (act.act c)⁻¹ := by
  have := act.add (-c) c
  rw [neg_add_cancel, act_zero] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem act_comm_of_closure {O : Type} [CommRing O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (act : OAct O G)
    (act' : OAct O G') {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {a : J → O}
    (ha : Subring.closure (Set.range a) = ⊤) (hj : ∀ j, (act'.act (a j)).left ≫ φ = φ ≫ (act.act (a j)).left) (c : O) :
    (act'.act c).left ≫ φ = φ ≫ (act.act c).left := by
  let u : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have key : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left ↔ pushHom h G' (act'.act c) = preHom u (act.act c) :=
    fun c => ⟨fun e => Over.OverMorphism.ext e, fun e => congrArg (fun z => z.left) e⟩
  have hc : c ∈ Subring.closure (Set.range a) := ha ▸ Subring.mem_top c
  induction hc using Subring.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hj j
  | zero => rw [key, act_zero, act_zero, map_one, map_one]
  | one => rw [act.one, act'.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  | add x y _ _ hx hy => rw [key] at hx hy ⊢; rw [act.add, act'.add, map_mul, map_mul, hx, hy]
  | neg x _ hx => rw [key] at hx ⊢; rw [act_neg, act_neg, map_inv, map_inv, hx]
  | mul x y _ _ hx hy => rw [act.mul, act'.mul, Over.comp_left, Over.comp_left, Category.assoc, hy, reassoc_of% hx]

theorem eq_of_basis {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u v : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) (hv : ∀ x y, v (x + y) = v x * v y)
    (h : ∀ i, u (bas (Pi.single i 1)) = v (bas (Pi.single i 1))) (x : D.La) : u x = v x := by
  let u' : D.La →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul (u x)) fun x y => by rw [hu]; rfl
  let v' : D.La →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul (v x)) fun x y => by rw [hv]; rfl
  have : u'.comp bas.toLinearMap.toAddMonoidHom = v'.comp bas.toLinearMap.toAddMonoidHom := by
    refine AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int ?_
    exact congrArg Additive.ofMul (h i)
  have e := DFunLike.congr_fun this (bas.symm x)
  simpa [u', v'] using e

theorem sabMap_of_tmap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    (h' : Under t' lv' a bas T') (hlv : ∀ x y, lv (x + y) = lv x * lv y) (hlv' : ∀ x y, lv' (x + y) = lv' x * lv' y)
    (ha : Subring.closure (Set.range a) = ⊤) (hS : IsReduced S') (hp : IsProper t'.G.hom) {f : S' ⟶ S}
    (m : TMap T' T f) : ∃ ν : SABMap t' t f, ∀ x, (lv' x).left ≫ ν.φ = f ≫ (lv x).left := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hψa, hψp⟩ := h'
  obtain ⟨χ, hχ, hχL, hpt, hact⟩ := m
  have : IsMonHom φ.symm.hom := inferInstanceAs (IsMonHom φ.inv)
  have hc : IsGrpPullback t'.G t.G f (ψ.hom.left ≫ χ ≫ φ.inv.left) :=
    ((isGrpPullback_of_iso ψ).comp (hχ.comp (isGrpPullback_of_iso φ.symm))).congr (by simp) rfl
  obtain ⟨ν, hν⟩ := exists_sabMap_of_lbIso E H S S' t t' f _ ⟨hS, fun _ _ _ _ _ _ _ => inferInstance⟩ hc
    (act_comm_of_closure t.act t'.act hc ha fun j => by
      have h₁ : (t'.act.act (a j)).left ≫ ψ.hom.left = ψ.hom.left ≫ (T'.act j).left :=
        congrArg (fun z => z.left) (hψa j)
      have h₂ : (T.act j).left ≫ φ.inv.left = φ.inv.left ≫ (t.act.act (a j)).left := by
        rw [← Over.comp_left, ← Over.comp_left]
        congr 1
        rw [Iso.comp_inv_eq, Category.assoc, hφa, Iso.inv_hom_id_assoc]
      rw [reassoc_of% h₁, reassoc_of% hact, h₂, Category.assoc, Category.assoc])
    (hψL.trans t'.PP.isLB (pull_isLB T'.isLB _) (pull_isLB t.PP.isLB _) (PELPull.lbIso_pull
      (hχL.trans T'.isLB (pull_isLB T.isLB _) (pull_isLB t.PP.isLB _) (PELPull.lbIso_pull (lbIso_inv φ hφL) χ rfl)) _ rfl))
  refine ⟨ν, fun x => ?_⟩
  have e := eq_of_basis bas lv' (fun x => ObjPull.secPull hc (lv x)) hlv' (fun x y => by rw [hlv, map_mul])
    (fun i => Over.OverMorphism.ext (hc.1.hom_ext (by
      rw [ObjPull.secPull_left, reassoc_of% hψp, reassoc_of% hpt, ← hφp, Category.assoc, hom_inv_left,
        Category.comp_id]) (by rw [Over.w, Over.w]))) x
  rw [hν, e, ObjPull.secPull_left]

end GlobalTheory.TripleTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardBasisPolarisationPowerZeroEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.RankZero

section
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)

theorem top_le_wchart (ψ : Fin 0 → (Y ⟶ X)) (j : Fin 0 → L.ι) : (⊤ : Y.Opens) ≤ LB.wchart L ψ j :=
  fun _ _ => Set.mem_iInter.2 fun k => k.elim0

theorem exists_fn (hL : L.IsLB) (hε : ∀ k, ε k = 0) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ f : Γ(Y, ⊤), ∀ y J, Good L y J → sval s (𝟙 Y) y J = gs (𝟙 Y) y ⊤ f := by
  have hF : FormEq φ ε (Fin.elim0 : Fin 0 → (Y ⟶ X)) (Fin.elim0 : Fin 0 → ℤ) := by
    intro U _ h
    simp [hε]
  obtain ⟨s', hs'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sec hL hF s
  refine ⟨(Y.presheaf.map (homOfLE (top_le_wchart (L := L) Fin.elim0 Fin.elim0)).op).hom (s'.f Fin.elim0),
    fun y J hJ => ?_⟩
  rw [← hs' Y (𝟙 Y) y J hJ, sval_of s' (𝟙 Y) y J Fin.elim0 (fun k => k.elim0)]
  exact (gs_res (𝟙 Y) y (top_le_wchart (L := L) Fin.elim0 Fin.elim0) trivial _).symm

theorem exists_sec_of_fn (hε : ∀ k, ε k = 0) (f : Γ(Y, ⊤)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ y J, Good L y J → sval s (𝟙 Y) y J = gs (𝟙 Y) y ⊤ f := by
  have hle : ∀ j : K → L.ι, LB.wchart L φ j ≤ ⊤ := fun _ => le_top
  have h1 : ∀ y j j', trF (L := L) φ ε (𝟙 Y) y j j' = 1 := fun y j j' => by simp [trF, hε]
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE (hle j)).op).hom f, fun (j j' : K → L.ι) => fn_ext fun y hy => ?_⟩,
    fun y J hJ => (gs_res (𝟙 Y) y (hle _) (hJ.mem φ (𝟙 Y)) f)⟩
  have hg : gm (𝟙 Y) y ((L.LinComb φ ε).U j ⊓ (L.LinComb φ ε).U j') ((L.LinComb φ ε).g j j') = 1 :=
    (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2).trans (h1 y j j')
  rw [gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, hg, Units.val_one, _root_.one_mul]
  exact ((gs_res (𝟙 Y) y inf_le_left hy _).trans (gs_res (𝟙 Y) y (hle j) hy.1 f)).trans
    ((gs_res (𝟙 Y) y inf_le_right hy _).trans (gs_res (𝟙 Y) y (hle j') hy.2 f)).symm

end

theorem eq_one_of_existsUnique {Γ : Type} [CommRing Γ] [Nontrivial Γ] {n : ℕ} (β : Fin n → Γ)
    (h : ∀ a : Γ, ∃! c : Fin n → Γ, a = ∑ i, c i * β i) : n = 1 := by
  let F : (Fin n → Γ) →ₗ[Γ] Γ :=
    { toFun := fun c => ∑ i, c i * β i
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [_root_.mul_assoc] }
  have hF : ∀ c, F c = ∑ i, c i * β i := fun _ => rfl
  have hb : Function.Bijective F := by
    refine ⟨fun c c' hcc => ?_, fun a => ?_⟩
    · obtain ⟨d, -, hd⟩ := h (F c)
      exact (hd c (hF c)).trans (hd c' (hcc.trans (hF c'))).symm
    · obtain ⟨c, hc, -⟩ := h a
      exact ⟨c, (hF c).trans hc.symm⟩
  have e := (LinearEquiv.ofBijective F hb).finrank_eq
  simpa using e

theorem eq_one_of_bijective {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (hL : L.IsLB) (T : Over Z)
    [Nontrivial Γ(T.left, ⊤)] (hb : Function.Bijective (fst T G).left.appTop.hom) {n : ℕ}
    (b : Fin n → LB.Sec (Out.LPow G L ((0 : ℕ) : ℤ) T)) (H : GlobalTheory.LN.BasisAlong G L 0 (𝟙 _) b) : n = 1 := by
  have hpull : ∀ (x : Γ(T.left, ⊤)) (y : (T ⊗ G).left),
      gs (fst T G).left y ⊤ x = gs (𝟙 _) y ⊤ ((fst T G).left.appTop.hom x) := fun x y => by
    have e := gs_pull (𝟙 _) (fst T G).left y ⊤ trivial x
    rw [Category.id_comp] at e
    exact e.symm
  have hρ : ∀ y : (T ⊗ G).left, ∃ ρ : Γ((T ⊗ G).left, ⊤) →+* (T ⊗ G).left.presheaf.stalk y,
      ∀ a, gs (𝟙 _) y ⊤ a = ρ a := fun y =>
    ⟨((T ⊗ G).left.presheaf.germ ((𝟙 (T ⊗ G).left) ⁻¹ᵁ ⊤) y trivial).hom.comp (Scheme.Hom.app (𝟙 (T ⊗ G).left) ⊤).hom,
      fun a => gs_eq _ y ⊤ trivial a⟩
  choose β' hβ' using fun i => exists_fn (L := L) (fun _ : Fin 1 => (snd T G).left) (fun _ => ((0 : ℕ) : ℤ)) hL
    (fun _ => rfl) (b i)
  choose β hβ using fun i => hb.2 (β' i)
  have hR : ∀ (c : Fin n → Γ(T.left, ⊤)) (z : (T ⊗ G).left) (J : ((T ⊗ G).left ⟶ G.left) → L.ι), Good L z J →
      ∑ i, gs (fst T G).left z ⊤ (c i) * sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left)
        (ε := fun _ => ((0 : ℕ) : ℤ)) (b i) (𝟙 T ▷ G).left z J
        = gs (𝟙 _) z ⊤ ((fst T G).left.appTop.hom (∑ i, c i * β i)) := by
    intro c z J hJ
    obtain ⟨ρ, hρz⟩ := hρ z
    rw [MonoidalCategory.id_whiskerRight, Over.id_left]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hβ' _ z J hJ, hpull, hρz, map_sum, map_mul, hβ]
  have hiff : ∀ (a : Γ(T.left, ⊤)) (c : Fin n → Γ(T.left, ⊤)) (s : LB.Sec (Out.LPow G L ((0 : ℕ) : ℤ) T)),
      (∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => ((0 : ℕ) : ℤ))
        s (𝟙 _) y J = gs (𝟙 _) y ⊤ ((fst T G).left.appTop.hom a)) →
      (GlobalTheory.LN.Lin G L 0 (𝟙 T) b c s ↔ a = ∑ i, c i * β i) := by
    intro a c s hs
    constructor
    · intro hl
      apply hb.1
      apply fn_ext
      intro z _
      obtain ⟨J, hJ, -⟩ := exists_good L hL z (Fin.elim0 : Fin 0 → ((T ⊗ G).left ⟶ G.left)) Fin.elim0
        (fun a => a.elim0) (fun k => k.elim0)
      rw [← hs z J hJ, hl z J hJ, hR c z J hJ]
    · rintro rfl z J hJ
      rw [hs z J hJ, hR c z J hJ]
  refine eq_one_of_existsUnique β (fun a => ?_)
  obtain ⟨s, hs⟩ := exists_sec_of_fn (L := L) (fun _ : Fin 1 => (snd T G).left) (fun _ => ((0 : ℕ) : ℤ))
    (fun _ => rfl) ((fst T G).left.appTop.hom a)
  obtain ⟨c, hc, hcu⟩ := H s
  exact ⟨c, (hiff a c s hs).1 hc, fun c' hc' => hcu c' ((hiff a c' s hs).2 hc')⟩

end GlobalTheory.RankZero

theorem GlobalTheory.basisAlong_zero_card : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [Nontrivial R] (P : Out.PolAV (Sp R)) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L ((0 : ℕ) : ℤ) (Over.mk (𝟙 (Sp R))))), GlobalTheory.LN.BasisAlong P.A P.L 0 (𝟙 _) b → n = 1 := by
  intro hG R _ _ P n b hB
  have : Nontrivial Γ((Over.mk (𝟙 (Sp R))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  refine GlobalTheory.RankZero.eq_one_of_bijective P.A P.L P.isLB (Over.mk (𝟙 (Sp R))) ?_ b hB
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A) := by
    change IsIso (snd (𝟙_ (Over (Sp R))) P.A)
    rw [← CartesianMonoidalCategory.leftUnitor_hom]
    infer_instance
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A).left :=
    (inferInstance : IsIso ((Over.forget _).map (snd (Over.mk (𝟙 (Sp R))) P.A)))
  have e1 : (fst (Over.mk (𝟙 (Sp R))) P.A).left = (snd (Over.mk (𝟙 (Sp R))) P.A).left ≫ P.A.hom := by
    have h1 : (fst (Over.mk (𝟙 (Sp R))) P.A).left ≫ 𝟙 (Sp R) = _ := Over.w (fst (Over.mk (𝟙 (Sp R))) P.A)
    have h2 := Over.w (snd (Over.mk (𝟙 (Sp R))) P.A)
    exact (Category.comp_id _).symm.trans (h1.trans h2.symm)
  have hc : ((snd (Over.mk (𝟙 (Sp R))) P.A).left ≫ P.A.hom).appTop =
      P.A.hom.appTop ≫ (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop := by
    simp
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop := by
    exact (inferInstance : IsIso ((snd (Over.mk (𝟙 (Sp R))) P.A).left.app ⊤))
  rw [e1, hc, CommRingCat.hom_comp, RingHom.coe_comp]
  exact Function.Bijective.comp (asIso (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop).commRingCatIsoToRingEquiv.bijective
    (@hG _ P.A P.grp P.isAb)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardPulledSectionsFormBasisEqPowDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.SecRank

theorem card_eq_of_basisAlong {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (hL : L.IsLB) (N : ℕ)
    {T₁ T₂ T' : Over S} [Nontrivial Γ(T'.left, ⊤)] (h₁ : T' ⟶ T₁) (h₂ : T' ⟶ T₂) {n m : ℕ}
    {a : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T₁)} {b : Fin m → LB.Sec (Out.LPow G L (N : ℤ) T₂)}
    (ha : BasisAlong G L N h₁ a) (hb : BasisAlong G L N h₂ b) : n = m := by
  choose a' ha' _ using fun i => PolFrames.exists_pullSec G L N h₁ (a i)
  choose b' hb' _ using fun i => PolFrames.exists_pullSec G L N h₂ (b i)
  obtain ⟨l₁, s₁⟩ := (PolFrames.basisAlong_iff G L N h₁ hL ha').1 ha
  obtain ⟨l₂, s₂⟩ := (PolFrames.basisAlong_iff G L N h₂ hL hb').1 hb
  have e₁ := Module.finrank_eq_card_basis (Module.Basis.mk l₁ s₁.ge)
  have e₂ := Module.finrank_eq_card_basis (Module.Basis.mk l₂ s₂.ge)
  simpa using e₁.symm.trans e₂

theorem card_basis_eq_pow : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), 1 ≤ N → GlobalTheory.LN.BasisAlong P.A P.L N (𝟙 _) b → n = N ^ P.g := by
  intro _ hL R _ _ P N n b hN hb
  obtain ⟨V, hV, c, hc⟩ := hL.secBaseChangeAny (Sp R) P N hN (IsLocalRing.closedPoint R)
  have hV' : V = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    exact (IsLocalRing.specializes_closedPoint x).mem_open V.isOpen hV
  subst hV'
  let χ : Sp R ⟶ (⊤ : (Sp R).Opens).toScheme := (Sp R).topIso.inv
  choose c' hc' _ using fun i => PolFrames.exists_pullSec P.A P.L N (Out.homAt χ) (c i)
  have H := (PolFrames.basisAlong_iff P.A P.L N (Out.homAt χ) P.isLB hc').2 (hc R χ c' hc')
  have : Nontrivial Γ((Over.mk (𝟙 (Sp R)) : Over (Sp R)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have key : ∀ (f : Sp R ⟶ Sp R) (hf : f = 𝟙 _) (T : Over (Sp R)) (h : Over.mk f ⟶ T)
      (d : Fin (N ^ P.g) → LB.Sec (Out.LPow P.A P.L (N : ℤ) T)), BasisAlong P.A P.L N h d → n = N ^ P.g := by
    rintro _ rfl T h d hd
    exact card_eq_of_basisAlong P.A P.L P.isLB N _ h hb hd
  refine key (Out.baseAt χ).hom ?_ _ (Out.homAt χ) c H
  exact (congrArg (χ ≫ ·) (Category.comp_id (⊤ : (Sp R).Opens).ι)).trans (Sp R).toIso_inv_ι

end GlobalTheory.LN.SecRank
end
end

