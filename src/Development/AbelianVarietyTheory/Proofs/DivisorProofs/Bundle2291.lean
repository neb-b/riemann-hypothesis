module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.PullDegUniq

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nonempty_psiOn_pull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    Nonempty (PsiOn D' (specOf φ ⁻¹ᵁ hD.W)) := by
  have hm : (specOf φ ∣_ hD.W) ≫ hD.W.ι = (specOf φ ⁻¹ᵁ hD.W).ι ≫ specOf φ := morphismRestrict_ι _ _
  have key : ∀ x : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (K := PUnit)
      (fun _ => (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left) (fun _ => -1)), a.IsGen ∧
      LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)))
        (LB.pullGen D'.P.L _ _ (D'.psi x) (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι) := by
    intro x
    have hψ : (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left ≫ proj hD =
        (specOf φ ∣_ hD.W) ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
      show (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        (specOf φ ∣_ hD.W) ≫ hD.W.ι ≫ (D.c (hD.xe x)).left
      rw [hD.c_pr x, ← Category.assoc, ← Category.assoc, hm]
    obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (K := PUnit)
      (ε := fun _ => -1) (specOf φ ∣_ hD.W) (fun _ => hψ) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
    refine ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have hz : ((jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ∣_ hD.W)) ≫ hD.W.ι =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ specOf φ := by
      rw [Category.assoc, hm, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨hp, P⟩ := ArcSpecialise.pmaps_psiOn hD hD.psiW _ _ hz x
    have v₁ := DegPull.pmaps_val (fun _ => hψ) H (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) y hJ hJ'
    have v₂ := DegPull.pmaps_val (fun _ => hp) P (𝟙 _) y hJ hJ'
    rw [val_pull hJ', val_pull hJ']
    rw [val_pull hJ, val_pull hJ'] at v₂
    simp only [Category.id_comp] at v₁ v₂ ⊢
    have hmor : (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ D'.xK x := by
      show (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ (D'.c x).left
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hmor] at v₁
    exact mul_left_cancel (v₁.symm.trans v₂)
  choose a ha hc using key
  exact ⟨⟨a, ha, hc⟩⟩

theorem exists_generic_section {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    ∃ s : (TK R').left ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme, s ≫ (specOf φ ⁻¹ᵁ hD.W).ι = jK R' :=
  ⟨(isPullback_morphismRestrict (specOf φ) hD.W).lift hD.g (jK R') hD.g_comm,
    (isPullback_morphismRestrict (specOf φ) hD.W).lift_snd _ _ _⟩

theorem nonempty_isPullDeg_cancel {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} (hα : Function.Injective α)
    (hβ : Function.Injective β) {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂} (h₁ : IsPullDeg α D₀ D₁)
    (h : IsPullDeg (β.comp α) D₀ D) : Nonempty (IsPullDeg β D₁ D) := by
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := exists_generic_section h₁
  obtain ⟨hD, -⟩ := DvrDeg.exists_isPullDeg_of_val hβ D₁ D ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK R₂ ≫ spMap β = genMap hβ ≫ jK R₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have sα : jK R₁ ≫ spMap α = genMap hα ≫ jK R₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq hα)
    have q₁ : genMap hβ ≫ jK R₁ ≫ spMap α = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK R₂).left ≫ jK R₂ ≫ spMap (β.comp α) = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap hβ ≫ D₁.xK (xe x) := by
      show (jK R₂ ≫ (D.c x).left) ≫ Φ = genMap hβ ≫ jK R₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

end GlobalTheory.PullDegUniq

namespace GlobalTheory.Mum

theorem isPullDeg_unique_and_comp : (∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (D : DegPre R) (D₁ D₂ : DegPre R'), Nonempty (IsPullDeg ρ D D₁) → Nonempty (IsPullDeg ρ D D₂) → Nonempty (IsPullDeg (RingHom.id R') D₁ D₂)) ∧ ∀ (R R' R'' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] (ρ : R →+* R') (ρ' : R' →+* R''), Function.Injective ρ → Function.Injective ρ' → ∀ (D : DegPre R) (D' : DegPre R') (D'' : DegPre R''), Nonempty (IsPullDeg ρ D D') → Nonempty (IsPullDeg ρ' D' D'') → Nonempty (IsPullDeg (ρ'.comp ρ) D D'') :=
  ⟨fun _ R' _ _ _ _ ρ hρ _ _ _ ⟨p₁⟩ ⟨p₂⟩ =>
    GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel (β := RingHom.id R') hρ Function.injective_id p₁
      ((RingHom.id_comp ρ).symm ▸ p₂),
   fun _ _ _ _ _ _ _ _ _ _ _ hρ hρ' _ _ _ ⟨p⟩ ⟨q⟩ => GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ hρ' p q⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackMorphismRestrictImageOfRestrictRestric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isPullback_morphismRestrict_image_of_restrict_restrict :
    ∀ (P' X S T : Scheme.{0}) (a : X ⟶ P') (W : P'.Opens) (V : W.toScheme.Opens) (q : X ⟶ S)
      (h : P' ⟶ T) (π : S ⟶ T),
      IsPullback ((a ∣_ W) ∣_ V) (((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι ≫ q) (V.ι ≫ W.ι ≫ h) π →
      IsPullback (a ∣_ (W.ι ''ᵁ V)) ((a ⁻¹ᵁ (W.ι ''ᵁ V)).ι ≫ q) ((W.ι ''ᵁ V).ι ≫ h) π := by
  intro P' X S T a W V q h π H
  have e1hom : ((a ⁻¹ᵁ W).ι.isoImage ((a ∣_ W) ⁻¹ᵁ V) ≪≫
      X.isoOfEq (image_morphismRestrict_preimage a W V)).hom ≫ (a ⁻¹ᵁ (W.ι ''ᵁ V)).ι =
      ((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι := by
    simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]
  refine IsPullback.of_iso H
    ((a ⁻¹ᵁ W).ι.isoImage ((a ∣_ W) ⁻¹ᵁ V) ≪≫ X.isoOfEq (image_morphismRestrict_preimage a W V))
    (W.ι.isoImage V) (Iso.refl S) (Iso.refl T) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (W.ι ''ᵁ V).ι]
    simp only [Category.assoc, Scheme.Hom.isoImage_hom_ι, morphismRestrict_ι]
    rw [reassoc_of% e1hom, morphismRestrict_ι_assoc, morphismRestrict_ι]
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [reassoc_of% e1hom]
  · simp only [Iso.refl_hom, Category.comp_id, Scheme.Hom.isoImage_hom_ι_assoc]
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPowersCartesianGroupSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PowCart

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {β : G'.left ⟶ G.left}

theorem square_over_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G2 G).left}
    (h : ∀ i, a ≫ (x2 G i).left = b ≫ (x2 G i).left) : a = b :=
  pullback.hom_ext (h 0) (h 1)

theorem isPullback_two (hp : IsPullback β G'.hom G.hom f) :
    IsPullback (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left (G2 G').hom (G2 G).hom f := by
  set F2 := (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left with hF2
  have f2 : ∀ i, F2 ≫ (x2 G i).left = (x2 G' i).left ≫ β := fun i => by
    fin_cases i
    · exact congrArg (fun z => z.left) (lift_fst (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
    · exact congrArg (fun z => z.left) (lift_snd (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
  have w : F2 ≫ (G2 G).hom = (G2 G').hom ≫ f := Over.w (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
  have ex : ∀ s : PullbackCone (G2 G).hom f, ∃ l : s.pt ⟶ (G2 G').left,
      l ≫ F2 = s.fst ∧ l ≫ (G2 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 2 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x2 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x2 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G2 G' := lift (x 0) (x 1)
    have lx : ∀ i, l ≫ x2 G' i = x i := fun i => by fin_cases i <;> simp [l, x2]
    refine ⟨l.left, square_over_hom_ext _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f2, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => square_over_hom_ext _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f2, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem fourth_power_over_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G4 G).left}
    (h : ∀ i, a ≫ (x4 G i).left = b ≫ (x4 G i).left) : a = b := by
  apply pullback.hom_ext
  · exact h 0
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]; exact h 1
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]; exact h 2
      · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]; exact h 3

theorem isPullback_four (hp : IsPullback β G'.hom G.hom f) :
    IsPullback (lift (pushPt hp.w (x4 G' 0)) (lift (pushPt hp.w (x4 G' 1))
      (lift (pushPt hp.w (x4 G' 2)) (pushPt hp.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f := by
  set L4 := lift (pushPt hp.w (x4 G' 0)) (lift (pushPt hp.w (x4 G' 1))
      (lift (pushPt hp.w (x4 G' 2)) (pushPt hp.w (x4 G' 3)))) with hL4
  have f4 : ∀ i, L4.left ≫ (x4 G i).left = (x4 G' i).left ≫ β := fun i => by
    rw [← Over.comp_left]
    have : L4 ≫ x4 G i = pushPt hp.w (x4 G' i) := by fin_cases i <;> simp [L4, x4]
    rw [this]; rfl
  have w : L4.left ≫ (G4 G).hom = (G4 G').hom ≫ f := Over.w L4
  have ex : ∀ s : PullbackCone (G4 G).hom f, ∃ l : s.pt ⟶ (G4 G').left,
      l ≫ L4.left = s.fst ∧ l ≫ (G4 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 4 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x4 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x4 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G4 G' := lift (x 0) (lift (x 1) (lift (x 2) (x 3)))
    have lx : ∀ i, l ≫ x4 G' i = x i := fun i => by fin_cases i <;> simp [l, x4]
    refine ⟨l.left, fourth_power_over_hom_ext _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f4, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => fourth_power_over_hom_ext _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f4, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem isPullback_three [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (gp : IsGrpPullback G' G f β) :
    IsPullback (cubeMapOf gp).F3 (G3 G').hom (G3 G).hom f := by
  have hp := gp.1
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 G' i).left ≫ β := cubeMap_comp_proj_three (cubeMapOf gp)
  have w : (cubeMapOf gp).F3 ≫ (G3 G).hom = (G3 G').hom ≫ f :=
    Over.w (lift (pushPt hp.w (x3 G' 0)) (lift (pushPt hp.w (x3 G' 1)) (pushPt hp.w (x3 G' 2))))
  have ex : ∀ s : PullbackCone (G3 G).hom f, ∃ l : s.pt ⟶ (G3 G').left,
      l ≫ (cubeMapOf gp).F3 = s.fst ∧ l ≫ (G3 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 3 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 G' := lift (x 0) (lift (x 1) (x 2))
    have lx : ∀ i, l ≫ x3 G' i = x i := fun i => by fin_cases i <;> simp [l, x3]
    refine ⟨l.left, hom_ext_triple _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f3, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => hom_ext_triple _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f3, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem isPullback_pow {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β) :
    IsPullback (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left (G2 G').hom (G2 G).hom f ∧
    IsPullback (cubeMapOf h).F3 (G3 G').hom (G3 G).hom f ∧
    IsPullback (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
      (pushPt h.1.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f :=
  ⟨isPullback_two h.1, isPullback_three h, isPullback_four h.1⟩

end GlobalTheory.Mum.PowCart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackRestrictISupOfForallRestrict
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isPullback_iSup_of_forall : ∀ (P' X T S : Scheme.{0}) (a : X ⟶ P') (p : X ⟶ S) (q : P' ⟶ T) (π : S ⟶ T), a ≫ q = p ≫ π → ∀ (I : Type) (V : I → P'.Opens), (∀ i, IsPullback (a ∣_ V i) ((a ⁻¹ᵁ V i).ι ≫ p) ((V i).ι ≫ q) π) → IsPullback (a ∣_ (⨆ i, V i)) ((a ⁻¹ᵁ (⨆ i, V i)).ι ≫ p) ((⨆ i, V i).ι ≫ q) π := by
  intro P' X T S a p q π w I V hV
  have hw : (a ∣_ (⨆ i, V i)) ≫ (⨆ i, V i).ι ≫ q = ((a ⁻¹ᵁ (⨆ i, V i)).ι ≫ p) ≫ π := by
    rw [morphismRestrict_ι_assoc, Category.assoc, w]
  set U := ⨆ i, V i with hUdef
  let L := pullback.lift (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ p) hw
  let Wo : I → U.toScheme.Opens := fun i => U.ι ⁻¹ᵁ V i
  let O : I → (pullback (U.ι ≫ q) π).Opens := fun i => pullback.fst (U.ι ≫ q) π ⁻¹ᵁ Wo i
  have hO : (⨆ i, O i) = ⊤ := by
    simp only [O, Wo]
    rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, ← hUdef, Scheme.Opens.ι_preimage_self,
      Scheme.Hom.preimage_top]
  have hle : ∀ i, V i ≤ U := fun i => le_iSup V i
  have hr1 : ∀ i, Set.range ((Wo i).ι ≫ U.ι) = Set.range (V i).ι := by
    intro i
    ext x
    simp only [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨⟨x, hle i hx⟩, hx⟩, rfl⟩
  have hpt : ∀ z, U.ι (pullback.fst (U.ι ≫ q) π (L z)) = a ((a ⁻¹ᵁ U).ι z) := by
    intro z
    have h := congr($(show L ≫ pullback.fst (U.ι ≫ q) π ≫ U.ι = (a ⁻¹ᵁ U).ι ≫ a by
      rw [pullback.lift_fst_assoc, morphismRestrict_ι]) z)
    simpa using h
  have key : ∀ i, IsIso (L ∣_ O i) := by
    intro i
    let e := IsOpenImmersion.isoOfRangeEq ((Wo i).ι ≫ U.ι) (V i).ι (hr1 i)
    have he : e.hom ≫ (V i).ι = (Wo i).ι ≫ U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    let j : (a ⁻¹ᵁ V i).toScheme ⟶ (a ⁻¹ᵁ U).toScheme := X.homOfLE (a.preimage_mono (hle i))
    have hj : j ≫ (a ⁻¹ᵁ U).ι = (a ⁻¹ᵁ V i).ι := Scheme.homOfLE_ι _ _
    have outer : IsPullback ((j ≫ L) ≫ pullback.snd (U.ι ≫ q) π) ((a ∣_ V i) ≫ e.inv) π
        ((Wo i).ι ≫ U.ι ≫ q) := by
      have h0 := (hV i).flip
      have e1 : (j ≫ L) ≫ pullback.snd (U.ι ≫ q) π = (a ⁻¹ᵁ V i).ι ≫ p := by
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hj]
      rw [e1]
      refine IsPullback.of_iso h0 (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp
      · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
        rw [← reassoc_of% he, Iso.inv_hom_id_assoc]
    have hv : IsPullback (j ≫ L) ((a ∣_ V i) ≫ e.inv) (pullback.fst (U.ι ≫ q) π) (Wo i).ι := by
      refine IsPullback.of_right (h₁₂ := pullback.snd (U.ι ≫ q) π) (h₂₂ := U.ι ≫ q) (v₁₃ := π) outer ?_
        (IsPullback.of_hasPullback (U.ι ≫ q) π).flip
      rw [← cancel_mono U.ι]
      simp only [Category.assoc, L, pullback.lift_fst_assoc, morphismRestrict_ι, reassoc_of% hj]
      rw [← he, Iso.inv_hom_id_assoc, morphismRestrict_ι]
    have R := (isPullback_morphismRestrict (pullback.fst (U.ι ≫ q) π) (Wo i)).flip
    have hr2 : Set.range ((L ⁻¹ᵁ O i).ι ≫ (a ⁻¹ᵁ U).ι) = Set.range (a ⁻¹ᵁ V i).ι := by
      ext x
      simp only [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩
        have hy := y.2
        change U.ι (pullback.fst (U.ι ≫ q) π (L y.1)) ∈ V i at hy
        rw [hpt] at hy
        exact hy
      · intro hx
        refine ⟨⟨⟨x, hle i hx⟩, ?_⟩, rfl⟩
        change U.ι (pullback.fst (U.ι ≫ q) π (L ⟨x, hle i hx⟩)) ∈ V i
        exact (congrArg (· ∈ V i) (hpt _)).mpr hx
    let f₁ := IsOpenImmersion.isoOfRangeEq _ _ hr2
    have hkey : L ∣_ O i = f₁.hom ≫ (hv.isoIsPullback _ _ R).hom := by
      rw [← cancel_mono (O i).ι, morphismRestrict_ι, Category.assoc, IsPullback.isoIsPullback_hom_fst,
        ← Category.assoc f₁.hom]
      congr 1
      rw [← cancel_mono (a ⁻¹ᵁ U).ι, Category.assoc, hj, IsOpenImmersion.isoOfRangeEq_hom_fac]
    rw [hkey]
    infer_instance
  have hiso : IsIso L :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) O hO key
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso L) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsDomainOfIsComplAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isRegularLocalRing_and_isDomain_of_isComplAt :
    ∀ (W : Type) [CommRing W] [IsRegularLocalRing W] (I : Type) [Fintype I] (R : Type) [CommRing R]
      [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) →
      IsRegularLocalRing R ∧ IsDomain R := by
  intro W _ _ I _ R _ _ ψ hψ _
  obtain ⟨hnoeth, -, hflat, hmap, -⟩ := hψ
  haveI : IsRegularRing W := GlobalTheory.isRegularRing_of_isRegularLocalRing W
  set q : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime ψ (maximalIdeal R)
  let L := Localization.AtPrime q
  haveI : IsRegularLocalRing L := IsRegularRing.isRegularLocalRing_localization q
  have hu : ∀ y : q.primeCompl, IsUnit (ψ y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let φ : L →+* R := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  letI : Algebra L R := φ.toAlgebra
  haveI : IsScalarTower (MvPolynomial I W) L R := IsScalarTower.of_algebraMap_eq (fun a => by
    change ψ a = φ (algebraMap _ L a)
    exact (IsLocalization.lift_eq (M := q.primeCompl) hu a).symm)
  haveI : Module.Flat (MvPolynomial I W) R := hflat
  haveI : IsLocalizedModule q.primeCompl (LinearMap.id : R →ₗ[MvPolynomial I W] R) :=
    isLocalizedModule_id q.primeCompl R L
  haveI : Module.Flat L R :=
    Module.Flat.of_isLocalizedModule L q.primeCompl (LinearMap.id : R →ₗ[MvPolynomial I W] R)
  haveI : IsNoetherianRing R := hnoeth
  have hm : maximalIdeal R = (maximalIdeal L).map (algebraMap L R) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hmap.symm
  haveI hreg : IsRegularLocalRing R :=
    GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal L R (maximalIdeal L) hm
  exact ⟨hreg, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).1⟩

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSharpBasisSharpBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

def sharpBasis (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) :
    (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
  (sharpReindex h).trans
    { twistSnd (e8 W).adjugate with
      invFun := twistSnd (e8 W)
      left_inv := twistSnd_twistSnd _ _ (by rw [Matrix.mul_adjugate, hW, one_smul])
      right_inv := twistSnd_twistSnd _ _ (by rw [Matrix.adjugate_mul, hW, one_smul]) }

theorem isSharpBasis_sharpBasis (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) :
    IsSharpBasis W (sharpBasis W hW h) := by
  intro i j
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd (e8 W) _ (by simp [e8, Matrix.transpose_add, add_comm])
    (by rw [Matrix.mul_adjugate, hW, one_smul]) _ _

def labMat (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) (a : Fin 2) :
    Matrix (Fin (2 * (8 * h))) (Fin (2 * (8 * h))) ℤ :=
  fun i' i => (sharpBasis W hW h).symm
    (fun u c => ∑ v, actMat W a u v * sharpBasis W hW h (Pi.single i 1) v c) i'

variable {S : Scheme.{0}}

def ptOf {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    {T : Over S} {C : Type} [Fintype C] (b : C → (T ⟶ B)) (x : Fin 8 → C → ℤ) : T ⟶ A :=
  (hP.2 T fun u => ∏ c, b c ^ x u c).exists.choose

theorem ptOf_pr {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    {T : Over S} {C : Type} [Fintype C] (b : C → (T ⟶ B)) (x : Fin 8 → C → ℤ) (u : Fin 8) :
    ptOf hP b x ≫ pr u = ∏ c, b c ^ x u c :=
  (hP.2 T fun u => ∏ c, b c ^ x u c).exists.choose_spec u

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
end

