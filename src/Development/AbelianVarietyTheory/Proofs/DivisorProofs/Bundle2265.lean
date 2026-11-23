module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchemePresentingSquareZeroSmoothLiftSystem
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPicardClassExtendAffineMilnorSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

open TopologicalSpace

theorem exists_pic_of_glue_units {X X₁ X₂ : Scheme.{0}} (p₁ : X₁ ⟶ X) (p₂ : X₂ ⟶ X) [IsClosedImmersion p₂]
    [Surjective p₂] (D : LB X₂) (hD : D.IsLB)
    (inj : ∀ (W : X.Opens) (a b : Γ(X, W)ˣ), pullU p₁ W a = pullU p₁ W b → pullU p₂ W a = pullU p₂ W b → a = b)
    (glue : ∀ (W : X.Opens) (a b : D.ι) (h : p₂ ⁻¹ᵁ W ≤ D.U a ⊓ D.U b),
      ∃ v : Γ(X, W)ˣ, pullU p₁ W v = 1 ∧ pullU p₂ W v = res h (D.g a b)) :
    ∃ c : Pic X, GlobalTheory.CechPic.pull p₁ c = 0 ∧ GlobalTheory.CechPic.pull p₂ c = cls D hD := by
  have hW : ∀ a : D.ι, ∃ W : X.Opens, ∀ y : X₂, p₂ y ∈ W ↔ y ∈ D.U a := fun a => by
    obtain ⟨t, ht, e⟩ := (p₂.isClosedEmbedding.isInducing.isOpen_iff).1 (D.U a).isOpen
    exact ⟨⟨t, ht⟩, fun y => Set.ext_iff.1 e y⟩
  choose W hW using hW
  have hle : ∀ a b, p₂ ⁻¹ᵁ (W a ⊓ W b) ≤ D.U a ⊓ D.U b := fun a b y hy => ⟨(hW a y).1 hy.1, (hW b y).1 hy.2⟩
  choose v hv₁ hv₂ using fun a b => glue (W a ⊓ W b) a b (hle a b)
  have g₁ : ∀ (y : X₁) a b, p₁ y ∈ W a → p₁ y ∈ W b → gm (𝟙 X₁ ≫ p₁) y (W a ⊓ W b) (v a b) = 1 :=
    fun y a b ha hb => by
      rw [← gm_pull (𝟙 X₁) p₁ y (W a ⊓ W b) ⟨ha, hb⟩, hv₁, map_one]
  have g₂ : ∀ (y : X₂) a b, p₂ y ∈ W a → p₂ y ∈ W b →
      gm (𝟙 X₂ ≫ p₂) y (W a ⊓ W b) (v a b) = gm (𝟙 X₂) y _ (D.g a b) :=
    fun y a b ha hb => by
      rw [← gm_pull (𝟙 X₂) p₂ y (W a ⊓ W b) ⟨ha, hb⟩, hv₂, gm_res (𝟙 X₂) y (hle a b) ⟨ha, hb⟩]
  have ext : ∀ (V : X.Opens) (a b : Γ(X, V)ˣ),
      (∀ y : X₁, p₁ y ∈ V → gm (𝟙 X₁ ≫ p₁) y V a = gm (𝟙 X₁ ≫ p₁) y V b) →
      (∀ y : X₂, p₂ y ∈ V → gm (𝟙 X₂ ≫ p₂) y V a = gm (𝟙 X₂ ≫ p₂) y V b) → a = b := fun V a b h₁ h₂ =>
    inj V a b
      (unit_ext fun y hy => by rw [gm_pull (𝟙 X₁) p₁ y V hy, gm_pull (𝟙 X₁) p₁ y V hy]; exact h₁ y hy)
      (unit_ext fun y hy => by rw [gm_pull (𝟙 X₂) p₂ y V hy, gm_pull (𝟙 X₂) p₂ y V hy]; exact h₂ y hy)
  let E : LB X := ⟨D.ι, W, v⟩
  have hE : E.IsLB :=
    { cover := by
        rw [eq_top_iff]
        intro x _
        obtain ⟨y, rfl⟩ := Surjective.surj (f := p₂) x
        obtain ⟨a, ha⟩ := exists_chart hD y
        exact Opens.mem_iSup.2 ⟨a, (hW a y).2 ha⟩
      g_self := fun a => ext _ _ _
        (fun y hy => by
          rw [gm_res (𝟙 X₁ ≫ p₁) y _ hy, map_one]
          exact g₁ y a a hy hy)
        (fun y hy => by
          rw [gm_res (𝟙 X₂ ≫ p₂) y _ hy, map_one]
          exact (g₂ y a a hy hy).trans (gm_self hD (𝟙 X₂) y ((hW a y).1 hy)))
      cocycle := fun a b c => ext _ _ _
        (fun y hy => by
          rw [map_mul, gm_res (𝟙 X₁ ≫ p₁) y _ hy, gm_res (𝟙 X₁ ≫ p₁) y _ hy, gm_res (𝟙 X₁ ≫ p₁) y _ hy]
          exact (congrArg₂ (· * ·) (g₁ y a b hy.1.1 hy.1.2) (g₁ y b c hy.1.2 hy.2)).trans
            ((_root_.mul_one _).trans (g₁ y a c hy.1.1 hy.2).symm))
        (fun y hy => by
          rw [map_mul, gm_res (𝟙 X₂ ≫ p₂) y _ hy, gm_res (𝟙 X₂ ≫ p₂) y _ hy, gm_res (𝟙 X₂ ≫ p₂) y _ hy]
          exact (congrArg₂ (· * ·) (g₂ y a b hy.1.1 hy.1.2) (g₂ y b c hy.1.2 hy.2)).trans
            ((gm_cocycle hD (𝟙 X₂) y ((hW a y).1 hy.1.1) ((hW b y).1 hy.1.2) ((hW c y).1 hy.2)).trans
              (g₂ y a c hy.1.1 hy.2).symm)) }
  refine ⟨cls E hE, ?_, ?_⟩
  · rw [← cls_pull hE p₁ (pull_isLB hE p₁), cls_eq_zero_iff]
    refine ⟨⟨fun _ => 1⟩, (isGen_iff_germ _).2 fun y J J' hJ hJ' => ?_⟩
    rw [map_one, map_one, _root_.mul_one]
    exact ((gm_pull_g E p₁ (𝟙 _) y J J' hJ hJ').trans (g₁ y _ _ (mem_pull.1 hJ) (mem_pull.1 hJ'))).symm
  · rw [← cls_pull hE p₂ (pull_isLB hE p₂)]
    refine Eq.symm ((cls_eq_iff hD (pull_isLB hE p₂)).2 (iso_of_chart (pull_isLB hE p₂) ?_))
    exact
      { idx := fun a _ => a
        le := fun a y hy => mem_pull.2 ((hW a y).2 hy)
        g := fun y a b ha hb => Eq.symm ((gm_pull_g E p₂ (𝟙 _) y (fun _ => a) (fun _ => b)
          (mem_pull.2 ((hW a y).2 ha)) (mem_pull.2 ((hW b y).2 hb))).trans
          (g₂ y a b ((hW a y).2 ha) ((hW b y).2 hb))) }

theorem isPullback_whiskerLeft_left {S : Scheme.{0}} (A : Over S) {T T' : Over S} (j : T' ⟶ T) :
    IsPullback (A ◁ j).left (snd A T').left (snd A T).left j.left := by
  have P : IsPullback (A ◁ j) (snd A T') (snd A T) j := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.fst ≫ fst A T) s.snd) ?_ ?_ ?_⟩⟩
    · intro s
      ext <;> simp [s.condition]
    · intro s
      simp
    · intro s m h₁ h₂
      ext <;> simp [← h₁, ← h₂]
  exact P.map (Over.forget S)

theorem exists_pic_extend_of_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → IsClosedImmersion j₂.left → Surjective j₂.left → Surjective k₂.left → ∀ c₂ : Pic (A ⊗ T₂).left, GlobalTheory.CechPic.pull (A ◁ k₂).left c₂ = 0 → ∃ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (A ◁ j₁).left c = 0 ∧ GlobalTheory.CechPic.pull (A ◁ j₂).left c = c₂ := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ hM hj hj' hk' c₂ hc
  have hk := hM.closed
  haveI : IsClosedImmersion (A ◁ j₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A j₂).flip hj
  haveI : Surjective (A ◁ j₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A j₂).flip hj'
  haveI : IsClosedImmersion (A ◁ k₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A k₂).flip hk
  haveI : Surjective (A ◁ k₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A k₂).flip hk'
  have w₀ : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext hM.w
  have w : (A ◁ k₁).left ≫ (A ◁ j₁).left = (A ◁ k₂).left ≫ (A ◁ j₂).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, w₀]
  obtain ⟨D, hD, rfl, h1⟩ := _root_.GlobalTheory.CechPic.exists_cocycle_one_on_thickening _ _ (A ◁ k₂).left c₂ hc
  have H := _root_.GlobalTheory.DualOpen.sections_milnor S A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ hM
  generalize (A ◁ j₁).left = p₁ at *
  generalize (A ◁ j₂).left = p₂ at *
  generalize (A ◁ k₁).left = q₁ at *
  generalize (A ◁ k₂).left = q₂ at *
  have inj : ∀ (W : (A ⊗ T).left.Opens) (a b : Γ((A ⊗ T).left, W)ˣ), pullU p₁ W a = pullU p₁ W b →
      pullU p₂ W a = pullU p₂ W b → a = b := fun W a b h₁ h₂ =>
    Units.ext ((H W).1 _ _ (congrArg Units.val h₁) (congrArg Units.val h₂))
  refine exists_pic_of_glue_units p₁ p₂ D hD inj fun W a b h => ?_
  have e : q₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W) = q₂ ⁻¹ᵁ (p₂ ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  have lift : ∀ u : Γ((A ⊗ T₂).left, p₂ ⁻¹ᵁ W)ˣ, pullU q₂ _ u = 1 →
      ∃ s : Γ((A ⊗ T).left, W), p₁.app W s = 1 ∧ p₂.app W s = u.val := fun u hu =>
    (H W).2 _ e.ge le_rfl e.le 1 u.val (by
      rw [map_one, Scheme.Hom.appLE_eq_app]
      exact (congrArg Units.val hu).symm)
  have hu : pullU q₂ _ (res h (D.g a b)) = 1 := unit_ext fun y hy => by
    rw [gm_pull (𝟙 _) q₂ y _ hy, gm_res (𝟙 _ ≫ q₂) y h hy, ← gm_pull (𝟙 _) q₂ y _ (h hy), h1, map_one, map_one]
  obtain ⟨s, hs₁, hs₂⟩ := lift _ hu
  obtain ⟨t, ht₁, ht₂⟩ := lift (res h (D.g a b))⁻¹ (by rw [map_inv, hu, inv_one])
  have st : s * t = 1 := (H W).1 _ _ (by rw [map_mul, hs₁, ht₁, map_one, _root_.mul_one])
    (by rw [map_mul, hs₂, ht₂, map_one, Units.mul_inv])
  exact ⟨⟨s, t, st, (mul_comm _ _).trans st⟩, Units.ext hs₁, Units.ext hs₂⟩

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointDisjointUnionRepresentingAdditiveFami
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem opens_disjoint_of {Y : Scheme.{0}} {U U' : Y.Opens} (h : ∀ z, z ∈ U → z ∉ U') : Disjoint U U' :=
  disjoint_iff.2 (eq_bot_iff.2 fun z hz ↦ (h z hz.1 hz.2).elim)

theorem not_mem_of_disjoint {Y : Scheme.{0}} {U U' : Y.Opens} (h : Disjoint U U') {z : Y} (hz : z ∈ U)
    (hz' : z ∈ U') : False := by
  have := h.le_bot (show z ∈ U ⊓ U' from ⟨hz, hz'⟩)
  simpa using this

theorem rep_exists {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S)
    (V : κ → X.left.Opens) (hV : ⨆ i, V i = ⊤) (hVd : Pairwise fun i i' => Disjoint (V i) (V i'))
    (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left]
    (hj : ⨆ i, (j i).left.opensRange = ⊤)
    (hjd : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange)
    (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X) (hb : ∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι)
    (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left) (hP : ∀ i, Rep A (b i) (P i)) (hPt : Pt.IsLB)
    (hiso : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) (T : Over S) (t : T ⟶ X) (N : LB (A ⊗ T).left)
    (hN : Fam A N) : ∃ x : T ⟶ Bt, x ≫ bt = t ∧ LBIso N (ev Pt (fst A T) (snd A T ≫ x)) := by
  let W : κ → T.left.Opens := fun i ↦ t.left ⁻¹ᵁ V i
  let Ti : κ → Over S := fun i ↦ Over.mk ((W i).ι ≫ T.hom)
  let w : ∀ i, Ti i ⟶ T := fun i ↦ Over.homMk (W i).ι
  let ti : ∀ i, Ti i ⟶ Over.mk ((V i).ι ≫ X.hom) := fun i ↦ Over.homMk (t.left ∣_ V i) (by
    simp [Ti, W, morphismRestrict_ι_assoc])
  have hti : ∀ i, ti i ≫ Over.homMk (V i).ι = w i ≫ t := fun i ↦ by
    ext1; simp [ti, w, W, morphismRestrict_ι]
  have hNi : ∀ i, Fam A (ev N (fst A (Ti i)) (snd A (Ti i) ≫ w i)) := fun i ↦ Model.fam_ev hN (w i)
  choose x hx _ using fun i ↦ (hP i).univ (Ti i) (ti i) _ (hNi i)
  have hWc : ⨆ i, (W i).ι.opensRange = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    have : t.left z ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by simpa [W] using hi⟩
  have hWd : _root_.Pairwise fun i i' ↦ Disjoint (W i).ι.opensRange (W i').ι.opensRange := by
    intro i i' h
    refine opens_disjoint_of fun z hz hz' ↦ ?_
    simp only [Scheme.Opens.opensRange_ι, W] at hz hz'
    exact not_mem_of_disjoint (hVd h) hz hz'
  obtain ⟨hT⟩ := nonempty_isColimit_cofanMk_of (fun i ↦ (W i).ι) hWc hWd
  let xl : T.left ⟶ Bt.left := Cofan.IsColimit.desc hT fun i ↦ (x i).left ≫ (j i).left
  have hxl : ∀ i, (W i).ι ≫ xl = (x i).left ≫ (j i).left := fun i ↦ Cofan.IsColimit.fac hT _ i
  have hxo : xl ≫ Bt.hom = T.hom := Cofan.IsColimit.hom_ext hT _ _ fun i ↦ by
    change (W i).ι ≫ _ = (W i).ι ≫ _
    rw [reassoc_of% hxl i, Over.w (j i), Over.w (x i)]
    rfl
  let xx : T ⟶ Bt := Over.homMk xl hxo
  have wxx : ∀ i, w i ≫ xx = x i ≫ j i := fun i ↦ by
    ext1
    simp only [Over.comp_left, Over.homMk_left, w, xx]
    exact hxl i
  have hxt : xx ≫ bt = t := by
    ext1
    refine Cofan.IsColimit.hom_ext hT _ _ fun i ↦ ?_
    change (W i).ι ≫ _ = (W i).ι ≫ _
    have e : w i ≫ xx ≫ bt = w i ≫ t := by
      rw [reassoc_of% wxx i, hb i, reassoc_of% (hx i).1, hti i]
    simpa [w, xx] using congrArg (fun q ↦ q.left) e
  refine ⟨xx, hxt, ?_⟩
  have hNl := hN.isLB
  refine (same_id_iff hNl hPt xx).1 ((same_iff hNl hPt _ _).2 ?_)
  have hwo : ∀ i, IsOpenImmersion (w i).left := fun i ↦ by
    show IsOpenImmersion (W i).ι; infer_instance
  have hwa : ∀ i, IsOpenImmersion (A ◁ w i).left := fun i ↦
    (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).1
  have hwr : ∀ i z, z ∈ (A ◁ w i).left.opensRange ↔ (snd A T).left z ∈ W i := fun i z ↦ by
    have := (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).2
    change z ∈ Set.range (A ◁ w i).left ↔ _
    rw [this, Set.mem_preimage]
    change _ ∈ Set.range (W i).ι ↔ _
    rw [Scheme.Opens.range_ι]
    rfl
  rw [← sub_eq_zero]
  refine _root_.GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero (fun i ↦ (A ◁ w i).left) ?_ ?_ _ fun i ↦ ?_
  · refine eq_top_iff.2 fun z _ ↦ ?_
    have : t.left ((snd A T).left z) ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hwr i z).2 hi⟩
  · intro i i' h
    refine opens_disjoint_of fun z hz hz' ↦ ?_
    exact not_mem_of_disjoint (hVd h) ((hwr i z).1 hz) ((hwr i' z).1 hz')
  · rw [map_sub, pull_evc, pull_evc, sub_eq_zero]
    simp only [whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd, Category.comp_id]
    rw [wxx i, ← Category.assoc, evc_comp_of_iso (j i) hPt (hP i).fam.isLB (hiso i)]
    exact (cls_eq_iff (hNi i).isLB (pull_isLB (hP i).fam.isLB _)).2 (hx i).2

end GlobalTheory.DualCon.ProdGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseCochainCoboundaryEqChernCocycleAl
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem commAlgFunctorCoboundaryOne_apply_of_eq_sub_vanishing {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
    {m : C1 F} {z z' : C2 F} (h : d1 F m = z - z') {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'')
    (h0 : z' T T' T'' a b = 0) :
    mp F b (m T T' a) - m T T'' (a ≫ b) + m T' T'' b = z T T' T'' a b := by
  rw [← d1_apply, h]
  simp only [Pi.sub_apply, h0, sub_zero]

theorem exists_crystallineCochain_coboundary_eq_chernCocycle {R : Type} [CommRing R] {I : Ideal R} {g : DividedPowers I} {X : Scheme.{0}}
    {s : X ⟶ Sp R} {L : LB X} {w : Z2 (O g s)} (hw : IsChern g s L (CatCoh.H2.mk _ w)) :
    ∃ V : C1 (O g s), ∀ (T T' T'' : Thick g s) (a : T ⟶ T') (b : T' ⟶ T''), IsSmall g s L.U T → T''.J = ⊥ →
      d1 _ V T T' T'' a b = w.1 T T' T'' a b := by
  obtain ⟨i, hi, u, ℓ, hu, hℓ, hz⟩ := hw
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hz
  obtain ⟨m, hm⟩ := hz
  classical
  have sm : ∀ {T T' : Thick g s} (_ : T ⟶ T'), IsSmall g s L.U T → IsSmall g s L.U T' := by
    rintro T T' a ⟨j, hj⟩
    exact ⟨j, a.le_preimage hj⟩
  refine ⟨fun T T' a ↦ if h : IsSmall g s L.U T then m ⟨T, h⟩ ⟨T', sm a h⟩ (ObjectProperty.homMk a) else 0, ?_⟩
  intro T T' T'' a b h hJ
  have h1 := sm a h
  have h2 := sm b h1
  rw [d1_apply]
  simp only [dite_eq_left h, dite_eq_left h1]
  refine commAlgFunctorCoboundaryOne_apply_of_eq_sub_vanishing hm (T := ⟨T, h⟩) (T' := ⟨T', h1⟩) (T'' := ⟨T'', h2⟩) (ObjectProperty.homMk a)
    (ObjectProperty.homMk b) ?_
  have := (hℓ ⟨T, h⟩ ⟨T', h1⟩ ⟨T'', h2⟩ (ObjectProperty.homMk a) (ObjectProperty.homMk b)).1
  exact Ideal.mem_bot.1 (hJ.le this)

theorem exists_pt_d_eq_chern {R : Type} [CommRing R] {X : Over (Sp R)} {L : LB X.left}
    {w : Z2 (O (dp0 R) (X.hom ≫ 𝟙 _))} (hw : IsChern (dp0 R) _ L (CatCoh.H2.mk _ w)) :
    ∃ V : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (z : Pt X E) (z' : Pt X E'),
      (trivAt z ⟶ trivAt z') → E',
      ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E'']
        [Algebra R E''] (z : Pt X E) (z' : Pt X E') (z'' : Pt X E'') (a : trivAt z ⟶ trivAt z')
        (b : trivAt z' ⟶ trivAt z'') (ψ : E' →ₐ[R] E''), b.φ = ψ → Sm L.U z →
        ψ (V E E' z z' a) - V E E'' z z'' (a ≫ b) + V E' E'' z' z'' b = w.1 _ _ _ a b := by
  obtain ⟨V, hV⟩ := exists_crystallineCochain_coboundary_eq_chernCocycle hw
  refine ⟨fun E _ _ E' _ _ z z' a ↦ V _ _ a, ?_⟩
  intro E _ _ E' _ _ E'' _ _ z z' z'' a b ψ hb hz
  subst ψ
  exact hV _ _ _ a b hz rfl

theorem exists_pointwiseCochain_coboundary_eq_chernCocycle : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (L : LB X.left) (w : Z2 (O (dp0 R) (X.hom ≫ 𝟙 _))), IsChern (dp0 R) _ L (CatCoh.H2.mk _ w) → ∃ n : Fn1 X, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt X E), Sm L.U z → ψ (n E E' φ z) - n E E'' (ψ.comp φ) z + n E' E'' ψ (spOver φ ≫ z) = w.1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) := by
  intro R _ X L w hw
  obtain ⟨V, hV⟩ := exists_pt_d_eq_chern hw
  refine ⟨fun E _ _ E' _ _ φ z ↦ V E E' z _ (trivMap φ z), ?_⟩
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  have gen : ∀ (y : Pt X E'') (_ : y = spOver (ψ.comp φ) ≫ z) (f : trivAt z ⟶ trivAt y),
      (∀ c, f.φ c = ψ (φ c)) → V E E'' z _ (trivMap (ψ.comp φ) z) = V E E'' z y f := by
    intro y hy f hf
    subst hy
    exact congrArg (V E E'' z _) (Thick.Hom.ext' (AlgHom.ext fun c ↦ (hf c).symm))
  have hc := gen (spOver ψ ≫ spOver φ ≫ z) (by rw [← Category.assoc, spOver_comp])
    (trivMap φ z ≫ trivMap ψ (spOver φ ≫ z)) fun _ ↦ rfl
  have key := hV E E' E'' z _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) ψ rfl hz
  rw [← hc] at key
  exact key

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseGeneratorOfDualNumberLineBundleGe
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem epsGen_epsEv_apply {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) (u : DualNumber E) :
    epsEv (R := R) e u = u.fst + u.snd * ptAlg (R := R) (D := DualNumber R) e DualNumber.eps := by
  simp [epsEv, DualNumber.lift_apply_apply]

theorem epsGen_epsEv_nat {E E' : Type} [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']
    (ψ : E →ₐ[R] E') (e : Pt (epsR R) E) (u : DualNumber E) :
    epsEv (R := R) (E := E') (spOver ψ ≫ e) (epsHom ψ u) = ψ (epsEv (R := R) e u) := by
  obtain ⟨h1, h2, -⟩ := dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ u
  simp only [epsGen_epsEv_apply, h1, h2, ptAlg_comp, AlgHom.comp_apply, map_add, map_mul]

theorem epsGen_spMap_eq {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) (p : Sp E) :
    (spMap (epsEv (R := R) e : DualNumber E →+* E)).base p =
      (spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)).base p := by
  apply PrimeSpectrum.ext
  ext u
  have hc : ptAlg (R := R) (D := DualNumber R) (E := E) e DualNumber.eps ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, ← map_mul, DualNumber.eps_mul_eps, map_zero]; exact p.asIdeal.zero_mem)
  change epsEv (R := R) e u ∈ p.asIdeal ↔ u.fst ∈ p.asIdeal
  rw [epsGen_epsEv_apply]
  constructor
  · intro h
    have := p.asIdeal.sub_mem h (p.asIdeal.mul_mem_left u.snd hc)
    simpa using this
  · intro h
    exact p.asIdeal.add_mem h (p.asIdeal.mul_mem_left u.snd hc)

theorem epsGen_mem {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) {Y : Scheme.{0}}
    (y : Sp (DualNumber E) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (spMap (epsEv (R := R) e : DualNumber E →+* E) ≫ y) ⁻¹ᵁ U) :
    ⊤ ≤ (spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) ≫ y) ⁻¹ᵁ U := by
  intro p _
  have := h (Set.mem_univ p)
  change y.base ((spMap (epsEv (R := R) e : DualNumber E →+* E)).base p) ∈ U at this
  change y.base ((spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)).base p) ∈ U
  rwa [← epsGen_spMap_eq (R := R) e p]

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem epsGen_red_ptV {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E] (x : Pt A E) :
    spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV (R := R) (D := E) v x =
      x ≫ AbDual.inl A B := by
  have hv' : spOver (TrivSqZeroExt.fstHom R R R) ≫ v = (1 : SpAlg R R ⟶ B) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, spOver_left]
    refine hv.trans ?_
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    change η[B].left = spMap (RingHom.id R) ≫ η[B].left
    rw [Cris.spMap_id, Category.id_comp]
  rw [AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by
      ext a
      simp
    rw [this, spOver_id, Category.id_comp]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (EpsWeil.epsMap R E) =
        (Algebra.ofId R E).comp (TrivSqZeroExt.fstHom R R R) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap]
    rw [this, ← spOver_comp, Category.assoc, hv', MonObj.comp_one]

theorem epsGen_key (v : epsR R ⟶ B) {E : Type} [CommRing E] [Algebra R E] (z : Pt (A ⊗ epsR R) E) :
    z ≫ lift (fst A (epsR R)) (snd A (epsR R) ≫ v) =
      spOver (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))) ≫
        ptV (R := R) (D := E) v (z ≫ fst A (epsR R)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc (spOver _), spOver_comp]
    have : (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))).comp
        (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by
      simp [epsEv]
    rw [this, spOver_id, Category.id_comp]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc (spOver _), spOver_comp]
    have : (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))).comp (EpsWeil.epsMap R E) =
        ptAlg (R := R) (D := DualNumber R) (E := E) (z ≫ snd A (epsR R)) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap, epsEv]
    rw [this, spOver_ptAlg, Category.assoc]

theorem exists_isPtGen_of_isEpsGen : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v →
    ∀ T, IsEpsGen (R := R) (A := A) P v T →
    ∃ t, IsPtGen (R := R) P (lift (fst A (epsR R)) (snd A (epsR R) ≫ v)) t := by
  intro R _ A B _ _ P _ v hv T hT
  obtain ⟨T1, T2, T3⟩ := hT
  have memV : ∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i →
      ⊤ ≤ (ptV (R := R) (D := E) v x).left ⁻¹ᵁ P.U i := by
    intro E _ _ x i h
    apply dualNumberPoint_preimage_top_of_reduction _ E (ptV (R := R) (D := E) v x).left (P.U i)
    have h1 : ⊤ ≤ (x ≫ AbDual.inl A B).left ⁻¹ᵁ P.U i := h
    rw [← epsGen_red_ptV (R := R) (E := E) hv x] at h1
    exact h1
  have memA : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt (A ⊗ epsR R) E) (i : P.ι),
      ⊤ ≤ (z ≫ CartesianMonoidalCategory.lift (fst A (epsR R)) (snd A (epsR R) ≫ v)).left ⁻¹ᵁ P.U i →
      ⊤ ≤ (z ≫ fst _ _).left ⁻¹ᵁ chartsA P i := by
    intro E _ _ z i h
    rw [epsGen_key (R := R) (E := E) v z, Over.comp_left, spOver_left] at h
    have h2 := epsGen_mem (R := R) (E := E) (z ≫ snd A (epsR R)) _ _ h
    have h3 : ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R E E) ≫
        ptV (R := R) (D := E) v (z ≫ fst A (epsR R))).left ⁻¹ᵁ P.U i := h2
    rw [epsGen_red_ptV hv] at h3
    exact h3
  refine ⟨fun E _ _ z i ↦ epsEv (R := R) (E := E) (z ≫ snd A (epsR R))
    (T E (z ≫ fst A (epsR R)) i), ?_, ?_, ?_⟩
  · intro E _ _ z i h
    exact (T1 E (z ≫ fst _ _) i (memA E z i h)).map _
  · intro E _ _ E' _ _ ψ z i h
    have h' := memA E z i h
    simp only [Category.assoc]
    rw [T2 E E' ψ (z ≫ fst A (epsR R)) i h', epsGen_epsEv_nat]
  · intro E _ _ z i j hi hj
    have hi' := memA E z i hi
    have hj' := memA E z j hj
    have hij : ⊤ ≤ (ptV (R := R) (D := E) v (z ≫ fst A (epsR R))).left ⁻¹ᵁ (P.U i ⊓ P.U j) :=
      fun p hp ↦ ⟨memV E _ i hi' hp, memV E _ j hj' hp⟩
    simp only
    rw [T3 E (z ≫ fst A (epsR R)) i j hi' hj', map_mul, epsGen_key (R := R) (E := E) v z,
      Over.comp_left, spOver_left, evalSectionAtPointOrZero_specMap_comp _ _ E
        (epsEv (R := R) (E := E) (z ≫ snd A (epsR R)) : DualNumber E →+* E) _ _ _ hij]
    rfl

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchemePresentingSquareZeroSmoothLiftSystemStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scheme_presenting_squareZeroSmoothLiftSystem : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ S : Sys I π s₀, ∃ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsClosedImmersion i ∧ Surjective i ∧ Nonempty (S.Presents s i) := by
  first | exact @GlobalTheory.LiftGlue.exists_presents | exact GlobalTheory.LiftGlue.exists_presents | (intros; apply GlobalTheory.LiftGlue.exists_presents <;> assumption)
end

