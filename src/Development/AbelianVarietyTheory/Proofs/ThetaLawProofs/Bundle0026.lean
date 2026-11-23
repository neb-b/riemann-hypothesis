module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PullbackSectionsBasisAffineBaseChangeOfAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

variable {X Y T Y' T' : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

theorem affine_gs_appLE {Z : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ W) (f : Γ(X, U)) : gs r z W ((q.appLE U W e).hom f) = gs (r ≫ q) z U f :=
  (gs_res r z e hz _).trans (gs_pull r q z U (e hz) f)

theorem affine_comb (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (j : Y' ⟶ Y) (p₁' : Y' ⟶ T') (g : T' ⟶ T) (w : j ≫ p₁ = p₁' ≫ g) (e : ⊤ ≤ g ⁻¹ᵁ W)
    (c : Fin N → Γ(T, W)) (z : Y') (i : L.ι) (h₂ : p₂ (j z) ∈ L.U i) :
    comb b p₁' (j ≫ p₂) ⊤ (fun k => (g.appLE W ⊤ e).hom (c k)) z i =
      (j.stalkMap z).hom (comb b p₁ p₂ W c (j z) i) := by
  have h₁ : p₁ (j z) ∈ W := by
    have : (j ≫ p₁) z ∈ W := by rw [w]; exact e (show p₁' z ∈ (⊤ : T'.Opens) from trivial)
    exact this
  rw [← comb_comp b j p₁ p₂ W c z i h₁ h₂, comb, comb]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [affine_gs_appLE g W ⊤ e p₁' z trivial, w]

theorem affine_transfer (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (j : Y' ⟶ Y) (p₁' : Y' ⟶ T') (g : T' ⟶ T) [IsOpenImmersion g] (sq : IsPullback j p₁' p₁ g)
    (hr : Set.range g = W) (e : ⊤ ≤ g ⁻¹ᵁ W) (hb : Function.Bijective (g.appLE W ⊤ e).hom)
    (h₁ : IndepOn b p₁' (j ≫ p₂) ⊤) (h₂ : SpanOn b p₁' (j ≫ p₂) ⊤) :
    IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W := by
  have hj : IsOpenImmersion j := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  have hW : ∀ z : Y', p₁ (j z) ∈ W := fun z => by
    have : (j ≫ p₁) z ∈ W := by rw [sq.w]; exact e (show p₁' z ∈ (⊤ : T'.Opens) from trivial)
    exact this
  refine ⟨fun c hc => ?_, fun σ hσ => ?_⟩
  · have := h₁ (fun k => (g.appLE W ⊤ e).hom (c k)) (fun z i _ hz => by
      rw [affine_comb b p₁ p₂ W j p₁' g sq.w e c z i hz, hc (j z) i (hW z) hz, map_zero])
    funext k
    apply hb.1
    rw [Pi.zero_apply, map_zero]
    exact congrFun this k
  · have le : ∀ i, p₁' ⁻¹ᵁ ⊤ ⊓ (j ≫ p₂) ⁻¹ᵁ L.U i ≤ j ⁻¹ᵁ (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i) :=
      fun i z hz => ⟨hW z, hz.2⟩
    have key : ∀ (z : Y') (i : L.ι), p₂ (j z) ∈ L.U i →
        gs (𝟙 Y') z _ ((j.appLE _ _ (le i)).hom (σ i)) = (j.stalkMap z).hom (gs (𝟙 Y) (j z) _ (σ i)) := by
      intro z i hz
      rw [affine_gs_appLE j _ _ (le i) (𝟙 Y') z ⟨trivial, hz⟩, Category.id_comp,
        ← gs_comp j (𝟙 Y) z (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i) ⟨hW z, hz⟩, Category.comp_id]
    obtain ⟨c', hc'⟩ := h₂ (fun i => (j.appLE _ _ (le i)).hom (σ i)) (fun z i i' _ hi hi' => by
      rw [key z i hi, key z i' hi', hσ (j z) i i' (hW z) hi hi', map_mul]
      congr 1
      have : gm (j ≫ p₂) z (L.U i ⊓ L.U i') (L.g i i') =
          Units.map (j.stalkMap z).hom.toMonoidHom (gm p₂ (j z) (L.U i ⊓ L.U i') (L.g i i')) := by
        apply Units.ext
        rw [← gs_unit (j ≫ p₂) z (L.U i ⊓ L.U i') ⟨hi, hi'⟩, gs_comp j p₂ z (L.U i ⊓ L.U i') ⟨hi, hi'⟩,
          gs_unit p₂ (j z) (L.U i ⊓ L.U i') ⟨hi, hi'⟩]
        rfl
      rw [this, ← map_zpow (Units.map (j.stalkMap z).hom.toMonoidHom)]
      rfl)
    choose c hc using fun k => hb.2 (c' k)
    refine ⟨c, fun y i hy hi => ?_⟩
    obtain ⟨s, hs⟩ : p₁ y ∈ Set.range g := by rw [hr]; exact hy
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback sq y s hs.symm
    apply (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1
    have := hc' z i trivial hi
    rw [key z i hi, ← funext hc, affine_comb b p₁ p₂ W j p₁' g sq.w e c z i hi] at this
    exact this

theorem indepOn_spanOn_of_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), (∀ (R' : Type) [CommRing R'] (f : R →+* R'), ∃ (Y : Scheme.{0}) (p₁ : Y ⟶ Sp R') (p₂ : Y ⟶ X), IsPullback p₂ p₁ p (spMap f) ∧ GlobalTheory.RelBasis.IndepOn b p₁ p₂ ⊤ ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ ⊤) → ∀ (T Y : Scheme.{0}) (q : T ⟶ Sp R) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), IsPullback p₂ p₁ p q → ∀ W : T.Opens, IsAffineOpen W → GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W := by
  intro R _ X p L t N b H T Y q p₁ p₂ sq W hW
  obtain ⟨Y', p₁', p₂', sq', h₁, h₂⟩ := H Γ(T, W) (Spec.preimage (hW.fromSpec ≫ q)).hom
  have hf : spMap (Spec.preimage (hW.fromSpec ≫ q)).hom = hW.fromSpec ≫ q := Spec.map_preimage _
  rw [hf] at sq'
  let j : Y' ⟶ Y := sq.lift p₂' (p₁' ≫ hW.fromSpec) (by rw [sq'.w, Category.assoc])
  have e₂ : j ≫ p₂ = p₂' := sq.lift_fst _ _ _
  have e₁ : j ≫ p₁ = p₁' ≫ hW.fromSpec := sq.lift_snd _ _ _
  rw [← e₂] at sq' h₁ h₂
  have sq'' : IsPullback j p₁' p₁ hW.fromSpec := IsPullback.of_right (by simpa using sq') e₁ sq
  have e : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge
  refine affine_transfer b p₁ p₂ W j p₁' hW.fromSpec sq'' hW.range_fromSpec e ?_ h₁ h₂
  have : hW.fromSpec.appLE W ⊤ e = (Scheme.ΓSpecIso Γ(T, W)).inv := by
    rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ ((congrArg _ (Subsingleton.elim _ _)).trans (CategoryTheory.Functor.map_id _ _))).trans
      (Category.comp_id _)
  rw [this]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(T, W)).inv

end GlobalTheory.RelBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PullbackSectionsBasisOfAffineOpens
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

theorem comb_res (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) {V W : T.Opens} (hle : V ≤ W)
    (c : Fin N → Γ(T, W)) (y : Y) (i : L.ι) (h : p₁ y ∈ V) :
    comb b p₁ p₂ V (fun k => (T.presheaf.map (homOfLE hle).op).hom (c k)) y i = comb b p₁ p₂ W c y i := by
  unfold comb
  exact Finset.sum_congr rfl fun k _ => by rw [gs_res p₁ y hle h]

theorem comb_sub (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) {W : T.Opens}
    (c c' : Fin N → Γ(T, W)) (y : Y) (i : L.ι) (h : p₁ y ∈ W) :
    comb b p₁ p₂ W (c - c') y i = comb b p₁ p₂ W c y i - comb b p₁ p₂ W c' y i := by
  unfold comb
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gs_eq_gsHom p₁ y W h, Pi.sub_apply, map_sub, sub_mul]

theorem exists_affine_le (W : T.Opens) (x : T) (hx : x ∈ W) :
    ∃ V : T.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ W := by
  obtain ⟨V, hV, hxV, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens) hx
  exact ⟨V, hV, hxV, hle⟩

theorem indepOn_of_affine (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X)
    (H : ∀ W : T.Opens, IsAffineOpen W → IndepOn b p₁ p₂ W) (W : T.Opens) : IndepOn b p₁ p₂ W := by
  intro c hc
  funext k
  refine fn_ext fun x hx => ?_
  obtain ⟨V, hV, hxV, hle⟩ := exists_affine_le W x hx
  have h0 := H V hV (fun k => (T.presheaf.map (homOfLE hle).op).hom (c k)) fun y i h₁ h₂ =>
    (comb_res b p₁ p₂ hle c y i h₁).trans (hc y i (hle h₁) h₂)
  have hk : (T.presheaf.map (homOfLE hle).op).hom (c k) = 0 := congrFun h0 k
  have hxV' : (𝟙 T : T ⟶ T) x ∈ V := hxV
  rw [← gs_res (𝟙 T) x hle hxV', ← gs_res (𝟙 T) x hle hxV', hk, Pi.zero_apply, map_zero]

theorem basis_of_affine (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t))
    (p₁ : Y ⟶ T) (p₂ : Y ⟶ X)
    (H : ∀ W : T.Opens, IsAffineOpen W → IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W) (W : T.Opens) :
    IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W := by
  have hI := indepOn_of_affine b p₁ p₂ fun W hW => (H W hW).1
  refine ⟨hI W, fun σ hσ => ?_⟩
  let Ix := {V : T.Opens // IsAffineOpen V ∧ V ≤ W}
  have hloc : ∀ V : Ix, ∃ c : Fin N → Γ(T, V.1), ∀ (y : Y) (i : L.ι), p₁ y ∈ V.1 → p₂ y ∈ L.U i →
      gs (𝟙 Y) y _ (σ i) = comb b p₁ p₂ V.1 c y i := by
    intro V
    have hle : ∀ i, p₁ ⁻¹ᵁ V.1 ⊓ p₂ ⁻¹ᵁ L.U i ≤ p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i := fun i y hy => ⟨V.2.2 hy.1, hy.2⟩
    have hr : ∀ (y : Y) i, p₁ y ∈ V.1 → p₂ y ∈ L.U i →
        gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (hle i)).op).hom (σ i)) = gs (𝟙 Y) y _ (σ i) :=
      fun y i h₁ h₂ => gs_res (𝟙 Y) y (hle i) ⟨h₁, h₂⟩ _
    obtain ⟨c, hc⟩ := (H V.1 V.2.1).2 (fun i => (Y.presheaf.map (homOfLE (hle i)).op).hom (σ i))
      (fun y i i' h₁ h₂ h₃ => (hr y i h₁ h₂).trans ((hσ y i i' (V.2.2 h₁) h₂ h₃).trans
        (congrArg _ (hr y i' h₁ h₃).symm)))
    exact ⟨c, fun y i h₁ h₂ => (hr y i h₁ h₂).symm.trans (hc y i h₁ h₂)⟩
  choose c hc using hloc
  have hcomp : ∀ V V' : Ix, (fun k => (T.presheaf.map (homOfLE (inf_le_left : V.1 ⊓ V'.1 ≤ V.1)).op).hom (c V k)) =
      (fun k => (T.presheaf.map (homOfLE (inf_le_right : V.1 ⊓ V'.1 ≤ V'.1)).op).hom (c V' k)) := by
    intro V V'
    refine sub_eq_zero.1 (hI (V.1 ⊓ V'.1) _ fun y i h₁ h₂ => ?_)
    rw [comb_sub b p₁ p₂ _ _ y i h₁, comb_res b p₁ p₂ _ _ y i h₁, comb_res b p₁ p₂ _ _ y i h₁,
      ← hc V y i h₁.1 h₂, ← hc V' y i h₁.2 h₂, sub_self]
  have glue : ∀ k, ∃ a : Γ(T, W), ∀ V : Ix, (T.presheaf.map (homOfLE V.2.2).op).hom a = c V k := by
    intro k
    obtain ⟨a, ha, -⟩ := T.sheaf.existsUnique_gluing' (fun V : Ix => V.1) W (fun V => homOfLE V.2.2)
      (fun x hx => by
        obtain ⟨V, hV, hxV, hle⟩ := exists_affine_le W x hx
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hle⟩, hxV⟩) (fun V => c V k)
      (fun V V' => congrFun (hcomp V V') k)
    exact ⟨a, ha⟩
  choose a ha using glue
  refine ⟨a, fun y i h₁ h₂ => ?_⟩
  obtain ⟨V, hV, hyV, hle⟩ := exists_affine_le W (p₁ y) h₁
  rw [hc ⟨V, hV, hle⟩ y i hyV h₂, ← comb_res b p₁ p₂ hle a y i hyV]
  exact congrArg (fun c => comb b p₁ p₂ V c y i) (funext fun k => (ha k ⟨V, hV, hle⟩).symm)

end GlobalTheory.RelBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PullbackSectionsSpanTwistedOfIndepSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

theorem boxSpan_of_indep_span (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t))
    (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (hL : L.IsLB) (H : ∀ W : T.Opens, IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W) :
    BoxSpan b p₁ p₂ := by
  intro K _ φ ε s
  have mem : ∀ (j : K → L.ι) (i : L.ι) (y : Y), p₁ y ∈ LB.wchart L φ j → p₂ y ∈ L.U i →
      y ∈ LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)) := by
    intro j i y h₁ h₂
    refine Set.mem_iInter.2 ?_
    rintro (k | k)
    exacts [Set.mem_iInter.1 h₁ k, h₂]
  have tr : ∀ (j j' : K → L.ι) (i i' : L.ι) (y : Y), p₁ y ∈ LB.wchart L φ j → p₂ y ∈ L.U i →
      p₁ y ∈ LB.wchart L φ j' → p₂ y ∈ L.U i' →
      gs (𝟙 Y) y (LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)))
          (s.f (Sum.elim j (fun _ => i))) =
        (trF φ ε p₁ y j j').val * (gm p₂ y (L.U i ⊓ L.U i') (L.g i i') ^ t).val *
        gs (𝟙 Y) y (LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j' (fun _ => i')))
          (s.f (Sum.elim j' (fun _ => i'))) := by
    intro j j' i i' y h₁ h₂ h₁' h₂'
    rw [sec_trans s (𝟙 Y) y (mem j i y h₁ h₂) (mem j' i' y h₁' h₂'), trF, Fintype.prod_sum_type, Units.val_mul,
      @Fintype.prod_unique _ PUnit]
    simp only [trF, Category.id_comp, Sum.elim_inl, Sum.elim_inr]
    rfl
  have hc : ∀ j : K → L.ι, ∃ c : Fin N → Γ(T, LB.wchart L φ j), ∀ (y : Y) (i : L.ι), p₁ y ∈ LB.wchart L φ j →
      p₂ y ∈ L.U i →
      gs (𝟙 Y) y (LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)))
          (s.f (Sum.elim j (fun _ => i))) = comb b p₁ p₂ _ c y i := by
    intro j
    have le : ∀ i, p₁ ⁻¹ᵁ LB.wchart L φ j ⊓ p₂ ⁻¹ᵁ L.U i ≤
        LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)) :=
      fun i y hy => mem j i y hy.1 hy.2
    obtain ⟨c, hc⟩ := (H (LB.wchart L φ j)).2
      (fun i => (Y.presheaf.map (homOfLE (le i)).op).hom (s.f (Sum.elim j (fun _ => i)))) (by
        intro y i i' h₁ h₂ h₂'
        have e := tr j j i i' y h₁ h₂ h₁ h₂'
        rw [mul_eq_left.1 (trF_trans hL φ ε p₁ y h₁ h₁ h₁), Units.val_one, _root_.one_mul] at e
        exact (gs_res (𝟙 Y) y (le i) ⟨h₁, h₂⟩ _).trans
          (e.trans (congrArg _ (gs_res (𝟙 Y) y (le i') ⟨h₁, h₂'⟩ _).symm)))
    exact ⟨c, fun y i h₁ h₂ => (gs_res (𝟙 Y) y (le i) ⟨h₁, h₂⟩ _).symm.trans (hc y i h₁ h₂)⟩
  choose c hc using hc
  have compat : ∀ j j' : K → L.ι, ∀ k,
      (T.presheaf.map (homOfLE (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j k) =
        (show Γ(T, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (T.presheaf.map (homOfLE (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j' k) := by
    intro j j' k
    refine sub_eq_zero.1 (congrFun ((H (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 (fun k =>
      (T.presheaf.map (homOfLE (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j k) -
        (show Γ(T, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (T.presheaf.map (homOfLE (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j' k)) ?_) k)
    intro y i h₁ h₂
    have e := tr j j' i i y h₁.1 h₂ h₁.2 h₂
    rw [hc j y i h₁.1 h₂, hc j' y i h₁.2 h₂, gm_self hL p₂ y h₂, one_zpow, Units.val_one, _root_.mul_one, comb, comb,
      Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    refine (Finset.sum_congr rfl fun k _ => ?_).trans e
    have u : gs p₁ y (LB.wchart L φ j ⊓ LB.wchart L φ j')
        (show Γ(T, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val =
        (trF φ ε p₁ y j j').val :=
      (gs_unit p₁ y _ h₁ _).trans (congrArg Units.val (gm_linComb L φ ε p₁ y j j' h₁.1 h₁.2))
    rw [gs_eq_gsHom p₁ y _ h₁, map_sub, ← gs_eq_gsHom, ← gs_eq_gsHom, gs_mul p₁ y _ h₁, u,
      gs_res p₁ y _ h₁, gs_res p₁ y _ h₁, sub_mul, _root_.mul_assoc]
  refine ⟨fun k => ⟨fun j => c j k, fun j j' => compat j j' k⟩, fun Z r z J hJ => ?_⟩
  have h₁ : p₁ (r z) ∈ LB.wchart L φ (fun k => J (r ≫ p₁ ≫ φ k)) :=
    Set.mem_iInter.2 fun k => hJ (r ≫ p₁ ≫ φ k)
  have h₂ : p₂ (r z) ∈ L.U (J (r ≫ p₂)) := hJ (r ≫ p₂)
  have e := (gs_comp r (𝟙 Y) z _ (mem _ _ _ h₁ h₂) _).trans ((congrArg (r.stalkMap z).hom (hc _ (r z) _ h₁ h₂)).trans
    (comb_comp b r p₁ p₂ _ _ z _ h₁ h₂).symm)
  rw [Category.comp_id] at e
  rw [sval_of s r z J (Sum.elim (fun k => J (r ≫ p₁ ≫ φ k)) (fun _ => J (r ≫ p₂))) (by rintro (k | k) <;> rfl)]
  refine e.trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [sval_of _ (r ≫ p₁) z J (fun k => J (r ≫ p₁ ≫ φ k)) (fun k => by rw [Category.assoc])]

end GlobalTheory.RelBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TransversalZerosOfJacobianNeZeroDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa
open EtBaseChange

theorem section_ext_of_apply_eq {K : Type} [Field K] {X : Scheme.{0}} (t : X ⟶ Sp K) (a b : Sp K ⟶ X)
    (ha : a ≫ t = 𝟙 _) (hb : b ≫ t = 𝟙 _) (p : Sp K) (h : a p = b p) : a = b := by
  obtain ⟨⟨y, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective a
  obtain ⟨⟨y', β⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hb h ⊢
  have hy : y = y' := by simpa using h
  subst hy
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField y ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at ha hb
  have h₁ := Spec.map_injective ha
  have h₂ := Spec.map_injective hb
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun q => q.hom k) h₁
  have e₂ : ∀ k, β.hom (c.hom k) = k := fun k => congrArg (fun q => q.hom k) h₂
  have : α = β := by
    ext k
    have e₃ : c.hom (α.hom k) = k := α.hom.injective (e₁ _)
    exact (e₂ (α.hom k)).symm.trans (congrArg β.hom e₃)
  rw [this]

theorem etZ_of_jac_ne_zero : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] (x : KeyIn O) (x' : KeyIn K) (f : O →+* K) φ w (n d : ℕ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), Function.Injective f → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, (∃ q : Sp K, spMap f q = x.P.A.hom y) → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (z' : Fin d → Pt x') (ch' : Fin d → x'.P.L.ι) (u : Fin d → Kˣ), EtZ x' s' z' ch' ∧ ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l = f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := by
  intro O K _ _ _ x x' f φ w n d hg s s' z ch hf ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ hs hz₁ hz₂ hz₃ hz₄ hz₅
  have hw : ∀ a, (spMap f ≫ (z a).left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f := fun a =>
    (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w (z a))).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  let z' : Fin d → Pt x' := fun a => Over.homMk (hp.1.lift (spMap f ≫ (z a).left) (𝟙 _) (hw a)) (hp.1.lift_snd _ _ _)
  have hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left := fun a => hp.1.lift_fst _ _ _
  have hch : ∀ a, ∃ i, ⊤ ≤ (z' a).left ⁻¹ᵁ x'.P.L.U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB ((z' a).left (IsLocalRing.closedPoint K))
    exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map (z' a).left.continuous).mem_open
      (x'.P.L.U i).isOpen hi⟩
  choose ch' hch' using hch
  have hφ : ∀ a, ⊤ ≤ ((z' a).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun a p _ => by
    rw [hz' a]
    exact hz₁ a (show spMap f p ∈ ⊤ from trivial)
  have hW := fun a => le_inf_pull (T := K) (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
  let u : Fin d → Kˣ := fun a => Units.map (valH (T := K) (z' a).left _ (hW a)).toMonoidHom (w.s (fun _ => ch a, ch' a))
  have hu : ∀ a, valT (T := K) (z' a).left ((x.P.L.pull φ).U (fun _ => ch a) ⊓ x'.P.L.U (ch' a))
      (w.s (fun _ => ch a, ch' a)).val = u a := fun a => valT_eq _ _ (hW a) _
  have hval : ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg →
      valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l =
        f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := fun l sg sg' a h => by
    have e := valT_via (T := K) h (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
    rw [hu] at e
    refine (_root_.mul_comm _ _).trans (e.symm.trans ?_)
    exact (congrArg (fun q => valT (T := K) q (x.P.L.U (ch a)) (sg.f (ch a))) (hz' a)).trans
      (valT_spMap f (z a).left (hz₁ a) _)
  have hzero : ∀ a i, valT (T := K) (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by
    have e := hval n _ _ a (hs i)
    rw [hz₂, map_zero] at e
    exact ((u a).isUnit.pow n).mul_left_eq_zero.1 e
  have hjac : ∀ a, jac x' s' (z' a) (ch' a) * (u a : K) ^ (x.P.g * n) = f (jac x s (z a) (ch a)) := fun a => by
    have ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T := DualNumber O) ((toUnit (epsR O) ≫ z a) * x.v (k.cast hg)).left
        (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a)))) = (u a : K) ^ n * TrivSqZeroExt.snd (valT (T := DualNumber K)
          ((toUnit (epsR K) ≫ z' a) * x'.v k).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a))) := fun i k => by
      have c := translate_comp hp F hF₁ (z a) (z' a) (hz' a) (x.v (k.cast hg)) (x'.v k) (hv k)
      have l₁ := translate_le (z a) (x.v (k.cast hg)) (x.basis.1 _) (hz₁ a)
      have l₂ := translate_le (z' a) (x'.v k) (x'.basis.1 _) (hch' a)
      have l₃ : ⊤ ≤ (((toUnit (epsR K) ≫ z' a) * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun p _ => by
        rw [c]
        exact l₁ (show spMap F p ∈ ⊤ from trivial)
      have e := valT_via (T := DualNumber K) (hs i) _ (ch a) (ch' a) l₃ l₂
      have e₂ := (congrArg (fun q => valT (T := DualNumber K) q (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a))) c).trans
        (valT_spMap F _ l₁ _)
      refine (snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)
      refine (snd_pow_mul _ _ _ ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hch' a) _).trans (hzero a i))).trans ?_
      exact congrArg (· ^ n * _) ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hW a) _).trans (hu a))
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n,
      pow_mul]
    have hc : x.P.g = Fintype.card (Fin x'.P.g) := hg.symm.trans (Fintype.card_fin _).symm
    refine (congrArg (fun m => ((u a : K) ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)
    congr 1
    ext i k
    exact (ent i k).symm
  refine ⟨z', ch', u, ⟨hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩, hval⟩
  · have hne : f (jac x s (z a) (ch a)) ≠ 0 := fun h => hz₃ a (hf (h.trans (map_zero f).symm))
    exact isUnit_of_mul_isUnit_left (hjac a ▸ hne.isUnit)
  · have e₀ : (z' a).left = (z' a').left :=
      section_ext_of_apply_eq x'.P.A.hom (z' a).left (z' a').left (Over.w (z' a)) (Over.w (z' a')) p e
    have e₁ : spMap f ≫ (z a).left = spMap f ≫ (z a').left :=
      (hz' a).symm.trans ((congrArg (· ≫ φ) e₀).trans (hz' a'))
    have : IsDominant (spMap f) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot f).1 hf]; exact bot_le)⟩
    have : IsProper x.P.A.hom := x.P.isAb.proper
    exact h (hz₄ (Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp O) x.P.A.hom
      ((Over.w (z a)).trans (Over.w (z a')).symm) (spMap f) e₁)))
  · obtain ⟨a, p, hp'⟩ := hz₅ (φ y) ⟨x'.P.A.hom y, (congrArg (fun q => q y) hp.1.w).symm⟩
      fun i h => hy (i.cast hg.symm) (mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)
    have sq : IsPullback (spMap f) (z' a).left (z a).left φ := by
      refine IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm
      have e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _ := Over.w (z' a)
      have e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _ := Over.w (z a)
      rw [e₁, e₂]
      exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp K)) (f := 𝟙 (Sp O)) (g := spMap f) ⟨by simp⟩
    obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq p y hp'
    exact ⟨a, q, hq⟩

end GlobalTheory.KeyKa
end
end

