module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteDimensionalField
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelDominatedOfMapToBaseModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models.Domination

noncomputable def toRing {T : Scheme.{0}} {R : Type} [CommRing R] (u : T ⟶ Sp R) : R →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ u.appTop).hom

theorem toRing_inj {T : Scheme.{0}} {R : Type} [CommRing R] {u v : T ⟶ Sp R} (h : toRing u = toRing v) : u = v := by
  apply ext_of_isAffine
  exact (cancel_epi _).1 (CommRingCat.hom_ext h)

theorem toRing_comp {T : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (u : T ⟶ Sp R') (b : R →+* R') :
    toRing (u ≫ spMap b) = (toRing u).comp b := by
  unfold toRing
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

theorem eq_of_overring {T : Scheme.{0}} {O O' F : Type} [CommRing O] [CommRing O'] [Field F] {β : O →+* F}
    {β' : O' →+* F} {b : O →+* O'} (hβ : IsDedFrac β) (hβ' : IsDedFrac β') (hb : β'.comp b = β) (u : T ⟶ Sp O')
    (w : T ⟶ Sp F) (h : u ≫ spMap b = w ≫ spMap β) : u = w ≫ spMap β' := by
  obtain ⟨⟨_, -⟩, -, hf⟩ := hβ
  obtain ⟨-, -, hf'⟩ := hβ'
  apply toRing_inj
  have h' := congrArg toRing h
  rw [toRing_comp, toRing_comp] at h'
  rw [toRing_comp]
  ext x
  letI := β.toAlgebra
  have hinj : Function.Injective β' := by
    letI := β'.toAlgebra
    exact IsFractionRing.injective O' F
  obtain ⟨p, q, hq, e⟩ := IsFractionRing.div_surjective (A := O) (β' x)
  have hq0 : β q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have e' : β' x * β q = β p := by
    rw [← e]; exact div_mul_cancel₀ _ hq0
  have e₂ : x * b q = b p := by
    apply hinj
    rw [map_mul]
    have := RingHom.congr_fun hb
    simp only [RingHom.comp_apply] at this
    rw [this, this, e']
  have hu : IsUnit (toRing w (β q)) := (IsUnit.mk0 _ hq0).map _
  have k₁ : ∀ y, toRing u (b y) = toRing w (β y) := RingHom.congr_fun h'
  apply hu.mul_right_cancel
  rw [RingHom.comp_apply, ← map_mul, e', ← k₁, ← k₁, ← map_mul, e₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_of_RZ {T : Scheme.{0}} {l : Level H} {S A : ℕ} (hA : l.A = A) {β : RZ H S A →+* KA l}
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) (u v : T ⟶ Sp (KA l))
    (h : u ≫ spMap β = v ≫ spMap β) : u = v := by
  apply toRing_inj
  have h' := congrArg toRing h
  rw [toRing_comp, toRing_comp] at h'
  have k₁ : ∀ y, toRing u (β y) = toRing v (β y) := RingHom.congr_fun h'
  have k₂ : ∀ (x : ℂ) (hx : x ∈ KA l), x ∈ RZ H S A → toRing u ⟨x, hx⟩ = toRing v ⟨x, hx⟩ := fun x hx hx' => by
    have : β ⟨x, hx'⟩ = ⟨x, hx⟩ := Subtype.ext (hβ _)
    rw [← this, k₁]
  let K : Subfield ℂ := ((toRing u).eqLocusField (toRing v)).map (KA l).val.toRingHom
  have hK : (KA l).toSubfield ≤ K := by
    have : KA l ≤ K.toIntermediateField (fun x => by simp) := by
      unfold KA
      rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      · have m₁ : (1 + H.rt0) / 2 ∈ RZ H S A := Subring.subset_closure (by simp)
        have m₂ : H.rt0 ∈ RZ H S A := by
          have : H.rt0 = (1 + H.rt0) / 2 + (1 + H.rt0) / 2 - 1 := by ring
          rw [this]
          exact sub_mem (add_mem m₁ m₁) (one_mem _)
        exact ⟨(baseKA l).ρ, k₂ _ _ m₂, rfl⟩
      · exact ⟨(baseKA l).ζ, k₂ _ _ (Subring.subset_closure (by simp [hA])), rfl⟩
    exact this
  ext x
  obtain ⟨y, hy, e⟩ := hK x.2
  have : y = x := Subtype.ext e
  exact this ▸ hy

theorem dominates_of_map_to_base : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model (Xo l) c β) (Y' : Model (Xo l) c β') (b : O →+* O') (f : pullback Y.s (spMap b) ⟶ B.C.X) (t : SAB H (pullback Y.s (spMap b))) (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t B.C.t f) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap Y.oF.t (Xo l₀).univ.t r) (k : KA l₀ →+* c.F), IsDedFrac β → IsDedFrac β' → β'.comp b = β → Raises B Y' → LevComp Y.oF (Xo l₀).univ r ν → IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k → r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k → (∀ g : (Xo l).XF c ⟶ pullback Y.s (spMap b), g ≫ pullback.fst _ _ = Y.j → g ≫ f = r ≫ B.C.j) → (∀ y : Y.oF.t.G.left ⟶ t.G.left, y ≫ m₁.φ = Y.m.φ → y ≫ m₂.φ = ν.φ ≫ B.C.m.φ) → Dominates Y Y' b := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N T l₀ l B c O O' _ _ β β' Y Y' b f t m₁ m₂ r ν k hβ hβ' hb hR hν hk hr hf hφ
  obtain ⟨b₀, r₀, ν₀, hb₀, hν₀, ⟨a₀⟩⟩ := hR

  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y'.m0.toSABMap Y.m0.toSABMap (𝟙 _) (Category.id_comp _)
  have η₁ : ∀ x, (Y.oF.eta x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.eta x).left := fun x =>
    LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by
      rw [hν', Category.id_comp]; exact (Y.m0.eta x).trans (Y'.m0.eta x).symm)
  have η₂ : ∀ x, (Y.oF.etaA x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.etaA x).left := fun x =>
    LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by
      rw [hν', Category.id_comp]; exact (Y.m0.etaA x).trans (Y'.m0.etaA x).symm)
  obtain ⟨ν₁, hν₁⟩ := LevelCover.sab_comp ν' ν₀ (Category.id_comp r₀)
  have hl₁ : LevComp Y.oF (Xo l₀).univ r₀ ν₁ := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hν₁, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₁ x), Category.id_comp, hν₀.1]
    · rw [hν₁, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₂ x), Category.id_comp, hν₀.2]
  have hkb : k.comp B.β = β'.comp b₀ := RingHom.ext fun x => Subtype.ext
    ((hk (B.β x)).trans ((B.β_inc x).trans (hb₀ x).symm))
  have hrB : r ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap (β'.comp b₀) := by
    rw [Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc, hr, Category.assoc, ← spMap_comp, hkb]
  have hrr : r ≫ (Xo l₀).s = r₀ ≫ (Xo l₀).s := by
    apply eq_of_RZ B.A_one B.β_inc
    rw [Category.assoc, Category.assoc, ← Cpt.openImmersion_comp_structure_eq_generic B.C, hrB, ← Category.assoc, ← a₀.j_comm, Category.assoc,
      a₀.π_over, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]
  have hred : IsReduced ((Xo l).XF c) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ (pullback.snd _ _)
      inferInstance).1
  obtain ⟨rfl, hνν⟩ := GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H D l₀ l (Xo l₀) _ _ _ _ Y.oF r r₀ ν ν₁ hred hrr hν hl₁

  obtain ⟨ido, hid⟩ := ObjMaps.exists_sab_id Y.oF.t
  obtain ⟨C, a, hiso⟩ := _root_.GlobalTheory.Models.Cpt.exists_above_isIso_of_overring E H _ c.F O _ Y.oF.t β O' β' b (ofModel Y) ido hid hβ hβ' hb
  obtain ⟨e, π, mu, _, e₁, e₂, hj, hm⟩ : ∃ (e : C.X ⟶ pullback Y.s (spMap b)) (π : C.X ⟶ Y.X) (mu : SABMap C.t Y.t π),
      IsIso e ∧ e ≫ pullback.fst _ _ = π ∧ e ≫ pullback.snd _ _ = C.s ∧ C.j ≫ π = Y.j ∧ C.m.φ ≫ mu.φ = Y.m.φ :=
    ⟨pullback.lift a.π C.s a.π_over, a.π, a.mu, hiso, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      a.j_comm.trans (Category.id_comp _), a.φ_comm.trans (by rw [hid]; exact Category.id_comp _)⟩
  have hje : ∀ (S : Scheme.{0}) (u : S ⟶ pullback Y.s (spMap b)) (x : S ⟶ (Xo l).XF c),
      u ≫ pullback.fst _ _ = x ≫ Y.j → u = x ≫ C.j ≫ e := fun S u x h => by
    apply pullback.hom_ext
    · rw [h, Category.assoc, Category.assoc, e₁, hj]
    · rw [Category.assoc, Category.assoc, e₂, Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc]
      apply eq_of_overring hβ hβ' hb
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, h, Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) (Cpt.openImmersion_comp_structure_eq_generic (ofModel Y))
  have hjf : C.j ≫ e ≫ f = r ≫ B.C.j := by
    rw [← Category.assoc]
    exact hf _ (by rw [Category.assoc, e₁, hj])
  obtain ⟨κ, hκ⟩ := LevelCover.sab_cancel m₁ mu e e₁
  obtain ⟨κ₂, hκ₂⟩ := LevelCover.sab_comp κ m₂ rfl
  have hm₁ : (C.m.φ ≫ κ.φ) ≫ m₁.φ = Y.m.φ := by
    rw [Category.assoc, hκ, hm]
  have hover : (e ≫ f) ≫ B.C.s = C.s ≫ spMap ((RingHom.id O').comp b₀) := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ'
    letI := β'.toAlgebra
    obtain ⟨-, -, -, -, -, h3, -⟩ :=
      GlobalTheory.genericPart_dense_proOpen O' c.F C.X _ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
    have : IsDominant C.j := h3
    have : IsReduced C.X := by
      have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
        have := (C.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk _
    apply ext_of_isDominant C.j
    rw [← Category.assoc, hjf, Category.assoc, hrB, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]
  obtain ⟨h₀, κ₀, hh₀, -, -, hjh₀, hmh₀, -⟩ := Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C
    (ofModel Y') C b₀ (RingHom.id O') (RingHom.id c.F) r ν₀ a₀ (𝟙 _) ν' (e ≫ f) κ₂ hover hβ' rfl
    (by rw [LevelCover.spMap_id', Category.id_comp, Category.comp_id]) (by rw [hjf, Category.id_comp])
    (by rw [hκ₂, ← Category.assoc, hφ _ hm₁, hνν, hν₁, Category.assoc])
  obtain ⟨h, κ', hh, hjh, hmh⟩ : ∃ (h : C.X ⟶ Y'.X) (κ' : SABMap C.t Y'.t h), h ≫ Y'.s = C.s ∧ C.j ≫ h = Y'.j ∧
      C.m.φ ≫ κ'.φ = ν'.φ ≫ Y'.m.φ :=
    ⟨h₀, κ₀, hh₀.trans (by rw [LevelCover.spMap_id', Category.comp_id]), hjh₀.trans (Category.id_comp _), hmh₀⟩
  obtain ⟨idt, hid'⟩ := ObjMaps.exists_sab_id t
  obtain ⟨κi, hκi⟩ := LevelCover.sab_cancel κ idt (inv e) (IsIso.inv_hom_id e)
  obtain ⟨m₃, hm₃⟩ := LevelCover.sab_comp κi κ' rfl
  have hκκ : κ.φ ≫ κi.φ = 𝟙 _ := by
    apply κ.cart.1.hom_ext
    · change (κ.φ ≫ κi.φ) ≫ κ.φ = 𝟙 _ ≫ κ.φ
      rw [Category.assoc, hκi, hid', Category.comp_id, Category.id_comp]
    · have w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e := κ.cart.1.w
      have w₂ : κi.φ ≫ C.t.G.hom = t.G.hom ≫ inv e := κi.cart.1.w
      rw [Category.assoc, w₂, ← Category.assoc, w₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        Category.id_comp]
  refine ⟨inv e ≫ h, t, m₁, m₃, ?_, fun u hu => ?_, fun S g g₁ g₂ q₁ q₂ q₃ => ?_⟩
  · rw [Category.assoc, hh, ← e₂, IsIso.inv_hom_id_assoc]
  · rw [hje _ u (𝟙 _) (by rw [hu, Category.id_comp]), Category.id_comp, Category.assoc, IsIso.hom_inv_id_assoc, hjh]
  · have w₀ : ν'.φ ≫ Y'.oF.t.G.hom = Y.oF.t.G.hom := ν'.cart.1.w.trans (Category.comp_id _)
    have s₂ : g₂ = g₁ ≫ ν'.φ := by
      apply Y'.m0.toSABMap.cart.1.hom_ext
      · change g₂ ≫ Y'.m0.toSABMap.φ = (g₁ ≫ ν'.φ) ≫ Y'.m0.toSABMap.φ
        rw [Category.assoc, hν', q₂]
      · rw [Category.assoc, w₀, q₃]
    have s₁ : g = g₁ ≫ C.m.φ ≫ κ.φ := by
      apply m₁.cart.1.hom_ext
      · change g ≫ m₁.φ = (g₁ ≫ C.m.φ ≫ κ.φ) ≫ m₁.φ
        rw [Category.assoc, hm₁, q₁]
      · have w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e := κ.cart.1.w
        have w₂ : C.m.φ ≫ C.t.G.hom = Y.oF.t.G.hom ≫ C.j := C.m.cart.1.w
        have w₃ : m₁.φ ≫ Y.t.G.hom = t.G.hom ≫ pullback.fst _ _ := m₁.cart.1.w
        have w₄ : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := Y.m.cart.1.w
        rw [hje S (g ≫ t.G.hom) (g₁ ≫ Y.oF.t.G.hom) (by
          rw [Category.assoc, ← w₃, ← Category.assoc, q₁, Category.assoc, w₄, Category.assoc])]
        simp only [Category.assoc]
        rw [w₁, reassoc_of% w₂]
    rw [s₁, s₂, hm₃]
    simp only [Category.assoc]
    rw [reassoc_of% hκκ, hmh]

end GlobalTheory.Models.Domination
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliLevelQuotientByFiniteGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevQuot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem over_of_fix (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3) {l₀ l₁ : Level H} {X₀ : Moduli D l₀}
    {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X} {ν : SABMap X₁.univ.t X₀.univ.t r} (hA : l₀.A = 1)
    (hc : LevComp X₁.univ X₀.univ r ν) {f : X₁.X ⟶ X₁.X} (m : SABMap X₁.univ.t X₁.univ.t f)
    (hm : ∀ a, (X₁.univ.eta a).left ≫ m.φ = f ≫ (X₁.univ.eta a).left) (hs : (f ≫ r) ≫ X₀.s = r ≫ X₀.s) :
    f ≫ r = r ∧ m.φ ≫ ν.φ = ν.φ := by
  obtain ⟨n, hn⟩ := LevelCover.sab_comp m ν rfl
  rw [← hn]
  refine LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ X₀ _ _ _ _ X₁.univ _ _ n ν (isReduced_moduli X₁) hs
    ⟨fun a => ?_, fun a => ?_⟩ hc
  · rw [hn, ← Category.assoc, LevelCover.sec_pow m _ _ (hm a), Category.assoc, hc.1, Category.assoc]
  · have e : X₁.univ.etaA a ^ (l₁.A / l₀.A) = X₁.univ.eta 0 ^ 0 := by
      rw [hA, Nat.div_one, pow_zero, ← Moduli.LevelAction.map_nsmul_of_add X₁.univ.etaA_add, X₁.univ.etaA_ker]
    rw [hn, Category.assoc, ← hc.2, e, ← Category.assoc, LevelCover.sec_pow m _ _ (hm 0), Category.assoc]

theorem exists_twist_of_fibre (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3) (hN : ToroidalLevelCompatibility (H := H) (D := D))
    {l₀ l₁ : Level H} {X₀ : Moduli D l₀} {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X} {ν : SABMap X₁.univ.t X₀.univ.t r}
    {j : KA l₀ →+* KA l₁} (hd : l₀.Dvd l₁) (hM : l₁.M = l₀.M) (hMb : l₁.Mb = l₀.Mb)
    (hj : IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom j) (hr : r ≫ X₀.s = X₁.s ≫ spMap j)
    (hc : LevComp X₁.univ X₀.univ r ν) {k : Type} [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X₁.X)
    (h₁ : y ≫ r = y' ≫ r) (h₂ : y ≫ X₁.s = y' ≫ X₁.s) :
    ∃ (ρ : X₁.X ≅ X₁.X) (m : SABMap X₁.univ.t X₁.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La),
      SemiTwist X₁ ρ.hom m.φ g (RingHom.id _) ∧ y' = y ≫ ρ.hom := by
  let c := LevelExist.minCoeff l₁
  have hM' : 0 < l₁.M' := LevelExist.M'_pos l₁
  have hz : ∀ a, a ∣ l₁.M' → zeta a ∈ c.F := fun a ha => by
    rw [LevelCover.zeta_dvd hM' ha]
    exact pow_mem c.zeta_mem _
  have hle : KA l₀ ≤ c.F := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x (rfl | rfl)
    · exact c.le (baseKA l₁).ρ.2
    · exact hz _ (hd.2.2.trans (Nat.dvd_lcm_right _ _))
  let c₀ : Coeff l₀ := ⟨c.F, c.fin, c.conj, hz _ (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _))
    (hd.2.2.trans (Nat.dvd_lcm_right _ _))), hle⟩
  obtain ⟨r', j', ν', hj', hr', e₁, e₂, -, hF⟩ := hN l₀ l₁ X₀ X₁ hd
  obtain rfl : j = j' := RingHom.ext fun x => Subtype.ext ((hj x).trans (hj' x).symm)
  obtain rfl : r = r' := (LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ X₀ _ _ _ _ X₁.univ _ _ ν ν'
    (isReduced_moduli X₁) (hr.trans hr'.symm) hc ⟨e₁, e₂⟩).1
  obtain ⟨rF, a₁, a₂, -, -, -, htr⟩ := hF c₀ c rfl
  obtain ⟨β, hβ⟩ := LevCover.exists_spMap (y ≫ X₁.s)
  obtain ⟨θ, hθ⟩ : ∃ θ : c.F →+* k, θ.comp (IntermediateField.inclusion c.le).toRingHom = β := by
    letI : Algebra (KA l₁) k := β.toAlgebra
    letI : Algebra (KA l₁) c.F := (IntermediateField.inclusion c.le).toRingHom.toAlgebra
    haveI := c.fin
    haveI : IsScalarTower ℚ (KA l₁) c.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : Algebra.IsAlgebraic (KA l₁) c.F := Algebra.IsAlgebraic.tower_top (K := ℚ) (KA l₁)
    haveI : Module.IsTorsionFree (KA l₁) c.F := DivisionSemiring.to_moduleIsTorsionFree
    exact ⟨(IsAlgClosed.lift (R := KA l₁) (S := c.F) (M := k)).toRingHom,
      (IsAlgClosed.lift (R := KA l₁) (S := c.F) (M := k)).comp_algebraMap⟩
  have w : y ≫ X₁.s = spMap θ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [LevCover.spMap_comp'', hθ, hβ]
  obtain ⟨⟨g, ρ, hg, ⟨hs, m, b₁, b₂⟩, -, hy⟩, -⟩ := htr k (pullback.lift y (spMap θ) w)
    (pullback.lift y' (spMap θ) (h₂ ▸ w)) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, a₁, pullback.lift_fst_assoc, pullback.lift_fst_assoc, h₁]
      · rw [Category.assoc, Category.assoc, a₂, pullback.lift_snd_assoc, pullback.lift_snd_assoc])
  rw [pullback.lift_fst, pullback.lift_fst_assoc] at hy
  refine ⟨ρ, m, g.f l₁.A, ⟨by rw [hs, LevelCover.spMap_id', Category.comp_id], fun a => ?_, b₂⟩, hy⟩
  rw [← b₁, Moduli.LevelAction.eta_congr X₁.univ (x := g.f l₁.M a) (y := a) (by rw [hM, hMb]; exact hg.2.1 a)]

theorem exists_finite_invariant {l : Level H} (Xo : Moduli D l) :
    ∃ (κ : Type) (_ : Finite κ) (q : (D.La →ₗ[𝓞 E] D.La) → κ), ∀ g g', q g = q g' →
      ∀ x, Xo.univ.etaA (g x) = Xo.univ.etaA (g' x) := by
  obtain ⟨_, _⟩ := LevCover.datum_free D
  obtain ⟨κ, _, q, hq⟩ := LevCover.exists_finite_mod D.La l.A_pos
  haveI : Nonempty D.La := ⟨0⟩
  refine ⟨κ → κ, inferInstance, fun g c => q (g (Function.invFun q c)), fun g g' h x => ?_⟩
  obtain ⟨c, hc⟩ := hq _ _ (Function.invFun_eq (f := q) ⟨x, rfl⟩)
  obtain ⟨c', hc'⟩ := hq _ _ (congrFun h (q x))
  generalize Function.invFun q (q x) = y at hc hc'
  subst hc
  simp only [map_add (f := _), map_nsmul, hc', Xo.univ.etaA_add, Xo.univ.etaA_ker, _root_.mul_one]

section

variable {l₀ l₁ : Level H} {X₀ : Moduli D l₀} {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X}

def twistMonoid (τ : autOver r →* Aut X₁.univ.t.G.left) : Submonoid (autOver r) :=
  { carrier := {ω | ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧
      SemiTwist X₁ ω.1.asIso.hom (τ ω).asIso.hom g σ.toRingHom}
    mul_mem' := by
      rintro a b ⟨g, σ, h₁, h₂⟩ ⟨g', σ', h₁', h₂'⟩
      refine ⟨g' ∘ₗ g, σ.trans σ', by rw [RingEquiv.trans_apply, h₁, h₁'], ?_⟩
      have e₁ : (a * b).1.asIso.hom = b.1.asIso.hom ≫ a.1.asIso.hom := rfl
      have e₂ : (τ (a * b)).asIso.hom = (τ b).asIso.hom ≫ (τ a).asIso.hom := by rw [map_mul]; rfl
      have e₃ : (σ.trans σ').toRingHom = σ'.toRingHom.comp σ.toRingHom := RingHom.ext fun _ => rfl
      rw [e₁, e₂, e₃, LinearMap.coe_comp]
      exact h₂'.comp h₂
    one_mem' := by
      refine ⟨LinearMap.id, RingEquiv.refl _, rfl, ?_⟩
      rw [map_one]
      exact ⟨(Category.id_comp _).trans ((Category.comp_id _).symm.trans
          (congrArg _ (LevelCover.spMap_id' _).symm)),
        fun a => (Category.comp_id _).trans (Category.id_comp _).symm,
        fun a => (Category.comp_id _).trans (Category.id_comp _).symm⟩ }

theorem inv_comp_square {X P : Scheme.{0}} (a : X ≅ X) (t : P ≅ P) {b : X ⟶ X} {u : P ⟶ P} {x y : X ⟶ P}
    (p₁ : y ≫ t.hom = a.hom ≫ x) (p₂ : y ≫ u = b ≫ x) : x ≫ t.inv ≫ u = (a.inv ≫ b) ≫ x := by
  rw [Category.assoc, ← p₂, Iso.eq_inv_comp, ← Category.assoc, ← p₁, Category.assoc, Iso.hom_inv_id_assoc]

theorem finite_twistMonoid (τ : autOver r →* Aut X₁.univ.t.G.left)
    (mu : ∀ ω : autOver r, SABMap X₁.univ.t X₁.univ.t ω.1.asIso.hom) (hmu : ∀ ω, (mu ω).φ = (τ ω).asIso.hom) :
    Finite (twistMonoid τ) := by
  obtain ⟨κ, _, q, hq⟩ := exists_finite_invariant X₁
  haveI := finite_fieldAut l₁
  have hch : ∀ ω : twistMonoid τ, ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁),
      SemiTwist X₁ ω.1.1.asIso.hom (τ ω.1).asIso.hom g σ.toRingHom := fun ω => by
    obtain ⟨g, σ, -, h⟩ := ω.2
    exact ⟨g, σ, h⟩
  choose g σ hg using hch
  refine Finite.of_injective (fun ω => (q (g ω), σ ω)) fun a b hab => ?_
  have h₁ := hq _ _ (congrArg Prod.fst hab)
  have h₂ : σ a = σ b := congrArg Prod.snd hab
  have e₀ : (b.1 * a.1⁻¹).1.asIso.hom = a.1.1.asIso.inv ≫ b.1.1.asIso.hom := rfl
  have e₁ : (τ (b.1 * a.1⁻¹)).asIso.hom = (τ a.1).asIso.inv ≫ (τ b.1).asIso.hom := by rw [map_mul, map_inv]; rfl
  have key : ∀ {x y : X₁.X ⟶ X₁.univ.t.G.left}, y ≫ (τ a.1).asIso.hom = a.1.1.asIso.hom ≫ x →
      y ≫ (τ b.1).asIso.hom = b.1.1.asIso.hom ≫ x → x ≫ (mu (b.1 * a.1⁻¹)).φ = (b.1 * a.1⁻¹).1.asIso.hom ≫ x := by
    intro x y p₁ p₂
    rw [hmu, e₀, e₁]
    exact inv_comp_square a.1.1.asIso (τ a.1).asIso p₁ p₂
  have hid : (b.1 * a.1⁻¹).1.asIso.hom = 𝟙 _ :=
    SemiTwist.eq_id (g := id) (σ := RingHom.id _) (mu (b.1 * a.1⁻¹)) ⟨by
      rw [e₀, Category.assoc, (hg b).1, ← h₂, ← (hg a).1, LevelCover.spMap_id', Category.comp_id]
      exact Iso.inv_hom_id_assoc a.1.1.asIso _,
      fun x => key ((hg a).2.1 x) ((hg b).2.1 x),
      fun x => key ((hg a).2.2 x) (h₁ x ▸ (hg b).2.2 x)⟩ rfl fun _ => rfl
  have : b.1 * a.1⁻¹ = 1 := Subtype.ext (Aut.ext (Iso.ext hid))
  exact Subtype.ext (mul_inv_eq_one.1 this).symm

theorem exists_mem_twistMonoid (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3)
    {ν : SABMap X₁.univ.t X₀.univ.t r} {k : KA l₀ →+* KA l₁} (hA : l₀.A = 1)
    (hk : IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k) (hr : r ≫ X₀.s = X₁.s ≫ spMap k)
    (hc : LevComp X₁.univ X₀.univ r ν) (τ : autOver r →* Aut X₁.univ.t.G.left)
    (hτ : ∀ ω, (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (τ ω).asIso.hom ≫ X₁.univ.t.G.hom = X₁.univ.t.G.hom ≫ ω.1.asIso.hom)
    (ρ : X₁.X ≅ X₁.X) (m : SABMap X₁.univ.t X₁.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁)
    (h₁ : σ (baseKA l₁).ρ = (baseKA l₁).ρ) (h₂ : SemiTwist X₁ ρ.hom m.φ g σ.toRingHom) :
    ∃ ω ∈ twistMonoid τ, ω.1.asIso.hom = ρ.hom := by
  have hkρ : k (baseKA l₀).ρ = (baseKA l₁).ρ := Subtype.ext (hk _)
  have hz : (baseKA l₀).ζ = 1 := by
    have := (baseKA l₀).ζ_prim.pow_eq_one
    rwa [hA, pow_one] at this
  have hσ : σ.toRingHom.comp k = k := field_hom_ext l₀ _ _ (by rw [RingHom.comp_apply, hkρ]; exact h₁)
    (by rw [hz, map_one, map_one])
  obtain ⟨o₁, o₂⟩ := over_of_fix hL hL2 hL3 hA hc m h₂.2.1 (by
    rw [Category.assoc, hr, ← Category.assoc, h₂.1, Category.assoc, LevCover.spMap_comp'', hσ])
  have e : m.φ = (τ ⟨Aut.of ρ, o₁⟩).asIso.hom :=
    ν.cart.1.hom_ext (o₂.trans (hτ _).1.symm) (m.cart.1.w.trans (hτ ⟨Aut.of ρ, o₁⟩).2.symm)
  exact ⟨⟨Aut.of ρ, o₁⟩, ⟨g, σ, h₁, e ▸ h₂⟩, rfl⟩

end

theorem exists_level_quotient : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).asIso.hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).asIso.hom ∧ (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.etaA x).left := by
  intro hL hL2 hL3 E _ _ _ H D Xo hpq hN l₀ l₁ r ν k hA hM hMb hk hr hc
  have hd : l₀.Dvd l₁ := ⟨hM ▸ dvd_rfl, hMb.le, hA ▸ one_dvd _⟩
  obtain ⟨hfin, het, hsur⟩ : IsFinite r ∧ Etale r ∧ Surjective r := by
    obtain ⟨k', r', ν', hr', hk', hc', -, -, -, h⟩ := LevelMap.exists_levelMap E H D Xo hN l₀ l₁ hd
    obtain rfl : k = k' := RingHom.ext fun x => Subtype.ext ((hk x).trans (hk' x).symm)
    obtain rfl : r = r' := (LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ _ _ _ _ _ (Xo l₁).univ _ _ ν ν'
      (isReduced_moduli _) (hr.trans hr'.symm) hc hc').1
    exact h
  obtain ⟨τ, hτ⟩ := exists_liftAut ν.cart.1
  have hmu : ∀ ω : autOver r, ∃ m : SABMap (Xo l₁).univ.t (Xo l₁).univ.t ω.1.asIso.hom, m.φ = (τ ω).asIso.hom := fun ω => by
    obtain ⟨m, hm⟩ := LevelCover.sab_cancel ν ν ω.1.asIso.hom ω.2
    exact ⟨m, ν.cart.1.hom_ext (hm.trans (hτ ω).1.symm) (m.cart.1.w.trans (hτ ω).2.symm)⟩
  choose mu hmu using hmu
  let S := twistMonoid τ
  have hS := exists_mem_twistMonoid hL hL2 hL3 hA hk hr hc τ hτ
  haveI : Finite S := finite_twistMonoid τ mu hmu
  obtain ⟨T, hT⟩ := exists_subgroup_of_finite S
  refine ⟨T, inferInstance, Finite.of_injective (fun t : T => (⟨t.1, (hT _).1 t.2⟩ : S))
      fun a b h => Subtype.ext (congrArg (fun s : S => s.1) h),
    (autOver r).subtype.comp T.subtype, τ.comp T.subtype, fun t => mu t.1,
    Subtype.val_injective.comp Subtype.val_injective, ⟨inferInstance, fun t => t.1.2, ?_⟩, fun t => ?_⟩
  · refine invariant_descends r (fun t : T => t.1.1.asIso.hom) (fun t => t.1.2) fun F _ _ y y' hy => ?_
    obtain ⟨β, hβ⟩ := LevCover.exists_spMap (y ≫ (Xo l₁).s)
    obtain ⟨β', hβ'⟩ := LevCover.exists_spMap (y' ≫ (Xo l₁).s)
    have hkρ : k (baseKA l₀).ρ = (baseKA l₁).ρ := Subtype.ext (hk _)
    have hb : β.comp k = β'.comp k := LevCover.spMap_inj' (by
      rw [← LevCover.spMap_comp'', ← LevCover.spMap_comp'', ← hβ, ← hβ', Category.assoc, Category.assoc, ← hr,
        ← Category.assoc, hy, Category.assoc])
    obtain ⟨σ, h₁, h₂⟩ := exists_fieldAut l₁ β β' (hkρ ▸ DFunLike.congr_fun hb (baseKA l₀).ρ)
    obtain ⟨ρ, m, g, h₃⟩ := exists_semiTwist_iso hpq l₀ hA hM hMb (Xo l₁) σ h₁
    obtain ⟨a, ha, ea⟩ := hS ρ m g σ h₁ h₃
    obtain ⟨ρ', m', g', h₄, h₅⟩ := exists_twist_of_fibre hL hL2 hL3 hN hd hM hMb hk hr hc (y ≫ ρ.hom) y'
      (by rw [Category.assoc, ← ea, show a.1.asIso.hom ≫ r = r from a.2, hy])
      (by rw [Category.assoc, h₃.1, ← Category.assoc, hβ, hβ', LevCover.spMap_comp'', h₂])
    obtain ⟨b, hb', eb⟩ := hS ρ' m' g' (RingEquiv.refl _) rfl h₄
    refine ⟨⟨b * a, (hT _).2 (S.mul_mem hb' ha)⟩, ?_⟩
    rw [h₅, Category.assoc, ← ea, ← eb]
    rfl
  · obtain ⟨g, σ, h₁, h₂⟩ := (hT _).1 t.2
    exact ⟨hmu _, (hτ _).1, h₂.2.1, g, σ, h₁, h₂.1, h₂.2.2⟩

end GlobalTheory.LevQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLevelExtendsFromDenseOpenNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem GlobalTheory.exists_torsion_level_extend : ∀ (Λ : Type) [AddCommGroup Λ] (N : ℕ) (S W : Scheme.{0}) [IsLocallyNoetherian S] (j : W ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over W) [GrpObj G'] (φ : G'.left ⟶ G.left) (lv' : Λ → (𝟙_ (Over W) ⟶ G')), Geo.Tor.IsNormalScheme S → IsOpenImmersion j → IsDominant j → IsProper G.hom → IsUnit (N : Γ(S, ⊤)) → IsGrpPullback G' G j φ → (∀ a c, lv' (a + c) = lv' a * lv' c) → (∀ a, lv' (N • a) = 1) → ∃ lv : Λ → (𝟙_ (Over S) ⟶ G), (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N • a) = 1) ∧ ∀ a, (lv' a).left ≫ φ = j ≫ (lv a).left := by
  intro Λ _ N S W _ j G _ _ G' _ φ lv' hS _ _ _ hN gp hadd hker
  have hred : IsReduced S := by
    have : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
      obtain ⟨_, _⟩ := hS x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have hqc : QuasiCompact j := inferInstance
  let P : Over S := Over.mk ((𝟙_ (Over W)).hom ≫ j)
  let ρ : (𝟙_ (Over W) ⟶ G') →* (P ⟶ G) := pushHom gp _
  have hρ : ∀ x, (ρ x).left = x.left ≫ φ := fun _ => rfl
  have h0 : lv' 0 = 1 := by simpa using hker 0
  have hpow : ∀ (n : ℕ) a, lv' (n • a) = lv' a ^ n := fun n a => by
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hex : ∀ a, ∃ σ : S ⟶ G.left, σ ≫ G.hom = 𝟙 S ∧ j ≫ σ = (lv' a).left ≫ φ := fun a => by
    obtain ⟨s, h₁, h₂⟩ := GlobalTheory.exists_section_of_pow_eq_one hS j G N hN P (ρ (lv' a))
      (by rw [← map_pow, ← hpow, hker, map_one]) (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
    exact ⟨s, h₁, h₂.trans (Category.id_comp _)⟩
  choose σ hσ₁ hσ₂ using hex
  let lv : Λ → (𝟙_ (Over S) ⟶ G) := fun a => Over.homMk (σ a) (hσ₁ a)
  let u : P ⟶ 𝟙_ (Over S) := Over.homMk j ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hu : ∀ a, u ≫ lv a = ρ (lv' a) := fun a => Over.OverMorphism.ext (hσ₂ a)
  have inj : ∀ s t : 𝟙_ (Over S) ⟶ G, u ≫ s = u ≫ t → s = t := fun s t h =>
    Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := S) G.hom ((Over.w s).trans (Over.w t).symm) j
      (congrArg (fun z => z.left) h))
  refine ⟨lv, fun a c => inj _ _ ?_, fun a => inj _ _ ?_, fun a => (hσ₂ a).symm⟩
  · rw [MonObj.comp_mul, hu, hu, hu, hadd, map_mul]
  · rw [hu, hker, map_one, MonObj.comp_one]
end

