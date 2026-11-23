module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDiscriminantModuleIntegralOverlatticeSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0073

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingCount
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Gluing

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem resQ_ne_zero [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (h : Irreducible ϖ) :
    resQ ϖ ≠ 0 := by
  unfold resQ
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 h]
  have : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

theorem encard_le [IsNonarchimedeanLocalField F] [CharZero F] {L : LocE F E} {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (h : IsHermND L Hm) {m : ℕ} {y : Fin m → Fin n → E}
    (hy : LinearIndependent E y) {Y : Submodule E (Fin n → E)}
    (hY : Submodule.span E (Set.range y) = Y) (hc : Y ⊔ perp L Hm Y = ⊤)
    (Mh Λ₀ Md : Submodule L.O (Fin n → E))
    (hMd : ∀ x, x ∈ Md ↔ x ∈ Y ∧ ∀ z ∈ Mh, hf L Hm x z ∈ L.O)
    {ι : Type} [Fintype ι] (b : ι → Fin n → E) (hb : Md = Submodule.span L.O (Set.range b))
    (hN : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≠ 0) :
    {Λ : Submodule L.O (Fin n → E) | IsSD L Hm Λ ∧ Λ ⊓ Y.restrictScalars L.O = Mh ∧
      Λ ⊓ (perp L Hm Y).restrictScalars L.O = Λ₀}.encard ≤
      ((Mh.toAddSubgroup.relIndex Md.toAddSubgroup ^ Fintype.card ι : ℕ) : ℕ∞) := by
  set T := {Λ : Submodule L.O (Fin n → E) | IsSD L Hm Λ ∧ Λ ⊓ Y.restrictScalars L.O = Mh ∧
      Λ ⊓ (perp L Hm Y).restrictScalars L.O = Λ₀} with hT
  rcases T.eq_empty_or_nonempty with h0 | ⟨Λ₁, hΛ₁⟩
  · simp [h0]
  have hsym : ∀ x v, hf L Hm x v ∈ L.O → hf L Hm v x ∈ L.O := fun x v hx => by
    rw [← DualInter.cj_hf h]
    exact GlobalTheory.UnramOrder.cj_mem L hx
  have hM : ∀ Λ ∈ T, ∀ x, x ∈ Mh ↔ x ∈ Λ ∧ x ∈ Y := fun Λ hΛ x => by
    rw [← hΛ.2.1]; rfl
  have h0 : ∀ Λ ∈ T, ∀ x, x ∈ Λ₀ ↔ x ∈ Λ ∧ x ∈ perp L Hm Y := fun Λ hΛ x => by
    rw [← hΛ.2.2]; rfl
  have hproj : ∀ Λ ∈ T, ∀ l ∈ Λ, ∀ w ∈ perp L Hm Y, l - w ∈ Y → l - w ∈ Md := by
    intro Λ hΛ l hl w hw hlw
    refine (hMd _).2 ⟨hlw, fun z hz => ?_⟩
    have hz' := (hM Λ hΛ z).1 hz
    rw [DualInter.sub_l, hw z hz'.2, sub_zero]
    exact (hΛ.1.2 z).2 hz'.1 l hl
  have hbM : ∀ i, b i ∈ Md := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  have hlift : ∀ Λ : T, ∀ i, ∃ a ∈ Λ.1, a - b i ∈ perp L Hm Y ∧
      ∃ c ∈ Λ₁, c - (a - b i) ∈ Y := by
    intro Λ i
    obtain ⟨-, -, h3, -⟩ := DualInter.dual_inter L Hm h Λ.1 Λ.2.1 m y hy
    obtain ⟨-, h2, -, -⟩ := DualInter.dual_inter L Hm h Λ₁ hΛ₁.1 m y hy
    rw [hY] at h2 h3
    obtain ⟨a, ha, hab⟩ := (h3 (b i)).1 fun x hx hxY =>
      hsym _ _ (((hMd _).1 (hbM i)).2 x ((hM _ Λ.2 x).2 ⟨hx, hxY⟩))
    obtain ⟨c, hc, hca⟩ := (h2 (a - b i)).1 fun x hx hxY => by
      rw [DualInter.sub_r, hxY _ ((hMd _).1 (hbM i)).1, sub_zero]
      exact (Λ.2.1.2 a).2 ha x ((h0 _ Λ.2 x).1 ((h0 _ hΛ₁ x).2 ⟨hx, hxY⟩)).1
    exact ⟨a, ha, by simpa using (perp L Hm Y).neg_mem hab, c, hc, by simpa using Y.neg_mem hca⟩
  choose a ha hab c hc1 hca using hlift
  have hle : ∀ Λ Λ' : T, (∀ i, a Λ i ∈ Λ'.1) → Λ.1 ≤ Λ'.1 := by
    intro Λ Λ' hi l hl
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hc ▸ Submodule.mem_top : l ∈ Y ⊔ perp L Hm Y)
    have hu' : l - w = u := by rw [← huw]; simp
    have h1 := hproj _ Λ.2 l hl w hw (hu' ▸ hu)
    rw [hb] at h1
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 h1
    have h2 : l - ∑ i, s i • a Λ i ∈ Λ₀ := by
      refine (h0 _ Λ.2 _).2 ⟨Λ.1.sub_mem hl (Λ.1.sum_mem fun i _ => Λ.1.smul_mem _ (ha Λ i)), ?_⟩
      have : l - ∑ i, s i • a Λ i = w - ∑ i, s i • (a Λ i - b i) := by
        simp only [smul_sub, Finset.sum_sub_distrib, hs]; abel
      rw [this]
      exact Submodule.sub_mem _ hw (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (s i : E) (hab Λ i))
    have h3 := Λ'.1.add_mem ((h0 _ Λ'.2 _).1 h2).1
      (Λ'.1.sum_mem (t := Finset.univ) fun i _ => Λ'.1.smul_mem (s i) (hi i))
    rwa [sub_add_cancel] at h3
  let Q := Md.toAddSubgroup ⧸ Mh.toAddSubgroup.addSubgroupOf Md.toAddSubgroup
  have hQ : Nat.card Q = Mh.toAddSubgroup.relIndex Md.toAddSubgroup := rfl
  have : Finite Q := Nat.finite_of_card_ne_zero (hQ ▸ hN)
  let Φ : T → ι → Q := fun Λ i =>
    QuotientAddGroup.mk ⟨c Λ i - (a Λ i - b i), hproj _ hΛ₁ _ (hc1 Λ i) _ (hab Λ i) (hca Λ i)⟩
  have key : ∀ Λ Λ' : T, Φ Λ = Φ Λ' → ∀ i, a Λ i ∈ Λ'.1 := by
    intro Λ Λ' he i
    have h1 : -(c Λ i - (a Λ i - b i)) + (c Λ' i - (a Λ' i - b i)) ∈ Mh :=
      QuotientAddGroup.eq.1 (congrFun he i)
    have h2 : a Λ i - a Λ' i ∈ Λ₀ := by
      refine (h0 _ hΛ₁ _).2 ⟨?_, ?_⟩
      · have := Λ₁.add_mem ((hM _ hΛ₁ _).1 h1).1 (Λ₁.sub_mem (hc1 Λ i) (hc1 Λ' i))
        convert this using 1; abel
      · have := (perp L Hm Y).sub_mem (hab Λ i) (hab Λ' i)
        convert this using 1; abel
    have h3 := Λ'.1.add_mem ((h0 _ Λ'.2 _).1 h2).1 (ha Λ' i)
    rwa [sub_add_cancel] at h3
  have hinj : Function.Injective Φ := fun Λ Λ' he =>
    Subtype.ext (le_antisymm (hle _ _ (key _ _ he)) (hle _ _ (key _ _ he.symm)))
  have : Finite T := Finite.of_injective Φ hinj
  have h4 := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_fun, hQ, Nat.card_eq_fintype_card (α := ι)] at h4
  rw [← (Set.toFinite T).cast_ncard_eq, ← Nat.card_coe_set_eq]
  exact_mod_cast h4

theorem gluing_count : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh Λ₀ : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (({Λ : Submodule L.O S.V | IsSD L S.Hm Λ ∧ S.sat Λ = Mh ∧ Λ ⊓ S.W0.restrictScalars L.O = Λ₀}.encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S C hC p hp Mh Λ₀ hM
  rcases {Λ : Submodule L.O S.V | IsSD L S.Hm Λ ∧ S.sat Λ = Mh ∧
    Λ ⊓ S.W0.restrictScalars L.O = Λ₀}.eq_empty_or_nonempty with h0 | ⟨Λ₁, hΛ₁⟩
  · simp [h0]
  obtain ⟨n, hn, n', hn', rfl⟩ := hC
  rw [((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 p hp).2] at hM
  obtain ⟨⟨c, hc0, hca, hdet⟩, -, hsp⟩ := _root_.GlobalTheory.FrameGram.main L r k S n hn n' hn'
  obtain ⟨hli, hcompl, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hMh : ∀ x, x ∈ Mh ↔ x ∈ Λ₁ ∧ x ∈ S.ME := fun x => by rw [← hΛ₁.2.1]; rfl
  let Md : Submodule L.O S.V :=
    { carrier := {x | x ∈ S.ME ∧ ∀ z ∈ Mh, hf L S.Hm x z ∈ L.O}
      zero_mem' := ⟨S.ME.zero_mem, fun z _ => by simp [hf]⟩
      add_mem' := by
        rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
        refine ⟨S.ME.add_mem hu hv, fun z hz => ?_⟩
        have : hf L S.Hm (u + v) z = hf L S.Hm u z + hf L S.Hm v z :=
          (DualInter.hfL L S.Hm z).map_add u v
        rw [this]
        exact L.O.add_mem (hu' z hz) (hv' z hz)
      smul_mem' := by
        rintro s u ⟨hu, hu'⟩
        refine ⟨S.ME.smul_mem (s : E) hu, fun z hz => ?_⟩
        have : hf L S.Hm (s • u) z = s * hf L S.Hm u z := DualInter.smul_l L S.Hm s u z
        rw [this]
        exact L.O.mul_mem s.2 (hu' z hz) }
  obtain ⟨-, hidx, -, b, hb⟩ := _root_.GlobalTheory.DiscOver.disc_overlattice L S.Hm S.herm S.ϖ S.ϖ_irr _ c hc0 hdet Mh Md
    (by rw [Set.Sum.elim_range]; exact hM)
    (fun x hx => by rw [hsp]; exact ((hMh x).1 hx).2)
    (fun x hx z hz => (hΛ₁.1.2 z).2 ((hMh z).1 hz).1 x ((hMh x).1 hx).1)
    (fun x => by rw [hsp]; rfl)
  rw [hca] at hidx
  have hq : resQ S.ϖ ^ (2 * S.a.toNat) ≠ 0 := pow_ne_zero _ (resQ_ne_zero _ S.ϖ_irr)
  have hN : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≠ 0 := fun h => hq (by rw [← hidx, h, zero_mul])
  have hNle : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≤ S.q ^ (2 * S.a.toNat) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Dvd.intro _ hidx)
  have hY : Submodule.span E (Set.range (Sum.elim S.f S.f' ∘ finSumFinEquiv.symm)) = S.ME := by
    rw [finSumFinEquiv.symm.surjective.range_comp, Set.Sum.elim_range, Submodule.span_union]
    have : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := Set.eq_univ_of_forall fun i => i.2
    simp only [Frames.ME, Frames.spanTo, this, Set.image_univ]
  have h1 := encard_le S.herm (hli.comp _ finSumFinEquiv.symm.injective) hY hcompl.sup_eq_top
    Mh Λ₀ Md (fun _ => Iff.rfl) b hb hN
  have h2 : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ^ Fintype.card (Fin (r + 1) ⊕ Fin (r + 1))
      ≤ S.q ^ (2 * S.a.toNat * (2 * r + 2)) := by
    rw [pow_mul, show Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) = 2 * r + 2 by simp; ring]
    exact Nat.pow_le_pow_left hNle _
  have h3 := h1.trans (Nat.cast_le.2 h2)
  have h4 := ENat.toENNReal_le.2 h3
  rw [ENat.toENNReal_coe, Nat.cast_pow] at h4
  exact h4

end GlobalTheory.HL.Gluing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCard
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SmallImage

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def reps (Λ : Submodule L.O S.V) : Submodule L.O S.V where
  carrier := {y | y ∈ Λ ∧ ∃ w ∈ S.W0, ∃ la ∈ S.X, ∃ la' ∈ S.X', w + la ∈ Λ ∧
    la' - la = algebraMap F E S.th • y}
  zero_mem' := ⟨Λ.zero_mem, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _,
    by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, w, hw, la, hla, la', hla', h1, h2⟩ ⟨hb, v, hv, lb, hlb, lb', hlb', h3, h4⟩
    refine ⟨Λ.add_mem ha hb, w + v, add_mem hw hv, la + lb, add_mem hla hlb, la' + lb', add_mem hla' hlb',
      ?_, ?_⟩
    · rw [add_add_add_comm]; exact Λ.add_mem h1 h3
    · rw [smul_add, ← h2, ← h4]; abel
  smul_mem' := by
    rintro c a ⟨ha, w, hw, la, hla, la', hla', h1, h2⟩
    refine ⟨Λ.smul_mem c ha, (c : E) • w, Submodule.smul_mem _ _ hw, (c : E) • la,
      Submodule.smul_mem _ _ hla, (c : E) • la', Submodule.smul_mem _ _ hla', ?_, ?_⟩
    · rw [← smul_add]; exact Λ.smul_mem c h1
    · rw [← smul_sub, h2, smul_comm]; rfl

end

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SmallImage.resQ_pos {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ϖ : 𝒪[F]) (h : Irreducible ϖ) : 0 < _root_.GlobalTheory.HL.resQ ϖ := by
  unfold _root_.GlobalTheory.HL.resQ
  have hmax : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp h
  rw [← hmax]
  have : Finite (IsLocalRing.ResidueField 𝒪[F]) := inferInstance
  exact Nat.card_pos_iff.mpr ⟨inferInstance, this⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma hf_sub_left_flag_measures {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L H (x - x') y = _root_.GlobalTheory.HL.hf L H x y - _root_.GlobalTheory.HL.hf L H x' y := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma hf_sub_right_flag_measures {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    _root_.GlobalTheory.HL.hf L H x (y - y') = _root_.GlobalTheory.HL.hf L H x y - _root_.GlobalTheory.HL.hf L H x y' := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma hf_add_left_flag_measures'' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L H (x + x') y = _root_.GlobalTheory.HL.hf L H x y + _root_.GlobalTheory.HL.hf L H x' y := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma hf_algebraMap_smul_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : F) :
    _root_.GlobalTheory.HL.hf L H x (algebraMap F E c • y) = algebraMap F E c * _root_.GlobalTheory.HL.hf L H x y := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SmallImage.small_image : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∃ i : ℕ, S.cardI d Λ = S.q ^ i) ∧ S.cardI d Λ ≤ S.be d Λ ∧ (¬ S.BBzero d Λ → ¬ S.TypeBe d Λ → S.q * S.cardI d Λ ≤ S.be d Λ) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  have hbasic := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hMsat : S.M d Λ ≤ S.sat Λ := hbasic.2.2.1
  have hth : S.th ≠ 0 := by
    unfold _root_.GlobalTheory.HL.Frames.th
    split_ifs
    · exact_mod_cast S.ϖ_irr.ne_zero
    · exact one_ne_zero
  have hX : S.X ≤ S.ME := by
    unfold _root_.GlobalTheory.HL.Frames.X _root_.GlobalTheory.HL.Frames.ME
    exact (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f (Nat.le_succ r)).trans le_sup_left
  have hX' : S.X' ≤ S.ME := by
    unfold _root_.GlobalTheory.HL.Frames.X' _root_.GlobalTheory.HL.Frames.ME
    exact (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f' (Nat.le_succ r)).trans le_sup_right
  have hIsat : S.Ihat d Λ ≤ S.sat Λ := by
    unfold _root_.GlobalTheory.HL.Frames.Ihat
    refine sup_le hMsat (Submodule.span_le.mpr ?_)
    rintro y ⟨w, hw, la, hla, la', hla', h1, h2, ⟨y1, hy1, hy1e⟩, h4⟩
    have hy1' : (algebraMap F E) S.th⁻¹ • (la' - la) = y1 := by
      rw [hy1e, smul_smul, ← map_mul, inv_mul_cancel₀ hth, map_one, one_smul]
    have hME : y1 ∈ S.ME := by
      rw [← hy1']
      apply Submodule.smul_mem
      exact Submodule.sub_mem _ (hX' hla') (hX hla)
    have hy1sat : y1 ∈ S.sat Λ := by
      unfold _root_.GlobalTheory.HL.Frames.sat
      exact Submodule.mem_inf.mpr ⟨hy1, (Submodule.restrictScalars_mem _ _ _).mpr hME⟩
    have hsum : y = (y - (algebraMap F E) S.th⁻¹ • (la' - la)) + y1 := by
      rw [hy1']; abel
    rw [SetLike.mem_coe, hsum]
    exact Submodule.add_mem _ (hMsat h4) hy1sat
  have hMI : S.M d Λ ≤ S.Ihat d Λ := by
    unfold _root_.GlobalTheory.HL.Frames.Ihat; exact le_sup_left
  have hq : 0 < S.q :=
    _root_.GlobalTheory.HL.SmallImage.resQ_pos S.ϖ S.ϖ_irr
  obtain ⟨j, -, hbe⟩ := (_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.1
  have hprod := AddSubgroup.relIndex_mul_relIndex (S.M d Λ).toAddSubgroup (S.Ihat d Λ).toAddSubgroup
    (S.sat Λ).toAddSubgroup (fun x hx => hMI hx) (fun x hx => hIsat hx)
  unfold _root_.GlobalTheory.HL.Frames.cardI _root_.GlobalTheory.HL.Frames.be
    at *
  have hbe0 : (S.M d Λ).toAddSubgroup.relIndex (S.sat Λ).toAddSubgroup ≠ 0 := by
    rw [hbe]; positivity
  rw [← hprod] at hbe0 ⊢
  have hI0 := left_ne_zero_of_mul hbe0
  have hJ0 := right_ne_zero_of_mul hbe0
  refine ⟨?_, ?_, ?_⟩
  · have hfin : Finite (↥(S.Ihat d Λ) ⧸ (S.M d Λ).comap (S.Ihat d Λ).subtype) :=
      Nat.finite_of_card_ne_zero hI0
    obtain ⟨i, hi⟩ := (_root_.GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ
      S.ϖ_irr (↥(S.Ihat d Λ) ⧸ (S.M d Λ).comap (S.Ihat d Λ).subtype)).1
    exact ⟨i, hi⟩
  · exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hJ0)
  · intro hB hTB
    have hne : S.Ihat d Λ ≠ S.sat Λ := by
      intro heq
      apply hTB
      have hcancel : ∀ v : S.V,
          algebraMap F E S.th • (algebraMap F E S.th⁻¹ • v) = v := by
        intro v; rw [smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul]
      have hcancel' : ∀ v : S.V,
          algebraMap F E S.th⁻¹ • (algebraMap F E S.th • v) = v := by
        intro v; rw [smul_smul, ← map_mul, inv_mul_cancel₀ hth, map_one, one_smul]
      refine _root_.GlobalTheory.HL.TypeRep.main L r k S d Λ hT hB
        (_root_.GlobalTheory.HL.SmallImage.reps S Λ) ?_ ?_ ?_
      · rintro y ⟨hyΛ, w, hw, la, hla, la', hla', h1, h2⟩
        refine ⟨hyΛ, ?_⟩
        rw [← hcancel' y, ← h2]
        exact Submodule.smul_mem _ _
          (Submodule.sub_mem _ (Submodule.mem_sup_right hla') (Submodule.mem_sup_left hla))
      · intro y hy
        rw [← heq] at hy
        have hle : S.Ihat d Λ ≤ S.M d Λ ⊔ _root_.GlobalTheory.HL.SmallImage.reps S Λ := by
          unfold _root_.GlobalTheory.HL.Frames.Ihat
          refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
          rintro z ⟨w, hw, la, hla, la', hla', h1, h2, ⟨y1, hy1, hy1e⟩, h4⟩
          have hy1' : (algebraMap F E) S.th⁻¹ • (la' - la) = y1 := by
            rw [hy1e, hcancel']
          have hrep : y1 ∈ _root_.GlobalTheory.HL.SmallImage.reps S Λ :=
            ⟨hy1, w, hw.1, la, hla, la', hla', h1, hy1e⟩
          have hsum : z = (z - (algebraMap F E) S.th⁻¹ • (la' - la)) + y1 := by
            rw [hy1']; abel
          rw [SetLike.mem_coe, hsum]
          exact Submodule.add_mem _ (Submodule.mem_sup_left h4) (Submodule.mem_sup_right hrep)
        obtain ⟨m, hm, y₀, hy₀, hmy⟩ := Submodule.mem_sup.mp (hle hy)
        refine ⟨y₀, hy₀, ?_⟩
        rw [← hmy, add_sub_cancel_right]
        exact hm
      · intro x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' hy₁ hy₂
        obtain ⟨hΛ1, w₁, hw₁, la₁, hla₁, la₁', hla₁', hwl₁, he₁⟩ := hy₁
        obtain ⟨hΛ2, w₂, hw₂, la₂, hla₂, la₂', hla₂', hwl₂, he₂⟩ := hy₂
        rw [hcancel] at he₁ he₂
        have isoX : ∀ a ∈ S.X, ∀ b ∈ S.X,
            _root_.GlobalTheory.HL.hf L S.Hm a b = 0 := fun a ha b hb =>
          _root_.GlobalTheory.HL.FrameOnto.spanTo_le_perp S S.f _ S.gram ha b hb
        have isoX' : ∀ a ∈ S.X', ∀ b ∈ S.X',
            _root_.GlobalTheory.HL.hf L S.Hm a b = 0 := fun a ha b hb =>
          _root_.GlobalTheory.HL.FrameOnto.spanTo_le_perp S S.f' _ S.gram' ha b hb
        have hperp : ∀ w ∈ S.W0, ∀ m ∈ S.ME,
            _root_.GlobalTheory.HL.hf L S.Hm w m = 0 := fun w hw m hm => hw m hm
        have hz₁ : x₁ + la₁ = la₁' - x₁' := by
          rw [sub_eq_iff_eq_add] at he₁; rw [he₁]; abel
        have hz₂ : x₂ + la₂ = la₂' - x₂' := by
          rw [sub_eq_iff_eq_add] at he₂; rw [he₂]; abel
        have hz₁X' : x₁ + la₁ ∈ S.X' := by
          rw [hz₁]; exact Submodule.sub_mem _ hla₁' hx₁'
        have hz₂X : x₂ + la₂ ∈ S.X := Submodule.add_mem _ hx₂ hla₂
        have hz₂X' : x₂ + la₂ ∈ S.X' := by
          rw [hz₂]; exact Submodule.sub_mem _ hla₂' hx₂'
        have e1 : x₁ = (x₁ + la₁) - la₁ := by abel
        have e2 : x₂' = la₂' - (x₂ + la₂) := by rw [hz₂]; abel
        have hmain : _root_.GlobalTheory.HL.hf L S.Hm x₁ x₂'
            = -_root_.GlobalTheory.HL.hf L S.Hm la₁ la₂' := by
          rw [e1, e2, hf_sub_left_flag_measures, hf_sub_right_flag_measures, hf_sub_right_flag_measures, isoX' _ hz₁X' _ hla₂',
            isoX' _ hz₁X' _ hz₂X', isoX _ hla₁ _ hz₂X]
          ring
        have hkey : _root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁) (la₂' - la₂)
            = _root_.GlobalTheory.HL.hf L S.Hm la₁ la₂' := by
          rw [hf_add_left_flag_measures'', hf_sub_right_flag_measures, hf_sub_right_flag_measures, hperp w₁ hw₁ la₂' (hX' hla₂'),
            hperp w₁ hw₁ la₂ (hX hla₂), isoX la₁ hla₁ la₂ hla₂]
          ring
        have hsm : _root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁) (la₂' - la₂)
            = algebraMap F E S.th * _root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁)
              (algebraMap F E S.th⁻¹ • (x₂ + x₂')) := by
          rw [← hf_algebraMap_smul_right, hcancel, he₂]
        have hdual := hbasic.1
        unfold _root_.GlobalTheory.HL.IsSD at hdual
        refine ⟨-_root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁)
          (algebraMap F E S.th⁻¹ • (x₂ + x₂')), ?_, ?_⟩
        · exact L.O.neg_mem ((hdual.2 _).mpr hΛ2 _ hwl₁)
        · show _root_.GlobalTheory.HL.hf L S.Hm x₁ x₂' = _
          rw [hmain, ← hkey, hsm]
          ring
    have hfin : Finite (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype) :=
      Nat.finite_of_card_ne_zero hJ0
    have hbot : (⊥ : Submodule L.O (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype)) ≠ ⊤ := by
      intro hbt
      apply hne
      refine le_antisymm hIsat (fun x hx => ?_)
      have hmem : Submodule.Quotient.mk (p := (S.Ihat d Λ).comap (S.sat Λ).subtype) ⟨x, hx⟩ ∈
          (⊥ : Submodule L.O (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype)) := by
        rw [hbt]; trivial
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem
      exact hmem
    have hle := (_root_.GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ
      S.ϖ_irr (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype)).2 ⊥ hbot
    rw [Nat.card_unique, mul_one] at hle
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hle

end GlobalTheory.HL.SmallImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassTermsLeOverlatticeMasses
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ClassMass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem M_eq_Mof (S : Frames L r k) {C : Set S.FrP} {p : S.FrP} (hp : p ∈ C) {d : S.Datum}
    {Λ : Submodule L.O S.V} (hC : S.Fr d Λ = C) : S.M d Λ = S.Mof p.1 p.2 := by
  subst hC
  exact ((GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).2.1 p hp).2.symm

theorem class_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, (∀ Q : ℕ → Prop, (S.sumData fun d => S.nT d C fun Λ => Q (S.be d Λ)) ≤ ∑' Mh : {Mh : Submodule L.O S.V // S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧ (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) ∧ Q ((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup)}, S.massSig Mh) ∧ (S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ) = S.massSig (S.Mof p.1 p.2) := by
  intro F _ _ _ _ _ E _ _ _ L r k S C hC p hp
  have hM : ∀ d Λ, S.Fr d Λ = C → S.M d Λ = S.Mof p.1 p.2 := fun d Λ hF => M_eq_Mof S hp hF
  constructor
  · intro Q
    refine (_root_.GlobalTheory.HL.sumData_nT_eq_mass L r k S C (fun d Λ => Q (S.be d Λ)) ?_).trans_le ?_
    · intro h hh d Λ hT hQ
      obtain ⟨-, -, -, hM', hsat', -⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hT h hh
      show Q (S.be (h • d) (h • Λ))
      unfold Frames.be
      rw [hM', hsat']
      exact hQ
    · unfold Frames.massSig
      rw [ENNReal.tsum_comm]
      refine ENNReal.tsum_le_tsum fun o => ?_
      split_ifs with hcond
      · obtain ⟨d, hT, hQ, hF⟩ := hcond
        have hbasic := GlobalTheory.HL.TermBasic.term_basic L r k S d o.out hT
        have hSD : IsSD L S.Hm o.out := hbasic.1
        have hle : S.M d o.out ≤ S.sat o.out := hbasic.2.2.1
        rw [hM d o.out hF] at hle
        have hQ' : Q ((S.Mof p.1 p.2).toAddSubgroup.relIndex (S.sat o.out).toAddSubgroup) := by
          have h := hQ
          unfold Frames.be at h
          rw [hM d o.out hF] at h
          exact h
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum ⟨S.sat o.out, hle,
          fun x hx => (Submodule.mem_inf.mp hx).2,
          fun x hx y hy => (hSD.2 y).mpr (Submodule.mem_inf.mp hy).1 x (Submodule.mem_inf.mp hx).1, hQ'⟩)
        rw [if_pos ⟨hSD, rfl⟩]
      · exact zero_le
  · have hb : ∀ Λ : Submodule L.O S.V, (∃ d, S.IsTerm d Λ ∧ S.BBzero d Λ ∧ S.Fr d Λ = C) ↔
        (IsSD L S.Hm Λ ∧ S.sat Λ = S.Mof p.1 p.2) := by
      intro Λ
      constructor
      · rintro ⟨d, hT, hB, hF⟩
        exact ⟨(GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1,
          (show S.M d Λ = S.sat Λ from hB).symm.trans (hM d Λ hF)⟩
      · rintro ⟨hSD, hsat⟩
        obtain ⟨d, hT, hF, hB⟩ := GlobalTheory.HL.PrimTerm.term_of_primitive L r k S Λ hSD C hC p hp hsat
        exact ⟨d, hT, hB, hF⟩
    refine (_root_.GlobalTheory.HL.sumData_nT_eq_mass L r k S C (fun d Λ => S.BBzero d Λ) ?_).trans ?_
    · intro h hh d Λ hT hB
      obtain ⟨-, -, -, hM', hsat', -⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hT h hh
      show S.M (h • d) (h • Λ) = S.sat (h • Λ)
      rw [hM', hsat']
      exact hB
    · unfold Frames.massSig
      exact tsum_congr fun o => if_congr (hb o.out) rfl rfl

end GlobalTheory.HL.ClassMass
end

