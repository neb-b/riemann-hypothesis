module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0089
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetKernelBoundByWeight
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernelWeight

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.KernelWeight.hf_add_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (a + b) y =
      _root_.GlobalTheory.HL.hf L Hm a y + _root_.GlobalTheory.HL.hf L Hm b y := by
  have h := _root_.GlobalTheory.HL.DualInter.sub_l L Hm (a + b) b y
  rw [add_sub_cancel_right] at h
  linear_combination -h

open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.KernelWeight.hf_smul_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (c • a) y = c * _root_.GlobalTheory.HL.hf L Hm a y :=
  _root_.GlobalTheory.HL.DualInter.smul_l L Hm c a y

def hfLin (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := hf_add_left L Hm a b y
  map_smul' c a := hf_smul_left L Hm c a y

theorem exists_coord {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ al : Fin (r + 1) → E, x = ∑ i, al i • n (g i) ∧ al j.castSucc = S.h x (gs j) := by
  have hu : n⁻¹ ∈ unipOn (S.spanTo g (j + 1)) (S.spanTo g j) := by
    apply Subgroup.inv_mem
    exact Subgroup.mem_iInf.1 hn.1.2 j
  have h1 : n⁻¹ x ∈ S.spanTo g (j + 1) := (hu.1 x).2 hx
  have h2 : n⁻¹ x - x ∈ S.spanTo g j := hu.2 x hx
  have h3 : n⁻¹ x ∈ Submodule.span E (Set.range g) :=
    Submodule.span_mono (Set.image_subset_range _ _) h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 h3
  have h4 : S.spanTo g j ≤ LinearMap.ker (hfLin L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < j := hi
    have : i ≠ j.castSucc := by
      rintro rfl
      simp at hi'
    show hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg this]
  have h5 : hfLin L S.Hm (gs j) (n⁻¹ x) = hfLin L S.Hm (gs j) x := by
    have := h4 h2
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  refine ⟨c, ?_, ?_⟩
  · have : x = n (n⁻¹ x) := (n.apply_symm_apply x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, ← hc, map_sum]
    simp
  · show _ = hfLin L S.Hm (gs j) x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h5, ← hc, map_sum]
    have : ∀ i, hfLin L S.Hm (gs j) (c i • g i) = if i = j.castSucc then c i else 0 := by
      intro i
      rw [map_smul]
      show c i * hf L S.Hm (g i) (gs j) = _
      rw [hd]; split_ifs <;> simp
    simp [this]

end

theorem kernel_weight : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ‖∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF
  have hW := (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.1
  have hom : ‖S.om d Λ‖ = 1 := (_root_.GlobalTheory.HL.WitIndep.witness_independence L r k S d Λ _ _ hW).2.2.2.2
  have hchi : ∀ b u, ‖S.chiM j d Λ b u‖ = 1 := fun b u =>
    (GlobalTheory.FramePsi.psi_unitary_character L r k S).2.2.2 _

  have hmove : ∀ w, S.Mv (j + 1) d Λ w → ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ S.IsTerm d Λ₁ ∧
      S.om d Λ₁ = S.om d Λ * S.chiM j d Λ w.1 w.2.1 := by
    intro w hw
    obtain ⟨Λ₁, h1, h2, -, -, h5⟩ := _root_.GlobalTheory.HL.MoveTerm.move_term L r k S j β βJ d Λ hT hF _ _ _ _ hw
    refine ⟨Λ₁, ⟨hw, h1⟩, h2, ?_⟩
    obtain ⟨al, hal, hal1⟩ := exists_coord S S.f S.es S.dual _ hW.2.2.1 j _ hw.1
    obtain ⟨al', hal', hal1'⟩ := exists_coord S S.f' S.es' S.dual' _ hW.2.2.2.1 j _ hw.2.1
    rw [h5 al al' hal hal', hal1, hal1']
    rfl
  have huniq : ∀ w Λ₁ Λ₂, S.MvTo (j + 1) d Λ Λ₁ w → S.MvTo (j + 1) d Λ Λ₂ w → Λ₁ = Λ₂ :=
    fun w Λ₁ Λ₂ h1 h2 => SetLike.coe_injective (h1.2.trans h2.2.symm)
  let P : Submodule L.O S.V → Prop := fun y => S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y
  let G : S.MW → ℂ := fun w => if ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ then
    S.om d Λ * S.chiM j d Λ w.1 w.2.1 else 0
  obtain ⟨hGn, hGs⟩ := (_root_.GlobalTheory.HL.moves_split_by_target L r k S j β βJ d Λ hT hF).2.2.2.2 P (S.om d) G
    (by
      intro w Λ₁ hw
      by_cases hP : P Λ₁
      · obtain ⟨Λ₂, h1, -, h3⟩ := hmove w hw.1
        rw [if_pos hP, huniq w Λ₁ Λ₂ hw h1, h3]
        exact if_pos ⟨Λ₁, hw, hP⟩
      · rw [if_neg hP]
        refine if_neg ?_
        rintro ⟨Λ₂, h1, h2⟩
        exact hP (huniq w Λ₂ Λ₁ h1 hw ▸ h2))
    (by
      intro w hw
      refine if_neg ?_
      rintro ⟨Λ₂, h1, -⟩
      exact hw h1.1)
  obtain ⟨-, hLn, hHn, -, hLb, hHb⟩ := _root_.GlobalTheory.HL.MoveTotal.total_moves L r k S hk j β βJ d Λ hT hF
  obtain ⟨hadd, hsm, -, -⟩ := GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound (S.refA (j + 1) Λ)
  set H : S.MW → ℂ := fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1 with hH
  obtain ⟨hn2, hc2⟩ := hsm (-S.om d Λ) H hHn
  obtain ⟨hn3, hc3, -⟩ := hadd G _ hGn hn2
  have hb := (hadd _ _ hn3 hLn).2.2 (by
    intro w
    simp only [Pi.add_apply, hH, ind, G]
    by_cases hw : S.Mv (j + 1) d Λ w
    · by_cases hex : ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁
      · rw [if_pos hex, if_pos hw]
        split_ifs <;> simp
      · have hl : ¬ S.NoLeak Λ w.2.1 := by
          intro hl
          obtain ⟨Λ₁, h1, h2, -⟩ := hmove w hw
          exact hex ⟨Λ₁, h1, h2, GlobalTheory.T.hermitianDoubleCoset_inFamily_moved_of_not_leak L r k S j β βJ d Λ hT hF _ _ _ _ hw hl Λ₁ h1.2⟩
        rw [if_neg hex, if_pos hw, if_pos ⟨hw, hl⟩]
        simp [hom, hchi]
    · have hex : ¬ ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ := by
        rintro ⟨Λ₂, h1, -⟩
        exact hw h1.1
      rw [if_neg hex, if_neg hw, if_neg (fun h => hw h.1)]
      simp)
  rw [hc3, hc2] at hb
  have hcK : 0 ≤ S.cK β βJ := by
    unfold Frames.cK
    positivity
  have hG : ‖cint (S.refA (j + 1) Λ) G‖ ≤
      (cint (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1)).re +
        ‖cint (S.refA (j + 1) Λ) H‖ := by
    have e : cint (S.refA (j + 1) Λ) G =
        (cint (S.refA (j + 1) Λ) G + -S.om d Λ * cint (S.refA (j + 1) Λ) H) +
          S.om d Λ * cint (S.refA (j + 1) Λ) H := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add hb ?_)
    rw [norm_mul, hom, one_mul]
  have := mul_le_mul_of_nonneg_left hG hcK
  show ‖∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ _
  rw [hGs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcK]
  linarith

end GlobalTheory.HL.KernelWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetKernelRowSumNearOne
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem cK_nonneg' (β βJ : ℕ) :
    0 ≤ S.cK β βJ := by
  unfold _root_.GlobalTheory.HL.Frames.cK
  positivity

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem ind_eq_one_of_pos {W : Type} {P : W → Prop} {w : W} (h : P w) :
    _root_.GlobalTheory.IdxInt.ind P w = 1 := by
  unfold _root_.GlobalTheory.IdxInt.ind
  exact if_pos h

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem ind_eq_zero_of_not {W : Type} {P : W → Prop} {w : W} (h : ¬ P w) :
    _root_.GlobalTheory.IdxInt.ind P w = 0 := by
  unfold _root_.GlobalTheory.IdxInt.ind
  exact if_neg h

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem eq_of_MvTo_of_MvTo {a : ℕ} {d : S.Datum}
    {Λ Λ₁ Λ₂ : Submodule L.O S.V} {w : S.MW}
    (h₁ : S.MvTo a d Λ Λ₁ w) (h₂ : S.MvTo a d Λ Λ₂ w) : Λ₁ = Λ₂ := by
  unfold _root_.GlobalTheory.HL.Frames.MvTo at h₁ h₂
  exact SetLike.coe_injective (h₁.2.trans h₂.2.symm)

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem Mv_of_MvTo {a : ℕ} {d : S.Datum}
    {Λ Λ₁ : Submodule L.O S.V} {w : S.MW}
    (h : S.MvTo a d Λ Λ₁ w) : S.Mv a d Λ w := by
  unfold _root_.GlobalTheory.HL.Frames.MvTo at h
  exact h.1

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem exists_MvTo_isTerm_of_Mv_of_InFF [IsNonarchimedeanLocalField F] [CharZero F]
    (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hF : S.InFF β (j + 1) βJ d Λ)
    (w : S.MW) (hw : S.Mv (j + 1) d Λ w) :
    ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ S.IsTerm d Λ₁ := by
  have hw' := hw
  unfold _root_.GlobalTheory.HL.Frames.Mv at hw'
  obtain ⟨n₀, -, n₀', -, n'', -, -, -, -, -, hmov, hW⟩ :=
    _root_.GlobalTheory.HL.MoveWit.main L r k S j β βJ d Λ hT hF _ _ _ _ hw'
  refine ⟨n₀⁻¹ • Λ, ?_, ?_⟩
  · unfold _root_.GlobalTheory.HL.Frames.MvTo
    exact ⟨hw, hmov⟩
  · unfold _root_.GlobalTheory.HL.Frames.IsTerm
    exact ⟨⟨_, _⟩, hW⟩


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.kern_row_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → |(∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, S.kern β (j + 1) βJ d Λ y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF
  obtain ⟨-, -, hfinK, -, hsplit⟩ :=
    _root_.GlobalTheory.HL.moves_split_by_target L r k S j β βJ d Λ hT hF
  obtain ⟨hNMv, hNLeak, -, hI, hIleak, -⟩ :=
    _root_.GlobalTheory.HL.MoveTotal.total_moves L r k S hk j β βJ d Λ hT hF
  have hlin := _root_.GlobalTheory.IdxInt.Lin.main (S.refA (↑j + 1) Λ)
  have hc := cK_nonneg' S β βJ
  set Good : S.MW → Prop := fun w => ∃ Λ₁, S.MvTo (↑j + 1) d Λ Λ₁ w ∧
    (S.IsTerm d Λ₁ ∧ S.InFF β (↑j + 1) βJ d Λ₁) with hGood
  obtain ⟨hNG, hsum⟩ := hsplit
    (fun y => S.IsTerm d y ∧ S.InFF β (↑j + 1) βJ d y)
    (fun _ => 1) (_root_.GlobalTheory.IdxInt.ind Good)
    (fun w Λ₁ h => by
      by_cases hP : S.IsTerm d Λ₁ ∧ S.InFF β (↑j + 1) βJ d Λ₁
      · rw [if_pos hP, ind_eq_one_of_pos ⟨Λ₁, h, hP⟩]
      · rw [if_neg hP, ind_eq_zero_of_not]
        rintro ⟨Λ₂, h₂, hP₂⟩
        exact hP (eq_of_MvTo_of_MvTo S h₂ h ▸ hP₂))
    (fun w hw => ind_eq_zero_of_not fun ⟨Λ₁, h, _⟩ =>
      hw (Mv_of_MvTo S h))
  have hsupp : (Function.support fun y : {y // S.IsTerm d y ∧
      S.InFF β (↑j + 1) βJ d y} =>
        S.kern β (↑j + 1) βJ d Λ ↑y).Finite :=
    (hfinK.preimage Subtype.val_injective.injOn).subset fun y hy => hy
  have hK : (((∑ᶠ y : {y // S.IsTerm d y ∧
      S.InFF β (↑j + 1) βJ d y},
        S.kern β (↑j + 1) βJ d Λ ↑y : ℝ)) : ℂ) =
      (S.cK β βJ : ℂ) *
        _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind Good) := by
    have hmap := map_finsum Complex.ofRealHom hsupp
    simp only [Complex.ofRealHom_eq_coe] at hmap
    rw [hmap, ← hsum]
    simp
  set H : S.MW → ℂ := fun w =>
    _root_.GlobalTheory.IdxInt.ind (S.Mv (↑j + 1) d Λ) w +
      (-1) * _root_.GlobalTheory.IdxInt.ind Good w with hH
  have hNH : _root_.GlobalTheory.IdxInt.Nice (S.refA (↑j + 1) Λ) H :=
    (hlin.1 _ _ hNMv (hlin.2.1 (-1) _ hNG).1).1
  have hIH : _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ) H =
      _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind (S.Mv (↑j + 1) d Λ)) +
        (-1) * _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind Good) := by
    rw [← (hlin.2.1 (-1) _ hNG).2]
    exact (hlin.1 _ _ hNMv (hlin.2.1 (-1) _ hNG).1).2.1
  have hbound : ∀ w, ‖H w‖ ≤ (_root_.GlobalTheory.IdxInt.ind
      (fun w => S.Mv (↑j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1) w).re := by
    intro w
    by_cases hw : S.Mv (↑j + 1) d Λ w
    · by_cases hg : Good w
      · rw [hH]
        simp only
        rw [ind_eq_one_of_pos hw, ind_eq_one_of_pos hg]
        unfold _root_.GlobalTheory.IdxInt.ind
        split_ifs <;> simp
      · have hleak : ¬ S.NoLeak Λ w.2.1 := by
          intro hno
          apply hg
          obtain ⟨Λ₁, h₁, hT₁⟩ := exists_MvTo_isTerm_of_Mv_of_InFF S j β βJ d Λ hT hF w hw
          refine ⟨Λ₁, h₁, hT₁, ?_⟩
          have hw' := hw
          unfold _root_.GlobalTheory.HL.Frames.Mv at hw'
          have h₁' := h₁
          unfold _root_.GlobalTheory.HL.Frames.MvTo at h₁'
          unfold _root_.GlobalTheory.HL.Frames.NoLeak at hno
          exact _root_.GlobalTheory.HL.OffLeak.inFF_moved_of_not_leak L r k S j β βJ d Λ hT hF _ _ _ _
            hw' hno Λ₁ h₁'.2
        rw [hH]
        simp only
        rw [ind_eq_one_of_pos hw, ind_eq_zero_of_not hg, ind_eq_one_of_pos ⟨hw, hleak⟩]
        simp
    · have hg : ¬ Good w := fun ⟨Λ₁, h, _⟩ => hw (Mv_of_MvTo S h)
      rw [hH]
      simp only
      rw [ind_eq_zero_of_not hw, ind_eq_zero_of_not hg]
      unfold _root_.GlobalTheory.IdxInt.ind
      split_ifs <;> simp
  have hnorm := (hlin.1 _ _ hNH hNLeak).2.2 hbound
  have hKre := congrArg Complex.re hK
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hKre
  have hsplitre := congrArg Complex.re hIH
  simp only [Complex.add_re, neg_one_mul, Complex.neg_re] at hsplitre
  have hHre : |S.cK β βJ *
      (_root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ) H).re| ≤
      16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
    rw [abs_mul, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc).trans
      ((mul_le_mul_of_nonneg_left hnorm hc).trans hIleak)
  rw [hKre]
  rw [hsplitre] at hHre
  rw [abs_le] at hI hHre ⊢
  constructor <;> nlinarith [hI.1, hI.2, hHre.1, hHre.2]

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermDefectEqOfLatticeEqStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTerm_defect_eq_of_lattice_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d d' : LocNG.Datum P) (τ τ' : Term V M r), LocNG.IsTermOver P d τ → LocNG.IsTermOver P d' τ' → τ.abelian₂ = τ'.abelian₂ → (LocNG.BBne (H := H) τ ↔ LocNG.BBne (H := H) τ') := by
  first | exact @GlobalTheory.HL.LocDefect.bbne_of_lam_eq | exact GlobalTheory.HL.LocDefect.bbne_of_lam_eq | (intros; apply GlobalTheory.HL.LocDefect.bbne_of_lam_eq <;> assumption)
end

