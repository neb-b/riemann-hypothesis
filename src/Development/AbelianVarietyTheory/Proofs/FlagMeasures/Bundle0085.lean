module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MoveLatticeIsTermSameDatumWithWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCountBoundFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0083
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetInFamilyMovedOfNotLeak
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.OffLeak

theorem ncard_image_eq_of_iff {α β γ : Type*} (B : Set α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ B, ∀ b ∈ B, f a = f b ↔ g a = g b) : (f '' B).ncard = (g '' B).ncard := by
  classical
  refine Set.ncard_congr (fun c hc => g (Classical.choose ((Set.mem_image f B c).1 hc))) ?_ ?_ ?_
  · intro c hc
    exact ⟨_, (Classical.choose_spec ((Set.mem_image f B c).1 hc)).1, rfl⟩
  · intro c c' hc hc' hgg
    have e₁ := Classical.choose_spec ((Set.mem_image f B c).1 hc)
    have e₂ := Classical.choose_spec ((Set.mem_image f B c').1 hc')
    exact e₁.2.symm.trans (((h _ e₁.1 _ e₂.1).2 hgg).trans e₂.2)
  · rintro _ ⟨a, ha, rfl⟩
    have hfa : f a ∈ f '' B := ⟨a, ha, rfl⟩
    refine ⟨f a, hfa, ?_⟩
    have e := Classical.choose_spec ((Set.mem_image f B (f a)).1 hfa)
    exact (h _ e.1 _ ha).1 e.2

theorem coset_eq_iff {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (M : Submodule R V) (a b : V) :
    ({x | x - a ∈ M} : Set V) = {x | x - b ∈ M} ↔ a - b ∈ M := by
  constructor
  · intro h
    have ha : a ∈ ({x | x - a ∈ M} : Set V) := by simp
    rw [h] at ha
    exact ha
  · intro h
    ext x
    constructor
    · intro hx
      have hxb : (x - a) + (a - b) ∈ M := M.add_mem hx h
      have e : (x - a) + (a - b) = x - b := by abel
      rw [e] at hxb
      exact hxb
    · intro hx
      have hxa : (x - b) - (a - b) ∈ M := M.sub_mem hx h
      have e : (x - b) - (a - b) = x - a := by abel
      rw [e] at hxa
      exact hxa

theorem relIndex_eq_of_reps {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (M T B : Submodule R V)
    (hM : M ≤ T) (hB : B ≤ T) (h : ∀ y ∈ T, ∃ y₀ ∈ B, y - y₀ ∈ M) :
    M.toAddSubgroup.relIndex T.toAddSubgroup =
      (M.toAddSubgroup ⊓ B.toAddSubgroup).relIndex B.toAddSubgroup := by
  have hT : T.toAddSubgroup = B.toAddSubgroup ⊔ M.toAddSubgroup := by
    apply le_antisymm
    · intro y hy
      obtain ⟨y₀, hy₀, hm⟩ := h y hy
      have hs : y₀ + (y - y₀) ∈ B.toAddSubgroup ⊔ M.toAddSubgroup :=
        AddSubgroup.add_mem_sup hy₀ hm
      have e : y₀ + (y - y₀) = y := by abel
      rw [e] at hs
      exact hs
    · exact sup_le (fun x hx => hB hx) (fun x hx => hM hx)
  rw [hT, AddSubgroup.relIndex_sup_right, AddSubgroup.inf_relIndex_right]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem spanTo_mono {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V) {a b : ℕ}
    (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b := by
  unfold Frames.spanTo
  apply Submodule.span_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi h, rfl⟩

theorem th_ne_zero {L : LocE F E} {r k : ℕ} (S : Frames L r k) : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h0
    apply S.ϖ_irr.ne_zero
    exact Subtype.ext h0
  · exact one_ne_zero

set_option maxHeartbeats 1000000 in
theorem inFF_moved_of_not_leak : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.InFF β (j + 1) βJ d Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hMv hleak Λ₁ hΛ₁
  obtain ⟨hT₁, hY⟩ := _root_.GlobalTheory.HL.MoveSame.move_same L r k S j β βJ d Λ hT hF x x' u s hMv Λ₁ hΛ₁
  have h78 := _root_.GlobalTheory.HL.TraceRep.class_from_trace L r k S j β βJ d Λ hT hF x x' u s hMv hleak Λ₁ hΛ₁
  have h64 := GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ hT
  have h64₁ := GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ₁ hT₁
  have hMs : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hMs₁ : S.M d Λ₁ ≤ S.sat Λ₁ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ₁ hT₁).2.2.1
  unfold Frames.InFF at hF ⊢
  obtain ⟨hTB, hbe, hle, ⟨z, hz, hzJ⟩, hn⟩ := hF
  unfold Frames.TypeBe at hTB
  obtain ⟨Y, hYdef⟩ : ∃ Y : Submodule E S.V, Y = S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1) :=
    ⟨_, rfl⟩
  have hYmem : ∀ y, y ∈ Y ↔ y ∈ S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1) := by
    intro y
    rw [hYdef]
  have hjr : (j : ℕ) + 1 ≤ r := j.isLt
  have hjr' : (j : ℕ) + 1 ≤ r + 1 := by omega
  have hYME : Y ≤ S.ME := by
    rw [hYdef]
    exact sup_le_sup (spanTo_mono S S.f hjr') (spanTo_mono S S.f' hjr')
  have hYX : Y ≤ S.X ⊔ S.X' := by
    rw [hYdef]
    exact sup_le_sup (spanTo_mono S S.f hjr) (spanTo_mono S S.f' hjr)
  have hYY : ∀ y ∈ Y, (y ∈ Λ → y ∈ Λ₁) ∧ (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) ∧
      S.lev (S.fr d Λ₁) (S.fr' d Λ₁) y = S.lev (S.fr d Λ) (S.fr' d Λ) y :=
    fun y hy => hY y ((hYmem y).1 hy)
  have memSat : ∀ (Λ' : Submodule L.O S.V) (y : S.V), y ∈ S.sat Λ' ↔ y ∈ Λ' ∧ y ∈ S.ME := by
    intro Λ' y
    unfold Frames.sat
    simp [Submodule.mem_inf]
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Submodule L.O S.V, ∀ y, y ∈ B₀ ↔ y ∈ Λ ∧ y ∈ Y :=
    ⟨Λ ⊓ Y.restrictScalars L.O, fun y => by simp [Submodule.mem_inf]⟩
  have hB₀Y : ∀ y ∈ B₀, y ∈ Y := fun y hy => ((hB₀ y).1 hy).2
  have hB₀sat : ∀ y ∈ B₀, y ∈ S.sat Λ := fun y hy =>
    (memSat Λ y).2 ⟨((hB₀ y).1 hy).1, hYME (hB₀Y y hy)⟩
  have hB₀Λ₁ : ∀ y ∈ B₀, y ∈ Λ₁ := fun y hy => (hYY y (hB₀Y y hy)).1 ((hB₀ y).1 hy).1
  have hB₀sat₁ : ∀ y ∈ B₀, y ∈ S.sat Λ₁ := fun y hy =>
    (memSat Λ₁ y).2 ⟨hB₀Λ₁ y hy, hYME (hB₀Y y hy)⟩
  have hMiff : ∀ y ∈ B₀, (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) := fun y hy => (hYY y (hB₀Y y hy)).2.1
  have hlev : ∀ y ∈ B₀, S.levC d Λ₁ y = S.levC d Λ y := by
    intro y hy
    unfold Frames.levC
    exact (hYY _ (Y.smul_mem _ (hB₀Y y hy))).2.2

  have rep : ∀ y ∈ S.sat Λ, ∃ y₁ ∈ B₀, y - y₁ ∈ S.M d Λ := by
    intro y hy
    obtain ⟨y₁, hy₁Y, hm⟩ := (h64.2.1 y hy (↑j + 1)).1 (hle y hy)
    have hs : y - (y - y₁) ∈ S.sat Λ := (S.sat Λ).sub_mem hy (hMs hm)
    have e : y - (y - y₁) = y₁ := by abel
    rw [e] at hs
    exact ⟨y₁, (hB₀ y₁).2 ⟨((memSat Λ y₁).1 hs).1, (hYmem y₁).2 hy₁Y⟩, hm⟩

  have rep₁ : ∀ y ∈ S.sat Λ₁, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ₁ := by
    intro y hy
    obtain ⟨y₀, h1, h2, h3⟩ := h78 y hy
    exact ⟨y₀, (hB₀ y₀).2 ⟨h1, (hYmem y₀).2 h2⟩, h3⟩

  have hinv : ∀ (Λ' : Submodule L.O S.V), S.IsTerm d Λ' → ∀ y ∈ S.sat Λ', ∀ y₁,
      y - y₁ ∈ S.M d Λ' → S.levC d Λ' y₁ = S.levC d Λ' y := by
    intro Λ' hT' y hy y₁ hm
    have hm' : -(y - y₁) ∈ S.M d Λ' := (S.M d Λ').neg_mem hm
    have e₁ : -(y - y₁) = y₁ - y := by abel
    rw [e₁] at hm'
    have hc := (GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ' hT').2.2.1 y hy (y₁ - y) hm'
    have e₂ : y + (y₁ - y) = y₁ := by abel
    rw [e₂] at hc
    exact hc

  have hbe₁ : S.be d Λ₁ = S.be d Λ := by
    unfold Frames.be
    rw [relIndex_eq_of_reps (S.M d Λ₁) (S.sat Λ₁) B₀ hMs₁ (fun y hy => hB₀sat₁ y hy) rep₁,
      relIndex_eq_of_reps (S.M d Λ) (S.sat Λ) B₀ hMs (fun y hy => hB₀sat y hy) rep]
    congr 1
    ext y
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup]
    exact ⟨fun h => ⟨(hMiff y h.2).1 h.1, h.2⟩, fun h => ⟨(hMiff y h.2).2 h.1, h.2⟩⟩

  have hth : S.th ≠ 0 := th_ne_zero S
  have hInTh : ∀ w : S.V, algebraMap F E S.th⁻¹ • w ∈ (B₀ : Set S.V) → S.InTh Λ w := by
    intro w hw
    refine ⟨_, ((hB₀ _).1 hw).1, ?_⟩
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul]
  have hnotBB : ¬ S.BBzero d Λ₁ := by
    intro hbb
    apply hTB.1
    unfold Frames.BBzero at hbb ⊢
    refine le_antisymm hMs ?_
    intro y hy
    obtain ⟨y₁, hy₁, hm⟩ := rep y hy
    have h1 : y₁ ∈ S.M d Λ₁ := by
      rw [hbb]
      exact hB₀sat₁ y₁ hy₁
    have h2 : (y - y₁) + y₁ ∈ S.M d Λ := (S.M d Λ).add_mem hm ((hMiff y₁ hy₁).1 h1)
    have e : (y - y₁) + y₁ = y := by abel
    rw [e] at h2
    exact h2
  have hTB₁ : S.TypeBe d Λ₁ :=
    _root_.GlobalTheory.HL.TypeRep.main L r k S d Λ₁ hT₁ hnotBB (B₀ : Set S.V)
      (fun y hy => ⟨hB₀Λ₁ y hy, hYX (hB₀Y y hy)⟩) rep₁
      (fun x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' h1 h2 =>
        hTB.2.2 x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' (hInTh _ h1) (hInTh _ h2))

  have hle₁ : ∀ y ∈ S.sat Λ₁, S.levC d Λ₁ y ≤ ↑j + 1 := by
    intro y hy
    obtain ⟨y₀, hy₀, hm⟩ := rep₁ y hy
    have hy0 : y₀ ∈ S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1) := (hYmem y₀).1 (hB₀Y y₀ hy₀)
    have key := (h64₁.2.1 y hy (↑j + 1)).2
    have ex : ∃ y₁ ∈ S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1), y - y₁ ∈ S.M d Λ₁ :=
      ⟨y₀, hy0, hm⟩
    exact key ex
  have hex₁ : ∃ y ∈ S.sat Λ₁, S.levC d Λ₁ y = ↑j + 1 := by
    obtain ⟨y₁, hy₁, hm⟩ := rep z hz
    refine ⟨y₁, hB₀sat₁ y₁ hy₁, ?_⟩
    rw [hlev y₁ hy₁, hinv Λ hT z hz y₁ hm, hzJ]

  have hset : ∀ (Λ' : Submodule L.O S.V), S.IsTerm d Λ' → (∀ y ∈ B₀, y ∈ S.sat Λ') →
      (∀ y ∈ S.sat Λ', ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ') →
      {C : Set S.V | ∃ y ∈ S.sat Λ', S.levC d Λ' y = ↑j + 1 ∧ C = {x | x - y ∈ S.M d Λ'}} =
        (fun y => {x | x - y ∈ S.M d Λ'}) '' {y | y ∈ B₀ ∧ S.levC d Λ' y = ↑j + 1} := by
    intro Λ' hT' hBs hrep
    ext C
    constructor
    · rintro ⟨y, hy, hyJ, rfl⟩
      obtain ⟨y₀, hy₀, hm⟩ := hrep y hy
      refine ⟨y₀, ⟨hy₀, (hinv Λ' hT' y hy y₀ hm).trans hyJ⟩, ?_⟩
      have hm' : -(y - y₀) ∈ S.M d Λ' := (S.M d Λ').neg_mem hm
      have e : -(y - y₀) = y₀ - y := by abel
      rw [e] at hm'
      exact (coset_eq_iff (S.M d Λ') y₀ y).2 hm'
    · rintro ⟨y, ⟨hy, hyJ⟩, rfl⟩
      exact ⟨y, hBs y hy, hyJ, rfl⟩
  have hn₁ : S.nLev d Λ₁ (↑j + 1) = βJ := by
    rw [← hn]
    unfold Frames.nLev
    rw [hset Λ₁ hT₁ hB₀sat₁ rep₁, hset Λ hT hB₀sat rep]
    have hBB : {y | y ∈ B₀ ∧ S.levC d Λ₁ y = ↑j + 1} = {y | y ∈ B₀ ∧ S.levC d Λ y = ↑j + 1} := by
      ext y
      exact ⟨fun h => ⟨h.1, (hlev y h.1).symm.trans h.2⟩, fun h => ⟨h.1, (hlev y h.1).trans h.2⟩⟩
    rw [hBB]
    apply ncard_image_eq_of_iff
    intro a ha b hb
    have hab : a - b ∈ Y := Y.sub_mem (hB₀Y a ha.1) (hB₀Y b hb.1)
    exact (coset_eq_iff (S.M d Λ₁) a b).trans ((hYY _ hab).2.1.trans (coset_eq_iff (S.M d Λ) a b).symm)
  exact ⟨hTB₁, hbe₁.trans hbe, hle₁, hex₁, hn₁⟩

end GlobalTheory.HL.OffLeak
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMoveTermWeightCharacter
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveTerm
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem cj_mem_O {c : E} (hc : c ∈ L.O) : L.cj c ∈ L.O := by
  rw [L.O_def] at hc ⊢
  exact hc.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem top_coord (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (w : S.GLV) (hw : w ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1))
    (al : Fin (r + 1) → E) (e : x = ∑ i, al i • w (g i)) :
    S.h x (gs j) = al j.castSucc := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hw
  obtain ⟨⟨-, h1⟩, -⟩ := hw
  have e' : x = w (∑ i, al i • g i) := by simp [e]
  have hz : ∑ i, al i • g i ∈ S.spanTo g (j + 1) := ((h1 j).1 _).1 (e' ▸ hx)
  have hB := (h1 j).2 _ hz
  have hK : S.spanTo g j ≤ LinearMap.ker (FramePsi.pairL L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg]
    rintro rfl
    simp at hi
  have h2 := LinearMap.mem_ker.1 (hK hB)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← e', map_sub, map_sum, sub_eq_zero] at h2
  have h3 : ∀ i, FramePsi.pairL L S.Hm (gs j) (al i • g i) = if i = j.castSucc then al i else 0 := by
    intro i
    rw [map_smul]
    change al i * hf L S.Hm (g i) (gs j) = _
    rw [hd]
    split_ifs <;> simp
  simp only [h3, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  exact h2

theorem psi'_eq_one (n : S.GLV) (hn : ∀ v ∈ perp L S.Hm S.X', n v = v) : S.psi' n = 1 := by
  have h : ∀ j, S.coef S.f' S.es' n j = 0 := by
    intro j
    have hp : S.f' j.succ ∈ perp L S.Hm S.X' := by
      refine FramePsi.hf_span_right L S.Hm _ _ ?_
      rintro _ ⟨i, hi, rfl⟩
      rw [S.gram', if_neg]
      rintro ⟨-, rfl⟩
      simp at hi
    rw [Frames.coef, hn _ hp, Frames.h, S.dual', if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [Frames.psi', Frames.psiOf, h]

theorem perp_left {A B : Submodule E S.V} {u : S.V} (hu : u ∈ perp L S.Hm (A ⊔ B)) :
    u ∈ perp L S.Hm A := fun y hy => hu y (Submodule.mem_sup_left hy)

theorem perp_right {A B : Submodule E S.V} {u : S.V} (hu : u ∈ perp L S.Hm (A ⊔ B)) :
    u ∈ perp L S.Hm B := fun y hy => hu y (Submodule.mem_sup_right hy)

end

theorem move_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∃ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s ∧ S.IsTerm d Λ₁ ∧ S.moved Λ₁ x (-u) (L.cj s) = Λ ∧ (S.InFF β (j + 1) βJ d Λ₁ → S.IsMove (j + 1) d Λ₁ x x' (-u) (L.cj s)) ∧ ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → S.om d Λ₁ = S.om d Λ * L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', e₀, e₀i, e₀', f'', hset, hW⟩ :=
    _root_.GlobalTheory.HL.MoveWit.main L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨t1, t2, -, -, -, -, -, hux, -, -, -⟩ := _root_.GlobalTheory.HL.MoveFacts.move_facts L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨hT₁, hY⟩ := _root_.GlobalTheory.HL.MoveSame.move_same L r k S j β βJ d Λ hT hFF x x' u s hM _ hset
  obtain ⟨hx, hx', hth, hlev, hu, hup, ⟨c, hc, hsc⟩, hs⟩ := hM
  have hb : x + x' ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1) := Submodule.add_mem_sup hx hx'
  have hmem : ∀ v, v ∈ (n₀⁻¹ • Λ : Submodule L.O S.V) ↔ eich L S.Hm x u s v ∈ Λ := fun v =>
    Set.ext_iff.1 hset v
  refine ⟨n₀⁻¹ • Λ, hset, hT₁, ?_, fun _ => ⟨hx, hx', ?_, ?_, ?_, (perp L S.Hm _).neg_mem hup, ?_, ?_⟩,
    fun al al' ex ex' => ?_⟩
  · ext v
    change eich L S.Hm x (-u) (L.cj s) v ∈ (n₀⁻¹ • Λ : Submodule L.O S.V) ↔ v ∈ Λ
    rw [hmem, ← e₀, ← e₀i]
    rw [show n₀ (n₀⁻¹ v) = v from n₀.apply_symm_apply v]
  · obtain ⟨y, hy, e⟩ := hth
    refine ⟨y, (hY y ?_).1 hy, e⟩
    have : y = algebraMap F E S.th⁻¹ • (x + x') := by
      rw [e, smul_smul, WitIndep.th_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hb
  · rw [(hY _ hb).2.2, hlev]
  · refine Submodule.neg_mem _ ((hmem u).2 ?_)
    have : eich L S.Hm x u s u = u + s • x + L.cj s • x := by
      have h1 : hf L S.Hm u x = 0 := hux
      have h2 : hf L S.Hm u u = s + L.cj s := hs.symm
      rw [eich, h1, h2]
      module
    rw [this]
    exact Λ.add_mem (Λ.add_mem hu t1) t2
  · exact ⟨L.cj c, cj_mem_O hc, by rw [hsc, map_mul, AlgEquiv.commutes]⟩
  · rw [L.cj_cj, Frames.h, hf_neg_l, hf_neg_r, neg_neg, add_comm]
    exact hs
  · have K := (TermBasic.term_basic L r k S d Λ hT).2.1
    have hw := K.2.2.1
    have hw' := K.2.2.2.1
    obtain ⟨p1, p2, p3, p4⟩ := FramePsi.psi_unitary_character L r k S
    obtain ⟨m, -, em, -, -, pm⟩ := EichlerUnip.eichler_mem_unip L r k S S.f S.es (.inl ⟨rfl, rfl⟩) j x u s
      hx (perp_left S hup) hs
    obtain ⟨m', -, em', -, -, pm'⟩ := EichlerUnip.eichler_mem_unip L r k S S.f' S.es' (.inr ⟨rfl, rfl⟩)
      j x' u s hx' (perp_right S hup) hs
    obtain rfl : m = n₀ := LinearEquiv.ext fun v => (em v).trans (e₀ v).symm
    obtain rfl : m' = n₀' := LinearEquiv.ext fun v => (em' v).trans (e₀' v).symm
    have q := pm _ hw
    have q' := pm' _ hw'
    rw [top_coord S S.f S.es S.dual _ hw j x hx al ex] at q
    rw [top_coord S S.f' S.es' S.dual' _ hw' j x' hx' al' ex'] at q'
    have a1 := p1 m hn₀ _ (mul_mem (inv_mem hn₀) hw)
    rw [mul_inv_cancel_left] at a1
    have a2 := p2 _ (mul_mem hn'' hn₀') _ hw'
    rw [p2 _ hn'' _ hn₀', psi'_eq_one S n'' f'', one_mul] at a2
    have z1 : S.psi m ≠ 0 := fun h => by simpa [h] using (p3 m).1
    have z2 : S.psi' m' ≠ 0 := fun h => by simpa [h] using (p3 m').2
    have hchi : L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ +
        al' j.castSucc • S.fr' d Λ j.succ) u)) = (S.psi m * S.psi' m')⁻¹ := by
      rw [AddChar.map_neg_eq_inv]
      congr 1
      change _ = S.psiOf S.f S.es m * S.psiOf S.f' S.es' m'
      rw [q, q', ← AddChar.map_add_eq_mul, Frames.h, hf_add_l, hf_smul_l, hf_smul_l, mul_add]
      rfl
    rw [(WitIndep.witness_independence L r k S _ _ _ _ hW).1, hchi, a2, Frames.om, a1]
    field_simp

end GlobalTheory.HL.MoveTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermCountFrameClassLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TermCount

theorem encard_le_mul {α β : Type} (s : Set α) (f : α → β) (t : Set β) (A B : ℝ≥0∞)
    (hf : ∀ a ∈ s, f a ∈ t) (ht : (t.encard : ℝ≥0∞) ≤ A)
    (hB : ∀ b ∈ t, (({a | a ∈ s ∧ f a = b} : Set α).encard : ℝ≥0∞) ≤ B) :
    (s.encard : ℝ≥0∞) ≤ A * B := by
  have h1 : s ⊆ ⋃ b : t, {a | a ∈ s ∧ f a = b.1} := by
    intro a ha
    exact Set.mem_iUnion.2 ⟨⟨f a, hf a ha⟩, ha, rfl⟩
  calc (s.encard : ℝ≥0∞) = ∑' _ : s, (1 : ℝ≥0∞) := (ENNReal.tsum_set_one s).symm
    _ ≤ ∑' _ : (⋃ b : t, {a | a ∈ s ∧ f a = b.1} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_mono_subtype (fun _ => (1 : ℝ≥0∞)) h1
    _ ≤ ∑' b : t, ∑' _ : ({a | a ∈ s ∧ f a = b.1} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_iUnion_le_tsum (fun _ => (1 : ℝ≥0∞)) _
    _ ≤ ∑' _ : t, B := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        rw [ENNReal.tsum_set_one]
        exact hB b.1 b.2
    _ = (t.encard : ℝ≥0∞) * B := ENNReal.tsum_set_const t B
    _ ≤ A * B := by gcongr

theorem nT_cardI_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (r k : ℕ) (S : Frames L r k) (d : S.Datum) (C : Set S.FrP) (j : ℕ) :
    (S.nT d C fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  unfold Frames.nT
  set s : Set (Submodule L.O S.V) := {Λ | S.IsTerm d Λ ∧ S.cardI d Λ = j ∧ S.Fr d Λ = C} with hs
  rcases s.eq_empty_or_nonempty with he | ⟨Λ₁, hΛ₁, -, hC₁⟩
  · simp [he]
  obtain ⟨ha, -, -, hq, hH1, -⟩ := _root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₁ hΛ₁
  have hcls : S.IsCls C := hC₁ ▸ (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ₁ hΛ₁).2.2.2.2.2.2.1.1
  have hp : (S.fr d Λ₁, S.fr' d Λ₁) ∈ C :=
    hC₁ ▸ (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ₁) (S.fr' d Λ₁)).1
  have hM : ∀ Λ ∈ s, S.Mof (S.fr d Λ₁) (S.fr' d Λ₁) ≤ S.sat Λ := by
    rintro Λ ⟨hΛ, -, hC⟩
    have h1 := ((GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).2.1
      (S.fr d Λ₁, S.fr' d Λ₁) (by
        have : S.frameCls (S.fr d Λ) (S.fr' d Λ) = C := hC
        rw [this]; exact hp)).2
    simp only at h1
    rw [h1]
    exact (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ).2.2.1
  have hmain : (s.encard : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) *
      (((S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1)) *
        (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2))) := by
    refine encard_le_mul s S.sat _ _ _ ?_ (_root_.GlobalTheory.FrameOver.encard_overlattices_le L r k S C hcls _ hp ha) ?_
    · intro Λ hΛ
      refine ⟨hM Λ hΛ, fun x hx => hx.2, fun x hx y hy => ?_⟩
      exact ((GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ.1).1.2 y).2 hy.1 x hx.1
    · intro Mh hMh
      refine encard_le_mul _ (fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) _ _ _ ?_
        (_root_.GlobalTheory.HL.GluingKernels.encard_kernels_le L r k S d C Mh j) ?_
      · rintro Λ ⟨⟨h1, h2, h3⟩, h4⟩
        exact ⟨Λ, ⟨h1, h3, h4, h2⟩, rfl⟩
      · intro Λ₀ _
        refine le_trans ?_ (_root_.GlobalTheory.HL.Gluing.gluing_count L r k S C hcls _ hp Mh Λ₀ hMh.1)
        refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
        rintro Λ ⟨⟨⟨h1, -, -⟩, h4⟩, h5⟩
        exact ⟨(GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h1).1, h4, h5⟩
  refine hmain.trans ?_
  have hq' : (S.q : ℝ) ^ S.a.toNat ≤ S.Hp := by
    have : S.a = (S.a.toNat : ℤ) := (Int.toNat_of_nonneg ha).symm
    rw [this, zpow_natCast] at hq
    exact hq
  have hreal : ((S.q : ℝ) ^ S.a.toNat) ^ (10 * (r + 1)) * (j : ℝ) ^ (k - 1) ≤
      S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ((S.q : ℝ) ^ S.a.toNat) ^ (10 * (r + 1)) ≤ S.Hp ^ (10 * (r + 1)) :=
          pow_le_pow_left₀ (by positivity) hq' _
      _ ≤ S.Hp ^ (12 * (r + 1)) := pow_le_pow_right₀ hH1 (by omega)
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hreal)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  ring

end GlobalTheory.HL.TermCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesLocalTermsWithDataStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryComplement_moves_local_terms_with_data : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ h ∈ P.UW0, ∀ (d d' : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Moves h d d' → LocNG.IsTermOver P d' ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ∧ (LocNG.BBne (H := H) ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ↔ LocNG.BBne (H := H) τ) := by
  first | exact @GlobalTheory.HL.LocalMove.main | exact GlobalTheory.HL.LocalMove.main | (intros; apply GlobalTheory.HL.LocalMove.main <;> assumption)
end

