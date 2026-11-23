module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MoveLatticeIsTermSameDatumWithWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeTraceInitialSpanVolumeEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDefectClassMemTraceFirstFrameSpan
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TraceRep

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E}

theorem hf_add {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_sub {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_zero {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    hf L Hm 0 y = 0 := by
  simp [hf]

theorem hf_neg_right {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a y : Fin n → E) :
    hf L Hm a (-y) = - hf L Hm a y := by
  simp [hf, Finset.sum_neg_distrib]

theorem hf_swap {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (v w : Fin n → E) :
    hf L Hm w v = L.cj (hf L Hm v w) := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_swap_zero {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) {v w : Fin n → E}
    (h0 : hf L Hm v w = 0) : hf L Hm w v = 0 := by
  rw [hf_swap h, h0, map_zero]

variable {r k : ℕ} (S : Frames L r k)

theorem frame_perp (g : Fin (r + 1) → S.V) (T : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then T else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (b : Fin (r + 1)) :
    n (g b) ∈ perp L S.Hm (S.spanTo g r) := by
  refine (hn.2.1 (g b)).2 ?_
  intro y hy
  apply hf_swap_zero S.herm.1
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [hg, if_neg]
    rintro ⟨rfl, -⟩
    simp at hi
  | zero => exact hf_zero _ _
  | add a c _ _ ha hc => rw [hf_add, ha, hc, add_zero]
  | smul c a _ ha => rw [hf_smul, ha, mul_zero]

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem mof_transport (Λ : Submodule L.O S.V) (Y : Submodule E S.V) (g g' g₁ g₁' : Fin (r + 1) → S.V)
    (x x' u : S.V) (h1 : ∀ b, g₁ b = g b - S.h (g b) u • x) (h1' : ∀ b, g₁' b = g' b + S.h (g' b) u • x')
    (hO : ∀ b, S.h (g' b) u ∈ L.O) (hΛ : algebraMap F E S.th⁻¹ • (x + x') ∈ Λ) (hY : x + x' ∈ Y)
    (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ y₁ ∈ Λ, y₁ ∈ Y ∧ m - S.h m u • x + y₁ ∈ S.Mof g₁ g₁' := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    rcases hm with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · refine ⟨0, Λ.zero_mem, Y.zero_mem, ?_⟩
      rw [add_zero, ← h1]
      exact Submodule.subset_span (Or.inl ⟨b, rfl⟩)
    · refine ⟨S.h (g' b) u • (algebraMap F E S.th⁻¹ • (x + x')), Λ.smul_mem ⟨_, hO b⟩ hΛ,
        Y.smul_mem _ (Y.smul_mem _ hY), ?_⟩
      have : algebraMap F E S.th⁻¹ • (g' b - g b) - S.h (algebraMap F E S.th⁻¹ • (g' b - g b)) u • x +
          S.h (g' b) u • (algebraMap F E S.th⁻¹ • (x + x')) = algebraMap F E S.th⁻¹ • (g₁' b - g₁ b) := by
        rw [h1, h1']
        simp only [Frames.h, hf_smul, hf_sub]
        module
      simp only []
      rw [this]
      exact Submodule.subset_span (Or.inr ⟨b, rfl⟩)
  | zero =>
    refine ⟨0, Λ.zero_mem, Y.zero_mem, ?_⟩
    simp [Frames.h, hf_zero]
  | add a c _ _ ha hc =>
    obtain ⟨y, hy, hy', ha⟩ := ha
    obtain ⟨z, hz, hz', hc⟩ := hc
    refine ⟨y + z, Λ.add_mem hy hz, Y.add_mem hy' hz', ?_⟩
    have : a + c - S.h (a + c) u • x + (y + z) = (a - S.h a u • x + y) + (c - S.h c u • x + z) := by
      simp only [Frames.h, hf_add]
      module
    rw [this]
    exact Submodule.add_mem _ ha hc
  | smul c a _ ha =>
    obtain ⟨y, hy, hy', ha⟩ := ha
    refine ⟨(c : E) • y, Λ.smul_mem c hy, Y.smul_mem _ hy', ?_⟩
    have : c • a - S.h (c • a) u • x + (c : E) • y = (c : E) • (a - S.h a u • x + y) := by
      change (c : E) • a - S.h ((c : E) • a) u • x + (c : E) • y = _
      simp only [Frames.h, hf_smul]
      module
    rw [this]
    exact Submodule.smul_mem _ c ha

theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

end GlobalTheory.HL.TraceRep


open GlobalTheory.HL.TraceRep in
theorem GlobalTheory.HL.TraceRep.class_from_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → ∀ y ∈ S.sat Λ₁, ∃ y₀ ∈ Λ, y₀ ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ y - y₀ ∈ S.M d Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hmv hw Λ₁ hΛ₁ y hy
  obtain ⟨w, hwΛ, hwW, huw⟩ := hw
  obtain ⟨hsx, -, -, -, -, -, -, hux, hux', hxX, hxX'⟩ :=
    _root_.GlobalTheory.HL.MoveFacts.move_facts L r k S j β βJ d Λ hT hF x x' u s hmv
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', -, e1, e2, e3, e4, hW₁⟩ :=
    _root_.GlobalTheory.HL.MoveWit.main L r k S j β βJ d Λ hT hF x x' u s hmv
  obtain ⟨hSD, hW, hMs, -, hf', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hlev := (_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.2.2.2.2.2
  have hΛe : n₀⁻¹ • Λ = Λ₁ := SetLike.coe_injective (e4.trans hΛ₁.symm)
  rw [hΛe] at hW₁
  have hM₁ := (GlobalTheory.HL.WitIndep.witness_independence L r k S d Λ₁ _ _ hW₁).2.1
  obtain ⟨hx, hx', ⟨t, ht, hte⟩, -, huΛ, huY, -⟩ := hmv
  have hH := S.herm.1
  have hint : ∀ a ∈ Λ, ∀ b ∈ Λ, S.h a b ∈ L.O := fun a ha b hb => (hSD.2 b).2 hb a ha
  have hp := frame_perp S S.f _ S.gram _ hW.2.2.1
  have hp' := frame_perp S S.f' _ S.gram' _ hW.2.2.2.1
  have hxME : x ∈ S.ME :=
    Submodule.mem_sup_left (spanTo_mono S S.f (Nat.le_succ r) hxX)
  have hyME : y ∈ S.ME := hy.2
  have hyΛ : eich L S.Hm x u s y ∈ Λ := by
    have : y ∈ (Λ₁ : Set S.V) := hy.1
    rw [hΛ₁] at this
    exact this
  have hκ : hf L S.Hm y x ∈ L.O := by
    have h1 := hint _ hyΛ _ hwΛ
    have h2 : hf L S.Hm y w = 0 := hf_swap_zero hH (hwW y hyME)
    have h3 : hf L S.Hm x w = 0 := hf_swap_zero hH (hwW x hxME)
    have h4 : hf L S.Hm u w = 1 := huw
    simp only [Frames.h, eich, hf_sub, hf_add, hf_smul, h2, h3, h4] at h1
    have := L.O.neg_mem h1
    simpa using this
  have hbΛ : y + hf L S.Hm y u • x ∈ Λ := by
    have : y + hf L S.Hm y u • x = eich L S.Hm x u s y + hf L S.Hm y x • (u + s • x) := by
      simp [eich]
    rw [this]
    exact Λ.add_mem hyΛ (Λ.smul_mem ⟨_, hκ⟩ (Λ.add_mem huΛ hsx))
  have hbs : y + hf L S.Hm y u • x ∈ S.sat Λ :=
    ⟨hbΛ, S.ME.add_mem hyME (S.ME.smul_mem _ hxME)⟩
  obtain ⟨y₀, hy₀Y, hm⟩ := (hlev _ hbs (j + 1)).1 (hF.2.2.1 _ hbs)
  have hy₀Λ : y₀ ∈ Λ := by
    have := Λ.sub_mem hbΛ (hMs hm).1
    simpa using this
  have hfrΛ : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    (hf' (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩) |>.1
  have hth : algebraMap F E S.th⁻¹ • (x + x') ∈ Λ := by
    rw [hte, smul_smul, ← map_mul, inv_mul_cancel₀ (th_ne S), map_one, one_smul]
    exact ht
  obtain ⟨y₁, hy₁Λ, hy₁Y, hm₁⟩ := mof_transport S Λ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))
    (S.fr d Λ) (S.fr' d Λ) (fun b => (n₀⁻¹ * (S.wit d Λ).1) (S.f b))
    (fun b => (n'' * n₀' * (S.wit d Λ).2) (S.f' b)) x x' u
    (fun b => by
      change n₀⁻¹ (S.fr d Λ b) = _
      have h0 : hf L S.Hm (S.fr d Λ b) x = 0 := hp b x hxX
      rw [e1, eich, h0, hf_neg_right]
      simp [Frames.h, sub_eq_add_neg])
    (fun b => by
      change n'' (n₀' (S.fr' d Λ b)) = _
      have h0 : hf L S.Hm (S.fr' d Λ b) x' = 0 := hp' b x' hxX'
      rw [e3 (n₀' (S.fr' d Λ b)) ((hn₀'.2.1 _).2 (hp' b)), e2, eich, h0]
      simp [Frames.h])
    (fun b => hint _ (hfrΛ b) _ huΛ) hth (Submodule.add_mem_sup hx hx') _ hm
  refine ⟨y₀ - y₁, Λ.sub_mem hy₀Λ hy₁Λ, Submodule.sub_mem _ hy₀Y hy₁Y, ?_⟩
  rw [hM₁]
  have h5 : hf L S.Hm x u = 0 := hf_swap_zero hH hux
  have h6 : hf L S.Hm y₀ u = 0 := hf_swap_zero hH (huY y₀ hy₀Y)
  have : y - (y₀ - y₁) = y + hf L S.Hm y u • x - y₀ - S.h (y + hf L S.Hm y u • x - y₀) u • x + y₁ := by
    simp only [Frames.h, hf_sub, hf_add, hf_smul, h5, h6]
    module
  rw [this]
  exact hm₁
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConst
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FamilyVol

theorem relIndex_symm_of_sub {G : Type*} [AddGroup G] {A A' B B' : AddSubgroup G} {β : ℕ} (hβ : β ≠ 0)
    (hA : B ≤ A) (hA' : B' ≤ A') (h : B.relIndex A = β) (h' : B'.relIndex A' = β)
    (hB : B.relIndex B' = B'.relIndex B) (hB0 : B.relIndex B' ≠ 0) :
    A.relIndex A' = A'.relIndex A := by
  have e1 : (B ⊓ B').relIndex A = B'.relIndex B * β := by
    rw [← h, ← AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B A inf_le_left hA,
      AddSubgroup.inf_relIndex_left]
  have e2 : (B ⊓ B').relIndex A' = B.relIndex B' * β := by
    rw [← h', ← AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B' A' inf_le_right hA',
      AddSubgroup.inf_relIndex_right]
  have hle : B ⊓ B' ≤ A ⊓ A' := inf_le_inf hA hA'
  have e3 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') (A ⊓ A') A hle inf_le_left
  have e4 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') (A ⊓ A') A' hle inf_le_right
  rw [AddSubgroup.inf_relIndex_left] at e3
  rw [AddSubgroup.inf_relIndex_right] at e4
  have hne : (B ⊓ B').relIndex (A ⊓ A') ≠ 0 := by
    intro h0
    rw [h0, zero_mul, e2] at e4
    exact mul_ne_zero hB0 hβ e4.symm
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
  rw [e3, e4, e1, e2, hB]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem resQ_ne_zero (ϖ : 𝒪[F]) (h : Irreducible ϖ) : resQ ϖ ≠ 0 := by
  have e : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F] := h.maximalIdeal_eq.symm
  unfold resQ
  rw [e]
  have : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

variable [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem exists_basis (S : Frames L r k) (J : ℕ) :
    ∃ (m : ℕ) (y : Fin m → S.V), LinearIndependent E y ∧
      Submodule.span E (Set.range y) = S.spanTo S.f J ⊔ S.spanTo S.f' J := by
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  let I := {i : Fin (r + 1) // (i : ℕ) < J}
  let φ : I ⊕ I → Fin (r + 1) ⊕ Fin (r + 1) := Sum.map Subtype.val Subtype.val
  have hφ : Function.Injective φ := Subtype.val_injective.sumMap Subtype.val_injective
  let e := (Fintype.equivFin (I ⊕ I)).symm
  refine ⟨_, (Sum.elim S.f S.f' ∘ φ) ∘ e, (hli.comp φ hφ).comp e e.injective, ?_⟩
  rw [e.surjective.range_comp, Frames.spanTo, Frames.spanTo, ← Submodule.span_union]
  congr 1
  ext v
  constructor
  · rintro ⟨i | i, rfl⟩
    · exact Or.inl ⟨i.1, i.2, rfl⟩
    · exact Or.inr ⟨i.1, i.2, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
    · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩

theorem spanTo_mono (S : Frames L r k) (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) :
    S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem relIndex_trace (S : Frames L r k) (J : ℕ) (hJ : J ≤ r + 1) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hl : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J) :
    (S.M d Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup = S.be d Λ := by
  have hM : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hlev := (_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.2.2.2.2.2
  set Y := (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O with hY
  have h1 : (S.sat Λ).toAddSubgroup = (Λ ⊓ Y).toAddSubgroup ⊔ (S.M d Λ).toAddSubgroup := by
    apply le_antisymm
    · intro y hy
      obtain ⟨y₁, hy₁, hm⟩ := (hlev y hy J).1 (hl y hy)
      have hy₁Λ : y₁ ∈ Λ := by
        have := Λ.sub_mem hy.1 (hM hm).1
        simpa using this
      have : y = y₁ + (y - y₁) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup (S := (Λ ⊓ Y).toAddSubgroup) ⟨hy₁Λ, hy₁⟩ hm
    · refine sup_le ?_ hM
      intro y hy
      exact ⟨hy.1, sup_le_sup (spanTo_mono S S.f hJ) (spanTo_mono S S.f' hJ) hy.2⟩
  have h2 : (S.M d Λ ⊓ Y).toAddSubgroup = (S.M d Λ).toAddSubgroup ⊓ (Λ ⊓ Y).toAddSubgroup := by
    ext y
    exact ⟨fun h => ⟨h.1, (hM h.1).1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [h2, AddSubgroup.inf_relIndex_right, Frames.be, h1, AddSubgroup.relIndex_sup_right]

theorem family_vol : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → ∀ Yy : Submodule L.O S.V, (Yy = (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O ∨ Yy = (perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))).restrictScalars L.O) → (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup = (Λ' ⊓ Yy).toAddSubgroup.relIndex (Λ ⊓ Yy).toAddSubgroup ∧ (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup ≠ 0 ∧ (S.M d Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup.relIndex (Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup = β := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF Λ' hT' hF' Yy hYy
  have hJ : (j : ℕ) + 1 ≤ r + 1 := by have := j.2; omega
  have b1 := relIndex_trace S (j + 1) hJ d Λ hT hF.2.2.1
  have b2 := relIndex_trace S (j + 1) hJ d Λ' hT' hF'.2.2.1
  have hβ : β ≠ 0 := by
    obtain ⟨i, -, hi⟩ := (_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.1
    rw [← hF.2.1, hi]
    exact pow_ne_zero _ (resQ_ne_zero _ S.ϖ_irr)
  rw [hF.2.1] at b1
  rw [hF'.2.1] at b2
  obtain ⟨hS, -, hM, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hS', -, hM', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ' hT'
  obtain ⟨v1, v2⟩ := _root_.GlobalTheory.HL.TraceVol.trace_volume L r k S d Λ hT d Λ' hT' (j + 1) _ hJ rfl
  have hY := relIndex_symm_of_sub hβ
    (Submodule.toAddSubgroup_mono (inf_le_inf_right _ (hM.trans inf_le_left)))
    (Submodule.toAddSubgroup_mono (inf_le_inf_right _ (hM'.trans inf_le_left))) b1 b2 v1 v2
  obtain ⟨m, y, hy, hsp⟩ := exists_basis S (j + 1)
  obtain ⟨p1, p2, p3⟩ := _root_.GlobalTheory.HL.VolPerp.vol_perp L S.Hm S.herm Λ Λ' hS hS' m y hy _ _ rfl rfl
  rw [hsp] at p1 p2 p3
  rcases hYy with rfl | rfl
  · exact ⟨hY, p2, b1⟩
  · refine ⟨?_, p1, b1⟩
    rw [← hY] at p3
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero p2) p3

end GlobalTheory.HL.FamilyVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev


open MeasureTheory NumberField IsDedekindDomain Matrix in
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical in
theorem _root_.GlobalTheory.RowLev.intAf_approx_inter_unit_conj : ∀ (I : _root_.Formalism.MainNotions.S.AutInst) (g : ℕ), 1 ≤ g →
    (∀ z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E, ∃ a : 𝓞 I.E, ∃ z' ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E,
      z = _root_.Formalism.UG.inclE (F := I.F) (_root_.Formalism.MainNotions.S.Af I.F) (a : I.E) + (g : (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F)) * z') ∧
    (∀ a : I.E, _root_.Formalism.UG.inclE (F := I.F) (_root_.Formalism.MainNotions.S.Af I.F) a ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E ↔
      a ∈ (algebraMap (𝓞 I.E) I.E).range) ∧
    IsUnit (g : (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F)) ∧
    ∀ z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E, _root_.Formalism.UG.sigR I.cm.sig (_root_.Formalism.MainNotions.S.Af I.F) z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E := by
  intro I g hg
  have hg0 : g ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨b, t, hbt⟩ := _root_.GlobalTheory.RowLev.Inhab.exists_approx (F := I.F) (E := I.E) hg0 ⟨z, hz⟩
    refine ⟨b, t, t.2, ?_⟩
    have h := congrArg Subtype.val hbt
    simpa [_root_.GlobalTheory.RowLev.Inhab.psi] using h
  · intro a
    constructor
    · intro ha
      have hint : IsIntegral ℤ a := _root_.Formalism.UG.P.csGlob_int a ha
      exact ⟨⟨a, hint⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact _root_.Formalism.UG.CS.incl_int b
  · have hF : IsUnit (g : I.F) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hg0)
    simpa using hF.map (algebraMap I.F (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F))
  · intro z hz
    exact _root_.Formalism.UG.P.csDual_sig_mem _ hz

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalLatticeLocalFactorProductPosAndLe
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.MaxLatLam

theorem factor_bounds {q : ℝ} (hq : 2 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    0 < (q ^ n - (-1) ^ n) / (q + 1) ∧ (q ^ n - (-1) ^ n) / (q + 1) ≤ (q ^ 2) ^ ((n : ℝ) / 2) := by
  have h1 : q ≤ q ^ n := le_self_pow₀ (by linarith) (by omega)
  have h2 : (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := neg_one_pow_eq_or ℝ n
  have h3 : (q ^ 2) ^ ((n : ℝ) / 2) = q ^ n := by
    rw [← Real.rpow_natCast q 2, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast q n]
    congr 1
    push_cast
    ring
  refine ⟨div_pos (by rcases h2 with e | e <;> rw [e] <;> linarith) (by linarith), ?_⟩
  rw [h3, div_le_iff₀ (by linarith)]
  rcases h2 with e | e <;> rw [e] <;> nlinarith

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → 1 ≤ Module.finrank K V → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → 0 < lamMax h M ∧ lamMax h M ≤ (discN h M : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hnd hn M hM
  obtain ⟨hfin, hd, -, hP⟩ := GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM
  rw [hd, lamMax, finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin]
  have hq : ∀ P ∈ hfin.toFinset, (2 : ℝ) ≤ (qIn P : ℝ) := fun P hp => by
    exact_mod_cast (hP P (hfin.mem_toFinset.1 hp)).2.1
  refine ⟨Finset.prod_pos fun P hp => (factor_bounds (hq P hp) hn).1, ?_⟩
  rw [Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun P _ => Nat.cast_nonneg _)]
  refine Finset.prod_le_prod₀ (fun P hp => (factor_bounds (hq P hp) hn).1.le) fun P hp => ?_
  rw [(hP P (hfin.mem_toFinset.1 hp)).2.2.1, Nat.cast_pow]
  exact (factor_bounds (hq P hp) hn).2

end GlobalTheory.MaxLatLam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfAdjointIdempotentPosType
section
noncomputable section

namespace GlobalTheory.RowLev.GroupAlgPos

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

variable {Q : Type} [Group Q]

theorem coeff_mul_eq_sum [Fintype Q] (a b : MonoidAlgebra ℂ Q) (q : Q) :
    (a * b).coeff q = ∑ x, a.coeff x * b.coeff (x⁻¹ * q) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]

def adj [Finite Q] (a : MonoidAlgebra ℂ Q) : MonoidAlgebra ℂ Q :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun q => star (a.coeff q⁻¹))

theorem adj_coeff [Finite Q] (a : MonoidAlgebra ℂ Q) (q : Q) : (adj a).coeff q = star (a.coeff q⁻¹) := rfl

theorem adj_mul [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a * b) = adj b * adj a := by
  haveI := Fintype.ofFinite Q
  ext q
  rw [adj_coeff, coeff_mul_eq_sum, coeff_mul_eq_sum, star_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun x => ?_
  simp [adj_coeff, mul_comm, mul_assoc]

theorem adj_adj [Finite Q] (a : MonoidAlgebra ℂ Q) : adj (adj a) = a := by
  ext q; simp [adj_coeff]

theorem adj_sub [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a - b) = adj a - adj b := by
  ext q; simp [adj_coeff]

theorem isSA_iff [Finite Q] (a : MonoidAlgebra ℂ Q) : IsSA a ↔ adj a = a := by
  constructor
  · intro h
    ext q
    rw [adj_coeff, h q, star_star]
  · intro h q
    have := adj_coeff a q⁻¹
    rw [h, inv_inv] at this
    exact this

theorem coeff_mul_adj_one [Fintype Q] (a : MonoidAlgebra ℂ Q) :
    (a * adj a).coeff 1 = ∑ x, a.coeff x * star (a.coeff x) := by
  rw [coeff_mul_eq_sum]
  simp only [adj_coeff, mul_one, inv_inv]

theorem eq_zero_of_coeff_mul_adj [Finite Q] (a : MonoidAlgebra ℂ Q) (h : (a * adj a).coeff 1 = 0) : a = 0 := by
  haveI := Fintype.ofFinite Q
  rw [coeff_mul_adj_one] at h
  ext q
  have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_star_self_nonneg (a.coeff x)).1 h q (Finset.mem_univ _)
  simpa using this

theorem isSA_central [Finite Q] (z : MonoidAlgebra ℂ Q) (hz : z * z = z) (hc : ∀ a, z * a = a * z) : IsSA z := by
  have hs : adj z * adj z = adj z := by rw [← adj_mul, hz]
  have h0 : z - z * adj z = 0 := by
    apply eq_zero_of_coeff_mul_adj
    rw [adj_sub, adj_mul, adj_adj]
    have e1 : z * adj z * adj z = z * adj z := by rw [mul_assoc, hs]
    have e2 : z * (z * adj z) = z * adj z := by rw [← mul_assoc, hz]
    have e3 : z * adj z * (z * adj z) = z * adj z := by
      rw [mul_assoc, ← mul_assoc (adj z), ← hc (adj z), mul_assoc z (adj z), hs, e2]
    rw [sub_mul, mul_sub, mul_sub, e1, e2, e3]; simp
  have h1 : z = z * adj z := sub_eq_zero.1 h0
  rw [isSA_iff]
  conv_lhs => rw [h1, adj_mul, adj_adj]
  exact h1.symm

end GlobalTheory.RowLev.GroupAlgPos
end
end

