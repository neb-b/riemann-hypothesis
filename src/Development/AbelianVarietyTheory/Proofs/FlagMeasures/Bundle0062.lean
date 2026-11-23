module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0025
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexIntegrableShareTopLevelVectors
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.TopLevelShare

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.TopLevelShare.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → 1 ≤ βJ ∧ 1 ≤ β ∧ _root_.GlobalTheory.IdxInt.Nice (S.refB (j + 1) Λ) (_root_.GlobalTheory.IdxInt.ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) ∧ _root_.GlobalTheory.IdxInt.cint (S.refB (j + 1) Λ) (_root_.GlobalTheory.IdxInt.ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) = (βJ : ℂ) / (β : ℂ) := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF
  obtain ⟨-, hbe, hle, ⟨y₀, hy₀, hy₀l⟩, hJ⟩ := hF
  obtain ⟨-, -, hMsat, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, -, -, -, ⟨i, -, hq⟩, -, -, -, -, hlev⟩ := _root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hth : S.th ≠ 0 := (_root_.GlobalTheory.FrameBasic.main L r k S).2.2.2.2.2.1
  set A := S.refB (↑j + 1) Λ with hAdef
  have hA : ∀ b : S.V × S.V, b ∈ A ↔ b.1 ∈ S.spanTo S.f (↑j + 1) ∧ b.2 ∈ S.spanTo S.f' (↑j + 1) ∧ ∃ y ∈ Λ, S.th • y = b.1 + b.2 := by
    intro b
    simp [hAdef, _root_.GlobalTheory.HL.Frames.refB, AddSubgroup.mem_prod, and_assoc]
  have hlevC : ∀ y, S.levC d Λ y = S.lev (S.fr d Λ) (S.fr' d Λ) (S.th • y) := by
    intro y
    simp [_root_.GlobalTheory.HL.Frames.levC]
  have hsat : ∀ y, y ∈ S.sat Λ ↔ y ∈ Λ ∧ y ∈ S.spanTo S.f (r + 1) ⊔ S.spanTo S.f' (r + 1) := by
    intro y
    show y ∈ Λ ⊓ S.ME.restrictScalars L.O ↔ _
    rw [Submodule.mem_inf, Submodule.restrictScalars_mem]
    rfl
  have hbe' : S.be d Λ = (S.M d Λ).toAddSubgroup.relIndex (S.sat Λ).toAddSubgroup := rfl
  have hq0 : S.q ≠ 0 := by
    have hirr := S.ϖ_irr
    show _root_.GlobalTheory.HL.resQ S.ϖ ≠ 0
    unfold _root_.GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr]
    exact (Nat.card_pos (α := IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)).ne'
  have hβ0 : β ≠ 0 := by rw [← hbe, hq]; exact pow_ne_zero _ hq0
  set π : S.V × S.V → S.V := fun b => S.th⁻¹ • (b.1 + b.2) with hπdef
  have hπsmul : ∀ b, S.th • π b = b.1 + b.2 := fun b => smul_inv_smul₀ hth _
  have hπadd : ∀ a b, π (a + b) = π a + π b := by
    intro a b
    simp only [hπdef, Prod.fst_add, Prod.snd_add, ← smul_add, add_add_add_comm]
  have hπsub : ∀ a b, π (a - b) = π a - π b := by
    intro a b
    simp only [hπdef, Prod.fst_sub, Prod.snd_sub, ← smul_sub, sub_add_sub_comm]
  have hπA : ∀ b ∈ A, π b ∈ S.sat Λ := by
    intro b hb
    obtain ⟨h1, h2, y, hy, hyb⟩ := (hA b).1 hb
    have hjr : (↑j + 1 : ℕ) ≤ r + 1 := by omega
    rw [hsat]
    refine ⟨?_, ?_⟩
    · rw [hπdef]; dsimp only; rw [← hyb, inv_smul_smul₀ hth]; exact hy
    · refine Submodule.smul_of_tower_mem _ _ (add_mem ?_ ?_)
      · exact Submodule.mem_sup_left (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f hjr h1)
      · exact Submodule.mem_sup_right (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f' hjr h2)
  have hlevπ : ∀ b : S.V × S.V, S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = S.levC d Λ (π b) := by
    intro b; rw [hlevC, hπsmul]
  have hinv : ∀ y ∈ S.sat Λ, ∀ m ∈ S.M d Λ, S.levC d Λ (y + m) = S.levC d Λ y := by
    intro y hy m hm
    have key : ∀ n : ℕ, S.levC d Λ (y + m) ≤ n ↔ S.levC d Λ y ≤ n := by
      intro n
      rw [hlev _ (add_mem hy (hMsat hm)), hlev _ hy]
      constructor
      · rintro ⟨y₁, h₁, h₂⟩
        exact ⟨y₁, h₁, by simpa [add_sub_right_comm] using sub_mem h₂ hm⟩
      · rintro ⟨y₁, h₁, h₂⟩
        exact ⟨y₁, h₁, by simpa [add_sub_right_comm] using add_mem h₂ hm⟩
    exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)
  set B : AddSubgroup (S.V × S.V) := A ⊓ AddSubgroup.comap (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V) ((S.M d Λ).toAddSubgroup.map (DistribSMul.toAddMonoidHom S.V S.th)) with hBdef
  have hB : ∀ b, b ∈ B ↔ b ∈ A ∧ π b ∈ S.M d Λ := by
    intro b
    rw [hBdef, AddSubgroup.mem_inf]
    refine and_congr_right fun _ => ?_
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, AddMonoidHom.add_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, DistribSMul.toAddMonoidHom_apply, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨m, hm, hmb⟩
      rw [hπdef]; dsimp only; rw [← hmb, inv_smul_smul₀ hth]; exact hm
    · intro h
      exact ⟨π b, h, hπsmul b⟩
  have hsatΛ : ∀ y ∈ S.sat Λ, y ∈ Λ := fun y hy => ((hsat y).1 hy).1
  have hlift : ∀ y ∈ S.sat Λ, ∃ b ∈ A, y - π b ∈ S.M d Λ := by
    intro y hy
    obtain ⟨y₁, hy₁U, hyM⟩ := (hlev y hy (↑j + 1)).1 (hle y hy)
    have hy₁Λ : y₁ ∈ Λ := by simpa using sub_mem (hsatΛ y hy) (hsatΛ _ (hMsat hyM))
    obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := Submodule.mem_sup.1 (Submodule.smul_of_tower_mem _ S.th hy₁U)
    refine ⟨(u₁, u₂), (hA _).2 ⟨hu₁, hu₂, y₁, hy₁Λ, hu.symm⟩, ?_⟩
    have : π (u₁, u₂) = y₁ := by
      rw [hπdef]; dsimp only; rw [hu, inv_smul_smul₀ hth]
    rw [this]; exact hyM
  set K := (S.M d Λ).toAddSubgroup.addSubgroupOf (S.sat Λ).toAddSubgroup with hKdef
  let πA : A →+ (S.sat Λ).toAddSubgroup :=
    { toFun := fun b => ⟨π b, hπA b b.2⟩
      map_zero' := Subtype.ext (by simp [hπdef])
      map_add' := fun a b => Subtype.ext (hπadd a b) }
  let g : A →+ (S.sat Λ).toAddSubgroup ⧸ K := (QuotientAddGroup.mk' K).comp πA
  have hg : ∀ a : A, g a = QuotientAddGroup.mk (⟨π a, hπA a a.2⟩ : (S.sat Λ).toAddSubgroup) := fun a => rfl
  have hsurj : Function.Surjective g := by
    intro c
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨b, hb, hbM⟩ := hlift y hy
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [hg, QuotientAddGroup.eq, hKdef, AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hbM
  have hker : g.ker = B.addSubgroupOf A := by
    ext a
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, hB, hg, QuotientAddGroup.eq_zero_iff, hKdef, AddSubgroup.mem_addSubgroupOf]
    simp
  have hidx : B.relIndex A = β := by
    rw [← hbe, hbe', AddSubgroup.relIndex, AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]
    rfl
  have hidx0 : B.relIndex A ≠ 0 := by rw [hidx]; exact hβ0
  haveI : Finite (A ⧸ B.addSubgroupOf A) := Nat.finite_of_card_ne_zero hidx0
  set φ := _root_.GlobalTheory.IdxInt.ind (fun b : S.V × S.V => b ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = ↑j + 1) with hφdef
  have hφval : ∀ w, φ w = if w ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (w.1 + w.2) = ↑j + 1 then 1 else 0 := by
    intro w
    rw [hφdef]
    unfold _root_.GlobalTheory.IdxInt.ind
    congr
  have hφinv : ∀ w b : S.V × S.V, b ∈ B → φ (w + b) = φ w := by
    intro w b hb
    obtain ⟨hbA, hbM⟩ := (hB b).1 hb
    have key : (w + b ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) ((w + b).1 + (w + b).2) = ↑j + 1) ↔ (w ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (w.1 + w.2) = ↑j + 1) := by
      by_cases hw : w ∈ A
      · rw [hlevπ, hlevπ, hπadd, hinv _ (hπA w hw) _ hbM]
        simp [hw, add_mem hw hbA]
      · have hwb : w + b ∉ A := fun h => hw (by simpa using sub_mem h hbA)
        simp [hw, hwb]
    simp only [hφval, key]
  have hsupp : Function.support φ ⊆ A := by
    intro w hw
    by_contra h
    exact hw (by rw [hφval, if_neg (fun hc => h hc.1)])
  have hfin : ((fun w : S.V × S.V => (w : (S.V × S.V) ⧸ B)) '' Function.support φ).Finite := by
    let h : A ⧸ B.addSubgroupOf A →+ (S.V × S.V) ⧸ B := QuotientAddGroup.map (B.addSubgroupOf A) B A.subtype (fun x hx => hx)
    refine (Set.finite_range h).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨QuotientAddGroup.mk ⟨w, hsupp hw⟩, rfl⟩
  have hfine : _root_.GlobalTheory.IdxInt.Fine A φ B := ⟨inf_le_left, hidx0, hφinv, hfin⟩
  set T : Set ((S.V × S.V) ⧸ B) := {c | Quotient.out c ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) ((Quotient.out c).1 + (Quotient.out c).2) = ↑j + 1} with hTdef
  have hTsub : T ⊆ (fun w : S.V × S.V => (w : (S.V × S.V) ⧸ B)) '' Function.support φ := by
    intro c hc
    refine ⟨Quotient.out c, ?_, QuotientAddGroup.out_eq' c⟩
    simp [Function.mem_support, hφval, hc.1, hc.2]
  have hTfin : T.Finite := hfin.subset hTsub
  have hsum : ∑ᶠ c : (S.V × S.V) ⧸ B, φ (Quotient.out c) = (T.ncard : ℂ) := by
    calc ∑ᶠ c : (S.V × S.V) ⧸ B, φ (Quotient.out c) = ∑ᶠ c ∈ T, (1 : ℂ) := by
          rw [finsum_mem_def]
          refine finsum_congr fun c => ?_
          simp only [hφval, Set.indicator, hTdef, Set.mem_setOf_eq]
      _ = T.ncard := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_const, nsmul_eq_mul, mul_one, Set.ncard_eq_toFinset_card T hTfin]
  have hout : ∀ b : S.V × S.V, Quotient.out (b : (S.V × S.V) ⧸ B) - b ∈ B := by
    intro b
    have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (b : (S.V × S.V) ⧸ B))
    rw [neg_add_eq_sub, ← neg_sub] at h
    simpa using B.neg_mem h
  set fC : (S.V × S.V) ⧸ B → Set S.V := fun c => {x | x - π (Quotient.out c) ∈ S.M d Λ} with hfCdef
  have himage : fC '' T = {C | ∃ y ∈ S.sat Λ, S.levC d Λ y = ↑j + 1 ∧ C = {x | x - y ∈ S.M d Λ}} := by
    ext C
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨π (Quotient.out c), hπA _ hc.1, (hlevπ _).symm.trans hc.2, rfl⟩
    · rintro ⟨y, hy, hyl, rfl⟩
      obtain ⟨b, hb, hbM⟩ := hlift y hy
      obtain ⟨h₁, h₂⟩ := (hB _).1 (hout b)
      have hoA : Quotient.out (b : (S.V × S.V) ⧸ B) ∈ A := by simpa using add_mem h₁ hb
      rw [hπsub] at h₂
      have hyo : y - π (Quotient.out (b : (S.V × S.V) ⧸ B)) ∈ S.M d Λ := by
        have := sub_mem hbM h₂
        rwa [sub_sub_sub_cancel_right] at this
      refine ⟨(b : (S.V × S.V) ⧸ B), ⟨hoA, ?_⟩, ?_⟩
      · have := hinv _ (hπA _ hoA) _ hyo
        rw [add_sub_cancel] at this
        rw [hlevπ, ← this, hyl]
      · ext x
        simp only [hfCdef, Set.mem_setOf_eq]
        constructor
        · intro hx
          have := sub_mem hx hyo
          rwa [sub_sub_sub_cancel_right] at this
        · intro hx
          have := add_mem hx hyo
          rwa [sub_add_sub_cancel] at this
  have hinj : Set.InjOn fC T := by
    intro c₁ hc₁ c₂ hc₂ heq
    have hmem : π (Quotient.out c₁) ∈ fC c₁ := by
      show π (Quotient.out c₁) - π (Quotient.out c₁) ∈ S.M d Λ
      rw [sub_self]; exact zero_mem _
    rw [heq] at hmem
    have hB₁₂ : Quotient.out c₁ - Quotient.out c₂ ∈ B :=
      (hB _).2 ⟨sub_mem hc₁.1 hc₂.1, by rw [hπsub]; exact hmem⟩
    rw [← QuotientAddGroup.out_eq' c₁, ← QuotientAddGroup.out_eq' c₂, QuotientAddGroup.eq, neg_add_eq_sub, ← neg_sub]
    exact B.neg_mem hB₁₂
  have hcount : T.ncard = βJ := by
    rw [← hJ]
    unfold _root_.GlobalTheory.HL.Frames.nLev
    rw [← himage, Set.InjOn.ncard_image hinj]
  have hTne : T.Nonempty := by
    have : (fC '' T).Nonempty := by
      rw [himage]; exact ⟨_, y₀, hy₀, hy₀l, rfl⟩
    exact Set.image_nonempty.1 this
  refine ⟨?_, Nat.one_le_iff_ne_zero.2 hβ0, ⟨B, hfine⟩, ?_⟩
  · rw [← hcount]
    exact (Set.ncard_pos hTfin).2 hTne
  · rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B φ hfine, hsum, hcount, hidx]

end GlobalTheory.TopLevelShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopCountExponentBound
section
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

theorem loop_count_exponent_bound : ∀ C₁ Ad : ℝ, 1 ≤ C₁ → ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C ≥ C₀, ∀ (s r f : ℕ) (De NT HH : ℝ), 1 ≤ s → 1 ≤ f → 1 ≤ De → 1 ≤ NT → 1 ≤ HH → De ≤ HH ^ Ad → NT ≤ HH → De ^ (4 + Real.logb 2 (2 * f)) * (De * NT) ^ (C₁ * s + C₁ * Real.log f) * (9 ^ (s * f) * (HH ^ (max Ad 3)) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2 ≤ HH ^ (C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + Real.logb 2 (2 * f))) * (C * s * f) ^ (6 * s * f) := by
  intro C₁ Ad hC₁
  have ha3 : (3 : ℝ) ≤ max Ad 3 := le_max_right _ _
  have haA : Ad ≤ max Ad 3 := le_max_left _ _
  generalize max Ad 3 = a at ha3 haA ⊢
  have hb : (0 : ℝ) ≤ (a + 1) * C₁ := by positivity
  refine ⟨5 * a + (a + 1) * C₁, by linarith, ?_⟩
  intro C hC s r f De NT HH hs hf hDe hNT hHH hDA hN
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hH0 : 0 < HH := by linarith
  have hlf0 : 0 ≤ Real.log f := Real.log_nonneg hf'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlfL : Real.log f ≤ Real.logb 2 (2 * f) := by
    rw [Real.logb, le_div_iff₀ hl2, Real.log_mul (by norm_num) (by linarith)]
    nlinarith
  have hL0 : 0 ≤ Real.logb 2 (2 * (f : ℝ)) := le_trans hlf0 hlfL
  generalize Real.logb 2 (2 * (f : ℝ)) = L at hlfL hL0 ⊢
  generalize Real.log (f : ℝ) = l at hlfL hlf0 ⊢
  have hDa : De ≤ HH ^ a := hDA.trans (Real.rpow_le_rpow_of_exponent_le hHH haA)
  have hDN : De * NT ≤ HH ^ (a + 1) := by
    rw [Real.rpow_add hH0, Real.rpow_one]
    exact mul_le_mul hDa hN (by linarith) (by positivity)
  have h1 : De ^ (4 + L) ≤ HH ^ (a * (4 + L)) := by
    rw [Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow (by linarith) hDa (by linarith)
  have h2 : (De * NT) ^ (C₁ * s + C₁ * l) ≤ HH ^ ((a + 1) * (C₁ * s + C₁ * l)) := by
    rw [Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow (by positivity) hDN (by positivity)
  have h3 : ((HH ^ a) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2
      = HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]
    congr 1
    push_cast
    ring
  have hC3 : (3 : ℝ) ≤ C * s * f := by
    have h0 : (3 : ℝ) ≤ C := by linarith
    have : (3 : ℝ) ≤ C * s := by nlinarith
    nlinarith
  have h4 : ((9 : ℝ) ^ (s * f)) ^ 2 ≤ (C * s * f) ^ (6 * s * f) := by
    calc ((9 : ℝ) ^ (s * f)) ^ 2 = 3 ^ (4 * (s * f)) := by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
          congr 1; ring
      _ ≤ 3 ^ (6 * s * f) := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le (s * f)])
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hC3 _
  have hexp : a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l)
      + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))
      ≤ C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + L) := by
    set P : ℝ := ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) with hP
    have hsr : (0 : ℝ) ≤ s * r := by positivity
    have hrr : (0 : ℝ) ≤ r ^ 2 := by positivity
    have e1 : (s : ℝ) ≤ P := by rw [hP]; nlinarith
    have e2 : 2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2) ≤ 5 * P := by rw [hP]; nlinarith
    have hP0 : 0 ≤ P := by linarith
    have e3 : (5 * a + (a + 1) * C₁) * P ≤ C * P := mul_le_mul_of_nonneg_right hC hP0
    have e4 : (5 * a + (a + 1) * C₁) * (1 + L) ≤ C * (1 + L) :=
      mul_le_mul_of_nonneg_right hC (by linarith)
    have e5 : (a + 1) * C₁ * s ≤ (a + 1) * C₁ * P := mul_le_mul_of_nonneg_left e1 hb
    have e6 : (a + 1) * C₁ * l ≤ (a + 1) * C₁ * (1 + L) := mul_le_mul_of_nonneg_left (by linarith) hb
    have e7 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ a by linarith)
    have e8 : a * (4 + L) ≤ a * (5 * (1 + L)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e9 : C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) = C * P := by rw [hP]; ring
    rw [e9]
    clear_value P
    linear_combination e3 + e4 + e5 + e6 + e7 + e8
  rw [mul_pow, h3]
  calc _ ≤ HH ^ (a * (4 + L)) * HH ^ ((a + 1) * (C₁ * s + C₁ * l)) *
        ((C * s * f) ^ (6 * s * f) * HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2)))) := by
        gcongr
    _ = HH ^ (a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l)
      + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))) * (C * s * f) ^ (6 * s * f) := by
        rw [Real.rpow_add hH0, Real.rpow_add hH0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hHH hexp) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIntegersLocalisationIffSumCmData
section
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_disc_notMem (hc : Formalism.BasicNotions.CMData F E) (p : HeightOneSpectrum (𝓞 F)) :
    ∃ (θ t : 𝓞 E) (d : 𝓞 F), (t : E) = star (θ : E) ∧ d ∉ p.asIdeal ∧
      algebraMap F E (d : F) = ((θ : E) - (t : E)) ^ 2 := by
  haveI := p.isMaximal
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) p.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
      exact bot_le)
  obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P hP
  have ht' : (t : E) = star (θ : E) := ht
  obtain ⟨d0, hd0⟩ := (hc.fixed (((θ : E) - (t : E)) ^ 2)).1 (by
    rw [ht', star_pow, star_sub, star_star]; ring)
  have hint : IsIntegral ℤ d0 := by
    have h1 : IsIntegral ℤ (algebraMap F E d0) := by
      rw [hd0]
      exact (θ.isIntegral_coe.sub t.isIntegral_coe).pow 2
    exact (isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom) (algebraMap F E).injective).1 h1
  refine ⟨θ, t, ⟨d0, hint⟩, ht', ?_, hd0⟩
  intro hd
  rw [← hPp] at hd
  replace hd := Ideal.mem_comap.1 hd
  have : algebraMap (𝓞 F) (𝓞 E) ⟨d0, hint⟩ = (θ - t) ^ 2 := by
    apply RingOfIntegers.ext
    simp only [map_pow, map_sub]
    exact hd0
  rw [this] at hd
  exact hθ (hP.isPrime.mem_of_pow_mem 2 hd)

theorem exists_coord (hc : Formalism.BasicNotions.CMData F E) (θ : E) (hθ : θ - star θ ≠ 0) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ := by
  have hθ' : star θ - θ ≠ 0 := fun h => hθ (by rw [← neg_sub, h, neg_zero])
  obtain ⟨b, hb⟩ := (hc.fixed ((x - star x) / (θ - star θ))).1 (by
    rw [star_div₀, star_sub, star_sub, star_star, star_star]; field_simp; ring)
  obtain ⟨a, ha⟩ := (hc.fixed (x - (x - star x) / (θ - star θ) * θ)).1 (by
    rw [star_sub, star_mul, star_div₀, star_sub, star_sub, star_star, star_star]; field_simp; ring)
  exact ⟨a, b, by rw [ha, hb]; ring⟩

omit [StarRing E] in
theorem isIntegral_ιE {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)
    (x : 𝓞 E) : IsIntegral 𝒪[A.Fp] (A.ιE (x : E)) :=
  (x.isIntegral_coe.map A.ιE.toIntAlgHom).tower_top

omit [StarRing E] in
theorem mem_integer_of_isIntegral {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) (a : A.Fp) (h : IsIntegral 𝒪[A.Fp] (algebraMap A.Fp A.Ep a)) :
    a ∈ 𝒪[A.Fp] := by
  haveI : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)
  have h1 : IsIntegral 𝒪[A.Fp] a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[A.Fp] A.Fp A.Ep)
      (algebraMap A.Fp A.Ep).injective).1 h
  exact (Valuation.integer.integers (valuation A.Fp)).mem_of_integral h1

omit [StarRing E] in
theorem valuation_ιF_eq_one {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) (d : 𝓞 F) (hd : d ∉ p.asIdeal) :
    valuation A.Fp (A.ιF (d : F)) = 1 := by
  have h : p.valuation F (d : F) = 1 := (p.valuation_eq_one_iff_notMem (K := F)).2 hd
  have h1 := (A.val (d : F) 1).2 (by rw [h, map_one])
  have h2 := (A.val 1 (d : F)).2 (by rw [h, map_one])
  rw [Valuation.Compatible.vle_iff_le (v := valuation A.Fp)] at h1 h2
  simp only [map_one] at h1 h2
  exact le_antisymm h1 h2

theorem mem_O_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), ∀ y : A.Ep, y ∈ A.O ↔ ∃ (n : ℕ) (c : Fin n → 𝒪[A.Fp]) (x : Fin n → 𝓞 E), y = ∑ i, algebraMap A.Fp A.Ep (c i : A.Fp) * A.ιE (x i : E) := by
  intro F E _ _ _ _ _ _ hc sig hsig p A y
  constructor
  · intro hy
    rw [A.O_def] at hy
    obtain ⟨θ, t, d, ht, hd, hdisc⟩ := exists_disc_notMem hc p
    have hv := valuation_ιF_eq_one A d hd
    have hne : (θ : E) - star (θ : E) ≠ 0 := by
      intro h
      rw [ht, h] at hdisc
      have : d = 0 := by
        apply RingOfIntegers.ext
        simpa using hdisc
      exact hd (this ▸ p.asIdeal.zero_mem)
    have hco : ∀ z : A.Ep, ∃ a b : A.Fp,
        z = algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (θ : E) := by
      intro z
      have hz : z ∈ Submodule.span A.Fp (Set.range A.ιE) := by rw [A.span]; trivial
      induction hz using Submodule.span_induction with
      | mem _ hx =>
        obtain ⟨x, rfl⟩ := hx
        obtain ⟨a, b, rfl⟩ := exists_coord hc θ hne x
        exact ⟨A.ιF a, A.ιF b, by rw [map_add (f := _), map_mul, A.compat, A.compat]⟩
      | zero => exact ⟨0, 0, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨a, b, rfl⟩ := h1
        obtain ⟨a', b', rfl⟩ := h2
        exact ⟨a + a', b + b', by rw [map_add (f := _), map_add (f := _)]; ring⟩
      | smul c _ _ h1 =>
        obtain ⟨a, b, rfl⟩ := h1
        exact ⟨c * a, c * b, by rw [map_mul, map_mul, Algebra.smul_def]; ring⟩
    obtain ⟨a, b, rfl⟩ := hco y
    have hcj := hy.map (A.cj.toAlgHom.restrictScalars 𝒪[A.Fp])
    have hcj' : IsIntegral 𝒪[A.Fp]
        (algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (t : E)) := by
      have e : A.cj (algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (θ : E)) =
          algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (t : E) := by
        rw [map_add (f := _), map_mul, A.cj.commutes, A.cj.commutes, A.cj_ιE, hsig, ht]
      rw [← e]; exact hcj
    have hbd : b * A.ιF (d : F) ∈ 𝒪[A.Fp] := by
      apply mem_integer_of_isIntegral A
      have := (hy.sub hcj').mul ((isIntegral_ιE A θ).sub (isIntegral_ιE A t))
      convert this using 1
      rw [map_mul, ← A.compat, hdisc, map_pow, map_sub]; ring
    have hb : b ∈ 𝒪[A.Fp] := by
      rw [Valuation.mem_integer_iff] at hbd ⊢
      rwa [map_mul, hv, mul_one] at hbd
    have hbI : IsIntegral 𝒪[A.Fp] (algebraMap A.Fp A.Ep b) :=
      isIntegral_algebraMap (R := 𝒪[A.Fp]) (x := ⟨b, hb⟩)
    have ha : a ∈ 𝒪[A.Fp] := by
      apply mem_integer_of_isIntegral A
      have := hy.sub (hbI.mul (isIntegral_ιE A θ))
      simpa using this
    exact ⟨2, ![⟨a, ha⟩, ⟨b, hb⟩], ![1, θ], by simp [Fin.sum_univ_two]⟩
  · rintro ⟨n, c, x, rfl⟩
    rw [A.O_def]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (isIntegral_ιE A _)
    exact isIntegral_algebraMap (R := 𝒪[A.Fp]) (x := c i)

end GlobalTheory.LocSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerCommensurableInvVolumeSmulComplement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem Frames.stab_commensurable_invVol_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ Λ : Submodule L.O S.V, IsLat L Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.complementReferenceCompactSubgroup ≠ 0 ∧ ∀ h ∈ S.H0, invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV (h • Λ)) = invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV Λ)) ∧ ∀ d Λ, S.IsTerm d Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV d) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV d).relIndex S.complementReferenceCompactSubgroup ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  obtain ⟨x, hdet, hspan, hH0, hstd, -⟩ := _root_.GlobalTheory.HL.FrameTuple.main L r k S
  set Λs : Submodule L.O S.V := Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V)) with hΛs
  have hK : S.complementReferenceCompactSubgroup = S.H0 ⊓ MulAction.stabilizer S.GLV Λs := rfl
  have comm : ∀ Λ Λ' : Submodule L.O S.V, IsLat L Λ → IsLat L Λ' →
      (S.H0 ⊓ MulAction.stabilizer S.GLV Λ').relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 :=
    fun Λ Λ' hΛ hΛ' => (_root_.GlobalTheory.LatComm.stab_commensurable L Λ Λ' hΛ hΛ' S.H0).1
  have latPart : ∀ Λ : Submodule L.O S.V, IsLat L Λ →
      S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧
        (S.H0 ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.complementReferenceCompactSubgroup ≠ 0 := by
    intro Λ hΛ
    rw [hK]
    exact ⟨comm Λ Λs hΛ hstd, comm Λs Λ hstd hΛ⟩
  refine ⟨fun Λ hΛ => ⟨(latPart Λ hΛ).1, (latPart Λ hΛ).2, ?_⟩, ?_⟩
  · intro h hh
    have hfix : S.H0 = fixG L S.Hm (Submodule.span E (Set.range x)) := by rw [hspan]; exact hH0
    have hh' : h ∈ fixG L S.Hm (Submodule.span E (Set.range x)) := hfix ▸ hh
    have key := _root_.GlobalTheory.HL.Unimod.unimodular L S.Hm S.herm (2 * r + 2) x hdet Λs Λ hstd hΛ h hh'
    rw [hK, hfix]
    exact key
  · intro d Λ hT
    have hΛ : IsLat L Λ := (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1.1
    obtain ⟨hlo, Λ₂, hΛ₂, hhi⟩ := _root_.GlobalTheory.HL.DatumStab.main L r k S d Λ hT
    refine ⟨fun h0 => (latPart Λ₂ hΛ₂).1 (Subgroup.relIndex_eq_zero_of_le_right hhi h0),
      fun h0 => (latPart Λ hΛ).2 (Subgroup.relIndex_eq_zero_of_le_left hlo h0)⟩

end GlobalTheory.HL
end

