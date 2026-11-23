module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCutoffOfAddCharTranslationInvariantFunctio
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.CharCutoff

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dot_eq_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (R : kˣ) {t y : n → k} (ht : t ∈ box n (c * R⁻¹)) (hy : y ∈ box n R) : ψ (t ⬝ᵥ y) = 1 := by
  apply h.eq_one
  show valuation k (∑ i, t i * y i) ≤ valuation k (c : k)
  refine Valuation.map_sum_le (valuation k) fun i _ => ?_
  have h2 : valuation k (t i * y i) ≤ valuation k (((c * R⁻¹ : kˣ) : k) * R) := by
    rw [map_mul, map_mul]
    exact mul_le_mul' (ht i trivial) (hy i trivial)
  rwa [← Units.val_mul, inv_mul_cancel_right] at h2

theorem exists_dot_ne_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s : kˣ) {y : n → k} (hy : y ∉ box n s) : ∃ b ∈ box n (c * s⁻¹), ψ (b ⬝ᵥ y) ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, y i ∉ cball s := by
    by_contra hne
    push_neg at hne
    exact hy fun i _ => hne i
  have hcs : c * (c * s⁻¹)⁻¹ = s := by
    rw [_root_.mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one (c * s⁻¹) (x := y i) (by rwa [hcs])
  refine ⟨Pi.single i t, fun j _ => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  · rwa [single_dotProduct]

theorem sum_char {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s R : kˣ) (S : Finset (n → k)) (hS : ∀ b ∈ S, b ∈ box n (c * s⁻¹))
    (hU : ∀ a ∈ box n (c * s⁻¹), ∃! b, b ∈ S ∧ a - b ∈ box n (c * R⁻¹)) {y : n → k}
    (hy : y ∈ box n R) :
    ∑ b ∈ S, (ψ (b ⬝ᵥ y) : ℂ) = (box n s).indicator (fun _ => (1 : ℂ)) y * S.card := by
  by_cases hys : y ∈ box n s
  · rw [Set.indicator_of_mem hys, one_mul]
    rw [Finset.sum_congr rfl fun b hb => by rw [dot_eq_one h s (hS b hb) hys, Circle.coe_one]]
    simp
  · rw [Set.indicator_of_notMem hys, zero_mul]
    obtain ⟨a, ha, hne⟩ := exists_dot_ne_one h s hys
    have key := _root_.GlobalTheory.CosetSumShift.sum_shift k n (c * R⁻¹) (c * s⁻¹) S hS hU (fun b => (ψ (b ⬝ᵥ y) : ℂ))
      (fun t ht z => by
        rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dot_eq_one h R ht hy,
          Circle.coe_one, mul_one]) a ha
    simp only [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, ← Finset.mul_sum] at key
    have h3 : (ψ (a ⬝ᵥ y) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
    refine (mul_eq_zero.mp ?_).resolve_left h3
    rw [sub_mul, key, one_mul, sub_self]

theorem exists_cutoff_of_char_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (s : kˣ), ∃ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x, Φ'.1 x = (box I₁ s).indicator (fun _ => (1 : ℂ)) x.2.1 * Φ.1 x) ∧ l Φ = l Φ' := by
  intro k _ _ _ _ ψ hψ h1 I₀ I₁ I₂ _ _ _ M _ _ l hl Φ s
  haveI := t2Space k
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hK : IsCompact ((fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => x.2.1) '' tsupport Φ.1) :=
    Φ.2.2.image (by fun_prop)
  obtain ⟨R, hsR, hKR⟩ := _root_.GlobalTheory.exists_box_superset_of_isCompact k I₁ _ hK s
  have hvr : valuation k ((c * R⁻¹ : kˣ) : k) ≤ valuation k ((c * s⁻¹ : kˣ) : k) := by
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    exact mul_le_mul' le_rfl (inv_anti₀ (by simp [zero_lt_iff]) hsR)
  obtain ⟨S, hS, hU⟩ := _root_.GlobalTheory.BoxReps.exists_finset_box_reps k I₁ (c * R⁻¹) (c * s⁻¹) hvr
  have hmem : ∀ b : I₁ → k,
      (fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) ∈
        SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b => by
    have hcont : Continuous fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => b ⬝ᵥ x.2.1 :=
      continuous_const.dotProduct (continuous_fst.comp continuous_snd)
    have h2 : IsLocallyConstant fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => (ψ (b ⬝ᵥ x.2.1) : ℂ) :=
      (IsLocallyConstant.comp_continuous hc.isLocallyConstant hcont).comp (fun z : Circle => (z : ℂ))
    exact ⟨IsLocallyConstant.mul h2 Φ.2.1, Φ.2.2.mul_left⟩
  let Φb : (I₁ → k) → SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b => ⟨_, hmem b⟩
  have hlb : ∀ b, l (Φb b) = l Φ := fun b => hl b Φ (Φb b) (fun x => rfl)
  have h0 : (0 : I₁ → k) ∈ box I₁ (c * s⁻¹) := fun i _ => by simp [cball]
  obtain ⟨b0, ⟨hb0, _⟩, _⟩ := hU 0 h0
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨b0, hb0⟩).ne'
  refine ⟨(S.card : ℂ)⁻¹ • ∑ b ∈ S, Φb b, fun x => ?_, ?_⟩
  · simp only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    show (S.card : ℂ)⁻¹ * ∑ b ∈ S, (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x = _
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport Φ.1
    · rw [sum_char hc s R S hS hU (hKR ⟨x, hx, rfl⟩), ← mul_assoc, mul_comm ((S.card : ℂ)⁻¹),
        mul_inv_cancel_right₀ hcard]
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_smul, map_sum, Finset.sum_congr rfl fun b _ => hlb b, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end GlobalTheory.CharCutoff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharOfOneRowFirstBlock
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.StepData

theorem det_eq_one_of_one_row {k n : Type*} [Field k] [Fintype n] [DecidableEq n] (M : Matrix n n k) (i : n)
    (h : ∀ a b, a ≠ i → M a b = (1 : Matrix n n k) a b) (hii : M i i = 1) : M.det = 1 := by
  have e : M = 1 + replicateCol Unit (Pi.single i (1 : k)) * replicateRow Unit (M i - Pi.single i (1 : k)) := by
    ext a b
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = a
      · subst hb; simp [Matrix.mul_apply, hii]
      · simp [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, hb, Ne.symm hb]
    · simp [Matrix.mul_apply, h a b ha, Pi.single_apply, ha]
  rw [e, det_one_add_replicateCol_mul_replicateRow]
  simp [hii]

theorem iter_lam_one_row (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum (k := k) (a := r))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (r₀ : r) : ∀ (h : (P.iter t μ hμ j).J),
    (∀ a b, a ≠ Sum.inl r₀ → (h : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b) →
    (h : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 →
    ∃ g : P.J, (g : GL r k).val = (h : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧
      (P.iter t μ hμ j).lam h = P.lam g := by
  induction j with
  | zero =>
    intro h _ _
    exact ⟨⟨(reGL (ixZero r t)).symm h, h.2⟩, rfl, rfl⟩
  | succ j ih =>
    intro h h1 h2
    set Q := P.iter t μ hμ j with hQ
    let h' : Q.stepJ t := ⟨(reGL (ixSucc r t j)).symm h, h.2⟩
    have eh' : (h' : GL (Ix r t j ⊕ t) k).val = (h : GL (Ix r t (j + 1)) k).val.submatrix (ixSucc r t j) (ixSucc r t j) := rfl
    let c := Q.corner h'
    have ec : ∀ a b, (c : GL (Ix r t j) k).val a b =
        (h : GL (Ix r t (j + 1)) k).val (ixSucc r t j (.inl a)) (ixSucc r t j (.inl b)) := by
      intro a b; rw [Q.corner_val]; rfl
    have hne : ∀ a, a ≠ Sum.inl r₀ → ixSucc r t j (.inl a) ≠ Sum.inl r₀ := by
      intro a ha e; apply ha
      have : (Sum.inl a : Ix r t j ⊕ t) = Sum.inl (Sum.inl r₀) :=
        (ixSucc r t j).injective (e.trans rfl)
      exact Sum.inl_injective this
    have c1 : ∀ a b, a ≠ Sum.inl r₀ → (c : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b := by
      intro a b ha
      rw [ec, h1 _ _ (hne a ha), Matrix.one_apply, Matrix.one_apply]
      simp [(ixSucc r t j).injective.eq_iff]
    have c2 : (c : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 := by rw [ec]; exact h2
    obtain ⟨g, hg, hl⟩ := ih c c1 c2
    refine ⟨g, ?_, ?_⟩
    · rw [hg]; ext x y; exact ec _ _
    · have d1 : Matrix.GeneralLinearGroup.det (c : GL (Ix r t j) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]; exact det_eq_one_of_one_row _ _ c1 c2)
      have d2 : Matrix.GeneralLinearGroup.det (h' : GL (Ix r t j ⊕ t) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, eh', det_submatrix_equiv_self]
        exact det_eq_one_of_one_row _ _ h1 h2)
      have e0 : (P.iter t μ hμ (j + 1)).lam h = (Q.step t (μ (j + 1)) (hμ _)).lam h' := rfl
      rw [e0, Q.step_lam _ _ h' c (Q.corner_val h'), ← hl, d1, d2]
      simp

end GlobalTheory.StepData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearWeilActionSupportAndPeriodIntegral
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.StepData

theorem om_support_period : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (i : ℕ)
    (μ : kˣ →* ℂˣ) (Φ : Matrix B A k → ℂ), (∀ x, Φ x ≠ 0 → IntM x) → (∀ x y, MaxM y → Φ (x + y) = Φ x) →
    ∀ (g : GL A k) (g' : GL B k), IntM (g⁻¹ : GL A k).val → IntM ((ϖ : k) ^ i • g.val) →
      IntM (g'⁻¹ : GL B k).val → IntM ((ϖ : k) ^ (i + 1) • g'.val) →
    (∀ x, om μ g g' Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ (i + 1))⁻¹ : kˣ) : k)) ∧
    (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ (i + 1))) → om μ g g' Φ (x + y) = om μ g g' Φ x) := by
  intro k _ _ _ _ A B _ _ _ _ ϖ hϖ i μ Φ hsupp hper g g' hg hgi hg' hg'i
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  have hvp : valuation k ((ϖ : k) ^ (i + 1)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ hϖ0
  constructor
  · intro x hx r s
    have hΦ : Φ ((g'⁻¹ : GL B k).val * x * g.val) ≠ 0 := by
      intro h0; apply hx; simp only [om, h0, mul_zero]
    have hz := hsupp _ hΦ
    have hx' : (ϖ : k) ^ (i + 1) • x = ((ϖ : k) ^ (i + 1) • g'.val) * ((g'⁻¹ : GL B k).val * x * g.val) *
        (g⁻¹ : GL A k).val := by
      rw [Matrix.smul_mul, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    have hint : IntM ((ϖ : k) ^ (i + 1) • x) := by rw [hx']; exact (hg'i.mul hz).mul hg
    have h1 : valuation k ((ϖ : k) ^ (i + 1) * x r s) ≤ 1 := hint r s
    rw [map_mul] at h1
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀]
    calc valuation k (x r s) = (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * (valuation k ((ϖ : k) ^ (i + 1)) * valuation k (x r s)) := by
          rw [inv_mul_cancel_left₀ hvp]
      _ ≤ (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  · intro x y hy
    have hy' : IntM (((ϖ : k) ^ (i + 1))⁻¹ • y) := fun r s => by
      show valuation k (((ϖ : k) ^ (i + 1))⁻¹ * y r s) ≤ 1
      rw [map_mul, map_inv₀]
      calc _ ≤ (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * valuation k ((ϖ : k) ^ (i + 1)) := by gcongr; exact hy r s
        _ = 1 := inv_mul_cancel₀ hvp
    have hc : (ϖ : k) * (ϖ : k) ^ i * ((ϖ : k) ^ (i + 1))⁻¹ = 1 := by
      rw [pow_succ]; field_simp
    have heq : (g'⁻¹ : GL B k).val * y * g.val = (ϖ : k) • ((g'⁻¹ : GL B k).val * (((ϖ : k) ^ (i + 1))⁻¹ • y) * ((ϖ : k) ^ i • g.val)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul, hc, one_smul]
    have hM : IntM ((g'⁻¹ : GL B k).val * (((ϖ : k) ^ (i + 1))⁻¹ • y) * ((ϖ : k) ^ i • g.val)) :=
      (hg'.mul hy').mul hgi
    have hmax : MaxM ((g'⁻¹ : GL B k).val * y * g.val) := by
      rw [heq]
      intro r s
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hϖ (hM r s)
    simp only [om, Matrix.mul_add, Matrix.add_mul, hper _ _ hmax]

end GlobalTheory.StepData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChainLastTwoStepsRootOfUnity
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LevelLaw

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : Type} [Fintype n] [DecidableEq n]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n : Type} [Fintype n] [DecidableEq n] in
private theorem reGL_mem_KO_of_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) {g : GL a k} (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k a) :
    _root_.GlobalTheory.StepData.reGL e g ∈ _root_.GlobalTheory.SplitWeil.KO k b := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv, _root_.GlobalTheory.StepData.reGL_val, _root_.GlobalTheory.StepData.reGL_val]
  obtain ⟨h1, h2⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff _).mp hg
  exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

open MeasureTheory ValuativeRel Matrix in
private theorem exists_pos_pow_eq_one_of_isTame_of_valuation_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {δ : kˣ →* ℂˣ} (hδ : _root_.GlobalTheory.SplitWeil.IsTame δ) {u : kˣ} (hu : valuation k (u : k) = 1) : ∃ n : ℕ, 0 < n ∧ δ u ^ n = 1 := by
  classical
  have hO := Valuation.integer.integers (valuation k)
  let x : 𝒪[k] := ⟨u, by rw [Valuation.mem_integer_iff, hu]⟩
  have hx : IsUnit x := hO.isUnit_iff_valuation_eq_one.mpr hu
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  have hr : IsLocalRing.residue 𝒪[k] x ≠ 0 := (RingHom.isUnit_map _ hx).ne_zero
  have hq : 1 < Fintype.card (IsLocalRing.ResidueField 𝒪[k]) := Fintype.one_lt_card
  refine ⟨Fintype.card (IsLocalRing.ResidueField 𝒪[k]) - 1, by omega, ?_⟩
  have hmem : x ^ (Fintype.card (IsLocalRing.ResidueField 𝒪[k]) - 1) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  have hnu := mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
  have hlt := lt_of_le_of_ne (hO.map_le_one _) (mt hO.isUnit_iff_valuation_eq_one.mpr hnu)
  rw [← map_pow]
  apply hδ
  refine lt_of_eq_of_lt ?_ hlt
  simp [x]
  rfl

open MeasureTheory ValuativeRel Matrix in
private theorem hasTypes_apply_mul_left_of_mem_J_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {μ : kˣ →* ℂˣ} {P : _root_.GlobalTheory.StepData.Level (GL a k)} {Q : _root_.GlobalTheory.StepData.Level (GL b k)} {Φ : Matrix b a k → ℂ} (hΦ : _root_.GlobalTheory.StepData.HasTypes μ P Q Φ) {g : GL b k} (hg : g ∈ Q.J) (hgi : g ∈ _root_.GlobalTheory.SplitWeil.KO k b) (B : Matrix b a k) :
    Φ (g.val * B) = ((Q.lam ⟨g, hg⟩ : ℂ) * ((μ (GeneralLinearGroup.det g) : ℂ))⁻¹) * Φ B := by
  have key := congrFun (hΦ.2 ⟨g⁻¹, inv_mem hg⟩) B
  have hn : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g⁻¹) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO (inv_mem hgi))
  have hl : Q.lam ⟨g⁻¹, inv_mem hg⟩ = (Q.lam ⟨g, hg⟩)⁻¹ := map_inv Q.lam ⟨g, hg⟩
  rw [map_inv] at hn
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, Units.smul_def, inv_inv, Matrix.mul_one, hl, hn, map_one, Real.one_rpow, Units.val_one, one_mul, map_inv, Units.val_inv_eq_inv_val, Complex.ofReal_one, mul_one, Units.val_one, _root_.GlobalTheory.SplitWeil.nabs_one, smul_eq_mul] at key
  rw [mul_right_comm, ← key, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

open MeasureTheory ValuativeRel Matrix in
private theorem hasTypes_apply_mul_right_of_mem_J_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {μ : kˣ →* ℂˣ} {P : _root_.GlobalTheory.StepData.Level (GL a k)} {Q : _root_.GlobalTheory.StepData.Level (GL b k)} {Φ : Matrix b a k → ℂ} (hΦ : _root_.GlobalTheory.StepData.HasTypes μ P Q Φ) {g : GL a k} (hg : g ∈ P.J) (hgi : g ∈ _root_.GlobalTheory.SplitWeil.KO k a) (B : Matrix b a k) :
    Φ (B * g.val) = ((P.lam ⟨g, hg⟩ : ℂ) * ((μ (GeneralLinearGroup.det g) : ℂ))⁻¹) * Φ B := by
  have key := congrFun (hΦ.1 ⟨g, hg⟩) B
  have hn : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hgi)
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, Units.smul_def, inv_one, Matrix.one_mul, hn, map_one, Real.one_rpow, Units.val_one, one_mul, inv_one, Complex.ofReal_one, mul_one, _root_.GlobalTheory.SplitWeil.nabs_one, smul_eq_mul] at key
  rw [mul_right_comm, ← key, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

open MeasureTheory ValuativeRel Matrix in
private theorem withCol_toBlocks11_mul_mulVec_eq_mul_withCol {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] (g : GL (n ⊕ Fin 0) k) (x : Matrix n n' k) (y : n → k) : _root_.GlobalTheory.StepData.withCol (g.val.toBlocks₁₁ * x) (g.val.toBlocks₁₁ *ᵥ y) = g.val * _root_.GlobalTheory.StepData.withCol x y := by
  ext (i | i) (j | j)
  · simp [_root_.GlobalTheory.StepData.withCol, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁]
  · simp [_root_.GlobalTheory.StepData.withCol, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁, mulVec, dotProduct]
  · exact i.elim0
  · exact i.elim0

open MeasureTheory ValuativeRel Matrix in
private theorem fromCols_zero_mul_toBlocks11_eq_mul_val {k : Type} [Field k] {n m : Type} [Fintype n] [DecidableEq n] (g : GL (n ⊕ Fin 0) k) (x : Matrix (m ⊕ Unit) n k) :
    (x * g.val.toBlocks₁₁).toRows₁.fromCols 0 = x.toRows₁.fromCols 0 * g.val := by
  ext i (j | j)
  · change _ = ∑ l, (x.toRows₁.fromCols (0 : Matrix m (Fin 0) k)) i l * (g : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) l (Sum.inl j)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, toRows₁, toBlocks₁₁]
  · exact j.elim0

open MeasureTheory ValuativeRel Matrix in
private theorem mul_apply_inr_unit_eq_vecMul {k : Type} [Field k] {n m : Type} [Fintype n] (x : Matrix (m ⊕ Unit) n k) (B : Matrix n n k) :
    (x * B) (Sum.inr ()) = x (Sum.inr ()) ᵥ* B := by
  funext j
  simp [Matrix.mul_apply, vecMul, dotProduct]

open MeasureTheory ValuativeRel Matrix in
private theorem mulVec_mem_box_of_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] (G : GL n k) (hG : G ∈ _root_.GlobalTheory.SplitWeil.KO k n) (w : kˣ) {m : n → k} (hm : m ∈ _root_.GlobalTheory.StepData.box n w) : (G : Matrix n n k) *ᵥ m ∈ _root_.GlobalTheory.StepData.box n w := by
  rw [_root_.GlobalTheory.StepData.mem_box] at hm ⊢
  intro i
  have hGi := ((_root_.GlobalTheory.SplitFlip.mem_KO_iff G).mp hG).1 i
  refine (Valuation.map_sum_le _ fun j _ => ?_)
  rw [map_mul]
  calc valuation k ((G : Matrix n n k) i j) * valuation k (m j) ≤ 1 * valuation k (m j) := by
        gcongr
        exact (Valuation.mem_integer_iff _ _).mp (hGi j)
    _ ≤ valuation k (w : k) := by rw [one_mul]; exact hm j

open MeasureTheory ValuativeRel Matrix in
private theorem hat_cosetInd_box_vecMul_KO_eq_mulVec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (ε : k) (G : GL n k) (hG : G ∈ _root_.GlobalTheory.SplitWeil.KO k n) (w : kˣ) (y v : n → k) :
    _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk y)) (v ᵥ* (G : Matrix n n k)) =
      _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y))) v := by
  have hdet : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det G) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hG)
  have hiff : ∀ z : n → k, (Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n w) z = Submodule.Quotient.mk y) ↔
      (Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n w) ((G : Matrix n n k) *ᵥ z) = Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y)) := by
    intro z
    simp only [Submodule.Quotient.eq, ← mulVec_sub]
    refine ⟨mulVec_mem_box_of_mem_KO G hG w, fun h => ?_⟩
    have := mulVec_mem_box_of_mem_KO G⁻¹ (inv_mem hG) w h
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
  unfold _root_.GlobalTheory.StepData.hat
  have h := _root_.GlobalTheory.SplitWeil.integral_comp_mulVec_eq_smul ν G (fun z => _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y)) z * ((ψ (ε * v ⬝ᵥ z) : Circle) : ℂ))
  rw [hdet, inv_one, one_smul] at h
  rw [← h]
  congr 1
  ext z
  rw [dotProduct_mulVec]
  congr 1
  unfold _root_.GlobalTheory.StepData.cosetInd
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [← hiff z]


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.LevelLaw.last_steps_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), _root_.GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : _root_.GlobalTheory.SplitWeil.IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, _root_.GlobalTheory.SplitWeil.IsUnram (η j)) → ∀ g : GL (_root_.GlobalTheory.StepData.XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : _root_.GlobalTheory.StepData.XIx κ t (s + 1) → k) x, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).xiTop (_root_.GlobalTheory.StepData.box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).xiTop (_root_.GlobalTheory.StepData.box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  intro k _ _ _ _ _ _ ν hν s κ t _ _ _ _ δ hδ η hη g hg
  haveI := hν.1
  set F := _root_.GlobalTheory.StepData.plainFrame (k := k) (_root_.GlobalTheory.StepData.stdOrd κ t (l := s + 1) (s + 1) 0 rfl) with hF
  have hg' : F.conj.symm g ∈ (_root_.GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 1) × t) δ hδ).J :=
    _root_.GlobalTheory.StepData.Level.mem_map.mp hg
  have hgg : g = _root_.GlobalTheory.StepData.reGL F.ord (F.conj.symm g) := by
    have := F.conj_apply (F.conj.symm g)
    rw [MulEquiv.apply_symm_apply] at this
    simpa [hF, _root_.GlobalTheory.StepData.plainFrame] using this
  have hlam : ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).lam ⟨g, hg⟩ =
      (_root_.GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 1) × t) δ hδ).lam ⟨F.conj.symm g, hg'⟩ :=
    _root_.GlobalTheory.StepData.Level.map_lam _ _ _
  obtain ⟨hg'int, hg'low⟩ := _root_.GlobalTheory.StepData.mem_parahoric.mp hg'
  obtain ⟨⟨A, hA, hAeq⟩, ⟨D, -, hDeq⟩⟩ := _root_.GlobalTheory.StepData.exists_diag_blocks hg'int hg'low
  have hint : g ∈ _root_.GlobalTheory.SplitWeil.KO k _ := by
    rw [hgg]
    exact reGL_mem_KO_of_mem_KO _ hg'int
  have hdet : GeneralLinearGroup.det g = GeneralLinearGroup.det (F.conj.symm g) := by
    conv_lhs => rw [hgg]
    exact _root_.GlobalTheory.StepData.det_reGL _ _
  have hsplit := _root_.GlobalTheory.StepData.tame_det_blocks hδ hg'int hg'low hAeq hDeq
  have hval := _root_.GlobalTheory.StepData.valuation_det_of_mem_KO hint
  set c : ℂˣ := ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).lam ⟨g, hg⟩ *
    (δ (GeneralLinearGroup.det g))⁻¹ with hc
  have hcA : c = (δ (GeneralLinearGroup.det A))⁻¹ := by
    rw [hc, hlam, _root_.GlobalTheory.StepData.parahoric_lam _ D hDeq, hdet, hsplit, _root_.mul_inv_rev, mul_inv_cancel_left]
  have hroot : ∃ n : ℕ, 0 < n ∧ (c : ℂ) ^ n = 1 := by
    obtain ⟨n, hn, hpow⟩ := exists_pos_pow_eq_one_of_isTame_of_valuation_eq_one hδ (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hA)
    exact ⟨n, hn, by rw [← Units.val_pow_eq_pow_val, hcA, inv_pow, hpow, inv_one, Units.val_one]⟩
  have hL := _root_.GlobalTheory.StepData.Chain.ofTwist_laws δ hδ η hη
    (fun j c h ↦ _root_.GlobalTheory.StepData.plainFrame (_root_.GlobalTheory.StepData.stdOrd κ t j c h))
    (_root_.GlobalTheory.StepData.LatFrame.refl k (_root_.GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) t (s + 2)))
  have hmu : ∀ j, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu j (GeneralLinearGroup.det g) =
      δ (GeneralLinearGroup.det g) := by
    intro j
    change (η j * δ) (GeneralLinearGroup.det g) = _
    rw [MonoidHom.mul_apply, hη j _ hval, one_mul]
  have hΦ := hasTypes_apply_mul_left_of_mem_J_KO (μ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu (s + 1))
    (Φ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl) (hL.1 s 0 rfl) hg hint
  have hTop := hasTypes_apply_mul_right_of_mem_J_KO (μ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu (s + 2))
    (Φ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop) hL.2 hg hint
  rw [hmu] at hΦ hTop
  have hΦ' : ∀ B, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl (g.val * B) =
      c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl B := by
    intro B
    rw [hΦ B, hc, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hTop' : ∀ B, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop (B * g.val) =
      c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop B := by
    intro B
    rw [hTop B, hc, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  obtain ⟨G, hGi, hGeq⟩ : ∃ G : GL (_root_.GlobalTheory.StepData.XIx κ t (s + 1)) k,
      G ∈ _root_.GlobalTheory.SplitWeil.KO k _ ∧ (G : Matrix _ _ k) = g.val.toBlocks₁₁ :=
    ⟨_root_.GlobalTheory.StepData.reGL (Equiv.sumEmpty _ (Fin 0)) g, reGL_mem_KO_of_mem_KO _ hint, by
      rw [_root_.GlobalTheory.StepData.reGL_val]
      rfl⟩
  refine ⟨c, hroot, ?_, ?_⟩
  · intro h x₀ y
    unfold _root_.GlobalTheory.StepData.Chain.Psi
    rw [withCol_toBlocks11_mul_mulVec_eq_mul_withCol]
    simp only [_root_.GlobalTheory.SplitWeil.om, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [hΦ']
    ring
  · intro ψ ε w y x
    unfold _root_.GlobalTheory.StepData.Chain.xiTop
    rw [fromCols_zero_mul_toBlocks11_eq_mul_val, mul_apply_inr_unit_eq_vecMul]
    erw [hTop']
    rw [← hGeq, hat_cosetInd_box_vecMul_KO_eq_mulVec ν ψ ε G hGi w y]
    ring

end GlobalTheory.LevelLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeRowUnipotentLatticeFrameConjApply
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory

theorem typeFrame_conj_symm_rowE_apply : ∀ (k : Type) [Field k] (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (ϖ : kˣ) (j c l : ℕ) (h : j + c = l) (p : ℕ) (hp : p < c) (u : XIx κ t j → k) (a b : Ix (κ ⊕ Fin l) t j), ((typeFrame ϖ (stdOrd κ t j c h)).conj.symm (rowE c (p + 1) u)).val a b = (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b + if a = Sum.inl (Sum.inr ⟨p, by omega⟩) then Sum.elim (fun y => ((ϖ : k) ^ (p + 1))⁻¹ * u y) (fun _ => 0) (stdOrd κ t j c h b) else 0 := by
  intro k _ κ t _ _ _ _ ϖ j c l h p hp u a b
  set ord := stdOrd κ t j c h with hord
  have hbas : (typeFrame ϖ ord).bas.val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
    change fromBlocks 1 0 0 _ = _
    congr 1
  have hinv : ((typeFrame ϖ ord).bas⁻¹).val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hbas]
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have hM : ((typeFrame ϖ ord).bas⁻¹ * rowE c (p + 1) u * (typeFrame ϖ ord).bas).val =
      fromBlocks 1 0 (Matrix.of fun (i : Fin c) y => if i.val = p then ((ϖ : k) ^ (p + 1))⁻¹ * u y else 0) 1 := by
    rw [Units.val_mul, Units.val_mul, hinv, hbas]
    change fromBlocks _ _ _ _ * fromBlocks 1 0 _ 1 * _ = _
    simp only [fromBlocks_multiply]
    congr 1 <;> ext i y <;> simp [diagonal_apply]
    by_cases hi : (i : ℕ) = p <;> simp [hi]
  have e : ((typeFrame ϖ ord).conj.symm (rowE c (p + 1) u)).val =
      ((typeFrame ϖ ord).bas⁻¹ * rowE c (p + 1) u * (typeFrame ϖ ord).bas).val.submatrix ord ord := rfl
  rw [e, submatrix_apply, hM]
  have haux : ord (Sum.inl (Sum.inr ⟨p, by omega⟩)) = Sum.inr ⟨p, hp⟩ := standardOrderExtendedBasis_apply_low_block κ t j c h ⟨p, hp⟩
  have hcond : a = Sum.inl (Sum.inr ⟨p, by omega⟩) ↔ ord a = Sum.inr ⟨p, hp⟩ := by
    rw [← haux]; exact ord.apply_eq_iff_eq.symm
  have h1 : (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b =
      (1 : Matrix (XIx κ t j ⊕ Fin c) (XIx κ t j ⊕ Fin c) k) (ord a) (ord b) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    simp only [ord.apply_eq_iff_eq]
  rw [h1]
  simp only [hcond]
  generalize ord a = x
  generalize ord b = y
  rcases x with x | i <;> rcases y with y | i' <;> simp [Matrix.one_apply, Fin.ext_iff]

end GlobalTheory
end

