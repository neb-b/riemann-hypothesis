module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatFunctionalZeroOfFibreIntegralZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeBlockDiagonalTargetEntryConditions
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.PosEntries

section Shape
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem shape_inr {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (h1 : M.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : M.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (i : Fin c) (s : n ⊕ Fin c)
    (hs : M (Sum.inr i) s ≠ 0) : s = Sum.inr i := by
  rcases s with x | j
  · exfalso
    by_cases h : i.val + 1 < p
    · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))
    · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
  · by_cases hij : j = i
    · rw [hij]
    exfalso
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
    · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))

theorem shape_inl {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hp : 1 ≤ p)
    (h1 : M.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : M.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (x : n) (j : Fin c)
    (hs : M (Sum.inl x) (Sum.inr j) ≠ 0) : j.val + 1 = p := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
  · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))

end Shape

section Trans
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem ch_add (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (x + y) = ch x + ch y := by
  simp [ch, Finset.sum_add_distrib]

theorem mulD_inr (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (ϖ : kˣ) (r : n ⊕ Fin c) (l : Fin (c + 1)) :
    (x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) r (Sum.inr l) =
      x r (Sum.inr l) * (ϖ : k) ^ (l.val + 1) := by
  simp [embA, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply]

theorem mulD_inl (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (ϖ : kˣ) (r : n ⊕ Fin c) (y : n') :
    (x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) r (Sum.inl y) =
      x r (Sum.inl y) := by
  simp [embA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
    Finset.sum_ite_eq']

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem opE_translate_free (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (p : ℕ)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k}
    (hz : ∀ r s, ¬ Free p (r, s) → z r s = 0) (hΨ : ∀ x, Ψ (x + z) = Ψ x) (x₀ : Matrix n n' k) :
    opE ψ ν p Ψ x₀ = (ψ (-ch z) : ℂ) * opE ψ ν p Ψ x₀ := by
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ez : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k := fun rs => z rs.1.1 rs.1.2
  have hpt : ∀ e, affPt p x₀ (e + ez) = affPt p x₀ e + z := by
    intro e; ext r s
    simp only [affPt, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
    split_ifs with h
    · simp only [ez]; ring
    · simp [hz r s h]
  unfold opE
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_add_right_eq_self _ ez]
  congr 1; ext e
  rw [hpt, hΨ, ch_add, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem exists_affPt_ne_zero (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k} (h : opE ψ ν p Ψ x₀ ≠ 0) :
    ∃ e, Ψ (affPt p x₀ e) ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply h
  simp [opE, hn]

end Trans

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem entries_core (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : HasConductor ψ 1)
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) < 1) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (c p : ℕ) (hp1 : 1 ≤ p) (A : GL (n ⊕ Fin c) k)
    (hA1 : A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (hA2 : A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)))
    (hB1 : (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (hB2 : (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)))
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (hInt : ∀ x, Ψ x ≠ 0 → IntM (A.val * x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val))
    (hMax : ∀ x z, MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) →
      Ψ (x + z) = Ψ x)
    (hE : opE ψ ν p Ψ ≠ 0) :
    (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧
      (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) ∧
    ∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] := by
  classical
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hE
  obtain ⟨e, he⟩ := exists_affPt_ne_zero ψ ν p hx₀
  have hI := hInt _ he
  have hx_diag : ∀ i : Fin c, affPt p x₀ e (Sum.inr i) (Sum.inr i.castSucc) = 1 := by
    intro i; simp [affPt, basePt, Free]
  have hx_X : ∀ (y : n) (q : Fin c), q.val + 1 = p → affPt p x₀ e (Sum.inl y) (Sum.inr q.castSucc) = 0 := by
    intro y q hq; subst hq; simp [affPt, basePt, Free]
  have hAB : ∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (A⁻¹).val (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun (Units.mul_inv A) (Sum.inr i)) (Sum.inr i)
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)] at h
    · simpa using h
    · intro s _ hs
      by_cases h0 : A.val (Sum.inr i) s = 0
      · simp [h0]
      · exact absurd (shape_inr hA1 hA2 i s h0) hs
    · simp
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · have h := hI (Sum.inr i) (Sum.inr i.castSucc)
    rw [mulD_inr, Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i), hx_diag] at h
    · simpa using h
    · intro s _ hs
      by_cases h0 : A.val (Sum.inr i) s = 0
      · simp [h0]
      · exact absurd (shape_inr hA1 hA2 i s h0) hs
    · simp
  · have hb0 : (A⁻¹).val (Sum.inr i) (Sum.inr i) ≠ 0 := right_ne_zero_of_mul_eq_one (hAB i)
    have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
    have key : ∀ y : k, valuation k y ≤ valuation k ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) →
        ψ y = 1 := by
      intro y hy
      let ζ := y * ((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹
      let E : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
        Matrix.of fun u s => if u = Sum.inr i ∧ s = Sum.inr i.succ then ζ else 0
      let z := (A⁻¹).val * E
      have hAz : A.val * z = E := by simp only [z, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      have hzent : ∀ r s, z r s = if s = Sum.inr i.succ then (A⁻¹).val r (Sum.inr i) * ζ else 0 := by
        intro r s
        simp only [z, E, Matrix.mul_apply, Matrix.of_apply]
        split_ifs with hs
        · rw [Finset.sum_eq_single (Sum.inr i)] <;> simp_all
        · simp [hs]
      have hval : valuation k (ζ * (ϖ : k) ^ (i.val + 2)) < 1 := by
        have h1 : (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ *
            (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) = ϖ := by
          field_simp; ring
        calc valuation k (ζ * (ϖ : k) ^ (i.val + 2))
            = valuation k y * valuation k (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) := by
              rw [← map_mul, mul_assoc]
          _ ≤ valuation k ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) *
              valuation k (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) := by gcongr
          _ = valuation k (ϖ : k) := by rw [← map_mul, h1]
          _ < 1 := hϖ
      have hmax : MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) := by
        intro r s
        rw [hAz]
        rcases s with y' | l
        · rw [mulD_inl]; simp [E]
        · rw [mulD_inr]
          simp only [E, Matrix.of_apply]
          split_ifs with h
          · obtain ⟨rfl, hl⟩ := h
            obtain rfl : l = i.succ := Sum.inr_injective hl
            rw [show (i.succ : Fin (c + 1)).val + 1 = i.val + 2 by simp [Fin.val_succ]]
            exact hval
          · simp
      have hfree : ∀ r s, ¬ Free p (r, s) → z r s = 0 := by
        intro r s hns
        rw [hzent]
        split_ifs with hs
        · subst hs
          by_cases h0 : (A⁻¹).val r (Sum.inr i) = 0
          · simp [h0]
          · exfalso; apply hns
            rcases r with y' | j
            · have := shape_inl hp1 hB1 hB2 y' i h0
              simp [Free, Fin.val_succ]; omega
            · obtain ⟨⟩ := shape_inr hB1 hB2 j (Sum.inr i) h0
              simp [Free, Fin.val_succ]
        · rfl
      have htr := opE_translate_free ψ ν p hfree (fun x' => hMax x' z hmax) x₀
      have hch : ch z = y := by
        simp only [ch, hzent]
        rw [Finset.sum_eq_single i]
        · simp only [if_true, ζ]; field_simp
        · intro j _ hj; simp [Fin.succ_inj, hj]
        · simp
      have h1 : (ψ (-ch z) : ℂ) = 1 := by
        have : ((ψ (-ch z) : ℂ) - 1) * opE ψ ν p Ψ x₀ = 0 := by rw [sub_mul, ← htr]; ring
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hx₀
      have h2 : ψ (-ch z) = 1 := Circle.ext (by simpa using h1)
      rw [AddChar.map_neg_eq_inv, inv_eq_one, hch] at h2
      exact h2
    have hle := (hψ _).mp key
    simp only [Units.val_one, map_one] at hle
    exact hle
  · intro q hq y
    have h := hI (Sum.inl y) (Sum.inr q.castSucc)
    rw [mulD_inr, Matrix.mul_apply, Finset.sum_eq_single (Sum.inr q)] at h
    · rw [hx_diag] at h; simpa using h
    · intro s _ hs
      rcases s with z | j
      · simp [hx_X z q hq]
      · by_cases h0 : A.val (Sum.inl y) (Sum.inr j) = 0
        · simp [h0]
        · have := shape_inl hp1 hA1 hA2 y j h0
          exact absurd (by congr 1; exact Fin.ext (by omega)) hs
    · simp

end Main

theorem entries : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], HasConductor ψ 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → ∀ (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), (∀ x, Ψ x ≠ 0 → IntM (A.val * x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val)) → (∀ x z, MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) → Ψ (x + z) = Ψ x) → opE ψ ν p Ψ ≠ 0 → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) ∧ ∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] := by
  intro k _ _ _ _ _ _ ψ ν _ hψ ϖ hϖ n n' _ _ _ _ c p hp1 _ A hA1 hA2 hB1 hB2 Ψ hInt hMax hE
  exact entries_core ψ ν hψ ϖ hϖ n n' c p hp1 A hA1 hA2 hB1 hB2 Ψ hInt hMax hE

end GlobalTheory.PosEntries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeRowUnipotentMemSourceLevel
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem conj_embA_lowU {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (d : Fin c → kˣ)
    (C : Matrix (Fin c) n k) :
    embA n (GlobalTheory.SplitFlip.diagGL d) * lowU (diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) * C) *
      (embA n (GlobalTheory.SplitFlip.diagGL d))⁻¹ = lowU C := by
  apply Units.ext
  have hinv : ((embA n (GlobalTheory.SplitFlip.diagGL d))⁻¹ : GL (n ⊕ Fin c) k).val =
      fromBlocks 1 0 0 (diagonal fun i => (((d i)⁻¹ : kˣ) : k)) := by
    rw [← map_inv]; rfl
  rw [Units.val_mul, Units.val_mul, hinv]
  change fromBlocks 1 0 0 (diagonal fun i => (d i : k)) * fromBlocks 1 0 _ 1 * _ = fromBlocks 1 0 C 1
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp [← Matrix.mul_assoc, diagonal_mul_diagonal]

theorem rowE_mem_symLev_of_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ u : XIx (Fin κ) t j → k, u ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev j (c + 1 + 1) (by omega)).J := by
  intro k _ _ _ _ s κ S t _ _ hP j c H r hc u hu
  have hr : r < S.ρ := by have := S.odd; omega
  let o := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  let d : Fin (c + 1 + 1) → kˣ := fun i => S.ϖ ^ (i.val + 1)
  let C : Matrix (Fin (c + 1 + 1)) (XIx (Fin κ) t j) k := Matrix.of fun l x => if l.val + 1 = r + 1 then u x else 0
  let C' := diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) * C
  have hC' : ∀ l x, C' l x = if l.val = r then (((S.ϖ ^ (r + 1))⁻¹ : kˣ) : k) * u x else 0 := by
    intro l x
    simp only [C', C, d, diagonal_mul, of_apply, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h; rfl
    · simp
  have hint : ∀ l x, C' l x ∈ 𝒪[k] := by
    intro l x
    rw [hC']
    split_ifs
    · rw [Valuation.mem_integer_iff, map_mul]
      have h0 : 0 < valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by simp [zero_lt_iff]
      rw [Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_one₀ h0]
      exact hu x
    · exact zero_mem _
  have e1 : (typeFrame S.ϖ o).conj ((reGL o).symm (lowU C')) = rowE (c + 1 + 1) (r + 1) u := by
    rw [LatFrame.conj_apply]
    change embA _ (GlobalTheory.SplitFlip.diagGL d) * reGL o ((reGL o).symm (lowU C')) * (embA _ (GlobalTheory.SplitFlip.diagGL d))⁻¹ = _
    rw [MulEquiv.apply_symm_apply]
    exact conj_embA_lowU d C
  show (typeFrame S.ϖ o).conj.symm (rowE (c + 1 + 1) (r + 1) u) ∈ (S.P.iter t S.μ S.tame j).J
  rw [← e1, MulEquiv.symm_apply_apply, hP]
  have hfb : ∀ (M : Matrix (Fin (c + 1 + 1)) (XIx (Fin κ) t j) k), (∀ l x, M l x ∈ 𝒪[k]) →
      ∀ y z, (fromBlocks 1 0 M 1 : Matrix (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) y z ∈ 𝒪[k] := by
    intro M hM y z
    rcases y with y | y <;> rcases z with z | z
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp [zero_mem, one_mem]
    · simp [zero_mem]
    · simpa using hM y z
    · simp only [fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs <;> simp [zero_mem, one_mem]
  refine ⟨?_, ?_⟩
  · rw [mem_KO, ← map_inv]
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [reGL_symm_val, submatrix_apply]; exact hfb C' hint _ _
    · rw [reGL_symm_val, submatrix_apply]
      exact hfb (-C') (fun l x => by simpa using neg_mem (hint l x)) _ _
  · intro a b hnf
    suffices h : (lowU C').val (o a) (o b) = (1 : Matrix _ _ k) a b by
      rw [reGL_symm_val, submatrix_apply, h, sub_self, map_zero]; exact zero_lt_one
    have h1 : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t j) (Ix (Fin κ ⊕ Fin (s + 1)) t j) k) a b =
        (1 : Matrix (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) (o a) (o b) := by
      simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
    rw [h1]
    change (fromBlocks 1 0 C' 1 : Matrix (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) (o a) (o b) = _
    rcases hoa : o a with y | l <;> rcases hob : o b with z | z
    · simp [Matrix.one_apply]
    · simp [one_apply]
    · rw [fromBlocks_apply₂₁, Matrix.one_apply, if_neg (by simp), hC']
      split_ifs with hl
      · exfalso
        have ha : a = Sum.inl (Sum.inr ⟨l.val, by omega⟩) :=
          o.injective (by rw [hoa]; exact (standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (by omega) l).symm)
        subst ha
        rcases z with (z | z) | z
        · have hb : b = Sum.inl (Sum.inl z) :=
            o.injective (by rw [hob]; exact (stdOrd_eps (Fin κ) t j (c + 1 + 1) (by omega) z).symm)
          subst hb
          exact hnf (by simp only [FreeIx, FreeTop]; omega)
        · have hb : b = Sum.inl (Sum.inr ⟨c + 1 + 1 + z.val, by omega⟩) :=
            o.injective (by rw [hob]; exact (stdOrd_f (Fin κ) t j (c + 1 + 1) (by omega) z).symm)
          subst hb
          exact hnf (by simp only [FreeIx, FreeTop, Fin.mk_lt_mk]; omega)
        · have hb : b = Sum.inr z :=
            o.injective (by rw [hob]; exact (stdOrd_d (Fin κ) t j (c + 1 + 1) (by omega) z).symm)
          subst hb
          exact hnf trivial
      · rfl
    · simp [Matrix.one_apply]

end GlobalTheory.SymChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatLinearFunctional
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.CoinvSB

theorem isLocallyConstant_indicator_const {X : Type*} [TopologicalSpace X] {U : Set X} (h1 : IsOpen U)
    (h2 : IsClosed U) (c : ℂ) : IsLocallyConstant (U.indicator fun _ => c) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  by_cases hx : x ∈ U
  · filter_upwards [h1.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  · filter_upwards [h2.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

theorem kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ D : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀, ∫ a, D.1 (x₀, 0, a) ∂(Measure.pi fun _ => ν) = 0) → l D = 0 := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν I₀ I₁ I₂ _ _ _ M _ _ l h1 h2 D hD
  obtain ⟨s, hs⟩ : ∃ s : kˣ, ∀ t ∈ box I₁ s, ∀ y : (I₀ → k) × (I₁ → k) × (I₂ → k),
      D.1 (y + (0, t, 0)) = D.1 y := by
    have h := GlobalTheory.SBConv.eventually_translate D.2
    have hT : Filter.Tendsto (fun t : I₁ → k => ((0 : I₀ → k), -t, (0 : I₂ → k))) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun t : I₁ → k => ((0 : I₀ → k), -t, (0 : I₂ → k))) := by fun_prop
      exact this.tendsto' 0 0 (by simp)
    obtain ⟨s, hs⟩ := exists_box_subset (hT.eventually h)
    refine ⟨s, fun t ht y => ?_⟩
    have := hs ht y
    simpa [sub_eq_add_neg] using this
  obtain ⟨Φ', hΦ', hl⟩ := _root_.GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant k ψ hψc hψ1 I₀ I₁ I₂ M l h1 D s
  have hz : ∀ x₀ x₁, ∫ a, Φ'.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0 := by
    intro x₀ x₁
    simp_rw [hΦ']
    by_cases hx : x₁ ∈ box I₁ s
    · have e : ∀ a, D.1 (x₀, x₁, a) = D.1 (x₀, 0, a) := fun a => by
        simpa using hs x₁ hx (x₀, 0, a)
      simp only [Set.indicator_of_mem hx, one_mul, e]
      exact hD x₀
    · simp [Set.indicator_of_notMem hx]
  rw [hl]
  exact _root_.GlobalTheory.SplitWeil.FourierPi.map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero k ν hν I₀ I₁ I₂ M l h2 Φ' hz

theorem coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∃! l₀ : SB (I₀ → k) →ₗ[ℂ] M, ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), ∃ Ψ : SB (I₀ → k), (∀ x, Ψ.1 x = ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∧ l Φ = l₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν I₀ I₁ I₂ _ _ _ M _ _ l h1 h2
  haveI := secondCountable k
  haveI := t2Space k
  set μ : Measure (I₂ → k) := Measure.pi fun _ => ν with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set vol : ℝ := μ.real (box I₂ 1) with hvol
  have hvol0 : vol ≠ 0 := by
    refine (ENNReal.toReal_pos ?_ ?_).ne'
    · exact (isOpen_box 1).measure_ne_zero μ ⟨0, fun i _ => by simp [cball]⟩
    · exact (isCompact_box 1).measure_lt_top.ne
  have hlc : ∀ (n : Type) [Fintype n] (c : ℂ), IsLocallyConstant ((box n (1 : kˣ)).indicator fun _ => c) :=
    fun n _ c => isLocallyConstant_indicator_const (isOpen_box 1) (isCompact_box 1).isClosed c
  let σf : SB (I₀ → k) → (I₀ → k) × (I₁ → k) × (I₂ → k) → ℂ := fun Ψ x =>
    Ψ.1 x.1 * ((box I₁ (1 : kˣ)).indicator (fun _ => (1 : ℂ)) x.2.1 *
      (box I₂ (1 : kˣ)).indicator (fun _ => ((vol : ℂ))⁻¹) x.2.2)
  have hσ : ∀ Ψ, σf Ψ ∈ SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := by
    intro Ψ
    refine ⟨(Ψ.2.1.comp_continuous continuous_fst).mul
      (((hlc I₁ 1).comp_continuous (by fun_prop)).mul ((hlc I₂ _).comp_continuous (by fun_prop))), ?_⟩
    refine HasCompactSupport.intro (Ψ.2.2.prod ((isCompact_box (1 : kˣ)).prod (isCompact_box (1 : kˣ)))) ?_
    intro x hx
    simp only [σf]
    by_cases h0 : x.1 ∈ tsupport Ψ.1
    · by_cases h1' : x.2.1 ∈ box I₁ (1 : kˣ)
      · have h2' : x.2.2 ∉ box I₂ (1 : kˣ) := fun h => hx ⟨h0, h1', h⟩
        simp [Set.indicator_of_notMem h2']
      · simp [Set.indicator_of_notMem h1']
    · simp [image_eq_zero_of_notMem_tsupport h0]
  let σ : SB (I₀ → k) →ₗ[ℂ] SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) :=
    { toFun := fun Ψ => ⟨σf Ψ, hσ Ψ⟩
      map_add' := fun Ψ Ψ' => by
        apply Subtype.ext; funext x; simp only [σf, Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun c Ψ => by
        apply Subtype.ext; funext x; simp only [σf, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]; ring }
  have hσv : ∀ Ψ x, (σ Ψ).1 x = σf Ψ x := fun _ _ => rfl
  have hInt : ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (x : I₀ → k),
      Integrable (fun a => Φ.1 (x, 0, a)) μ := by
    intro Φ x
    refine Continuous.integrable_of_hasCompactSupport (Φ.2.1.continuous.comp (by fun_prop)) ?_
    refine HasCompactSupport.intro (IsCompact.image Φ.2.2 (continuous_snd.comp continuous_snd)) fun a ha => ?_
    exact image_eq_zero_of_notMem_tsupport fun h => ha ⟨_, h, rfl⟩
  have hσi : ∀ Ψ x, ∫ a, (σ Ψ).1 (x, 0, a) ∂μ = Ψ.1 x := by
    intro Ψ x
    simp only [hσv, σf]
    have h0 : (0 : I₁ → k) ∈ box I₁ (1 : kˣ) := fun i _ => by simp [cball]
    simp only [Set.indicator_of_mem h0, one_mul]
    rw [integral_const_mul, integral_indicator_const _ (isOpen_box _).measurableSet]
    rw [← hvol, Complex.real_smul, mul_inv_cancel₀ (by exact_mod_cast hvol0), mul_one]
  refine ⟨l ∘ₗ σ, fun Φ => ⟨⟨_, _root_.GlobalTheory.SliceIntegral.integral_slice_mem_SB k ν I₀ I₁ I₂ Φ⟩, fun x => rfl, ?_⟩, ?_⟩
  · set Ψ : SB (I₀ → k) := ⟨_, _root_.GlobalTheory.SliceIntegral.integral_slice_mem_SB k ν I₀ I₁ I₂ Φ⟩
    have hk := kernel k ψ ν hψc hψ1 hν I₀ I₁ I₂ M l h1 h2 (Φ - σ Ψ) (fun x₀ => by
      simp only [Submodule.coe_sub, Pi.sub_apply]
      rw [integral_sub (hInt Φ x₀) (hInt (σ Ψ) x₀), hσi]
      exact sub_self _)
    rw [map_sub, sub_eq_zero] at hk
    simpa using hk
  · intro l₀ hl₀
    ext1 Ψ
    obtain ⟨Ψ', hΨ', hl⟩ := hl₀ (σ Ψ)
    have : Ψ' = Ψ := Subtype.ext (funext fun x => (hΨ' x).trans (hσi Ψ x))
    subst this
    simp [← hl]

end GlobalTheory.CoinvSB
end
end

