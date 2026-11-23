module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PosIffLtNP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurDiag

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.IsBlockHighestWeight
section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJMS

open PI.FJM PI.FJMP

theorem pos_of_sign {x : ℚ} {b : Bool} (hb : b = true) (h : b = true ↔ 0 < x) : 0 < x := h.mp hb

theorem neg_of_sign {x : ℚ} {b : Bool} (hb : b = false) (h0 : x ≠ 0) (h : b = true ↔ 0 < x) : x < 0 := by
  rcases lt_or_gt_of_ne h0 with hlt | hgt
  · exact hlt
  · exact absurd (h.mpr hgt) (by rw [hb]; decide)

theorem segs_of {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : SegFacts p q r s μ μ' :=
  segJ_of leftDiagonalActionFormula rightDiagonalActionFormula leftOffDiagonalActionFormula rightOffDiagonalActionFormula p q r s μ μ' P hM

theorem hypothesis_first_cover : HypA := by
  intro p q r s μ μ' P hM
  obtain ⟨sL1p, -, -, -, sL2p, -, -, -⟩ := segs_of hM
  refine blkHyp_pos hM (fun i => (Sum.inl (Fin.castLE (nP_le_nW _) i) : Ix p q))
    (fun k => (Sum.inl (Fin.castLE (nP_le_nW _) k) : Ix r s))
    (Sum.inl_injective.comp (Fin.castLE_injective _)) (Sum.inl_injective.comp (Fin.castLE_injective _))
    (fun a b h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun c d h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => pos_of_lt (leftWeightFirst p q r s μ) sL1p i) (fun k => pos_of_lt (rightWeightFirst p q r s μ') sL2p k)
    _ _ (fun i => rfl) (fun k => rfl)
  · cases c with
    | inl c =>
      obtain ⟨x, hx⟩ := idxP (rightWeightFirst p q r s μ') sL2p c h2
      exact ⟨x, by simp only [hx]⟩
    | inr c => simp [linePos] at h1
  · cases a with
    | inl a =>
      obtain ⟨x, hx⟩ := idxP (leftWeightFirst p q r s μ) sL1p a h2
      exact ⟨x, by simp only [hx]⟩
    | inr a => simp [linePos] at h1

theorem hypothesis_third_cover : HypC := by
  intro p q r s μ μ' P hM
  obtain ⟨-, -, sR1p, -, -, -, sR2p, -⟩ := segs_of hM
  refine blkHyp_pos hM (fun i => (Sum.inr (Fin.castLE (nP_le_nW _) i) : Ix p q))
    (fun k => (Sum.inr (Fin.castLE (nP_le_nW _) k) : Ix r s))
    (Sum.inr_injective.comp (Fin.castLE_injective _)) (Sum.inr_injective.comp (Fin.castLE_injective _))
    (fun a b h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun c d h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => pos_of_lt (leftWeightSecond p q r s μ) sR1p i) (fun k => pos_of_lt (rightWeightSecond p q r s μ') sR2p k)
    _ _ (fun i => rfl) (fun k => rfl)
  · cases c with
    | inl c => simp [linePos] at h1
    | inr c =>
      obtain ⟨x, hx⟩ := idxP (rightWeightSecond p q r s μ') sR2p c h2
      exact ⟨x, by simp only [hx]⟩
  · cases a with
    | inl a => simp [linePos] at h1
    | inr a =>
      obtain ⟨x, hx⟩ := idxP (leftWeightSecond p q r s μ) sR1p a h2
      exact ⟨x, by simp only [hx]⟩

theorem hypothesis_second_cover : HypB := by
  intro p q r s μ μ' P hM
  obtain ⟨-, sL1n, -, -, -, -, -, sR2n⟩ := segs_of hM
  refine blkHyp_neg hM (fun i => (Sum.inl (Fin.rev (Fin.castLE (nN_le _) i)) : Ix p q))
    (fun k => (Sum.inr (Fin.rev (Fin.castLE (nN_le _) k)) : Ix r s))
    (Sum.inl_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (Sum.inr_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (fun a b h => ?_) (fun c d h => ?_)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => neg_of_lt (leftWeightFirst p q r s μ) sL1n i) (fun k => neg_of_lt (rightWeightSecond p q r s μ') sR2n k)
    _ _ (fun i => rfl) (fun k => rfl)
  · have h' : a.val < b.val := h
    have := b.isLt
    have := nN_le (leftWeightFirst p q r s μ)
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · have h' : c.val < d.val := h
    have := d.isLt
    have := nN_le (rightWeightSecond p q r s μ')
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · cases c with
    | inl c => simp [linePos] at h1
    | inr c =>
      obtain ⟨x, hx⟩ := idxN (rightWeightSecond p q r s μ') sR2n c h2
      exact ⟨x, by simp only [hx]⟩
  · cases a with
    | inl a =>
      obtain ⟨x, hx⟩ := idxN (leftWeightFirst p q r s μ) sL1n a h2
      exact ⟨x, by simp only [hx]⟩
    | inr a => simp [linePos] at h1

theorem hypothesis_fourth_cover : HypD := by
  intro p q r s μ μ' P hM
  obtain ⟨-, -, -, sR1n, -, sL2n, -, -⟩ := segs_of hM
  refine blkHyp_neg hM (fun i => (Sum.inr (Fin.rev (Fin.castLE (nN_le _) i)) : Ix p q))
    (fun k => (Sum.inl (Fin.rev (Fin.castLE (nN_le _) k)) : Ix r s))
    (Sum.inr_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (Sum.inl_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (fun a b h => ?_) (fun c d h => ?_)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => neg_of_lt (leftWeightSecond p q r s μ) sR1n i) (fun k => neg_of_lt (rightWeightFirst p q r s μ') sL2n k)
    _ _ (fun i => rfl) (fun k => rfl)
  · have h' : a.val < b.val := h
    have := b.isLt
    have := nN_le (leftWeightSecond p q r s μ)
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · have h' : c.val < d.val := h
    have := d.isLt
    have := nN_le (rightWeightFirst p q r s μ')
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · cases c with
    | inl c =>
      obtain ⟨x, hx⟩ := idxN (rightWeightFirst p q r s μ') sL2n c h2
      exact ⟨x, by simp only [hx]⟩
    | inr c => simp [linePos] at h1
  · cases a with
    | inl a => simp [linePos] at h1
    | inr a =>
      obtain ⟨x, hx⟩ := idxN (leftWeightSecond p q r s μ) sR1n a h2
      exact ⟨x, by simp only [hx]⟩

theorem cover_by_blocks : CoverJ := by
  intro p q r s μ μ' P hM e he l hl
  obtain ⟨sL1p, sL1n, sR1p, sR1n, sL2p, sL2n, sR2p, sR2n⟩ := segs_of hM
  obtain ⟨h1, h2, h3, h4⟩ := pure_of hM he hl
  rcases l with ⟨a | a, c | c⟩
  · obtain ⟨x, hx⟩ := idxP (leftWeightFirst p q r s μ) sL1p a (pos_of_sign rfl h3)
    obtain ⟨y, hy⟩ := idxP (rightWeightFirst p q r s μ') sL2p c (pos_of_sign rfl h4)
    exact Or.inl (Or.inl (Or.inl ⟨(x, y), by simp only [ιA, hx, hy]⟩))
  · obtain ⟨x, hx⟩ := idxN (leftWeightFirst p q r s μ) sL1n a (neg_of_sign rfl h1 h3)
    obtain ⟨y, hy⟩ := idxN (rightWeightSecond p q r s μ') sR2n c (neg_of_sign rfl h2 h4)
    exact Or.inl (Or.inl (Or.inr ⟨(x, y), by simp only [ιB, hx, hy]⟩))
  · obtain ⟨x, hx⟩ := idxN (leftWeightSecond p q r s μ) sR1n a (neg_of_sign rfl h1 h3)
    obtain ⟨y, hy⟩ := idxN (rightWeightFirst p q r s μ') sL2n c (neg_of_sign rfl h2 h4)
    exact Or.inr ⟨(x, y), by simp only [ιD, hx, hy]⟩
  · obtain ⟨x, hx⟩ := idxP (leftWeightSecond p q r s μ) sR1p a (pos_of_sign rfl h3)
    obtain ⟨y, hy⟩ := idxP (rightWeightSecond p q r s μ') sR2p c (pos_of_sign rfl h4)
    exact Or.inl (Or.inr ⟨(x, y), by simp only [ιC, hx, hy]⟩)

theorem intFacts_of {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : IntFacts p q r s μ μ' := by
  obtain ⟨e0, he0⟩ := exists_mem_support hM.2.1
  refine ⟨fun a => ?_, fun c => ?_⟩
  · rw [← monomialLeftWeight_eq_weight_sub leftDiagonalActionFormula (mem_leftHighestWeight_of_isMinimalJointVector hM) e0 he0 a, Int.floor_intCast]
  · rw [← monomialRightWeight_eq_weight_sub rightDiagonalActionFormula (mem_rightHighestWeight_of_isMinimalJointVector hM) e0 he0 c, Int.floor_intCast]

end PI.FJMS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurCauchy
section
noncomputable section

open MvPolynomial Classical

namespace PI.FJMB

def HypAnti : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (P : MvPolynomial σ ℂ), P ≠ 0 → (∀ a b : Fin m, a < b → PI.FJM.bRow ι a b P = 0) →
  (∀ e ∈ P.support, ∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) → Antitone α

def HypShape : Prop := ∀ (σ : Type) (m : ℕ) (ι : Fin m × Fin m → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ), Antitone α →
  HWB ι (PI.FJM.shapeProd (Matrix.of fun (i : Fin m) (k : Fin m) => (X (ι (i, k)) : MvPolynomial σ ℂ))
    (List.ofFn α)) ∧
  aeval (killS (offD ι)) (PI.FJM.shapeProd (Matrix.of fun (i : Fin m) (k : Fin m) =>
    (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α)) = ∏ i, X (ι (i, i)) ^ α i

def diagOne' {σ : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) : σ → MvPolynomial σ ℂ := fun v =>
  if v ∈ offD ι then 0 else if ∃ i k, ι (i, k) = v ∧ (i : ℕ) = k then 1 else X v

def HypDiag : Prop := ∀ (σ : Type) (m : ℕ) (ι : Fin m × Fin m → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (P : MvPolynomial σ ℂ), (∀ e ∈ P.support, ∀ i, ∑ k : Fin m, e (ι (i, k)) = α i) →
  aeval (killS (offD ι)) P = (∏ i, X (ι (i, i)) ^ α i) * aeval (diagOne' ι) P

def HypFree : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ P : MvPolynomial σ ℂ, ∀ e ∈ (aeval (diagOne' ι) P).support, ∀ x, e (ι x) = 0

variable {σ : Type*}

theorem exists_support_of_killS {S : Set σ} {P : MvPolynomial σ ℂ} (h : aeval (killS S) P ≠ 0) :
    ∃ e ∈ P.support, ∀ v ∈ S, e v = 0 := by
  by_contra hne
  push_neg at hne
  apply h
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨v, hvS, hv⟩ := hne e he
  rw [aeval_monomial, Finsupp.prod]
  refine mul_eq_zero_of_right _ ?_
  refine Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hv) ?_
  simp [killS, hvS, hv]

theorem aeval_killS_free {S : Set σ} {Q : MvPolynomial σ ℂ} (h : ∀ e ∈ Q.support, ∀ v ∈ S, e v = 0) :
    aeval (killS S) Q = Q := by
  conv_rhs => rw [Q.as_sum]
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [aeval_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, algebraMap_eq]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvS : v ∉ S := fun hvS => (Finsupp.mem_support_iff.mp hv) (h e he v hvS)
  simp only [killS, if_neg hvS]

private theorem pderiv_eq_zero_of_forall_support_apply_eq_zero {v : σ} {Q : MvPolynomial σ ℂ} (h : ∀ e ∈ Q.support, e v = 0) :
    pderiv v Q = 0 := by
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun e he => ?_
  simp [pderiv_monomial, h e he]

theorem bRow_mul_free {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (S Q : MvPolynomial σ ℂ)
    (hQ : ∀ e ∈ Q.support, ∀ x, e (ι x) = 0) : PI.FJM.bRow ι a b (S * Q) = PI.FJM.bRow ι a b S * Q := by
  show (∑ k : Fin n, LinearMap.mulLeft ℂ (X (ι (a, k))) * (pderiv (ι (b, k))).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) (S * Q) =
    (∑ k : Fin n, LinearMap.mulLeft ℂ (X (ι (a, k))) * (pderiv (ι (b, k))).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) S * Q
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  change X (ι (a, k)) * pderiv (ι (b, k)) (S * Q) = X (ι (a, k)) * pderiv (ι (b, k)) S * Q
  have hl := (pderiv (ι (b, k))).leibniz S Q
  rw [pderiv_eq_zero_of_forall_support_apply_eq_zero fun e he => hQ e he (b, k), smul_zero, zero_add, smul_eq_mul] at hl
  rw [hl]
  ring

theorem bCol_mul_free {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (S Q : MvPolynomial σ ℂ)
    (hQ : ∀ e ∈ Q.support, ∀ x, e (ι x) = 0) : PI.FJM.bCol ι c d (S * Q) = PI.FJM.bCol ι c d S * Q := by
  show (∑ i : Fin m, LinearMap.mulLeft ℂ (X (ι (i, c))) * (pderiv (ι (i, d))).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) (S * Q) =
    (∑ i : Fin m, LinearMap.mulLeft ℂ (X (ι (i, c))) * (pderiv (ι (i, d))).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) S * Q
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  change X (ι (i, c)) * pderiv (ι (i, d)) (S * Q) = X (ι (i, c)) * pderiv (ι (i, d)) S * Q
  have hl := (pderiv (ι (i, d))).leibniz S Q
  rw [pderiv_eq_zero_of_forall_support_apply_eq_zero fun e he => hQ e he (i, d), smul_zero, zero_add, smul_eq_mul] at hl
  rw [hl]
  ring

theorem cauchyHW_of (hA : HypAnti) (hS : HypShape) (hD : HypDiag) (hF : HypFree) : PI.FJM.CauchyHW := by
  intro τ m n ι hι α β P hP hrow hcol hsum hα hβ
  have hinvP : HWB ι P := ⟨hrow, hcol⟩
  have hne : aeval (killS (offD ι)) P ≠ 0 := fun h0 =>
    hP (diag_zero m n ι hι P hinvP h0)
  obtain ⟨e, heP, he0⟩ := exists_support_of_killS hne
  have hoff : ∀ (i : Fin m) (k : Fin n), (i : ℕ) ≠ k → e (ι (i, k)) = 0 :=
    fun i k h => he0 _ ⟨i, k, rfl, h⟩
  have hrowsum : ∀ (i : Fin m) (k : Fin n), (i : ℕ) = k → α i = e (ι (i, k)) := by
    intro i k hik
    rw [← (hsum e heP).1 i, Finset.sum_eq_single k]
    · intro k' _ hk'
      exact hoff i k' fun h => hk' (Fin.ext (h.symm.trans hik))
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hcolsum : ∀ (i : Fin m) (k : Fin n), (i : ℕ) = k → β k = e (ι (i, k)) := by
    intro i k hik
    rw [← (hsum e heP).2 k, Finset.sum_eq_single i]
    · intro i' _ hi'
      exact hoff i' k fun h => hi' (Fin.ext (h.trans hik.symm))
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hrowlt : ∀ i : Fin m, (i : ℕ) < n := by
    intro i
    by_contra hi
    push_neg at hi
    have h0 : α i = 0 := by
      rw [← (hsum e heP).1 i]
      exact Finset.sum_eq_zero fun k _ => hoff i k (by have := k.isLt; omega)
    exact (hα i).ne' h0
  have hcollt : ∀ k : Fin n, (k : ℕ) < m := by
    intro k
    by_contra hk
    push_neg at hk
    have h0 : β k = 0 := by
      rw [← (hsum e heP).2 k]
      exact Finset.sum_eq_zero fun i _ => hoff i k (by have := i.isLt; omega)
    exact (hβ k).ne' h0
  have hmn : m = n := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      exact lt_irrefl n (hrowlt ⟨n, h⟩)
    · by_contra h
      push_neg at h
      exact lt_irrefl m (hcollt ⟨m, h⟩)
  have hanti : Antitone α := hA τ m n ι hι α P hP hrow fun e he i => (hsum e he).1 i
  refine ⟨hmn, hanti, fun i k h => (hrowsum i k h).trans (hcolsum i k h).symm, ?_⟩
  subst n
  obtain ⟨hMinv, hMdiag⟩ := hS τ m ι hι α hanti
  obtain ⟨hMr, hMc⟩ := hMinv
  have hDP := hD τ m ι hι α P fun e he i => (hsum e he).1 i
  have hFP := hF τ m m ι hι P
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = aeval (diagOne' ι) P := ⟨_, rfl⟩
  rw [← hQ] at hDP hFP
  refine ⟨Q, hFP, ?_⟩
  rw [← sub_eq_zero]
  refine diag_zero m m ι hι _ ⟨fun a b hab => ?_, fun c d hcd => ?_⟩ ?_
  · rw [map_sub, bRow_mul_free ι a b _ Q hFP, hrow a b hab, hMr a b hab, zero_mul, sub_zero]
  · rw [map_sub, bCol_mul_free ι c d _ Q hFP, hcol c d hcd, hMc c d hcd, zero_mul, sub_zero]
  · have hQfree : ∀ f ∈ Q.support, ∀ v ∈ offD ι, f v = 0 := by
      rintro f hf v ⟨i, k, rfl, -⟩
      exact hFP f hf (i, k)
    rw [map_sub, map_mul, hMdiag, aeval_killS_free hQfree, hDP, sub_self]

end PI.FJMB
end
end

