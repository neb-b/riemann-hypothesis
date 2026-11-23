module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0105

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationsEqualTracesConjugate
section
open Matrix

namespace GlobalTheory

def piMatUnit {I : Type} [DecidableEq I] (m : ℕ) (τ : I) (i j : Fin m) :
    I → Matrix (Fin m) (Fin m) ℂ :=
  Pi.single τ (Matrix.single i j 1)

lemma piMatUnit_mul {I : Type} [DecidableEq I] (m : ℕ) (τ τ' : I) (i j k l : Fin m) :
    piMatUnit m τ i j * piMatUnit m τ' k l =
      if τ = τ' ∧ j = k then piMatUnit m τ i l else 0 := by
  funext ρ
  simp only [piMatUnit, Pi.mul_apply]
  by_cases h1 : τ = τ'
  · subst h1
    by_cases h2 : j = k
    · subst h2
      by_cases h3 : ρ = τ
      · subst h3; simp [Matrix.single_mul_single_same]
      · simp [Pi.single_apply, h3]
    · by_cases h3 : ρ = τ
      · subst h3; simp [Matrix.single_mul_single_of_ne, h2]
      · simp [Pi.single_apply, h3, h2]
  · by_cases h3 : ρ = τ
    · subst h3
      have : ρ ≠ τ' := h1
      simp [Pi.single_apply, this, h1]
    · simp [Pi.single_apply, h3, h1]

lemma piMatUnit_decomp {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (x : I → Matrix (Fin m) (Fin m) ℂ) :
    x = ∑ τ, ∑ i, ∑ j, x τ i j • piMatUnit m τ i j := by
  funext ρ
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, piMatUnit,
    Pi.single_apply]
  simp only [show ∀ (c : Prop) [Decidable c] (M : Matrix (Fin m) (Fin m) ℂ),
      (if c then M else 0) a b = if c then M a b else 0 from fun c _ M => by split_ifs <;> rfl]
  simp [Matrix.zero_apply, Matrix.single_apply, mul_ite, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

lemma sum_piMatUnit_diag {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (τ : I) :
    ∑ i, piMatUnit m τ i i = Pi.single τ 1 := by
  funext ρ
  ext a b
  by_cases h : ρ = τ
  · subst h
    simp only [piMatUnit, Finset.sum_apply, Matrix.sum_apply, Pi.single_eq_same, Matrix.single_apply,
      Matrix.one_apply]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab]
  · simp [piMatUnit, Finset.sum_apply, Matrix.sum_apply, Pi.single_apply, h]

lemma exists_mul_idem_mul_eq_of_trace_eq {g : ℕ} (P P' : Matrix (Fin g) (Fin g) ℂ)
    (hP : IsIdempotentElem P) (hP' : IsIdempotentElem P') (ht : P.trace = P'.trace) :
    ∃ X Y : Matrix (Fin g) (Fin g) ℂ, Y * P' * X = P := by
  first
  | exact @_root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq
  | exact _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq
  | (apply _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq ..)

theorem conj_of_trace_central_idem_eq :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (m g : ℕ), 0 < m →
      ∀ (σ σ' : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ),
        (∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace) →
          ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ x, σ' x * h = h * σ x := by
  intro I _ _ m g hm σ σ' htr
  set z : Fin m := ⟨0, hm⟩

  have hdiag : ∀ (ρ : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (τ : I),
      (ρ (Pi.single τ 1)).trace = (m : ℂ) * (ρ (piMatUnit m τ z z)).trace := by
    intro ρ τ
    have hi : ∀ i, (ρ (piMatUnit m τ i i)).trace = (ρ (piMatUnit m τ z z)).trace := by
      intro i
      have e1 : piMatUnit m τ i i = piMatUnit m τ i z * piMatUnit m τ z i := by
        rw [piMatUnit_mul]; simp
      have e2 : piMatUnit m τ z z = piMatUnit m τ z i * piMatUnit m τ i z := by
        rw [piMatUnit_mul]; simp
      rw [e1, e2, map_mul, map_mul, Matrix.trace_mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_piMatUnit_diag, map_sum, Matrix.trace_sum, Finset.sum_congr rfl (fun i _ => hi i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hidem : ∀ (ρ : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (τ : I),
      IsIdempotentElem (ρ (piMatUnit m τ z z)) := by
    intro ρ τ
    unfold IsIdempotentElem
    rw [← map_mul, piMatUnit_mul]; simp
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have htr' : ∀ τ, (σ (piMatUnit m τ z z)).trace = (σ' (piMatUnit m τ z z)).trace := by
    intro τ
    have := htr τ
    rw [hdiag σ, hdiag σ'] at this
    exact mul_left_cancel₀ hm' this
  choose X Y hYX using fun τ => exists_mul_idem_mul_eq_of_trace_eq _ _ (hidem σ τ) (hidem σ' τ) (htr' τ)
  set h : Matrix (Fin g) (Fin g) ℂ :=
    ∑ τ, ∑ i, σ' (piMatUnit m τ i z) * X τ * σ (piMatUnit m τ z i) with hh
  set h' : Matrix (Fin g) (Fin g) ℂ :=
    ∑ τ, ∑ i, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) with hh'

  have hE : ∀ τ k l, σ' (piMatUnit m τ k l) * h = h * σ (piMatUnit m τ k l) := by
    intro τ k l
    have hL : ∀ τ' i, σ' (piMatUnit m τ k l) * (σ' (piMatUnit m τ' i z) * X τ' * σ (piMatUnit m τ' z i))
        = if τ = τ' ∧ l = i then σ' (piMatUnit m τ k z) * X τ * σ (piMatUnit m τ z l) else 0 := by
      intro τ' i
      rw [← mul_assoc, ← mul_assoc, ← map_mul, piMatUnit_mul]
      split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; rfl
      · simp
    have hR : ∀ τ' i, σ' (piMatUnit m τ' i z) * X τ' * σ (piMatUnit m τ' z i) * σ (piMatUnit m τ k l)
        = if τ = τ' ∧ k = i then σ' (piMatUnit m τ k z) * X τ * σ (piMatUnit m τ z l) else 0 := by
      intro τ' i
      rw [mul_assoc _ (σ _), ← map_mul, piMatUnit_mul]
      by_cases hc : τ' = τ ∧ i = k
      · obtain ⟨rfl, rfl⟩ := hc; simp
      · have hc' : ¬ (τ = τ' ∧ k = i) := fun h => hc ⟨h.1.symm, h.2.symm⟩
        simp [hc, hc']
    rw [hh, Finset.mul_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_mul, hL, hR]
    simp [ite_and, Finset.sum_ite_eq]
  have hint : ∀ x, σ' x * h = h * σ x := by
    intro x
    rw [piMatUnit_decomp m x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hE]

  have hprod : ∀ τ i τ' j, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) *
      (σ' (piMatUnit m τ' j z) * X τ' * σ (piMatUnit m τ' z j))
        = if τ = τ' ∧ i = j then σ (piMatUnit m τ i i) else 0 := by
    intro τ i τ' j
    have e : σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) *
        (σ' (piMatUnit m τ' j z) * X τ' * σ (piMatUnit m τ' z j)) =
        σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i * piMatUnit m τ' j z) * X τ' *
          σ (piMatUnit m τ' z j) := by
      rw [map_mul]; simp only [mul_assoc]
    rw [e, piMatUnit_mul]
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      rw [show σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z z) * X τ * σ (piMatUnit m τ z i) =
          σ (piMatUnit m τ i z) * (Y τ * σ' (piMatUnit m τ z z) * X τ) * σ (piMatUnit m τ z i) by
            simp only [mul_assoc], hYX τ, ← map_mul, ← map_mul]
      simp [piMatUnit_mul]
    · simp
  have hrow : ∀ τ i, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) * h =
      σ (piMatUnit m τ i i) := by
    intro τ i
    rw [hh]
    simp only [Finset.mul_sum, hprod]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hinv : h' * h = 1 := by
    rw [hh', Finset.sum_mul]
    simp only [Finset.sum_mul, hrow]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one σ, ← Finset.univ_sum_single (1 : I → Matrix (Fin m) (Fin m) ℂ), map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Pi.one_apply, ← sum_piMatUnit_diag, map_sum]
  exact ⟨h, (Matrix.isUnit_iff_isUnit_det h).mpr (Matrix.isUnit_det_of_left_inverse hinv), hint⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfBorelMovesOpenFrames
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix

namespace GlobalTheory

theorem scalar_of_triangular_moves_open :
  ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (m : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ x ∈ W, ∃ b ∈ Bor X.Ψ r, lact m x = rmul x b) → ∃ s : E, (m : Matrix (Fin r) (Fin r) E) = Matrix.scalar (Fin r) s := by
  intro E _ _ _ r X m W hW hne _ hact
  classical
  cases r with
  | zero => exact ⟨0, by ext i; exact i.elim0⟩
  | succ n =>
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h : σ ∈ X.Ψ
    · exact ⟨σ, h⟩
    · refine ⟨ComplexEmbedding.conjugate σ, ?_⟩
      by_contra h'
      exact h ((X.cmType σ).2 h')
  obtain ⟨τ0, hτ0⟩ := hτ
  let τ : X.Ψ := ⟨τ0, hτ0⟩
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := (m : Matrix (Fin (n+1)) (Fin (n+1)) E).map τ0
  have key : ∀ y ∈ W, ∀ i j : Fin (n+1),
      (M *ᵥ (fun k => y τ k 0)) i * y τ j 0 = (M *ᵥ (fun k => y τ k 0)) j * y τ i 0 := by
    intro y hy i j
    obtain ⟨b, hb, he⟩ := hact y hy
    have hcol : ∀ a : Fin (n+1), (M *ᵥ (fun k => y τ k 0)) a = y τ a 0 * b τ 0 0 := by
      intro a
      have := congrFun (congrFun (congrFun he τ) a) 0
      simp only [lact, rmul, mat, Matrix.mul_apply, Matrix.of_apply] at this
      have hs : ∑ k, y τ a k * b τ k 0 = y τ a 0 * b τ 0 0 := by
        rw [Finset.sum_eq_single (0 : Fin (n+1))]
        · intro k _ hk
          rw [(hb τ).2 k 0 (Fin.pos_of_ne_zero hk), mul_zero]
        · simp
      rw [hs] at this
      simp only [Matrix.mulVec, dotProduct]
      exact this
    rw [hcol i, hcol j]; ring
  obtain ⟨x0, hx0⟩ := hne
  have hq : ∀ w : Fin (n+1) → ℂ, ∀ i j : Fin (n+1), (M *ᵥ w) i * w j = (M *ᵥ w) j * w i := by
    intro w i j
    let pert : ℂ → Frame X.Ψ (n+1) := fun t σ a c => x0 σ a c + if σ = τ ∧ c = 0 then t * w a else 0
    have hc : Continuous pert := by
      apply continuous_pi; intro σ; apply continuous_pi; intro a; apply continuous_pi; intro c
      by_cases h : σ = τ ∧ c = 0
      · simp only [pert, h, and_self, if_true]; fun_prop
      · simp only [pert, h, if_false]; fun_prop
    have h0 : pert 0 = x0 := by funext σ a c; simp [pert]
    have hO : IsOpen (pert ⁻¹' W) := hW.preimage hc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO 0 (by simp [h0, hx0])
    set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht_def
    have htn : t ≠ 0 := by
      rw [ht_def]; exact_mod_cast (by positivity : ε / 2 ≠ 0)
    have hnorm : ‖t‖ < ε := by
      rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
    have h1 : pert t ∈ W := hball (by simpa using hnorm)
    have h2 : pert (-t) ∈ W := hball (by simpa using hnorm)
    have hcolp : ∀ s : ℂ, (fun k => pert s τ k 0) = (fun k => x0 τ k 0) + s • w := by
      intro s; funext k; simp [pert]
    have e1 := key _ h1 i j
    have e2 := key _ h2 i j
    have e0 := key _ hx0 i j
    have hpt : ∀ s : ℂ, ∀ k, pert s τ k 0 = x0 τ k 0 + s * w k := by
      intro s k; simp [pert]
    rw [hcolp] at e1 e2
    simp only [hpt, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have : t ^ 2 * ((M *ᵥ w) i * w j - (M *ᵥ w) j * w i) = 0 := by
      linear_combination (1/2 : ℂ) * e1 + (1/2 : ℂ) * e2 - e0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) htn
    · exact sub_eq_zero.mp h
  have hoff : ∀ i j : Fin (n+1), i ≠ j → M i j = 0 := by
    intro i j hij
    have := hq (Pi.single j 1) i j
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hij] using this
  have hsv : ∀ j k : Fin (n+1), (M *ᵥ Pi.single j (1:ℂ)) k = M k j := by
    intro j k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdiag : ∀ i j : Fin (n+1), M i i = M j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have := hq (Pi.single i 1 + Pi.single j 1) i j
    have hji : j ≠ i := Ne.symm hij
    rw [Matrix.mulVec_add] at this
    simp only [Pi.add_apply, hsv, Pi.single_apply, hij, hji, if_true, if_false, mul_one, add_zero, zero_add, hoff i j hij, hoff j i hji] at this
    exact this
  refine ⟨(m : Matrix (Fin (n+1)) (Fin (n+1)) E) 0 0, ?_⟩
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    apply τ0.injective
    have := hdiag i 0
    simpa [M] using this
  · apply τ0.injective
    have := hoff i j hij
    simpa [M] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledKoszulTestFamilyHasDerivAtScale
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

noncomputable section

namespace GlobalTheory.PsCo.HomotDeriv

theorem ev_rP {n : ℕ} (ε : Fin n → Bool) (g : Mat n) : ev g (rP ε) = ((rM ε g : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rP, rM, map_sum, map_mul, ev, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem hasDerivAt_scale (G : ℝ → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (k : ℕ) (r t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => iteratedDeriv k (fun y => G (s * y)) r)
      (t⁻¹ * (k * iteratedDeriv k (fun y => G (t * y)) r + r * iteratedDeriv (k + 1) (fun y => G (t * y)) r)) t := by
  have hc : ∀ m : ℕ, ContDiff ℝ m G := fun m => hG.of_le (by exact_mod_cast le_top)
  have e : ∀ (m : ℕ) (s : ℝ), iteratedDeriv m (fun y => G (s * y)) r = s ^ m * iteratedDeriv m G (s * r) :=
    fun m s => congrFun (iteratedDeriv_comp_const_mul (hc m) s) r
  simp only [e]
  have hD : HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G (t * r)) (t * r) := by
    rw [iteratedDeriv_succ]
    exact ((hc (k + 1)).differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => s * r) r t := by simpa using (hasDerivAt_id t).mul_const r
  have h2 : HasDerivAt (fun s : ℝ => s ^ k * iteratedDeriv k G (s * r))
      (k * t ^ (k - 1) * iteratedDeriv k G (t * r) + t ^ k * (iteratedDeriv (k + 1) G (t * r) * r)) t :=
    by
    have h3 := (hasDerivAt_pow k t).mul (hD.comp t h1)
    exact h3
  refine h2.congr_deriv ?_
  rcases k with _ | k
  · simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, pow_one]
    field_simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

theorem sum_shift (N : ℕ) (a e : ℕ → ℂ) (r : ℂ) (he : e (N + 1) = 0) :
    ∑ k ∈ Finset.range (N + 1), ((k : ℂ) * a k + r * a (k + 1)) * e k =
      ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1) + r * e k) := by
  have h1 : ∑ k ∈ Finset.range (N + 1), (k : ℂ) * a k * e k =
      ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1)) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ (n := N), he]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  simp only [add_mul (_ * a _), mul_add (a _), Finset.sum_add_distrib, h1]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sum_prev {n : ℕ} (g : Mat n) (N : ℕ) (a : ℕ → ℂ) (q : ℕ → Poly n) (hq : q N = 0) (R : ℂ) :
    ∑ k ∈ Finset.range (N + 1), a (k + 1) * (R * ev g (prev q k)) =
      ∑ k ∈ Finset.range (N + 1), a (k + 1 + 1) * (R * ev g (q k)) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ (n := N), hq]
  simp [prev]

theorem famF_hasDerivAt : ∀ {n : ℕ} (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → GlobalTheory.PsCo.Pc1.Poly n) (q : GlobalTheory.PsCo.Pc1.Mode ε → ℕ → GlobalTheory.PsCo.Pc1.Poly n), ContDiff ℝ (⊤ : ℕ∞) G → GlobalTheory.PsCo.Pc1.IsKoszul ε p q → ∀ t : ℝ, 0 < t → ∀ g : GlobalTheory.PsCo.Pc1.Mat n, HasDerivAt (fun s : ℝ => GlobalTheory.PsCo.Pc1.famF ε G p s g) (((t⁻¹ : ℝ) : ℂ) * ∑ x : GlobalTheory.PsCo.Pc1.Mode ε, ∑ j ∈ Finset.range (GlobalTheory.PsCo.Pc1.nMode ε + 1), GlobalTheory.PsCo.Pc1.adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g) t := by
  intro n ε G p q hG hK t ht g
  obtain ⟨hrec, hp, hq⟩ := hK
  let a : ℕ → ℂ := fun j => ((iteratedDeriv j (fun y => G (t * y)) (rM ε g) : ℝ) : ℂ)
  have hd : ∀ k ∈ Finset.range (nMode ε + 1),
      HasDerivAt (fun s : ℝ => bas ε (iteratedDeriv k fun x => G (s * x)) (p k) g)
        (((t⁻¹ : ℝ) : ℂ) * (((k : ℂ) * a k + (rM ε g : ℂ) * a (k + 1)) * ev g (p k))) t := by
    intro k _
    refine (((hasDerivAt_scale G hG k (rM ε g) t ht.ne').ofReal_comp).mul_const (ev g (p k))).congr_deriv ?_
    simp only [a]
    push_cast
    ring
  refine (HasDerivAt.fun_sum hd).congr_deriv ?_
  rw [← Finset.mul_sum]
  congr 1
  have hA : ∀ (x : Mode ε) (j : ℕ),
      adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g =
        a (j + 1) * ev g (dM ε x (q x j)) + a (j + 1 + 1) * (ev g (dM ε x (rP ε)) * ev g (q x j)) := by
    intro x j
    simp only [adBas, bas, dM, ← iteratedDeriv_succ, map_mul, a]
    ring
  have hR : ∀ j : ℕ, ((j : ℂ) + 1) * ev g (p (j + 1)) + (rM ε g : ℂ) * ev g (p j) =
      ∑ x, (ev g (dM ε x (q x j)) + ev g (dM ε x (rP ε)) * ev g (prev (q x) j)) := by
    intro j
    have := congrArg (ev g) (hrec j)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_add (f := _), map_mul, ev_rP, map_natCast, map_one] using this
  rw [sum_shift (nMode ε) a (fun k => ev g (p k)) (rM ε g : ℂ) (by simp [hp (nMode ε + 1) (Nat.lt_succ_self _)])]
  simp only [hA, hR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_prev g (nMode ε) a (q x) (hq x _ le_rfl)]

end GlobalTheory.PsCo.HomotDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerRepUnitary
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

theorem integral_rhoFun_mul_conj (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by
  have h : ∀ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) =
      u (x + pPart w) * starRingEnd ℂ (v (x + pPart w)) := by
    intro x
    have hp : phase w x * starRingEnd ℂ (phase w x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]
      simp
    simp only [rhoFun, map_mul]
    calc _ = (phase w x * starRingEnd ℂ (phase w x)) * (u (x + pPart w) * starRingEnd ℂ (v (x + pPart w))) := by
          ring
      _ = _ := by rw [hp, one_mul]
  simp_rw [h]
  exact integral_add_right_eq_self (fun x => u x * starRingEnd ℂ (v x)) (pPart w)

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDenseHasCompactSupport
section
open Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem schwartz_dense_hasCompactSupport :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Dense {f : SchwartzMap V ℂ | HasCompactSupport (f : V → ℂ)} := by
  intro V _ _ _
  obtain ⟨χ, -, hχc, hχs, -, hχ0⟩ := exists_contDiff_tsupport_subset (n := ⊤) (Filter.univ_mem (f := 𝓝 (0 : V)))
  set L : ℝ → V →L[ℝ] V := fun r => r • ContinuousLinearMap.id ℝ V with hL
  have hLx : ∀ r x, L r x = r • x := fun r x => by simp [hL]
  have hLn : ∀ r, ‖L r‖ ≤ |r| := fun r => by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg r) ContinuousLinearMap.norm_id_le
  set g : ℝ → V → ℂ := fun r => Complex.ofRealLI ∘ (χ ∘ L r) with hg
  have hgx : ∀ r x, g r x = ((χ (r • x) : ℝ) : ℂ) := fun r x => by simp [hg, hLx]
  have hχL : ∀ r, ContDiff ℝ ∞ (χ ∘ L r) := fun r => hχs.comp (L r).contDiff
  have hgs : ∀ r, ContDiff ℝ ∞ (g r) := fun r => Complex.ofRealLI.contDiff.comp (hχL r)
  have hM : ∀ i : ℕ, ∃ M, ∀ y, ‖iteratedFDeriv ℝ i χ y‖ ≤ M := fun i =>
    (hχs.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hχc.iteratedFDeriv i)
  choose M hM using hM
  have hgb : ∀ i : ℕ, ∀ r x, ‖iteratedFDeriv ℝ i (g r) x‖ ≤ M i * ‖L r‖ ^ i := by
    intro i r x
    rw [hg, Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hχL r).contDiffAt (mod_cast le_top),
      ContinuousLinearMap.iteratedFDeriv_comp_right (L r) hχs x (mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (hM i _) (by positivity)
  have htg : ∀ r, (g r).HasTemperateGrowth := fun r =>
    ⟨hgs r, fun n => ⟨0, M n * ‖L r‖ ^ n, fun x => by simpa using hgb n r x⟩⟩
  intro f
  set F : ℝ → SchwartzMap V ℂ := fun r => SchwartzMap.smulLeftCLM ℂ (g r) f with hF
  have hFx : ∀ r, (F r : V → ℂ) = fun y => g r y * f y := fun r => by
    ext y; simp [hF, SchwartzMap.smulLeftCLM_apply_apply (htg r)]
  have hF0 : F 0 = f := by
    ext y; rw [hFx]; simp [hgx, hχ0]
  have hcont : ContinuousAt F 0 := by
    refine schwartz_continuousAt_of_pointwise_of_bounded F 0 (fun v => ?_) (fun k n => ?_)
    · simp only [hFx, hgx]
      exact ((Complex.continuous_ofReal.comp (hχs.continuous.comp
        (continuous_id.smul continuous_const))).mul continuous_const).continuousAt
    · refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |M i| * SchwartzMap.seminorm ℂ k (n - i) f, ?_⟩
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with r hr v
      have hr1 : |r| ≤ 1 := by simpa [Real.dist_0_eq_abs] using hr
      rw [hFx]
      refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (N := ∞) (hgs r) (f.smooth ⊤) v
        (mod_cast le_top)) (by positivity)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : ‖iteratedFDeriv ℝ i (g r) v‖ ≤ |M i| := by
        refine (hgb i r v).trans ?_
        refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
        exact mul_le_of_le_one_right (abs_nonneg _)
          (pow_le_one₀ (norm_nonneg _) ((hLn r).trans hr1))
      have h2 := SchwartzMap.le_seminorm ℂ k (n - i) f v
      calc ‖v‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (g r) v‖ * ‖iteratedFDeriv ℝ (n - i) (⇑f) v‖)
          = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (g r) v‖ * (‖v‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (⇑f) v‖) := by ring
        _ ≤ (n.choose i : ℝ) * |M i| * SchwartzMap.seminorm ℂ k (n - i) f :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (by positivity) (by positivity)
  have ht : Tendsto F (𝓝[≠] 0) (𝓝 f) := by
    rw [← hF0]; exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun r hr => ?_)
  have hr0 : r ≠ 0 := hr
  show HasCompactSupport (F r : V → ℂ)
  rw [hFx]
  have hgc : HasCompactSupport (g r) := by
    have : g r = fun x => ((χ (r • x) : ℝ) : ℂ) := funext (hgx r)
    rw [this]
    exact (hχc.comp_smul hr0).comp_left Complex.ofReal_zero
  exact hgc.mul_right

end GlobalTheory
end

