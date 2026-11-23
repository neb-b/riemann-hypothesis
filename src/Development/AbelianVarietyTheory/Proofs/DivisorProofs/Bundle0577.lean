module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFormalGroupLawEvalPointsOfDegreeLeOne
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.QLog.OpLin

variable {R : Type} [CommRing R]

theorem degree_eq_one {σ : Type} [Fintype σ] {D : σ →₀ ℕ} (h : D.degree = 1) :
    ∃ s, D = Finsupp.single s 1 := by
  classical
  have hsum := h
  rw [Finsupp.degree_eq_sum] at hsum
  obtain ⟨s, hs⟩ : ∃ s, D s ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at hsum
  refine ⟨s, ?_⟩
  have hle : ∀ t, t ≠ s → D s + D t ≤ 1 := fun t ht => by
    rw [← hsum, ← Finset.sum_pair (Ne.symm ht)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  ext t
  by_cases ht : t = s
  · subst ht
    have : D t ≤ 1 := h ▸ Finsupp.le_degree t D
    simp only [Finsupp.single_eq_same]
    omega
  · have := hle t ht
    simp only [Finsupp.single_apply, if_neg (Ne.symm ht)]
    omega

theorem le_order_prod_pow {σ τ : Type} {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (D : σ →₀ ℕ) :
    (D.degree : ℕ∞) ≤ (D.prod fun s e => a s ^ e).order := by
  refine le_trans ?_ (le_order_prod _ _)
  rw [Finsupp.degree_apply, Nat.cast_sum]
  exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (ha s)

theorem coeff_subst_of_degree_le_one {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0)
    {β : τ →₀ ℕ} (hβ : β.degree ≤ 1) :
    coeff β (subst a f) = ∑ s, coeff (Finsupp.single s 1) f * coeff β (a s) := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst hs]
  have hsupp : (Function.support fun D : σ →₀ ℕ =>
      coeff D f • coeff β (D.prod fun s e => a s ^ e)) ⊆
      ((Finset.univ.image fun s : σ => Finsupp.single s 1 : Finset (σ →₀ ℕ)) : Set (σ →₀ ℕ)) := by
    intro D hD
    rw [Function.mem_support] at hD
    have h0 : D ≠ 0 := by
      rintro rfl
      apply hD
      rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    have h1 : D.degree ≤ 1 := by
      by_contra hlt
      push_neg at hlt
      apply hD
      rw [coeff_of_lt_order (lt_of_lt_of_le ?_ (le_order_prod_pow ha D)), smul_zero]
      exact_mod_cast lt_of_le_of_lt hβ hlt
    have h2 : D.degree = 1 := by
      have : D.degree ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff D).1 h)
      omega
    obtain ⟨s, rfl⟩ := degree_eq_one h2
    simp
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun s _ t _ h => Finsupp.single_left_injective one_ne_zero h)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.prod_single_index (by simp), pow_one, smul_eq_mul]

end GlobalTheory.QLog.OpLin

namespace GlobalTheory.QLog.OpLin

variable {B O : Type} [CommRing B] [CommRing O] {d : ℕ}

theorem coeff_inl {θ : B →+* O} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ)
    (i j : Fin d) : coeff (Finsupp.single (Sum.inl j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single j 1)) (congrFun hμ.unit i)
  simp only [op, at2] at h
  rw [coeff_subst_of_degree_le_one (by rintro (s | s) <;> simp) (hμ.const i)
    (by simp), Fintype.sum_sum_type] at h
  simpa [coeff_X, Finsupp.single_left_inj one_ne_zero, eq_comm] using h

theorem coeff_inr {θ : B →+* O} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : IsLift θ μ)
    (i j : Fin d) : coeff (Finsupp.single (Sum.inr j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) (hμ.comm i)
  simp only [swap, at2] at h
  rw [coeff_subst_of_degree_le_one (by rintro (s | s) <;> simp) (hμ.const i)
    (by simp), Fintype.sum_sum_type] at h
  rw [← h, ← coeff_inl hμ i j]
  simp [coeff_X, Finsupp.single_left_inj one_ne_zero]

theorem coeff_op_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type}
    (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) →
    (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 →
    coeff β (op μ u v i) = coeff β (u i + v i) := by
  intro B O _ _ θ d μ hμ τ u v hu hv i β hβ
  classical
  simp only [op, at2]
  rw [coeff_subst_of_degree_le_one (by rintro (s | s); exacts [hu s, hv s]) (hμ.const i) hβ,
    Fintype.sum_sum_type, map_add]
  simp [coeff_inl hμ, coeff_inr hμ]

end GlobalTheory.QLog.OpLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPLogarithmsEqInvFrobeniusMatrix
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobCoef

theorem coeff_frob_single (p : ℕ) [hp : Fact p.Prime] {Q : Type} [CommRing Q] {d : ℕ}
    (s : Q →+* Q) (f : MvPowerSeries (Fin d) Q) (j : Fin d) :
    coeff (Finsupp.single j p) (frob p s f) = s (lin f j) := by
  classical
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hs : HasSubst (fun i => (X i : MvPowerSeries (Fin d) Q) ^ p) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [hp0]
  rw [frob, coeff_subst hs]
  have key : ∀ e : Fin d →₀ ℕ, (e.prod fun i n => ((X i : MvPowerSeries (Fin d) Q) ^ p) ^ n) =
      monomial (p • e) 1 := by
    intro e
    induction e using Finsupp.induction with
    | zero => simp
    | single_add i n e hi hn ih =>
      rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.prod_single_index
        (by simp), ← pow_mul, X_pow_eq, monomial_mul_monomial, one_mul, smul_add,
        Finsupp.smul_single, smul_eq_mul]
  simp_rw [key]
  rw [finsum_eq_single _ (Finsupp.single j 1)]
  · rw [coeff_monomial, if_pos (by rw [Finsupp.smul_single, smul_eq_mul, mul_one]), smul_eq_mul,
      mul_one, coeff_map, lin]
  · intro e he
    rw [coeff_monomial, if_neg, smul_zero]
    intro h
    apply he
    ext i
    have := congrArg (fun g => g i) h
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at this ⊢
    split_ifs at this ⊢ with h1
    · exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) (this.symm.trans (mul_one p).symm)
    · exact (mul_eq_zero.1 this.symm).resolve_left hp0

theorem coef_logs_inv_frob : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (s : Q →+* Q) (σ : B →+* B), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → Function.Injective (algebraMap B Q) → ∀ (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B), IsUnit U → (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : B)}) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e)) → (∀ a, lin (e (Sum.inl a)) = Pi.single a 1) → (∀ r j, ∃ b, lin (e r) j = algebraMap B Q b) → ∃ c : Fin d → Fin d → B, ∀ a j, algebraMap B Q (c a j) = (p : Q) * coeff (Finsupp.single j p) (e (Sum.inl a)) ∧ ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b := by
  intro p _ B Q _ _ _ s σ hs _ d k e U hU h hlin hint
  classical
  set x : Fin d → Fin d ⊕ Fin k → Q := fun j l => (p : Q) * coeff (Finsupp.single j p) (e l) with hx
  have hD : ∀ l i, (U * blk d k (p : B) 1) l i =
      U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i := by
    intro l i
    simp [blk, Matrix.mul_diagonal]
  have hco : ∀ i j, coeff (Finsupp.single j p)
      (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) =
      s (lin (e i) j) - ∑ l, algebraMap B Q (U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i) *
        coeff (Finsupp.single j p) (e l) := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, GlobalTheory.FrobCoef.coeff_frob_single, comb, map_sum]
    simp_rw [coeff_smul, hD]
  have key : ∀ j, ∃ y : Fin d ⊕ Fin k → B, (∀ i, ∑ l, algebraMap B Q (U l i) * x j l =
      algebraMap B Q (y i)) ∧ ∀ i, ∃ t, y i - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t := by
    intro j
    have H : ∀ i, ∃ yi : B, ∑ l, algebraMap B Q (U l i) * x j l = algebraMap B Q yi ∧
        ∃ t, yi - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t := by
      rintro (a | r)
      · obtain ⟨b, hb, hbe⟩ := (h (Sum.inl a)).2 a rfl (Finsupp.single j p)
        obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.1 hb
        rw [hco, hlin] at hbe
        refine ⟨(Pi.single a (1 : B) : Fin d → B) j - β * p, ?_, -β, ?_⟩
        · have h1 : s ((Pi.single a (1 : Q) : Fin d → Q) j) = algebraMap B Q ((Pi.single a (1 : B) : Fin d → B) j) := by
            by_cases haj : j = a
            · subst haj; simp
            · simp [Pi.single_apply, haj]
          have hS : ∑ l, algebraMap B Q (U l (Sum.inl a)) * x j l = ∑ l, algebraMap B Q
              (U l (Sum.inl a) * (p : B)) * coeff (Finsupp.single j p) (e l) :=
            Finset.sum_congr rfl fun l _ => by simp only [hx, Sum.elim_inl, map_mul, map_natCast]; ring
          simp only [Sum.elim_inl] at hbe
          rw [hS, map_sub, ← h1]
          linear_combination -hbe
        · by_cases haj : a = j
          · subst haj; simp; ring
          · simp [Pi.single_apply, haj, Ne.symm haj]; ring
      · obtain ⟨b1, -, hb1⟩ := (h (Sum.inr r)).1 (Finsupp.single j p)
        obtain ⟨b0, hb0⟩ := hint (Sum.inr r) j
        rw [hco, hb0, hs] at hb1
        refine ⟨p * (σ b0 - b1), ?_, σ b0 - b1, by simp⟩
        simp only [Sum.elim_inr, mul_one] at hb1
        have : ∑ l, algebraMap B Q (U l (Sum.inr r)) * coeff (Finsupp.single j p) (e l) =
            algebraMap B Q (σ b0 - b1) := by
          rw [map_sub, ← hb1]; ring
        simp only [hx, map_mul, map_natCast, ← this, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
    choose y hy1 hy2 using H
    exact ⟨y, hy1, hy2⟩
  choose y hy1 hy2 using key
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)
  refine ⟨fun a j => ∑ i, U⁻¹ i (Sum.inl a) * y j i, fun a j => ⟨?_, ?_⟩⟩
  · have : ∀ m, algebraMap B Q (∑ i, U⁻¹ i m * y j i) = x j m := by
      intro m
      calc algebraMap B Q (∑ i, U⁻¹ i m * y j i)
          = ∑ i, algebraMap B Q (U⁻¹ i m) * ∑ l, algebraMap B Q (U l i) * x j l := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [map_sum, map_mul, hy1]
        _ = ∑ l, algebraMap B Q ((U * U⁻¹) l m) * x j l := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
        _ = x j m := by
            rw [hUU]
            simp [Matrix.one_apply]
    exact this _
  · choose t ht using hy2 j
    refine ⟨∑ i, U⁻¹ i (Sum.inl a) * t i, ?_⟩
    have h1 : U⁻¹ (Sum.inl j) (Sum.inl a) = ∑ i, U⁻¹ i (Sum.inl a) * (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i := by
      simp [Pi.single_apply]
    rw [h1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, ht i]; ring

end GlobalTheory.FrobCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowFirstAddSecondThreeGroups
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.BinomLeft

variable {R : Type} [CommRing R] {d : ℕ}

theorem natCast_eq_monomial {σ : Type} (n : ℕ) : ((n : ℕ) : MvPowerSeries σ R) = monomial 0 (n : R) := by
  rw [monomial_zero_eq_C_apply, map_natCast]

theorem pow_threeGroupsFirst_add_second_expansion (i : Fin d) (k : ℕ) :
    ((x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        monomial (Finsupp.single (Sum.inl i) j + Finsupp.single (Sum.inr (Sum.inl i)) (k - j)) (k.choose j : R) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [x1, x2, X_pow_eq, monomial_mul_monomial, one_mul, natCast_eq_monomial, add_zero, mul_one]

theorem expo_iff (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) (p : Fin d → ℕ)
    (hp : ∀ i, p i ≤ α (Sum.inl i)) :
    Finsupp.sumElim a (Finsupp.sumElim b e) =
        (∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) +
          ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) ↔
      α = Finsupp.sumElim (a + b) e ∧ p = ⇑a := by
  classical
  have hv : ∀ s, ((∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) +
          ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ) s =
        Sum.elim p (Sum.elim (fun i => α (Sum.inl i) - p i) (fun i => α (Sum.inr i))) s := by
    intro s
    rcases s with i | i | i
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj, Ne.symm hj]) (by simp)]
      simp
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  constructor
  · intro h
    have h1 : ∀ i, a i = p i := fun i => by
      have := DFunLike.congr_fun h (Sum.inl i); rw [hv] at this; simpa using this
    have h2 : ∀ i, b i = α (Sum.inl i) - p i := fun i => by
      have := DFunLike.congr_fun h (Sum.inr (Sum.inl i)); rw [hv] at this; simpa using this
    have h3 : ∀ i, e i = α (Sum.inr i) := fun i => by
      have := DFunLike.congr_fun h (Sum.inr (Sum.inr i)); rw [hv] at this; simpa using this
    refine ⟨?_, funext fun i => (h1 i).symm⟩
    ext s
    rcases s with i | i
    · have := hp i; have := h1 i; have := h2 i; simp; omega
    · simp [h3 i]
  · rintro ⟨rfl, rfl⟩
    ext s
    rw [hv]
    rcases s with i | i | i <;> simp

theorem coeff_prod_pow_add (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e))
        (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) =
      if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, pow_threeGroupsFirst_add_second_expansion]
  rw [Finset.prod_univ_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [x3, X_pow_eq, prod_monomial, Finset.sum_mul, monomial_mul_monomial, mul_one, map_sum,
    coeff_monomial, Finset.prod_const_one]
  have hmem : ∀ p ∈ Fintype.piFinset fun i => Finset.range (α (Sum.inl i) + 1), ∀ i, p i ≤ α (Sum.inl i) := by
    intro p hp i
    have := Fintype.mem_piFinset.1 hp i
    rw [Finset.mem_range] at this
    omega
  split_ifs with hα
  · rw [Finset.sum_congr rfl fun p hp => by rw [if_congr (expo_iff α a b e p (hmem p hp)) rfl rfl]]
    simp only [hα, true_and]
    rw [Finset.sum_ite_eq']
    rw [if_pos]
    · simp
    · rw [Fintype.mem_piFinset]
      intro i
      simp only [Finset.mem_range, Finsupp.sumElim_apply, Sum.elim_inl, Finsupp.coe_add, Pi.add_apply]
      omega
  · refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg]
    intro h
    exact hα ((expo_iff α a b e p (hmem p hp)).1 h).1

end GlobalTheory.BinomLeft
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowSecondAddThirdThreeGroups
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.BinomRight

theorem prod_monomial' {R σ ι : Type} [CommRing R] (s : Finset ι) (n : ι → σ →₀ ℕ) (c : ι → R) :
    ∏ i ∈ s, (monomial (n i) (c i) : MvPowerSeries σ R) =
      monomial (∑ i ∈ s, n i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [monomial_zero_eq_C]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, ih, monomial_mul_monomial, Finset.sum_insert hj, Finset.prod_insert hj]

theorem add_pow_X' {R σ : Type} [CommRing R] (u v : σ) (k : ℕ) :
    ((X u + X v : MvPowerSeries σ R)) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        monomial (Finsupp.single u j + Finsupp.single v (k - j)) (k.choose j : R) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, ← map_natCast (C (σ := σ) (R := R)),
    ← monomial_zero_eq_C, monomial_mul_monomial, add_zero]
  simp only [one_mul]

end GlobalTheory.BinomRight

namespace GlobalTheory.BinomRight

variable {R : Type} [CommRing R] {d : ℕ}

def expo (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ :=
  (∑ i, Finsupp.single (Sum.inl i) (α (Sum.inl i))) +
    ∑ i, (Finsupp.single (Sum.inr (Sum.inl i)) (J i) +
      Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i) - J i))

theorem expo_inl (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) (i : Fin d) :
    expo α J (Sum.inl i) = α (Sum.inl i) := by
  classical
  simp [expo, Finsupp.single_apply]

theorem expo_inr_inl (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) (i : Fin d) :
    expo α J (Sum.inr (Sum.inl i)) = J i := by
  classical
  simp [expo, Finsupp.single_apply]

theorem expo_inr_inr (α : Fin d ⊕ Fin d →₀ ℕ) (J : Fin d → ℕ) (i : Fin d) :
    expo α J (Sum.inr (Sum.inr i)) = α (Sum.inr i) - J i := by
  classical
  simp [expo, Finsupp.single_apply]
  rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
  simp

theorem prod_eq_sum (α : Fin d ⊕ Fin d →₀ ℕ) :
    (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) =
      ∑ J ∈ Fintype.piFinset (fun i => Finset.range (α (Sum.inr i) + 1)),
        monomial (expo α J) (∏ i, ((α (Sum.inr i)).choose (J i) : R)) := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, x1, x2, x3, X_pow_eq, add_pow_X', prod_monomial']
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [prod_monomial', monomial_mul_monomial, Finset.prod_const_one, one_mul, expo]

end GlobalTheory.BinomRight

namespace GlobalTheory.BinomRight

variable {R : Type} [CommRing R] {d : ℕ}

theorem sumElim_eq_expo_iff (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) (J : Fin d → ℕ)
    (hJ : ∀ i, J i ≤ α (Sum.inr i)) :
    Finsupp.sumElim a (Finsupp.sumElim b e) = expo α J ↔
      α = Finsupp.sumElim a (b + e) ∧ J = ⇑b := by
  constructor
  · intro h
    have h1 := fun i => DFunLike.congr_fun h (Sum.inl i)
    have h2 := fun i => DFunLike.congr_fun h (Sum.inr (Sum.inl i))
    have h3 := fun i => DFunLike.congr_fun h (Sum.inr (Sum.inr i))
    simp only [expo_inl, expo_inr_inl, expo_inr_inr, Finsupp.sumElim_apply, Sum.elim_inl,
      Sum.elim_inr] at h1 h2 h3
    have hJb : J = ⇑b := funext fun i => (h2 i).symm
    refine ⟨Finsupp.ext fun s => ?_, hJb⟩
    rcases s with i | i
    · simp [h1 i]
    · have := h3 i; have := hJ i; have := h2 i
      simp only [Finsupp.sumElim_apply, Sum.elim_inr, Finsupp.add_apply]
      omega
  · rintro ⟨rfl, rfl⟩
    refine Finsupp.ext fun s => ?_
    rcases s with i | i | i
    · simp [expo_inl]
    · simp [expo_inr_inl]
    · simp [expo_inr_inr]

end GlobalTheory.BinomRight

namespace GlobalTheory.BinomRight

theorem coeff_prod_pow_second_add_third_threeGroups {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ)
    (a b e : Fin d →₀ ℕ) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e))
        (α.prod fun s k => (Sum.elim x1
          (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) =
      if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [prod_eq_sum, map_sum]
  simp only [coeff_monomial]
  have hmem : ∀ J ∈ Fintype.piFinset (fun i => Finset.range (α (Sum.inr i) + 1)),
      ∀ i, J i ≤ α (Sum.inr i) := fun J hJ i =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hJ i))
  by_cases hα : α = Finsupp.sumElim a (b + e)
  · rw [if_pos hα]
    have hb : ⇑b ∈ Fintype.piFinset (fun i => Finset.range (α (Sum.inr i) + 1)) := by
      refine Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 ?_
      rw [hα]; simp
    rw [Finset.sum_eq_single_of_mem (⇑b) hb]
    · rw [if_pos ((sumElim_eq_expo_iff α a b e _ (hmem _ hb)).2 ⟨hα, rfl⟩)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hα]; simp
    · intro J hJ hJb
      rw [if_neg fun h => hJb ((sumElim_eq_expo_iff α a b e J (hmem J hJ)).1 h).2]
  · rw [if_neg hα]
    refine Finset.sum_eq_zero fun J hJ => ?_
    rw [if_neg fun h => hα ((sumElim_eq_expo_iff α a b e J (hmem J hJ)).1 h).1]

end GlobalTheory.BinomRight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBotStatement
section
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_columnCharacter_eigenSubmodule_ne_bot : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), Monotone b → (∀ p : blockTri (κ := F) b, (∀ i j, b i = b j → ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1) → ∀ k : Fin r, eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ → ∃ l : Fin r → F, (∀ i, l i ≠ 0 → i < k ∧ b i = b k) ∧ eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | exact GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | (intros; apply GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot <;> assumption)
end

