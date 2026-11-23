module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0635
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshNormalFrameQuadraticComparison
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem leviV_re_le_sum_norm {n : ℕ} (g : V n → ℂ) (p ζ : V n) :
    (leviV n g p ζ.ofLp).re ≤
      (∑ j, ∑ k, ‖wd n j (wdb n k g) p‖) * ‖ζ‖ ^ 2 := by
  calc (leviV n g p ζ.ofLp).re ≤ ‖leviV n g p ζ.ofLp‖ := Complex.re_le_norm _
    _ ≤ ∑ j, ‖∑ k, wd n j (wdb n k g) p * ζ.ofLp j * (starRingEnd ℂ) (ζ.ofLp k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j, ∑ k, ‖wd n j (wdb n k g) p‖ * ‖ζ‖ ^ 2 := by
        gcongr with j _
        refine (norm_sum_le _ _).trans ?_
        gcongr with k _
        rw [norm_mul, norm_mul, Complex.norm_conj, sq, ← mul_assoc]
        have hj : ‖ζ.ofLp j‖ ≤ ‖ζ‖ := PiLp.norm_apply_le ζ j
        have hk : ‖ζ.ofLp k‖ ≤ ‖ζ‖ := PiLp.norm_apply_le ζ k
        gcongr
    _ = (∑ j, ∑ k, ‖wd n j (wdb n k g) p‖) * ‖ζ‖ ^ 2 := by
        simp only [Finset.sum_mul]

theorem psh_normal_frame : ∀ (n : ℕ) (O : Set (V n)) (φ : V n → ℝ) (p : V n), IsOpen O → p ∈ O → ContDiffOn ℝ ∞ φ O → (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => ((φ w : ℝ) : ℂ)) p ξ).re) → ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧ closedBall p ρ ⊆ O ∧ ∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ φ v - 2 * (q v).re ∧ φ v - 2 * (q v).re ≤ C * ‖v - p‖ ^ 2 := by
  intro n O φ p hO hp hφ hlevi
  set g : V n → ℂ := fun w => ((φ w : ℝ) : ℂ) with hg
  have hgs : ContDiffOn ℝ ∞ g O := Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  obtain ⟨m, hm, hmb⟩ := levi_pos_compact (g := g) hO hgs (K0 := {p}) isCompact_singleton
    (Set.singleton_subset_iff.2 hp) (fun u hu ζ hζ => by
      rw [Set.mem_singleton_iff.1 hu]
      refine hlevi _ ?_
      intro h0; apply hζ
      exact (WithLp.ofLp_eq_zero 2).1 h0)
  have hφ2 : ContDiffAt ℝ 2 φ p :=
    ((hφ.contDiffAt (hO.mem_nhds hp)).of_le (by norm_cast))
  obtain ⟨q, hq, ho⟩ := _root_.GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi n φ p hφ2
  set A : ℝ := ∑ j, ∑ k, ‖wd n j (wdb n k g) p‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _
  have hev := ho.def (half_pos hm)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨ε2, hε2, hε2O⟩ := Metric.isOpen_iff.1 hO p hp
  refine ⟨q, m / 2, A + m / 2, min ε ε2 / 2, hq, half_pos hm, by positivity,
    by positivity, ?_, ?_⟩
  · intro v hv
    apply hε2O
    rw [mem_closedBall] at hv
    rw [mem_ball]
    have : min ε ε2 / 2 < ε2 := by
      have := min_le_right ε ε2; linarith [lt_min hε hε2]
    linarith
  · intro v hv
    rw [mem_closedBall] at hv
    have hvε : dist v p < ε := by
      have := min_le_left ε ε2; linarith [lt_min hε hε2]
    have hR := hεb hvε
    rw [Real.norm_eq_abs, norm_pow, norm_norm] at hR
    have hlo := hmb p rfl (v - p)
    have hup := leviV_re_le_sum_norm g p (v - p)
    have habs := abs_le.1 hR
    change m * ‖v - p‖ ^ 2 ≤ (leviV n g p (fun j => (v - p) j)).re at hlo
    change (leviV n g p (fun j => (v - p) j)).re ≤ A * ‖v - p‖ ^ 2 at hup
    constructor <;> nlinarith [habs.1, habs.2, sq_nonneg ‖v - p‖]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogFirstBlockSmallOfFrobenius
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.SmallFirst

theorem coeff_single_frob {Q : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {d : ℕ}
    (f : MvPowerSeries (Fin d) Q) (i : Fin d) :
    coeff (Finsupp.single i p) (frob p s f) = s (lin f i) := by
  have h1 : frob p s f = expand p hp (map s f) := by
    rw [frob, expand, substAlgHom_apply]
  have h2 : (Finsupp.single i p : Fin d →₀ ℕ) = p • Finsupp.single i 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1, h2, coeff_expand_smul, coeff_map, lin]

theorem coeff_comb {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ ι : Type} [Fintype ι]
    (b : ι → B) (e : ι → MvPowerSeries σ Q) (α : σ →₀ ℕ) :
    coeff α (comb b e) = ∑ l, algebraMap B Q (b l) * coeff α (e l) := by
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [MvPowerSeries.coeff_smul]

end GlobalTheory.QLog.SmallFirst

theorem GlobalTheory.QLog.small_first_of_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) → ∀ i, ¬IsUnit (F.θ (w (Sum.inl i))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbas hadp U hU w hw i
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsLocalRing O := ValuationRing.isLocalRing O
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set J : Ideal F.B := Ideal.comap F.θ (IsLocalRing.maximalIdeal O) with hJ
  have memJ : ∀ x, x ∈ J ↔ ¬IsUnit (F.θ x) := fun x => by
    rw [hJ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hpJ : (p : F.B) ∈ J := by
    rw [memJ, map_natCast]; exact Fact.out
  haveI hJp : J.IsPrime := Ideal.IsPrime.comap F.θ
  set α : Fin d →₀ ℕ := Finsupp.single i p with hα

  have hc : ∀ l, ∃ cl : F.B, (p : F.Q) * coeff α (e l) = algebraMap F.B F.Q cl := by
    intro l
    obtain ⟨b, -, hb⟩ := GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hlift ⊤ (e l) (hbas.1 l) α i
    refine ⟨b, ?_⟩
    rw [← hb, hα, Finsupp.single_eq_same]
  choose cc hcc using hc
  have key : ∀ m, algebraMap F.B F.Q (∑ l, U l m * cc l) =
      (p : F.Q) * ∑ l, algebraMap F.B F.Q (U l m) * coeff α (e l) := by
    intro m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← hcc]; ring
  have hcol : ∀ m l, (U * blk d k (p : F.B) 1) l m = U l m * Sum.elim (fun _ => (p : F.B)) (fun _ => 1) m := by
    intro m l
    rw [blk, Matrix.mul_diagonal]
  have hR : ∀ m, (∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0) ∈ J := by
    intro m
    cases m with
    | inl i' =>
      obtain ⟨t, ht, hteq⟩ := (hU (Sum.inl i')).2 i' rfl α
      obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 ht
      rw [map_sub, SmallFirst.coeff_single_frob p hp0, (hadp i').2, SmallFirst.coeff_comb] at hteq
      have hs : F.s (Pi.single (M := fun _ : Fin d => F.Q) i' 1 i) =
          algebraMap F.B F.Q (if (Sum.inl i' : Fin d ⊕ Fin k) = Sum.inl i then 1 else 0) := by
        by_cases h : i' = i
        · subst h; simp
        · have h' : i ≠ i' := Ne.symm h
          simp [Pi.single_apply, h', h]
      have hsum : ∑ l, algebraMap F.B F.Q ((U * blk d k (p : F.B) 1) l (Sum.inl i')) * coeff α (e l) =
          algebraMap F.B F.Q (∑ l, U l (Sum.inl i') * cc l) := by
        rw [key, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcol, Sum.elim_inl, map_mul, map_natCast]; ring
      rw [hs, hsum, ← map_sub] at hteq
      have := F.frame.inj hteq
      have h2 : (∑ l, U l (Sum.inl i') * cc l) - (if (Sum.inl i' : Fin d ⊕ Fin k) = Sum.inl i then 1 else 0)
          = -(t' * p) := by rw [← this]; ring
      rw [h2]
      exact J.neg_mem (J.mul_mem_left _ hpJ)
    | inr j =>
      obtain ⟨b, -, hb⟩ := (hbas.1 (Sum.inr j)).2.1 i
      obtain ⟨t, -, hteq⟩ := (hU (Sum.inr j)).1 α
      rw [map_sub, SmallFirst.coeff_single_frob p hp0, hb, F.s_alg, SmallFirst.coeff_comb] at hteq
      have hsum : ∑ l, algebraMap F.B F.Q ((U * blk d k (p : F.B) 1) l (Sum.inr j)) * coeff α (e l) =
          ∑ l, algebraMap F.B F.Q (U l (Sum.inr j)) * coeff α (e l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcol, Sum.elim_inr, mul_one]
      rw [hsum] at hteq
      have h3 : algebraMap F.B F.Q (∑ l, U l (Sum.inr j) * cc l) =
          algebraMap F.B F.Q ((p : F.B) * (F.σ b - t)) := by
        rw [key, map_mul, map_sub, map_natCast, ← hteq]; ring
      have h4 := F.frame.inj h3
      have hne : (Sum.inr j : Fin d ⊕ Fin k) ≠ Sum.inl i := Sum.inr_ne_inl
      rw [if_neg hne, sub_zero, h4]
      exact J.mul_mem_right _ hpJ

  have hW : ∑ m, F.σ (w m) * ∑ l, U l m * cc l ∈ J := by
    have : ∑ m, F.σ (w m) * ∑ l, U l m * cc l = ∑ l, U.mulVec (fun j => F.σ (w j)) l * cc l := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [this]
    exact J.sum_mem fun l _ => J.mul_mem_right _ ((memJ _).2 (hw l))
  have hD : ∑ m, F.σ (w m) * ((∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0)) ∈ J :=
    J.sum_mem fun m _ => J.mul_mem_left _ (hR m)
  have hσ : F.σ (w (Sum.inl i)) ∈ J := by
    have : F.σ (w (Sum.inl i)) = (∑ m, F.σ (w m) * ∑ l, U l m * cc l) -
        ∑ m, F.σ (w m) * ((∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    rw [this]
    exact J.sub_mem hW hD
  obtain ⟨z, hz⟩ := F.σ_pow (w (Sum.inl i))
  have hpow : w (Sum.inl i) ^ p ∈ J := by
    have : w (Sum.inl i) ^ p = F.σ (w (Sum.inl i)) - p * z := by rw [← hz]; ring
    rw [this]
    exact J.sub_mem hσ (J.mul_mem_right _ hpJ)
  exact (memJ _).1 (hJp.mem_of_pow_mem p hpow)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogLiftPdivGroupFrame
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.FrobQL

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem in_add {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f + g) := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  obtain ⟨b, hb, e'⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add (f := _), e, e', map_add (f := _)]⟩

theorem in_mono {σ : Type} {N N' : Ideal B} (h : N ≤ N') {f : MvPowerSeries σ Q} (hf : In N f) :
    In N' f := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  exact ⟨a, h ha, e⟩

theorem in_map {σ : Type} (t : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (t b))
    {N N' : Ideal B} (hN : ∀ b ∈ N, t b ∈ N') {f : MvPowerSeries σ Q} (hf : In N f) :
    In N' (map s f) := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  exact ⟨t a, hN a ha, by rw [coeff_map, e, hs]⟩

theorem in_expand {σ : Type} (p : ℕ) (hp : p ≠ 0) {N : Ideal B} {f : MvPowerSeries σ Q}
    (hf : In N f) : In N (expand p hp f) := fun α => by
  by_cases h : ∀ i, p ∣ α i
  · obtain ⟨m, hm⟩ : ∃ m : σ →₀ ℕ, p • m = α := ⟨α.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [Nat.mul_div_cancel' (h i)]⟩
    rw [← hm, coeff_expand_smul]
    exact hf m
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    exact ⟨0, N.zero_mem, by rw [coeff_expand_of_not_dvd p hp f hi, map_zero]⟩

theorem frob_congr (p : ℕ) [Fact p.Prime] (t : B →+* B) (ht : ∀ b, (p : B) ∣ t b - b ^ p)
    (hu : ¬IsUnit (p : B)) {τ : Type} (w : MvPowerSeries τ B) (α : τ →₀ ℕ) :
    coeff α (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) ∈
      Ideal.span {(p : B)} := by
  set I : Ideal B := Ideal.span {(p : B)}
  haveI : CharP (B ⧸ I) p := CharP.quotient B p (by simpa [mem_nonunits_iff] using hu)
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime Fact.out
  have hw : map (Ideal.Quotient.mk I) (map t w) =
      map (frobenius (B ⧸ I) p) (map (Ideal.Quotient.mk I) w) := by
    ext n
    simp only [coeff_map, frobenius_def]
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ht _
  have key : map (Ideal.Quotient.mk I)
      (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) = 0 := by
    rw [map_sub, map_pow, map_expand, hw, ← map_expand, map_frobenius_expand, sub_self]
  have := congrArg (coeff α) key
  rwa [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this

end GlobalTheory.QLog.FrobQL

namespace GlobalTheory.QLog.FrobQL

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem frob_eq_expand (p : ℕ) (hp : p ≠ 0) {σ : Type} (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  simp only [frob, expand, substAlgHom_apply]

theorem cob1_expand_frobenius_map (p : ℕ) (hp : p ≠ 0) (t : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (t b)) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (h0 : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    cob1 (up Q μ) (expand p hp (map s f)) =
      (subst (up Q fun i => μ i ^ p) (map s f) -
        subst (up Q fun i => expand p hp (map t (μ i))) (map s f)) +
        expand p hp (map s (cob1 (up Q μ) f)) := by
  have hU : HasSubst (up Q μ) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have hXp : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hexp : ∀ {σ : Type} (g : MvPowerSeries σ Q), expand p hp g = subst (fun i => X i ^ p) g :=
    fun g => by simp only [expand, substAlgHom_apply]
  have hmapU : (fun i => map s (up Q μ i)) = up Q (fun i => map t (μ i)) := by
    funext i; ext n; simp [up, coeff_map, hs]
  have e1 : subst (up Q μ) (expand p hp (map s f)) = subst (up Q fun i => μ i ^ p) (map s f) := by
    rw [hexp, subst_comp_subst_apply hXp hU]
    congr 1
    funext i
    rw [subst_pow hU, subst_X hU]
    simp [up, map_pow]
  have e2 : inL (expand p hp (map s f)) = subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [inL, hexp, subst_comp_subst_apply hXp hL]
    congr 1
    funext i
    rw [subst_pow hL, subst_X hL]
  have e3 : inR (expand p hp (map s f)) = subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [inR, hexp, subst_comp_subst_apply hXp hR]
    congr 1
    funext i
    rw [subst_pow hR, subst_X hR]
  have hV : HasSubst (up Q fun i => map t (μ i)) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have m1 : map s (subst (up Q μ) f) = subst (up Q fun i => map t (μ i)) (map s f) := by
    rw [map_subst hU, hmapU]
  have m2 : map s (subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) f) =
      subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f) := by
    rw [map_subst hL]; congr 1; funext i; simp
  have m3 : map s (subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) f) =
      subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f) := by
    rw [map_subst hR]; congr 1; funext i; simp
  have x1 : expand p hp (subst (up Q fun i => map t (μ i)) (map s f)) =
      subst (up Q fun i => expand p hp (map t (μ i))) (map s f) := by
    rw [expand_subst p hp hV]; congr 1; funext i; simp [up, map_expand]
  have x2 : expand p hp (subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f)) =
      subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [expand_subst p hp hL]; congr 1; funext i; simp
  have x3 : expand p hp (subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f)) =
      subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [expand_subst p hp hR]; congr 1; funext i; simp
  have e4 : expand p hp (map s (cob1 (up Q μ) f)) =
      subst (up Q fun i => expand p hp (map t (μ i))) (map s f) -
        subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) -
        subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    simp only [cob1, inL, inR, map_sub, m1, m2, m3, x1, x2, x3]
  rw [cob1, e1, e2, e3, e4]
  abel

end GlobalTheory.QLog.FrobQL

namespace GlobalTheory.QLog


open GlobalTheory.QLog.FrobQL in
theorem ql_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' →
    (∀ i, map F.θ (μ' i) = c.μ i) → ∀ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f →
    QL μ' ⊤ (frob p F.s f) ∧
      (In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) →
        QL μ' (Ideal.span {(p : F.B)}) (frob p F.s f)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε F G d c μ' hμ _ f hf
  have hpp : p.Prime := Fact.out
  have hp : p ≠ 0 := hpp.ne_zero
  have hu : ¬IsUnit (p : F.B) := fun h =>
    (Fact.out : ¬IsUnit (p : O)) (by simpa using h.map F.θ)
  rw [frob_eq_expand p hp]
  have hc0 : constantCoeff (expand p hp (map F.s f)) = 0 := by
    rw [constantCoeff_expand, constantCoeff_map, hf.1, map_zero]
  have hlin : ∀ i, lin (expand p hp (map F.s f)) i = 0 := fun i => by
    unfold lin
    exact coeff_expand_of_not_dvd p hp _ (i := i) (by simpa using hpp.not_dvd_one)
  have hJ : ∀ x ∈ Ideal.span {(p : F.B)}, ∃ y ∈ Ideal.span {(p : F.B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have e : (p : F.B) ^ p = p * p ^ (p - 1) := by
      rw [← pow_succ']; congr 1; have := hpp.one_lt; omega
    refine ⟨(p : F.B) ^ (p - 1) * b ^ p, Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hpp.one_lt; omega)), ?_⟩
    rw [mul_pow, e]; ring
  have hD : DIn (⊤ : Ideal F.B) (map F.s f) := by
    have h := _root_.GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hμ ⊤ f hf
    intro α i
    obtain ⟨b, _, e⟩ := h α i
    exact ⟨F.σ b, trivial, by rw [coeff_map, ← map_natCast F.s, ← map_mul, e, F.s_alg]⟩
  have hK := GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem p F.B O F.Q F.θ F.frame _ hJ (Fin d) (Fin d ⊕ Fin d) ⊤ (map F.s f)
    (fun i => μ' i ^ p) (fun i => expand p hp (map F.σ (μ' i))) hD
    (fun i => by rw [map_pow, hμ.const i, zero_pow hp])
    (fun i => by rw [constantCoeff_expand, constantCoeff_map, hμ.const i, map_zero])
    (fun i α => frob_congr p F.σ F.σ_pow hu (μ' i) α)
  rw [Ideal.mul_top] at hK
  simp only [QL]
  rw [cob1_expand_frobenius_map p hp F.σ F.s F.s_alg μ' hμ.const f]
  refine ⟨⟨hc0, fun i => ⟨0, trivial, by rw [hlin, map_zero]⟩,
    in_add (in_mono le_top hK) (in_expand p hp (in_map F.σ F.s F.s_alg (N' := ⊤) (fun _ _ => Submodule.mem_top) hf.2.2))⟩,
    fun hker => ⟨hc0, fun i => ⟨0, Ideal.zero_mem _, by rw [hlin, map_zero]⟩,
      in_add hK (in_expand p hp (in_map F.σ F.s F.s_alg ?_ hker))⟩⟩
  intro b hb
  rw [RingHom.mem_ker] at hb
  obtain ⟨y, _, hy⟩ := F.frame.pd b hb
  obtain ⟨z, hz⟩ := F.σ_pow b
  rw [Ideal.mem_span_singleton]
  exact ⟨z + y, by rw [mul_add, ← hz, ← hy]; ring⟩

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogReduces
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

open CategoryTheory TensorProduct MvPowerSeries in
private lemma mem_quasiLog_iff (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : _root_.GlobalTheory.Katz.IsLaw μ)
    (f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k)) :
    f ∈ _root_.GlobalTheory.Katz.quasiLog p h ↔
      f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d) ∧
        _root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f ∈
          _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) 1 := by
  unfold _root_.GlobalTheory.Katz.quasiLog
  exact Iff.rfl

open CategoryTheory TensorProduct MvPowerSeries in
private lemma exists_lin_eq_algebraMap_of_mem_quasiInt (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    {d : ℕ} {f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    (hf : f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d)) (i : Fin d) :
    ∃ a, _root_.GlobalTheory.Katz.lin f i = algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) a := by
  obtain ⟨a, ha⟩ := hf (Finsupp.single i 1) i
  exact ⟨a, by simpa [_root_.GlobalTheory.Katz.lin] using ha⟩

open CategoryTheory TensorProduct MvPowerSeries in
private lemma isCoc_of_red_cob1_quasiInt (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (h : _root_.GlobalTheory.Katz.IsLaw μ) (f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k))
    (hf : f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d))
    (c : MvPowerSeries (Fin d ⊕ Fin d) k)
    (hc : _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c) :
    _root_.GlobalTheory.Katz.IsCoc μ c := by
  obtain ⟨-, huniq, -, hadd, -, hdivp, -⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  obtain ⟨-, huniq3, -, -, -, hdivp3, -⟩ :=
    _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d ⊕ Fin d)
  obtain ⟨htwo, hswap⟩ := _root_.GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem p k d μ h f hf
  obtain ⟨hcomm, -⟩ := _root_.GlobalTheory.Katz.red_coboundaries p k d μ
    h.const
  obtain ⟨hred2, hredswap⟩ := hcomm _ c hc
  unfold _root_.GlobalTheory.Katz.IsCoc
  refine ⟨huniq3 _ _ _ hred2 ((hdivp3 _).1 htwo), ?_⟩
  exact sub_eq_zero.1 (huniq _ _ _ (hadd _ _ _ _ hredswap hc).2 ((hdivp _).1 hswap))


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.quasiLog_reduces : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : _root_.GlobalTheory.Katz.IsLaw μ), (∀ f ∈ _root_.GlobalTheory.Katz.quasiLog p h, ∃ c w, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c ∧ _root_.GlobalTheory.Katz.RedV p (_root_.GlobalTheory.Katz.lin f) w) ∧ ∀ f ∈ _root_.GlobalTheory.Katz.quasiLog p h, ∀ c, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c → _root_.GlobalTheory.Katz.IsCoc μ c := by
  intro p _ k _ _ _ d μ h
  refine ⟨fun f hf => ?_, fun f hf c hc => ?_⟩
  · obtain ⟨hint, hcob⟩ := (mem_quasiLog_iff p k d μ h f).1 hf
    obtain ⟨c, hc⟩ := ((_root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)).1 _).1 hcob
    choose a ha using exists_lin_eq_algebraMap_of_mem_quasiInt p k hint
    exact ⟨c, fun i => WittVector.constantCoeff (a i), hc, fun i => ⟨a i, ha i, rfl⟩⟩
  · exact isCoc_of_red_cob1_quasiInt p k d μ h f
      ((mem_quasiLog_iff p k d μ h f).1 hf).1 c hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftKillsCuspOfDegreeNotDvd
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_lift_kills_cusp_of_degree_not_dvd : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → ¬ Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (cusp θ n (k * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ (n * i))) := by
  first | (exact @GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd) | (exact GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd) | (intros; apply GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKlingenDeligneRibetOfBoth
section
namespace GlobalTheory

theorem siegelKlingenDeligneRibet_of_both :
    GlobalTheory.Published.SiegelKlingen → GlobalTheory.Published.DeligneRibet → GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  fun a b => ⟨a, b⟩

end GlobalTheory
end

