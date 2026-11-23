module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.BoxBoundAlt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SymmetricDistance.SymDistOf
public import Formalism.PeriodIntegrals.Bundle0021

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.BoxBound
section
noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace BoxB

variable {n : ℕ}

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra Matrix.frobeniusNormedSpace

lemma frob_sq (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ^ 2 = Formalism.REAL.hs A := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  simp only [Real.rpow_two]
  norm_num [Formalism.REAL.hs]

lemma frob_eq (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ = Real.sqrt (Formalism.REAL.hs A) := by
  rw [← frob_sq, Real.sqrt_sq (norm_nonneg A)]

lemma hs_one : Formalism.REAL.hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  unfold Formalism.REAL.hs
  have h1 : ∀ i : Fin n, ∑ j, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Matrix.one_apply_ne (Ne.symm hj)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp [h1]

lemma norm_one_eq : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [frob_eq, hs_one]

lemma term_le (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ‖((k.factorial : ℂ)⁻¹) • X ^ k‖ ≤ Real.sqrt n * (‖X‖ ^ k / k.factorial) := by
  have hsq : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have hpow : ‖X ^ k‖ ≤ Real.sqrt n * ‖X‖ ^ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [norm_one_eq]
    · calc ‖X ^ k‖ ≤ ‖X‖ ^ k := norm_pow_le' X hk
        _ ≤ Real.sqrt n * ‖X‖ ^ k := le_mul_of_one_le_left (by positivity) hsq
  have hc : ‖((k.factorial : ℂ)⁻¹)‖ = (k.factorial : ℝ)⁻¹ := by simp
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [norm_smul, hc, inv_mul_eq_div, mul_div_assoc']
  exact div_le_div_of_nonneg_right hpow hf.le

lemma norm_exp_le (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp X‖ ≤ Real.sqrt n * Real.exp ‖X‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  have hs := (NormedSpace.expSeries_div_hasSum_exp ‖X‖).mul_left (Real.sqrt n)
  rw [← Real.exp_eq_exp_ℝ] at hs
  exact tsum_of_norm_bounded hs (fun k => term_le hn X k)

lemma hs_exp_le (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (NormedSpace.exp X) ≤ (Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Formalism.REAL.hs]
  · rw [← frob_sq, ← frob_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_exp_le hn X) 2

end Frob

private lemma hs_eq_re_trace_conjTranspose_mul' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs M = (Mᴴ * M).trace.re := by
  unfold Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma hs_unitary_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : kᴴ * k = 1) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (k * M) = Formalism.REAL.hs M := by
  rw [hs_eq_re_trace_conjTranspose_mul', hs_eq_re_trace_conjTranspose_mul', Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k M, hk,
    Matrix.one_mul]

end BoxB

open BoxB in
theorem box_lattice_point_bound : BoxBound := by
  intro n ε g
  have hK : ∀ k : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε → kᴴ * k = 1 := by
    intro k hk
    simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at hk
    exact Matrix.mem_unitaryGroup_iff'.mp hk.1
  have hP : Formalism.REAL.Polar := Formalism.REAL.polar_decomposition_holds
  have hgi : Formalism.REAL.inUJ ε (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) := g.2
  obtain ⟨k0, X0, hk0, hX0, hg0⟩ := (hP n ε).1 _ hgi
  set S := {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
      t = Real.sqrt (Formalism.REAL.hs X)} with hS
  have hne : S.Nonempty := ⟨_, k0, X0, hk0, hX0, hg0, rfl⟩
  have hbound : ∀ t ∈ S, hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp t := by
    rintro t ⟨k, X, hk, _, hgk, rfl⟩
    unfold hsN Formalism.MainNotions.S.uMat
    rw [hgk, hs_unitary_mul (hK k hk)]
    calc Real.sqrt (Formalism.REAL.hs (NormedSpace.exp X))
        ≤ Real.sqrt ((Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2) :=
          Real.sqrt_le_sqrt (hs_exp_le X)
      _ = Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X)) := Real.sqrt_sq (by positivity)
  show hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp (sInf S)
  by_contra hlt
  push_neg at hlt
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have h0 : hsN (Formalism.MainNotions.S.uMat g) = 0 := by
      unfold hsN Formalism.REAL.hs
      simp
    rw [h0] at hlt
    simp at hlt
  · have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
    set a := hsN (Formalism.MainNotions.S.uMat g) with ha
    have hapos : 0 < a := lt_of_le_of_lt (by positivity) hlt
    have h1 : sInf S < Real.log (a / Real.sqrt n) := by
      rw [Real.lt_log_iff_exp_lt (div_pos hapos hsqpos), lt_div_iff₀ hsqpos, mul_comm]
      exact hlt
    obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hne h1
    have h2 := hbound t htS
    have h3 : Real.exp t < a / Real.sqrt n := by
      rw [← Real.exp_log (div_pos hapos hsqpos)]
      exact Real.exp_lt_exp.mpr htlt
    rw [lt_div_iff₀ hsqpos] at h3
    linarith

end PI.UnitaryGroupMassFormula.LCG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.LatCountAllOf
section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

open PI.LatCountG

theorem hsN_zero {n : ℕ} : hsN (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [hsN, Formalism.REAL.hs]

theorem hsN_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN A := Real.sqrt_nonneg _

theorem mem_gf (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) :
    ∃ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      (∀ v, Formalism.MainNotions.S.uMat ((γ : I.GA).1 v) = (I.P v)⁻¹ * (g : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat (γ : I.GA).2 = (g : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := γ.2

def gm (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) : Matrix (Fin I.n) (Fin I.n) I.E :=
  (((mem_gf I γ).choose : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)

theorem gm_spec (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) :
    (∀ v, Formalism.MainNotions.S.uMat ((γ : I.GA).1 v) = (I.P v)⁻¹ * (gm I γ).map (I.φ v) * I.P v) ∧
      I.fmat (γ : I.GA).2 = (gm I γ).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := (mem_gf I γ).choose_spec.2

theorem gm_inj (I : Formalism.MainNotions.S.AutInst) {γ γ' : I.GFset} (h : gm I γ = gm I γ') : γ = γ' := by
  obtain ⟨h1a, h1b⟩ := gm_spec I γ
  obtain ⟨h2a, h2b⟩ := gm_spec I γ'
  rw [h] at h1a h1b
  apply Subtype.ext
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((h1a v).trans (h2a v).symm))
  · exact Subtype.ext (Units.ext (h1b.trans h2b.symm))

theorem phi_eq (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (γ : I.GFset) (v : InfinitePlace I.F) :
    Formalism.MainNotions.S.uMat ((x⁻¹ * (γ : I.GA) * y).1 v) = amat I x y v (gm I γ) := by
  obtain ⟨h1, -⟩ := gm_spec I γ
  rw [amat, ← h1 v]
  simp only [Formalism.MainNotions.S.uMat, Prod.fst_mul, Prod.fst_inv, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul,
    Units.val_mul]

theorem amat_sub (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (v : InfinitePlace I.F) (δ₁ δ₂ : Matrix (Fin I.n) (Fin I.n) I.E) :
    amat I x y v (δ₁ - δ₂) = amat I x y v δ₁ - amat I x y v δ₂ := by
  have hm : (δ₁ - δ₂).map (I.φ v) = δ₁.map (I.φ v) - δ₂.map (I.φ v) := by
    ext i j; simp
  simp only [amat, hm, mul_sub, sub_mul]

theorem latCountAll_of (hB : BoxBound) (hLM : LatMap) (hLS : LatSub) (hS : Sep) (hP : PackLem) (hN : NPos)
    (hC : CardPl) : LatCountAll := by
  classical
  intro I x y hx hy r hr S hSc
  have hn : 1 ≤ I.n := hN I x hx
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = PI.LatCountG.tau1 I x * PI.LatCountG.tau1 I y := ⟨_, rfl⟩
  rw [← hρdef]
  have hρ : 0 < ρ := by rw [hρdef]; exact mul_pos hx hy
  have hτx : PI.LatCountG.tau1 I x ≤ 1 / 2 := by unfold PI.LatCountG.tau1; exact min_le_left _ _
  have hτy : PI.LatCountG.tau1 I y ≤ 1 / 2 := by unfold PI.LatCountG.tau1; exact min_le_left _ _
  have hρle : ∀ v, ρ ≤ Real.sqrt I.n * Real.exp (r v) := fun v => by
    have h0 : ρ ≤ 1 / 2 * (1 / 2) := by rw [hρdef]; exact mul_le_mul hτx hτy hy.le (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.sqrt I.n := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    have h3 : (1 : ℝ) ≤ Real.exp (r v) := Real.one_le_exp (hr v)
    nlinarith
  let g : I.GFset → (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
    fun γ v => amat I x y v (gm I γ)
  have hgsub : ∀ γ γ' : I.GFset, ∀ v, g γ v - g γ' v = amat I x y v (gm I γ - gm I γ') :=
    fun γ γ' v => (amat_sub I x y v _ _).symm
  have hlat : ∀ γ ∈ S, ∀ u ∈ PI.LatCountG.latSet I y, gm I γ *ᵥ u ∈ PI.LatCountG.latSet I x :=
    fun γ hγ u hu => hLM I x y γ (mem_gf I γ).choose (gm_spec I γ).2 (hSc γ hγ).1 u hu
  have hsep : ∀ γ ∈ S, ∀ γ' ∈ S, gm I γ ≠ gm I γ' → ∃ v, ρ ≤ hsN (g γ v - g γ' v) := by
    intro γ hγ γ' hγ' hne
    have hδ : gm I γ - gm I γ' ≠ 0 := sub_ne_zero.mpr hne
    have hmap : ∀ u ∈ PI.LatCountG.latSet I y,
        (gm I γ - gm I γ') *ᵥ u ∈ PI.LatCountG.latSet I x := by
      intro u hu
      rw [Matrix.sub_mulVec]
      exact hLS I x _ _ (hlat γ hγ u hu) (hlat γ' hγ' u hu)
    have hineq := hS I x y hx hy _ hδ hmap
    rw [← hρdef] at hineq
    by_contra hcon
    push_neg at hcon
    have hprod : ∏ v, hsN (g γ v - g γ' v) < ρ ^ I.f := by
      rw [← hC I, ← Finset.card_univ, ← Finset.prod_const]
      by_cases h0 : ∃ v, hsN (g γ v - g γ' v) = 0
      · obtain ⟨v, hv⟩ := h0
        rw [Finset.prod_eq_zero (Finset.mem_univ v) hv]
        exact Finset.prod_pos fun _ _ => hρ
      · push_neg at h0
        have hne' : (Finset.univ : Finset (InfinitePlace I.F)).Nonempty := by
          by_contra he
          rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at he
          have hf0 : I.f = 0 := by rw [← hC I]; exact Fintype.card_eq_zero
          have hpos : 0 < I.f := by
            first
              | exact (hC I) ▸ Fintype.card_pos
              | unfold Formalism.MainNotions.S.AutInst.f; exact Module.finrank_pos
          omega
        exact Finset.prod_lt_prod_of_nonempty₀
          (fun v _ => lt_of_le_of_ne (hsN_nonneg _) (h0 v).symm) (fun v _ => hcon v) hne'
    simp only [hgsub] at hprod
    linarith
  have hinj : Set.InjOn g S := by
    intro γ hγ γ' hγ' heq
    by_contra hne
    obtain ⟨v, hv⟩ := hsep γ hγ γ' hγ' (fun h => hne (gm_inj I h))
    rw [heq, sub_self, hsN_zero] at hv
    linarith
  have hbound : ∀ p ∈ S.image g, ∀ v, hsN (p v) ≤ Real.sqrt I.n * Real.exp (r v) := by
    intro p hp v
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    show hsN (amat I x y v (gm I γ)) ≤ _
    rw [← phi_eq]
    refine (hB I.n (I.ε v) ((x⁻¹ * (γ : I.GA) * y).1 v)).trans ?_
    gcongr
    exact (hSc γ hγ).2 v
  have hsepT : ∀ p ∈ S.image g, ∀ q ∈ S.image g, p ≠ q → ∃ v, ρ ≤ hsN (p v - q v) := by
    intro p hp q hq hpq
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.mp hq
    exact hsep γ hγ γ' hγ' (fun h => hpq (by simp only [g, h]))
  have hpack := hP (InfinitePlace I.F) I.n (fun v => Real.sqrt I.n * Real.exp (r v)) (fun _ => ρ)
    (fun _ => hρ) (fun v => by positivity) (S.image g) hbound hsepT
  have hexp : ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) = Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnn : ∀ v, 0 ≤ 2 * (Real.sqrt I.n * Real.exp (r v)) + ρ := fun v => by
    have := Real.sqrt_nonneg (I.n : ℝ)
    have := Real.exp_pos (r v)
    nlinarith
  calc (S.card : ℝ) = ((S.image g).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ ∏ v, ((2 * (Real.sqrt I.n * Real.exp (r v)) + ρ) / ρ) ^ (2 * I.n ^ 2) := hpack
    _ ≤ ∏ v, ((3 * Real.sqrt I.n / ρ) * Real.exp (r v)) ^ (2 * I.n ^ 2) := by
        refine Finset.prod_le_prod₀ (fun v _ => pow_nonneg (div_nonneg (hnn v) hρ.le) _)
          (fun v _ => ?_)
        refine pow_le_pow_left₀ (div_nonneg (hnn v) hρ.le) ?_ _
        rw [div_mul_eq_mul_div]
        gcongr
        nlinarith [hρle v]
    _ = (∏ v : InfinitePlace I.F, (3 * Real.sqrt I.n / ρ) ^ (2 * I.n ^ 2)) *
          ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) := by
        rw [← Finset.prod_mul_distrib]; simp_rw [mul_pow]
    _ = _ := by rw [hexp, Finset.prod_const, Finset.card_univ, hC I, ← pow_mul]

end PI.UnitaryGroupMassFormula.LCG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.PackLem
section
noncomputable section

open MeasureTheory Metric Module

namespace PI.UnitaryGroupMassFormula.LCG

def matVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : EuclideanSpace ℂ (Fin N × Fin N) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

theorem norm_matVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ‖matVec A‖ = hsN A := by
  rw [EuclideanSpace.norm_eq, hsN, Formalism.REAL.hs, Fintype.sum_prod_type]
  rfl

theorem matVec_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) : matVec (A - B) = matVec A - matVec B := by
  ext ij
  simp [matVec]

theorem finrank_matSpace (N : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin N × Fin N)) = 2 * N ^ 2 := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, sq]

theorem lattice_packLem : PackLem := by
  intro ι _ N R ρ hρ hR T hT hsep
  classical
  let W := EuclideanSpace ℂ (Fin N × Fin N)
  let μ : Measure W := Measure.addHaar
  let ν : Measure (ι → W) := Measure.pi fun _ => μ
  let B : (ι → Matrix (Fin N) (Fin N) ℂ) → Set (ι → W) :=
    fun p => Set.univ.pi fun v => ball (matVec (p v)) (ρ v / 2)
  let Big : Set (ι → W) := Set.univ.pi fun v => ball (0 : W) (R v + ρ v / 2)
  have hdisj : (T : Set (ι → Matrix (Fin N) (Fin N) ℂ)).PairwiseDisjoint B := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    obtain ⟨v, hv⟩ := hsep p hp q hq hpq
    have h1 := (Set.mem_univ_pi.1 hzp) v
    have h2 := (Set.mem_univ_pi.1 hzq) v
    rw [mem_ball] at h1 h2
    have h3 : dist (matVec (p v)) (matVec (q v)) < ρ v := by
      calc dist (matVec (p v)) (matVec (q v)) ≤ dist (matVec (p v)) (z v) + dist (z v) (matVec (q v)) :=
            dist_triangle _ _ _
        _ < ρ v / 2 + ρ v / 2 := by rw [dist_comm] at h1; exact add_lt_add h1 h2
        _ = ρ v := by ring
    rw [dist_eq_norm, ← matVec_sub, norm_matVec] at h3
    linarith
  have hmeas : ∀ p ∈ T, MeasurableSet (B p) := fun p _ =>
    MeasurableSet.univ_pi fun v => measurableSet_ball
  have hsub : (⋃ p ∈ T, B p) ⊆ Big := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    refine Set.mem_univ_pi.2 fun v => ?_
    have h1 := (Set.mem_univ_pi.1 hz) v
    rw [mem_ball, dist_eq_norm] at h1
    rw [mem_ball_zero_iff]
    have h2 : ‖matVec (p v)‖ ≤ R v := by rw [norm_matVec]; exact hT p hp v
    calc ‖z v‖ = ‖(z v - matVec (p v)) + matVec (p v)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z v - matVec (p v)‖ + ‖matVec (p v)‖ := norm_add_le _ _
      _ < ρ v / 2 + R v := by linarith
      _ = R v + ρ v / 2 := by ring
  have key : ∑ p ∈ T, ν (B p) ≤ ν Big := by
    rw [← measure_biUnion_finset hdisj hmeas]
    exact measure_mono hsub
  set d := finrank ℝ W with hd
  set c := μ (ball (0 : W) 1) with hc
  have hc0 : c ≠ 0 := (measure_ball_pos μ (0 : W) one_pos).ne'
  have hctop : c ≠ ⊤ := measure_ball_lt_top.ne
  have hB : ∀ p, ν (B p) = ∏ v, ENNReal.ofReal ((ρ v / 2) ^ d) * c := by
    intro p
    simp only [ν, B, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact Measure.addHaar_ball_of_pos μ _ (by linarith [hρ v])
  have hBig : ν Big = ∏ v, ENNReal.ofReal ((R v + ρ v / 2) ^ d) * c := by
    simp only [ν, Big, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact Measure.addHaar_ball_of_pos μ _ (by linarith [hρ v, hR v])
  simp only [hB, Finset.sum_const, nsmul_eq_mul] at key
  rw [hBig] at key
  have hfin : ∏ v, ENNReal.ofReal ((R v + ρ v / 2) ^ d) * c ≠ ⊤ :=
    ENNReal.prod_ne_top fun v _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop
  have key' := ENNReal.toReal_mono hfin key
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_prod, ENNReal.toReal_prod] at key'
  simp only [ENNReal.toReal_mul] at key'
  have hc' : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  have hpos : ∀ v, 0 < ρ v / 2 := fun v => by linarith [hρ v]
  simp only [fun v => ENNReal.toReal_ofReal (pow_nonneg (hpos v).le d),
    fun v => ENNReal.toReal_ofReal (pow_nonneg (add_pos_of_nonneg_of_pos (hR v) (hpos v)).le d)] at key'
  have hprodpos : 0 < ∏ v, (ρ v / 2) ^ d * c.toReal :=
    Finset.prod_pos fun v _ => mul_pos (pow_pos (hpos v) d) hc'
  rw [← le_div_iff₀ hprodpos, ← Finset.prod_div_distrib] at key'
  have hdN : d = 2 * N ^ 2 := finrank_matSpace N
  calc (T.card : ℝ) ≤ ∏ v, (R v + ρ v / 2) ^ d * c.toReal / ((ρ v / 2) ^ d * c.toReal) := key'
    _ = ∏ v, ((2 * R v + ρ v) / ρ v) ^ (2 * N ^ 2) := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [mul_div_mul_right _ _ hc'.ne', ← div_pow, hdN]
      congr 1
      have := hρ v
      field_simp

end PI.UnitaryGroupMassFormula.LCG

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SublatticeOfLattice
section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

theorem sublattice_of_lattice : LatSub := by
  intro I x u u' hu hu'
  simp only [PI.LatCountG.latSet, Set.mem_setOf_eq] at hu hu' ⊢
  have h : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((u - u') i)) =
      (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) -
        (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u' i)) := by
    funext i
    simp [map_sub]
  rw [h, Matrix.mulVec_sub]
  exact Submodule.sub_mem _ hu hu'

theorem lattice_map_image : LatMap := by
  intro I x y γ g hγ hK u hu
  simp only [PI.LatCountG.latSet, Set.mem_setOf_eq] at hu ⊢
  have h1 : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (((g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) i)) =
      I.fmat γ.2 *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) := by
    funext i
    rw [hγ]
    exact RingHom.map_mulVec _ _ _ i
  have hK' : ∀ v, v ∈ I.Lf ↔ I.fmat (x⁻¹ * γ * y).2 *ᵥ v ∈ I.Lf := hK
  have hk := (hK' (I.fmat y.2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i))).1 hu
  rw [h1]
  convert hk using 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Formalism.MainNotions.S.AutInst.fmat, Prod.snd_mul, Prod.snd_inv]
  push_cast
  simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)),
    Matrix.mul_one]

theorem norm_positive : NPos := by
  intro I x h
  by_contra hn
  have hn0 : I.n = 0 := by omega
  have hE : IsEmpty (PI.LatCountG.Sub I x) := by
    constructor
    intro s
    have hj := s.j_pos
    apply s.b_ind.ne_zero ⟨0, by omega⟩
    funext i
    exact absurd i.2 (by omega)
  have h0 : PI.LatCountG.tau1 I x = 0 := by
    unfold PI.LatCountG.tau1
    rw [Real.iInf_of_isEmpty]
    exact min_eq_right (by norm_num)
  linarith

theorem card_places_bound : CardPl := by
  intro I
  haveI : NumberField.IsTotallyReal I.F := I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
  have h3 := NumberField.IsTotallyReal.nrComplexPlaces_eq_zero (K := I.F)
  show _ = Module.finrank ℚ I.F
  omega

end PI.UnitaryGroupMassFormula.LCG
end
end

