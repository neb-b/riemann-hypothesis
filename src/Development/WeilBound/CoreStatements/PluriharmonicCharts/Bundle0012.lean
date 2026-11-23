module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0033
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0006
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsValueAtZpow
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.FlHeightNonnegDominant
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace PositivityTheory.Xgp.block_hermitian_pullback

namespace FlPos

section Fs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem levi_wsum_nonneg {J : Type} [Fintype J] {z : J → ℂ} (c : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (f : K → (J → ℂ) → ℝ) (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (hl : ∀ k w, 0 ≤ levi (f k) z w)
    (w : J → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => ∑ k ∈ s, c k * f k y) z ∧
      0 ≤ levi (fun y => ∑ k ∈ s, c k * f k y) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using contDiffAt_const, by simp [levi]⟩
  | insert a s ha ih =>
    have heq : (fun y => ∑ k ∈ insert a s, c k * f k y) =
        fun y => (fun y' => ∑ k ∈ s, c k * f k y') y + c a * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq]
    refine ⟨ih.1.add (contDiffAt_const.mul (hf a)), ?_⟩
    rw [levi_add_smul (f := fun y' => ∑ k ∈ s, c k * f k y') (g := f a) (c a) ih.1 (hf a) w]
    exact add_nonneg ih.2 (mul_nonneg (hc a) (hl a w))

theorem fsHerm_levi (a : K → ℕ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    0 ≤ leviForm (fun y => Real.log ((fsHerm ι fun k => (a k : ℤ)).h y)) z w := by
  classical
  set F : K → ((Σ k, ι k) → ℂ) → ℝ :=
    fun k y => Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩)) with hF
  have hev : (fun y => Real.log ((fsHerm ι fun k => (a k : ℤ)).h y)) =ᶠ[𝓝 z]
      fun y => ∑ k ∈ Finset.univ, (a k : ℝ) * F k y := by
    have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hz k
      exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
        fun y hy => ⟨i, hy⟩
    filter_upwards [Filter.eventually_all.mpr hopen] with y hy
    have hS : ∀ k, 0 < ∑ i, ‖y ⟨k, i⟩‖ ^ 2 := fun k => by
      obtain ⟨i, hi⟩ := hy k
      exact Finset.sum_pos' (fun j _ => sq_nonneg ‖y ⟨k, j⟩‖)
        ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
    rw [fsHerm_h]
    unfold refNorm
    rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos (hS k) _).ne']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.log_rpow (hS k)]
    have hρ : (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) = Real.sqrt (∑ i, ‖y ⟨k, i⟩‖ ^ 2) := by
      change ‖WithLp.toLp 2 (fun i => y ⟨k, i⟩)‖ = _
      rw [EuclideanSpace.norm_eq]
    simp only [hF]
    rw [hρ, Real.log_sqrt (hS k).le]
    push_cast
    ring
  have hblock : ∀ k, ContDiffAt ℝ 2 (F k) z ∧ ∀ v, 0 ≤ levi (F k) z v := by
    intro k
    have hk0 : (fun i => z ⟨k, i⟩) ≠ 0 := by
      obtain ⟨i, hi⟩ := hz k
      exact fun h0 => hi (congrFun h0 i)
    have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
      (HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) hk0
    have hFk : F k = (fun u => Real.log ((fsMetric (ι := ι k)).ρ u)) ∘ FubiniStudyLeviForm.blockProj ι k := rfl
    refine ⟨hFk ▸ hφ.comp z ((FubiniStudyLeviForm.blockProj ι k).restrictScalars ℝ).contDiff.contDiffAt,
      fun v => ?_⟩
    rw [hFk, levi_comp v ((FubiniStudyLeviForm.blockProj ι k).analyticAt z) hφ]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hk0 _
  change 0 ≤ levi _ z w
  rw [levi_congr hev]
  exact (levi_wsum_nonneg (fun k => (a k : ℝ)) (fun k => Nat.cast_nonneg _) F
    (fun k => (hblock k).1) (fun k => (hblock k).2) w Finset.univ).2

theorem fsHerm_monomials (P : Ideal (MRing ι)) (a : K → ℕ) :
    MonomialsBounded P (fsHerm ι fun k => (a k : ℤ)) a := by
  intro z _ μ hμ
  rw [norm_prod, fsHerm_h]
  unfold refNorm
  rw [Fintype.prod_sigma]
  refine Finset.prod_le_prod₀ (fun k _ => Finset.prod_nonneg fun _ _ => norm_nonneg _) fun k _ => ?_
  have hS : 0 ≤ ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hle : ∀ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ μ ⟨k, i⟩ := fun i => by
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) (Real.le_sqrt_of_sq_le ?_) _
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖
      ≤ ∏ i, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ μ ⟨k, i⟩ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => hle i
    _ = Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k := by
        rw [Finset.prod_pow_eq_pow_sum, hμ k]
    _ = (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (((a k : ℤ) : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hS]
        congr 1
        push_cast
        ring

end Fs

theorem wordSum_nonneg {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ)
    (h : ∀ c : σ → ℕ, 0 ≤ ∑ w : Fin n → σ, a w * ∏ j, (c (w j) : ℝ)) (c : σ → ℝ) (hc : ∀ p, 0 ≤ c p) :
    0 ≤ ∑ w : Fin n → σ, a w * ∏ j, c (w j) := by
  have hcont : Continuous fun c : σ → ℝ => ∑ w : Fin n → σ, a w * ∏ j, c (w j) := by
    fun_prop
  let u : ℕ → σ → ℝ := fun m p => (⌊c p * ((m : ℝ) + 1)⌋₊ : ℝ) / ((m : ℝ) + 1)
  have hu : Tendsto u atTop (𝓝 c) := by
    refine tendsto_pi_nhds.2 fun p => ?_
    exact (tendsto_nat_floor_mul_div_atTop (hc p)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine ge_of_tendsto' ((hcont.tendsto c).comp hu) fun m => ?_
  have hm := h fun p => ⌊c p * ((m : ℝ) + 1)⌋₊
  have e : (∑ w : Fin n → σ, a w * ∏ j, u m (w j)) =
      (((m : ℝ) + 1) ^ n)⁻¹ * ∑ w : Fin n → σ, a w * ∏ j, (⌊c (w j) * ((m : ℝ) + 1)⌋₊ : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [u, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, inv_pow]
    ring
  simp only [Function.comp]
  rw [e]
  exact mul_nonneg (by positivity) hm

section Flag

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem self_nonneg [Nonempty Ψ] (hG : ArithmeticIntersectionNonneg) (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (hN : 2 ≤ N) (hP : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1)) (a : FlBlock Ψ N → ℕ) :
    0 ≤ II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1)
      fun _ => fsHerm (FlIdx Ψ N) fun k => (a k : ℤ) := by
  have hrel : ∀ k, ∃ i, yFl Ψ N ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    simp [PFl, mCoordIdeal, RingHom.mem_ker, mConeMap, h0]
  obtain ⟨Ω', _, y', hy, hB⟩ := PositivityTheory.Xgp.t_birat (FlBlock Ψ N) (FlIdx Ψ N) (ΩFl Ψ N) (yFl Ψ N) hrel
  have hPy : mCoordIdeal y' = PFl Ψ N := hy
  rw [← hPy] at hP ⊢
  have hD : 1 ≤ antisymDegree Ψ N := Nat.mul_pos Fintype.card_pos (Nat.choose_pos hN)
  exact hG _ _ Ω' y' (antisymDegree Ψ N) a _ ⊥ II hD hII hP hB rfl bot_le
    ⟨FlagHeightMultilinear.isSmoothHerm_fsHerm _, fun z hz w _ => fsHerm_levi a hz.1 w⟩
    (fsHerm_monomials _ a) (fun z => by simp [fsHerm_h, refNorm])

end Flag

end FlPos


open FlPos in
theorem flHeight_nonneg_dominant : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ∀ lam : Ψ × Fin N → ℝ, Dominant lam → 0 ≤ eval lam (hFlPoly Ψ N II) := by
  intro hIn II hII Ψ _ _ _ N hN lam hlam
  have hP : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := (PositivityTheory.Xgp.t_fl_arith Ψ N hN).1
  have hI := hII.1 (FlBlock Ψ N) (FlIdx Ψ N)
  set a : (Fin (antisymDegree Ψ N + 1) → Ψ × Fin N) → ℝ := fun w =>
    II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => yLineFl Ψ N (w r) with ha
  have hnat : ∀ c : Ψ × Fin N → ℕ, 0 ≤ ∑ w, a w * ∏ j, (c (w j) : ℝ) := by
    intro c
    have h := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ p => (c p : ℤ)) (FlLines.yDeg Ψ N)
    have hy0 : ∀ p q, 0 ≤ FlLines.yDeg Ψ N p q := fun p q => by
      unfold FlLines.yDeg
      split_ifs <;> norm_num
    have hb : (fun q => (((∑ p, (c p : ℤ) • FlLines.yDeg Ψ N p) q).toNat : ℤ)) =
        ∑ p, (c p : ℤ) • FlLines.yDeg Ψ N p := by
      funext q
      refine Int.toNat_of_nonneg ?_
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun p _ => mul_nonneg (Int.natCast_nonneg _) (hy0 p q)
    have hs := self_nonneg hIn.2.1.2.2 II hII.1 hN hP
      fun q => ((∑ p, (c p : ℤ) • FlLines.yDeg Ψ N p) q).toNat
    rw [hb, h] at hs
    refine hs.trans_eq (Finset.sum_congr rfl fun w _ => ?_)
    rw [mul_comm]
    simp only [Int.cast_natCast]
    rfl
  have hzero : ∀ (w : Fin (antisymDegree Ψ N + 1) → Ψ × Fin N) (j : Fin (antisymDegree Ψ N + 1)),
      ¬ ((w j).2 : ℕ) + 1 < N → a w = 0 := by
    intro w j hj
    have hy : FlLines.yDeg Ψ N (w j) = 0 := by
      funext q
      have hq := q.2.2
      have : ¬ ((q.2 : ℕ) = ((w j).2 : ℕ)) := by omega
      simp [FlLines.yDeg, this]
    exact (FlagHeightMultilinear.fsMultilin hI hP).map_coord_zero (m := fun r => FlLines.yDeg Ψ N (w r)) j hy
  rw [(flLines_polys hIn II hII Ψ N hN hP).1, eval_toWt_gap, (formPoly_isHomogeneous_and_eval _ _ _).2]
  have e : ∑ w, a w * ∏ j, gap lam (w j) =
      ∑ w, a w * ∏ j, (if ((w j).2 : ℕ) + 1 < N then gap lam (w j) else 0) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : ∀ j, ((w j).2 : ℕ) + 1 < N
    · congr 1
      exact Finset.prod_congr rfl fun j _ => (if_pos (hw j)).symm
    · push_neg at hw
      obtain ⟨j, hj⟩ := hw
      rw [hzero w j (not_lt.2 hj), zero_mul, zero_mul]
  rw [e]
  exact wordSum_nonneg _ a hnat (fun p => if (p.2 : ℕ) + 1 < N then gap lam p else 0) fun p => by
    split_ifs with hp
    · exact hlam p hp
    · exact le_rfl

end PositivityTheory.Xgp.block_hermitian_pullback
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.RefNorm
section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {M : FlagModel y Ψ N j}
variable {Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop}

theorem sum_dy (p : Ψ × Fin N) (L : K → ℝ) :
    ∑ k, (M.dy p k : ℝ) * L k = (M.blk p).elim 0 L - ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * L k'.1 := by
  have e1 : ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * L k'.1 =
      ∑ k, if h : ∀ p', M.blk p' ≠ some k then (M.b p ⟨k, h⟩ : ℝ) * L k else 0 :=
    Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
      (fun k hk => dif_neg fun h => hk ⟨⟨k, h⟩, rfl⟩) (fun k => by rw [dif_pos k.2])
  have e2 : (M.blk p).elim 0 L = ∑ k, if M.blk p = some k then L k else 0 := by
    cases M.blk p with
    | none => simp
    | some k => simp
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold FlagModel.dy
  by_cases h : ∀ p', M.blk p' ≠ some k
  · rw [dif_pos h, dif_pos h, if_neg (h p)]; simp
  · rw [dif_neg h, dif_neg h]; split_ifs <;> simp

theorem Rel.smul
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (htor : ∀ F τ w G (c : NonPluckerBlocks M.blk → ℂ), (∀ k, c k ≠ 0) → Gr F τ w G → Gr F τ (torusSmul c w) G)
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r : ℝ} (h1 : Rel M Gr p z r) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    Rel M Gr p (torusSmul c z) (r + ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖) := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨hF, hw, gd, -, -⟩ := hgood _ _ _ _ hG
  have hG' := htor _ _ _ _ (fun k => c k.1) (fun k => hc _) hG
  have eb : basePart M.blk (torusSmul c z) = torusSmul (fun k => c k.1) (basePart M.blk z) := rfl
  have ev : ∀ s, valAt M.x s (basePart M.blk (torusSmul c z)) = valAt M.x s (basePart M.blk z) := fun s =>
    GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit _ _ _ M.x s _ _ (hgood _ _ _ _ hG').2.1
      ⟨fun k => c k.1, fun k => hc _, rfl⟩
  have el : ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk (torusSmul c z) ⟨k', F.c k'⟩‖ =
      ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * Real.log ‖c k'.1‖ +
        ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk z ⟨k', F.c k'⟩‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eb, torusSmul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 (ne_of_notMem (gd.1 k)))]
    ring
  refine ⟨F, G, hG', h, bh, dh, t + (M.blk p).elim 0 (fun k => Real.log ‖c k‖), ?_, ?_⟩
  · rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩
    · refine Or.inl ⟨k, c k * a, hk, mul_ne_zero (hc k) ha, fun m => ?_, ?_⟩
      · simp only [ev]
        rw [torusSmul, hz m, mul_assoc]
      · rw [hk, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 ha), Option.elim_some, add_comm]
    · refine Or.inr ⟨hk, ?_⟩
      rw [hk, ev, Option.elim_none, add_zero]
  · rw [el, sum_dy]
    ring

theorem Rel.conj
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (hconj : ∀ F τ w G, Gr F τ w G → Gr F τ (conjVec w) (G.map (starRingEnd ℂ)))
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r : ℝ} (h1 : Rel M Gr p z r) : Rel M Gr p (conjVec z) r := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨hF, hw, gd, -, -⟩ := hgood _ _ _ _ hG
  have hG' := hconj _ _ _ _ hG
  have hw' := (hgood _ _ _ _ hG').2.1
  have eb : basePart M.blk (conjVec z) = conjVec (basePart M.blk z) := rfl
  refine ⟨F, _, hG', h.map (starRingEnd ℂ), bh.map _, ?_, t, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 dh
  · rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩
    · refine Or.inl ⟨k, starRingEnd ℂ a, hk, (map_ne_zero _).2 ha, fun m => ?_, by simp⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [conjVec, hz m, map_mul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_mul, eb, valAt_conj hw hw' (gd.2.1 _ I).1, minorIJ_map]
    · refine Or.inr ⟨hk, ?_⟩
      rw [eb, valAt_conj hw hw' (gd.2.2 p hk).2.1, RCLike.norm_conj]
  · rw [pot_conj]
    simp only [eb, conjVec, RCLike.norm_conj]

theorem exists_hom
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (htor : ∀ F τ w G (c : NonPluckerBlocks M.blk → ℂ), (∀ k, c k ≠ 0) → Gr F τ w G → Gr F τ (torusSmul c w) G)
    (hconj : ∀ F τ w G, Gr F τ w G → Gr F τ (conjVec w) (G.map (starRingEnd ℂ)))
    (hcomp : ∀ F F' τ w G G', Gr F τ w G → Gr F' τ w G' → ∃ Rz : Matrix (Fin N) (Fin N) ℂ,
      (∀ a b, IsValueAt M.x (((F.T τ)⁻¹ * F'.T τ) a b) w (Rz a b)) ∧ Rz.det ≠ 0 ∧ G' = Rzᴴ * G * Rz)
    (p : Ψ × Fin N) : ∃ A : HermLine ι, A.a = M.dy p ∧
      (∀ F w G, Gr F p.1 w G → M.IsInducedAt F w p G A) ∧ ∀ z, A.h (conjVec z) = A.h z := by
  let f : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    if h : ∃ r, Rel M Gr p z r then Real.exp h.choose else refNorm (M.dy p) z
  have fr : ∀ z r, Rel M Gr p z r → f z = Real.exp r := fun z r h => by
    have hex : ∃ r, Rel M Gr p z r := ⟨r, h⟩
    simp only [f, dif_pos hex]
    rw [Rel.unique hgood hcomp hex.choose_spec h]
  refine ⟨⟨M.dy p, f, fun z hz => ?_, fun c z hc => ?_⟩, rfl, fun F w G hG z hz ho hn h bh dh => ?_, fun z => ?_⟩
  · simp only [f]
    split_ifs
    exacts [Real.exp_pos _, refNorm_pos _ hz]
  · change f (torusSmul c z) = _
    by_cases h : ∃ r, Rel M Gr p z r
    · obtain ⟨r, h⟩ := h
      rw [fr _ _ h, fr _ _ (h.smul hgood htor hc), Real.exp_add, mul_comm, Real.exp_sum]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Real.log_zpow, Real.exp_log (zpow_pos (norm_pos_iff.2 (hc k)) _)]
    · have h' : ¬ ∃ r, Rel M Gr p (torusSmul c z) r := by
        rintro ⟨r, hr⟩
        have := hr.smul hgood htor (c := fun k => (c k)⁻¹) fun k => inv_ne_zero (hc k)
        have e : torusSmul (fun k => (c k)⁻¹) (torusSmul c z) = z := by
          funext q; simp [torusSmul, hc]
        rw [e] at this
        exact h ⟨_, this⟩
      simp only [f, dif_neg h, dif_neg h']
      exact refNorm_smul _ _ _
  · obtain ⟨c, hc, e⟩ := ho
    have hG' : Gr F p.1 (basePart M.blk z) G := by
      rw [e]; exact htor _ _ _ _ c hc hG
    refine ⟨fun k hk hz => ?_, fun hk => ?_⟩
    · show Real.log (f z) = _
      rw [fr z _ ⟨F, G, hG', h, bh, dh, _, Or.inl ⟨k, 1, hk, one_ne_zero, fun m => by rw [one_mul, hz m], rfl⟩, rfl⟩,
        Real.log_exp]
      simp [hn]
    · show Real.log (f z) = _
      rw [fr z _ ⟨F, G, hG', h, bh, dh, _, Or.inr ⟨hk, rfl⟩, rfl⟩, Real.log_exp]
      simp only [hn, norm_one, Real.log_one, mul_zero, Finset.sum_const_zero]
      ring
  · show f _ = f z
    by_cases h : ∃ r, Rel M Gr p z r
    · obtain ⟨r, h⟩ := h
      rw [fr _ _ h, fr _ _ (h.conj hgood hconj)]
    · have h' : ¬ ∃ r, Rel M Gr p (conjVec z) r := by
        rintro ⟨r, hr⟩
        have := hr.conj hgood hconj
        have e : conjVec (conjVec z) = z := by
          funext q; simp [conjVec]
        rw [e] at this
        exact h ⟨_, this⟩
      simp only [f, dif_neg h, dif_neg h']
      simp [refNorm, conjVec]

end PositivityTheory.Xgp.c_bm_exists_hom
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.X_deg_generic
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_deg_generic : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : IFamily ℚ ι), IsFieldIntersection I → ∀ (D : ℕ) (P : Ideal (MRing ι)) (L : Fin D → HermLine ι), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (pot L) (fun _ => 1) = (I (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D fun j => (L j).a : ℤ) := by
  intro hI K _ ι _ I hF D P L hP hL
  classical
  obtain ⟨I₀, -, hu⟩ := GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full ℚ ι
  have hQ := GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hP
  have h1 := hu I hF _ D (fun j => (L j).a) hQ
  have h2 := hu _ (GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) _ D (fun j => (L j).a) hQ
  rw [h1, ← h2]
  exact GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree K ι P D L hP hL
end

