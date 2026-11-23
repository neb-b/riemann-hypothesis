module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEnergyMin
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EnergyMin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem energy_nonneg {H A : Matrix ι ι ℂ} (h : IsLog H A) : 0 ≤ (Matrix.trace (H * H)).re := by
  obtain ⟨U, d, -, hH, -⟩ := h
  have hh : Hᴴ = H := by
    rw [hH]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    ext i
    simp
  have h1 := (Matrix.posSemidef_conjTranspose_mul_self H).trace_nonneg
  rw [hh] at h1
  exact (Complex.le_def.mp h1).1


omit [Fintype ι] [DecidableEq ι] in
theorem isCompact_box (C : ℝ) : IsCompact {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C} := by
  have h : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {x : ι → ι → ℂ | ∀ i j, ‖x i j‖ ≤ C} =
      Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C := by
    ext x
    simp [Set.mem_pi]
  rw [← e] at h
  exact h

theorem exists_det_one (P : Matrix ι ι ℂ) (hP : IsUnit P.det) :
    ∃ Q : Matrix ι ι ℂ, Q.det = 1 ∧ ∀ x : Matrix ι ι ℂ, Q * x * Q⁻¹ = P * x * P⁻¹ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨P, Matrix.det_isEmpty, fun _ => rfl⟩
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq P.det (Fintype.card_pos (α := ι))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow Fintype.card_ne_zero] at hc
    exact hP.ne_zero hc.symm
  refine ⟨c⁻¹ • P, ?_, fun x => ?_⟩
  · rw [Matrix.det_smul, ← hc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow]
  · have : (c⁻¹ • P)⁻¹ = c • P⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.mul_nonsing_inv _ hP]
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem inv_eq_adj {P : Matrix ι ι ℂ} (hP : P.det = 1) : P⁻¹ = P.adjugate := by
  rw [Matrix.inv_def, hP]
  simp

end GlobalTheory.ClassFin.EnergyMin


open GlobalTheory.ClassFin.EnergyMin in
theorem GlobalTheory.ClassFin.exists_energy_min : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), (∀ s, IsUnit (g s).det) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ (P : Matrix ι ι ℂ) (H : σ → Matrix ι ι ℂ), IsUnit P.det ∧ (∀ s, IsLog (H s) ((P * g s * P⁻¹)ᴴ * (P * g s * P⁻¹))) ∧ ∀ (P' : Matrix ι ι ℂ) (H' : σ → Matrix ι ι ℂ), IsUnit P'.det → (∀ s, IsLog (H' s) ((P' * g s * P'⁻¹)ᴴ * (P' * g s * P'⁻¹))) → ∑ s, (Matrix.trace (H s * H s)).re ≤ ∑ s, (Matrix.trace (H' s * H' s)).re := by
  intro ι _ _ σ _ g hg hspan
  choose H₀ hH₀ using fun s => _root_.GlobalTheory.ClassFin.exists_isLog_gram ι (g s) (hg s)
  let En : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) → ℝ := fun p => ∑ s, (Matrix.trace (p.2 s * p.2 s)).re
  have hEn : Continuous En := by
    refine continuous_finsetSum _ fun s _ => Complex.continuous_re.comp ?_
    have h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s :=
      (continuous_apply s).comp continuous_snd
    exact (h.matrix_mul h).matrix_trace
  let E₀ : ℝ := En (1, H₀)
  let Z : Set (Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) := {p | p.1.det = 1 ∧
    (∀ s, IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))) ∧ En p ≤ E₀}
  have hZc : IsClosed Z := by
    have hlog : IsClosed {p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) |
        ∀ s, IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))} := by
      have : IsClosed (⋂ s, {p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) |
        IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))}) := by
        refine isClosed_iInter fun s => ?_
        have h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s :=
          (continuous_apply s).comp continuous_snd
        have h2 : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.1 * g s * p.1.adjugate :=
          (continuous_fst.matrix_mul continuous_const).matrix_mul continuous_fst.matrix_adjugate
        exact (_root_.GlobalTheory.ClassFin.isClosed_isLog ι).preimage (h.prodMk (h2.matrix_conjTranspose.matrix_mul h2))
      rw [← Set.setOf_forall] at this
      exact this
    have heq : Z = ({p | p.1.det = 1} ∩
        ({p | ∀ s, IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))} ∩
          {p | En p ≤ E₀})) := by
      ext p
      simp [Z]
    rw [heq]
    exact (isClosed_eq continuous_fst.matrix_det continuous_const).inter
      (hlog.inter (isClosed_le hEn continuous_const))
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.ClassFin.entries_le_of_energy_le ι E₀
  obtain ⟨C', hC'⟩ := _root_.GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded ι σ g hspan C
  have hK : IsCompact ({x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C'} ×ˢ
      (Set.pi Set.univ fun _ : σ => {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C})) :=
    (GlobalTheory.ClassFin.EnergyMin.isCompact_box C').prod
      (isCompact_univ_pi fun _ => GlobalTheory.ClassFin.EnergyMin.isCompact_box C)
  have hZ : IsCompact Z := by
    refine hK.of_isClosed_subset hZc ?_
    rintro ⟨P, H⟩ ⟨hd, hl, hE⟩
    have hb : ∀ s i j, ‖(P * g s * P.adjugate) i j‖ ≤ C ∧ ‖H s i j‖ ≤ C := by
      intro s
      refine hC _ _ (hl s) (le_trans ?_ hE)
      exact Finset.single_le_sum (f := fun s => (Matrix.trace (H s * H s)).re)
        (fun t _ => GlobalTheory.ClassFin.EnergyMin.energy_nonneg (hl t)) (Finset.mem_univ s)
    refine ⟨hC' P hd fun s i j => ?_, fun s _ i j => (hb s i j).2⟩
    rw [GlobalTheory.ClassFin.EnergyMin.inv_eq_adj hd]
    exact (hb s i j).1
  have h0 : ((1, H₀) : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) ∈ Z := by
    refine ⟨Matrix.det_one, fun s => ?_, le_rfl⟩
    simpa using hH₀ s
  obtain ⟨⟨P, H⟩, ⟨hd, hl, hE⟩, hmin⟩ := hZ.exists_isMinOn ⟨_, h0⟩ hEn.continuousOn
  have hd' : P.det = 1 := hd
  have hP : IsUnit P.det := hd'.symm ▸ isUnit_one
  refine ⟨P, H, hP, ?_, ?_⟩
  · intro s
    rw [GlobalTheory.ClassFin.EnergyMin.inv_eq_adj hd']
    exact hl s
  · intro P' H' hP' hl'
    obtain ⟨Q, hQ, hQx⟩ := GlobalTheory.ClassFin.EnergyMin.exists_det_one P' hP'
    change En (P, H) ≤ En (Q, H')
    by_cases hle : En (Q, H') ≤ E₀
    · refine hmin (a := (Q, H')) ⟨hQ, fun s => ?_, hle⟩
      simpa only [← hQx (g s), GlobalTheory.ClassFin.EnergyMin.inv_eq_adj hQ] using hl' s
    · exact hE.trans (not_le.mp hle).le
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentatives
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_uniformizer_and_residue_representatives :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  intro F _ _ v
  classical
  have h2 : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have h3 : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
      ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := GlobalTheory.Idele.exists_valued_sub_le v hx 1
    refine ⟨a, lt_of_le_of_lt ha ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨?_, h2, h3, ?_⟩
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    exact ⟨π, hπ, (h2 π).trans hπ⟩
  · haveI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    choose s hs using Ideal.Quotient.mk_surjective (I := v.asIdeal)
    refine ⟨Finset.univ.image fun q : 𝓞 F ⧸ v.asIdeal =>
      algebraMap F (v.adicCompletion F) ((s q : 𝓞 F) : F), ?_, ?_, ?_⟩
    · refine Finset.card_image_le.trans (le_of_eq ?_)
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Finset.card_univ, Nat.card_eq_fintype_card]
    · intro r hr
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
      rw [h2]
      exact v.valuation_le_one (s q)
    · intro x hx
      obtain ⟨a, ha⟩ := h3 x hx
      refine ⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ a, Finset.mem_univ _, rfl⟩, ?_⟩
      have hm : a - s (Ideal.Quotient.mk _ a) ∈ v.asIdeal := Ideal.Quotient.eq.1 (hs _).symm
      have hl : v.valuation F (algebraMap (𝓞 F) F (a - s (Ideal.Quotient.mk _ a))) < 1 :=
        (v.valuation_lt_one_iff_mem _).2 hm
      rw [← h2, map_sub, map_sub] at hl
      rw [← sub_add_sub_cancel x (algebraMap F (v.adicCompletion F) (a : F))]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hl)

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsHermiteReducedLatticeBasis
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.HermiteReduction

theorem exists_lt_two_mul {S : Type} [Nonempty S] (f : S → ℝ) (c : ℝ) (hc : 0 < c) (hf : ∀ s, c ≤ f s) :
    ∃ s, ∀ t, f s < 2 * f t := by
  have hbdd : BddBelow (Set.range f) := ⟨c, by rintro _ ⟨s, rfl⟩; exact hf s⟩
  have hm : c ≤ ⨅ s, f s := le_ciInf hf
  have hlt : ⨅ s, f s < 2 * ⨅ s, f s := by linarith
  obtain ⟨s, hs⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨s, fun t => hs.trans_le (by linarith [ciInf_le hbdd t])⟩

noncomputable def gramMinor {N : ℕ} (x : Matrix (Fin N) (Fin N) ℝ) (j : Fin (N + 1)) : ℝ :=
  ((xᵀ * x).submatrix (Fin.castLE (Nat.lt_succ_iff.mp j.2)) (Fin.castLE (Nat.lt_succ_iff.mp j.2))).det

theorem prod_castLE_succ {N : ℕ} (f : Fin N → ℝ) (p q : Fin N) (hq : (q : ℕ) = p + 1) (h : (q : ℕ) ≤ N) :
    ∏ i : Fin q, f (Fin.castLE h i) = (∏ l ∈ Finset.univ.filter (· < p), f l) * f p := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq'⟩ := q
  simp only at hq h ⊢
  subst hq
  rw [Fin.prod_univ_castSucc]
  congr 1
  refine Finset.prod_bij (fun i _ => Fin.castLE h i.castSucc) ?_ ?_ ?_ ?_
  · intro i _
    simp [Fin.lt_def]
  · intro i _ j _ hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)
  · intro l hl
    have hl' : (l : ℕ) < p := by simpa [Fin.lt_def] using hl
    exact ⟨⟨l, hl'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _
    rfl

theorem mul_upper {N : ℕ} (n m : Matrix (Fin N) (Fin N) ℝ) (hn1 : ∀ i, n i i = 1) (hn0 : ∀ i j, j < i → n i j = 0)
    (hm1 : ∀ i, m i i = 1) (hm0 : ∀ i j, j < i → m i j = 0) :
    (∀ i, (n * m) i i = 1) ∧ ∀ i j, j < i → (n * m) i j = 0 := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hn1, hm1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hn0 i l h, zero_mul]
      · rw [hm0 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hn0 i l h, zero_mul]
    · rw [hm0 l j (lt_of_lt_of_le hij h), mul_zero]

theorem le_of_swap {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ)
    (hk : kᵀ * k = 1) (ha : ∀ i, 0 < a i) (hn1 : ∀ i, n i i = 1) (hn0 : ∀ i j, j < i → n i j = 0)
    (hν : ∀ i j, i < j → |n i j| ≤ 1 / 2) (p q : Fin N) (hq : (q : ℕ) = p + 1)
    (hlt : ∏ j, gramMinor (k * diagonal a * n) j <
      2 * ∏ j, gramMinor ((k * diagonal a * n).submatrix id (Equiv.swap p q)) j) : a p ≤ 2 * a q := by
  set g := k * diagonal a * n with hg
  have hpq : p < q := by rw [Fin.lt_def]; omega
  have hqN : (q : ℕ) ≤ N := q.2.le
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.ClassFin.gram_minor_swap_columns N k a n g (g.submatrix id (Equiv.swap p q)) p q hk hn1 hn0 hq rfl rfl
  have hG : ∀ j : Fin (N + 1),
      gramMinor g j = ∏ i : Fin j, a (Fin.castLE (Nat.lt_succ_iff.mp j.2) i) ^ 2 :=
    fun j => _root_.GlobalTheory.ClassFin.det_leading_gram_iwasawa N k a n hk hn1 hn0 j _
  let qq : Fin (N + 1) := ⟨q, Nat.lt_succ_of_le hqN⟩
  have hpos : ∀ j, 0 < gramMinor g j := fun j => by
    rw [hG]
    exact Finset.prod_pos fun i _ => pow_pos (ha _) 2
  have hrest : ∏ j ∈ Finset.univ.erase qq, gramMinor (g.submatrix id (Equiv.swap p q)) j =
      ∏ j ∈ Finset.univ.erase qq, gramMinor g j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne : (j : ℕ) ≠ q := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
    exact h1 j (Nat.lt_succ_iff.mp j.2) hne
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ qq),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ qq), hrest] at hlt
  have hR : 0 < ∏ j ∈ Finset.univ.erase qq, gramMinor g j := Finset.prod_pos fun j _ => hpos j
  have hlt' : gramMinor g qq < 2 * gramMinor (g.submatrix id (Equiv.swap p q)) qq := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith [mul_le_mul_of_nonneg_right hc' hR.le]
  have eG : gramMinor g qq = (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * a p ^ 2 := by
    rw [hG]
    exact prod_castLE_succ (fun i => a i ^ 2) p q hq _
  have eG' : gramMinor (g.submatrix id (Equiv.swap p q)) qq =
      (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := h2 hqN
  rw [eG, eG'] at hlt'
  have hP : 0 < ∏ l ∈ Finset.univ.filter (· < p), a l ^ 2 :=
    Finset.prod_pos fun l _ => pow_pos (ha l) 2
  have hn : n p q ^ 2 ≤ 1 / 4 := by
    have h3 := abs_le.mp (hν p q hpq)
    nlinarith [h3.1, h3.2]
  have key : a p ^ 2 < 2 * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith [mul_le_mul_of_nonneg_left hc' hP.le]
  have hap := ha p
  have haq := ha q
  by_contra hc
  have hc' := not_le.mp hc
  nlinarith [mul_lt_mul'' hc' hc' (by positivity) (by positivity),
    mul_le_mul_of_nonneg_right hn (sq_nonneg (a p))]

theorem exists_reduced : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (γ : Matrix (Fin N) (Fin N) ℤ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), (γ.det = 1 ∨ γ.det = -1) ∧ kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ (∀ i j, i < j → |n i j| ≤ 1 / 2) ∧ (∀ p q : Fin N, (q : ℕ) = p + 1 → a p ≤ 2 * a q) ∧ g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  intro N g hg
  obtain ⟨c, hc, hcb⟩ := _root_.GlobalTheory.ClassFin.gram_leading_minor_lower_bound N g hg
  let S := {γ : Matrix (Fin N) (Fin N) ℤ // γ.det = 1 ∨ γ.det = -1}
  have : Nonempty S := ⟨⟨1, Or.inl Matrix.det_one⟩⟩
  have hdet0 : ∀ γ : S, γ.1.det ≠ 0 := fun γ => by
    rcases γ.2 with h | h <;> rw [h] <;> norm_num
  have hbound : ∀ γ : S, c ^ (N + 1) ≤ ∏ j, gramMinor (g * γ.1.map (Int.cast : ℤ → ℝ)) j := by
    intro γ
    calc c ^ (N + 1) = ∏ _j : Fin (N + 1), c := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hc.le)
          (fun j _ => hcb γ.1 (hdet0 γ) j (Nat.lt_succ_iff.mp j.2))
  obtain ⟨γ0, hγ0⟩ := exists_lt_two_mul
    (fun γ : S => ∏ j, gramMinor (g * γ.1.map (Int.cast : ℤ → ℝ)) j) (c ^ (N + 1)) (pow_pos hc _) hbound
  have hgd : (g * γ0.1.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [Matrix.det_mul]
    refine mul_ne_zero hg ?_
    rw [← Int.cast_det]
    exact_mod_cast hdet0 γ0
  obtain ⟨k, a, n, hk, ha, hn1, hn0, hgk⟩ := _root_.GlobalTheory.ClassFin.iwasawa_real N _ hgd
  obtain ⟨ν, hν1, hν0, hνb⟩ := _root_.GlobalTheory.ClassFin.unipotent_size_reduction N n hn1 hn0
  have hνR1 : ∀ i, ν.map (Int.cast : ℤ → ℝ) i i = 1 := fun i => by simp [hν1]
  have hνR0 : ∀ i j, j < i → ν.map (Int.cast : ℤ → ℝ) i j = 0 := fun i j h => by simp [hν0 i j h]
  obtain ⟨hn'1, hn'0⟩ := mul_upper n _ hn1 hn0 hνR1 hνR0
  have hνdet : ν.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j h => hν0 i j h)]
    simp [hν1]
  have hγdet : (γ0.1 * ν).det = 1 ∨ (γ0.1 * ν).det = -1 := by
    rw [Matrix.det_mul, hνdet, mul_one]
    exact γ0.2
  have hmap : (γ0.1 * ν).map (Int.cast : ℤ → ℝ) =
      γ0.1.map (Int.cast : ℤ → ℝ) * ν.map (Int.cast : ℤ → ℝ) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  have heq : g * (γ0.1 * ν).map (Int.cast : ℤ → ℝ) =
      k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ)) := by
    rw [hmap, ← Matrix.mul_assoc, hgk, Matrix.mul_assoc (k * diagonal a)]
  have hΦ : ∏ j, gramMinor (k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ))) j =
      ∏ j, gramMinor (g * γ0.1.map (Int.cast : ℤ → ℝ)) j := by
    rw [hgk]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold gramMinor
    rw [_root_.GlobalTheory.ClassFin.det_leading_gram_iwasawa N k a _ hk hn'1 hn'0 j _, _root_.GlobalTheory.ClassFin.det_leading_gram_iwasawa N k a n hk hn1 hn0 j _]
  refine ⟨γ0.1 * ν, k, a, n * ν.map (Int.cast : ℤ → ℝ), hγdet, hk, ha, hn'1, hn'0, hνb,
    fun p q hq => ?_, heq⟩
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  let γ' : S := ⟨(γ0.1 * ν).submatrix id (Equiv.swap p q), by
    rw [Matrix.det_permute', Equiv.Perm.sign_swap hpq]
    rcases hγdet with h | h <;> simp [h]⟩
  have hsw : g * γ'.1.map (Int.cast : ℤ → ℝ) =
      (k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ))).submatrix id (Equiv.swap p q) := by
    rw [← heq]
    ext i j
    rfl
  refine le_of_swap k a _ hk ha hn'1 hn'0 hνb p q hq ?_
  rw [hΦ, ← hsw]
  exact hγ0 γ'

end GlobalTheory.ClassFin.HermiteReduction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIndependentPrimeRelIndexSubgroups
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem relIndex_eq_prime_of_generated {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime)
    (E K : Subgroup G) (x : G) (hxE : x ∈ E) (hxK : x ∉ K) (hxp : x ^ p ∈ K)
    (hgen : ∀ y ∈ E, ∃ k : ℕ, y / x ^ k ∈ K) : K.relIndex E = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set c : E ⧸ K.subgroupOf E := QuotientGroup.mk (⟨x, hxE⟩ : E) with hc
  have ho : orderOf c = p := by
    apply orderOf_eq_prime
    · rw [hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hxp
    · rw [hc, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hxK
  have hall : ∀ y : E ⧸ K.subgroupOf E, y ∈ Submonoid.powers c := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hgen y y.2
    refine ⟨k, ?_⟩
    simp only [hc]
    rw [← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa using hk
  rw [Subgroup.relIndex, Subgroup.index, ← ho]
  exact (orderOf_eq_card_of_forall_mem_powers hall).symm

theorem exists_independent_prime_relIndex_subgroups (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι]
    (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ) (hp : p.Prime)
    (hH : H.relIndex U = p ^ m) (h1 : ∀ i, good i → U ⊓ H ≤ K i)
    (h2 : ∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i)
    (h2' : ∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i)
    (h3 : ∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) (k : ℕ) (hk : k ≤ m) :
    ∃ T : Finset ι, T.card = k ∧ (∀ i ∈ T, good i) ∧
      (∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j) ∧
      ∃ D : Subgroup G, (∀ x, x ∈ D ↔ ∀ i ∈ T, x ∈ K i) ∧ D.relIndex U = p ^ k := by
  induction k with
  | zero =>
    refine ⟨∅, rfl, by simp, by simp, ⊤, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hT, hg, hA, D, hD, hDi⟩ := ih (by omega)
    have hx : ∃ x ∈ U, x ∈ D ∧ x ∉ H := by
      by_contra hcon
      push Not at hcon
      have heq : D ⊓ U = H ⊓ U := by
        ext x
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨a, b⟩
          exact ⟨hcon x b a, b⟩
        · rintro ⟨a, b⟩
          exact ⟨(hD x).2 fun i hi => h1 i (hg i hi) ⟨b, a⟩, b⟩
      have h4 : D.relIndex U = H.relIndex U := by
        rw [← Subgroup.inf_relIndex_right D U, heq, Subgroup.inf_relIndex_right]
      rw [hDi, hH] at h4
      have := Nat.pow_right_injective hp.two_le h4
      omega
    obtain ⟨x, hxU, hxD, hxH⟩ := hx
    obtain ⟨j, hj, hxj⟩ := h3 x hxU hxH
    have hjT : j ∉ T := fun h => hxj ((hD x).1 hxD j h)
    refine ⟨insert j T, by rw [Finset.card_insert_of_notMem hjT, hT], ?_, ?_, K j ⊓ D, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hj
      · exact hg i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨x, hxU, hxj, fun l hl hli => ?_⟩
        rcases Finset.mem_insert.1 hl with rfl | hl
        · exact absurd rfl hli
        · exact (hD x).1 hxD l hl
      · obtain ⟨u, huU, hui, hu⟩ := hA i hi
        obtain ⟨n, hn⟩ := h2' j hj x hxU hxj u huU
        refine ⟨u / x ^ n, U.div_mem huU (U.pow_mem hxU n), ?_, fun l hl hli => ?_⟩
        · intro h
          apply hui
          have := (K i).mul_mem h ((K i).pow_mem ((hD x).1 hxD i hi) n)
          simpa using this
        · rcases Finset.mem_insert.1 hl with rfl | hl
          · exact hn
          · exact (K l).div_mem (hu l hl hli) ((K l).pow_mem ((hD x).1 hxD l hl) n)
    · intro y
      simp only [Subgroup.mem_inf, hD, Finset.forall_mem_insert]
    · have h5 : (K j).relIndex (D ⊓ U) = p :=
        relIndex_eq_prime_of_generated hp (D ⊓ U) (K j) x ⟨hxD, hxU⟩ hxj (h2 j hj x hxU)
          (fun y hy => h2' j hj x hxU hxj y hy.2)
      rw [← Subgroup.relIndex_inf_mul_relIndex, h5, hDi, pow_succ, mul_comm]

theorem exists_indep_prime_index : ∀ (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι] (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ), p.Prime → H.relIndex U = p ^ m → (∀ i, good i → U ⊓ H ≤ K i) → (∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i) → (∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i) → (∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) → ∃ T : Finset ι, T.card = m ∧ (∀ i ∈ T, good i) ∧ ∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j := by
  intro p G ι _ _ U H K good m hp hH h1 h2 h2' h3
  obtain ⟨T, a, b, c, -⟩ :=
    exists_independent_prime_relIndex_subgroups p G ι U H K good m hp hH h1 h2 h2' h3 m le_rfl
  exact ⟨T, a, b, c⟩

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsKum
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isKum : ∀ (p : ℕ) (F : Type) [Field F] [CharZero F] (ζ δ : F), p.Prime → IsPrimitiveRoot ζ p → (∀ r : F, r ^ p ≠ δ) → ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ := by
  intro p F _ _ ζ δ hp hζ hδ
  have : Fact (Irreducible (X ^ p - C δ)) := ⟨X_pow_sub_C_irreducible_of_prime hp hδ⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨AdjoinRoot (X ^ p - C δ), inferInstance, inferInstance, AdjoinRoot.root _,
    autAdjoinRootXPowSubC p δ hζ.toRootsOfUnity, ?_⟩
  refine ⟨hp, hζ, hδ, ?_, ?_, AdjoinRoot.adjoinRoot_eq_top⟩
  · have h := AdjoinRoot.eval₂_root (X ^ p - C δ)
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
    rw [h, AdjoinRoot.algebraMap_eq]
  · rw [autAdjoinRootXPowSubC_root, Algebra.smul_def, IsPrimitiveRoot.val_toRootsOfUnity_coe]

end GlobalTheory.CNorm
end

