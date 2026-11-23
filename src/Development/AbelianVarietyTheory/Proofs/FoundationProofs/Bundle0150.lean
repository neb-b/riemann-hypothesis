module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeULeftRepresentativesLevelChange
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lrep_repU_of_dvd (M l : ℕ) (hl : l.Prime) (hlM : l ∣ M) :
    LRep M {δ : M2 | δ.det = l ∧ (M : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0} (repU l) := by
  have hlM' : (l : ℤ) ∣ (M : ℤ) := by exact_mod_cast hlM
  have hpZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have key : ∀ γ : SL(2, ℤ), (M : ℤ) ∣ (γ : M2) 1 0 → ¬ (l : ℤ) ∣ (γ : M2) 0 0 := by
    intro γ hc ha
    have hdet : (γ : M2).det = 1 := γ.2
    rw [Matrix.det_fin_two] at hdet
    have : (l : ℤ) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right (hlM'.trans hc) _)
    exact hpZ.not_dvd_one this
  have ent : ∀ (A : M2) (j : Fin l), (A * repU l j) 0 0 = A 0 0 ∧ (A * repU l j) 1 0 = A 1 0 ∧
      (A * repU l j) 0 1 = A 0 0 * (j : ℕ) + A 0 1 * l ∧
      (A * repU l j) 1 1 = A 1 0 * (j : ℕ) + A 1 1 * l := by
    intro A j
    simp [repU, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨γ, hγ⟩, j⟩ -
    have hc : (M : ℤ) ∣ (γ : M2) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨e1, e2, -, -⟩ := ent (γ : M2) j
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.det_mul, repU, Matrix.det_fin_two_of]
      rw [show (γ : M2).det = 1 from γ.2]
      simp
    · simpa [e2] using hc
    · simpa [e1] using key γ hc
  · rintro ⟨⟨γ, hγ⟩, j⟩ - ⟨⟨γ', hγ'⟩, j'⟩ - h
    simp only at h
    have hc : (M : ℤ) ∣ (γ : M2) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨e1, e2, e3, e4⟩ := ent (γ : M2) j
    obtain ⟨f1, f2, f3, f4⟩ := ent (γ' : M2) j'
    have h00 : (γ : M2) 0 0 = (γ' : M2) 0 0 := by rw [← e1, ← f1, h]
    have h10 : (γ : M2) 1 0 = (γ' : M2) 1 0 := by rw [← e2, ← f2, h]
    have h01 : (γ : M2) 0 0 * (j : ℕ) + (γ : M2) 0 1 * l = (γ' : M2) 0 0 * (j' : ℕ) + (γ' : M2) 0 1 * l := by
      rw [← e3, ← f3, h]
    have h11 : (γ : M2) 1 0 * (j : ℕ) + (γ : M2) 1 1 * l = (γ' : M2) 1 0 * (j' : ℕ) + (γ' : M2) 1 1 * l := by
      rw [← e4, ← f4, h]
    have hdiv : (l : ℤ) ∣ (γ : M2) 0 0 * (((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ)) :=
      ⟨(γ' : M2) 0 1 - (γ : M2) 0 1, by rw [h00] at h01 ⊢; linear_combination h01⟩
    have hd2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ) :=
      (hpZ.dvd_or_dvd hdiv).resolve_left (key γ hc)
    have hjj : j = j' := by
      have hj := j.2
      have hj' := j'.2
      obtain ⟨k, hk⟩ := hd2
      have hk0 : k = 0 := by
        rcases lt_trichotomy k 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      subst hk0
      ext
      omega
    subst hjj
    have g01 : (γ : M2) 0 1 = (γ' : M2) 0 1 := by
      apply mul_right_cancel₀ hl0; rw [h00] at h01; linarith
    have g11 : (γ : M2) 1 1 = (γ' : M2) 1 1 := by
      apply mul_right_cancel₀ hl0; rw [h10] at h11; linarith
    have : γ = γ' := by
      ext i k; fin_cases i <;> fin_cases k <;> simp [h00, h10, g01, g11]
    subst this
    rfl
  · rintro δ ⟨hdet, hc, ha⟩
    haveI : Fact l.Prime := ⟨hl⟩
    have hlc : (l : ℤ) ∣ δ 1 0 := hlM'.trans hc
    rw [Matrix.det_fin_two] at hdet
    have hld : (l : ℤ) ∣ δ 1 1 := by
      have : (l : ℤ) ∣ δ 0 0 * δ 1 1 := ⟨1 + (δ 0 1) * ((δ 1 0) / l), by
        obtain ⟨t, ht⟩ := hlc
        rw [ht, Int.mul_ediv_cancel_left _ hl0]
        linear_combination hdet + (δ 0 1) * ht⟩
      exact (hpZ.dvd_or_dvd this).resolve_left ha
    have haZ : ((δ 0 0 : ℤ) : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ha
    let j : Fin l := ⟨(((δ 0 1 : ℤ) : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹).val, ZMod.val_lt _⟩
    have hjZ : ((j : ℕ) : ZMod l) = ((δ 0 1 : ℤ) : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹ :=
      ZMod.natCast_zmod_val _
    have hb : (l : ℤ) ∣ δ 0 1 - δ 0 0 * (j : ℕ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hjZ]
      field_simp
      ring
    have hdd : (l : ℤ) ∣ δ 1 1 - δ 1 0 * (j : ℕ) := dvd_sub hld (dvd_mul_of_dvd_left hlc _)
    obtain ⟨e, he⟩ := hb
    obtain ⟨f, hf⟩ := hdd
    have hγdet : (!![δ 0 0, e; δ 1 0, f] : M2).det = 1 := by
      rw [Matrix.det_fin_two_of]
      apply mul_left_cancel₀ hl0
      linear_combination -(δ 0 0) * hf + (δ 1 0) * he + hdet
    let γ : SL(2, ℤ) := ⟨!![δ 0 0, e; δ 1 0, f], hγdet⟩
    have hγ : γ ∈ Gamma0 M := by
      rw [Gamma0_mem]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa [γ] using hc)
    refine ⟨(⟨γ, hγ⟩, j), Set.mem_univ _, ?_⟩
    obtain ⟨e1, e2, e3, e4⟩ := ent (γ : M2) j
    ext i k; fin_cases i <;> fin_cases k
    · simpa [γ] using e1
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e3 ⊢
      rw [e3]; simp [γ]; linarith
    · simpa [γ] using e2
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e4 ⊢
      rw [e4]; simp [γ]; linarith

theorem lrep_repU (L l : ℕ) (hl : l.Prime) :
    (l ∣ L → LRep L (DU L l) (repU l)) ∧
      (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) := by
  refine ⟨fun h => lrep_repU_of_dvd L l hl h, fun _ => ?_⟩
  have hs : {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} =
      {δ : M2 | δ.det = l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0} := by
    ext δ
    simp only [DU, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩; exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h4, h3⟩
      exact ⟨⟨h1, (Int.natCast_dvd_natCast.mpr (dvd_mul_right L l)).trans h4, h3⟩, h4⟩
  rw [hs]
  exact lrep_repU_of_dvd (L * l) l hl (dvd_mul_left l L)

theorem zrepU : ∀ L l : ℕ, l.Prime → (l ∣ L → LRep L (DU L l) (repU l)) ∧
    (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) :=
  fun L l hl => lrep_repU L l hl

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermiteRightFactorOfPrimeDvdDet
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory

theorem hermite_right_factor_prime_det : ∀ (p : ℕ), p.Prime → ∀ (m : Matrix (Fin 2) (Fin 2) ℤ), (p : ℤ) ∣ m.det → (∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![(p : ℤ), 0; 0, 1]) ∨ ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
  intro p hp m hdet
  haveI := Fact.mk hp
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℤ, m = !![a, b; c, d] :=
    ⟨m 0 0, m 0 1, m 1 0, m 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  rw [Matrix.det_fin_two_of] at hdet
  have hdetZ : (a : ZMod p) * d = b * c := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a * d - b * c) p).2 hdet
    push_cast at this
    linear_combination this
  have fin : ∀ k : ℕ, k < p → (k : ZMod p) * a = b → (k : ZMod p) * c = d →
      ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, !![a, b; c, d] = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
    intro k hk h1 h2
    obtain ⟨u, hu⟩ : (p : ℤ) ∣ b - k * a := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h1]; ring
    obtain ⟨v, hv⟩ : (p : ℤ) ∣ d - k * c := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h2]; ring
    refine ⟨k, hk, !![a, u; c, v], ?_⟩
    rw [Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  by_cases ha : (a : ZMod p) = 0
  · by_cases hc : (c : ZMod p) = 0
    · left
      obtain ⟨a', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 ha
      obtain ⟨c', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).1 hc
      refine ⟨!![a', b; c', d], ?_⟩
      rw [Matrix.mul_fin_two]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
    · right
      refine fin ((d : ZMod p) * (c : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_
      · rw [ZMod.natCast_zmod_val]
        calc (d : ZMod p) * (c : ZMod p)⁻¹ * a = (a * d) * (c : ZMod p)⁻¹ := by ring
          _ = b * c * (c : ZMod p)⁻¹ := by rw [hdetZ]
          _ = b := by rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
      · rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · right
    refine fin ((b : ZMod p) * (a : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_
    · rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    · rw [ZMod.natCast_zmod_val]
      calc (b : ZMod p) * (a : ZMod p)⁻¹ * c = (b * c) * (a : ZMod p)⁻¹ := by ring
        _ = (a * d) * (a : ZMod p)⁻¹ := by rw [hdetZ]
        _ = d := by rw [mul_comm (a : ZMod p) d, mul_assoc, mul_inv_cancel₀ ha, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnFdImPowMulExp
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem fd_half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

theorem fd_volume_lt_top : volume ModularGroup.fd < ⊤ := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  set S : Set ℂ := Complex.re ⁻¹' Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∩ Complex.im ⁻¹' Set.Ici (1 / 2 : ℝ)
    with hS
  have hsub : ((↑) '' ModularGroup.fd : Set ℂ) ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨abs_le.1 hz.2, fd_half_le_im hz⟩
  have hSm : MeasurableSet S :=
    (Complex.measurable_re measurableSet_Icc).inter (Complex.measurable_im measurableSet_Ici)
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  rw [← lintegral_indicator hSm]
  set g : ℂ → ENNReal := fun z => ↑((1 / ‖z.im‖₊) ^ 2 : NNReal) with hg
  have e := (Complex.volume_preserving_equiv_real_prod.symm _).lintegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding (S.indicator g)
  rw [← e]
  have hle : ∀ p : ℝ × ℝ, S.indicator g (Complex.measurableEquivRealProd.symm p) ≤
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ENNReal)) p.1 *
      (Set.Ici (1 / 2 : ℝ)).indicator (fun y => ENNReal.ofReal (1 / y ^ 2)) p.2 := by
    rintro ⟨x, y⟩
    have hsy : Complex.measurableEquivRealProd.symm (x, y) = ⟨x, y⟩ := rfl
    rw [hsy]
    by_cases hm : (⟨x, y⟩ : ℂ) ∈ S
    · obtain ⟨hx, hy⟩ := id hm
      have hx' : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := hx
      have hy' : y ∈ Set.Ici (1 / 2 : ℝ) := hy
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hx', Set.indicator_of_mem hy', one_mul]
      apply le_of_eq
      simp only [hg]
      rw [ENNReal.ofReal]
      congr 1
      ext
      simp [sq_abs]
      positivity
    · rw [Set.indicator_of_notMem hm]
      exact bot_le
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [Measure.volume_eq_prod, lintegral_prod_mul (aemeasurable_const.indicator measurableSet_Icc)
    ((by fun_prop : Measurable fun y : ℝ => ENNReal.ofReal (1 / y ^ 2)).aemeasurable.indicator
      measurableSet_Ici)]
  rw [lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Ici,
    setLIntegral_const, one_mul, Real.volume_Icc]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have h : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Set.Ioi (1 / 2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h' : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Set.Ici (1 / 2 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) ≤ y := le_trans (by norm_num) (le_of_lt hy)
    simp only
    rw [Real.rpow_neg hy0, Real.rpow_two, one_div]
  exact h'.lintegral_lt_top

theorem fd_measurableSet : MeasurableSet ModularGroup.fd := by
  apply IsClosed.measurableSet
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (UpperHalfPlane.continuous_re.abs) continuous_const
  exact h1.inter h2

theorem pow_mul_exp_neg_le (δ : ℝ) (A : ℕ) (hδ : 0 < δ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ A * Real.exp (-δ * y) ≤ (A.factorial : ℝ) / δ ^ A := by
  have h := Real.pow_div_factorial_le_exp (δ * y) (mul_nonneg hδ.le hy) A
  have hf : (0 : ℝ) < A.factorial := by exact_mod_cast A.factorial_pos
  have hδA : 0 < δ ^ A := pow_pos hδ A
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ hδA, neg_mul, Real.exp_neg]
  have he := Real.exp_pos (δ * y)
  calc y ^ A * (Real.exp (δ * y))⁻¹ * δ ^ A = δ ^ A * y ^ A * (Real.exp (δ * y))⁻¹ := by ring
    _ ≤ Real.exp (δ * y) * A.factorial * (Real.exp (δ * y))⁻¹ := by gcongr
    _ = A.factorial := by field_simp

theorem integrableOn_fd_im_pow_mul_exp :
    ∀ (δ : ℝ) (A : ℕ), 0 < δ →
      IntegrableOn (fun τ : ℍ => τ.im ^ A * Real.exp (-δ * τ.im)) ModularGroup.fd := by
  intro δ A hδ
  refine Measure.integrableOn_of_bounded (M := (A.factorial : ℝ) / δ ^ A) fd_volume_lt_top.ne
    (by fun_prop : Continuous fun τ : ℍ => τ.im ^ A * Real.exp (-δ * τ.im)).aestronglyMeasurable
    ((ae_restrict_iff' fd_measurableSet).2 (Filter.Eventually.of_forall fun τ _ => ?_))
  have hy := τ.im_pos.le
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_mul_exp_neg_le δ A hδ hy

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsBoundedAtImInftyOfPeriodicPolynomialBound
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem periodic_comp_ofComplex_of_vadd' {f : ℍ → ℂ} {M : ℝ} (hper : ∀ τ : ℍ, f (M +ᵥ τ) = f τ) :
    Function.Periodic (f ∘ ofComplex) M := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]
  · push_neg at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem qParam_add_period {M : ℝ} (hM : M ≠ 0) (z : ℂ) :
    Function.Periodic.qParam M (z + M) = Function.Periodic.qParam M z := by
  unfold Function.Periodic.qParam
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [show 2 * π * Complex.I * (z + M) / M = 2 * π * Complex.I * z / M + 2 * π * Complex.I by field_simp,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem isBoundedAtImInfty_of_periodic_of_polyBound :
    ∀ (f : ℍ → ℂ) (h : ℕ) (C : ℝ) (A : ℕ), 0 < h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
      (∀ τ : ℍ, f ((h : ℝ) +ᵥ τ) = f τ) →
      (∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ h → ‖f τ‖ ≤ C * τ.im ^ A) → IsBoundedAtImInfty f := by
  intro f h C A hh hf hper hbd
  set M : ℝ := (h : ℝ) with hMdef
  have hM : 0 < M := by simp [hMdef, hh]
  have hperF : Function.Periodic (f ∘ ofComplex) M := periodic_comp_ofComplex_of_vadd' hper

  have hbd' : ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ C * τ.im ^ A := by
    intro τ hτ
    set n : ℤ := ⌊τ.re / M⌋
    have h1 : (n : ℝ) ≤ τ.re / M := Int.floor_le _
    have h2 : τ.re / M < n + 1 := Int.lt_floor_add_one _
    have hw : 0 < ((τ : ℂ) - n * M).im := by simpa using τ.im_pos
    set σ : ℍ := ⟨(τ : ℂ) - n * M, hw⟩
    have hσ : f σ = f τ := by
      have := hperF.sub_int_mul_eq (x := (τ : ℂ)) n
      simp only [Function.comp_apply, ofComplex_apply] at this
      rw [← this, ofComplex_apply_of_im_pos hw]
    have hσim : σ.im = τ.im := by
      change ((τ : ℂ) - (n : ℂ) * (M : ℂ)).im = τ.im
      simp
    have hσre : σ.re = τ.re - n * M := by
      change ((τ : ℂ) - (n : ℂ) * (M : ℂ)).re = τ.re - n * M
      simp
    have hre1 : n * M ≤ τ.re := by rwa [le_div_iff₀ hM] at h1
    have hre2 : τ.re < (n + 1) * M := by rwa [div_lt_iff₀ hM] at h2
    have habs : |σ.re| ≤ h := by
      rw [hσre, abs_le]
      constructor <;> nlinarith
    rw [← hσ, ← hσim]
    exact hbd σ (hσim ▸ hτ) habs

  set g : ℍ → ℂ := fun τ ↦ f τ * Function.Periodic.qParam M τ with hg
  have hnormg : ∀ τ : ℍ, ‖g τ‖ = ‖f τ‖ * Real.exp (-2 * π * τ.im / M) := by
    intro τ
    simp [hg, norm_mul, Function.Periodic.norm_qParam]
  have hgdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g :=
    hf.mul ((Function.Periodic.differentiable_qParam (h := M)).comp_mdifferentiable
      UpperHalfPlane.mdifferentiable_coe)
  have hgper : ∀ τ : ℍ, g (M +ᵥ τ) = g τ := by
    intro τ
    simp only [hg, hper, coe_vadd]
    rw [add_comm, qParam_add_period hM.ne']
  have hgzero : IsZeroAtImInfty g := by
    set c : ℝ := 2 * π / M with hc
    have hcpos : 0 < c := by positivity
    have hT : Tendsto (fun y : ℝ ↦ C * (c⁻¹) ^ A * ((c * y) ^ A * Real.exp (-(c * y)))) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero A).comp
        (tendsto_id.const_mul_atTop hcpos)).const_mul (C * (c⁻¹) ^ A)
    have heq : ∀ y : ℝ, C * (c⁻¹) ^ A * ((c * y) ^ A * Real.exp (-(c * y))) =
        C * y ^ A * Real.exp (-2 * π * y / M) := by
      intro y
      have : -(c * y) = -2 * π * y / M := by rw [hc]; ring
      rw [this, mul_pow, ← mul_assoc, ← mul_assoc, mul_assoc C, ← mul_pow, inv_mul_cancel₀ hcpos.ne',
        one_pow, mul_one]
    simp_rw [heq] at hT
    have hT' : Tendsto (fun τ : ℍ ↦ C * τ.im ^ A * Real.exp (-2 * π * τ.im / M)) atImInfty (𝓝 0) :=
      hT.comp tendsto_comap
    refine squeeze_zero_norm' ?_ hT'
    refine (atImInfty_mem _).2 ⟨1, fun τ hτ ↦ ?_⟩
    rw [Set.mem_setOf_eq, hnormg]
    exact mul_le_mul_of_nonneg_right (hbd' τ hτ) (Real.exp_pos _).le
  have hgbdd : IsBoundedAtImInfty g := hgzero.boundedAtFilter
  have hdecay := hgzero.exp_decay_atImInfty hM (periodic_comp_ofComplex_of_vadd' hgper) hgdiff hgbdd
  obtain ⟨K, hK⟩ := hdecay.bound
  obtain ⟨B, hB⟩ := (atImInfty_mem _).1 hK
  refine isBoundedAtImInfty_iff.2 ⟨K, B, fun τ hτ ↦ ?_⟩
  have h1 := hB τ hτ
  simp only [Set.mem_setOf_eq, hnormg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  exact le_of_mul_le_mul_right h1 (Real.exp_pos _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KillsTranslatesSumMulMeanDifferenceEq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem kills_sum_dif_eq : ∀ (L : ℕ) (v : ℤ × ℤ) (Φ G : ℤ × ℤ → ℂ), 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x => ‖G x‖) → (Summable fun x => ‖dif L v G x‖) ∧ ∑' x, Φ x * dif L v G x = ∑' x, Φ x * G x := by
  intro L v Φ G _hL ⟨C, hC⟩ hK hG
  have hGs : Summable G := hG.of_norm
  have hsh : ∀ r : ℕ, Summable fun x => ‖G (x + (r : ℤ) • v)‖ := fun r =>
    (Equiv.addRight ((r : ℤ) • v)).summable_iff.mpr hG
  have hshs : ∀ r : ℕ, Summable fun x => G (x + (r : ℤ) • v) := fun r => (hsh r).of_norm
  have hsum : Summable fun x => ∑ r ∈ Finset.range L, G (x + (r : ℤ) • v) :=
    summable_sum fun r _ => hshs r
  have hdif : Summable (dif L v G) := by
    unfold dif
    exact hGs.sub (hsum.mul_left _)
  refine ⟨summable_norm_iff.mpr hdif, ?_⟩
  have hΦG : ∀ r : ℕ, Summable fun x => Φ x * G (x + (r : ℤ) • v) := fun r =>
    Summable.of_norm_bounded ((hsh r).mul_left C) (fun x => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  have hΦG0 : Summable fun x => Φ x * G x := by
    simpa using hΦG 0
  have key : ∀ r : ℕ, ∑' x, Φ x * G (x + (r : ℤ) • v) = ∑' x, Φ (x - (r : ℤ) • v) * G x := by
    intro r
    rw [← (Equiv.addRight ((r : ℤ) • v)).tsum_eq (fun y => Φ (y - (r : ℤ) • v) * G y)]
    simp
  have hΦG' : ∀ r : ℕ, Summable fun x => Φ (x - (r : ℤ) • v) * G x := fun r => by
    have := (Equiv.subRight ((r : ℤ) • v)).summable_iff.mpr (hΦG r)
    simpa [Function.comp_def] using this
  have e1 : (fun x => Φ x * dif L v G x) = fun x => Φ x * G x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, Φ x * G (x + (r : ℤ) • v) := by
    funext x; unfold dif; rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun r _ => by ring
  rw [e1, hΦG0.tsum_sub ((summable_sum fun r _ => hΦG r).mul_left _), tsum_mul_left,
    Summable.tsum_finsetSum (fun r _ => hΦG r)]
  simp_rw [key]
  rw [← Summable.tsum_finsetSum (fun r _ => hΦG' r)]
  have : (fun x => ∑ r ∈ Finset.range L, Φ (x - (r : ℤ) • v) * G x) = fun _ => 0 := by
    funext x; rw [← Finset.sum_mul, hK x, zero_mul]
  rw [this, tsum_zero, mul_zero, sub_zero]

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormUniformiserEqInvAbsNorm
section
open scoped NNReal
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_uniformiser_eq_inv_absNorm :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : v.adicCompletion F),
      Formalism.UG.IsUnifV F v ϖ → ‖ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ := by
  intro F _ _ v ϖ h
  apply NNReal.eq
  rw [coe_nnnorm, FinitePlace.norm_def]
  unfold Formalism.UG.IsUnifV at h
  rw [h]
  have hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    WithZero.coe_ne_zero
  rw [WithZeroMulInt.toNNReal_neg_apply _ hne]
  simp only [WithZero.log, WithZero.recZeroCoe_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv]

end GlobalTheory
end

