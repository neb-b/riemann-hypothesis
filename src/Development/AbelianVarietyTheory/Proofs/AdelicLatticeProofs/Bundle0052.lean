module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasFiniteAdelicDoubleCosetsOfBlockDiagPartImage
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAuxiliaryPlacesSquarePatternsSUnits
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasFiniteAdelicDoubleCosetsOfBlockDiagPartImageStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFiniteAdelicDoubleCosets_of_blockDiagPart_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → AdelicPair R R₀ → CF (blk e '' Γ) R R₀ → CF Γ R R₀ := by
  first | exact @GlobalTheory.ClassFin.cf_of_cf_blk_image | exact GlobalTheory.ClassFin.cf_of_cf_blk_image | (intros; apply GlobalTheory.ClassFin.cf_of_cf_blk_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem two_le_absNorm_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  omega

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem one_sub_mul_natCast_cpow_neg_ne_zero {c : ℂ} (hc : ‖c‖ ≤ 1) {n : ℕ} (hn : 2 ≤ n)
    {s : ℂ} (hs : 0 < s.re) : 1 - c * (n : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : c * (n : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖(n : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < n)) (by linarith)
  have h3 := congrArg norm h1
  rw [norm_mul, norm_one] at h3
  nlinarith [norm_nonneg c, norm_nonneg ((n : ℂ) ^ (-s))]


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.idealCharacterL_continuation_ne_zero_one :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ)
    (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) →
    (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) →
    (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) →
    ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} →
    (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) →
    (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) →
    (∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → ∀ c : HeightOneSpectrum (𝓞 K) → ℂ,
    (∀ P, ‖c P‖ ≤ 1) → (∀ P, ¬ m ≤ P.asIdeal → c P = X P.asIdeal) →
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s | 0 < s.re} ∧ (∀ s : ℂ, 1 < s.re →
      L s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))) ∧ L 1 ≠ 0 := by
  intro K _ _ m X φ hm hXbot hXmul hXnorm hXzero hφmul hφsmul hφsmooth hφnorm hXφ hJ c hc hcX
  have hXtop : X ⊤ = 1 := by
    have h1 := hXnorm ⊤ top_ne_bot (top_sup_eq m)
    have h2 : X ⊤ = X ⊤ * X ⊤ := by rw [← hXmul, Ideal.top_mul]
    have h3 : X ⊤ ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
    exact mul_left_cancel₀ h3 (by rw [mul_one]; exact h2.symm)
  have hXle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · rw [hI, hXbot, norm_zero]
      exact zero_le_one
    by_cases hIm : I ⊔ m = ⊤
    · rw [hXnorm I hI hIm]
    · rw [hXzero I hIm, norm_zero]
      exact zero_le_one
  obtain ⟨Z, hZd, hZ, hZ1⟩ := _root_.GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hXbot hXmul hXnorm
    hXzero hφmul hφsmul hφsmooth hφnorm hXφ
  have hZ0 := hZ1 hJ
  let LX : ℂ → ℂ := dslope Z 1
  have hLXd : Differentiable ℂ LX := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd.differentiableOn
  have hLX : ∀ s : ℂ, 1 < s.re → LX s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [← _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hXbot hXtop hXmul hXle s hs]
    simp only [LX, dslope_of_ne _ hs1, slope_def_field, hZ s hs, hZ0, sub_zero]
    field_simp
  obtain ⟨Zζ, hZζd, hZζ⟩ := _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun P : HeightOneSpectrum (𝓞 K) =>
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-σ) :=
    fun σ hσ => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2
  have hne : Nonempty (HeightOneSpectrum (𝓞 K)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩
  have hLX1 : LX 1 ≠ 0 := _root_.GlobalTheory.eulerProduct_ne_zero_one_of_entire (HeightOneSpectrum (𝓞 K))
    (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum
    (fun P => hXle _) hsum hne Zζ LX hZζd hLXd hZζ hLX
  have hfin : {P : HeightOneSpectrum (𝓞 K) | P.asIdeal ∣ m}.Finite := Ideal.finite_factors hm
  let S := hfin.toFinset
  have hmemS : ∀ P, P ∈ S ↔ m ≤ P.asIdeal := fun P => by simp [S, Ideal.dvd_iff_le]
  have hfac : ∀ (P : HeightOneSpectrum (𝓞 K)) (s : ℂ), 0 < s.re →
      1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 :=
    fun P s hs => one_sub_mul_natCast_cpow_neg_ne_zero (hc P) (two_le_absNorm_heightOneSpectrum P) hs
  let F : ℂ → ℂ := ∏ P ∈ S, fun s => (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  have hF : ∀ s, F s = ∏ P ∈ S, (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ :=
    fun s => by simp [F, Finset.prod_apply]
  refine ⟨fun s => LX s * F s, ?_, ?_, ?_⟩
  · apply hLXd.differentiableOn.mul
    apply DifferentiableOn.finsetProd
    intro P _
    refine DifferentiableOn.inv ?_ (fun s hs => hfac P s hs)
    refine DifferentiableOn.const_sub ?_ _
    refine DifferentiableOn.const_mul ?_ _
    intro s _
    refine DifferentiableAt.differentiableWithinAt ?_
    exact differentiableAt_id.neg.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (by have := two_le_absNorm_heightOneSpectrum P; omega)))
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    obtain ⟨hsa, -⟩ := (_root_.GlobalTheory.eulerProduct_eq_exp_and_pos (HeightOneSpectrum (𝓞 K))
      (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum
      (fun P => hXle _) hsum).1 s hs
    have hsplit : ∀ P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) =
        -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) +
        (if P ∈ S then -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))
          else 0) := by
      intro P
      by_cases hP : P ∈ S
      · rw [if_pos hP]
        have hXP : X P.asIdeal = 0 := hXzero _ (by
          rw [sup_eq_left.mpr ((hmemS P).mp hP)]
          exact P.isPrime.ne_top)
        rw [hXP, zero_mul, sub_zero, Complex.log_one, neg_zero, zero_add]
      · rw [if_neg hP, add_zero, hcX P (fun h => hP ((hmemS P).mpr h))]
    show LX s * F s = _
    rw [tsum_congr hsplit, hsa.tsum_add (summable_of_ne_finset_zero (s := S) fun P hP => if_neg hP),
      tsum_eq_sum (s := S) (fun P hP => if_neg hP), Complex.exp_add, ← hLX s hs, hF,
      Complex.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [if_pos hP, Complex.exp_neg, Complex.exp_log (hfac P s hs0)]
  · show LX 1 * F 1 ≠ 0
    rw [hF]
    exact mul_ne_zero hLX1 (Finset.prod_ne_zero_iff.mpr fun P _ => inv_ne_zero (hfac P 1 (by simp)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemGlobalNormOfMemLocalNorms
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup {G : Type} [CommGroup G] (U W : Subgroup G) :
    W.index = W.relIndex U * (U ⊔ W).index := by
  rw [← Subgroup.relIndex_mul_index (le_sup_right : W ≤ U ⊔ W), Subgroup.relIndex_sup_right]

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.sqs_le_locSq (F : Type) [Field F] [NumberField F]
    (U : Subgroup Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    _root_.GlobalTheory.QNorm.sqs U ≤ _root_.GlobalTheory.QNorm.locSq F S := by
  intro x hx
  unfold _root_.GlobalTheory.QNorm.sqs at hx
  obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp hx
  unfold _root_.GlobalTheory.QNorm.locSq _root_.GlobalTheory.QNorm.finSq
  rw [Subgroup.mem_inf]
  simp only [Subgroup.mem_iInf, _root_.GlobalTheory.QNorm.mem_sqSub, powMonoidHom_apply,
    Units.val_pow_eq_pow_val, map_pow]
  exact ⟨fun v _ => ⟨_, sq _⟩, fun σ => ⟨_, sq _⟩⟩

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma eq_one_of_mul_self_eq_one_withZero (a : WithZero (Multiplicative ℤ))
    (h : a * a = 1) : a = 1 := by
  induction a using WithZero.recZeroCoe with
  | zero => simp at h
  | coe m =>
    have h1 : m * m = 1 := by exact_mod_cast h
    have h2 : Multiplicative.toAdd m + Multiplicative.toAdd m = 0 := by
      rw [← toAdd_mul, h1, toAdd_one]
    have h3 : Multiplicative.toAdd m = 0 := by omega
    have h4 : m = 1 := by rw [← ofAdd_toAdd m, h3, ofAdd_zero]
    rw [h4, WithZero.coe_one]

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.mem_sqs_sUnits_of_isSquare (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Fˣ) (hy : y ∈ _root_.GlobalTheory.QNorm.sUnits F S)
    (h : IsSquare (y : F)) : y ∈ _root_.GlobalTheory.QNorm.sqs (_root_.GlobalTheory.QNorm.sUnits F S) := by
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact y.ne_zero hs
  unfold _root_.GlobalTheory.QNorm.sqs
  refine Subgroup.mem_map.mpr ⟨Units.mk0 s hs0, ?_, ?_⟩
  · rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hy ⊢
    intro v hv
    have h1 := hy v hv
    rw [hs, map_mul] at h1
    exact eq_one_of_mul_self_eq_one_withZero _ h1
  · ext
    simp [hs, sq]

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma sqs_le_self {G : Type} [CommGroup G] (U : Subgroup G) :
    _root_.GlobalTheory.QNorm.sqs U ≤ U := by
  intro y hy
  unfold _root_.GlobalTheory.QNorm.sqs at hy
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
  rw [powMonoidHom_apply]
  exact U.pow_mem hs 2


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), _root_.GlobalTheory.QNorm.admitted F S → δ ∈ _root_.GlobalTheory.QNorm.sUnits F S → ¬ IsSquare (δ : F) → ∀ x ∈ _root_.GlobalTheory.QNorm.sUnits F S, x ∈ _root_.GlobalTheory.QNorm.locNorm F δ S → x ∈ _root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) := by
  intro F _ _ δ S hS hδ hns x hx hxN
  classical
  obtain ⟨T, hST, hcard, hδT, hpat⟩ :=
    _root_.GlobalTheory.QNorm.exists_auxiliary_places F δ S hS hδ hns
  have htop := _root_.GlobalTheory.QNorm.sUnits_union_sup_finSq_eq_top F S T hS hST hpat
  have hS' := hS.mono (Finset.subset_union_left (s₂ := T))
  have hUU : _root_.GlobalTheory.QNorm.sUnits F S ≤ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T) := by
    intro z hz
    rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hz ⊢
    intro v hv
    exact hz v (fun h => hv (Finset.mem_union_left _ h))
  have hsq_eq : _root_.GlobalTheory.QNorm.locSq F S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T) =
      _root_.GlobalTheory.QNorm.sqs (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) := by
    apply le_antisymm
    · rintro y ⟨hyL, hyU⟩
      exact _root_.GlobalTheory.QNorm.mem_sqs_sUnits_of_isSquare F _ y hyU
        (_root_.GlobalTheory.QNorm.isSquare_of_mem_locSq F S T hS htop y hyU hyL)
    · exact le_inf (_root_.GlobalTheory.QNorm.sqs_le_locSq F _ S) (sqs_le_self _)
  obtain ⟨hL0, hL⟩ := _root_.GlobalTheory.QNorm.index_locSq_le F S
  have hrel := _root_.GlobalTheory.QNorm.relIndex_sqs_sUnits F (S ∪ T)
  have hL' := _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.locSq F S)
  rw [← Subgroup.inf_relIndex_right, hsq_eq, hrel, Finset.card_union_of_disjoint hST] at hL'
  have hJ0 : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locSq F S).index ≠ 0 := by
    rw [hL'] at hL0
    exact right_ne_zero_of_mul hL0
  have hJ : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locSq F S).index ≤ 2 := by
    have h4 : (4 : ℕ) ^ (S.card + Fintype.card (InfinitePlace F)) =
        2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ]
      congr 1
      omega
    rw [hL', h4] at hL
    exact le_of_mul_le_mul_left hL (by positivity)
  have hLN : _root_.GlobalTheory.QNorm.locSq F S ≤ _root_.GlobalTheory.QNorm.locNorm F δ S := by
    intro y hy
    unfold _root_.GlobalTheory.QNorm.locSq _root_.GlobalTheory.QNorm.finSq at hy
    unfold _root_.GlobalTheory.QNorm.locNorm
    rw [Subgroup.mem_inf] at hy ⊢
    simp only [Subgroup.mem_iInf] at hy ⊢
    exact ⟨fun v hv => _root_.GlobalTheory.QNorm.sqSub_le_normSub _ _ (hy.1 v hv),
      fun σ => _root_.GlobalTheory.QNorm.sqSub_le_normSub _ _ (hy.2 σ)⟩
  haveI : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locSq F S).FiniteIndex :=
    ⟨hJ0⟩
  have hK : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locNorm F δ S).index ≤ 2 :=
    le_trans (Subgroup.index_antitone (sup_le_sup_left hLN _)) hJ
  obtain ⟨hR0, hR⟩ := _root_.GlobalTheory.QNorm.first_inequality_sUnits F δ (S ∪ T) hS' (hUU hδ) hns
  obtain ⟨-, hN⟩ := _root_.GlobalTheory.QNorm.two_pow_le_index_locNorm F (δ : F) S δ.ne_zero
  have hcnt : _root_.GlobalTheory.QNorm.tFin F δ (S ∪ T) = _root_.GlobalTheory.QNorm.tFin F δ S := by
    unfold _root_.GlobalTheory.QNorm.tFin
    congr 1
    ext v
    simp only [Set.mem_setOf_eq, Finset.mem_union]
    constructor
    · rintro ⟨hv | hv, h⟩
      · exact ⟨hv, h⟩
      · exact absurd (hδT v hv) h
    · rintro ⟨hv, h⟩
      exact ⟨Or.inl hv, h⟩
  have hNidx := _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.locNorm F δ S)
  have hGN := _root_.GlobalTheory.QNorm.normSub_id_le_locNorm F (δ : F) S
  have hRle : (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F)).relIndex
      (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) ≤
      (_root_.GlobalTheory.QNorm.locNorm F δ S).relIndex (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) := by
    have h2 : 2 * (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F)).relIndex
        (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) ≤
        (_root_.GlobalTheory.QNorm.locNorm F δ S).relIndex (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) * 2 := by
      calc _ ≤ _ := hR
        _ = 2 ^ (_root_.GlobalTheory.QNorm.tFin F δ S + _root_.GlobalTheory.QNorm.tReal F δ) := by rw [hcnt]
        _ ≤ _ := hN
        _ = _ := hNidx
        _ ≤ _ := Nat.mul_le_mul_left _ hK
    omega
  have hchain := Subgroup.relIndex_mul_relIndex
    (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.locNorm F δ S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) (inf_le_inf_right _ hGN) inf_le_right
  rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at hchain
  have hne : (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)).relIndex
      (_root_.GlobalTheory.QNorm.locNorm F δ S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hchain
    exact hR0 hchain.symm
  have hNpos := lt_of_lt_of_le (Nat.pos_of_ne_zero hR0) hRle
  have hone : (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)).relIndex
      (_root_.GlobalTheory.QNorm.locNorm F δ S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) = 1 := by
    have hle1 := hchain.le.trans hRle
    have h3 := le_of_mul_le_mul_right (hle1.trans (one_mul _).symm.le) hNpos
    omega
  exact (Subgroup.relIndex_eq_one.mp hone ⟨hxN, hUU hx⟩).1

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemKummerNormsOfLocalNorms
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem index_eq_relIndex_mul_index_sup_normThm {G : Type} [CommGroup G] (U W : Subgroup G) :
    W.index = W.relIndex U * (U ⊔ W).index := by
  rw [← Subgroup.relIndex_mul_index (le_sup_right : W ≤ U ⊔ W), Subgroup.relIndex_sup_right]

theorem inf_le_of_index_count_normThm {G : Type} [CommGroup G] (p : ℕ) (hp : 0 < p)
    (U W D N : Subgroup G) (s k t : ℕ)
    (hWD : W ≤ D) (hND : N ≤ D) (hk : k + 1 = 2 * s) (hW0 : W.index ≠ 0)
    (hW : W.index ≤ p ^ (2 * s)) (hWU : W.relIndex U = p ^ k) (hD : p ^ t ≤ D.index)
    (hN0 : N.relIndex U ≠ 0) (hN : p * N.relIndex U ≤ p ^ t) : D ⊓ U ≤ N := by
  have e1 := index_eq_relIndex_mul_index_sup_normThm U W
  have e2 := index_eq_relIndex_mul_index_sup_normThm U D
  have h4 : p ^ (2 * s) = p ^ k * p := by
    rw [← pow_succ, hk]
  have hUW0 : (U ⊔ W).index ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hW0 e1
  have hUW : (U ⊔ W).index ≤ p := by
    rw [e1, hWU, h4] at hW
    exact Nat.le_of_mul_le_mul_left hW (by positivity)
  have hUD : (U ⊔ D).index ≤ p :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hUW0)
      (Subgroup.index_dvd_of_le (sup_le_sup_left hWD U))) hUW
  have h3 : N.relIndex U ≤ D.relIndex U := by
    have : p * N.relIndex U ≤ p * D.relIndex U := by
      calc p * N.relIndex U ≤ D.relIndex U * (U ⊔ D).index := by
            rw [← e2]; exact hN.trans hD
        _ ≤ D.relIndex U * p := Nat.mul_le_mul_left _ hUD
        _ = p * D.relIndex U := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left this hp
  have e3 : N.relIndex (D ⊓ U) * D.relIndex U = N.relIndex U := by
    have := Subgroup.relIndex_inf_mul_relIndex N D U
    rwa [inf_eq_left.mpr hND] at this
  have hD0 : D.relIndex U ≠ 0 := by
    intro h; rw [h, mul_zero] at e3; exact hN0 e3.symm
  have hm0 : N.relIndex (D ⊓ U) ≠ 0 := by
    intro h; rw [h, zero_mul] at e3; exact hN0 e3.symm
  have hm : N.relIndex (D ⊓ U) ≤ 1 := by
    rw [← e3] at h3
    have : N.relIndex (D ⊓ U) * D.relIndex U ≤ 1 * D.relIndex U := by rwa [one_mul]
    exact Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hD0)
  exact Subgroup.relIndex_eq_one.mp (by omega)

theorem pows_le_finPow_normThm (p : ℕ) (F : Type) [Field F] [NumberField F] (U : Subgroup Fˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : pows p U ≤ finPow p F S := by
  rintro _ ⟨y, -, rfl⟩
  have h : ∀ {L : Type} [Field L] (φ : F →+* L), powMonoidHom p y ∈ powSub p φ := by
    intro L _ φ
    exact ⟨φ y, by simp⟩
  exact Subgroup.mem_iInf.mpr fun _ => Subgroup.mem_iInf.mpr fun _ => h _

theorem mem_pows_sUnits_normThm (p : ℕ) (hp : 0 < p) (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Fˣ) (hy : y ∈ sUnits F S)
    (h : ∃ r : F, r ^ p = (y : F)) : y ∈ pows p (sUnits F S) := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hr, zero_pow hp.ne'])
  refine ⟨Units.mk0 r hr0, ?_, ?_⟩
  · intro v hv
    have h1 := hy v hv
    have h2 : v.valuation F r ^ p = 1 := by
      rw [← map_pow, hr]; exact h1
    exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne').mp h2
  · ext
    simp [hr]

theorem sUnit_mem_kNorm_of_mem_finNorm : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∀ x ∈ sUnits F S, x ∈ finNorm p F δ S → x ∈ kNorm p (RingHom.id F) (δ : F) := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns x hx hxl
  classical
  have hp0 := hp.pos
  obtain ⟨T, hST, hcard, hsq, hA⟩ := _root_.GlobalTheory.CNorm.exists_auxiliary_places_prime p F ζ δ S hp hζ hS hδ hns
  have hsurj := _root_.GlobalTheory.CNorm.sUnits_union_sup_finPow_eq_top p F S T hp hS hST hA
  have hinj := _root_.GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow p F ζ S T hp hζ hS hsurj
  have hmono : sUnits F S ≤ sUnits F (S ∪ T) := fun y hy v hv =>
    hy v (fun h => hv (by simp only [Finset.coe_union, Set.mem_union]; exact Or.inl h))
  have hS' : AdmP p F (S ∪ T) :=
    (exists_admissiblePlaces_superset_and_mono p F hp0).2 S (S ∪ T) Finset.subset_union_left hS
  obtain ⟨hN0, hN⟩ := _root_.GlobalTheory.CNorm.first_inequality_sUnits_prime p F ζ δ (S ∪ T) hp hζ hS' (hmono hδ) hns
  have ht : tNon p F δ (S ∪ T) = tNon p F δ S := by
    unfold tNon
    congr 1
    ext v
    simp only [Finset.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact ⟨h, h'⟩
      · obtain ⟨r, hr⟩ := hsq v h
        exact absurd hr (h' r)
    · rintro ⟨h, h'⟩
      exact ⟨Or.inl h, h'⟩
  rw [ht] at hN
  obtain ⟨-, hD⟩ := _root_.GlobalTheory.CNorm.pow_tNon_le_index_finNorm p F ζ δ S hp hζ
  obtain ⟨hW0, hW⟩ := _root_.GlobalTheory.CNorm.index_finPow_le p F S hp0
  have hU := (pTor_pIdx_sUnits p F ζ (S ∪ T) hp hζ).2
  unfold pIdx at hU
  have hinf : finPow p F S ⊓ sUnits F (S ∪ T) = pows p (sUnits F (S ∪ T)) ⊓ sUnits F (S ∪ T) := by
    apply le_antisymm
    · rintro y ⟨h1, h2⟩
      exact ⟨mem_pows_sUnits_normThm p hp0 F _ y h2 (hinj y h2 h1), h2⟩
    · exact inf_le_inf_right _ (pows_le_finPow_normThm p F _ S)
  have hWU : (finPow p F S).relIndex (sUnits F (S ∪ T)) =
      p ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) := by
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right, hU]
  obtain ⟨k1, k2⟩ := _root_.GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map p hp0
  have hWD : finPow p F S ≤ finNorm p F δ S := iInf₂_mono fun _ _ => k1 _ _ _ _
  have hND : kNorm p (RingHom.id F) (δ : F) ≤ finNorm p F δ S :=
    le_iInf₂ fun _ _ => k2 _ _ _ _
  refine inf_le_of_index_count_normThm p hp0 (sUnits F (S ∪ T)) (finPow p F S) (finNorm p F δ S)
    _ _ _ _ hWD hND ?_ hW0 hW hWU hD hN0 hN ⟨hxl, hmono hx⟩
  rw [Finset.card_union_of_disjoint hST]
  omega

end GlobalTheory.CNorm
end

