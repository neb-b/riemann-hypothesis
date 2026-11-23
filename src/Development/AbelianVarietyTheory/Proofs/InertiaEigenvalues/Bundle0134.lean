module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Formalism.CoboundaryTransfers.Statement
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LocalRingStructure
public import ReciprocityTheory.GaloisValuations.Global
public import ReciprocityTheory.GaloisValuations.ArithOfA
public import ReciprocityTheory.NeutralLocalFields.Bundle0001
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZero
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset Matrix

theorem coefB_norm {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] {h : ℕ}
    (ϖ : F) (lam π : Fin h → F) (L U : ℕ)
    (hb : ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖)) :
    (∀ m r j, ‖coefB p ϖ lam π L U m r j‖ ≤ 1) ∧ (∀ m, L < m → ∀ r j, ‖coefB p ϖ lam π L U m r j‖ < 1) := by
  have key : ∀ m r j, ‖coefB p ϖ lam π L U m r j‖ ≤ 1 ∧ (L < m → ‖coefB p ϖ lam π L U m r j‖ < 1) := by
    intro m r j
    simp only [coefB, Matrix.of_apply]
    split_ifs with hm
    · rw [norm_pow, norm_div]
      obtain ⟨h1, h2⟩ := hb r j ((m : ℤ) - L)
      have hpos : p ^ (h - (r : ℕ)) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
      rcases eq_or_lt_of_le (norm_nonneg (lam r * π r ^ p ^ (r : ℕ))) with hc | hc
      · rw [← hc, div_zero, zero_pow hpos]
        exact ⟨zero_le_one, fun _ => zero_lt_one⟩
      · refine ⟨pow_le_one₀ (div_nonneg (norm_nonneg _) hc.le) ((div_le_one hc).2 h1), fun hLm => ?_⟩
        exact pow_lt_one₀ (div_nonneg (norm_nonneg _) hc.le) ((div_lt_one hc).2 (h2 (by omega))) hpos
    · simp
  exact ⟨fun m r j => (key m r j).1, fun m hm r j => (key m r j).2 hm⟩

theorem gsum_mul_left {F : Type} [NormedField F] {m : Type} [Fintype m] (q D : ℕ) (A : Matrix m m F)
    (B : ℕ → Matrix m m F) (z : m → F) :
    gsum q D (fun n => A * B n) z = A *ᵥ gsum q D B z := by
  simp only [gsum, Matrix.mulVec_sum, Matrix.mulVec_mulVec]

theorem normalize {F : Type} [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hlam : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hanti : Antitone (fun j => ‖lam j‖)) (horth : Orth p lam) (L U : ℕ) (hL : 1 ≤ L)
    (hb : ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖)) :
    ∃ M : ℕ → Matrix (Fin h) (Fin h) F, Normal L M ∧ (M 0).det ≠ 0 ∧
      ∃ Φ : (Fin h → F) → (Fin h → F), (∀ b, (∀ r, ‖b r‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖) → Integral (Φ b)) ∧
        Φ 0 = 0 ∧ ∀ z b, gsum (p ^ h) (L + U) M z = Φ b ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = b r := by
  set B := coefB p ϖ lam π L U with hBdef
  obtain ⟨hB1, hB2⟩ := coefB_norm p ϖ lam π L U hb
  obtain ⟨hdet, hdet0⟩ := GlobalTheory.T.normalizedRowCoefficientMatrices_det_norm F p h ϖ hϖ lam π hlam hπ hanti horth L U
  obtain ⟨hN, hinv⟩ := _root_.GlobalTheory.PMonE.normal_of_inv_mul F (Fin h) L B hB1 hB2 hdet
  have hdne : (B L).det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    exact zero_ne_one hdet
  have hdu : IsUnit (B L).det := isUnit_iff_ne_zero.2 hdne
  have hc : ∀ r, lam r * π r ^ p ^ (r : ℕ) ≠ 0 := fun r => mul_ne_zero (hlam r) (pow_ne_zero _ (hπ r))
  let nb : (Fin h → F) → (Fin h → F) := fun b r => (b r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ))
  refine ⟨fun n => (B L)⁻¹ * B n, hN, ?_, fun b => (B L)⁻¹ *ᵥ nb b, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det (B L) hdu).ne_zero hdet0
  · intro b hbb i
    simp only [Matrix.mulVec, dotProduct]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro j _
    rw [norm_mul]
    have h1 : ‖nb b j‖ ≤ 1 := by
      simp only [nb]
      rw [norm_pow, norm_div]
      exact pow_le_one₀ (div_nonneg (norm_nonneg _) (norm_nonneg _))
        ((div_le_one (norm_pos_iff.2 (hc j))).2 (hbb j))
    exact mul_le_one₀ (hinv i j) (norm_nonneg _) h1
  · have : nb 0 = 0 := by
      funext r
      simp only [nb, Pi.zero_apply, zero_div]
      exact zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    simp only [this, Matrix.mulVec_zero]
  · intro z b
    rw [gsum_mul_left]
    constructor
    · intro H r
      have H2 : gsum (p ^ h) (L + U) B z = nb b := by
        have := congrArg (fun v => B L *ᵥ v) H
        simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdu, Matrix.one_mulVec] using this
      have H3 := congrFun H2 r
      rw [← _root_.GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB F p h ϖ lam π L U hL z r] at H3
      have H4 := (iterateFrobenius_inj F p (h - (r : ℕ))).eq_iff.1 (by simpa [iterateFrobenius_def] using H3)
      exact (div_left_inj' (hc r)).1 H4
    · intro H
      have H2 : gsum (p ^ h) (L + U) B z = nb b := by
        funext r
        rw [← _root_.GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB F p h ϖ lam π L U hL z r, H r]
      rw [H2]

theorem winThm : WinThm := by
  intro F _ _ _ _ p _ _ _ h ϖ hh hϖ lam hlam hanti horth hlt
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  obtain ⟨π, hπ, hrel1, hrel2⟩ := exists_window_radii F p k ϖ hϖ lam hlam hanti hlt
  have hp := (Fact.out : p.Prime)
  have hϖ0 : ϖ ≠ 0 := by
    have : (0 : ℝ) < ‖ϖ‖ := by
      rw [hϖ]
      exact inv_pos.2 (by exact_mod_cast hp.pos)
    exact norm_pos_iff.1 this
  have hbd := _root_.GlobalTheory.PMonE.WinBounds.term_le_bound F p k ϖ hϖ lam π hlam hanti hlt hπ hrel1 hrel2
  have hb : ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) :=
    fun r j n => ⟨(hbd r j n).1, (hbd r j n).2.1⟩
  have hπ0 : ∀ j, π j ≠ 0 := fun j => (hπ j).1
  have hGL := _root_.GlobalTheory.PMonE.generalLemma_allOrders
  refine ⟨fun j => ‖π j‖, fun r => ‖lam r * π r ^ p ^ (r : ℕ)‖, 2,
    fun j => ⟨norm_pos_iff.2 (hπ j).1, (hπ j).2⟩,
    fun r => norm_pos_iff.2 (mul_ne_zero (hlam r) (pow_ne_zero _ (hπ r).1)), ?_, ?_, ?_⟩
  · intro x hx r j n
    have hm := _root_.GlobalTheory.PMonE.term_norm_mono F p (k + 1) ϖ lam π x hx r j n
    exact ⟨hm.trans (hbd r j n).1, fun hn => hm.trans ((hbd r j n).2.2 (by exact_mod_cast hn))⟩
  · intro b hbnd
    obtain ⟨M, hM, _, Φ, hΦ, _, hiff⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth 2 2 (by norm_num) hb
    obtain ⟨z, hz, hzb⟩ := (hGL 2).1 F p (Fin (k + 1)) (k + 1) (2 + 2) (by omega) (by omega) M hM (Φ b)
      (hΦ b hbnd)
    refine ⟨winPt p π 2 z, ?_, fun r => ?_⟩
    · intro j
      simp only [winPt]
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz j))
    · rw [rowT_eq_rowS]
      exact (hiff z b).1 hzb r
  · obtain ⟨M, hM, hM0, Φ, _, hΦ0, hiff⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth 2 2 (by norm_num) hb
    obtain ⟨M', hM', hM0', Φ', _, hΦ0', hiff'⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth (2 - 1) (2 + 1) (by norm_num) hb
    have c1 := (hGL 2).2 F p (Fin (k + 1)) (k + 1) (2 + 2) (by omega) (by omega) M hM hM0
    have c2 := (hGL (2 - 1)).2 F p (Fin (k + 1)) (k + 1) ((2 - 1) + (2 + 1)) (by omega) (by omega) M' hM' hM0'
    have d1 := GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem F p (k + 1) ϖ lam π hπ0 2 2 M (fun z => by simpa [hΦ0] using hiff z 0)
    have d2 := GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem F p (k + 1) ϖ lam π hπ0 (2 - 1) (2 + 1) M' (fun z => by simpa [hΦ0'] using hiff' z 0)
    have e1 := _root_.GlobalTheory.PMonE.win_inner F p (k + 1) 2 ϖ hϖ0 (by norm_num) lam π
    have hq1 : 1 < p ^ (k + 1) := Nat.one_lt_pow (by omega) hp.one_lt
    have cS : Nat.card {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0} =
        (p ^ (k + 1)) ^ ((k + 1) * 2) := by
      rw [d1, c1, Fintype.card_fin]
    have cI : Nat.card {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
        ∀ r, rowT p ϖ lam 2 x r = 0} = (p ^ (k + 1)) ^ ((k + 1) * (2 - 1)) := by
      rw [e1, d2, c2, Fintype.card_fin]
    by_contra hcon
    have hsub : ∀ x : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0},
        ∀ j, ‖x.1 j‖ ≤ ‖π j‖ ^ p ^ (k + 1) := by
      intro x
      by_contra hx
      push_neg at hx
      exact hcon ⟨x.1, x.2.1, hx, x.2.2⟩
    haveI : Finite {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
        ∀ r, rowT p ϖ lam 2 x r = 0} := Nat.finite_of_card_ne_zero (by rw [cI]; positivity)
    have hle := Nat.card_le_card_of_injective
      (fun x : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0} =>
        (⟨x.1, hsub x, x.2.2⟩ : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
          ∀ r, rowT p ϖ lam 2 x r = 0}))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    rw [cS, cI] at hle
    exact absurd hle (not_le.2 (Nat.pow_lt_pow_right hq1 (by omega)))

end GlobalTheory.PMonE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElements
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.Sandwich

theorem exists_dvd_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : O)
    (ha : a ∈ IsLocalRing.maximalIdeal O) (d : O) (hd : d ≠ 0) : ∃ k : ℕ, d ∣ a ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
  refine ⟨k, ?_⟩
  have h1 : ϖ ∣ a := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ
    rw [hϖ] at ha
    exact Ideal.mem_span_singleton.1 ha
  exact hk.dvd.trans (pow_dvd_pow_of_dvd h1 k)

theorem eventually_pow_mul_mem {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) (S : Submodule O A)
    (x : A) (d : O) (hd : d ≠ 0) (hx : d • x ∈ S) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → algebraMap O A a ^ n * x ∈ S := by
  obtain ⟨k, c, hc⟩ := exists_dvd_pow a ha d hd
  refine ⟨k, fun n hn => ?_⟩
  have e : algebraMap O A a ^ n * x = (a ^ (n - k) * c) • (d • x) := by
    rw [smul_smul, Algebra.smul_def, ← map_pow]
    congr 2
    rw [mul_assoc, mul_comm c d, ← hc, ← pow_add, Nat.sub_add_cancel hn]
  rw [e]
  exact S.smul_mem _ hx

end GlobalTheory.UnitLemma.Sandwich

namespace GlobalTheory.UnitLemma.Sandwich

variable {K : UQ} (B : InvAlg K)

theorem exists_smul_isIntegral (x : B.A) : ∃ d : K.O, d ≠ 0 ∧ IsIntegral K.O (d • x) := by
  have h : IsAlgebraic K.E x := Algebra.IsAlgebraic.isAlgebraic x
  have h' : IsAlgebraic K.O x := (IsFractionRing.isAlgebraic_iff K.O K.E B.A).2 h
  obtain ⟨d, hd, hi⟩ := h'.exists_integral_multiple
  exact ⟨d, hd, hi⟩

theorem exists_smul_mem (L : Submodule K.O B.A) (hL : Submodule.span K.E (L : Set B.A) = ⊤) (x : B.A) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.DenominatorOfSpan.exists_denominator
  | exact _root_.GlobalTheory.DenominatorOfSpan.exists_denominator
  | (apply _root_.GlobalTheory.DenominatorOfSpan.exists_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorOfSpan.exists_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorOfSpan.exists_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorOfSpan.exists_denominator ..)

end GlobalTheory.UnitLemma.Sandwich

namespace GlobalTheory.UnitLemma.Sandwich

variable {K : UQ} (B : InvAlg K)

theorem exists_aeval (hP : B.P.Separable) (x : B.A) : ∃ f : K.E[X], x = aeval B.g f := by
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hP
  refine ⟨∑ i, C (e.repr x i) * X ^ (i : ℕ), ?_⟩
  conv_lhs => rw [← e.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, he, Algebra.smul_def]

theorem traceForm_nondegenerate (hP : B.P.Separable) : (Algebra.traceForm K.E B.A).Nondegenerate := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · exact TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP (exists_aeval B hP) w
      (fun y => by simpa [Algebra.traceForm_apply] using hw y)
  · exact TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP (exists_aeval B hP) w
      (fun y => by simpa [Algebra.traceForm_apply, mul_comm] using hw y)

theorem integral_sub (hP : B.P.Separable) (a : K.O) (ha : a ∈ IsLocalRing.maximalIdeal K.O)
    (L : Submodule K.O B.A) (hL : Submodule.span K.E (L : Set B.A) = ⊤) :
    ∃ m : ℕ, ∀ n, m ≤ n → ∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L := by
  classical
  have hnd := traceForm_nondegenerate B hP
  let b0 := Module.finBasis K.E B.A
  choose d hd0 hdi using fun i => exists_smul_isIntegral B (b0 i)
  have hu : ∀ i, IsUnit (algebraMap K.O K.E (d i)) := fun i =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 (hd0 i))
  let b := b0.isUnitSMul hu
  have hb : ∀ i, IsIntegral K.O (b i) := by
    intro i
    rw [Module.Basis.isUnitSMul_apply, algebraMap_smul]
    exact hdi i
  let bd := (Algebra.traceForm K.E B.A).dualBasis hnd b
  choose c hc0 hc using fun i => exists_smul_mem B L hL (bd i)
  choose k hk using fun i => eventually_pow_mul_mem a ha L (bd i) (c i) (hc0 i) (hc i)
  refine ⟨Finset.univ.sup k, fun n hn y hy => ?_⟩
  have hrep := bd.sum_repr y
  have hint : ∀ i, ∃ o : K.O, algebraMap K.O K.E o = bd.repr y i := by
    intro i
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    exact IsIntegrallyClosed.isIntegral_iff.1
      (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral K.O K.E B.A _ (hy.mul (hb i)))
  choose o ho using hint
  rw [← hrep, Finset.mul_sum]
  refine L.sum_mem fun i _ => ?_
  rw [← ho i, algebraMap_smul, mul_smul_comm]
  exact L.smul_mem _ (hk i n ((Finset.le_sup (Finset.mem_univ i)).trans hn))

theorem sub_integral (a : K.O) (ha : a ∈ IsLocalRing.maximalIdeal K.O) (L : Submodule K.O B.A) (hL : L.FG) :
    ∃ m : ℕ, ∀ n, m ≤ n → ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  classical
  obtain ⟨s, hs⟩ := hL
  have hk : ∀ x : B.A, ∃ k : ℕ, ∀ n, k ≤ n →
      algebraMap K.O B.A a ^ n * x ∈ Subalgebra.toSubmodule (integralClosure K.O B.A) := by
    intro x
    obtain ⟨d, hd, hi⟩ := exists_smul_isIntegral B x
    exact eventually_pow_mul_mem a ha _ x d hd hi
  choose k hk using hk
  refine ⟨s.sup k, fun n hn y hy => ?_⟩
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact hk x n ((Finset.le_sup hx).trans hn)
  | zero => simpa using isIntegral_zero
  | add x z _ _ hx hz => rw [mul_add]; exact hx.add hz
  | smul r x _ hx => rw [mul_smul_comm, Algebra.smul_def]; exact isIntegral_algebraMap.mul hx

end GlobalTheory.UnitLemma.Sandwich

namespace GlobalTheory.UnitLemma

theorem lattice_sandwich : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a →
    ∀ L : Submodule K.O B.A, IsLat K.O K.E L → ∃ m : ℕ, ∀ n : ℕ, m ≤ n →
      (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L) ∧
        ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  intro K B hB a ha L hL
  obtain ⟨m₁, h₁⟩ := Sandwich.integral_sub B hB.2 a ha.2.1 L hL.2
  obtain ⟨m₂, h₂⟩ := Sandwich.sub_integral B a ha.2.1 L hL.1
  exact ⟨max m₁ m₂, fun n hn => ⟨h₁ n (le_of_max_le_left hn), h₂ n (le_of_max_le_right hn)⟩⟩

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeightsFromJumpsIff
section
noncomputable section

namespace GlobalTheory.HeightsFromJumpsCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

end Generic


open TensorProduct in
theorem _root_.GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (AI : _root_.Formalism.BasicNotions.LocAinf l P)
    (H : _root_.Formalism.BasicNotions.LocHW l P) (F : _root_.Formalism.BasicNotions.LocFon l P AI H) (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H F C ↔
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure.HeightsFromJumps l P AI H F C :=
  Iff.rfl

end GlobalTheory.HeightsFromJumpsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HilbertSubgroupLeKerOfKillsInertia
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField
open Pointwise

namespace GlobalTheory.HilbertKill

theorem hilbertSubgroup_le_ker : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (M : Type) [AddCommGroup M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    IsLocallyConstant z → (∀ v, ∀ σ ∈ Ine (F := E) (Av v), z σ = 0) →
    (∀ c : Ω ≃ₐ[E] Ω, IsComplexConjugation c → z c = 0) →
    ∀ σ ∈ hilbertSubgroup E Ω, z σ = 0 := by
  intro E Ω _ _ _ _ _ Av hAv M _ z hz hlc hIne hC
  let f : G E Ω →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by
        have h := hz 1 1
        rw [mul_one, left_eq_add] at h
        simp [h]
      map_mul' := fun g h => by simp [hz] }
  have hf : ∀ g, g ∈ f.ker ↔ z g = 0 := fun g => by
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z g) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  have hclosed : IsClosed (f.ker : Set (G E Ω)) := by
    convert hlc.isClosed_fiber 0 using 1
    ext g
    exact hf g
  have hinv : ∀ g, z g⁻¹ = - z g := fun g => by
    have h := hz g g⁻¹
    have h1 : z 1 = 0 := (hf 1).1 f.ker.one_mem
    rw [mul_inv_cancel, h1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  intro σ hσ
  refine (hf σ).1 (Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_) hclosed hσ)
  rintro g ((hg | ⟨A, hg⟩) | hg)
  · exact Abelianization.commutator_subset_ker f hg
  · have hg' := (ReciprocityTheory.Neutral.Bridge.HCF.mem_inertia_map_iff E A g).1 hg
    rcases GlobalTheory.inertiaEl_eq_one_or_liesAbove E Ω A g hg' with rfl | ⟨v, hv⟩
    · exact f.ker.one_mem
    have hA : IsPlaceOver A v := fun x => by rw [← hv x, A.mem_nonunits_iff]
    have hgI : g ∈ Ine (F := E) A :=
      ⟨hg'.1, fun x hx => A.mem_nonunits_iff.1 (hg'.2 x ((A.valuation_le_one_iff x).1 hx))⟩
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (hAv v) hA
    have h2 : τ⁻¹ * g * τ⁻¹⁻¹ ∈ Ine (F := E) (τ⁻¹ • A) := conj_mem_Ine_smul hgI
    rw [inv_inv, ← hτ, inv_smul_smul] at h2
    have h3 := hIne v _ h2
    show z g = 0
    have e : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
    rw [e, hz, hz, h3, hinv, add_zero, add_neg_cancel]
  · exact (hf g).2 (hC g hg)

end GlobalTheory.HilbertKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne
section
noncomputable section
open GlobalTheory.BI

namespace GlobalTheory.BrauerZero

def D0 (G : Type) [Group G] : AddSubgroup (G → ℂ) :=
  AddSubgroup.closure {f | ∃ (H : Subgroup G) (χ : H →* ℂˣ),
    f = ind H (fun h => (χ h : ℂ)) - ind H (fun _ => 1)}

theorem ind_sub {G : Type} [Group G] [Finite G] (T : Subgroup G) (a b : T → ℂ) :
    ind T (a - b) = ind T a - ind T b :=
  (indAddHomComplex T).map_sub a b

theorem ind_const {G : Type} [Group G] [Finite G] (T : Subgroup G) (c : ℂ) (g : G) :
    ind T (fun _ => c) g = c * ind T (fun _ => 1) g := by
  classical
  haveI := Fintype.ofFinite G
  simp only [ind, finsum_eq_sum_of_fintype, ext0]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem ind_apply_one {G : Type} [Group G] [Finite G] (T : Subgroup G) (ψ : T → ℂ) :
    ind T ψ 1 = (T.index : ℂ) * ψ 1 := by
  classical
  haveI := Fintype.ofFinite G
  have h1 : ∀ x : G, ext0 T ψ (x⁻¹ * 1 * x) = ψ 1 := fun x => by
    have e : x⁻¹ * 1 * x = 1 := by group
    simp only [ext0, e, dif_pos T.one_mem]
    rfl
  simp only [ind, finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← T.card_mul_index]
  have : (Nat.card T : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := T)).ne'
  push_cast
  field_simp

theorem ind_top {G : Type} [Group G] [Finite G] (F : G → ℂ) (hF : ∀ g x : G, F (x⁻¹ * g * x) = F g) :
    ind (⊤ : Subgroup G) (fun h => F h) = F := by
  classical
  haveI := Fintype.ofFinite G
  funext g
  simp only [ind, finsum_eq_sum_of_fintype, ext0, Subgroup.mem_top, dite_true, hF]
  have hc : Nat.card {x : G // True} = Nat.card G := Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hc]
  have : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  field_simp

theorem indFun_eq_ind {G : Type} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ) :
    GlobalTheory.Published.indFun H f = ind H f := by
  classical
  funext g
  simp only [GlobalTheory.Published.indFun, ind, finsum_eq_sum_of_fintype, ext0]

end GlobalTheory.BrauerZero
end
end

