module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0197

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtNormMulWeylPairingIntegralSelfDual
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.PairInt

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem val_mul_nonneg (w : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : 0 ≤ vw w a) (hb : 0 ≤ vw w b) :
    0 ≤ vw w (a * b) := by
  by_cases h0 : a = 0
  · rw [h0, zero_mul, ValuationRepresentative.vw_zero]
  by_cases h1 : b = 0
  · rw [h1, mul_zero, ValuationRepresentative.vw_zero]
  rw [ValuationRepresentative.vw_mul w a b h0 h1]
  exact add_nonneg ha hb

theorem val_pow_eq_zero (w : HeightOneSpectrum (𝓞 K)) {a : K} (ha : vw w a = 0) (k : ℕ) : vw w (a ^ k) = 0 := by
  by_cases h0 : a = 0
  · subst h0
    rcases k with _ | k
    · rw [pow_zero, ValuationRepresentative.vw_one]
    · rw [pow_succ, mul_zero, ValuationRepresentative.vw_zero]
  induction k with
  | zero => rw [pow_zero, ValuationRepresentative.vw_one]
  | succ k ih => rw [pow_succ, ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ h0) h0, ih, ha, add_zero]

theorem val_zpow_eq_zero (w : HeightOneSpectrum (𝓞 K)) {a : K} (ha : vw w a = 0) (e : ℤ) : vw w (a ^ e) = 0 := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · rw [zpow_natCast, val_pow_eq_zero w ha]
  · rw [zpow_neg, zpow_natCast, ValuationRepresentative.vw_inv, val_pow_eq_zero w ha, neg_zero]

theorem val_prod_nonneg (w : HeightOneSpectrum (𝓞 K)) {ι : Type} (s : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ s, 0 ≤ vw w (f i)) : 0 ≤ vw w (∏ i ∈ s, f i) :=
  Finset.prod_induction f (fun a => 0 ≤ vw w a) (fun _ _ ha hb => val_mul_nonneg w ha hb)
    (ValuationRepresentative.vw_one w).ge hf

private theorem selfDualK_full {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : IsSelfDualK G M) : Submodule.IsFullLattice K M := by
  classical
  haveI : Submodule.IsLattice K M := hM.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hM.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin n → K) → K := fun x => star x ⬝ᵥ G *ᵥ y
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) s f
  have ha0 : (algebraMap (𝓞 K) K a) ≠ 0 :=
    (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 K) (Fin n → K) := {
    carrier := {x | ∃ b : 𝓞 K, (b : K) = (algebraMap (𝓞 K) K a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : K) + c = _
      rw [hb, hc]
      simp [f, dotProduct, Matrix.mulVec, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd K) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def,
        RingOfIntegers.mapRingHom_apply, Pi.star_apply, star_mul, dotProduct, Matrix.mulVec,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : K) * _ = _
      ring }
  have hsP : (s : Set (Fin n → K)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 K) K a) • y ∈ M := by
    rw [← hM.2]
    change ∀ x ∈ M, star x ⬝ᵥ G *ᵥ ((algebraMap (𝓞 K) K a) • y) ∈ (1 : Submodule (𝓞 K) K)
    intro x hx
    obtain ⟨b, hb⟩ := (hs ▸ Submodule.span_le.mpr hsP) hx
    have hpair : (b : K) = star x ⬝ᵥ G *ᵥ ((algebraMap (𝓞 K) K a) • y) := by
      rw [hb]
      simp only [f, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    refine ⟨b, ?_⟩
    simpa [LinearMap.toSpanSingleton_apply, Algebra.smul_def] using hpair
  have hy' : (algebraMap (𝓞 K) K a) • y ∈ Submodule.span K (M : Set (Fin n → K)) :=
    Submodule.subset_span hy
  have := (Submodule.span K (M : Set (Fin n → K))).smul_mem (algebraMap (𝓞 K) K a)⁻¹ hy'
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this


theorem extNorm_mul_pairK_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, (G τ)ᴴ = G τ) → (∀ τ, IsUnit (G τ).det) → (∀ τ, IsSelfDualK (G τ) (M τ)) → ∀ x ∈ nabK lam M, ∀ y ∈ nabK lam M, extNorm K lam * pairK lam G x y ∈ (algebraMap (𝓞 K) K).range := by
  intro K _ _ _ ι _ n lam G M hG hdet hM x hx y hy
  obtain ⟨hglob, hloc⟩ := GlobalTheory.LocInt.localIntegrality K
  refine hglob _ fun w => ?_
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (selfDualK_full (G τ) (M τ) (hM τ)) (conjPl w)
  choose B' hB' using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (selfDualK_full (G τ) (M τ) (hM τ)) w
  have hx' : x.1 ∈ nabP lam M := hx
  have hy' : y.1 ∈ nabP lam M := hy
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars] at hx' hy'
  have hF := hx' (conjPl w) B hB
  have hF' := hy' w B' hB'
  have ex : x.1 = actP lam B (actP lam B⁻¹ x.1) := by rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  have ey : y.1 = actP lam B' (actP lam B'⁻¹ y.1) := by rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  obtain ⟨q, hq, hq'⟩ := extNormPos K ι n lam
  have hne : extNorm K lam ≠ 0 := by
    rw [hq']
    simpa using hq.ne'
  have hP := fun τ => GlobalTheory.GramLoc.gram_locally_unimodular K n (G τ) (M τ) (hG τ) (hdet τ) (hM τ) w (B τ) (B' τ) (hB τ) (hB' τ)
  rw [pairK_apply, ex, ey, pairTransport K ι n lam G B B', pairP_apply, ← mul_assoc, mul_div_cancel₀ _ hne,
    fockL_apply]
  refine val_mul_nonneg w ?_ ?_
  · exact val_prod_nonneg w _ _ fun τ _ => (val_zpow_eq_zero w (hP τ).2 _).ge
  · exact GlobalTheory.TestLat.vw_fockS_blockAct_nonneg K ι n w _ _ _ (hloc ι n lam (conjPl w) _ hF) (hloc ι n lam w _ hF')
      fun τ a b => (hP τ).1 b a

end GlobalTheory.PairInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinsumQuotientNonnegOfSwapConj
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem sum_nonneg_of_swap_conj_fintype (Q : Type) [AddCommGroup Q] [Fintype Q] (ψ : Q → ℂ)
    (P S L : Q →+ Q) (hL : Function.Injective L)
    (hP : ∀ x, P (P x) = P x) (hS : ∀ x, S (S x) = x)
    (hSP : ∀ x, S (P x) = S x - P (S x)) (hLP : ∀ x, L (P x) = P (L x))
    (hψ : ∀ x, ψ x = ψ (P x) * ψ (x - P x)) (hψS : ∀ x, ψ (S x) = ψ x)
    (hψL : ∀ x, ψ (L x) = (starRingEnd ℂ) (ψ x)) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ q : Q, ψ q = (r : ℂ) := by
  set A : Finset Q := Finset.univ.filter (fun x => P x = x) with hA
  set A' : Finset Q := Finset.univ.filter (fun x => P x = 0) with hA'
  have mA : ∀ x, x ∈ A ↔ P x = x := by intro x; simp [hA]
  have mA' : ∀ x, x ∈ A' ↔ P x = 0 := by intro x; simp [hA']
  have h1 : ∑ q : Q, ψ q = ∑ p ∈ A ×ˢ A', ψ p.1 * ψ p.2 := by
    refine Finset.sum_nbij' (fun q => (P q, q - P q)) (fun p => p.1 + p.2) ?_ ?_ ?_ ?_ ?_
    · intro q _
      simp [Finset.mem_product, mA, mA', hP]
    · intro p _
      exact Finset.mem_univ _
    · intro q _
      simp
    · intro p hp
      rw [Finset.mem_product, mA, mA'] at hp
      ext <;> simp [hp.1, hp.2]
    · intro q _
      exact hψ q
  have h2 : ∑ x ∈ A', ψ x = ∑ x ∈ A, ψ x := by
    refine Finset.sum_nbij' S S ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mA'] at hx
      rw [mA]
      have := hSP x
      rw [hx, map_zero] at this
      exact (sub_eq_zero.mp this.symm).symm
    · intro x hx
      rw [mA] at hx
      rw [mA']
      have := hSP x
      rw [hx] at this
      exact sub_eq_self.mp this.symm
    · intro x _
      exact hS x
    · intro x _
      exact hS x
    · intro x _
      exact (hψS x).symm
  have h3 : (starRingEnd ℂ) (∑ x ∈ A, ψ x) = ∑ x ∈ A, ψ x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_bij (fun x _ => L x) ?_ ?_ ?_ ?_
    · intro x hx
      rw [mA] at hx
      rw [mA, ← hLP, hx]
    · intro x _ y _ h
      exact hL h
    · intro y hy
      obtain ⟨x, rfl⟩ := (Finite.injective_iff_surjective.mp hL) y
      refine ⟨x, ?_, rfl⟩
      rw [mA] at hy ⊢
      apply hL
      rw [hLP, hy]
    · intro x _
      exact (hψL x).symm
  obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.mp h3
  refine ⟨t * t, mul_self_nonneg t, ?_⟩
  rw [h1, Finset.sum_product, ← Finset.sum_mul_sum, h2, ht]
  push_cast
  rfl

theorem finsum_quotient_nonneg_of_swap_conj :
    ∀ (G : Type) [AddCommGroup G] (B : AddSubgroup G) [Finite (G ⧸ B)] (φ : G → ℂ) (P S L : G →+ G), (∀ x, ∀ w ∈ B, φ (x + w) = φ x) → (∀ w ∈ B, P w ∈ B ∧ S w ∈ B) → (∀ x, L x ∈ B ↔ x ∈ B) → (∀ x, P (P x) = P x) → (∀ x, S (S x) = x) → (∀ x, S (P x) = S x - P (S x)) → (∀ x, L (P x) = P (L x)) → (∀ x, φ x = φ (P x) * φ (x - P x)) → (∀ x, φ (S x) = φ x) → (∀ x, φ (L x) = (starRingEnd ℂ) (φ x)) → ∃ r : ℝ, 0 ≤ r ∧ ∑ᶠ q : G ⧸ B, φ q.out = (r : ℂ) := by
  intro G _ B _ φ P S L hper hB hLB hP hS hSP hLP hφ hφS hφL
  haveI : Fintype (G ⧸ B) := Fintype.ofFinite _
  have hout : ∀ x : G, φ (QuotientAddGroup.mk x : G ⧸ B).out = φ x := by
    intro x
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_out_eq_mul B x
    rw [hw]
    exact hper x w w.2
  let P' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B P (fun w hw => (hB w hw).1)
  let S' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B S (fun w hw => (hB w hw).2)
  let L' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B L (fun w hw => (hLB w).2 hw)
  have eP : ∀ x : G, P' (x : G ⧸ B) = (P x : G) := fun x => rfl
  have eS : ∀ x : G, S' (x : G ⧸ B) = (S x : G) := fun x => rfl
  have eL : ∀ x : G, L' (x : G ⧸ B) = (L x : G) := fun x => rfl
  rw [finsum_eq_sum_of_fintype]
  refine sum_nonneg_of_swap_conj_fintype (G ⧸ B) (fun q => φ q.out) P' S' L' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro q hq
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [eL, QuotientAddGroup.eq_zero_iff] at hq
      exact (QuotientAddGroup.eq_zero_iff x).2 ((hLB x).1 hq)
  all_goals
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      simp only [eP, eS, eL, ← QuotientAddGroup.mk_sub, hout]
      first
        | rw [hP]
        | rw [hS]
        | rw [hSP]
        | rw [hLP]
        | exact hφ x
        | exact hφS x
        | exact hφL x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.TraceInt

theorem pair_integral {E : Type} [Field E] [NumberField E] [StarRing E] {N N' : ℕ}
    {L : Submodule (𝓞 E) (Fin N → E)} {L' : Submodule (𝓞 E) (Fin N' → E)}
    (hL : IsSDLat E N L) (hL' : IsSDLat E N' L') {A B : Matrix (Fin N') (Fin N) E}
    (hA : ∀ x ∈ L, A.mulVec x ∈ L') (hB : ∀ x ∈ L, B.mulVec x ∈ L') :
    IsIntegral ℤ (∑ i, ∑ j, A i j * star (B i j)) := by
  obtain ⟨hLfg, hLspan, hLdual⟩ := hL
  obtain ⟨-, -, hL'dual⟩ := hL'
  obtain ⟨m, x, φ, hx, hφ, hxφ⟩ := GlobalTheory.TauLat.exists_dual_family L
    { toIsLattice := Submodule.IsLattice.of_fg E hLfg, span_eq_top := hLspan }

  set ψ : Fin m → Fin N → E := fun k b => star (φ k b) with hψdef
  have hψ : ∀ k, ψ k ∈ L := by
    intro k
    rw [hLdual]
    intro y hy
    rw [GlobalTheory.TauLat.mem_range_iff]
    have h1 : ∑ i, star (y i) * ψ k i = starRingEnd E (φ k ⬝ᵥ y) := by
      rw [starRingEnd_apply, dotProduct, star_sum]
      simp [hψdef, star_mul', mul_comm]
    unfold stdH
    rw [h1]
    exact GlobalTheory.TauLat.integral_map _ (hφ k y hy)

  have key : ∀ i, ∑ j, A i j * star (B i j) = ∑ k, (A.mulVec (x k)) i * star ((B.mulVec (ψ k)) i) := by
    intro i
    have e1 : ∑ j, A i j * star (B i j) =
        ∑ a, ∑ b, A i a * star (B i b) * ∑ k, x k a * φ k b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [hxφ, mul_ite]
    rw [e1]
    simp only [Matrix.mulVec, dotProduct, hψdef, star_sum, star_mul', star_star, Finset.mul_sum,
      Finset.sum_mul]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_comm]
  refine IsIntegral.sum _ fun k _ => ?_

  have hint : IsIntegral ℤ (∑ i, star ((A.mulVec (x k)) i) * (B.mulVec (ψ k)) i) := by
    rw [← GlobalTheory.TauLat.mem_range_iff]
    exact (hL'dual _).1 (hB _ (hψ k)) _ (hA _ (hx k))
  have h2 : ∑ i, (A.mulVec (x k)) i * star ((B.mulVec (ψ k)) i) =
      starRingEnd E (∑ i, star ((A.mulVec (x k)) i) * (B.mulVec (ψ k)) i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, starRingEnd_apply, starRingEnd_apply, star_star, mul_comm]
  rw [h2]
  exact GlobalTheory.TauLat.integral_map _ hint

theorem mulVec_mem_of_homL (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') : ∀ x ∈ L, A.mulVec x ∈ L' := by
  unfold homL at hA
  induction hA using Submodule.span_induction with
  | mem B hB => exact hB
  | zero => intro x _; simp
  | add B C _ _ hB hC =>
    intro x hx
    rw [Matrix.add_mulVec]
    exact L'.add_mem (hB x hx) (hC x hx)
  | smul c B _ hB =>
    intro x hx
    rw [Matrix.smul_mulVec]
    exact L'.smul_mem c (hB x hx)

theorem hYY_add_left (D : D7) {N N' : ℕ} (x x' y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (x + x') y = hYY D x y + hYY D x' y := by
  unfold hYY
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem hYY_add_right (D : D7) {N N' : ℕ} (x y y' : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D x (y + y') = hYY D x y + hYY D x y' := by
  unfold hYY
  simp only [Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hYY_gen (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) (hL' : SD D L')
    {a a' : D.host.E} (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (ha' : a' ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    {A B : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L') (hB : B ∈ homL D L L') :
    hYY D (a • A) (a' • B) ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  have hs : IsIntegral ℤ (∑ i, ∑ j, A i j * D.host.conj (B i j)) := by
    let _ := D.host.cmStar
    have h := pair_integral (E := D.host.E) hL hL' (mulVec_mem_of_homL D hA) (mulVec_mem_of_homL D hB)
    simpa only [bridge_star_holds _ D.host] using h
  have hsum : ∑ i, ∑ j, (a • A) i j * D.host.conj ((a' • B) i j) =
      a * (∑ i, ∑ j, A i j * D.host.conj (B i j)) * D.host.conj a' := by
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have has : a * (∑ i, ∑ j, A i j * D.host.conj (B i j)) ∈ D.host.AA0 := by
    have h1 : ∀ c : 𝓞 D.host.E, (c : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro c
      have h := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
      rwa [Algebra.smul_def] at h
    rw [mul_comm]
    exact h1 ⟨_, hs⟩
  unfold hYY
  rw [hsum]
  exact (factMMUnimodular _ D.host _).1 has a' ha'

private theorem exists_ringOfIntegers_eq_conj (D : D7) (c : 𝓞 D.host.E) :
    ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.host.conj (c : D.host.E) :=
  ⟨⟨D.host.conj (c : D.host.E),
    GlobalTheory.TauLat.integral_map (D.host.conj : D.host.E →+* D.host.E) c.isIntegral_coe⟩, rfl⟩

private theorem conjO_conjO_unimodular_class_representatives (D : D7) (z : D.host.E) : D.host.conj (D.host.conj z) = z := by
  let _ := D.host.cmStar
  rw [← bridge_star_holds _ D.host z, ← bridge_star_holds _ D.host (star z), star_star]

private theorem hYY_smul_left_eq_conj_smul_right (D : D7) {N N' : ℕ} (c c' : 𝓞 D.host.E)
    (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (c • x) y = hYY D x (c' • y) := by
  unfold hYY
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
  change (c : D.host.E) * x i j * D.host.conj (y i j) =
    x i j * (D.host.conj (c' : D.host.E) * D.host.conj (y i j))
  rw [hc, conjO_conjO_unimodular_class_representatives]
  ring

private theorem hYY_smul_right_eq_conj_smul_left (D : D7) {N N' : ℕ} (c c' : 𝓞 D.host.E)
    (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D x (c • y) = hYY D (c' • x) y := by
  have hc' : (c : D.host.E) = D.host.conj (c' : D.host.E) := by rw [hc, conjO_conjO_unimodular_class_representatives]
  exact (hYY_smul_left_eq_conj_smul_right D c' c hc' x y).symm

theorem hYY_integral : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    ∀ x ∈ YYl D L L', ∀ y ∈ YYl D L L', hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  intro D N N' L L' hL hL' x hx y hy
  have hsub : ∀ (c : 𝓞 D.host.E) (a : D.host.E),
      a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) →
      (c : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro c a ha
    have h := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
    rwa [Algebra.smul_def] at h

  have hgen : ∀ y ∈ YYl D L L', ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      ∀ A ∈ homL D L L', hYY D (a • A) y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
    intro y hy
    unfold YYl at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a', ha', B, hB, rfl⟩ := hz
      intro a ha A hA
      exact hYY_gen D hL hL' ha ha' hA hB
    | zero =>
      intro a _ A _
      unfold hYY
      simp
    | add z w _ _ hz hw =>
      intro a ha A hA
      rw [hYY_add_right]
      exact Subring.add_mem _ (hz a ha A hA) (hw a ha A hA)
    | smul c z _ hz =>
      intro a ha A hA
      obtain ⟨c', hc'⟩ := exists_ringOfIntegers_eq_conj D c
      rw [hYY_smul_right_eq_conj_smul_left D c c' hc', ← smul_assoc, Algebra.smul_def]
      exact hz _ (hsub c' a ha) A hA
  unfold YYl at hx
  induction hx using Submodule.span_induction generalizing y with
  | mem z hz =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hz
    exact hgen y hy a ha A hA
  | zero =>
    unfold hYY
    simp
  | add z w _ _ hz hw =>
    rw [hYY_add_left]
    exact Subring.add_mem _ (hz y hy) (hw y hy)
  | smul c z _ hz =>
    obtain ⟨c', hc'⟩ := exists_ringOfIntegers_eq_conj D c
    rw [hYY_smul_left_eq_conj_smul_right D c c' hc']
    exact hz _ ((YYl D L L').smul_mem c' hy)

end GlobalTheory.NormSum.TraceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStable
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.WeightDecomp

lemma comp_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) (S : Finset (Ix p q → ℚ)) :
    ∀ f : (Ix p q → ℚ) → V, (∀ ν, f ν ∈ wtSub act ν) → ∑ ν ∈ S, f ν ∈ N → ∀ ν ∈ S, f ν ∈ N := by
  first
  | exact @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | (apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem ..)

theorem mem_iSup_inf_wtSub : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V),
    (∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) → ∀ x ∈ N, x ∈ (⨆ μ : Ix p q → ℚ, wtSub act μ) →
      x ∈ ⨆ μ : Ix p q → ℚ, N ⊓ wtSub act μ := by
  intro p q V _ _ act N hN x hx hx'
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have h := comp_mem act N hN f.support f hf hx
  refine Submodule.sum_mem _ fun ν hν => ?_
  exact Submodule.mem_iSup_of_mem ν ⟨h ν hν, hf ν⟩

end GlobalTheory.WeightDecomp
end

