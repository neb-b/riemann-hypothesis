module

public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueDual
section
open Formalism.REAL

namespace GlobalTheory

theorem splitCasimir_eigenvalue_dual : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + (n : ℂ) := by
  intro V _ _ _ n E Et Om m hrel hunit hdet hEt hOm lam x hx hxe
  obtain ⟨-, -, -, hcomm⟩ := tensor_dual_standard_rel V n E Et Om hrel hunit hEt hOm
  obtain ⟨K, hK, -⟩ := lastComatrixRow_inverts_dual V n E Om m hrel hdet hOm
  have key : ∀ z : PiLp 2 (fun _ : Fin (n + 1) => V), Om z = lam • z →
      z (Fin.last n) ≠ 0 → ∃ j, lam = m j + (n : ℂ) := by
    intro z hz hzl
    have h0 := hK ((n : ℂ) - lam) z
    have hzero : ((n : ℂ) - lam - (n : ℂ)) • z + Om z = 0 := by
      rw [hz, ← add_smul]
      simp
    rw [hzero, map_zero] at h0
    have hprod : (∏ j, ((n : ℂ) - lam + m j)) = 0 := by
      rcases (smul_eq_zero.mp h0.symm) with h | h
      · exact h
      · exact absurd h hzl
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hprod
    exact ⟨j, by linear_combination -hj⟩
  by_cases hl : x (Fin.last n) = 0
  · have hc : ∃ c, x c ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      apply hx
      ext c
      simp [hne c]
    obtain ⟨c, hc⟩ := hc
    apply key (Et c (Fin.last n) x)
    · have h1 := congrArg (fun f => f x) (hcomm c (Fin.last n))
      simp only [Module.End.mul_apply] at h1
      rw [h1, hxe, map_smul]
    · rw [hEt, hl, map_zero]
      simpa using hc
  · exact key x hxe hl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdNabValLeadingMinorsOfColumnJets
section
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory


open CrudeValue SymbolCols in
theorem sum_prod_nabVal_leading_minors_of_column_jets : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), constantCoeff h = 0 → ∀ (w0 : O) (q : ℕ) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → ∀ (u : (Σ τ : T, Fin (r τ)) → Fin d → k) (lam : Fin n → (Σ τ : T, Fin (r τ)) → Fin d → k), (∀ b l l', (∃ i, col l.1 i = b) → (∃ i, col l'.1 i = b) → ∑ i, lam b l i * u l' i = if l = l' then 1 else 0) → ∀ (c : Fin n → k) (f : Fin n → PS k 1 d), (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ (colM al b).degree → coeff mo (f b) = c b * coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) = (∏ b, c b) * ∏ p, ((al p).factorial : k) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 q T _ _ r n col m hcol P al hP hal u lam hpair c f hf
  obtain ⟨h1, hhom, -, hsupp⟩ :=
    LeadingMinors.coeff_prod_leading_minors k T r n col m hcol P al hP hal
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  have halP : al ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, h1]
    exact one_ne_zero
  set E : PS k 1 d := FB.expS k ((q : k) • B.hL k h w0) with hE
  have hE1 : constantCoeff E = 1 := constantCoeff_expS _ (by
    rw [smul_eq_C_mul, map_mul, constantCoeff_hL B h hh w0, mul_zero])
  have hdeg : ∀ mo ∈ P.support, mo.degree = al.degree := fun mo hmo => by
    have := hhom (MvPolynomial.mem_support_iff.1 hmo)
    rw [← this, Finsupp.degree_eq_weight_one]
    rfl
  have hval : ∀ mo ∈ P.support, ∀ b, (colM mo b).degree ≤ (colM al b).degree →
      B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) =
        if colM mo b = colM al b then (∏ l, ((al (l, b)).factorial : k)) * c b else 0 := by
    intro mo hmo b hb
    have hsym := constantCoeff_dmonOf_prod_linear R k (algebraMap R k) d B.G _ u (lam b)
      (fun _ => 1) (colM al b) (colM mo b) (C (c b) * E)
      (fun l l' hl hl' => hpair b l l' (hsupp al halP l b (by rwa [colM_apply] at hl))
        (hsupp mo hmo l' b (by rwa [colM_apply] at hl'))) hb
    simp only [colM_apply, one_pow, mul_one, map_mul, constantCoeff_C, hE1] at hsym
    rw [nabVal_monomial, ← hE, ← hsym, ← mul_assoc, mul_comm _ (C (c b))]
    refine constantCoeff_DmonOf_congr_jet k d _ _ u (colM mo b) _ _ fun mo' hm => ?_
    refine coeff_mul_congr (colM al b).degree _ _ E (fun mo'' hm' => ?_) mo' (hm.trans hb)
    rw [coeff_C_mul]
    exact hf b mo'' hm'
  rw [Finset.sum_eq_single al]
  · rw [h1, one_mul, Finset.prod_congr rfl fun b _ => (hval al halP b le_rfl).trans (if_pos rfl),
      Finset.prod_mul_distrib, mul_comm, Fintype.prod_prod_type_right]
  · intro mo hmo hne
    obtain ⟨b, hb, hb'⟩ := exists_col mo al (hdeg mo hmo) hne
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (by rw [hval mo hmo b hb, if_neg hb']), mul_zero]
  · intro hal'
    exact absurd halP hal'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitDeterminantBasis
section
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Pdiv

namespace GlobalTheory.UnitDeterminantBasis

theorem det_ne_zero {k A O : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing O]
    [Algebra k O] [IsDomain O] {n : ℕ} {e : A}
    (b : Module.Basis (Fin n) k (LinearMap.range (LinearMap.mulLeft k e)))
    (T : Fin n → (A →ₐ[k] O)) (hT : Function.Injective T) (hTe : ∀ j, T j e = 1) :
    (Matrix.of fun i j => T j (b i : A)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hc0
  have hli := (linearIndependent_algHom_toLinearMap k A O).comp T hT
  rw [Fintype.linearIndependent_iff] at hli
  funext j
  refine hli c ?_ j
  have h1 : (∑ j, c j • (T j).toLinearMap) ∘ₗ
      (LinearMap.range (LinearMap.mulLeft k e)).subtype = 0 := by
    refine b.ext fun i => ?_
    have := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    simpa [LinearMap.sum_apply, mul_comm] using this
  ext a
  have h2 := LinearMap.congr_fun h1 ⟨e * a, a, rfl⟩
  simpa [LinearMap.sum_apply, hTe] using h2

end GlobalTheory.UnitDeterminantBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightNearDiagonalOperatorsBounds
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem wtdiag_pyth {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ι : Type} (T : Finset ι) (x : ι → M)
    (h : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ⟪x i, x j⟫_ℂ = 0) (c : ι → ℂ) :
    ‖∑ i ∈ T, c i • x i‖ ^ 2 = ∑ i ∈ T, ‖c i‖ ^ 2 * ‖x i‖ ^ 2 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ← ih (fun i hi j hj => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]
    have h0 : ⟪c a • x a, ∑ i ∈ s, c i • x i⟫_ℂ = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [inner_smul_left, inner_smul_right, h a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun e => ha (e ▸ hi))]
      simp
    rw [@norm_add_sq ℂ, h0, norm_smul]
    simp [mul_pow]

theorem wtNear_diag_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → (∀ m : ℝ, (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → m ≤ ∑ a, ω a ^ 2) → m * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2) ∧ (∀ (a : Fin n) (ζ : ℂ) (d : ℝ), 0 ≤ d → (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → d ≤ ‖ζ + (ω a : ℂ)‖) → d ^ 2 * ‖w‖ ^ 2 ≤ ‖ζ • w + E a a w‖ ^ 2) ∧ ∀ (a : Fin n) (D : ℝ), (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → |ω a| ≤ D) → ‖E a a w‖ ^ 2 ≤ D ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E Λ t w hU hw
  obtain ⟨T, x, hx, hsum, horth⟩ := _root_.GlobalTheory.WtOrth.wtNear_orth_decomp M n ε E Λ t w hU hw
  have P := wtdiag_pyth T x horth
  have hw2 : ‖w‖ ^ 2 = ∑ ω ∈ T, ‖x ω‖ ^ 2 := by
    have := P (fun _ => 1)
    simpa [← hsum] using this
  have hE : ∀ a, E a a w = ∑ ω ∈ T, (ω a : ℂ) • x ω := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Finset.sum_congr rfl fun ω hω => (hx ω hω).2 a
  have hE2 : ∀ a, ‖E a a w‖ ^ 2 = ∑ ω ∈ T, ω a ^ 2 * ‖x ω‖ ^ 2 := by
    intro a
    rw [hE a, P]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    simp_rw [hE2]
    rw [Finset.sum_comm, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hm ω (hx ω hω).1) (sq_nonneg _)
  · intro a ζ d hd h
    have e : ζ • w + E a a w = ∑ ω ∈ T, (ζ + (ω a : ℂ)) • x ω := by
      rw [hE a]
      conv_lhs => rw [hsum, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ω _ => (add_smul _ _ _).symm
    rw [e, P, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd (h ω (hx ω hω).1) 2) (sq_nonneg _)
  · intro a D h
    rw [hE2, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h ω (hx ω hω).1) 2
end GlobalTheory
end

