module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0232
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCoeffMonomial
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.MinorBound

theorem card_strictMono_le (a d : ℕ) [Fintype {s : Fin a → Fin d // StrictMono s}] :
    Fintype.card {s : Fin a → Fin d // StrictMono s} ≤ 2 ^ d := by
  have h : Function.Injective
      (fun s : {s : Fin a → Fin d // StrictMono s} => (Set.range s.1 : Set (Fin d))) := by
    intro s t hst
    exact Subtype.ext ((s.2.range_inj t.2).1 hst)
  have := Fintype.card_le_of_injective _ h
  simpa using this

theorem sum_coeff_monomial {σ : Type} (w : (σ →₀ ℕ) → ℂ) :
    ∃ L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ, (∀ α c, L (MvPolynomial.monomial α c) = c * w α) ∧
      ∀ P, L P = ∑ α ∈ P.support, AddMonoidAlgebra.coeff P α * w α := by
  let L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ := (MvPolynomial.basisMonomials σ ℂ).constr ℂ w
  have h1 : ∀ α c, L (MvPolynomial.monomial α c) = c * w α := by
    intro α c
    have : MvPolynomial.monomial α c = c • (MvPolynomial.basisMonomials σ ℂ) α := by
      simp [MvPolynomial.smul_monomial]
    rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  refine ⟨L, h1, fun P => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum]
  simp only [h1]

theorem prod_monomial {σ ι : Type} (s : Finset ι) (α : ι → σ →₀ ℕ) (c : ι → ℂ) :
    ∏ i ∈ s, MvPolynomial.monomial (α i) (c i) =
      MvPolynomial.monomial (∑ i ∈ s, α i) (∏ i ∈ s, c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih,
      MvPolynomial.monomial_mul]

noncomputable def expo (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : Mono D a d :=
  ∑ τ, ∑ j, ∑ i, Finsupp.single (τ, (T τ j).1 (p τ j i), i) 1

theorem minorPol_eq (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    minorPol D T = ∑ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)),
      MvPolynomial.monomial (expo D T p) (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)) := by
  unfold minorPol
  have hdet : ∀ τ (j : Fin (n τ)), (Matrix.of fun i i' : Fin a =>
      (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det =
      ∑ σ : Equiv.Perm (Fin a), MvPolynomial.monomial
        (∑ i, Finsupp.single ((τ, (T τ j).1 (σ i), i) : GL3Theta.Idx D a d) 1)
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) := by
    intro τ j
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply, MvPolynomial.X]
    rw [prod_monomial, ← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (GL3Theta.Idx D a d) ℂ),
      MvPolynomial.C_mul_monomial]
    simp
  simp only [hdet]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr (by convert rfl) fun p _ => ?_
  simp only [prod_monomial, expo]

theorem expo_le (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) (k : D.what₂.Tau × Fin d × Fin a) :
    expo D T p k ≤ n k.1 := by
  obtain ⟨τ0, r, c⟩ := k
  simp only [expo, Finset.sum_apply']
  rw [Finset.sum_eq_single τ0]
  · calc _ ≤ ∑ _j : Fin (n τ0), 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.sum_eq_single c]
          · rw [Finsupp.single_apply]; split_ifs <;> simp
          · intro i _ hi
            rw [Finsupp.single_apply, if_neg]
            simp [hi]
          · simp
      _ = n τ0 := by simp
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    simp [hτ]
  · simp

theorem expo_sum (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) :
    ((expo D T p).sum fun _ m => m) = a * ∑ τ, n τ := by
  have : ((expo D T p).sum fun _ m => m) = Finsupp.degree (expo D T p) := rfl
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [expo, map_sum, Finsupp.degree_single]
  simp [Finset.mul_sum, mul_comm]

theorem minor_bound : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → (∀ τ, (n τ : ℝ) ≤ 2 * B) → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → (Fintype.card (Tup D a d n) ≤ 2 ^ (d * ∑ τ, n τ)) ∧ ∀ T : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D T) G‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ)) := by
  intro D a d n G S A B hA hB hS hn hG hbd
  constructor
  · simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_mul, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' fun τ _ => Nat.pow_le_pow_left (card_strictMono_le a d) _
  · intro T
    obtain ⟨L, hL1, hL2⟩ := sum_coeff_monomial
      (fun α : Mono D a d => (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α)
    have h0 : GL3Theta.applyAt0 D (minorPol D T) G = L (minorPol D T) := by
      rw [hL2]; simp only [GL3Theta.applyAt0, mul_assoc]
    set M := S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ) with hM
    have hM0 : 0 ≤ M := by
      have : (0:ℝ) < B := by linarith
      have := Real.pi_pos
      positivity
    have hterm : ∀ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)),
        ‖L (MvPolynomial.monomial (expo D T p)
          (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)))‖ ≤ Real.sqrt M := by
      intro p
      rw [hL1, norm_mul]
      have hs : ‖(∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ))‖ = 1 := by
        rw [norm_prod]
        refine Finset.prod_eq_one fun τ _ => ?_
        rw [norm_prod]
        refine Finset.prod_eq_one fun j _ => ?_
        rcases Int.units_eq_one_or (Equiv.Perm.sign (p τ j)) with h | h <;> simp [h]
      rw [hs, one_mul]
      apply Real.le_sqrt_of_sq_le
      have := _root_.GlobalTheory.GaussCauchy.monomial_deriv_bound D a d G S A B hA hB hS hG hbd (expo D T p) (fun k =>
        le_trans (by exact_mod_cast expo_le D T p k) (hn k.1))
      rwa [expo_sum] at this
    have hcard : (Fintype.card (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : ℝ) =
        (a.factorial : ℝ) ^ (∑ τ, n τ) := by
      simp [Fintype.card_pi, Fintype.card_perm, Finset.prod_pow_eq_pow_sum]
    have hle : ‖L (minorPol D T)‖ ≤ (a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [minorPol_eq, map_sum]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    rw [h0]
    calc _ ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, Real.sq_sqrt hM0]

end GlobalTheory.MinorBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableExpNegHerm
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.GaussSumm

theorem exists_mul_norm_sq_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) : ∃ c : ℝ, 0 < c ∧ ∀ x : V, c * ‖x‖ ^ 2 ≤ (H x x).re := by
  have hcont : Continuous fun x : V => (H x x).re := by
    let b := Module.finBasis ℂ V
    have e : (fun x : V => H x x) = fun x => ∑ i, H x (b i) * conj (b.repr x i) := by
      funext x
      conv_lhs => rw [show H x x = H x (∑ i, b.repr x i • b i) by rw [b.sum_repr]]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, smul_eq_mul, mul_comm]
    have : Continuous fun x : V => H x x := by
      rw [e]
      refine continuous_finsetSum _ fun i _ => ?_
      have h1 : Continuous fun x : V => H x (b i) :=
        (H.flip (b i)).continuous_of_finiteDimensional
      have h2 : Continuous fun x : V => b.repr x i :=
        (b.coord i).continuous_of_finiteDimensional
      exact h1.mul (continuous_conj.comp h2)
    exact continuous_re.comp this
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Metric.sphere (0 : V) 1, c ≤ (H x x).re := by
    refine (isCompact_sphere (0 : V) 1).exists_forall_le' hcont.continuousOn fun x hx => hH.2 x ?_
    rintro rfl
    simp at hx
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h1 := hle (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne'])
  have e : H (((‖x‖⁻¹ : ℝ) : ℂ) • x) (((‖x‖⁻¹ : ℝ) : ℂ) • x) = ((‖x‖⁻¹ ^ 2 : ℝ) : ℂ) * H x x := by
    rw [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, conj_ofReal, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [e, re_ofReal_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
  have e2 : ‖x‖⁻¹ ^ 2 * (H x x).re * ‖x‖ ^ 2 = (H x x).re := by field_simp
  rwa [e2] at h2

theorem exp_le_inv_pow {a : ℝ} (ha : 0 < a) (C : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(a * t ^ 2) + C * t) ≤ (k.factorial * Real.exp ((C + 1) ^ 2 / (4 * a))) * t⁻¹ ^ k := by
  have h1 : t ^ k / k.factorial ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hk] at h1
  have h2 : -(a * t ^ 2) + C * t + t ≤ (C + 1) ^ 2 / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a * t - (C + 1))]
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc Real.exp (-(a * t ^ 2) + C * t) * t ^ k
      ≤ Real.exp (-(a * t ^ 2) + C * t) * (Real.exp t * k.factorial) := by gcongr
    _ = k.factorial * Real.exp (-(a * t ^ 2) + C * t + t) := by rw [Real.exp_add _ t]; ring
    _ ≤ _ := by gcongr

theorem summable_exp_neg_herm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (C : ℝ), Summable (fun x : Λ => Real.exp (-(π / 2) * (H x x).re + C * ‖(x : V)‖)) := by
  intro V _ _ _ H hH Λ _ C
  obtain ⟨c, hc, hle⟩ := exists_mul_norm_sq_le H hH
  letI : NormedSpace ℝ V := NormedSpace.complexToReal
  haveI : FiniteDimensional ℝ V := FiniteDimensional.complexToReal V
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := ‹DiscreteTopology Λ›
  have hs : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (Module.finrank ℤ L + 1) :=
    ZLattice.summable_norm_pow_inv L (Module.finrank ℤ L + 1) (Nat.lt_succ_self _)
  have ha : 0 < π / 2 * c := by have := Real.pi_pos; positivity
  refine Summable.of_norm_bounded_eventually (hs.mul_left
    ((Module.finrank ℤ L + 1).factorial * Real.exp ((C + 1) ^ 2 / (4 * (π / 2 * c))))) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : Λ)] with x hx
  have hn : 0 < ‖(x : V)‖ := norm_pos_iff.2 fun h => hx (Subtype.ext h)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine le_trans (Real.exp_le_exp.2 ?_) (exp_le_inv_pow ha C _ hn)
  have := mul_le_mul_of_nonneg_left (hle x) (by have := Real.pi_pos; positivity : 0 ≤ π / 2)
  linarith

end GlobalTheory.UnitaryTheta.GaussSumm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorConjugateTangentSpacePadZeroColumns
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.ConjRestrict

theorem coeff_taylorDir_embDomain {σ σ' W : Type*} [Fintype σ] [Fintype σ'] [NormedAddCommGroup W]
    [NormedSpace ℂ W] (e : σ ↪ σ') (u : σ' → W) {f : W → ℂ} (hf : AnalyticAt ℂ f 0) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (taylorDir (fun i => u (e i)) f) =
      MvPowerSeries.coeff (Finsupp.embDomain e α) (taylorDir u f) := by
  have h1 : ((α.toMultiset.toList : List σ) : Multiset σ) = Finsupp.toMultiset α := by simp
  have h2 : ((α.toMultiset.toList.map e : List σ') : Multiset σ') =
      Finsupp.toMultiset (Finsupp.embDomain e α) := by
    rw [← Multiset.map_coe, h1, Finsupp.toMultiset_map, Finsupp.embDomain_eq_mapDomain]
  have h3 : ∏ i, ((Finsupp.embDomain e α) i).factorial = ∏ i, (α i).factorial := by
    rw [← Finsupp.prod_fintype (Finsupp.embDomain e α) (fun _ n => n.factorial) (by simp),
      Finsupp.prod_embDomain, Finsupp.prod_fintype _ _ (by simp)]
  rw [coeff_taylorDir_eq_lineDerivList _ hf h1, coeff_taylorDir_eq_lineDerivList _ hf h2, h3,
    List.map_map]
  rfl

def colEmb (D : D7) (N N' m : ℕ) :
    D.what₂.Tau × Fin N' × Fin N ↪ D.what₂.Tau × Fin N' × Fin (N + m) :=
  ⟨fun k => (k.1, k.2.1, Fin.castAdd m k.2.2), by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at h
    simp [h]⟩

theorem colEmb_apply (D : D7) (N N' m : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    colEmb D N N' m k = (k.1, k.2.1, Fin.castAdd m k.2.2) := rfl

theorem pad_coordV (D : D7) {N N' : ℕ} (m : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    pad D m (coordV D k) = coordV D (colEmb D N N' m k) := by
  funext τ a i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [pad_left]; simp [coordV, colEmb_apply]
  · rw [pad_right]
    have : Fin.natAdd N i ≠ Fin.castAdd m k.2.2 := by
      intro h
      have := congrArg Fin.val h
      have := k.2.2.2
      simp at *
      omega
    simp [coordV, colEmb_apply, this]

theorem taylor_pad (D : D7) {N N' : ℕ} (m : ℕ) {G : VC D (N + m) N' → ℂ} (hG : Differentiable ℂ G)
    (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z : VC D N N' => G (pad D m z)) α =
      Formalism.MainNotions.TaylorLogMetric.taylor D G (Finsupp.embDomain (colEmb D N N' m) α) := by
  have han : AnalyticAt ℂ G 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Filter.Eventually.of_forall hG)
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff, ← coeff_taylorDir_embDomain _ _ han]
  have h := taylorDir_comp_clm (LinearMap.toContinuousLinearMap (padL D m (N := N) (N' := N')))
    (coordV D) han
  simp only [LinearMap.coe_toContinuousLinearMap', padL_apply, pad_coordV] at h
  rw [h]

theorem mono_pad (D : D7) {N N' : ℕ} (m : ℕ) (α : Mono D N N') (z : VC D N N') :
    mono D (Finsupp.embDomain (colEmb D N N' m) α) (pad D m z) = mono D α z := by
  rw [mono, Finsupp.prod_embDomain]
  simp [mono, colEmb_apply]

theorem mem_range_of_mono_pad (D : D7) {N N' : ℕ} (m : ℕ) (β : Mono D (N + m) N') (z : VC D N N')
    (h : mono D β (pad D m z) ≠ 0) : β ∈ Set.range (Finsupp.embDomain (colEmb D N N' m)) := by
  rw [Finsupp.mem_range_embDomain_iff]
  rintro ⟨τ, a, i⟩ hk
  revert hk
  refine Fin.addCases (fun i _ => ⟨(τ, a, i), rfl⟩) (fun i hk => ?_) i
  refine absurd (Finset.prod_eq_zero hk ?_) h
  have : β (τ, a, Fin.natAdd N i) ≠ 0 := Finsupp.mem_support_iff.1 hk
  simp [this]

theorem fnConj_pad : ∀ (D : D7) (N N' m : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D (N + m) N' → ℂ), Differentiable ℂ G → fnConj D M ρ (fun z : VC D N N' => G (pad D m z)) = fun z => fnConj D M ρ G (pad D m z) := by
  intro D N N' m M ρ G hG
  funext z
  simp only [fnConj]
  rw [← (Finsupp.embDomain_injective (colEmb D N N' m)).tsum_eq
    (f := fun β => ρ (TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.taylor D G β)) * mono D β (pad D m z))
    (fun β hβ => mem_range_of_mono_pad D m β z (right_ne_zero_of_mul hβ))]
  simp only [taylor_pad D m hG, mono_pad]

end GlobalTheory.ConjRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaIntertwinerPairEqSumCorrespondingRepresenta
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj.IopRepr

theorem mk_eq_iff {V : Type*} [AddCommGroup V] (A₁ A₂ : AddSubgroup V) (a b : A₂) :
    (QuotientAddGroup.mk a : A₂ ⧸ A₁.addSubgroupOf A₂) = QuotientAddGroup.mk b ↔
      (a : V) - (b : V) ∈ A₁ := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  rfl

theorem iop_eq_sum (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ : AddSubgroup (VC D N N'))
    (F : VC D N N' → ℂ) (hF : RepInd D T A₁ A₂ F) {n : ℕ} (x : Fin n → A₂)
    (hx : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂))) :
    Iop D T A₁ A₂ F =
      (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T (x i) F z) := by
  let e := Equiv.ofBijective _ hx
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofEquiv _ e
  have hn : (A₁.addSubgroupOf A₂).index = n := by
    rw [AddSubgroup.index, ← Nat.card_congr e]; simp
  funext z
  unfold Iop
  rw [hn, finsum_eq_sum_of_fintype, ← e.sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((Quotient.out (e i) : A₂) : VC D N N') - x i ∈ A₁ := by
    rw [← mk_eq_iff]
    exact Quotient.out_eq (e i)
  exact congrFun (hF _ (Quotient.out (e i) : A₂).2 _ (x i).2 h) z

theorem iop_pair : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (A₁ A₂ A₁' A₂' : AddSubgroup (VC D N N')) (F F' : VC D N N' → ℂ) (R : VC D N N' → VC D N N' → Prop), (A₁.addSubgroupOf A₂).FiniteIndex → RepInd D T A₁ A₂ F → RepInd D T' A₁' A₂' F' → (∀ x ∈ A₂, ∃ x' ∈ A₂', R x x') → (∀ x' ∈ A₂', ∃ x ∈ A₂, R x x') → (∀ x x' y y', R x x' → R y y' → (x - y ∈ A₁ ↔ x' - y' ∈ A₁')) → ∃ (n : ℕ) (x x' : Fin n → VC D N N'), (∀ i, x i ∈ A₂ ∧ x' i ∈ A₂' ∧ R (x i) (x' i)) ∧ Iop D T A₁ A₂ F = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T (x i) F z) ∧ Iop D T' A₁' A₂' F' = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T' (x' i) F' z) := by
  intro D T T' N N' A₁ A₂ A₁' A₂' F F' R hfin hF hF' h1 h2 h3
  haveI : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.finite_quotient_of_finiteIndex
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (A₂ ⧸ A₁.addSubgroupOf A₂)
  let x : Fin n → A₂ := fun i => Quotient.out (e.symm i)
  have hxe : ∀ i, (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂) = e.symm i :=
    fun i => Quotient.out_eq _
  have hx : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂)) := by
    have : (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂)) = e.symm :=
      funext hxe
    rw [this]; exact e.symm.bijective
  choose y hy hR using fun i => h1 (x i) (x i).2
  let x' : Fin n → A₂' := fun i => ⟨y i, hy i⟩
  have hx' : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x' i) : A₂' ⧸ A₁'.addSubgroupOf A₂')) := by
    constructor
    · intro i j hij
      apply hx.1
      have := (mk_eq_iff _ _ _ _).1 hij
      exact (mk_eq_iff _ _ _ _).2 ((h3 _ _ _ _ (hR i) (hR j)).2 this)
    · intro q
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨a, ha, hab⟩ := h2 b b.2
      obtain ⟨i, hi⟩ := hx.2 (QuotientAddGroup.mk ⟨a, ha⟩)
      refine ⟨i, (mk_eq_iff _ _ _ _).2 ?_⟩
      exact (h3 _ _ _ _ (hR i) hab).1 ((mk_eq_iff _ _ _ _).1 hi)
  exact ⟨n, fun i => x i, y, fun i => ⟨(x i).2, hy i, hR i⟩,
    iop_eq_sum D T A₁ A₂ F hF x hx, iop_eq_sum D T' A₁' A₂' F' hF' x' hx'⟩

end GlobalTheory.ThetaConj.IopRepr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariant
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalThetaSign

theorem sign_eq {p k k' : ℕ} {m m' : ℤ} {q : ℝ} (hp : Odd p) (h : (p : ℝ) ^ k * q = (m : ℝ))
    (h' : (p : ℝ) ^ k' * q = (m' : ℝ)) : (-1 : ℂ) ^ m' = (-1 : ℂ) ^ m := by
  have key : ∀ {a a' : ℕ} {b b' : ℤ}, a ≤ a' → (p : ℝ) ^ a * q = (b : ℝ) → (p : ℝ) ^ a' * q = (b' : ℝ) →
      (-1 : ℂ) ^ b' = (-1 : ℂ) ^ b := by
    intro a a' b b' hle hb hb'
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hr : (b' : ℝ) = ((p : ℤ) ^ j * b : ℤ) := by
      rw [← hb', Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← hb, pow_add]
      ring
    have hi : b' = (p : ℤ) ^ j * b := by exact_mod_cast hr
    have hoddp : Odd ((p : ℤ) ^ j) := (by exact_mod_cast hp : Odd (p : ℤ)).pow
    have hev : Even (b' - b) := by
      rw [hi, show (p : ℤ) ^ j * b - b = ((p : ℤ) ^ j - 1) * b by ring]
      exact (hoddp.sub_odd odd_one).mul_right b
    rw [show b' = b + (b' - b) by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hev.neg_one_zpow, mul_one]
  rcases le_total k k' with hle | hle
  · exact key hle h h'
  · exact (key hle h' h).symm

theorem wPh_eq (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {p k : ℕ} {m : ℤ} (hp : p.Prime) (h2 : p ≠ 2)
    (h : (p : ℝ) ^ k * qH D T x = (m : ℝ)) : wPh D T p x = (-1 : ℂ) ^ m := by
  have hodd : Odd p := hp.odd_of_ne_two h2
  rw [wPh, if_neg h2]
  have hex : ∃ s : ℂ, ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m :=
    ⟨_, k, m, h, rfl⟩
  obtain ⟨k0, m0, h0, hs⟩ := Classical.epsilon_spec hex
  rw [hs]
  exact sign_eq hodd h h0

theorem ee_half_pow (q : ℝ) (n : ℕ) :
    ee (q / 2) ^ n = Complex.exp ((((n : ℝ) * q : ℝ) : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
  rw [ee, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem exp_int_pi (m : ℤ) : Complex.exp ((m : ℂ) * ((Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ m := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem cj_top_pow (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (z : ℂ) (n : ℕ) :
    cj ⊤ σ (z ^ n) = cj ⊤ σ z ^ n := by
  have hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) :=
    fun w => dif_pos IntermediateField.mem_top
  simp only [cj]
  rw [hl, hl, ← map_pow]
  congr 1

theorem cj_top_sign (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (m : ℤ) :
    cj ⊤ σ ((-1 : ℂ) ^ m) = (-1 : ℂ) ^ m := by
  have hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) :=
    fun w => dif_pos IntermediateField.mem_top
  have he : (⟨(-1 : ℂ) ^ m, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) = (-1) ^ m := by
    apply Subtype.ext
    change (-1 : ℂ) ^ m = (⊤ : IntermediateField ℚ ℂ).val ((-1) ^ m)
    rw [map_zpow₀, map_neg, map_one]
  simp only [cj]
  rw [hl, he, map_zpow₀, map_neg, map_one]

theorem wPh_conj : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (x x' : VC D N N') (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (p k : ℕ) (m : ℤ), p.Prime → p ≠ 2 → (p : ℝ) ^ k * qH D T x = (m : ℝ) → cj ⊤ σ (wdPh D T x) = wdPh D T' x' → wPh D T p x = (-1 : ℂ) ^ m ∧ wPh D T' p x' = (-1 : ℂ) ^ m := by
  intro D T T' N N' x x' σ p k m hp h2 h hcj
  refine ⟨wPh_eq D T x hp h2 h, ?_⟩
  have h1 : wdPh D T x ^ (p ^ k) = (-1 : ℂ) ^ m := by
    rw [wdPh, ee_half_pow, Nat.cast_pow, h, ← exp_int_pi m, Complex.ofReal_intCast]
  have h3 : wdPh D T' x' ^ (p ^ k) = (-1 : ℂ) ^ m := by
    rw [← hcj, ← cj_top_pow, h1, cj_top_sign]
  rw [wdPh, ee_half_pow, ← exp_int_pi m, Complex.exp_eq_exp_iff_exists_int] at h3
  obtain ⟨l, hl⟩ := h3
  have hπ : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have hreal : (p : ℝ) ^ k * qH D T' x' = ((m + 2 * l : ℤ) : ℝ) := by
    have hc : (((p : ℝ) ^ k * qH D T' x' : ℝ) : ℂ) = (((m + 2 * l : ℤ) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hπ
      push_cast at hl ⊢
      linear_combination hl
    exact Complex.ofReal_injective hc
  rw [wPh_eq D T' x' hp h2 hreal, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), (even_two_mul l).neg_one_zpow, mul_one]

end GlobalTheory.GalThetaSign
end

