module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMulEqZeroImp
section
namespace GlobalTheory.TraceMulVanishing

theorem trace_mul_eq_zero_imp {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] [IsReduced A] (x : A)
    (h : ∀ z : A, (Algebra.trace F A : A → F) (x * z) = (0 : F)) : x = 0 := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A)
  simp only [smul_eq_mul, mul_one] at hy

  have h1 : x ^ (n + 1) = x ^ (n + 1) * (x * y) := by
    calc x ^ (n + 1) = x * x ^ n := by rw [pow_succ']
      _ = x * (x ^ (n + 1) * y) := by rw [hy]
      _ = x ^ (n + 1) * (x * y) := by ring
  have h2 : ∀ j : ℕ, x ^ (n + 1) = x ^ (n + 1) * (x * y) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ (x * y) j, ← mul_assoc, ← ih]; exact h1
  have h3 : x ^ (n + 1) = x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1) := by
    calc x ^ (n + 1) = x ^ (n + 1) * (x * y) ^ (n + 1) := h2 (n + 1)
      _ = x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1) := by rw [mul_pow]; ring
  have he : IsIdempotentElem (x ^ (n + 1) * y ^ (n + 1)) := by
    unfold IsIdempotentElem
    calc x ^ (n + 1) * y ^ (n + 1) * (x ^ (n + 1) * y ^ (n + 1))
        = (x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1)) * y ^ (n + 1) := by ring
      _ = x ^ (n + 1) * y ^ (n + 1) := by rw [← h3]
  have htr : Algebra.trace F A (x ^ (n + 1) * y ^ (n + 1)) = 0 := by
    have := h (x ^ n * y ^ (n + 1))
    rwa [show x * (x ^ n * y ^ (n + 1)) = x ^ (n + 1) * y ^ (n + 1) by ring] at this
  have hl : IsIdempotentElem (Algebra.lmul F A (x ^ (n + 1) * y ^ (n + 1))) := he.map _
  have hz : Algebra.lmul F A (x ^ (n + 1) * y ^ (n + 1)) = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff hl).1 (by rw [← Algebra.trace_apply]; exact htr)
  have he0 : x ^ (n + 1) * y ^ (n + 1) = 0 := by
    have := congrArg (fun f : Module.End F A => f 1) hz
    simpa using this
  have hxn : x ^ (n + 1) = 0 := by
    rw [h3, mul_assoc, he0, mul_zero]
  exact IsReduced.eq_zero x ⟨n + 1, hxn⟩

end GlobalTheory.TraceMulVanishing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsometrySchwartzOperator
section
open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory.TransDecay

theorem seminorm_mul_shift_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ h : 𝓢(V, ℂ)) (hχ : HasCompactSupport (χ : V → ℂ)) (l m M : ℕ) :
    ∃ C : ℝ, ∀ (v : V) (k' : 𝓢(V, ℂ)), (∀ x, k' x = χ x * h (x + v)) →
      SchwartzMap.seminorm ℂ l m k' ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  obtain ⟨r, hr⟩ := hχ.isCompact.isBounded.subset_closedBall (0 : V)
  set R := max r 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hxR : ∀ x ∈ tsupport (χ : V → ℂ), ‖x‖ ≤ R := fun x hx => by
    have := hr hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set S := ((Finset.Iic (M, m)).sup fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h
  have hS0 : 0 ≤ S := apply_nonneg _ _
  set A := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨R ^ l * A * ((1 + R) ^ M * (2 ^ M * S)), fun v k' hk' => ?_⟩
  have hvpos : 0 < (1 + ‖v‖) ^ M := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ l m k' (by positivity) fun x => ?_
  have hfun : (k' : V → ℂ) = fun y => χ y * h (y + v) := funext hk'
  rw [hfun]
  have hsh : ContDiff ℝ (⊤ : ℕ∞) (fun y => h (y + v)) :=
    (h.smooth ⊤).comp (contDiff_id.add contDiff_const)
  have hL := norm_iteratedFDeriv_mul_le (χ.smooth ⊤) hsh x (n := m) (by exact_mod_cast le_top)
  have hterm : ∀ i ∈ Finset.range (m + 1), ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
      ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖) ≤
      R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ) * ((1 + R) ^ M * (2 ^ M * S)) *
        ((1 + ‖v‖) ^ M)⁻¹ := by
    intro i _
    by_cases hx : x ∈ tsupport (χ : V → ℂ)
    · have hx1 := hxR x hx
      rw [iteratedFDeriv_comp_add_right]
      have hj : (1 + ‖x + v‖) ^ M * ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ ≤ 2 ^ M * S :=
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, m)) le_rfl (Nat.sub_le _ _) h (x + v)
      have hv : 1 + ‖v‖ ≤ (1 + R) * (1 + ‖x + v‖) := by
        have : ‖v‖ ≤ ‖x + v‖ + ‖x‖ := by
          calc ‖v‖ = ‖(x + v) - x‖ := by simp
            _ ≤ _ := norm_sub_le _ _
        nlinarith [norm_nonneg (x + v)]
      have hD : ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ ≤
          (1 + R) ^ M * (2 ^ M * S) * ((1 + ‖v‖) ^ M)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hvpos]
        calc ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ * (1 + ‖v‖) ^ M
            ≤ ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ * ((1 + R) * (1 + ‖x + v‖)) ^ M := by gcongr
          _ = (1 + R) ^ M * ((1 + ‖x + v‖) ^ M * ‖iteratedFDeriv ℝ (m - i) h (x + v)‖) := by
            rw [mul_pow]; ring
          _ ≤ (1 + R) ^ M * (2 ^ M * S) := by gcongr
      have hχi : ‖iteratedFDeriv ℝ i χ x‖ ≤ SchwartzMap.seminorm ℂ 0 i χ :=
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ χ i x
      calc ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
            ‖iteratedFDeriv ℝ (m - i) h (x + v)‖)
          ≤ R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ *
            ((1 + R) ^ M * (2 ^ M * S) * ((1 + ‖v‖) ^ M)⁻¹)) := by gcongr
        _ = _ := by ring
    · have h0 : iteratedFDeriv ℝ i χ x = 0 := by
        by_contra hne
        exact hx (support_iteratedFDeriv_subset i (Function.mem_support.2 hne))
      rw [h0, norm_zero, mul_zero, zero_mul, mul_zero]
      positivity
  calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ m (fun y => χ y * h (y + v)) x‖
      ≤ ‖x‖ ^ l * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (m + 1), ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ) *
          ((1 + R) ^ M * (2 ^ M * S)) * ((1 + ‖v‖) ^ M)⁻¹ := Finset.sum_le_sum hterm
    _ = R ^ l * A * ((1 + R) ^ M * (2 ^ M * S)) * ((1 + ‖v‖) ^ M)⁻¹ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]

theorem decay : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ) →
    ∀ (χ ψ h : SchwartzMap V ℂ), HasCompactSupport (χ : V → ℂ) → ∀ M : ℕ, ∃ C : ℝ,
      ∀ (v : V) (k ψv : SchwartzMap V ℂ), (∀ x, k x = χ (x - v) * h x) → (∀ x, ψv x = ψ (x - v)) →
        ‖∫ x, T k x * starRingEnd ℂ (T ψv x) ∂μ‖ ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  intro V _ _ _ _ _ μ _ T hinv χ ψ h hχ M
  have hp : Continuous ((SchwartzMap.seminorm ℂ 0 0 : Seminorm ℂ 𝓢(V, ℂ)).comp
      (T : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))) :=
    ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (0, 0)).comp T.continuous
  obtain ⟨s, C0, -, hC0⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) _ hp
  have hA : ∀ i : ℕ × ℕ, ∃ C : ℝ, ∀ (v : V) (k' : 𝓢(V, ℂ)), (∀ x, k' x = χ x * h (x + v)) →
      SchwartzMap.seminorm ℂ i.1 i.2 k' ≤ C * ((1 + ‖v‖) ^ M)⁻¹ :=
    fun i => seminorm_mul_shift_le χ h hχ i.1 i.2 M
  choose Cf hCf using hA
  set Cs := ∑ i ∈ s, |Cf i|
  have hCs : 0 ≤ Cs := Finset.sum_nonneg fun i _ => abs_nonneg _
  set I := ∫ x, ‖T ψ x‖ ∂μ
  have hint : Integrable (fun x => ‖T ψ x‖) μ := (SchwartzMap.integrable (T ψ)).norm
  refine ⟨(C0 : ℝ) * Cs * I, fun v k ψv hk hψv => ?_⟩
  set k' := SchwartzMap.compSubConstCLM ℂ (-v) k
  have hk' : ∀ x, k' x = k (x + v) := by
    intro x; simp [k', SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  have hk'' : ∀ x, k' x = χ x * h (x + v) := by intro x; rw [hk', hk]; simp
  have hψ : ∀ x, ψ x = ψv (x + v) := by intro x; rw [hψv]; simp
  rw [← hinv v k k' ψv ψ hk' hψ]
  have hsup : (s.sup (schwartzSeminormFamily ℂ V ℂ)) k' ≤ Cs * ((1 + ‖v‖) ^ M)⁻¹ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
    calc schwartzSeminormFamily ℂ V ℂ i k' ≤ Cf i * ((1 + ‖v‖) ^ M)⁻¹ := hCf i v k' hk''
      _ ≤ |Cf i| * ((1 + ‖v‖) ^ M)⁻¹ := by gcongr; exact le_abs_self _
      _ ≤ Cs * ((1 + ‖v‖) ^ M)⁻¹ := by
        gcongr
        exact Finset.single_le_sum (f := fun i => |Cf i|) (fun i _ => abs_nonneg _) hi
  have hTk : ∀ x, ‖T k' x‖ ≤ (C0 : ℝ) * (Cs * ((1 + ‖v‖) ^ M)⁻¹) := by
    intro x
    have h2 := hC0 k'
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h2
    calc ‖T k' x‖ ≤ SchwartzMap.seminorm ℂ 0 0 (T k') := SchwartzMap.norm_le_seminorm ℂ _ x
      _ ≤ (C0 : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) k' := h2
      _ ≤ _ := by gcongr
  calc ‖∫ x, T k' x * starRingEnd ℂ (T ψ x) ∂μ‖
      ≤ ∫ x, ((C0 : ℝ) * (Cs * ((1 + ‖v‖) ^ M)⁻¹)) * ‖T ψ x‖ ∂μ := by
        refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun x => ?_)
        rw [norm_mul, RCLike.norm_conj]
        gcongr
        exact hTk x
    _ = (C0 : ℝ) * Cs * I * ((1 + ‖v‖) ^ M)⁻¹ := by rw [integral_const_mul]; ring

end GlobalTheory.TransDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegComplexBaseChangeEq
section
open scoped TensorProduct

namespace GlobalTheory

theorem algebraicIndependent_one_tmul_of_field {k K L ι : Type} [Field k] [Field K] [CommRing L] [Algebra k K] [Algebra k L]
    {t : ι → L} (ht : AlgebraicIndependent k t) :
    AlgebraicIndependent K (fun i => (1 : K) ⊗ₜ[k] t i) := by
  rw [algebraicIndependent_iff_injective_aeval] at ht ⊢
  have h1 : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L).toLinearMap ht
  have h2 : (MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ[k] t i) : MvPolynomial ι K →ₐ[K] K ⊗[k] L) =
      (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L)).comp
        (MvPolynomial.algebraTensorAlgEquiv k K (σ := ι)).symm.toAlgHom := by
    ext i
    simp
  rw [h2]
  exact h1.comp (MvPolynomial.algebraTensorAlgEquiv k K (σ := ι)).symm.injective

theorem trdeg_tensorProduct_eq {k K L : Type} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [IsDomain (K ⊗[k] L)] : Algebra.trdeg K (K ⊗[k] L) = Algebra.trdeg k L := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  have hi := algebraicIndependent_one_tmul_of_field (K := K) hs.1
  set S := Algebra.adjoin K (Set.range fun i : s => (1 : K) ⊗ₜ[k] (i : L)) with hS
  have halg : Algebra.IsAlgebraic S (K ⊗[k] L) := by
    have hA := hs.isAlgebraic
    set T := Algebra.adjoin k (Set.range (Subtype.val : s → L)) with hT
    have hmem : ∀ x : T, (1 : K) ⊗ₜ[k] (x : L) ∈ S := by
      rintro ⟨x, hx⟩
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Algebra.subset_adjoin ⟨i, rfl⟩
      | algebraMap r =>
        have : (1 : K) ⊗ₜ[k] (algebraMap k L r) = algebraMap K (K ⊗[k] L) (algebraMap k K r) := by
          rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply k K (K ⊗[k] L)]
        simp only [this]
        exact S.algebraMap_mem _
      | add x y hx hy ihx ihy =>
        simp only [TensorProduct.tmul_add]
        exact S.add_mem ihx ihy
      | mul x y hx hy ihx ihy =>
        have : (1 : K) ⊗ₜ[k] (x * y) = ((1 : K) ⊗ₜ[k] x) * ((1 : K) ⊗ₜ[k] y) := by simp
        simp only [this]
        exact S.mul_mem ihx ihy
    let g : L →+* K ⊗[k] L := (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := L)).toRingHom
    let f : T →+* S := (g.comp T.val.toRingHom).codRestrict S hmem
    have hf : Function.Injective f := by
      intro x y hxy
      have : g x = g y := congrArg Subtype.val hxy
      exact Subtype.ext (g.injective this)
    refine ⟨fun z => ?_⟩
    induction z using TensorProduct.induction_on with
    | zero => exact isAlgebraic_zero
    | add x y hx hy => exact hx.add hy
    | tmul a b =>
      have h1 : IsAlgebraic S (g b) :=
        (hA.isAlgebraic b).ringHom_of_comp_eq f g hf (by ext; rfl)
      have h2 : IsAlgebraic S (algebraMap S (K ⊗[k] L) (algebraMap K S a)) := isAlgebraic_algebraMap _
      have h3 : a ⊗ₜ[k] b = algebraMap S (K ⊗[k] L) (algebraMap K S a) * g b := by
        simp [g]
      rw [h3]
      exact h2.mul h1
  have hb : IsTranscendenceBasis K (fun i : s => (1 : K) ⊗ₜ[k] (i : L)) :=
    hi.isTranscendenceBasis_iff_isAlgebraic.mpr halg
  rw [← hb.cardinalMk_eq_trdeg, ← hs.cardinalMk_eq_trdeg]

theorem trdeg_complex_baseChange_eq : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] [IsDomain (K ⊗[ℂ] κ')], Algebra.trdeg K (K ⊗[ℂ] κ') = Algebra.trdeg ℂ κ' :=
  trdeg_tensorProduct_eq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedMonomialsLinearIndependentOverConstants
section
open scoped TensorProduct

namespace GlobalTheory

open MvPolynomial

theorem truncMono_deriv_aeval {k A : Type} [Field k] [CommRing A] [Algebra k A] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) (i : Fin d) (F : MvPolynomial (Fin d) B) :
    E i (aeval x F) = aeval x (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C b =>
    rw [aeval_C, pderiv_C, map_zero]
    exact hB i _ b.2
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p j hp =>
    have h1 : E i (aeval x p * x j) = aeval x p * E i (x j) + x j * E i (aeval x p) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [map_mul, aeval_X, h1, hp, pderiv_mul, pderiv_X, map_add (f := _), map_mul, map_mul, aeval_X, hE]
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h, Pi.single_apply, Ne.symm h]; ring

theorem truncMono_eq_zero {p : ℕ} [Fact p.Prime] {k A : Type} [Field k] [CommRing A]
    [Algebra k A] [CharP k p] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) :
    ∀ n : ℕ, ∀ F : MvPolynomial (Fin d) B,
      (∀ m ∈ F.support, (∀ i, m i < p) ∧ ∑ i, m i ≤ n) → aeval x F = 0 → F = 0 := by
  have hconst : ∀ F : MvPolynomial (Fin d) B, (∀ m, m ≠ 0 → AddMonoidAlgebra.coeff F m = 0) →
      aeval x F = 0 → F = 0 := by
    intro F hc hF
    have hFC : F = C (AddMonoidAlgebra.coeff F 0) := by
      refine MvPolynomial.ext _ _ (fun m => ?_)
      rw [coeff_C]
      by_cases hm : m = 0
      · subst hm; simp
      · rw [if_neg (Ne.symm hm)]; exact hc m hm
    rw [hFC, aeval_C] at hF
    have h0 : AddMonoidAlgebra.coeff F 0 = 0 := Subtype.ext (by simpa using hF)
    rw [hFC, h0, C_0]
  intro n
  induction n with
  | zero =>
    intro F hs hF
    apply hconst F _ hF
    intro m hm
    by_contra hc
    have := (hs m (mem_support_iff.mpr hc)).2
    apply hm
    ext i
    have := (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp this)) i (Finset.mem_univ _)
    simpa using this
  | succ n ih =>
    intro F hs hF
    have hpd : ∀ i, pderiv i F = 0 := by
      intro i
      apply ih
      · intro m hm
        rw [mem_support_iff, coeff_pderiv] at hm
        have hm' := hs _ (mem_support_iff.mpr (left_ne_zero_of_mul hm))
        refine ⟨fun j => lt_of_le_of_lt ?_ (hm'.1 j), ?_⟩
        · simp
        · have h2 := hm'.2
          simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib] at h2
          have h3 : ∑ j, (Finsupp.single i 1 : Fin d →₀ ℕ) j = 1 := by
            simp [Finsupp.single_apply]
          omega
      · rw [← truncMono_deriv_aeval x E hE B hB, hF, map_zero]
    apply hconst F _ hF
    intro m hm
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hm (Finsupp.ext h)
    by_contra hc
    have hlt := (hs m (mem_support_iff.mpr hc)).1 i
    have hcoef := coeff_pderiv (i := i) F (m - Finsupp.single i 1)
    rw [Finsupp.sub_add_single_one_cancel hi, hpd i] at hcoef
    simp at hcoef
    have hmi : (m - Finsupp.single i 1 : Fin d →₀ ℕ) i + 1 = m i := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
    have hunit : IsUnit (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) := by
      have e : (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) = algebraMap k B ((m i : ℕ) : k) := by
        rw [map_natCast, ← hmi]; push_cast; rfl
      rw [e]
      apply IsUnit.map
      apply Ne.isUnit
      rw [Ne, CharP.cast_eq_zero_iff k p]
      intro hdvd
      exact hi (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
    have hcoef' : F.coeff m * (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) = 0 := by
      have hmi' : m i - 1 = (m - Finsupp.single i 1 : Fin d →₀ ℕ) i := by
        omega
      simpa only [← hmi'] using hcoef.symm
    exact hc ((hunit.mul_left_eq_zero).mp hcoef')

end GlobalTheory

namespace GlobalTheory
open MvPolynomial

theorem truncMono_linearIndependent : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by
  intro p _ k A _ _ _ _ d x E hE B hB
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let toF : (Fin d → Fin p) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))
  have hinj : Function.Injective toF := by
    intro a b hab
    funext i
    apply Fin.ext
    have := congrArg (fun f : Fin d →₀ ℕ => f i) hab
    simpa [toF] using this
  let F : MvPolynomial (Fin d) B := ∑ a, monomial (toF a) (g a)
  have hcoeff : ∀ m, AddMonoidAlgebra.coeff F m = ∑ a, if toF a = m then g a else 0 := by
    intro m
    simp only [F, coeff_sum, coeff_monomial]
  have hF : aeval x F = 0 := by
    rw [← hg]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sum, aeval_monomial]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Subalgebra.smul_def]
    rfl
  have hF0 : F = 0 := by
    refine truncMono_eq_zero x E hE B hB (∑ _i : Fin d, p) F ?_ hF
    intro m hm
    rw [mem_support_iff, hcoeff] at hm
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    have hm' : toF a = m := by
      by_contra h
      exact ha (if_neg h)
    subst hm'
    refine ⟨fun i => by simp [toF], ?_⟩
    apply Finset.sum_le_sum
    intro i _
    simp [toF, (a i).isLt.le]
  intro a
  have := hcoeff (toF a)
  rw [hF0] at this
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  simp_rw [hinj.eq_iff] at this
  have hsum : (∑ b : Fin d → Fin p, if b = a then g b else 0) = g a := by
    simp
  rw [hsum] at this
  simpa using this.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumExpNegAbsIntLtTop
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.VolBoxMajorant

theorem tsum_pi_prod_ennreal' : ∀ {ι : Type} [Fintype ι] {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
    ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  intro ι _
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
      ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y) ?_ ?_ ?_ ι
  · intro α β _ e h X φ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h1 := h (X := fun a => X (e a)) (fun a => φ (e a))
    rw [← (Equiv.piCongrLeft X e).tsum_eq]
    calc ∑' x : ∀ a, X (e a), ∏ b, φ b (Equiv.piCongrLeft X e x b)
        = ∑' x : ∀ a, X (e a), ∏ a, φ (e a) (x a) := by
          congr 1; ext x
          rw [← Fintype.prod_equiv e (fun a => φ (e a) (Equiv.piCongrLeft X e x (e a)))
            (fun b => φ b (Equiv.piCongrLeft X e x b)) (fun _ => rfl)]
          simp only [Equiv.piCongrLeft_apply_apply]
      _ = ∏ a, ∑' y, φ (e a) y := h1
      _ = ∏ b, ∑' y, φ b y := Fintype.prod_equiv e _ _ (fun _ => rfl)
  · intro X φ
    simp
  · intro α _ h X φ
    rw [← (Equiv.piOptionEquivProd (β := X)).symm.tsum_eq, Fintype.prod_option]
    rw [← h (X := fun a => X (some a)) (fun a => φ (some a))]
    rw [← ENNReal.tsum_mul_right]
    simp only [Fintype.prod_option]
    rw [ENNReal.tsum_prod']
    congr 1; ext y
    rw [← ENNReal.tsum_mul_left]
    rfl

end GlobalTheory.VolBoxMajorant

namespace GlobalTheory.VolBoxMajorant

end GlobalTheory.VolBoxMajorant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfClosedCoverInUniversallyClose
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem universallyClosed_of_closed_cover_in_universallyClosed :
    ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y),
      UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) →
        π '' T = Set.univ → UniversallyClosed f := by
  intro S X Y P f π q s T hs hq hcomm hT hqT hπT
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hT⟩ : TopologicalSpace.Closeds Y)
  have hrange : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hcl : IsClosedImmersion (I.subschemeι ≫ q) := by
    refine .of_isPreimmersion _ ?_
    have : Set.range (I.subschemeι ≫ q) = q '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [this]; exact hqT
  have : UniversallyClosed ((I.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc, ← hcomm, ← Category.assoc]
    infer_instance
  have : Surjective (I.subschemeι ≫ π) := by
    constructor
    have : Set.range (I.subschemeι ≫ π) = π '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [← Set.range_eq_univ, this]; exact hπT
  exact UniversallyClosed.of_comp_surjective (I.subschemeι ≫ π) f

end GlobalTheory
end

