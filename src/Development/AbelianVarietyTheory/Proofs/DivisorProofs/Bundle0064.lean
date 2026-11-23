module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastRest
section
noncomputable section

open MeasureTheory

namespace GlobalTheory.Pc3.RS

theorem exists_finset_sep {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∀ (m : ℕ) (K : Submodule ℂ W), Module.finrank ℂ K = m →
      ∃ S : Finset X, ∀ w ∈ K, (∀ s ∈ S, (w : X → ℂ) s = 0) → w = 0 := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro K hK
    by_cases h0 : K = ⊥
    · exact ⟨∅, fun w hw _ => by rw [h0] at hw; exact (Submodule.mem_bot ℂ).1 hw⟩
    · obtain ⟨w0, hw0K, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
      have : ∃ x0, (w0 : X → ℂ) x0 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hw0 (Subtype.ext (funext hc))
      obtain ⟨x0, hx0⟩ := this
      let e : W →ₗ[ℂ] ℂ := (LinearMap.proj x0).comp W.subtype
      let K' : Submodule ℂ W := K ⊓ LinearMap.ker e
      have hlt : K' < K := by
        refine lt_of_le_of_ne inf_le_left fun heq => ?_
        have : w0 ∈ K' := heq ▸ hw0K
        exact hx0 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2)
      have hr : Module.finrank ℂ K' < m := hK ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨S, hS⟩ := ih _ hr K' rfl
      refine ⟨insert x0 S, fun w hw hv => hS w (Submodule.mem_inf.2 ⟨hw, ?_⟩) fun s hs => hv s (Finset.mem_insert_of_mem hs)⟩
      exact LinearMap.mem_ker.2 (hv x0 (Finset.mem_insert_self _ _))

theorem integral_mem {X Y : Type} [MeasurableSpace Y] (μ : Measure Y) (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] (G : Y → X → ℂ) (hG : ∀ y, G y ∈ W) (hi : ∀ x, Integrable (fun y => G y x) μ) :
    (fun x => ∫ y, G y x ∂μ) ∈ W := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_sep W _ ⊤ rfl
  let r : W →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun w s => (w : X → ℂ) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact hS w Submodule.mem_top fun s hs => congrFun hw ⟨s, hs⟩
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective r hinj
  have key : ∀ (w : W) (x : X), (w : X → ℂ) x = ∑ s : S, (w : X → ℂ) s * ((L (Pi.single s 1) : W) : X → ℂ) x := by
    intro w x
    have h1 : L (r w) = w := by simpa using LinearMap.congr_fun hL w
    have h2 : r w = ∑ s : S, (w : X → ℂ) s • (Pi.single s 1 : S → ℂ) := by
      ext t
      simp [r, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [← h1, h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, Finset.sum_apply]
  have hfun : (fun x => ∫ y, G y x ∂μ) =
      ((∑ s : S, (∫ y, G y s ∂μ) • L (Pi.single s 1) : W) : X → ℂ) := by
    funext x
    have e : ∀ y, G y x = ∑ s : S, G y s * ((L (Pi.single s 1) : W) : X → ℂ) x :=
      fun y => key ⟨G y, hG y⟩ x
    simp_rw [e]
    rw [integral_finsetSum (Finset.univ : Finset S) fun (s : S) _ =>
      (hi (s : X)).mul_const (((L (Pi.single s 1) : W) : X → ℂ) x)]
    simp only [integral_mul_const, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact Submodule.coe_mem _

end GlobalTheory.Pc3.RS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreTail
section
namespace GlobalTheory.AuxiliaryLemmaSecond

open IsLocalRing

theorem main : ∀ {κ : Type} [inst : Field κ] (R : Subring κ) [IsNoetherianRing ↥R] [IsIntegrallyClosed ↥R]
    [IsFractionRing (↥R) κ] (Q : Ideal ↥R) [Ideal.IsPrime Q], Q ≠ ⊥ →
    (∀ (p : Ideal ↥R), Ideal.IsPrime p → p ≠ ⊥ → p ≤ Q → p = Q) →
    ∃ (W : ValuationSubring κ), IsDiscreteValuationRing ↥W ∧ (∀ (r : ↥R), (↑r : κ) ∈ W) ∧
      (∀ r ∉ Q, (↑r : κ)⁻¹ ∈ W) ∧ (∀ r ∈ Q, r ≠ (0 : ↥R) → (↑r : κ)⁻¹ ∉ W) ∧
      ∀ w ∈ W, ∃ (b : ↥R), ∃ s ∉ Q, w = (↑b : κ) / (↑s : κ) := by
  intro κ _ R _ _ _ Q _ hQ0 hmin
  have hS : Q.primeCompl ≤ nonZeroDivisors R := Q.primeCompl_le_nonZeroDivisors
  set A : Subalgebra R κ := Localization.subalgebra.ofField κ Q.primeCompl hS with hAdef
  have memA : ∀ x : κ, x ∈ A ↔ ∃ (a s : R) (_ : s ∈ Q.primeCompl),
      x = algebraMap R κ a * (algebraMap R κ s)⁻¹ := fun x => Iff.rfl
  haveI : IsLocalization.AtPrime A Q := Localization.subalgebra.isLocalization_ofField κ _ hS
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A Q
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing Q.primeCompl A inferInstance
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A Q.primeCompl hS
  have hcm : (maximalIdeal A).comap (algebraMap R A) = Q :=
    IsLocalization.AtPrime.under_maximalIdeal A Q
  have hmap : ∀ r : R, algebraMap R κ r = (r : κ) := fun r => rfl
  simp only [hmap] at memA
  have hinj : Function.Injective (algebraMap R A) := IsLocalization.injective A hS
  have hm0 : maximalIdeal A ≠ ⊥ := by
    intro h
    apply hQ0
    rw [← hcm, h]
    exact Ideal.comap_bot_of_injective _ hinj
  have hnf : ¬ IsField A := isField_iff_maximalIdeal_eq.not.mpr hm0
  have hDVR : IsDiscreteValuationRing A := by
    have h03 := (IsDiscreteValuationRing.TFAE A hnf).out 1 4
    refine h03.mpr ⟨inferInstance, ExistsUnique.intro (maximalIdeal A) ⟨hm0, inferInstance⟩ ?_⟩
    rintro P ⟨hP0, hPp⟩
    have eP : Ideal.map (algebraMap R A) (P.comap (algebraMap R A)) = P :=
      IsLocalization.map_under Q.primeCompl A P
    have eM : Ideal.map (algebraMap R A) ((maximalIdeal A).comap (algebraMap R A)) = maximalIdeal A :=
      IsLocalization.map_under Q.primeCompl A (maximalIdeal A)
    have hc : P.comap (algebraMap R A) = Q := by
      apply hmin
      · exact Ideal.comap_isPrime _ _
      · intro h
        apply hP0
        rw [← eP, h, Ideal.map_bot]
      · rw [← hcm]
        exact Ideal.comap_mono (le_maximalIdeal hPp.ne_top)
    rw [← eP, ← eM, hc, hcm]
  let W : ValuationSubring κ := .ofSubring A.toSubring fun x => by
    simpa [IsLocalization.IsInteger] using ValuationRing.isInteger_or_isInteger A x
  refine ⟨W, hDVR, ?_, ?_, ?_, ?_⟩
  · intro r
    show (r : κ) ∈ A
    exact (memA _).mpr ⟨r, 1, Q.primeCompl.one_mem, by simp⟩
  · intro r hr
    show (r : κ)⁻¹ ∈ A
    exact (memA _).mpr ⟨1, r, hr, by simp⟩
  · intro r hrQ hr0 hmem
    change (r : κ)⁻¹ ∈ A at hmem
    obtain ⟨a, s, hs, hx⟩ := (memA _).mp hmem
    have hs0 : (s : κ) ≠ 0 := by
      intro h
      apply hs
      have : s = 0 := Subtype.ext h
      rw [this]; exact Q.zero_mem
    have hr0' : (r : κ) ≠ 0 := fun h => hr0 (Subtype.ext h)
    have key : (s : κ) = (r : κ) * (a : κ) := by
      have hx' : (r : κ)⁻¹ = (a : κ) * (s : κ)⁻¹ := by simpa using hx
      field_simp at hx'
      linear_combination hx'
    have : s = r * a := Subtype.ext (by simpa using key)
    exact hs (this ▸ Q.mul_mem_right a hrQ)
  · intro w hw
    change w ∈ A at hw
    obtain ⟨a, s, hs, rfl⟩ := (memA _).mp hw
    exact ⟨a, s, hs, by simp [div_eq_mul_inv]⟩

end GlobalTheory.AuxiliaryLemmaSecond
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreTer
section
namespace GlobalTheory.IntegerMultipleMembership

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (z : Fin n → E) : ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • z ∈ L := by
  have hz : z ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hby a
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨k, hk, hkc⟩ := hc.exists_integral_multiple
    refine ⟨k * a, mul_ne_zero hk ha, ?_⟩
    have h := L.smul_mem (⟨k • c, hkc⟩ : NumberField.RingOfIntegers E) hax
    have e : (k * a) • c • x
        = (⟨k • c, hkc⟩ : NumberField.RingOfIntegers E) • a • x := by
      change _ = (k • c) • a • x
      rw [mul_smul, smul_comm a c x, smul_assoc]
    rw [e]; exact h

end GlobalTheory.IntegerMultipleMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerAlt
section
namespace GlobalTheory.IterativeScalingBound

theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w - 1) * (2 + (w - 1)) := by ring
  rw [e, norm_mul]
  have h2 : (3/2 : ℝ) ≤ ‖2 + (w - 1)‖ := by
    have t := norm_sub_le (2 + (w - 1)) (w - 1)
    have e2 : (2 + (w - 1)) - (w - 1) = (2 : ℂ) := by ring
    rw [e2] at t
    have : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have h0 : 0 ≤ ‖w - 1‖ := norm_nonneg _
  nlinarith

theorem main : ∀ (z : ℂ), (∀ (k : ℕ), ‖z ^ (2 : ℕ) ^ k - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have key : ∀ k : ℕ, (3/2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ 2 ^ k - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have e : z ^ 2 ^ (n + 1) = (z ^ 2 ^ n) ^ 2 := by rw [pow_succ 2 n, pow_mul]
      rw [e, pow_succ (3/2 : ℝ) n]
      calc (3/2 : ℝ) ^ n * (3/2) * ‖z - 1‖ = (3/2) * ((3/2) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3/2) * ‖z ^ 2 ^ n - 1‖ := by gcongr
        _ ≤ _ := step _ (h n)
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key k
  have h2 := h k
  have h3 : 1 / 2 < (3/2 : ℝ) ^ k * ‖z - 1‖ := by rwa [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.IterativeScalingBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerBis
section
namespace GlobalTheory.IntertwiningOperators

open Polynomial

theorem intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C)
    (p : K[X]) : aeval B p * C = C * aeval A p := by
  induction p using Polynomial.induction_on with
  | C c =>
    simp only [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval B) (Polynomial.C c * X ^ n) X,
      map_mul (aeval A) (Polynomial.C c * X ^ n) X, aeval_X, aeval_X, Matrix.mul_assoc, ← h,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem main : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) := by
  intro K _ a b A B C hcop h
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B u * aeval B (Matrix.charpoly A) = 1 := by
    have := congrArg (aeval B) huv
    rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one] at this
    exact this
  have h2 : aeval B (Matrix.charpoly A) * C = 0 := by
    rw [intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = (aeval B u * aeval B (Matrix.charpoly A)) * C := by rw [h1, Matrix.one_mul]
    _ = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]

end GlobalTheory.IntertwiningOperators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerMore
section
namespace GlobalTheory.InductiveNormBound

theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w^2 - 1‖ := by
  have e : w^2 - 1 = (w - 1) * ((w - 1) + 2) := by ring
  rw [e, norm_mul]
  have h2 : (3/2 : ℝ) ≤ ‖(w - 1) + 2‖ := by
    have h3 := norm_sub_le ((w - 1) + 2) (w - 1)
    have h4 : (w - 1) + 2 - (w - 1) = (2:ℂ) := by ring
    rw [h4] at h3
    have : ‖(2:ℂ)‖ = 2 := by simp
    linarith
  have h0 := norm_nonneg (w - 1)
  nlinarith

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  have key : ∀ k : ℕ, (3/2 : ℝ)^k * ‖z - 1‖ ≤ ‖z^(2^k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := step (z^(2^k)) (hz _)
      have e : (z^(2^k))^2 = z^(2^(k+1)) := by rw [← pow_mul, ← pow_succ]
      rw [e] at hs
      have hp : (3/2:ℝ)^(k+1) = (3/2)^k * (3/2) := pow_succ _ _
      rw [hp]
      nlinarith [ih, hs]
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖) (by norm_num : (1:ℝ) < 3/2)
  have h1 := key k
  have h2 := hz (2^k)
  have h3 : 1 < (3/2:ℝ)^k * ‖z - 1‖ := by
    rw [div_lt_iff₀ hpos] at hk; linarith
  linarith

end GlobalTheory.InductiveNormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerRest
section
namespace GlobalTheory.TargetInequalityLemmas

open Polynomial

theorem main {R F K : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K] (θ z : K)
    (hz : z ∈ Algebra.adjoin F ({θ} : Set K)) :
    ∃ d : R, d ≠ 0 ∧ (algebraMap R K d * z) ∈ Algebra.adjoin R ({θ} : Set K) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hz
  simp only [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
  obtain ⟨p, rfl⟩ := hz
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  refine ⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors R) p, ?_⟩
  have hmap : (IsLocalization.integerNormalization (nonZeroDivisors R) p).map (algebraMap R F)
      = C (algebraMap R F b) * p := by
    rw [hb]
    ext i
    rw [AddMonoidAlgebra.coeff_smul_apply, coeff_C_mul, Algebra.smul_def]
  rw [← aeval_map_algebraMap F, hmap, map_mul, aeval_C, ← IsScalarTower.algebraMap_apply]

theorem target : ∀ {R F K : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field F] [inst_3 : Algebra R F] [IsFractionRing R F] [inst_5 : Field K] [inst_6 : Algebra R K] [inst_7 : Algebra F K] [IsScalarTower R F K] (θ z : K), Membership.mem (Algebra.adjoin F (Singleton.singleton θ)) z → Exists fun (d : R) ↦ And (Ne d (0 : R)) (Membership.mem (Algebra.adjoin R (Singleton.singleton θ)) (HMul.hMul ((Algebra.algebraMap R K) d) z)) :=
  fun θ z hz => main θ z hz

end GlobalTheory.TargetInequalityLemmas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleIncomparability
section
namespace GlobalTheory

theorem eq_of_le_of_comap_eq_of_indEtale : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := by
  intro B O _ _ _ ⟨ι, _, _, _, Si, _, hcov, hloc⟩ p p' hp hp' hle hcomap
  by_contra hne
  obtain ⟨x, hx', hx⟩ : ∃ x, x ∈ p' ∧ x ∉ p := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hle h)
  obtain ⟨i, hi⟩ := hcov x
  obtain ⟨E, _, _, _, P, _, ⟨e⟩⟩ := hloc i
  haveI : Algebra.QuasiFinite B (Localization.AtPrime P) := inferInstance
  haveI : Algebra.QuasiFinite B (Si i) := (Algebra.QuasiFinite.iff_of_algEquiv e).mp inferInstance
  have key := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := B)
    (p.comap (algebraMap (Si i) O)) (p'.comap (algebraMap (Si i) O)) (Ideal.comap_mono hle)
    (by
      simp only [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hcomap)
  have h1 : (⟨x, hi⟩ : Si i) ∈ p'.comap (algebraMap (Si i) O) := hx'
  rw [← key] at h1
  exact hx h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfSupPowEqOfTorsionArtinRees
section
namespace GlobalTheory

theorem inf_sup_pow_eq_of_torsion : ∀ (B : Type) [CommRing B] [IsNoetherianRing B]
    (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by
  intro B _ _ K τ τ' hle htor
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian τ' : τ'.FG)
  have hrad : K ≤ (τ.colon (s : Set B)).radical := by
    intro f hf
    have hm : ∀ b ∈ s, ∃ m : ℕ, f ^ m * b ∈ τ := fun b hb =>
      htor b (hs ▸ Submodule.subset_span hb) f hf
    choose! m hm using hm
    refine ⟨∑ b ∈ s, m b, ?_⟩
    rw [Submodule.mem_colon]
    intro b hb
    have hb' : b ∈ s := hb
    have hle' : m b ≤ ∑ b ∈ s, m b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb'
    rw [smul_eq_mul, ← Nat.sub_add_cancel hle', pow_add, mul_assoc]
    exact τ.mul_mem_left _ (hm b hb')
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian K)
  have hKm : K ^ m * τ' ≤ τ := by
    rw [Ideal.mul_le]
    intro r hr t ht
    have hr' := Submodule.mem_colon.mp (hm hr)
    rw [← hs] at ht
    induction ht using Submodule.span_induction with
    | mem x hx => simpa [smul_eq_mul] using hr' x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact τ.add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact τ.mul_mem_left a hx
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul K (M := B) (τ' : Submodule B B)
  refine ⟨c + m, fun k hk => ?_⟩
  have hAR : K ^ k ⊓ τ' ≤ τ := by
    have h := hc k (by omega)
    simp only [smul_eq_mul, Ideal.mul_top] at h
    rw [h]
    calc K ^ (k - c) * (K ^ c ⊓ τ') ≤ K ^ (k - c) * τ' := Ideal.mul_mono_right inf_le_right
      _ ≤ K ^ m * τ' := Ideal.mul_mono_left (Ideal.pow_le_pow_right (by omega))
      _ ≤ τ := hKm
  apply le_antisymm
  · rw [inf_comm, sup_inf_assoc_of_le _ hle]
    exact sup_le le_rfl hAR
  · exact le_inf hle le_sup_left

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveCotangentComplexBaseChangeOfFormsExtend
section
open TensorProduct KaehlerDifferential

namespace GlobalTheory

theorem injective_cotangentComplexBaseChange_of_forms_extend : ∀ (A P R K : Type) [CommRing A] [CommRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], (∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i) → Function.Injective (KaehlerDifferential.cotangentComplexBaseChange A R P K) := by
  intro A P R K _ _ _ _ _ _ _ _ _ _ _ _ _ hext
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  refine (Module.forall_dual_apply_eq_zero_iff K z).1 fun φ => ?_
  let ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K :=
    (φ.restrictScalars P) ∘ₗ (TensorProduct.mk P K (RingHom.ker (algebraMap P R)) 1)
  obtain ⟨D, hD⟩ := hext ℓ
  let Λ : K ⊗[P] Ω[P⁄A] →ₗ[K] K := LinearMap.liftBaseChange K D.liftKaehlerDifferential
  have key : Λ ∘ₗ cotangentComplexBaseChange A R P K = φ := by
    ext i
    simp [Λ, cotangentComplexBaseChange_tmul, kerToTensor_apply, hD, ℓ]
  have h2 := congrArg (fun f => f z) key
  simpa [hz] using h2.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveMulVecMapBasis
section
namespace GlobalTheory.BasisLeftInverse

theorem exists_left_inv {E : Type} [Field E] {n d : ℕ} (B : Matrix (Fin n) (Fin d) E)
    (h : LinearIndependent E B.col) : ∃ C : Matrix (Fin d) (Fin n) E, C * B = 1 := by
  have hinj : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem injective_mulVec_map_basis {E : Type} [Field E] {n : ℕ} (V : Submodule E (Fin n → E))
    (τ : E →+* ℂ) :
    Function.Injective (Matrix.mulVec (Matrix.of fun (k : Fin n) (i : Fin (Module.finrank E V)) =>
      τ (((Module.finBasis E V i : V) : Fin n → E) k))) := by
  let B : Matrix (Fin n) (Fin (Module.finrank E V)) E :=
    Matrix.of fun k i => ((Module.finBasis E V i : V) : Fin n → E) k
  have hB : LinearIndependent E B.col :=
    (Module.finBasis E V).linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  obtain ⟨C, hC⟩ := exists_left_inv B hB
  have hC' : C.map τ * B.map τ = 1 := by
    rw [← Matrix.map_mul, hC, Matrix.map_one τ (map_zero τ) (map_one τ)]
  change Function.Injective (B.map τ).mulVec
  intro v w hvw
  have h1 : Matrix.mulVec (C.map τ * B.map τ) v = Matrix.mulVec (C.map τ * B.map τ) w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvw]
  rwa [hC', Matrix.one_mulVec, Matrix.one_mulVec] at h1

end GlobalTheory.BasisLeftInverse
end

