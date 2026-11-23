module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmodule
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.CauchyFar
section
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4

section Adic

variable {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

private lemma ev_le {x : AdicCompletion I M} {s m : ℕ} (h : s ≤ m)
    (e : AdicCompletion.eval I M m x = 0) : AdicCompletion.eval I M s x = 0 := by
  have hx := x.2 h
  rw [AdicCompletion.eval_apply] at e ⊢
  rw [← hx, e, map_zero]

private lemma cauchy_far (d : ℕ → AdicCompletion I M) (n : ℕ)
    (hd : ∀ k, AdicCompletion.eval I M (n + k) (d (k + 1) - d k) = 0) (k j : ℕ) :
    AdicCompletion.eval I M (n + k) (d (k + j) - d k) = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := ev_le (show n + k ≤ n + (k + j) by omega) (hd (k + j))
    have e : d (k + (j + 1)) - d k = (d (k + j + 1) - d (k + j)) + (d (k + j) - d k) := by
      rw [← add_assoc]; abel
    rw [e, map_add (f := _), h1, ih, add_zero]

private lemma lim_exists (d : ℕ → AdicCompletion I M) (n : ℕ)
    (hd : ∀ k, AdicCompletion.eval I M (n + k) (d (k + 1) - d k) = 0) :
    ∃ L : AdicCompletion I M, ∀ k, AdicCompletion.eval I M (n + k) (L - d k) = 0 := by
  have hc : ∀ s j, AdicCompletion.eval I M s (d (s + j)) = AdicCompletion.eval I M s (d s) :=
    fun s j => sub_eq_zero.1 (by
      rw [← map_sub]; exact ev_le (by omega) (cauchy_far d n hd s j))
  obtain ⟨L, hLe⟩ : ∃ L : AdicCompletion I M, ∀ s, AdicCompletion.eval I M s L =
      AdicCompletion.eval I M s (d s) := by
    refine ⟨⟨fun s => AdicCompletion.eval I M s (d s), ?_⟩, fun _ => rfl⟩
    intro m p hmp
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmp
    have hx := (d (m + j)).2 hmp
    have hy := hc m j
    simp only [AdicCompletion.eval_apply] at hy ⊢
    rw [hx, hy]
  refine ⟨L, fun k => ?_⟩
  have h := cauchy_far d n hd k n
  rw [map_sub, sub_eq_zero, add_comm k n] at h
  rw [map_sub, sub_eq_zero, hLe, h]

end Adic

private lemma vand (l : ℕ) [Fact l.Prime] (w : ℕ) : ∃ (c : ℕ) (E : Fin (w + 1) → Fin (w + 1) → ℤ_[l]),
    ∀ i i' : Fin (w + 1), ∑ j : Fin (w + 1), E i j * (((j : ℕ) : ℤ_[l]) ^ (i' : ℕ)) =
      if i = i' then (l : ℤ_[l]) ^ c else 0 := by
  set V : Matrix (Fin (w + 1)) (Fin (w + 1)) ℤ_[l] :=
    Matrix.vandermonde (fun j : Fin (w + 1) => ((j : ℕ) : ℤ_[l])) with hV
  have hdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_vandermonde_ne_zero_iff]
    intro a b h
    exact Fin.ext (Nat.cast_injective h)
  refine ⟨V.det.valuation, fun i j => ((PadicInt.unitCoeff hdet)⁻¹ : (ℤ_[l])ˣ) * V.adjugate i j, ?_⟩
  intro i i'
  have h1 : (V.adjugate * V) i i' = ∑ j, V.adjugate i j * V j i' := Matrix.mul_apply
  rw [Matrix.adjugate_mul] at h1
  have h2 := PadicInt.unitCoeff_spec hdet
  have h3 : ∑ j : Fin (w + 1), ((PadicInt.unitCoeff hdet)⁻¹ : (ℤ_[l])ˣ) * V.adjugate i j * (((j : ℕ) : ℤ_[l]) ^ (i' : ℕ))
      = ((PadicInt.unitCoeff hdet)⁻¹ : (ℤ_[l])ˣ) * ∑ j, V.adjugate i j * V j i' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hV, Matrix.vandermonde_apply, mul_assoc]
  rw [h3, ← h1]
  by_cases hii : i = i'
  · subst hii
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, if_true]
    exact (Units.inv_mul_eq_iff_eq_mul _).2 h2
  · simp [Matrix.smul_apply, Matrix.one_apply_ne hii, hii]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private lemma un_pow (X : Tower Ω ε) {l a b P : ℕ} {f : X.Kˣ} (hf : f ∈ X.Un (l ^ (a + b))) :
    f ^ P ∈ X.Un (l ^ b) := by
  intro W hW
  obtain ⟨g, hg⟩ := hf W hW
  refine ⟨(g ^ (l ^ a)) ^ P, ?_⟩
  have e : (((f ^ P : X.Kˣ) : X.K) / (((g ^ (l ^ a)) ^ P : X.Kˣ) : X.K) ^ (l ^ b)) =
      ((f : X.K) / (g : X.K) ^ (l ^ (a + b))) ^ P := by
    push_cast
    rw [div_pow, pow_add]
    congr 1
    ring
  rw [e, map_pow, hg, one_pow]

private lemma cls_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s P : ℕ) (f : X.Kˣ) :
    X.cls l s (f ^ P) = (P : ℤ_[l]) • X.cls l s f := by
  unfold Tower.cls
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  rw [ofMul_pow, Nat.cast_smul_eq_nsmul ℤ_[l]]
  exact map_nsmul (TensorProduct.mk ℤ ℤ_[l] (Additive X.Kˣ) 1) P (Additive.ofMul f)

private lemma cls_le (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {s m : ℕ} (h : s ≤ m) (f : X.Kˣ) {x : X.Khat l}
    (e : AdicCompletion.eval (idl l) (X.Kl l) m x = X.cls l m f) :
    AdicCompletion.eval (idl l) (X.Kl l) s x = X.cls l s f := by
  have hx := x.2 h
  rw [AdicCompletion.eval_apply] at e ⊢
  rw [← hx, e]
  rfl

private lemma kmap_cong (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) {s : ℕ} {x : X.Khat l}
    (e : AdicCompletion.eval (idl l) (X.Kl l) s x = 0) :
    AdicCompletion.eval (idl l) (X.Kl l) s (X.kmap l φ x) = 0 := by
  rw [AdicCompletion.eval_apply] at e ⊢
  unfold Tower.kmap
  simp only [LinearMap.restrictScalars_apply]
  rw [AdicCompletion.map_val_apply, e, map_zero]

end UpperTheory.Kd.K4

theorem UpperTheory.Kd.K4.lim :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l : ℕ) [Fact l.Prime] (N w : ℕ), ∃ c : ℕ, ∀ (n : ℕ) (t : ℕ → X.Fn l), (∀ k, PolMod X l w (n + k) (t k)) →
      (∀ k, CgF X l (n + k) (t (k + 1)) (t k)) → (∀ k, ∀ γ ∈ Gam N l, CgF X l (n + k) (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (t k)) (t k)) →
      ∃ b, LiftB X l N w n c (t 0) b := by
  intro Ω _ _ _ ε X l _ N w
  obtain ⟨c, E, hE⟩ := vand l w
  refine ⟨c, fun n t hP hC hI => ?_⟩
  choose a hp using hP
  have ht := fun k => (hp k).2
  have hrec : ∀ k i, ((l : ℤ_[l]) ^ c) • a k i =
      ∑ j : Fin (w + 1), E i j • t k ![((j : ℕ) : ℤ_[l]), 1] := by
    intro k i
    have e : ∀ j : Fin (w + 1), E i j • t k ![((j : ℕ) : ℤ_[l]), 1] =
        ∑ i' : Fin (w + 1), (E i j * (((j : ℕ) : ℤ_[l]) ^ (i' : ℕ))) • a k i' := by
      intro j
      rw [ht k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      simp [smul_smul]
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hE]
    simp
  have hd : ∀ i k, AdicCompletion.eval (idl l) (X.Kl l) (n + k)
      (((l : ℤ_[l]) ^ c) • a (k + 1) i - ((l : ℤ_[l]) ^ c) • a k i) = 0 := by
    intro i k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hrec, hrec, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← smul_sub, map_smul, hC k _, smul_zero]
  choose L hL using fun i => lim_exists (fun k => ((l : ℤ_[l]) ^ c) • a k i) n (hd i)
  let b : X.Fn l := fun u => ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • L i
  have hb : ∀ k u, AdicCompletion.eval (idl l) (X.Kl l) (n + k) (b u - ((l : ℤ_[l]) ^ c) • t k u) = 0 := by
    intro k u
    show AdicCompletion.eval (idl l) (X.Kl l) (n + k)
      ((∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • L i) - ((l : ℤ_[l]) ^ c) • t k u) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ht k u, Finset.smul_sum, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_comm ((l : ℤ_[l]) ^ c), ← smul_sub, map_smul, hL i k, smul_zero]
  have hA : ∀ i, L i ∈ X.ASet l := by
    intro i s
    obtain ⟨f, hf, hr⟩ := (hp s).1 i
    refine ⟨f ^ (l ^ c), un_pow X hf, ?_⟩
    have h1 := ev_le (show s ≤ n + s by omega) (hL i s)
    rw [map_sub, sub_eq_zero, map_smul] at h1
    rw [h1, cls_le X l (show s ≤ n + s by omega) f hr, cls_pow]
    push_cast
    rfl
  have hpol : b ∈ X.Pol l w :=
    ⟨L, fun i => Submodule.subset_span (hA i), fun u => rfl⟩
  have hinv : ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
    intro γ hγ
    funext u
    apply AdicCompletion.ext
    intro s
    have h1 := ev_le (show s ≤ n + s by omega) (hb s u)
    have h2 := ev_le (show s ≤ n + s by omega) (hb s (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
    have h3 := kmap_cong X l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv h2
    have h4 := ev_le (show s ≤ n + s by omega) (hI s γ hγ u)
    have e : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b u - b u =
        (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
          (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) - ((l : ℤ_[l]) ^ c) • t s (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)))
        + ((l : ℤ_[l]) ^ c) • (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (t s) u - t s u)
        - (b u - ((l : ℤ_[l]) ^ c) • t s u) := by
      show X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) - b u = _ + ((l : ℤ_[l]) ^ c) • (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (t s (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) - t s u) - _
      rw [map_sub, map_smul, smul_sub]
      abel
    have h5 : AdicCompletion.eval (idl l) (X.Kl l) s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b u - b u) = 0 := by
      rw [e, map_sub, map_add (f := _), map_smul, h3, h4, h1]
      simp
    rw [map_sub, sub_eq_zero] at h5
    exact h5
  exact ⟨b, Submodule.subset_span ⟨hpol, hinv⟩, fun u => hb 0 u⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.CountSpanEqZero
section
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem valuation_eq_exp_neg_count_spanSingleton {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (v : IsDedekindDomain.HeightOneSpectrum R) {x : L}
    (hx : x ≠ 0) :
    v.valuation L x = WithZero.exp
      (-FractionalIdeal.count L v (FractionalIdeal.spanSingleton (nonZeroDivisors R) x)) := by
  classical
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hs : (s : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors R) (IsLocalization.mk' L a s) =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) ((algebraMap R L) (s : R))⁻¹ *
        ↑(Ideal.span {a}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined L v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    hspan, IsDedekindDomain.HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg ha,
    v.intValuation_if_neg hs, ← WithZero.exp_sub]
  congr 1
  ring

private theorem valuation_eq_one_of_valuationSubring_eq_one {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (v : IsDedekindDomain.HeightOneSpectrum R) {y : L}
    (hy : ((v.valuation L).valuationSubring).valuation y = 1) : v.valuation L y = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have h1 : y ∈ (v.valuation L).valuationSubring :=
    (ValuationSubring.valuation_le_one_iff _ y).mp hy.le
  have h2 : y⁻¹ ∈ (v.valuation L).valuationSubring :=
    (ValuationSubring.valuation_le_one_iff _ _).mp (by rw [map_inv₀, hy, inv_one])
  rw [Valuation.mem_valuationSubring_iff] at h1 h2
  rw [map_inv₀] at h2
  have hv0 : v.valuation L y ≠ 0 := by simpa using hy0
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr hv0)).mp h2)

private theorem ringOfIntegers_mem_of_polynomial_mem (k K : Type) [Field k] [Field K] [Algebra k[X] K]
    [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K] (B : ValuationSubring K)
    (hB : ∀ p : k[X], algebraMap k[X] K p ∈ B) (x : FunctionField.ringOfIntegers k K) :
    (x : K) ∈ B := by
  obtain ⟨p, hpm, hp⟩ := x.2
  let φ : k[X] →+* B := (algebraMap k[X] K).codRestrict B hB
  have hc : (algebraMap B K).comp φ = algebraMap k[X] K := RingHom.ext fun _ => rfl
  have hint : IsIntegral B (x : K) := by
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hc]
    exact hp
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

private theorem exists_mul_spanSingleton_eq_of_classGroup_mk_eq {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (I J : (FractionalIdeal (nonZeroDivisors R) L)ˣ)
    (h : ClassGroup.mk L I = ClassGroup.mk L J) :
    ∃ x : L, x ≠ 0 ∧
      (I : FractionalIdeal (nonZeroDivisors R) L) * FractionalIdeal.spanSingleton (nonZeroDivisors R) x = J := by
  have h2 := congrArg (ClassGroup.equiv L) h
  rw [ClassGroup.equiv_mk, ClassGroup.equiv_mk, QuotientGroup.mk'_eq_mk'] at h2
  obtain ⟨z, ⟨x, rfl⟩, hz⟩ := h2
  refine ⟨x, x.ne_zero, ?_⟩
  have h3 := congrArg Units.val hz
  simpa [FractionalIdeal.canonicalEquiv_self] using h3

theorem UpperTheory.Kd.K4.cdAbs :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (m m' : ℕ) (f : K), 0 < m → 0 < m' → f ≠ 0 →
      (∀ B : ValuationSubring K, (∀ p : k[X], algebraMap k[X] K p ∈ B) → ∃ c : K, c ≠ 0 ∧ B.valuation (f / c ^ m) = 1) →
      ∃ h : K, h ≠ 0 ∧ ∀ B : ValuationSubring K, (∀ p : k[X], algebraMap k[X] K p ∈ B) → ∃ c : K, c ≠ 0 ∧ B.valuation (f / h ^ m / c ^ (m * m')) = 1 := by
  intro k K _ _ _ _ _ _ _ _ m m' f hm hm' hf hloc
  classical
  have hF : FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf
  have hdiv : ∀ v : IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k K),
      (m : ℤ) ∣ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f) := by
    intro v
    obtain ⟨c, hc, hcv⟩ := hloc ((v.valuation K).valuationSubring) (fun p => by
      rw [Valuation.mem_valuationSubring_iff,
        IsScalarTower.algebraMap_apply k[X] (FunctionField.ringOfIntegers k K) K]
      exact v.valuation_le_one _)
    have h1 := valuation_eq_one_of_valuationSubring_eq_one v hcv
    have hc0 : v.valuation K c ^ m ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hc)
    rw [map_div₀, map_pow, div_eq_one_iff_eq hc0, valuation_eq_exp_neg_count_spanSingleton v hf, valuation_eq_exp_neg_count_spanSingleton v hc,
      ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h1
    exact ⟨FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ c), by linarith⟩
  obtain ⟨I, hIdef⟩ : ∃ I : FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K,
      I = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k K),
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K) ^
          (FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f) / m) :=
    ⟨_, rfl⟩
  have he : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k K) in
      Filter.cofinite, FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f) / m = 0 :=
    (FractionalIdeal.finite_factors _).mono fun v hv => by rw [hv, Int.zero_ediv]
  have hI0 : I ≠ 0 := by
    rw [hIdef]
    refine finprod_induction (fun J => J ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) ?_
    intro v
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have hIm : I ^ m = FractionalIdeal.spanSingleton _ f := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (pow_ne_zero m hI0)]
    conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hF]
    refine finprod_congr fun v => ?_
    rw [FractionalIdeal.count_pow, hIdef, FractionalIdeal.count_finprod K v _ he,
      Int.mul_ediv_cancel' (hdiv v)]
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.classGroup_ringOfIntegers_divisible k K m' hm' (ClassGroup.mk K (Units.mk0 I hI0))
  obtain ⟨Ju, rfl⟩ : ∃ Ju : (FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K)ˣ,
      ClassGroup.mk K Ju = d :=
    ClassGroup.induction K (P := fun d => ∃ Ju, ClassGroup.mk K Ju = d) (fun J => ⟨J, rfl⟩) d
  rw [← map_pow] at hd
  obtain ⟨x, hx, hxJ⟩ := exists_mul_spanSingleton_eq_of_classGroup_mk_eq _ _ hd
  rw [Units.val_mk0, Units.val_pow_eq_pow_val] at hxJ
  refine ⟨x⁻¹, inv_ne_zero hx, fun B hB => ?_⟩
  have hJ : ((Ju : FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K) :
      Submodule (FunctionField.ringOfIntegers k K) K) ^ (m * m') =
        (FunctionField.ringOfIntegers k K) ∙ (f / x⁻¹ ^ m) := by
    rw [← FractionalIdeal.coe_pow, ← FractionalIdeal.coe_spanSingleton (nonZeroDivisors _), pow_mul',
      ← hxJ, mul_pow, hIm, FractionalIdeal.spanSingleton_pow,
      FractionalIdeal.spanSingleton_mul_spanSingleton, inv_pow, div_inv_eq_mul]
  have hw : f / x⁻¹ ^ m ≠ 0 := div_ne_zero hf (pow_ne_zero _ (inv_ne_zero hx))
  obtain ⟨c, hc, hcv⟩ := _root_.GlobalTheory.valuation_eq_one_of_pow_eq_span K K (FunctionField.ringOfIntegers k K) B _ (m * m')
    (Nat.mul_pos hm hm') (fun r => ringOfIntegers_mem_of_polynomial_mem k K B hB r) (f / x⁻¹ ^ m) hw hJ
  exact ⟨c, hc, by simpa using hcv⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.GaloisActionAdicClose
section
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem UpperTheory.Kd.K4.galoisAction_adic_close {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (b : X.Fn l) (hb : b ∈ X.B N l w) (n : ℕ) :
    ∃ E0 : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s x = x) → ∀ u,
      (X.galB l s b - b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  induction hb using Submodule.span_induction with
  | mem b hb => exact GalCont.galB_sub_mem_of_Pol X l w b hb.1 n
  | zero => exact ⟨∅, fun s _ u => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨E, hE⟩ := ha
    obtain ⟨F, hF⟩ := hb
    refine ⟨E ∪ F, fun s hs u => ?_⟩
    have h := Submodule.add_mem _ (hE s (fun x hx => hs x (Finset.mem_union_left _ hx)) u)
      (hF s (fun x hx => hs x (Finset.mem_union_right _ hx)) u)
    have e : (X.galB l s (a + b) - (a + b)) u =
        (X.galB l s a - a) u + (X.galB l s b - b) u := by
      simp only [map_add (f := _), Pi.add_apply, Pi.sub_apply]
      abel
    rw [e]
    exact h
  | smul r a _ ha =>
    obtain ⟨E, hE⟩ := ha
    refine ⟨E, fun s hs u => ?_⟩
    have h := Submodule.smul_mem _ r (hE s hs u)
    have e : (X.galB l s (r • a) - r • a) u = r • (X.galB l s a - a) u := by
      simp only [map_smul, Pi.smul_apply, Pi.sub_apply, smul_sub]
    rw [e]
    exact h

theorem UpperTheory.Kd.K4.galc :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ), ∀ b ∈ X.B N l w, ∀ n : ℕ, ∃ E0 : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s x = x) → CgF X l n (X.galB l s b) b := by
  intro Ω _ _ _ ε X l _ N w b hb n
  obtain ⟨E, hE⟩ := UpperTheory.Kd.K4.galoisAction_adic_close X l N w b hb n
  refine ⟨E, fun s hs u => ?_⟩
  have h := hE s hs u
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker] at h
  exact h
end

