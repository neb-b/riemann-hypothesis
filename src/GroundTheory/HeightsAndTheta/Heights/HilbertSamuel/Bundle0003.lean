module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexMinimalPrimesContract
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem mvPolynomial_int_complex_flat (σ : Type) :
    Module.Flat (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) :=
  Module.Flat.isBaseChange ℤ (MvPolynomial σ ℤ) ℂ (MvPolynomial σ ℂ)
    (Algebra.IsPushout.out (R := ℤ) (S := MvPolynomial σ ℤ) (R' := ℂ) (S' := MvPolynomial σ ℂ))

theorem algebraMap_mvPolynomial_int_complex (σ : Type) :
    algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) = MvPolynomial.map (Int.castRingHom ℂ) := by
  rw [MvPolynomial.algebraMap_def]
  congr 1

theorem ComplexMinimalPrimesContract.proof : ComplexMinimalPrimesContract.Statement := by
  intro σ _ P hP Q hQ
  have := hP
  have hflat := mvPolynomial_int_complex_flat σ
  have hAlg := algebraMap_mvPolynomial_int_complex σ
  have : Q.IsPrime := hQ.1.1
  have hPQ : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q := hQ.1.2
  have hle : P ≤ Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
    Ideal.map_le_iff_le_comap.mp hPQ
  have : (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have : Q.LiesOver (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) :=
    ⟨by rw [Ideal.under, Ideal.comap, hAlg]; rfl⟩
  obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (R := MvPolynomial σ ℤ) (p := P)
      (q := Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) Q hle
  have hQ'P : Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
    have := hQ'over.over
    rw [Ideal.under, hAlg] at this
    exact this.symm
  have hmapQ' : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q' :=
    Ideal.map_le_iff_le_comap.mpr hQ'P.ge
  have hQQ' : Q ≤ Q' := hQ.2 ⟨hQ'prime, hmapQ'⟩ hQ'Q
  rw [← le_antisymm hQ'Q hQQ']
  exact hQ'P

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDoubleComplexVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem DoubleComplexVanish.proof : DoubleComplexVanish.Statement := by
  intro C _ P δ κ R hδP hκP hδδ hδκ hκκ hsurj hex hzero hacyc

  have triv : ∀ p n, R ≤ p → ∀ x ∈ P p (n + 1), (∃ y ∈ P (p + 1) (n + 1), κ p (n + 1) y = x) →
      ∃ w ∈ P p n, δ p n w = x ∧ ∃ w' ∈ P (p + 1) n, κ p n w' = w := by
    rintro p n hp x - ⟨y, hy, rfl⟩
    rw [hzero (p + 1) (n + 1) (by omega) y hy, map_zero]
    exact ⟨0, zero_mem _, map_zero _, 0, zero_mem _, map_zero _⟩
  have claim : ∀ k p n, R ≤ p + k → ∀ x ∈ P p (n + 1), δ p (n + 1) x = 0 →
      (∃ y ∈ P (p + 1) (n + 1), κ p (n + 1) y = x) →
      ∃ w ∈ P p n, δ p n w = x ∧ ∃ w' ∈ P (p + 1) n, κ p n w' = w := by
    intro k
    induction k with
    | zero => exact fun p n hp x hx _ hy => triv p n (by omega) x hx hy
    | succ k ih =>
      intro p n hp x hx hdx hy0
      by_cases hRp : R ≤ p
      · exact triv p n hRp x hx hy0
      obtain ⟨y, hy, hyx⟩ := hy0
      have hdy : δ (p + 1) (n + 1) y ∈ P (p + 1) (n + 2) := hδP _ _ y hy
      have hk : κ p (n + 2) (δ (p + 1) (n + 1) y) = 0 := by
        rw [← hδκ p (n + 1) y hy, hyx, hdx]
      obtain ⟨w, hw, hwe, w', hw', hw'e⟩ :=
        ih (p + 1) (n + 1) (by omega) _ hdy (hδδ _ _ y hy) (hex p (n + 2) _ hdy hk)
      have hdyw : δ (p + 1) (n + 1) (y - w) = 0 := by rw [map_sub, hwe, sub_self]
      obtain ⟨v, hv, hve⟩ := hacyc (p + 1) (by omega) (by omega) n (y - w) (sub_mem hy hw) hdyw
      refine ⟨κ p n v, hκP _ _ v hv, ?_, v, hv, rfl⟩
      rw [hδκ p n v hv, hve, map_sub, hyx, ← hw'e, hκκ p (n + 1) w' hw', sub_zero]
  intro n x hx hdx
  obtain ⟨w, hw, hwe, -⟩ := claim R 0 n (by omega) x hx hdx (hsurj (n + 1) x hx)
  exact ⟨w, hw, hwe⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiniteSeparatingModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

namespace FiniteSeparatingModel

variable {σ : Type} {e : ℕ}

theorem aeval_eval₂ (ℓ : Fin e → MvPolynomial σ ℚ) (Q : Polynomial (MvPolynomial (Fin e) ℚ))
    (g : MvPolynomial σ ℚ) (z : σ → ℂ) :
    aeval z (Q.eval₂ (aeval ℓ).toRingHom g) =
      Q.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (aeval z g) := by
  have hc : (aeval (R := ℚ) z).toRingHom.comp (aeval (R := ℚ) ℓ).toRingHom =
      (aeval fun j => aeval z (ℓ j)).toRingHom := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp
  have := Polynomial.hom_eval₂ Q (aeval (R := ℚ) ℓ).toRingHom (aeval (R := ℚ) z).toRingHom g
  rw [hc] at this
  exact this

theorem exists_monic_coeff_zero_ne {P : Ideal (MvPolynomial σ ℚ)} (hP : P.IsPrime)
    (ℓ : Fin e → MvPolynomial σ ℚ) {f : MvPolynomial σ ℚ} (hf : f ∉ P)
    {p : Polynomial (MvPolynomial (Fin e) ℚ)} (hp : p.Monic) (hpf : p.eval₂ (aeval ℓ).toRingHom f ∈ P) :
    ∃ q : Polynomial (MvPolynomial (Fin e) ℚ),
      q.Monic ∧ q.eval₂ (aeval ℓ).toRingHom f ∈ P ∧ q.coeff 0 ≠ 0 := by
  obtain ⟨q, hpq, hdvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hdvd
  refine ⟨q, ?_, ?_, fun h => hdvd (Polynomial.X_dvd_iff.mpr h)⟩
  · rw [hpq] at hp
    exact (Polynomial.monic_X.pow _).of_mul_monic_left hp
  · rw [hpq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hpf
    exact (hP.mem_or_mem hpf).resolve_left fun h => hf (hP.mem_of_pow_mem _ h)


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_minpoly {P : Ideal (MvPolynomial σ ℚ)} (hP : P.IsPrime)
    (ℓ : Fin e → MvPolynomial σ ℚ) (hinj : ∀ q : MvPolynomial (Fin e) ℚ, aeval ℓ q ∈ P → q = 0)
    (hint : ∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
      p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P) (u : MvPolynomial σ ℚ) :
    ∃ G : Polynomial (MvPolynomial (Fin e) ℚ), G.Monic ∧ G.eval₂ (aeval ℓ).toRingHom u ∈ P ∧
      ∀ Q : Polynomial (MvPolynomial (Fin e) ℚ), Q.eval₂ (aeval ℓ).toRingHom u ∈ P → G ∣ Q := by
  let φ : MvPolynomial (Fin e) ℚ →+* MvPolynomial σ ℚ ⧸ P :=
    (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom
  let _ : Algebra (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P) := φ.toAlgebra
  have key : ∀ Q : Polynomial (MvPolynomial (Fin e) ℚ),
      Polynomial.aeval (Ideal.Quotient.mk P u) Q = Ideal.Quotient.mk P (Q.eval₂ (aeval ℓ).toRingHom u) :=
    fun Q => by rw [Polynomial.aeval_def, Polynomial.hom_eval₂]; rfl
  have hφ : Function.Injective (algebraMap (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    exact hinj q (Ideal.Quotient.eq_zero_iff_mem.mp hq)
  have : Module.IsTorsionFree (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  obtain ⟨p, hpm, hp⟩ := hint u
  have hu : IsIntegral (MvPolynomial (Fin e) ℚ) (Ideal.Quotient.mk P u) :=
    ⟨p, hpm, by rw [← Polynomial.aeval_def, key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hp⟩
  refine ⟨minpoly _ (Ideal.Quotient.mk P u), minpoly.monic hu, ?_, fun Q hQ => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← key]
    exact minpoly.aeval _ _
  · exact minpoly.isIntegrallyClosed_dvd hu (by rw [key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hQ)

theorem exists_separating [Fintype σ] (S : Finset (σ → ℂ)) (x : σ → ℂ) :
    ∃ u : MvPolynomial σ ℚ, ∀ z ∈ S, aeval z u = aeval x u → z = x := by
  classical
  let k : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let q : (σ → ℂ) → Polynomial ℂ :=
    fun z => ∑ i, Polynomial.C (z i - x i) * Polynomial.X ^ (k i : ℕ)
  have hq : ∀ z, z ≠ x → q z ≠ 0 := by
    intro z hz h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    have h1 := congrArg (fun r => _root_.AddMonoidAlgebra.coeff (M := ℕ) r (k i : ℕ)) h
    simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single i] at h1
    · rw [if_pos rfl] at h1
      exact hi (sub_eq_zero.mp h1)
    · intro j _ hj
      rw [if_neg]
      intro h'
      exact hj (k.injective (Fin.ext h'.symm))
    · simp
  let Q : Polynomial ℂ := ∏ z ∈ S.erase x, q z
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun z hz => hq z (Finset.ne_of_mem_erase hz)
  obtain ⟨c, hc⟩ : ∃ c : ℚ, Q.eval (c : ℂ) ≠ 0 := by
    by_contra h
    push Not at h
    apply Set.infinite_range_of_injective (Rat.cast_injective (α := ℂ))
    refine (Q.roots.toFinset.finite_toSet).subset ?_
    rintro _ ⟨c, rfl⟩
    simp [Polynomial.mem_roots hQ, h c]
  refine ⟨∑ i, C (c ^ (k i : ℕ)) * X i, fun z hz hzu => ?_⟩
  by_contra hzx
  have hev : aeval z (∑ i, C (c ^ (k i : ℕ)) * X i) - aeval x (∑ i, C (c ^ (k i : ℕ)) * X i) =
      (q z).eval (c : ℂ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, aeval_C, aeval_X, q, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eq_ratCast (algebraMap ℚ ℂ)]
    push_cast
    ring
  rw [hzu, sub_self] at hev
  rw [Polynomial.eval_prod] at hc
  exact Finset.prod_ne_zero_iff.mp hc z (Finset.mem_erase.mpr ⟨hzx, hz⟩) hev.symm

end FiniteSeparatingModel

theorem FiniteSeparatingModel.proof (hN : NoetherProjection.Statement)
    (hL : RootsLiftToZeros.Statement) : FiniteSeparatingModel.Statement := by
  classical
  intro σ _ P f x hP hf _
  obtain ⟨e, ℓ, hinj, hint⟩ := hN σ P hP.ne_top
  choose p hpm hp using hint
  let yx : Fin e → ℂ := fun j => aeval x (ℓ j)
  let S : Finset (σ → ℂ) := Fintype.piFinset fun i =>
    ((p (X i)).map (aeval yx).toRingHom).roots.toFinset
  have hS : ∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) → (fun j => aeval z (ℓ j)) = yx → z ∈ S := by
    intro z hz hzl
    rw [Fintype.mem_piFinset]
    intro i
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((hpm _).map _).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← hzl]
    have := hz _ (hp (X i))
    rwa [FiniteSeparatingModel.aeval_eval₂, aeval_X] at this
  obtain ⟨u, hu⟩ := FiniteSeparatingModel.exists_separating S x
  obtain ⟨G, hGm, hGu, hGdvd⟩ :=
    FiniteSeparatingModel.exists_minpoly hP ℓ hinj (fun g => ⟨p g, hpm g, hp g⟩) u
  obtain ⟨q, -, hqf, hq0⟩ :=
    FiniteSeparatingModel.exists_monic_coeff_zero_ne hP ℓ hf (hpm f) (hp f)
  refine ⟨e, ℓ, u, G, q.coeff 0, 1, hGm, hq0, one_ne_zero,
    fun i => ⟨p (X i), hpm _, fun z hz => ?_⟩, fun z hz => ?_, fun z hz hc hfz => ?_,
    fun y t _ ht => hL σ P e ℓ u G (fun g => ⟨p g, hpm g, hp g⟩) hGdvd y t ht,
    fun z hz hzl hzu => hu z (hS z hz hzl) hzu⟩
  · have := hz _ (hp (X i))
    rwa [FiniteSeparatingModel.aeval_eval₂, aeval_X] at this
  · have := hz _ hGu
    rwa [FiniteSeparatingModel.aeval_eval₂] at this
  · apply hc
    have := hz _ hqf
    rw [FiniteSeparatingModel.aeval_eval₂, hfz, Polynomial.eval₂_at_zero] at this
    exact this

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIndependentModBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial TensorProduct

noncomputable section

theorem IndependentModBaseChange.proof : IndependentModBaseChange.Statement := by
  intro σ P r g hg
  let θ : MvPolynomial σ ℂ →ₐ[ℂ] ℂ ⊗[ℤ] (MvPolynomial σ ℤ ⧸ P) :=
    (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ ℤ P)).comp
      (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ).symm.toAlgHom
  have hθ : ∀ p : MvPolynomial σ ℤ,
      θ (MvPolynomial.map (Int.castRingHom ℂ) p) = (1 : ℂ) ⊗ₜ Ideal.Quotient.mk P p := by
    intro p
    have h1 : MvPolynomial.map (Int.castRingHom ℂ) p =
        MvPolynomial.algebraTensorAlgEquiv ℤ ℂ ((1 : ℂ) ⊗ₜ p) := by
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
      congr 1
    rw [h1]
    change Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ ℤ P)
      ((MvPolynomial.algebraTensorAlgEquiv ℤ ℂ).symm (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ ((1 : ℂ) ⊗ₜ p))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have hle : ∀ a ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ)), θ a = 0 := by
    have hker : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker θ := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, hθ, Ideal.Quotient.eq_zero_iff_mem.mpr hp, tmul_zero]
    exact fun a ha => hker ha
  let ψ := Ideal.Quotient.liftₐ _ θ hle
  have key : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[ℤ] Ideal.Quotient.mk P (g i)) :=
    Module.Flat.linearIndependent_one_tmul hg
  have hfun : (ψ.toLinearMap ∘ fun i => Ideal.Quotient.mk (P.map (MvPolynomial.map (Int.castRingHom ℂ)))
      (MvPolynomial.map (Int.castRingHom ℂ) (g i))) = fun i => (1 : ℂ) ⊗ₜ[ℤ] Ideal.Quotient.mk P (g i) := by
    funext i
    exact hθ (g i)
  rw [← hfun] at key
  exact key.of_comp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedTopAlgebra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Polynomial

theorem MixedTopAlgebra.clear_den (d : ℕ) (m : ℕ → ℝ) (Q x : ℝ) (hQ : Q ≠ 0) :
    Q ^ d * ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * m i * (x / Q) ^ i =
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : Q ^ d = Q ^ (d - i) * Q ^ i := by rw [← pow_add, Nat.sub_add_cancel hid]
  rw [hpow, div_pow]
  field_simp

theorem MixedTopAlgebra.sum_ge (d : ℕ) (m : ℕ → ℝ) (hm : ∀ i, 1 ≤ i → i ≤ d → 0 ≤ m i)
    (Q x : ℝ) (hQ : 0 ≤ Q) (hx : 0 ≤ x) :
    Q * ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * Q ^ (d - 1 - i) * x ^ i * m i
        + x ^ d * m d ≤
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, Finset.mul_sum]
  simp only [Nat.cast_one, one_mul, mul_one]
  refine add_le_add (Finset.sum_le_sum fun i hi => ?_) le_rfl
  have hid : i < d := Finset.mem_range.mp hi
  have hpow : Q * Q ^ (d - 1 - i) = Q ^ (d - i) := by
    rw [← pow_succ']; congr 1; omega
  calc Q * (((d - 1).choose i : ℝ) * Q ^ (d - 1 - i) * x ^ i * m i)
      = ((d - 1).choose i : ℝ) * (Q * Q ^ (d - 1 - i)) * x ^ i * m i := by ring
    _ = ((d - 1).choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by rw [hpow]
    _ ≤ (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp
      · have hmi : 0 ≤ m i := hm i hi0 hid.le
        have hc : ((d - 1).choose i : ℝ) ≤ (d.choose i : ℝ) := by
          exact_mod_cast Nat.choose_le_choose i (Nat.sub_le d 1)
        gcongr

theorem MixedTopAlgebra.proof (hP : PolyNonnegAtZero.Statement) : MixedTopAlgebra.Statement := by
  intro d m hd hm hmd hST
  set P : Polynomial ℝ := ∑ i ∈ Finset.range (d + 1), C ((d.choose i : ℝ) * m i) * X ^ i with hPdef
  have heval : ∀ t : ℝ, P.eval t = ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * m i * t ^ i := by
    intro t; simp [P, eval_finsetSum]
  have h0 : P.eval 0 = m 0 := by
    rw [heval, Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp [zero_pow hi]
    · intro h; simp at h
  rw [← h0]
  refine hP d P (m d) hmd ?_ ?_
  · intro t ht hPt
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = t.num :=
      ⟨t.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.mpr ht.le)⟩
    have hp1 : 1 ≤ p := by
      have : 0 < t.num := Rat.num_pos.mpr ht
      omega
    have hq0 : (0 : ℝ) < (t.den : ℝ) := by exact_mod_cast t.den_pos
    have htq : (t : ℝ) = (p : ℝ) / (t.den : ℝ) := by
      rw [Rat.cast_def, ← hp]; push_cast; rfl
    have hS := MixedTopAlgebra.clear_den d m (t.den : ℝ) (p : ℝ) hq0.ne'
    rw [← htq, ← heval] at hS
    have hSpos : 0 < ∑ i ∈ Finset.range (d + 1),
        (d.choose i : ℝ) * (t.den : ℝ) ^ (d - i) * (p : ℝ) ^ i * m i := by
      rw [← hS]; positivity
    have hT := hST t.den p t.den_pos hp1 hSpos
    have hge := MixedTopAlgebra.sum_ge d m hm (t.den : ℝ) (p : ℝ) hq0.le (by positivity)
    have hqd : (0 : ℝ) < (t.den : ℝ) ^ d := by positivity
    have hmt : (t.den : ℝ) ^ d * (m d * (t : ℝ) ^ d) = (p : ℝ) ^ d * m d := by
      rw [htq, div_pow]; field_simp
    refine le_of_mul_le_mul_left ?_ hqd
    rw [hmt, hS]
    nlinarith [mul_nonneg hq0.le hT]
  · have hlow : ∀ t : ℝ, 0 ≤ t → m 0 + m d * t ^ d ≤ P.eval t := by
      intro t ht
      have hsub : ({0, d} : Finset ℕ) ⊆ Finset.range (d + 1) := by
        intro i hi; simp at hi; simp; omega
      rw [heval]
      calc m 0 + m d * t ^ d = ∑ i ∈ ({0, d} : Finset ℕ), (d.choose i : ℝ) * m i * t ^ i := by
            rw [Finset.sum_pair (by omega)]; simp
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi hi' => by
            have h1 : 1 ≤ i := by simp at hi'; omega
            have := hm i h1 (by simp at hi; omega)
            positivity
    filter_upwards [eventually_ge_atTop (max 1 ((|m 0| + 1) / m d))] with t ht
    have ht1 : 1 ≤ t := le_of_max_le_left ht
    have ht2 : (|m 0| + 1) / m d ≤ t := le_of_max_le_right ht
    have htd : t ≤ t ^ d := by
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ d := pow_le_pow_right₀ ht1 (by omega)
    have h3 : |m 0| + 1 ≤ m d * t := by rw [div_le_iff₀ hmd] at ht2; linarith
    have h4 : m d * t ≤ m d * t ^ d := mul_le_mul_of_nonneg_left htd hmd.le
    have h5 := hlow t (by linarith)
    linarith [neg_abs_le (m 0)]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNoetherProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem NoetherProjection.proof : NoetherProjection.Statement := by
  intro σ _ P hP
  have : Nontrivial (MvPolynomial σ ℚ ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (MvPolynomial σ ℚ ⧸ P)
  choose ℓ hℓ using fun j => Ideal.Quotient.mk_surjective (g (X j))
  have hcomp : (Ideal.Quotient.mkₐ ℚ P).comp (aeval ℓ) = g := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [hℓ]
  have hcompR : (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom = g.toRingHom := by
    rw [← hcomp]
    rfl
  refine ⟨s, ℓ, ?_, ?_⟩
  · intro q hq
    apply hinj
    rw [map_zero, ← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hq]
  · intro f
    obtain ⟨p, hpm, hp⟩ := hint (Ideal.Quotient.mk P f)
    refine ⟨p, hpm, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂, hcompR]
    exact hp

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonvanishDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem PolyNonvanishDense.proof : PolyNonvanishDense.Statement := by
  intro e D hD
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  have hzero : map (algebraMap ℚ ℂ) D = 0 := by
    refine funext_set (fun j => Metric.ball (y₀ j) ε)
      (fun j => infinite_of_mem_nhds (y₀ j) (Metric.ball_mem_nhds _ hε)) fun y hy => ?_
    rw [← ball_pi y₀ hε] at hy
    have hyU := hball hy
    rw [map_zero, eval_map, ← aeval_def]
    by_contra hyD
    exact (Set.eq_empty_iff_forall_notMem.mp hne) y ⟨hyU, hyD⟩
  exact hD (map_injective _ (algebraMap ℚ ℂ).injective (by rw [hzero, map_zero]))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

