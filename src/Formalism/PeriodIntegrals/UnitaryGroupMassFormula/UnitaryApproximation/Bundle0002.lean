module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.WeakApproxF

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.ApproxE
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_span_int : ∃ (d : ℕ) (b : Fin d → E), (∀ k, b k ∈ PI.UnitaryApproxDefs.intOE E) ∧
    ∀ e : E, ∃ f : Fin d → F, e = ∑ k, f k • b k := by
  let B := (NumberField.integralBasis E).reindex (Fintype.equivFin _)
  refine ⟨_, fun k => B k, fun k => ?_, fun e => ?_⟩
  · show B k ∈ (algebraMap (𝓞 E) E).range
    refine ⟨RingOfIntegers.basis E ((Fintype.equivFin _).symm k), ?_⟩
    simp only [B, Module.Basis.reindex_apply, NumberField.integralBasis_apply]
  · refine ⟨fun k => ((B.repr e k : ℚ) : F), ?_⟩
    conv_lhs => rw [← B.sum_repr e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_ratCast, eq_ratCast]

theorem tensor_decomp {d : ℕ} (b : Fin d → E) (hb : ∀ e : E, ∃ f : Fin d → F, e = ∑ k, f k • b k)
    {R : Type} [CommRing R] [Algebra F R] (x : E ⊗[F] R) :
    ∃ c : Fin d → R, x = ∑ k, b k ⊗ₜ[F] c k := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul e r =>
    obtain ⟨f, hf⟩ := hb e
    refine ⟨fun k => f k • r, ?_⟩
    rw [hf, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨c1, h1⟩ := hx
    obtain ⟨c2, h2⟩ := hy
    refine ⟨c1 + c2, ?_⟩
    simp [h1, h2, TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem approxEStep : ApproxEStep := by
  intro hW
  unfold ApproxE
  intro F E _ _ _ _ _ T x D hD
  obtain ⟨d, b, hbint, hb⟩ := exists_span_int (F := F) (E := E)
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : Fin d → v.adicCompletion F,
      x v = ∑ k, b k ⊗ₜ[F] c k := fun v => tensor_decomp b hb (x v)
  choose c hc using hc
  have ha : ∀ k, ∃ a : F, ∀ v ∈ T, ∃ t ∈ v.adicCompletionIntegers F,
      c v k - algebraMap F (v.adicCompletion F) a = algebraMap F (v.adicCompletion F) (D : F) * t :=
    fun k => hW F T (fun v => c v k) D hD
  choose a ht using ha
  refine ⟨∑ k, a k • b k, fun v hv => ?_⟩
  choose t htO hteq using fun k => ht k v hv
  refine ⟨∑ k, (1 : E) ⊗ₜ[F] t k * PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (b k), ?_, ?_⟩
  · exact Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (one_tmul_mem_Sv v (htO k)) (inclE_mem_Sv v (hbint k))
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hc v, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [PI.UnitaryApproxDefs.inclE, dv, Algebra.TensorProduct.includeLeftRingHom_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [TensorProduct.smul_tmul, ← TensorProduct.tmul_sub, Algebra.smul_def (a k), mul_one, hteq k,
        ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]

end PI.UnitaryApproxFinWork

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.BoundedRationalUnitary
section
noncomputable section

open TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace PI.UnitaryApproxFinWork

theorem bd_int_mult {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ N : ℤ, N ≠ 0 ∧ IsIntegral ℤ ((N : K) * e) := by
  have halg : IsAlgebraic ℤ e :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  exact ⟨y, hy0, by rwa [zsmul_eq_mul] at hyint⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bd_local (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) :
    ∃ N : ℤ, N ≠ 0 ∧ Valued.v ((N : v.adicCompletion F) * a) ≤ 1 := by
  obtain ⟨b, hb, hab⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨(Ideal.absNorm (Ideal.span {b}) : ℤ), ?_, ?_⟩
  · have h0 : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hb0
    exact_mod_cast h0
  · have hab' : a * algebraMap F (v.adicCompletion F) (b : F) ∈ v.adicCompletionIntegers F := by
      first
      | exact hab
      | (convert hab using 2)
      | simpa using hab
    have hc' : algebraMap F (v.adicCompletion F) (c : F) ∈ v.adicCompletionIntegers F := by
      first
      | exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v c
      | (convert IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v c using 1)
      | simpa using IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v c
    have hcast : algebraMap F (v.adicCompletion F) (c : F) * algebraMap F (v.adicCompletion F) (b : F) =
        ((Ideal.absNorm (Ideal.span {b}) : ℤ) : v.adicCompletion F) := by
      rw [← map_mul, show (c : F) * (b : F) = ((c * b : 𝓞 F) : F) from rfl, hc]
      simp
    rw [← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← hcast]
    have e : algebraMap F (v.adicCompletion F) (c : F) * algebraMap F (v.adicCompletion F) (b : F) * a =
        algebraMap F (v.adicCompletion F) (c : F) * (a * algebraMap F (v.adicCompletion F) (b : F)) := by
      ring
    rw [e]
    exact mul_mem hc' hab'

theorem bd_main (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : E ⊗[F] v.adicCompletion F) * x ∈ Sv E v := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | tmul e t =>
    obtain ⟨N₁, hN₁, h₁⟩ := bd_int_mult e
    obtain ⟨N₂, hN₂, h₂⟩ := bd_local v t
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, ?_⟩
    have hL : ((N₁ : ℤ) : E ⊗[F] v.adicCompletion F) = (N₁ : E) ⊗ₜ[F] (1 : v.adicCompletion F) := by
      rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_intCast]
    have hR : ((N₂ : ℤ) : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] (N₂ : v.adicCompletion F) := by
      rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]
    have e1 : ((N₁ * N₂ : ℤ) : E ⊗[F] v.adicCompletion F) * (e ⊗ₜ[F] t) =
        ((N₁ : E) * e) ⊗ₜ[F] (1 : v.adicCompletion F) *
          ((1 : E) ⊗ₜ[F] ((N₂ : v.adicCompletion F) * t)) := by
      rw [Int.cast_mul, hL, hR]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e1]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨⟨(N₁ : E) * e,
      RingHom.mem_range.2 ⟨⟨_, h₁⟩, rfl⟩⟩, rfl⟩))
      (Subring.subset_closure (Set.mem_union_right _ ⟨⟨(N₂ : v.adicCompletion F) * t, ?_⟩, rfl⟩))
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 h₂
  | add x y hx hy =>
    obtain ⟨N₁, hN₁, h₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, ?_⟩
    have e2 : ((N₁ * N₂ : ℤ) : E ⊗[F] v.adicCompletion F) * (x + y) =
        (N₂ : E ⊗[F] v.adicCompletion F) * ((N₁ : E ⊗[F] v.adicCompletion F) * x) +
          (N₁ : E ⊗[F] v.adicCompletion F) * ((N₂ : E ⊗[F] v.adicCompletion F) * y) := by
      push_cast
      ring
    rw [e2]
    exact Subring.add_mem _ (Subring.mul_mem _ (intCast_mem _ N₂) h₁)
      (Subring.mul_mem _ (intCast_mem _ N₁) h₂)

theorem bounded_rational_unitary : BddR := by
  intro F E _ _ _ _ _ v x
  obtain ⟨N, hN, h⟩ := bd_main v x
  refine ⟨(N : 𝓞 F), by exact_mod_cast hN, ?_⟩
  have e : dv E v (N : 𝓞 F) = (N : E ⊗[F] v.adicCompletion F) := by
    unfold dv
    simp [PI.UnitaryApproxDefs.inclE]
  rw [e]
  exact h

end PI.UnitaryApproxFinWork

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Cayley
section
noncomputable section

open Matrix

namespace PI.UnitaryApproxFinWork

variable {n : Type} [Fintype n] [DecidableEq n] {A : Type} [CommRing A] (ρ : A →+* A)

theorem cT_add (M N : Matrix n n A) : PI.UnitaryApproxDefs.cT ρ (M + N) = PI.UnitaryApproxDefs.cT ρ M + PI.UnitaryApproxDefs.cT ρ N := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT]

theorem cT_sub (M N : Matrix n n A) : PI.UnitaryApproxDefs.cT ρ (M - N) = PI.UnitaryApproxDefs.cT ρ M - PI.UnitaryApproxDefs.cT ρ N := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT]

theorem cayley_unitary (J X : Matrix n n A) (hX : PI.UnitaryApproxDefs.cT ρ X * J + J * X = 0)
    (hQ : IsUnit (1 + X).det) :
    PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹) * J * ((1 - X) * (1 + X)⁻¹) = J := by
  have hXJ : PI.UnitaryApproxDefs.cT ρ X * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have hcP : PI.UnitaryApproxDefs.cT ρ (1 - X) * J = J * (1 + X) := by
    rw [cT_sub ρ, PI.UnitaryApproxDefs.cT_one, sub_mul, one_mul, hXJ, sub_neg_eq_add, mul_add, mul_one]
  have hcQ : PI.UnitaryApproxDefs.cT ρ (1 + X) * J = J * (1 - X) := by
    rw [cT_add ρ, PI.UnitaryApproxDefs.cT_one, add_mul, one_mul, hXJ, mul_sub, mul_one, sub_eq_add_neg]
  have hinvQ : PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + X) = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.mul_nonsing_inv _ hQ, PI.UnitaryApproxDefs.cT_one]
  have hcomm : (1 + X) * (1 - X) = (1 - X) * (1 + X) := by noncomm_ring
  rw [PI.UnitaryApproxDefs.cT_mul]
  calc PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 - X) * J * ((1 - X) * (1 + X)⁻¹)
      = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * (PI.UnitaryApproxDefs.cT ρ (1 - X) * J) * (1 - X) * (1 + X)⁻¹ := by simp only [mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * J * ((1 + X) * (1 - X)) * (1 + X)⁻¹ := by rw [hcP]; simp only [mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * J * (1 - X) * ((1 + X) * (1 + X)⁻¹) := by rw [hcomm]; simp only [mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * (J * (1 - X)) := by rw [Matrix.mul_nonsing_inv _ hQ, mul_one, mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * (PI.UnitaryApproxDefs.cT ρ (1 + X) * J) := by rw [hcQ]
    _ = J := by rw [← mul_assoc, hinvQ, one_mul]

theorem cayley_mem_UJ (J X : Matrix n n A) (hJd : IsUnit J.det) (hX : PI.UnitaryApproxDefs.cT ρ X * J + J * X = 0)
    (hQ : IsUnit (1 + X).det) :
    ∃ γ ∈ PI.UnitaryApproxDefs.UJ ρ J, (γ : Matrix n n A) = (1 - X) * (1 + X)⁻¹ := by
  have hU := cayley_unitary ρ J X hX hQ
  have hdet := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have h2 : J.det * ((PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹)).det * ((1 - X) * (1 + X)⁻¹).det) = J.det * 1 := by
    rw [mul_one]
    calc J.det * ((PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹)).det * ((1 - X) * (1 + X)⁻¹).det)
        = (PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹)).det * J.det * ((1 - X) * (1 + X)⁻¹).det := by ring
      _ = J.det := hdet
  have h3 := hJd.mul_left_cancel h2
  have hu : IsUnit ((1 - X) * (1 + X)⁻¹).det := isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact h3⟩
  exact ⟨Matrix.nonsingInvUnit _ hu, hU, rfl⟩

theorem lie_of_unitary (J g : Matrix n n A) (hg : PI.UnitaryApproxDefs.cT ρ g * J * g = J) (hP : IsUnit (1 + g).det) :
    PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹) = 0 := by
  have hL : PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + g) = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.mul_nonsing_inv _ hP, PI.UnitaryApproxDefs.cT_one]
  have hLinv : PI.UnitaryApproxDefs.cT ρ (1 + g) * PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.nonsing_inv_mul _ hP, PI.UnitaryApproxDefs.cT_one]
  have hR : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
  have e1 : (1 - PI.UnitaryApproxDefs.cT ρ g) * J * (1 + g) + (1 + PI.UnitaryApproxDefs.cT ρ g) * J * (1 - g) =
      J + J - (PI.UnitaryApproxDefs.cT ρ g * J * g + PI.UnitaryApproxDefs.cT ρ g * J * g) := by noncomm_ring
  have key : PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) * (1 + g) = 0 := by
    rw [PI.UnitaryApproxDefs.cT_mul]
    calc PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 - g) * J + J * ((1 - g) * (1 + g)⁻¹)) * (1 + g)
        = (PI.UnitaryApproxDefs.cT ρ (1 + g) * PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹) * PI.UnitaryApproxDefs.cT ρ (1 - g) * J * (1 + g) +
            PI.UnitaryApproxDefs.cT ρ (1 + g) * J * (1 - g) * ((1 + g)⁻¹ * (1 + g)) := by
          simp only [mul_add, add_mul, mul_assoc]
          abel
      _ = PI.UnitaryApproxDefs.cT ρ (1 - g) * J * (1 + g) + PI.UnitaryApproxDefs.cT ρ (1 + g) * J * (1 - g) := by
          rw [hLinv, Matrix.nonsing_inv_mul _ hP, one_mul, mul_one]
      _ = 0 := by
          rw [cT_sub ρ, cT_add ρ, PI.UnitaryApproxDefs.cT_one, e1, hg, sub_self]
  calc PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)
      = PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) *
          ((1 + g) * (1 + g)⁻¹) := by rw [hL, hR, one_mul, mul_one]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * (PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) *
          (1 + g)) * (1 + g)⁻¹ := by simp only [mul_assoc]
    _ = 0 := by rw [key, mul_zero, zero_mul]

end PI.UnitaryApproxFinWork

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.SigmaMemIntOE
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : Type} [Fintype n] [DecidableEq n]

def MS (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
    (M : Matrix n n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i j, M i j ∈ Sv E v

def MC (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F)
    (M : Matrix n n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∃ A, MS E v A ∧ M = dv E v d • A

variable {v : HeightOneSpectrum (𝓞 F)}

theorem MS_mul {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)

theorem MS_add {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M + N) := fun i j => Subring.add_mem _ (hM i j) (hN i j)

theorem MS_sub {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M - N) := fun i j => Subring.sub_mem _ (hM i j) (hN i j)

theorem MS_one : MS E v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem MS_smul {a : E ⊗[F] v.adicCompletion F} (ha : a ∈ Sv E v)
    {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : MS E v (a • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ ha (hM i j)

def toS {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : Matrix n n (Sv E v) :=
  fun i j => ⟨M i j, hM i j⟩

theorem map_toS {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    (Sv E v).subtype.mapMatrix (toS hM) = M := by
  ext i j
  rfl

theorem MS_adjugate {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    MS E v M.adjugate := by
  intro i j
  rw [← map_toS hM, ← RingHom.map_adjugate]
  exact ((toS hM).adjugate i j).2

private lemma dv_mem_Sv' (d : 𝓞 F) : dv E v d ∈ Sv E v := by
  apply Subring.subset_closure
  left
  exact ⟨⟨algebraMap F E (d : F),
    ⟨⟨algebraMap F E (d : F), (RingOfIntegers.isIntegral_coe d).algebraMap⟩, rfl⟩⟩, rfl⟩

theorem det_one_add (π : 𝓞 F) {A : Matrix n n (E ⊗[F] v.adicCompletion F)} (hA : MS E v A) :
    ∃ s ∈ Sv E v, (1 + dv E v π • A).det = 1 + dv E v π * s := by
  let p : Sv E v := ⟨dv E v π, dv_mem_Sv' π⟩
  let B := toS hA
  let I : Ideal (Sv E v) := Ideal.span {p}
  have hp0 : Ideal.Quotient.mk I p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have h0 : (Ideal.Quotient.mk I).mapMatrix (p • B) = 0 := by
    ext i j
    simp [hp0]
  have hmap : (Ideal.Quotient.mk I).mapMatrix (1 + p • B) = 1 := by
    rw [map_add (f := _), map_one, h0, add_zero]
  have hdet : Ideal.Quotient.mk I ((1 + p • B).det - 1) = 0 := by
    rw [map_sub, RingHom.map_det, hmap, Matrix.det_one, map_one, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdet)
  refine ⟨(t : E ⊗[F] v.adicCompletion F), t.2, ?_⟩
  have h2 : (Sv E v).subtype.mapMatrix (1 + p • B) = 1 + dv E v π • A := by
    rw [map_add (f := _), map_one]
    congr 1
  have h4 : (1 + p • B).det = 1 + p * t := by
    rw [mul_comm, ht]
    ring
  rw [← h2, ← RingHom.map_det, h4]
  simp [p]

theorem MC_entries {d : 𝓞 F} {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (h : MC E v d M) (i j : n) :
    Cong E v d (M i j) := by
  obtain ⟨A, hA, rfl⟩ := h
  exact ⟨A i j, hA i j, by rw [Matrix.smul_apply, smul_eq_mul]⟩

theorem MC_of_entries {d : 𝓞 F} {M : Matrix n n (E ⊗[F] v.adicCompletion F)}
    (h : ∀ i j, Cong E v d (M i j)) : MC E v d M := by
  choose t ht heq using h
  refine ⟨Matrix.of fun i j => t i j, fun i j => ht i j, ?_⟩
  ext i j
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact heq i j

theorem MC_cancel {c e : 𝓞 F} (hc : c ≠ 0) {M A : Matrix n n (E ⊗[F] v.adicCompletion F)}
    (h : dv E v c • M = dv E v (c * e) • A) : M = dv E v e • A := by
  have hx : algebraMap F E (c : F) ≠ 0 := by simpa using hc
  have hu : IsUnit (dv E v c) :=
    (IsUnit.mk0 _ hx).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))
  have hmul : dv E v (c * e) = dv E v c * dv E v e := by simp [dv]
  rw [hmul, mul_smul] at h
  exact hu.smul_left_cancel.1 h

theorem sigma_mem_intOE (σ : E →ₐ[F] E) {x : E} (hx : x ∈ PI.UnitaryApproxDefs.intOE E) : σ x ∈ PI.UnitaryApproxDefs.intOE E := by
  simp only [PI.UnitaryApproxDefs.intOE, RingHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨σ y, (RingOfIntegers.isIntegral_coe y).map σ.toRingHom.toIntAlgHom⟩, rfl⟩

theorem sigR_mem_Sv (σ : E →ₐ[F] E) {s : E ⊗[F] v.adicCompletion F} (hs : s ∈ Sv E v) :
    PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) s ∈ Sv E v := by
  have h : Sv E v ≤ (Sv E v).comap (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · simp only [Subring.coe_comap, Set.mem_preimage]
      apply Subring.subset_closure
      left
      exact ⟨⟨σ x, sigma_mem_intOE σ hx⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩
    · simp only [Subring.coe_comap, Set.mem_preimage]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩
  exact h hs

theorem MS_cT (σ : E →ₐ[F] E) {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    MS E v (PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) M) := fun i j => sigR_mem_Sv σ (hM j i)

theorem sigR_dv (σ : E →ₐ[F] E) (d : 𝓞 F) : PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (dv E v d) = dv E v d := by
  simp [PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE, dv]

theorem cT_map (σ : E →ₐ[F] E) (M : Matrix n n E) :
    PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (M.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) =
      (PI.UnitaryApproxDefs.cT (σ : E →+* E) M).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT, PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]

end PI.UnitaryApproxFinWork

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.TopStep
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

theorem topStep : TopStep := by
  unfold TopStep CayleyFin EigAvoid PI.UnitaryApproxFin.UnitaryApproxFin
  intro hC hE F E iF iNF iE iNE iA n iFt iDe σ J hσ hθ hJ hdet T g hg D hD
  obtain ⟨μ, hμ, hinv⟩ := hE F E n σ hσ hθ T (fun v => ((g v : GL n _) : Matrix n n _))
  have hμ' : μ * σ μ = 1 := by rw [mul_comm]; exact hμ
  have hab : ∀ v : HeightOneSpectrum (𝓞 F),
      PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) = 1 := fun v => by
    rw [← map_mul, hμ', map_one]
  have hρ : ∀ v : HeightOneSpectrum (𝓞 F),
      PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)
          (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ) *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := fun v => by
    rw [sigR_inclE, ← map_mul, hμ, map_one]
  obtain ⟨c, hc0, hc⟩ := exists_int_mul (F := F) (σ μ)
  obtain ⟨γ', hγ', hcong⟩ := hC F E n σ J hσ hJ hdet T
    (fun v => scU (n := n) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ)
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ)) (hab v) * g v)
    (fun v hv => Subgroup.mul_mem _
      (scU_mem_UJ (n := n) (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F))
        (J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) _ _ _ (hρ v)) (hg v hv))
    (fun v hv => by
      simp only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul]
      exact hinv v hv)
    (D * c) (mul_ne_zero hD hc0)
  refine ⟨scU (n := n) (σ μ) μ hμ * γ',
    Subgroup.mul_mem _ (scU_mem_UJ (n := n) (σ : E →+* E) J (σ μ) μ hμ ?_) hγ', ?_⟩
  · show σ (σ μ) * σ μ = 1
    rw [hσ, hμ']
  · intro v hv i j
    obtain ⟨s, hs, hseq⟩ := hcong v hv i j
    refine ⟨PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F) * σ μ) * s,
      Subring.mul_mem _ (inclE_mem_Sv v hc) hs, ?_⟩
    have hdv : dv E v (D * c) =
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) *
          PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) :=
      dv_mul v D c
    have hba : PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := by
      rw [← map_mul, hμ, map_one]
    simp only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      smul_eq_mul] at hseq ⊢
    rw [hdv] at hseq
    simp only [map_mul]
    linear_combination PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) * hseq -
      ((g v : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j * hba

end PI.UnitaryApproxFinWork

end
end

