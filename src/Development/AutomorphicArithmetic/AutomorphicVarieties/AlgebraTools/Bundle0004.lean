module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IdemLiftComplete
section
open Polynomial Matrix IsLocalRing TensorProduct

namespace UpperTheory.V.AlgebraTools

private noncomputable def ilcP (B : Type) [CommRing B] : ℕ → B[X]
  | 0 => X
  | k + 1 => 3 * ilcP B k ^ 2 - 2 * ilcP B k ^ 3

end UpperTheory.V.AlgebraTools

open UpperTheory.V.AlgebraTools in
theorem UpperTheory.V.AlgebraTools.idem_lift_complete :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (I : Ideal B) [IsAdicComplete I E] (z : E) (M : ℕ), (z * z - z) ^ M ∈ I • (⊤ : Submodule B E) → ∃ e : E, IsIdempotentElem e ∧ ∀ N : ℕ, ∃ q : B[X], e - (z + (z * z - z) * aeval z q) ∈ I ^ N • (⊤ : Submodule B E) := by
  intro B E _ _ _ I _ z M hM
  set S : ℕ → Submodule B E := fun n => I ^ n • (⊤ : Submodule B E) with hS
  have L2r : ∀ n (x y : E), x ∈ I ^ n • (⊤ : Submodule B E) →
      x * y ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n x y hx
    refine Submodule.smul_induction_on (p := fun x => x * y ∈ I ^ n • (⊤ : Submodule B E)) hx
      (fun a ha m _ => ?_) (fun x1 x2 h1 h2 => ?_)
    · rw [smul_mul_assoc]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [add_mul]
      exact add_mem h1 h2
  have L2l : ∀ n (x y : E), x ∈ I ^ n • (⊤ : Submodule B E) →
      y * x ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n x y hx
    refine Submodule.smul_induction_on (p := fun x => y * x ∈ I ^ n • (⊤ : Submodule B E)) hx
      (fun a ha m _ => ?_) (fun x1 x2 h1 h2 => ?_)
    · rw [mul_smul_comm]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [mul_add]
      exact add_mem h1 h2
  have L3 : ∀ n (x w : E), x ∈ I • (⊤ : Submodule B E) → w ∈ I ^ n • (⊤ : Submodule B E) →
      x * w ∈ I ^ (n + 1) • (⊤ : Submodule B E) := by
    intro n x w hx hw
    refine Submodule.smul_induction_on
      (p := fun x => x * w ∈ I ^ (n + 1) • (⊤ : Submodule B E)) hx
      (fun a ha m _ => ?_) (fun x1 x2 h1 h2 => ?_)
    · rw [smul_mul_assoc]
      have h := Submodule.smul_mem_smul ha (L2l n w m hw)
      rwa [← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ'] at h
    · rw [add_mul]
      exact add_mem h1 h2
  have Lpow : ∀ n (x : E), x ∈ I • (⊤ : Submodule B E) → x ^ n ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n x hx
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    | succ n ih =>
      rw [pow_succ' x n]
      exact L3 n x _ hx ih
  have Mem : ∀ n k, M * n ≤ 2 ^ k → ∀ y : E,
      (z * z - z) ^ (2 ^ k) * y ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n k hk y
    have h : (z * z - z) ^ (2 ^ k) = ((z * z - z) ^ M) ^ n * (z * z - z) ^ (2 ^ k - M * n) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk]
    rw [h, mul_assoc]
    exact L2r _ _ _ (Lpow n _ hM)
  have hk2 : ∀ k : ℕ, k ≤ 2 ^ k := fun k => (Nat.lt_two_pow_self).le
  have PoincareLelongAlt : ∀ k, ∃ Q : B[X], ilcP B k = X + (X * X - X) * Q := by
    intro k
    induction k with
    | zero => exact ⟨0, by rw [ilcP]; ring⟩
    | succ k ih =>
      obtain ⟨Q, hQ⟩ := ih
      refine ⟨Q - (1 + 2 * X * Q + (X * X - X) * Q ^ 2 - Q) * (2 * (X + (X * X - X) * Q) - 1), ?_⟩
      rw [ilcP, hQ]
      ring
  have ProjectiveLineTwo : ∀ k, ∃ W : B[X], ilcP B k * ilcP B k - ilcP B k = (X * X - X) ^ (2 ^ k) * W := by
    intro k
    induction k with
    | zero => exact ⟨1, by rw [ilcP]; ring⟩
    | succ k ih =>
      obtain ⟨W, hW⟩ := ih
      have hid : ∀ P : B[X], (3 * P ^ 2 - 2 * P ^ 3) * (3 * P ^ 2 - 2 * P ^ 3) -
          (3 * P ^ 2 - 2 * P ^ 3) = (P * P - P) ^ 2 * (4 * (P * P - P) - 3) := fun P => by ring
      refine ⟨W ^ 2 * (4 * (X * X - X) ^ (2 ^ k) * W - 3), ?_⟩
      rw [ilcP, hid, hW, pow_succ 2 k, pow_mul]
      ring
  have PL3 : ∀ k, ∃ V : B[X], ilcP B (k + 1) - ilcP B k = (X * X - X) ^ (2 ^ k) * V := by
    intro k
    obtain ⟨W, hW⟩ := ProjectiveLineTwo k
    refine ⟨-(W * (2 * ilcP B k - 1)), ?_⟩
    rw [ilcP]
    linear_combination (-(2 * ilcP B k - 1)) * hW
  have PL4 : ∀ k j, ∃ V : B[X], ilcP B (k + j) - ilcP B k = (X * X - X) ^ (2 ^ k) * V := by
    intro k j
    induction j with
    | zero => exact ⟨0, by simp⟩
    | succ j ih =>
      obtain ⟨V0, hV0⟩ := ih
      obtain ⟨V1, hV1⟩ := PL3 (k + j)
      have hpow : (X * X - X : B[X]) ^ (2 ^ (k + j)) =
          (X * X - X) ^ (2 ^ k) * (X * X - X) ^ (2 ^ (k + j) - 2 ^ k) := by
        rw [← pow_add, Nat.add_sub_cancel' (Nat.pow_le_pow_right (by norm_num) (by omega))]
      refine ⟨(X * X - X) ^ (2 ^ (k + j) - 2 ^ k) * V1 + V0, ?_⟩
      rw [show k + (j + 1) = k + j + 1 by omega]
      linear_combination hV1 + hV0 + V1 * hpow
  have hD : aeval z (X * X - X : B[X]) = z * z - z := by simp
  let f : ℕ → E := fun n => aeval z (ilcP B (M * n))
  have hdiff : ∀ k j, ∃ V : B[X], aeval z (ilcP B (k + j)) - aeval z (ilcP B k) =
      (z * z - z) ^ (2 ^ k) * aeval z V := by
    intro k j
    obtain ⟨V, hV⟩ := PL4 k j
    refine ⟨V, ?_⟩
    have h := congrArg (aeval z) hV
    rwa [map_sub, map_mul, map_pow, hD] at h
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (I ^ m • (⊤ : Submodule B E))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    obtain ⟨V, hV⟩ := hdiff (M * m) (M * n - M * m)
    rw [Nat.add_sub_cancel' (Nat.mul_le_mul_left M hmn)] at hV
    have h : f m - f n = -((z * z - z) ^ (2 ^ (M * m)) * aeval z V) := by
      rw [← hV]
      simp only [f]
      abel
    rw [h]
    exact neg_mem (Mem m (M * m) (hk2 _) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I E) hcauchy
  have hd : ∀ n, L - f n ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n
    have h := (SModEq.sub_mem).mp (hL n)
    rw [← neg_sub]
    exact neg_mem h
  have hsq : ∀ n, f n * f n - f n ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n
    obtain ⟨W, hW⟩ := ProjectiveLineTwo (M * n)
    have h := congrArg (aeval z) hW
    rw [map_sub, map_mul, map_mul, map_pow, hD] at h
    simp only [f]
    rw [h]
    exact Mem n (M * n) (hk2 _) _
  have hidem : IsIdempotentElem L := by
    have h0 : L * L - L = 0 := by
      apply IsHausdorff.haus (inferInstance : IsHausdorff I E)
      intro n
      rw [SModEq.sub_mem, sub_zero]
      have e1 : L * L - L = (f n * f n - f n) + (f n * (L - f n) + (L - f n) * f n +
          (L - f n) * (L - f n) - (L - f n)) := by noncomm_ring
      rw [e1]
      have hdn := hd n
      exact add_mem (hsq n) (sub_mem (add_mem (add_mem (L2l _ _ _ hdn) (L2r _ _ _ hdn))
        (L2r _ _ _ hdn)) hdn)
    exact sub_eq_zero.mp h0
  refine ⟨L, hidem, fun N => ?_⟩
  obtain ⟨Q, hQ⟩ := PoincareLelongAlt (M * N)
  refine ⟨Q, ?_⟩
  have h : f N = z + (z * z - z) * aeval z Q := by
    simp only [f]
    rw [hQ, map_add (f := _), map_mul, hD, aeval_X]
  rw [← h]
  exact hd N
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IntertwinerIso
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.intertwiner_iso :
    ∀ {F Γ : Type} [Field F] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (ρ : Γ → Matrix m m F) (ρ' : Γ → Matrix n n F), Submodule.span F (Set.range ρ) = ⊤ → Submodule.span F (Set.range ρ') = ⊤ → (∀ V : Matrix m n F, (∀ g, ρ g * V = V * ρ' g) → V ≠ 0 → ∃ V' : Matrix n m F, V * V' = 1 ∧ V' * V = 1) ∧ ∀ V : Matrix m m F, (∀ g, ρ g * V = V * ρ g) → ∃ c : F, V = c • (1 : Matrix m m F) := by
  intro F Γ _ m n _ _ _ _ ρ ρ' hρ hρ'
  refine ⟨fun V hV hV0 => ?_, fun V hV => ?_⟩
  · have hR : ∀ A : Matrix m m F, ∃ C : Matrix n n F, A * V = V * C := by
      intro A
      have hA : A ∈ Submodule.span F (Set.range ρ) := by rw [hρ]; exact Submodule.mem_top
      induction hA using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨ρ' g, hV g⟩
      | zero => exact ⟨0, by rw [Matrix.zero_mul, Matrix.mul_zero]⟩
      | add x y _ _ hx hy =>
        obtain ⟨C, hC⟩ := hx
        obtain ⟨D, hD⟩ := hy
        exact ⟨C + D, by rw [Matrix.add_mul, Matrix.mul_add, hC, hD]⟩
      | smul a x _ hx =>
        obtain ⟨C, hC⟩ := hx
        exact ⟨a • C, by rw [Matrix.smul_mul, hC, Matrix.mul_smul]⟩
    have hL : ∀ B : Matrix n n F, ∃ A : Matrix m m F, V * B = A * V := by
      intro B
      have hB : B ∈ Submodule.span F (Set.range ρ') := by rw [hρ']; exact Submodule.mem_top
      induction hB using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨ρ g, (hV g).symm⟩
      | zero => exact ⟨0, by rw [Matrix.zero_mul, Matrix.mul_zero]⟩
      | add x y _ _ hx hy =>
        obtain ⟨C, hC⟩ := hx
        obtain ⟨D, hD⟩ := hy
        exact ⟨C + D, by rw [Matrix.add_mul, Matrix.mul_add, hC, hD]⟩
      | smul a x _ hx =>
        obtain ⟨C, hC⟩ := hx
        exact ⟨a • C, by rw [Matrix.smul_mul, ← hC, Matrix.mul_smul]⟩
    have inj : Function.Injective (Matrix.toLin' V) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      rw [Matrix.toLin'_apply] at hx
      by_contra hne
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have hj' : x j ≠ 0 := by simpa using hj
      apply hV0
      ext i k
      obtain ⟨A, hA⟩ := hL (Matrix.single k j (x j)⁻¹)
      have h1 : V *ᵥ (Matrix.single k j (x j)⁻¹ *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      rw [Matrix.single_mulVec, inv_mul_cancel₀ hj'] at h1
      have h2 := congrFun h1 i
      change (V *ᵥ Pi.single k 1) i = 0 at h2
      rw [Matrix.mulVec_single_one] at h2
      simpa using h2
    have surj : Function.Surjective (Matrix.toLin' V) := by
      obtain ⟨i0, k0, h0⟩ : ∃ i k, V i k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hV0 (Matrix.ext fun i k => by simp [h i k])
      intro y
      let A : Matrix m m F := Matrix.of fun i a => if a = i0 then y i * (V i0 k0)⁻¹ else 0
      obtain ⟨C, hC⟩ := hR A
      refine ⟨C *ᵥ Pi.single k0 1, ?_⟩
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hC, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_single_one]
      funext i
      simp [A, Matrix.mulVec, dotProduct, ite_mul, h0]
    let e := LinearEquiv.ofBijective (Matrix.toLin' V) ⟨inj, surj⟩
    have he1 : Matrix.toLin' V ∘ₗ (e.symm : (m → F) →ₗ[F] (n → F)) = LinearMap.id :=
      LinearMap.ext fun y => e.apply_symm_apply y
    have he2 : (e.symm : (m → F) →ₗ[F] (n → F)) ∘ₗ Matrix.toLin' V = LinearMap.id :=
      LinearMap.ext fun y => e.symm_apply_apply y
    refine ⟨LinearMap.toMatrix' (e.symm : (m → F) →ₗ[F] (n → F)), ?_, ?_⟩
    · have h := LinearMap.toMatrix'_comp (Matrix.toLin' V) (e.symm : (m → F) →ₗ[F] (n → F))
      rw [he1, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h
      exact h.symm
    · have h := LinearMap.toMatrix'_comp (e.symm : (m → F) →ₗ[F] (n → F)) (Matrix.toLin' V)
      rw [he2, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h
      exact h.symm
  · have hC : ∀ A : Matrix m m F, Commute A V := by
      intro A
      have hA : A ∈ Submodule.span F (Set.range ρ) := by rw [hρ]; exact Submodule.mem_top
      induction hA using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact hV g
      | zero => exact Commute.zero_left V
      | add x y _ _ hx hy => exact hx.add_left hy
      | smul a x _ hx => exact hx.smul_left a
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (fun i j _ => hC _)
    refine ⟨c, ?_⟩
    rw [← hc]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
section
open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure IsCplAt (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B]
    [Algebra R B] : Prop where
  noeth : IsNoetherianRing B
  complete : IsAdicComplete (maximalIdeal B) B
  comap_eq : (maximalIdeal B).comap (algebraMap R B) = p
  dense : ∀ (n : ℕ) (b : B), ∃ a s : R, s ∉ p ∧
    algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n
  strict : ∀ (n : ℕ) (a : R), algebraMap R B a ∈ maximalIdeal B ^ n → ∃ s : R, s ∉ p ∧ s * a ∈ p ^ n

theorem IsCplAt.isPrime {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) : p.IsPrime := by
  rw [← h.comap_eq]
  exact Ideal.comap_isPrime _ _

abbrev CplAt (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] : Type :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)

end UpperTheory.V.AlgebraTools
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LenFgQuot
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.length_quotient_fg_bounds {A : Type} [CommRing A] (H : Type) [AddCommGroup H] [Module A H]
    (r : ℕ) (π : H →ₗ[A] (Fin r → A)) (hπ : Function.Surjective π) (I : Ideal A) :
    Module.length A (Fin r → A ⧸ I) ≤ Module.length A (H ⧸ I • (⊤ : Submodule A H)) ∧
    Module.length A (H ⧸ I • (⊤ : Submodule A H)) ≤
      Module.length A (Fin r → A ⧸ I) + Module.length A (LinearMap.ker π) := by
  classical
  let N := I • (⊤ : Submodule A H)
  let φ : H →ₗ[A] (Fin r → A ⧸ I) := LinearMap.pi fun i => I.mkQ ∘ₗ (LinearMap.proj i ∘ₗ π)
  have hφ : ∀ h i, φ h i = Submodule.Quotient.mk (π h i) := fun h i => rfl
  have hNφ : N ≤ LinearMap.ker φ := by
    rw [Submodule.smul_le]
    intro a ha h _
    rw [LinearMap.mem_ker]
    funext i
    rw [hφ, map_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact I.mul_mem_right _ ha
  let φ' := N.liftQ φ hNφ
  have hφ' : ∀ h, φ' (N.mkQ h) = φ h := fun h => rfl
  have hsurj : Function.Surjective φ' := by
    intro y
    choose z hz using fun i => Submodule.Quotient.mk_surjective I (y i)
    obtain ⟨h, rfl⟩ := hπ z
    refine ⟨N.mkQ h, ?_⟩
    funext i
    rw [hφ', hφ, hz]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs' : ∀ v, π (s v) = v := fun v => LinearMap.congr_fun hs v
  let ρ : LinearMap.ker π →ₗ[A] LinearMap.ker φ' :=
    (N.mkQ ∘ₗ (LinearMap.ker π).subtype).codRestrict (LinearMap.ker φ') (by
      intro k
      rw [LinearMap.mem_ker, LinearMap.comp_apply, hφ']
      funext i
      rw [hφ, Submodule.subtype_apply, LinearMap.mem_ker.1 k.2]
      simp)
  have hρ : Function.Surjective ρ := by
    rintro ⟨x, hx⟩
    obtain ⟨h, rfl⟩ := N.mkQ_surjective x
    rw [LinearMap.mem_ker, hφ'] at hx
    have hI : ∀ i, π h i ∈ I := fun i => by
      have := congrFun hx i
      rw [hφ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    have hsN : s (π h) ∈ N := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [pi_eq_sum_univ (π h), map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem_smul (hI i) trivial
    have hk : h - s (π h) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, hs', sub_self]
    refine ⟨⟨_, hk⟩, ?_⟩
    apply Subtype.ext
    change N.mkQ (h - s (π h)) = N.mkQ h
    have h0 : N.mkQ (s (π h)) = 0 := (Submodule.Quotient.mk_eq_zero N).2 hsN
    rw [map_sub, h0, sub_zero]
  have hex := Module.length_eq_add_of_exact (LinearMap.ker φ').subtype φ'
    (Submodule.subtype_injective _) hsurj (LinearMap.exact_subtype_ker_map φ')
  refine ⟨Module.length_le_of_surjective φ' hsurj, ?_⟩
  rw [hex, add_comm]
  exact add_le_add le_rfl (Module.length_le_of_surjective ρ hρ)

private theorem UpperTheory.V.AlgebraTools.len_fg_quot_tors {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] (hT : Module.IsTorsion A T) :
    Module.length A T ≠ ⊤ := by
  classical
  obtain ⟨x, hxann, hx⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hT
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  have hspan : Ideal.span {x} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hspan hϖ
  have hJ : Ideal.span {x} = maximalIdeal A ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' A T
  let I : Ideal A := maximalIdeal A ^ n
  have hIf : I • (⊤ : Submodule A (Fin k → A)) ≤ LinearMap.ker f := by
    rw [Submodule.smul_le]
    intro a ha v _
    rw [LinearMap.mem_ker, map_smul]
    have ha' : a ∈ Ideal.span {x} := by rw [hJ]; exact ha
    rw [Ideal.mem_span_singleton'] at ha'
    obtain ⟨c, rfl⟩ := ha'
    rw [mul_smul, (Submodule.mem_annihilator.1 hxann) _ trivial, smul_zero]
  have hsurj : Function.Surjective ((I • (⊤ : Submodule A (Fin k → A))).liftQ f hIf) := by
    intro t
    obtain ⟨v, rfl⟩ := hf t
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  have h1 := (UpperTheory.V.AlgebraTools.length_quotient_fg_bounds (Fin k → A) k LinearMap.id
    Function.surjective_id I).2
  have hker : Module.length A (LinearMap.ker (LinearMap.id : (Fin k → A) →ₗ[A] (Fin k → A))) = 0 := by
    rw [Module.length_eq_zero_iff]
    constructor
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [LinearMap.mem_ker, LinearMap.id_apply] at ha hb
    subst ha hb
    rfl
  have h2 : Module.length A (Fin k → A ⧸ I) = (k * n : ℕ) := by
    rw [Module.length_pi, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    simp
  have h3 := Module.length_le_of_surjective _ hsurj
  rw [hker, add_zero, h2] at h1
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) (h3.trans h1)

theorem UpperTheory.V.AlgebraTools.len_fg_quot :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (H : Type) [AddCommGroup H] [Module A H] [Module.Finite A H], ∃ c : ℕ, Module.length A (Submodule.torsion A H) = c ∧ ∀ j : ℕ, ((Module.finrank A H * j : ℕ) : ℕ∞) ≤ Module.length A (H ⧸ maximalIdeal A ^ j • (⊤ : Submodule A H)) ∧ Module.length A (H ⧸ maximalIdeal A ^ j • (⊤ : Submodule A H)) ≤ ((Module.finrank A H * j + c : ℕ) : ℕ∞) := by
  intro A _ _ _ H _ _ _
  classical
  let Tor := Submodule.torsion A H
  haveI : Module.Free A (H ⧸ Tor) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis A (H ⧸ Tor)
  have hm : Module.finrank A (H ⧸ Tor) = Module.finrank A H :=
    finrank_quotient_eq_of_le_torsion le_rfl
  let π : H →ₗ[A] (Fin (Module.finrank A (H ⧸ Tor)) → A) := b.equivFun.toLinearMap ∘ₗ Tor.mkQ
  have hπ : Function.Surjective π := b.equivFun.surjective.comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker π = Tor := by
    simp only [π, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  have hTf : Module.length A Tor ≠ ⊤ :=
    UpperTheory.V.AlgebraTools.len_fg_quot_tors Tor (Submodule.torsion_isTorsion)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hTf
  refine ⟨c, hc.symm, fun j => ?_⟩
  have h := UpperTheory.V.AlgebraTools.length_quotient_fg_bounds H _ π hπ (maximalIdeal A ^ j)
  have hlen : Module.length A (Fin (Module.finrank A (H ⧸ Tor)) → A ⧸ maximalIdeal A ^ j) =
      ((Module.finrank A H * j : ℕ) : ℕ∞) := by
    rw [Module.length_pi, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, hm]
    simp
  rw [hlen, hker, ← hc] at h
  refine ⟨h.1, ?_⟩
  rw [Nat.cast_add]
  exact h.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSplitDefs
section
noncomputable section

open Polynomial

namespace UpperTheory.V.AlgebraTools

variable {R κ : Type} [CommRing R] (P : κ → R[X]) (n : ℕ)

def mSplitIdeal : Ideal (MvPolynomial (κ × Fin n) R) :=
  Ideal.span (Set.range fun jk : κ × ℕ =>
    (∏ i : Fin n, (X - C (MvPolynomial.X (jk.1, i) : MvPolynomial (κ × Fin n) R)) -
      (P jk.1).map MvPolynomial.C).coeff jk.2)

abbrev MSplitAlg : Type := MvPolynomial (κ × Fin n) R ⧸ mSplitIdeal P n

def MSplitAlg.root (j : κ) (i : Fin n) : MSplitAlg P n := Ideal.Quotient.mk _ (MvPolynomial.X (j, i))

theorem MSplitAlg.prod_root (j : κ) :
    ∏ i : Fin n, (X - C (MSplitAlg.root P n j i)) = (P j).map (algebraMap R (MSplitAlg P n)) := by
  have h : (∏ i : Fin n, (X - C (MvPolynomial.X (j, i) : MvPolynomial (κ × Fin n) R)) -
      (P j).map MvPolynomial.C).map (Ideal.Quotient.mk (mSplitIdeal P n)) = 0 := by
    ext k
    rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨(j, k), rfl⟩
  rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero] at h
  simp only [Polynomial.map_sub, map_X, map_C] at h
  exact h

def MSplitAlg.lift {A : Type} [CommRing A] [Algebra R A] (a : κ → Fin n → A)
    (h : ∀ j, ∏ i : Fin n, (X - C (a j i)) = (P j).map (algebraMap R A)) : MSplitAlg P n →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2) fun x hx => by
    refine (Ideal.span_le (I := RingHom.ker
      (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 : MvPolynomial (κ × Fin n) R →ₐ[R] A))).2 ?_ hx
    rintro _ ⟨⟨j, k⟩, rfl⟩
    have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X (j, i) : MvPolynomial (κ × Fin n) R)) -
        (P j).map MvPolynomial.C).map
        (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 : MvPolynomial (κ × Fin n) R →ₐ[R] A).toRingHom = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero]
      have h3 : (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 :
          MvPolynomial (κ × Fin n) R →ₐ[R] A).toRingHom.comp MvPolynomial.C = algebraMap R A :=
        RingHom.ext fun r => by simp
      rw [h3, ← h j]
      simp
    have h4 := congrArg (fun q => q.coeff k) h2
    simp only [coeff_map, coeff_zero] at h4
    exact h4

theorem MSplitAlg.lift_root {A : Type} [CommRing A] [Algebra R A] (a : κ → Fin n → A)
    (h : ∀ j, ∏ i : Fin n, (X - C (a j i)) = (P j).map (algebraMap R A)) (j : κ) (i : Fin n) :
    MSplitAlg.lift P n a h (MSplitAlg.root P n j i) = a j i :=
  MvPolynomial.aeval_X (fun p : κ × Fin n => a p.1 p.2) (j, i)

theorem MSplitAlg.hom_ext {A : Type} [CommRing A] [Algebra R A] {f g : MSplitAlg P n →ₐ[R] A}
    (h : ∀ j i, f (MSplitAlg.root P n j i) = g (MSplitAlg.root P n j i)) : f = g :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun p => h p.1 p.2)

end UpperTheory.V.AlgebraTools
end
end

