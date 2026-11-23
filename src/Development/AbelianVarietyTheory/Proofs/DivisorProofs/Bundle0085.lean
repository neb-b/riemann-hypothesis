module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicSplitsValuationSubringOfSeparableReduction
section
open Polynomial IsLocalRing

namespace GlobalTheory

theorem monic_splits_of_separable_residue (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (V : ValuationSubring Ω) (q : Polynomial V) (hq : q.Monic)
    (hs : (q.map (IsLocalRing.residue V)).Separable) :
    ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  have hinj : Function.Injective (algebraMap V Ω) := IsFractionRing.injective V Ω

  have hdegree : ∀ g : Polynomial Ω, Irreducible g → g ∣ q.map (algebraMap V Ω) →
      g.degree = 1 := by
    intro g hg hgd
    obtain ⟨g₀, hg₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd Ω hq hgd
    have hg0 : g ≠ 0 := hg.ne_zero
    have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    have hmap : g₀.map (algebraMap V Ω) = g * C g.leadingCoeff⁻¹ := by
      set c := g.leadingCoeff with hc
      rw [← hg₀, mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, mul_one]
    have hmapm : (g₀.map (algebraMap V Ω)).Monic := by
      rw [hmap]; exact monic_mul_leadingCoeff_inv hg0
    have hg₀m : g₀.Monic := monic_of_injective hinj hmapm
    have hdvd : g₀ ∣ q := by
      rw [← map_dvd_map (algebraMap V Ω) hinj hg₀m, hmap]
      refine dvd_trans (Dvd.intro (C g.leadingCoeff) ?_) hgd
      rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
    have hsep₀ : (g₀.map (residue V)).Separable :=
      hs.of_dvd (Polynomial.map_dvd _ hdvd)
    have hdeg : (g₀.map (residue V)).natDegree = g.natDegree := by
      rw [hg₀m.natDegree_map, ← natDegree_map_eq_of_injective hinj, hmap,
        natDegree_mul_C (inv_ne_zero hlc)]
    have hgdeg : g.natDegree ≠ 0 := fun h =>
      hg.not_isUnit (isUnit_iff_degree_eq_zero.mpr ((degree_eq_iff_natDegree_eq hg0).mpr h))
    have hder₀ : derivative (g₀.map (residue V)) ≠ 0 := by
      intro h0
      have hu : IsUnit (g₀.map (residue V)) := by
        have := hsep₀
        rw [Polynomial.Separable, h0, isCoprime_zero_right] at this
        exact this
      exact hgdeg (hdeg ▸ natDegree_eq_zero_of_isUnit hu)
    have hder : derivative g ≠ 0 := by
      intro h0
      apply hder₀
      have h1 : derivative (g₀.map (algebraMap V Ω)) = 0 := by
        rw [hmap, derivative_mul, derivative_C, h0]; simp
      rw [derivative_map] at h1 ⊢
      have h2 : derivative g₀ = 0 := by
        apply Polynomial.map_injective _ hinj
        rw [h1, Polynomial.map_zero]
      rw [h2, Polynomial.map_zero]
    exact IsSepClosed.degree_eq_one_of_irreducible Ω hg
      ((separable_iff_derivative_ne_zero hg).mpr hder)
  have hQ : (q.map (algebraMap V Ω)).Splits := by
    by_cases hq0 : q.map (algebraMap V Ω) = 0
    · simp [hq0]
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hq0
    rw [← hu]
    refine (Splits.multisetProd fun f hf ↦ ?_).mul u.isUnit.splits
    let h := UniqueFactorizationMonoid.irreducible_of_factor f hf
    exact Splits.of_degree_eq_one (hdegree f h
      (UniqueFactorizationMonoid.dvd_of_mem_factors hf))
  have hroots : ∀ a ∈ (q.map (algebraMap V Ω)).roots, a ∈ (algebraMap V Ω).range := by
    intro a ha
    have hne : q.map (algebraMap V Ω) ≠ 0 := (hq.map _).ne_zero
    have hr : aeval a q = 0 := by
      rw [mem_roots hne, IsRoot, eval_map_algebraMap] at ha
      exact ha
    have hint : IsIntegral V a := ⟨q, hq, by rwa [← aeval_def]⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).mp hint
    exact ⟨y, hy⟩
  have hqs : q.Splits := Splits.of_splits_map_of_injective hinj hQ hroots
  exact ⟨q.roots, hqs.eq_prod_roots_of_monic hq⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorseInequalityArith
section
namespace GlobalTheory

theorem morse_inequality_arith (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ)
    (H1 : ∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤
      C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1)))
    (H2 : ∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤
      C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)))
    (hab : ((d : ℤ) + 1) * b < a) : ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = C * (d + 1) + (d + 1) * C' * d := ⟨_, rfl⟩
  obtain ⟨m, hm0, hm1, hmK⟩ : ∃ m : ℕ, m₀ ≤ m ∧ m₁ ≤ m ∧ K * 2 ^ d + 1 ≤ m :=
    ⟨m₀ + m₁ + (K * 2 ^ d + 1), by omega, by omega, by omega⟩
  have hm : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hmK
  refine ⟨m, hm, ?_⟩
  by_contra hcon
  have hcon' : (h m : ℤ) ≤ (m : ℤ) * g m := by exact_mod_cast not_lt.mp hcon
  have h1 := (abs_le.mp (H1 m hm0)).1
  have h2 := (abs_le.mp (H2 m hm1)).2
  rw [Nat.add_sub_cancel, Nat.factorial_succ] at h1
  push_cast at h1
  have hM : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hMK : (K : ℤ) * 2 ^ d + 1 ≤ m := by exact_mod_cast hmK
  have hKz : (K : ℤ) = C * ((d : ℤ) + 1) + (d + 1) * C' * d := by rw [hK]; push_cast; ring
  generalize (m : ℤ) = M at *
  have hF : (0 : ℤ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hd : (0 : ℤ) ≤ d := by positivity
  have hA : M * ((d : ℤ) * (M + 1) ^ (d - 1)) ≤ d * (M + 1) ^ d := by
    rcases d with _ | e
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      have : (0 : ℤ) ≤ ((e + 1 : ℕ) : ℤ) * (M + 1) ^ e := by positivity
      nlinarith
  have hP : (M + 1) ^ d ≤ 2 ^ d * M ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) d
  have hQ : 0 < M ^ d := by positivity
  have e1 : ((d : ℤ) + 1) * d.factorial * h m ≤ ((d : ℤ) + 1) * d.factorial * (M * g m) :=
    mul_le_mul_of_nonneg_left hcon' (by positivity)
  have e2 : ((d : ℤ) + 1) * M * ((d.factorial : ℤ) * g m - b * M ^ d) ≤
      ((d : ℤ) + 1) * M * (C' * ((d : ℤ) * (M + 1) ^ (d - 1))) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e3 : ((d : ℤ) + 1) * C' * (M * ((d : ℤ) * (M + 1) ^ (d - 1))) ≤
      ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have e4 : (K : ℤ) * (M + 1) ^ d ≤ K * (2 ^ d * M ^ d) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have e5 : ((K : ℤ) * 2 ^ d + 1) * M ^ d ≤ M * M ^ d :=
    mul_le_mul_of_nonneg_right hMK hQ.le
  have e6 : (((d : ℤ) + 1) * b + 1) * (M * M ^ d) ≤ a * (M * M ^ d) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e7 : (K : ℤ) * (M + 1) ^ d =
      C * ((d + 1) * (M + 1) ^ d) + ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) := by
    rw [hKz]; ring
  rw [pow_succ' M d] at h1
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulNormSqLeNormProjApplySqOfSpanningParts
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts
    {X Y ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (T : X →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ) (hP : (⨆ k, P k) = ⊤)
    (hl : ∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) (u : Y) :
    m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  haveI : Nontrivial Y := ⟨⟨u, 0, hu⟩⟩
  set S : Y →ₗ[ℂ] Y := T ∘ₗ LinearMap.adjoint T with hS
  have hsym : S.IsSymmetric := by
    intro a b
    simp only [hS, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right T, LinearMap.adjoint_inner_left]
  have hq : ∀ y : Y, RCLike.re ⟪S y, y⟫_ℂ = ‖LinearMap.adjoint T y‖ ^ 2 := by
    intro y
    simp only [hS, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right T, inner_self_eq_norm_sq]
  have hev : ∀ μ : ℝ, Module.End.HasEigenvalue S (μ : ℂ) → m ≤ μ := by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    by_contra hlt
    have hlt : μ < m := not_le.mp hlt
    have hSv : S v = (μ : ℂ) • v := hv.apply_eq_smul
    have hle : ∀ k, P k ≤ (ℂ ∙ v)ᗮ := by
      intro k y hy
      obtain ⟨l, hml, hly⟩ := hl k
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      have h1 := hsym v y
      have h2 : S y = (l : ℂ) • y := hly y hy
      rw [hSv, h2, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
      have h3 : ((μ : ℂ) - (l : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        have : μ = l := by exact_mod_cast h
        linarith
      have h4 : ((μ : ℂ) - (l : ℂ)) * ⟪v, y⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.mp h4).resolve_left h3
    have hv' : v ∈ (ℂ ∙ v)ᗮ := by
      have : (⊤ : Submodule ℂ Y) ≤ (ℂ ∙ v)ᗮ := hP ▸ iSup_le hle
      exact this Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hv'
    exact hv.2 hv'
  have h1 := hev _ hsym.hasEigenvalue_iInf_of_finiteDimensional
  have hb : BddBelow (Set.range fun x : { x : Y // x ≠ 0 } =>
      RCLike.re ⟪S x, x⟫_ℂ / ‖(x : Y)‖ ^ 2) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    simp only [hq]
    positivity
  have h2 := h1.trans (ciInf_le hb ⟨u, hu⟩)
  simp only [hq] at h2
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  rwa [le_div_iff₀ hpos] at h2

theorem mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts :
    ∀ (X Y ι : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ), 0 < m → LinearMap.adjoint e = e → (∀ y, e (e y) = e y) → (⨆ k, P k) = ⊤ → (∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) → ∀ x ∈ (LinearMap.ker (e ∘ₗ T))ᗮ, m * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 := by
  intro X Y ι _ _ _ _ _ _ T e P m hm he hee hP hl x hx
  rw [LinearMap.orthogonal_ker] at hx
  obtain ⟨w, hw⟩ := hx
  rw [LinearMap.adjoint_comp, he, LinearMap.comp_apply] at hw
  set u := e w with hu
  have h1 := mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts T P m hP hl u
  rw [hw] at h1
  have h2 : ⟪x, x⟫_ℂ = ⟪u, e (T x)⟫_ℂ := by
    have : ⟪u, e (T x)⟫_ℂ = ⟪e u, T x⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_left e, he]
    rw [this, hu, hee, ← hu, ← LinearMap.adjoint_inner_left T, hw]
  have h3 : ‖x‖ ^ 2 ≤ ‖u‖ * ‖e (T x)‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) u (e (T x))
    rw [← h2, inner_self_eq_norm_sq_to_K] at h
    simpa using h
  by_cases hx0 : x = 0
  · simp [hx0]
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  have h4 : (‖x‖ ^ 2) ^ 2 ≤ (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
  have h5 : (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by
    calc (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 = m * (‖x‖ ^ 2) ^ 2 := by ring
      _ ≤ m * (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
      _ = ‖e (T x)‖ ^ 2 * (m * ‖u‖ ^ 2) := by ring
      _ ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
  exact le_of_mul_le_mul_right h5 hpos

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTensorInjectiveOfFlatBaseChangeKerInf
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open TensorProduct

namespace GlobalTheory.TorStep

theorem mul_tensor_injective : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B]
    [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂),
    Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ →
    RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ →
    a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := by
  intro P R₂ B B₂ _ _ _ _ _ K₁ f₂ a₂ c₂ hf hc hcomp hker hK hflat
  letI := a₂.toAlgebra
  haveI : Module.Flat R₂ B₂ := hflat
  have hc' : ∀ p : P, c₂ (algebraMap P B p) = a₂ (f₂ p) := fun p => by
    simpa using congrArg (fun g : P →+* B₂ => g p) hcomp
  have hsmulB : ∀ (p : P) (b : B), c₂ (p • b) = f₂ p • c₂ b := fun p b => by
    rw [Algebra.smul_def, map_mul, hc', Algebra.smul_def, RingHom.algebraMap_toAlgebra]

  have hzero : ∀ x : P, x ∈ K₁ → f₂ x = 0 → x = 0 := fun x h1 h2 => by
    have : x ∈ K₁ ⊓ RingHom.ker f₂ := ⟨h1, h2⟩
    rw [hK] at this
    simpa using this

  have L0 : ∀ x : B, x ∈ RingHom.ker c₂ → ∀ k : K₁, (k ⊗ₜ[P] x : K₁ ⊗[P] B) = 0 := by
    intro x hx
    rw [hker, Ideal.map] at hx
    suffices H : ∀ (k : K₁) (y : B), (k ⊗ₜ[P] (y * x) : K₁ ⊗[P] B) = 0 by
      intro k; simpa using H k 1
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨κ, hκ, rfl⟩ := hz
      intro k y
      have e1 : y * algebraMap P B κ = κ • y := by rw [Algebra.smul_def, mul_comm]
      rw [e1, ← smul_tmul]
      have e2 : κ • k = 0 := by
        apply Subtype.ext
        apply hzero
        · exact (κ • k).2
        · simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
          rw [RingHom.mem_ker.mp hκ, zero_mul]
      rw [e2, zero_tmul]
    | zero => intro k y; rw [mul_zero, tmul_zero]
    | add u v _ _ hu hv => intro k y; rw [mul_add, tmul_add, hu, hv, add_zero]
    | smul b u _ hu => intro k y; rw [smul_eq_mul, ← mul_assoc]; exact hu k (y * b)
  have L1 : ∀ (k : K₁) (x y : B), c₂ x = c₂ y → (k ⊗ₜ[P] x : K₁ ⊗[P] B) = k ⊗ₜ[P] y := by
    intro k x y h
    rw [← sub_eq_zero, ← tmul_sub]
    exact L0 _ (by rw [RingHom.mem_ker, map_sub, h, sub_self]) k
  let s := Function.surjInv hc
  have hs : ∀ β, c₂ (s β) = β := Function.surjInv_eq hc
  let J₂ : Ideal R₂ := K₁.map f₂
  let ej : K₁ → J₂ := fun k => ⟨f₂ k, Ideal.mem_map_of_mem f₂ k.2⟩
  have hpre : ∀ j : J₂, ∃ k : P, k ∈ K₁ ∧ f₂ k = j := fun j =>
    (Ideal.mem_map_iff_of_surjective f₂ hf).mp j.2
  let einv : J₂ → K₁ := fun j => ⟨Classical.choose (hpre j), (Classical.choose_spec (hpre j)).1⟩
  have hE' : ∀ j : J₂, f₂ (einv j) = j := fun j => (Classical.choose_spec (hpre j)).2
  have hE : ∀ (k : K₁) (j : J₂), f₂ k = j → einv j = k := by
    intro k j h
    apply Subtype.ext
    rw [← sub_eq_zero]
    apply hzero
    · exact (einv j - k).2
    · rw [map_sub, hE', h, sub_self]

  let ψ0 : K₁ →+ B →+ J₂ ⊗[R₂] B₂ :=
    AddMonoidHom.mk' (fun k => AddMonoidHom.mk' (fun b => ej k ⊗ₜ[R₂] c₂ b)
      (fun b b' => by rw [map_add (f := _), tmul_add]))
      (fun k k' => by
        ext b
        have : ej (k + k') = ej k + ej k' := Subtype.ext (by simp [ej])
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, this, add_tmul])
  let ψ : K₁ ⊗[P] B →+ J₂ ⊗[R₂] B₂ := liftAddHom ψ0 (by
    intro p k b
    simp only [ψ0, AddMonoidHom.mk'_apply]
    have : ej (p • k) = f₂ p • ej k := Subtype.ext (by simp [ej])
    rw [this, hsmulB, smul_tmul])

  let χ0 : J₂ →+ B₂ →+ K₁ ⊗[P] B :=
    AddMonoidHom.mk' (fun j => AddMonoidHom.mk' (fun β => einv j ⊗ₜ[P] s β)
      (fun β β' => by rw [← tmul_add]; exact L1 _ _ _ (by rw [map_add (f := _), hs, hs, hs])))
      (fun j j' => by
        ext β
        have : einv (j + j') = einv j + einv j' :=
          hE _ _ (by rw [Submodule.coe_add, map_add (f := _), hE', hE', Submodule.coe_add])
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, this, add_tmul])
  let χ : J₂ ⊗[R₂] B₂ →+ K₁ ⊗[P] B := liftAddHom χ0 (by
    intro r j β
    simp only [χ0, AddMonoidHom.mk'_apply]
    obtain ⟨p, rfl⟩ := hf r
    have e1 : einv (f₂ p • j) = p • einv j :=
      hE _ _ (by simp [hE'])
    rw [e1, smul_tmul]
    exact L1 _ _ _ (by rw [hsmulB, hs, hs]))
  have hχψ : ∀ t, χ (ψ t) = t := by
    intro t
    induction t with
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
    | tmul k b =>
      simp only [ψ, χ, liftAddHom_tmul, ψ0, χ0, AddMonoidHom.mk'_apply]
      rw [hE k (ej k) rfl]
      exact L1 _ _ _ (hs _)

  let ν : J₂ ⊗[R₂] B₂ →ₗ[R₂] B₂ :=
    (TensorProduct.lid R₂ B₂).toLinearMap ∘ₗ J₂.subtype.rTensor B₂
  have hν : Function.Injective ν :=
    (TensorProduct.lid R₂ B₂).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ J₂.injective_subtype)
  set μ := TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype) with hμ
  have key : ∀ t, ν (ψ t) = c₂ (μ t) := by
    intro t
    induction t with
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _), map_add (f := _)]
    | tmul k b =>
      simp only [ψ, liftAddHom_tmul, ψ0, AddMonoidHom.mk'_apply, ν, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul, hμ, TensorProduct.lift.tmul, LinearMap.coe_comp,
        LinearMap.lsmul_apply]
      rw [hsmulB]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have h1 : ψ t = 0 := hν (by rw [key, ht, map_zero, map_zero])
  rw [← hχψ t, h1, map_zero]

end GlobalTheory.TorStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearMemSpanImagePartial
section
namespace GlobalTheory.MultilinearSpanImage

theorem multilinear_mem_span_image_partial {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module ℂ (M i)] {N : Type} [AddCommGroup N]
    [Module ℂ N] (Φ : MultilinearMap (RingHom.id ℂ) M N) (s : (i : ι) → Set (M i)) (t : Finset ι) :
    ∀ f : (i : ι) → M i, (∀ i ∈ t, f i ∈ Submodule.span ℂ (s i)) → (∀ i, i ∉ t → f i ∈ s i) →
      Φ f ∈ Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
  refine Finset.induction_on t ?_ ?_
  · intro f _ h
    exact Submodule.subset_span ⟨f, fun i => h i (by simp), rfl⟩
  · intro a t ha ih f h1 h2
    have key : ∀ x ∈ Submodule.span ℂ (s a), Φ (Function.update f a x) ∈
        Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        apply ih
        · intro i hi
          have hne : i ≠ a := by rintro rfl; exact ha hi
          simpa [hne] using h1 i (Finset.mem_insert_of_mem hi)
        · intro i hi
          by_cases h : i = a
          · subst h; simpa using hx
          · simpa [h] using h2 i (by simp [h, hi])
      | zero => rw [Φ.map_update_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Φ.map_update_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [Φ.map_update_smul]; exact Submodule.smul_mem _ c hx
    have := key (f a) (h1 a (Finset.mem_insert_self a t))
    simpa using this

theorem multilinear_apply_mem_span_image {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [inst : (i : ι) → AddCommGroup (M i)] [inst_1 : (i : ι) → Module ℂ (M i)] {N : Type}
    [inst_2 : AddCommGroup N] [inst_3 : Module ℂ N] (Φ : MultilinearMap (RingHom.id ℂ) M N)
    (s : (i : ι) → Set (M i)) (f : (i : ι) → M i) (hf : ∀ (i : ι), f i ∈ Submodule.span ℂ (s i)) :
    (Φ : ((i : ι) → M i) → N) f ∈ Submodule.span ℂ
      {y : N | ∃ (g : (i : ι) → M i), (∀ (i : ι), g i ∈ s i) ∧ y = (Φ : ((i : ι) → M i) → N) g} :=
  multilinear_mem_span_image_partial Φ s Finset.univ f (fun i _ => hf i) (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory.MultilinearSpanImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialIdealEqBotOfPderivStableNoConstants
section
namespace GlobalTheory

open MvPolynomial Finsupp

theorem mvPolynomial_ideal_eq_bot_of_pderiv_stable :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by
  intro R _ _ _ r I hI hC
  have key : ∀ n : ℕ, ∀ P ∈ I, P.totalDegree = n → P = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro P hP h
    by_contra hne
    by_cases hn : n = 0
    · subst hn
      rw [totalDegree_eq_zero_iff_eq_C] at h
      apply hne
      rw [h] at hP ⊢
      rw [hC _ hP, C_0]
    · obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hne)
        (fun s => s.sum fun _ e => e)
      have hdeg : (m.sum fun _ e => e) = n := by rw [← h, totalDegree, hmd]
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have hm0 : m = 0 := Finsupp.ext hcon
        subst hm0
        simp at hdeg
        omega
      have hQ : pderiv i P ∈ I := hI P hP i
      have hQne : pderiv i P ≠ 0 := by
        intro h0
        have hc := coeff_pderiv (i := i) P (m - single i 1)
        rw [h0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
          sub_add_single_one_cancel hi] at hc
        have hcm : AddMonoidAlgebra.coeff P m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
        have hk : (((m - single i 1 : Fin r →₀ ℕ) i : ℕ) : R) + 1 ≠ 0 :=
          Nat.cast_add_one_ne_zero _
        exact (mul_ne_zero hcm hk) hc.symm
      have hlt : (pderiv i P).totalDegree < n := by
        have hle : (pderiv i P).totalDegree ≤ n - 1 := by
          apply Finset.sup_le
          intro s hs
          have hs' := MvPolynomial.mem_support_iff.mp hs
          rw [coeff_pderiv] at hs'
          have hsupp : s + single i 1 ∈ P.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs')
          have hd := le_totalDegree hsupp
          rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl, h] at hd
          omega
        omega
      exact hQne (ih _ hlt _ hQ rfl)
  rw [eq_bot_iff]
  intro P hP
  rw [Ideal.mem_bot]
  exact key _ P hP rfl

end GlobalTheory
end

