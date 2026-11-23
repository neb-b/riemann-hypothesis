module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerLeSpanImageKerOfSemilinear
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem ker_le_span_image_ker_of_semilinear :
    ∀ (K X Y H W : Type) [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y] [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (θ : X →ₗ[K] Y) (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W), Submodule.span ℂ (Set.range j) = ⊤ → (∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k)) → (∀ x, T (j x) = jW (θ x)) → LinearMap.ker T ≤ Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) := by
  intro K X Y H W _ _ _ _ _ _ _ _ _ _ σ θ j jW T hspan hind hT
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker θ)
  let b := Module.finBasis K C
  have hinj : LinearMap.ker (θ ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have h1 : (m : X) ∈ LinearMap.ker θ := hm
    have h2 : (m : X) ∈ LinearMap.ker θ ⊓ C := ⟨h1, m.2⟩
    rw [hC.inf_eq_bot] at h2
    exact Subtype.ext (by simpa using h2)
  have hli : LinearIndependent K (fun k => θ (b k : X)) :=
    b.linearIndependent.map' (θ ∘ₗ C.subtype) hinj
  have hli2 := hind _ _ hli
  set N := Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) with hN
  have hNT : N ≤ LinearMap.ker T := by
    rw [hN, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : θ x = 0 := hx
    show T (j x) = 0
    rw [hT, hx', map_zero]
  have htop : N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ LinearMap.ker θ ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    refine Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) ?_
    have hcs : c = ∑ k, b.repr ⟨c, hc⟩ k • (b k : X) := by
      have := congrArg (fun z : C => (z : X)) (b.sum_repr ⟨c, hc⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hcs, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  intro h hh
  have hmem : h ∈ N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) := by
    rw [htop]; trivial
  obtain ⟨u, hu, s, hs, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
  have hTu : T u = 0 := hNT hu
  have h0 : ∑ k, a k • jW (θ (b k : X)) = 0 := by
    have : T (u + ∑ k, a k • j (b k : X)) = 0 := hh
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), hTu, zero_add, map_sum] at this
    simpa [hT] using this
  have ha := Fintype.linearIndependent_iff.1 hli2 a h0
  simpa [ha] using hu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSmulLeIdealSmulOfFree
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem ker_smul_le_ideal_smul_of_free : ∀ (Λ : Type) [CommRing Λ] (t : Λ), (∀ x : Λ, t * x = 0 → x ∈ Ideal.span {t}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M], Module.Free Λ M → ∀ m : M, t • m = 0 → m ∈ Ideal.span {t} • (⊤ : Submodule Λ M) := by
  intro Λ _ t ht M _ _ hfree m hm
  let b := Module.Free.chooseBasis Λ M
  have hc : ∀ i, ∃ d, b.repr m i = t * d := by
    intro i
    have h0 : t * b.repr m i = 0 := by
      have := congrArg (fun x => b.repr x i) hm
      simpa using this
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (ht _ h0)
    exact ⟨d, by rw [← hd, mul_comm]⟩
  choose d hd using hc
  have hm' : m = t • ∑ i ∈ (b.repr m).support, d i • b i := by
    have e := b.linearCombination_repr m
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at e
    rw [Finset.smul_sum]
    conv_lhs => rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd i, mul_smul]
  rw [hm']
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullIntersectionIdealLocalForm
section
namespace GlobalTheory

theorem krull_inter_ideal_local (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B)
    (h : ∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) : ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  set N : Submodule B (B ⧸ a') := Submodule.map (Submodule.mkQ a') a with hN
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  have hle : N ≤ I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h k hx)
    have h1 : Submodule.mkQ a' (y + z) = z • Submodule.mkQ a' 1 := by
      have hy0 : Submodule.mkQ a' y = 0 := by
        rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero a').2 hy
      rw [map_add (f := _), hy0, zero_add, ← map_smul, smul_eq_mul, mul_one]
    rw [h1]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  have hNI : N ≤ I • N := by
    have e1 : N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := (inf_eq_right.2 hle).symm
    calc N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := e1
      _ = I ^ (k + 1 - k) • (I ^ k • ⊤ ⊓ N) := hk (k + 1) (Nat.le_succ k)
      _ ≤ I • N := by
        rw [Nat.add_sub_cancel_left, pow_one]
        exact Submodule.smul_mono le_rfl inf_le_right
  have hfg : N.FG := IsNoetherian.noetherian N
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N hfg hNI
  refine ⟨r, hr, fun x hx => ?_⟩
  have hx' := hrN (Submodule.mkQ a' x) ⟨x, hx, rfl⟩
  rw [← map_smul, smul_eq_mul] at hx'
  have : Submodule.mkQ a' ((1 - r) * x) = 0 := by
    rw [sub_mul, one_mul, map_sub, hx', sub_self]
  rw [Submodule.mkQ_apply] at this
  exact (Submodule.Quotient.mk_eq_zero a').1 this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAevalValuationDvr
section
open Polynomial IsLocalRing

namespace GlobalTheory

theorem kummer_residue_aeval (T V : Type) [CommRing T] [IsLocalRing T] [CommRing V] [IsLocalRing V]
    [Algebra T V] [IsLocalHom (algebraMap T V)] (γ : V) (p : T[X]) :
    residue V (aeval γ p) = aeval (residue V γ) (p.map (residue T)) := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a hp => simp [hp, pow_succ, ← mul_assoc]

theorem kummer_step_one (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra T V]
    [IsLocalHom (algebraMap T V)]
    (γ : V) (ϖ u : T) (k : ℕ) (hϖ : Irreducible ϖ) (hu : IsUnit u) (hk : IsUnit (k : T))
    (hk0 : 0 < k) (hγ : γ ^ k = algebraMap T V u) (h : T[X])
    (hm : aeval γ h ∈ maximalIdeal V) :
    ∃ ν r : T[X], IsUnit (aeval γ ν) ∧
      aeval γ h * aeval γ ν = algebraMap T V ϖ * aeval γ r := by
  set γ' := residue V γ with hγ'
  set f : (ResidueField T)[X] := X ^ k - C (residue T u) with hf
  have hkκ : ((k : ℕ) : ResidueField T) ≠ 0 := by
    have := (hk.map (residue T)).ne_zero
    simpa using this
  have hu' : residue T u ≠ 0 := (hu.map (residue T)).ne_zero
  have hsep : f.Separable := separable_X_pow_sub_C _ hkκ hu'
  have hfγ : aeval γ' f = 0 := by
    have := congrArg (residue V) hγ
    simp only [map_pow] at this
    simp [hf, hγ', this]
  have hhm : aeval γ' (h.map (residue T)) = 0 := by
    rw [hγ', ← kummer_residue_aeval]
    exact (residue_eq_zero_iff _).mpr hm
  obtain ⟨νb, hνb⟩ := minpoly.dvd (ResidueField T) γ' hfγ
  obtain ⟨qb, hqb⟩ := minpoly.dvd (ResidueField T) γ' hhm
  have hνne : aeval γ' νb ≠ 0 := by
    intro h0
    have hcop : IsCoprime (minpoly (ResidueField T) γ') νb := Separable.isCoprime (hνb ▸ hsep)
    obtain ⟨a, b, hab⟩ := hcop
    have := congrArg (aeval γ') hab
    simp [minpoly.aeval, h0] at this
  obtain ⟨ν, rfl⟩ := map_surjective (residue T) residue_surjective νb
  obtain ⟨q, rfl⟩ := map_surjective (residue T) residue_surjective qb
  set D : T[X] := h * ν - q * (X ^ k - C u) with hD
  have hDm : D.map (residue T) = 0 := by
    have e1 : (X ^ k - C u).map (residue T) = f := by simp [hf]
    rw [hD, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, e1, hνb, hqb]
    ring
  have hDI : D ∈ Ideal.span {C ϖ} := by
    have : D ∈ Ideal.map (C : T →+* T[X]) (maximalIdeal T) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      rw [← residue_eq_zero_iff, ← coeff_map, hDm, coeff_zero]
    rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton] at this
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hDI
  refine ⟨ν, r, ?_, ?_⟩
  · rw [← residue_ne_zero_iff_isUnit, kummer_residue_aeval]
    exact hνne
  · have := congrArg (aeval γ) hr
    simp only [hD, map_mul, map_sub, map_pow, aeval_X, aeval_C, hγ, sub_self, mul_zero,
      sub_zero] at this
    rw [← this, mul_comm]

theorem kummer_valuation : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (γ : V) (ϖ u : T) (k : ℕ), Irreducible ϖ → IsUnit u → IsUnit (k : T) → 0 < k →
    γ ^ k = algebraMap T V u →
    ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h' := by
  intro T V _ _ _ _ _ _ _ _ hinj γ ϖ u k hϖ hu hk hk0 hγ h
  by_cases h0 : aeval γ h = 0
  · exact Or.inl h0
  right
  have hϖV : ¬ IsUnit (algebraMap T V ϖ) := fun h' => hϖ.not_isUnit (isUnit_of_map_unit _ _ h')
  suffices H : ∀ x : V, ∀ h : T[X], aeval γ h = x → x ≠ 0 →
      ∃ (a : ℕ) (h' c : T[X]), IsUnit (aeval γ c) ∧ IsUnit (aeval γ h') ∧
        aeval γ c * aeval γ h = algebraMap T V ϖ ^ a * aeval γ h' from H _ h rfl h0
  intro x
  refine (wellFounded_dvdNotUnit (α := V)).induction
    (C := fun x => ∀ h : T[X], aeval γ h = x → x ≠ 0 →
      ∃ (a : ℕ) (h' c : T[X]), IsUnit (aeval γ c) ∧ IsUnit (aeval γ h') ∧
        aeval γ c * aeval γ h = algebraMap T V ϖ ^ a * aeval γ h') x ?_
  intro x ih h hx hx0
  subst hx
  by_cases hunit : IsUnit (aeval γ h)
  · exact ⟨0, h, 1, by simp, hunit, by simp⟩
  have hm : aeval γ h ∈ maximalIdeal V := (mem_maximalIdeal _).mpr hunit
  obtain ⟨ν, r, hν, hr⟩ := kummer_step_one T V γ ϖ u k hϖ hu hk hk0 hγ h hm
  have hr0 : aeval γ r ≠ 0 := by
    intro h'
    rw [h', mul_zero] at hr
    exact mul_ne_zero hx0 hν.ne_zero hr
  have hdvd : DvdNotUnit (aeval γ r) (aeval γ h) := by
    refine ⟨hr0, algebraMap T V ϖ * ↑hν.unit⁻¹, ?_, ?_⟩
    · intro hu'
      exact hϖV (isUnit_of_mul_isUnit_left hu')
    · calc aeval γ h = aeval γ h * aeval γ ν * ↑hν.unit⁻¹ := by
            rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
        _ = _ := by rw [hr]; ring
  obtain ⟨a, h', c, hc, hh', he⟩ := ih _ hdvd r rfl hr0
  refine ⟨a + 1, h', c * ν, ?_, hh', ?_⟩
  · rw [map_mul]
    exact hc.mul hν
  · calc aeval γ (c * ν) * aeval γ h = aeval γ c * (aeval γ h * aeval γ ν) := by
          rw [map_mul]; ring
      _ = algebraMap T V ϖ * (aeval γ c * aeval γ r) := by rw [hr]; ring
      _ = _ := by rw [he]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerResidueMemAdjoinUnit
section
open Polynomial IsLocalRing

namespace GlobalTheory

theorem kummer_residue_mem_adjoin (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)]
    (hinj : Function.Injective (algebraMap T V))
    (α γ : V) (ϖ : T) (m : ℕ) (hϖ : Irreducible ϖ) (hm : 0 < m) (hγ : IsUnit γ)
    (hα : α ^ m = γ * algebraMap T V ϖ)
    (hpol : ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h')
    (hgen : ∀ v : V, ∃ f g : Polynomial T, Polynomial.aeval α g ≠ 0 ∧
      Polynomial.aeval α g * v = Polynomial.aeval α f)
    (v : V) : IsLocalRing.residue V v ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField T) {IsLocalRing.residue V γ} := by
  set K := IntermediateField.adjoin (IsLocalRing.ResidueField T) {IsLocalRing.residue V γ} with hK
  have hγK : residue V γ ∈ K := IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have hres : ∀ p : T[X], residue V (aeval γ p) ∈ K := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      rw [aeval_C]
      have : residue V (algebraMap T V a) =
          algebraMap (ResidueField T) (ResidueField V) (residue T a) :=
        (ResidueField.map_residue _ a).symm
      rw [this]; exact K.algebraMap_mem _
    | add p q hp hq => rw [map_add (f := _), map_add (f := _)]; exact K.add_mem hp hq
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, map_mul]
      exact K.mul_mem ih hγK
  have hϖ0 : algebraMap T V ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap T V)]; exact fun h => hϖ.ne_zero (hinj h)
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hα
    exact mul_ne_zero hγ.ne_zero hϖ0 hα.symm
  have hαnu : ¬ IsUnit α := by
    intro h
    have h1 : IsUnit (γ * algebraMap T V ϖ) := hα ▸ h.pow m
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap T V) ϖ).1 (isUnit_of_mul_isUnit_right h1))
  have hsmall : ∀ k : ℕ, 0 < k → ∀ x : V, residue V (α ^ k * x) = 0 := by
    intro k hk x
    rw [residue_eq_zero_iff]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hαnu) k hk)
  have hcomb : ∀ (u u' : V) (k : ℕ), 0 < k → IsUnit u → residue V u ∈ K →
      IsUnit (u + α ^ k * u') ∧ residue V (u + α ^ k * u') ∈ K := by
    intro u u' k hk hu huK
    have e : residue V (u + α ^ k * u') = residue V u := by rw [map_add (f := _), hsmall k hk, add_zero]
    refine ⟨?_, e ▸ huK⟩
    rw [← residue_ne_zero_iff_isUnit, e, residue_ne_zero_iff_isUnit]; exact hu
  let Good : Finset ℕ → V → Prop := fun s x =>
    x = 0 ∨ ∃ n u, IsUnit u ∧ residue V u ∈ K ∧ n % m ∈ s ∧ x = α ^ n * u
  have hdec : ∀ p : T[X], ∃ a : ℕ → T[X],
      aeval α p = ∑ j ∈ Finset.range m, aeval γ (a j) * α ^ j := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp; obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by simp only [map_add (f := _), ha, hb, Pi.add_apply, add_mul, Finset.sum_add_distrib]⟩
    | monomial n t =>
      refine ⟨fun j => if j = n % m then C t * (C ϖ * X) ^ (n / m) else 0, ?_⟩
      simp only [apply_ite (aeval γ), ite_mul, map_zero, zero_mul, Finset.sum_ite_eq',
        Finset.mem_range, Nat.mod_lt _ hm, if_true]
      rw [aeval_monomial, map_mul, aeval_C, map_pow, map_mul, aeval_C, aeval_X]
      conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hα]
      ring
  have hterm : ∀ (a : T[X]) (j : ℕ), j < m → Good {j} (aeval γ a * α ^ j) := by
    intro a j hj
    rcases hpol a with h0 | ⟨b, h', c, hc, hh', hrel⟩
    · left; rw [h0, zero_mul]
    · right
      refine ⟨m * b + j, ((hγ.unit⁻¹ ^ b * hc.unit⁻¹ : Vˣ) : V) * aeval γ h',
        (Units.isUnit _).mul hh', ?_, ?_, ?_⟩
      · rw [map_mul, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, map_units_inv,
          map_units_inv, IsUnit.unit_spec, IsUnit.unit_spec]
        exact K.mul_mem (K.mul_mem (pow_mem (K.inv_mem hγK) b) (K.inv_mem (hres c))) (hres h')
      · rw [Finset.mem_singleton, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      · have e1 : (γ * ((hγ.unit⁻¹ : Vˣ) : V)) ^ b = 1 := by
          rw [IsUnit.mul_val_inv hγ, one_pow]
        have e2 : aeval γ c * ((hc.unit⁻¹ : Vˣ) : V) = 1 := by
          exact IsUnit.mul_val_inv hc
        rw [pow_add, pow_mul, hα, Units.val_mul, Units.val_pow_eq_pow_val]
        linear_combination (-(aeval γ a * α ^ j)) * e2 + (((hc.unit⁻¹ : Vˣ) : V) * α ^ j) * hrel
          + (-(algebraMap T V ϖ ^ b * aeval γ h' * ((hc.unit⁻¹ : Vˣ) : V) * α ^ j)) * e1
  have hsum : ∀ (a : ℕ → T[X]) (s : Finset ℕ), s ⊆ Finset.range m →
      Good s (∑ j ∈ s, aeval γ (a j) * α ^ j) := by
    intro a s
    induction s using Finset.induction_on with
    | empty => intro _; left; simp
    | insert j s hjs ih =>
      intro hsub
      rw [Finset.sum_insert hjs]
      have hj : j < m := Finset.mem_range.1 (hsub (Finset.mem_insert_self _ _))
      have ih' := ih ((Finset.subset_insert _ _).trans hsub)
      rcases hterm (a j) j hj with h0 | ⟨n, u, hu, huK, hn, he⟩
      · rw [h0, zero_add]
        rcases ih' with h | ⟨n', u', hu', hu'K, hn', he'⟩
        · left; exact h
        · right; exact ⟨n', u', hu', hu'K, Finset.mem_insert_of_mem hn', he'⟩
      · rw [Finset.mem_singleton] at hn
        rcases ih' with h | ⟨n', u', hu', hu'K, hn', he'⟩
        · right; rw [h, add_zero]
          exact ⟨n, u, hu, huK, hn ▸ Finset.mem_insert_self _ _, he⟩
        · right
          have hne : n ≠ n' := by rintro rfl; exact hjs (hn ▸ hn')
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · obtain ⟨h1, h2⟩ := hcomb u u' (n' - n) (Nat.sub_pos_of_lt hlt) hu huK
            refine ⟨n, _, h1, h2, hn ▸ Finset.mem_insert_self _ _, ?_⟩
            rw [he, he', mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
          · obtain ⟨h1, h2⟩ := hcomb u' u (n - n') (Nat.sub_pos_of_lt hlt) hu' hu'K
            refine ⟨n', _, h1, h2, Finset.mem_insert_of_mem hn', ?_⟩
            rw [he, he', mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le, add_comm]
  by_cases hv : IsUnit v
  · obtain ⟨f, g, hg0, hfg⟩ := hgen v
    obtain ⟨a, ha⟩ := hdec g
    obtain ⟨b, hb⟩ := hdec f
    have Gg := hsum a _ subset_rfl
    have Gf := hsum b _ subset_rfl
    rw [← ha] at Gg
    rw [← hb] at Gf
    rcases Gg with h | ⟨n, u, hu, huK, -, he⟩
    · exact absurd h hg0
    rcases Gf with h | ⟨n', u', hu', hu'K, -, he'⟩
    · exact absurd (hfg.trans h) (mul_ne_zero hg0 hv.ne_zero)
    rw [he, he'] at hfg
    have key : n = n' := by
      rcases lt_trichotomy n n' with h | h | h
      · exfalso
        have h2 : α ^ n * (u * v) = α ^ n * (α ^ (n' - n) * u') := by
          rw [← mul_assoc, hfg, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le]
        have h3 := mul_left_cancel₀ (pow_ne_zero n hα0) h2
        have h4 := hsmall (n' - n) (Nat.sub_pos_of_lt h) u'
        rw [← h3] at h4
        exact (residue_ne_zero_iff_isUnit _).2 (hu.mul hv) h4
      · exact h
      · exfalso
        have h2 : α ^ n' * (α ^ (n - n') * (u * v)) = α ^ n' * u' := by
          rw [← hfg, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le, mul_assoc]
        have h3 := mul_left_cancel₀ (pow_ne_zero n' hα0) h2
        have h4 := hsmall (n - n') (Nat.sub_pos_of_lt h) (u * v)
        rw [h3] at h4
        exact (residue_ne_zero_iff_isUnit _).2 hu' h4
    subst key
    have huv : u * v = u' := mul_left_cancel₀ (pow_ne_zero n hα0) (by rw [← mul_assoc, hfg])
    have hr : residue V u * residue V v = residue V u' := by rw [← map_mul, huv]
    have hru : residue V u ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hu
    have : residue V v = residue V u' / residue V u := by
      rw [← hr]; field_simp
    rw [this]; exact K.div_mem hu'K huK
  · rw [(residue_eq_zero_iff v).2 ((mem_maximalIdeal _).2 hv)]; exact K.zero_mem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerUnitRadicandQuotientRootIsReduced
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem kummerUnit_quotRoot_isReduced : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A) (u : Aˣ) (m k : ℕ), Irreducible ϖ → IsUnit (m : A) → 0 < k → IsReduced (AdjoinRoot (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A))) ⧸ Ideal.span {AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)))}) := by
  intro A _ _ _ ϖ u m k hϖ hm hk
  set f : A[X] := X ^ m - C (u : A) with hf
  set c : AdjoinRoot f := AdjoinRoot.of f ϖ * AdjoinRoot.root f with hc
  set g : (AdjoinRoot f)[X] := X ^ k - C c with hg
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hy : IsUnit (AdjoinRoot.root f) := by
    have h0 := AdjoinRoot.eval₂_root f
    have h1 : AdjoinRoot.root f ^ m = AdjoinRoot.of f (u : A) := by
      rw [hf] at h0
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0
      exact sub_eq_zero.mp h0
    have h2 : IsUnit (AdjoinRoot.root f ^ m) := by
      rw [h1]; exact (u.isUnit.map _)
    exact (isUnit_pow_iff hm0).mp h2
  have hspan : Ideal.span {c} = (Ideal.span {ϖ}).map (AdjoinRoot.of f) := by
    rw [Ideal.map_span, Set.image_singleton, hc]
    exact Ideal.span_singleton_mul_right_unit hy _
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (A ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hredK : IsReduced ((A ⧸ Ideal.span {ϖ})[X] ⧸ Ideal.span {f.map (Ideal.Quotient.mk (Ideal.span {ϖ}))}) := by
    rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
    apply Squarefree.isRadical
    apply Polynomial.Separable.squarefree
    have hmap : f.map (Ideal.Quotient.mk (Ideal.span {ϖ})) =
        X ^ m - C ((Units.map (Ideal.Quotient.mk (Ideal.span {ϖ})).toMonoidHom u : (A ⧸ Ideal.span {ϖ})ˣ) : A ⧸ Ideal.span {ϖ}) := by
      simp [hf, Polynomial.map_sub]
    rw [hmap]
    apply separable_X_pow_sub_C_unit
    simpa using hm.map (Ideal.Quotient.mk (Ideal.span {ϖ}))
  have hred1 : IsReduced (AdjoinRoot f ⧸ Ideal.span {c}) := by
    have e := (Ideal.quotEquivOfEq hspan).trans (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (Ideal.span {ϖ}) f)
    exact isReduced_of_injective e.toRingHom e.injective
  have hgroot : AdjoinRoot.of g c = AdjoinRoot.root g ^ k := by
    have h0 := AdjoinRoot.eval₂_root g
    rw [hg] at h0
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0
    exact (sub_eq_zero.mp h0).symm
  let φ0 : AdjoinRoot g →+* AdjoinRoot f ⧸ Ideal.span {c} :=
    AdjoinRoot.lift (Ideal.Quotient.mk (Ideal.span {c})) 0 (by
      rw [hg]
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, zero_pow hk.ne', zero_sub, neg_eq_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c))
  let φ : AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.root g} →+* AdjoinRoot f ⧸ Ideal.span {c} :=
    Ideal.Quotient.lift _ φ0 (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [φ0])
  let ψ : AdjoinRoot f ⧸ Ideal.span {c} →+* AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.root g} :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (AdjoinRoot.of g)) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [RingHom.comp_apply, map_mul, hgroot, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) k hk))
  have hcomp : ψ.comp φ = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply AdjoinRoot.ringHom_ext
    · ext <;> simp [φ, φ0, ψ]
    · simp [φ, φ0, ψ]
  have hinj : Function.Injective φ := by
    intro x y hxy
    have := congrArg ψ hxy
    simpa [← RingHom.comp_apply, hcomp] using this
  exact isReduced_of_injective φ hinj

end GlobalTheory
end

