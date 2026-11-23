module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomWProd
section
noncomputable def UpperTheory.Reformulated.B.Qi22.wsum.{v} :
    {ι : Type v} → (ι → ℤ) → (ι →₀ ℕ) → ℤ :=
    fun {ι : Type v} (w : ι → ℤ) (n : ι →₀ ℕ) ↦ n.sum fun (x : ι) (k : ℕ) ↦ (↑k : ℤ) * w x

noncomputable def UpperTheory.Reformulated.B.Qi22.HomW.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → (ι → ℤ) → ℤ → MvPowerSeries ι K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (w : ι → ℤ) (c : ℤ) (f : MvPowerSeries ι K) ↦
      ∀ (n : ι →₀ ℕ), (MvPowerSeries.coeff n : MvPowerSeries ι K → K) f ≠ (0 : K) → UpperTheory.Reformulated.B.Qi22.wsum w n = c

private theorem UpperTheory.Reformulated.B.Qi22.wsum_add {ι : Type*} (w : ι → ℤ) (a b : ι →₀ ℕ) :
    UpperTheory.Reformulated.B.Qi22.wsum w (a + b) = UpperTheory.Reformulated.B.Qi22.wsum w a + UpperTheory.Reformulated.B.Qi22.wsum w b := by
  unfold UpperTheory.Reformulated.B.Qi22.wsum
  apply Finsupp.sum_add_index'
  · intro x; simp
  · intro x p q; push_cast; ring

private theorem UpperTheory.Reformulated.B.Qi22.homW_one {K : Type*} [NormedField K] {ι : Type*} (w : ι → ℤ) :
    UpperTheory.Reformulated.B.Qi22.HomW w 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n hn
  have h0 : n = 0 := by
    by_contra h
    exact hn (by rw [MvPowerSeries.coeff_one, if_neg h])
  subst h0
  simp [UpperTheory.Reformulated.B.Qi22.wsum]

private theorem UpperTheory.Reformulated.B.Qi22.homW_mul {K : Type*} [NormedField K] {ι : Type*} {w : ι → ℤ}
    {c d : ℤ} {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qi22.HomW w c f)
    (hg : UpperTheory.Reformulated.B.Qi22.HomW w d g) : UpperTheory.Reformulated.B.Qi22.HomW w (c + d) (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hsum : p.1 + p.2 = n := by simpa using hp
  rw [← hsum, UpperTheory.Reformulated.B.Qi22.wsum_add, hf p.1 (left_ne_zero_of_mul hne),
    hg p.2 (right_ne_zero_of_mul hne)]

theorem UpperTheory.Reformulated.B.Qi22.homW_prod.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} {w : ι → ℤ} {α : Type w} (s : Finset α) (c : α → ℤ)
      (F : α → MvPowerSeries ι K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi22.HomW w (c i) (F i)) → UpperTheory.Reformulated.B.Qi22.HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by
  intro K inst ι w α s c F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using UpperTheory.Reformulated.B.Qi22.homW_one (K := K) w
  | insert a s ha ih =>
    intro h
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qi22.homW_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomologyFiniteShortExact
section
open CategoryTheory

namespace UpperTheory

universe v u w

private lemma finite_middle {R : Type u} [Ring R] {M₁ M₂ M₃ : Type v}
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : Function.Exact f g)
    [IsNoetherianRing R] [Module.Finite R M₁] [Module.Finite R M₃] :
    Module.Finite R M₂ := by
  have hk : Module.Finite R (LinearMap.ker g) := by
    rw [LinearMap.exact_iff.1 h]
    exact Module.Finite.range f
  have : IsNoetherian R M₃ := isNoetherian_of_isNoetherianRing_of_finite R M₃
  have hq : Module.Finite R (M₂ ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

theorem homology_finite_short_exact {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)} (hS : S.ShortExact) (i : ι) :
    (Finite (S.X₁.homology i) → Finite (S.X₃.homology i) → Finite (S.X₂.homology i)) ∧
    (IsNoetherianRing R → Module.Finite R (S.X₁.homology i) →
      Module.Finite R (S.X₃.homology i) → Module.Finite R (S.X₂.homology i)) := by
  have hE := hS.homology_exact₂ i
  refine ⟨fun h₁ h₃ ↦ ?_, fun _ h₁ h₃ ↦ ?_⟩
  · exact AddCommGrpCat.isFinite.prop_X₂_of_exact
      (hE.map (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})) h₁ h₃
  · exact finite_middle _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hE)

end UpperTheory
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HsSum
section
noncomputable def UpperTheory.Reformulated.B.Qh70.Hs :
    {L V ι : Type} →
      [inst : Field L] →
        [inst_1 : Algebra ℂ L] →
          [inst_2 : AddCommGroup V] → [_root_.Module L V] → Subalgebra ℂ L → Finset ι → (ι → V) → V → Prop :=
    fun {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [_root_.Module L V] (B : Subalgebra ℂ L) (P : Finset ι)
        (g : ι → V) (w : V) ↦
      ∃ (c : ι → L), (∀ (S : ι), c S ∈ B) ∧ w = ∑ S ∈ P, c S • g S

theorem UpperTheory.Reformulated.B.Qh70.Hs_sum :
    ∀ {L V ι : Type} [inst : Field L] [inst_1 : Algebra ℂ L] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module L V]
      {B : Subalgebra ℂ L} {P : Finset ι} {g : ι → V} {α : Type} (s : Finset α) (f : α → V),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qh70.Hs B P g (f a)) → UpperTheory.Reformulated.B.Qh70.Hs B P g (∑ a ∈ s, f a) := by
  intro L V ι _ _ _ _ B P g α s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh70.Hs B P g) ?_ ?_ h
  · rintro a b ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨fun S => c S + d S, fun S => B.add_mem (hc S) (hd S), ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
  · exact ⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HwvLoweringSpanLower
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk30.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qk30.loweringMonoid.{u_1, u_2} :
    {n : ℕ} →
      {K : Type u_1} →
        {V : Type u_2} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → Submonoid (Module.End K V) :=
    fun {n : ℕ} {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) ↦
      Submonoid.closure {g : Module.End K V | ∃ (c : Fin n), ∃ d < c, g = E c d}

noncomputable def UpperTheory.Reformulated.B.Qk30.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

noncomputable def UpperTheory.Reformulated.B.Qk30.IsHWV.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → (Fin n → ℤ) → V → Prop :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (lam : Fin n → ℤ) (v : V) ↦
      v ≠ (0 : V) ∧ v ∈ UpperTheory.Reformulated.B.Qk30.weightSp E lam ∧ ∀ (a b : Fin n), a < b → (E a b : V → V) v = (0 : V)

noncomputable def UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan.{u_1, u_2} :
    {n : ℕ} →
      {K : Type u_1} →
        {V : Type u_2} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (mu : Fin n → ℤ) ↦
      Submodule.span K
        {x : V | ∃ u ∈ UpperTheory.Reformulated.B.Qk30.loweringMonoid E, ∃ (w : V), UpperTheory.Reformulated.B.Qk30.IsHWV E mu w ∧ x = (u : V → V) w}

theorem UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n},
      b < a → ∀ {x : V}, x ∈ UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan E mu := by
  intro n K V _ _ _ E mu a b hab x hx
  unfold UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    refine Submodule.subset_span ⟨E a b * u, ?_, w, hw, rfl⟩
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨a, b, hab, rfl⟩) hu
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImagOfSq
section
theorem UpperTheory.Reformulated.B.Qh67.imag_of_sq :
    ∀ {c : ℂ} {d : ℕ},
    (0 : ℕ) < d → c ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) c = -c ∧ c ≠ (0 : ℂ) := by
  intro c d hd h
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : c.re * c.re - c.im * c.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have h2 : c.re * c.im + c.im * c.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h3 : c.re * c.im = 0 := by linarith [mul_comm c.re c.im]
  have hre : c.re = 0 := by
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · rw [h4] at h1
      nlinarith [mul_self_nonneg c.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext
    · simp [hre]
    · simp
  · rintro rfl
    simp at h1
    omega
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Imports
section
theorem UpperTheory.Reformulated.B.DYda8.main :
    ∀ (E : Type) [inst : Field E] [inst_1 : NumberField E] [IsGalois ℚ E],
      (∀ (a b : Gal(E/ℚ)), a * b = b * a) →
        ∀ (p : ℕ),
          Nat.Prime p →
            ∃ (φ : Gal(E/ℚ)),
              ∀ (O : Type) [inst_3 : CommRing O] (n : Ideal O),
                n.IsPrime →
                  (↑p : O) ∈ n →
                    ∀ (τ : NumberField.RingOfIntegers E →+* O) (x : NumberField.RingOfIntegers E),
                      (τ : NumberField.RingOfIntegers E → O)
                            ((NumberField.RingOfIntegers.mapRingEquiv φ.toRingEquiv :
                                NumberField.RingOfIntegers E → NumberField.RingOfIntegers E)
                              x) -
                          (τ : NumberField.RingOfIntegers E → O) x ^ p ∈
                        n := by
  intro E _ _ _ hc p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    simpa using hp.ne_zero
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hp)) hp0
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := NumberField.RingOfIntegers E) (Ideal.span {(p : ℤ)})
  have hQbot : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q
  haveI : Finite (NumberField.RingOfIntegers E ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(E/ℚ) Q
  refine ⟨φ, ?_⟩
  intro O _ n hn hpn τ x
  have hP : (n.comap τ).IsPrime := Ideal.comap_isPrime τ n
  have hle : Ideal.span {(p : ℤ)} ≤ (n.comap τ).under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap]
    simpa using hpn
  have hund : (n.comap τ).under ℤ = Ideal.span {(p : ℤ)} :=
    (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have hund' : Q.under ℤ = Ideal.span {(p : ℤ)} := hQo.over.symm
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ℤ (NumberField.RingOfIntegers E)
    Gal(E/ℚ) Q (n.comap τ) (hund'.trans hund.symm)
  have hcj := hφ.conj g
  have hcomm : g * φ * g⁻¹ = φ := by
    rw [hc g φ, mul_assoc, mul_inv_cancel, mul_one]
  rw [hcomm, ← hg] at hcj
  have hx := hcj x
  rw [hund] at hx
  rw [Int.card_ideal_quot, Ideal.mem_comap] at hx
  have he : (MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers E) φ) x =
      NumberField.RingOfIntegers.mapRingEquiv φ.toRingEquiv x := by
    ext
    rfl
  rw [he, map_sub, map_pow] at hx
  exact hx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsAlt
section
theorem UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main :
    ∀ {d : ℕ}, (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have h := congrArg Complex.re hz
    simpa [pow_two] using h
  have him : z.re * z.im + z.im * z.re = 0 := by
    have h := congrArg Complex.im hz
    simpa [pow_two] using h
  have hprod : z.re * z.im = 0 := by linarith
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [hre0]
  · simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBis
section
theorem UpperTheory.Reformulated.B.DYdc4.main :
    ∀ (n a : ℕ) (G : Finset (Fin n)),
      G.card = a → ∃ (τ : Equiv.Perm (Fin n)), ∀ (j : Fin n), (↑j : ℕ) < a ↔ (τ : Fin n → Fin n) j ∈ G := by
  intro n a G hG
  have ha : a ≤ n := by
    have h := G.card_le_univ
    rw [Fintype.card_fin, hG] at h
    exact h
  have hp : Fintype.card {x : Fin n // (x : ℕ) < a} = a := by
    have e : Fin a ≃ {x : Fin n // (x : ℕ) < a} :=
      { toFun := fun i => ⟨Fin.castLE ha i, i.isLt⟩
        invFun := fun x => ⟨x.1.1, x.2⟩
        left_inv := fun i => rfl
        right_inv := fun x => rfl }
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hq : Fintype.card {x : Fin n // x ∈ G} = a := by
    rw [Fintype.card_coe, hG]
  let e : {x : Fin n // (x : ℕ) < a} ≃ {x : Fin n // x ∈ G} :=
    Fintype.equivOfCardEq (hp.trans hq.symm)
  refine ⟨e.extendSubtype, fun j => ⟨fun h => e.extendSubtype_mem j h, fun h => ?_⟩⟩
  by_contra h'
  exact e.extendSubtype_not_mem j h' h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisAlt
section
theorem UpperTheory.Reformulated.B.DYhc4.main :
    ∀ {K A : Type} [inst : Field K] [inst_1 : CommRing A] [inst_2 : Algebra K A] [Algebra.FiniteType K A] (σ : K →+* ℂ)
      (p : Ideal A) [hp : p.IsPrime] {b : A},
      b ∉ p →
        ∃ (ψ : A →+* ℂ), ψ.comp (Algebra.algebraMap K A) = σ ∧ (∀ a ∈ p, (ψ : A → ℂ) a = (0 : ℂ)) ∧ (ψ : A → ℂ) b ≠ (0 : ℂ) := by
  intro K A _ _ _ _ σ p hp b hb
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  have hj : p.jacobson = p := IsJacobsonRing.out' p hp.isRadical
  have hex : ∃ m : Ideal A, p ≤ m ∧ m.IsMaximal ∧ b ∉ m := by
    by_contra h
    push_neg at h
    apply hb
    rw [← hj]
    refine Ideal.mem_sInf.2 ?_
    rintro J ⟨hpJ, hJ⟩
    exact h J hpJ hJ
  obtain ⟨m, hpm, hm, hbm⟩ := hex
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  letI : Algebra K ℂ := σ.toAlgebra
  let f : (A ⧸ m) →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(f : (A ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m), ?_, ?_, ?_⟩
  · ext x
    have h1 : Ideal.Quotient.mk m (algebraMap K A x) = algebraMap K (A ⧸ m) x := rfl
    have h2 : f (algebraMap K (A ⧸ m) x) = algebraMap K ℂ x := f.commutes x
    exact h2
  · intro a ha
    have : Ideal.Quotient.mk m a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hpm ha)
    simp [this]
  · intro h0
    have h1 : f (Ideal.Quotient.mk m b) = 0 := h0
    have h2 : Ideal.Quotient.mk m b = 0 := by
      simpa using (map_eq_zero f).1 h1
    exact hbm (Ideal.Quotient.eq_zero_iff_mem.1 h2)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisBis
section
noncomputable def UpperTheory.Reformulated.B.DYhc9.IsLat :
    {E : Type} → [inst : Field E] → {N : ℕ} → Submodule (NumberField.RingOfIntegers E) (Fin N → E) → Prop :=
    fun {E : Type} [Field E] {N : ℕ} (Λ : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) ↦
      Λ.FG ∧ Submodule.span E (↑Λ : Set (Fin N → E)) = ⊤

private theorem UpperTheory.Reformulated.B.DYhc9.exists_denom {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  have halg : IsAlgebraic ℤ a := by
    have : Algebra.IsAlgebraic ℤ E :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).mpr inferInstance
    exact Algebra.IsAlgebraic.isAlgebraic a
  obtain ⟨r, hr, hint⟩ := halg.exists_integral_multiple
  have hint' : IsIntegral ℤ ((r : E) * a) := by simpa [zsmul_eq_mul] using hint
  refine ⟨r.natAbs, Int.natAbs_ne_zero.mpr hr, ?_⟩
  rcases Int.natAbs_eq r with h | h
  · have : ((r.natAbs : E)) = (r : E) := by
      conv_rhs => rw [h]
      simp
    rwa [this]
  · have : ((r.natAbs : E)) = -(r : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]
    exact hint'.neg

theorem UpperTheory.Reformulated.B.DYhc9.main :
    ∀ {E : Type} [inst : Field E] [NumberField E] {N : ℕ} {Λ : Submodule (NumberField.RingOfIntegers E) (Fin N → E)},
      UpperTheory.Reformulated.B.DYhc9.IsLat Λ → ∀ (x : Fin N → E), ∃ (m : ℕ), m ≠ (0 : ℕ) ∧ (↑m : E) • x ∈ Λ := by
  intro E _ _ N Λ h x
  have hx : x ∈ Submodule.span E (Λ : Set (Fin N → E)) := by
    rw [h.2]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hmy⟩ := hy
    obtain ⟨n, hn, hnz⟩ := hz
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have key : ((m * n : ℕ) : E) • (y + z) = n • ((m : E) • y) + m • ((n : E) • z) := by
      ext i
      simp
      ring
    rw [key]
    exact Λ.add_mem (nsmul_mem hmy n) (nsmul_mem hnz m)
  | smul a y _ hy =>
    obtain ⟨m, hm, hmy⟩ := hy
    obtain ⟨d, hd, hint⟩ := UpperTheory.Reformulated.B.DYhc9.exists_denom a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    obtain ⟨b, hb⟩ : ∃ b : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E b = (d : E) * a :=
      ⟨_, IsIntegralClosure.algebraMap_mk' _ _ hint⟩
    have key : ((d * m : ℕ) : E) • (a • y) = b • ((m : E) • y) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Algebra.smul_def, hb]
      push_cast
      ring
    rw [key]
    exact Λ.smul_mem _ hmy
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisExtra
section
theorem UpperTheory.Reformulated.B.DYlb5.main :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {n : ℕ} (f : Module.Dual k (Matrix (Fin n) (Fin n) k)), Continuous (⇑f : Matrix (Fin n) (Fin n) k → k) := by
  intro k _ _ _ _ n f
  haveI : IsTopologicalRing k := inferInstance
  have key : ∀ M : Matrix (Fin n) (Fin n) k,
      f M = ∑ i, ∑ j, M i j * f (Matrix.single i j 1) := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (M i j) = (M i j) • Matrix.single i j (1 : k) := by
      simp [Matrix.smul_single]
    rw [this, map_smul, smul_eq_mul]
  have : (⇑f : Matrix (Fin n) (Fin n) k → k) =
      fun M => ∑ i, ∑ j, M i j * f (Matrix.single i j 1) := funext key
  rw [this]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_id.matrix_elem i j).mul continuous_const
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSumLt
section
theorem UpperTheory.Reformulated.B.Qe17.norm_sum_lt :
    ∀ {F ι : Type} [inst : NormedField F] [IsUltrametricDist F]
    (s : Finset ι) (f : ι → F) {C : ℝ}, (0 : ℝ) < C → (∀ i ∈ s, ‖f i‖ < C) → ‖∑ i ∈ s, f i‖ < C := by
  intro F ι _ _ s f C hC h
  refine Finset.sum_induction f (fun x => ‖x‖ < C) ?_ ?_ h
  · intro a b ha hb
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)
  · simpa using hC
end

