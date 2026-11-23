module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpDiagMul
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe40.M4 :
    Type → Type :=
    fun (R : Type) ↦ Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) R

noncomputable def UpperTheory.Reformulated.B.Qe40.IsUp :
    {R : Type} → [CommRing R] → UpperTheory.Reformulated.B.Qe40.M4 R → Prop :=
    fun {R : Type} [CommRing R] (X : UpperTheory.Reformulated.B.Qe40.M4 R) ↦ ∀ (i j : Fin (4 : ℕ)), j < i → X i j = (0 : R)

theorem UpperTheory.Reformulated.B.Qe40.up_diag_mul :
    ∀ {R : Type} [inst : CommRing R] {X Y : UpperTheory.Reformulated.B.Qe40.M4 R},
      UpperTheory.Reformulated.B.Qe40.IsUp X → UpperTheory.Reformulated.B.Qe40.IsUp Y → ∀ (i : Fin (4 : ℕ)), (X * Y) i i = X i i * Y i i := by
  intro R _ X Y hX hY i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hX i k h, zero_mul]
  · rw [hY k i h, mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpUMul
section
noncomputable def UpperTheory.Reformulated.B.Qh21.UpU.{u_1} :
    {K : Type u_1} → [Field K] → {N : ℕ} → Matrix (Fin N) (Fin N) K → Prop :=
    fun {K : Type u_1} [Field K] {N : ℕ} (U : Matrix (Fin N) (Fin N) K) ↦
      ∀ (i j : Fin N), (j < i → U i j = (0 : K)) ∧ (i = j → U i j = (1 : K))

theorem UpperTheory.Reformulated.B.Qh21.upU_mul.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] {N : ℕ} {A B : Matrix (Fin N) (Fin N) K},
      UpperTheory.Reformulated.B.Qh21.UpU A → UpperTheory.Reformulated.B.Qh21.UpU B → UpperTheory.Reformulated.B.Qh21.UpU (A * B) := by
  intro K _ N A B hA hB i j
  have hz : j ≤ i → ∀ k : Fin N, k ≠ i → A i k * B k j = 0 := by
    intro hji k hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [(hA i k).1 h, zero_mul]
    · rw [(hB k j).1 (lt_of_le_of_lt hji h), mul_zero]
  have hs : j ≤ i → (A * B) i j = B i j := by
    intro hji
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => hz hji k hk)
      (fun h => absurd (Finset.mem_univ i) h), (hA i i).2 rfl, one_mul]
  exact ⟨fun h => (hs h.le).trans ((hB i j).1 h), fun h => (hs h.ge).trans ((hB i j).2 h)⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ValPrimeOfLt
section
theorem UpperTheory.Reformulated.B.Qi55.val_prime_of_lt :
    ∀ {Ω : Type} [inst : Field Ω]
    (A : ValuationSubring Ω) (n : ℕ),
    n ≠ (0 : ℕ) →
      (A.valuation : Ω → A.ValueGroup) (↑n : Ω) < (1 : A.ValueGroup) →
        ∃ (t : ℕ), Nat.Prime t ∧ t ∣ n ∧ (A.valuation : Ω → A.ValueGroup) (↑t : Ω) < (1 : A.ValueGroup) := by
  intro Ω _ A n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ h; simp at h
  | prime_mul p a hp ih =>
    intro hne h
    have ha : a ≠ 0 := right_ne_zero_of_mul hne
    by_cases hpv : A.valuation (p : Ω) < 1
    · exact ⟨p, hp, dvd_mul_right p a, hpv⟩
    · have hav : A.valuation (a : Ω) < 1 := by
        by_contra hc
        rw [Nat.cast_mul, map_mul] at h
        exact absurd h (not_lt.mpr (one_le_mul (not_lt.mp hpv) (not_lt.mp hc)))
      obtain ⟨t, ht, hd, hv⟩ := ih ha hav
      exact ⟨t, ht, hd.mul_left p, hv⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VandermondeOfEqDet
section
noncomputable def UpperTheory.Reformulated.B.Qm12.vandermondeOf.{u_1} :
    {R : Type u_1} → [CommRing R] → {m : ℕ} → (Fin m → R) → R :=
    fun {R : Type u_1} [CommRing R] {m : ℕ} (v : Fin m → R) ↦ ∏ i : Fin m, ∏ j > i, (v i - v j)

theorem UpperTheory.Reformulated.B.Qm12.vandermondeOf_eq_det.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (v : Fin m → R),
      UpperTheory.Reformulated.B.Qm12.vandermondeOf v =
        ((Matrix.of : (Fin m → Fin m → R) → Matrix (Fin m) (Fin m) R) fun (i j : Fin m) ↦
            v i ^ (m - (1 : ℕ) - (↑j : ℕ))).det := by
  intro m R _ v
  have hM : ((Matrix.of : (Fin m → Fin m → R) → Matrix (Fin m) (Fin m) R) fun (i j : Fin m) ↦
      v i ^ (m - (1 : ℕ) - (↑j : ℕ))) = Matrix.projVandermonde (fun _ ↦ (1 : R)) v := by
    ext i j
    rw [Matrix.of_apply, Matrix.projVandermonde_apply, one_pow, one_mul, Fin.val_rev,
      Nat.sub_sub, Nat.add_comm]
  rw [hM, Matrix.det_projVandermonde]
  unfold UpperTheory.Reformulated.B.Qm12.vandermondeOf
  refine Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr ?_ fun j _ ↦ ?_
  · ext j
    simp
  · rw [one_mul, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VolumePreservingUncurry
section
theorem UpperTheory.Reformulated.B.VolumePreservingUncurry.volume_preserving_uncurry.{u_1, u_2} :
    ∀ (ι : Type u_1) (κ : Type u_2) [inst : Fintype ι] [inst_1 : Fintype κ],
      @MeasureTheory.MeasurePreserving (ι → κ → Real) (Prod ι κ → Real)
        (@MeasureTheory.MeasureSpace.toMeasurableSpace (ι → κ → Real)
          (@MeasureTheory.MeasureSpace.pi ι inst (fun (a : ι) ↦ κ → Real) fun (i : ι) ↦
            @MeasureTheory.MeasureSpace.pi κ inst_1 (fun (a : κ) ↦ Real) fun (i : κ) ↦ Real.measureSpace))
        (@MeasureTheory.MeasureSpace.toMeasurableSpace (Prod ι κ → Real)
          (@MeasureTheory.MeasureSpace.pi (Prod ι κ) (@instFintypeProd ι κ inst inst_1) (fun (a : Prod ι κ) ↦ Real)
            fun (i : Prod ι κ) ↦ Real.measureSpace))
        (@Function.uncurry ι κ Real)
        (@MeasureTheory.MeasureSpace.volume (ι → κ → Real)
          (@MeasureTheory.MeasureSpace.pi ι inst (fun (a : ι) ↦ κ → Real) fun (i : ι) ↦
            @MeasureTheory.MeasureSpace.pi κ inst_1 (fun (a : κ) ↦ Real) fun (i : κ) ↦ Real.measureSpace))
        (@MeasureTheory.MeasureSpace.volume (Prod ι κ → Real)
          (@MeasureTheory.MeasureSpace.pi (Prod ι κ) (@instFintypeProd ι κ inst inst_1) (fun (a : Prod ι κ) ↦ Real)
            fun (i : Prod ι κ) ↦ Real.measureSpace)) := by
  intro ι κ _ _
  have hm : Measurable (@Function.uncurry ι κ ℝ) :=
    Measurable.of_eval fun p ↦ (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine ⟨hm, ?_⟩
  symm
  refine MeasureTheory.Measure.pi_eq (μ := fun _ : ι × κ ↦ (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ?_
  intro s hs
  rw [MeasureTheory.Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (@Function.uncurry ι κ ℝ) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi fun i ↦ Set.univ.pi fun k ↦ s (i, k) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall,
      Function.uncurry_apply_pair]
  rw [hpre, MeasureTheory.volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [MeasureTheory.volume_pi_pi]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightComponentsMemInvariant
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf7.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qf7.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf7.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf7.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

private theorem UpperTheory.Reformulated.B.Qf7.apply_of_mem_weightSp {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V]
    [_root_.Module K V] {E : UpperTheory.Reformulated.B.Qf7.GLOps n K V} {mu : Fin n → ℤ} {x : V}
    (hx : x ∈ UpperTheory.Reformulated.B.Qf7.weightSp E mu) (a : Fin n) : E a a x = (mu a : K) • x := by
  unfold UpperTheory.Reformulated.B.Qf7.weightSp at hx
  have h := (Submodule.mem_iInf _).1 hx a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at h
  exact h

theorem UpperTheory.Reformulated.B.Qf7.weight_components_mem_invariant.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      [CharZero K] (E : UpperTheory.Reformulated.B.Qf7.GLOps n K V) (W : Submodule K V),
      (∀ (a : Fin n), ∀ x ∈ W, (E a a : V → V) x ∈ W) →
        ∀ (s : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V),
          (∀ mu ∈ s, f mu ∈ UpperTheory.Reformulated.B.Qf7.weightSp E mu) → ∑ mu ∈ s, f mu ∈ W → ∀ mu ∈ s, f mu ∈ W := by
  intro n K V _ _ _ _ E W hW s
  classical
  induction s using Finset.induction_on with
  | empty => intro f _ _ mu hmu; simp at hmu
  | insert nu t hnu ih =>
    intro f hf hsum
    have ht : ∀ mu ∈ t, f mu ∈ W := by
      intro mu hmu
      have hne : mu ≠ nu := fun h => hnu (h ▸ hmu)
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
      have h1 : E a a (∑ l ∈ insert nu t, f l) - (nu a : K) • (∑ l ∈ insert nu t, f l) ∈ W :=
        W.sub_mem (hW a _ hsum) (W.smul_mem _ hsum)
      have h2 : E a a (∑ l ∈ insert nu t, f l) - (nu a : K) • (∑ l ∈ insert nu t, f l)
          = ∑ l ∈ insert nu t, ((l a : K) - (nu a : K)) • f l := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [UpperTheory.Reformulated.B.Qf7.apply_of_mem_weightSp (hf l hl) a, sub_smul]
      rw [h2, Finset.sum_insert hnu, sub_self, zero_smul, zero_add] at h1
      have h3 := ih (fun l => ((l a : K) - (nu a : K)) • f l)
        (fun l hl => Submodule.smul_mem _ _ (hf l (Finset.mem_insert_of_mem hl))) h1 mu hmu
      have hc : ((mu a : K) - (nu a : K)) ≠ 0 :=
        sub_ne_zero.2 (fun h => ha (Int.cast_injective h))
      exact (W.smul_mem_iff hc).1 h3
    intro mu hmu
    rcases Finset.mem_insert.1 hmu with rfl | hmu
    · rw [Finset.sum_insert hnu] at hsum
      exact (W.add_mem_iff_left (W.sum_mem ht)).1 hsum
    · exact ht mu hmu
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightedHomogeneousMap
section
theorem UpperTheory.aeval_map_eq_rename_map_iff :
    ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S), Function.Injective φ → ∀ (σ M : Type) [AddCommMonoid M] (w : σ → M) (ν : M) (f : MvPolynomial σ R), (MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.map φ f) ν ↔ MvPolynomial.IsWeightedHomogeneous w f ν) ∧ ∀ (τ : Type) (gR : σ → MvPolynomial τ R) (gS : σ → MvPolynomial τ S) (ρ : σ → τ), (∀ v, MvPolynomial.map φ (gR v) = gS v) → (MvPolynomial.aeval gS (MvPolynomial.map φ f) = MvPolynomial.rename ρ (MvPolynomial.map φ f) ↔ MvPolynomial.aeval gR f = MvPolynomial.rename ρ f) := by
  intro R S _ _ φ hφ σ M _ w ν f
  refine ⟨?_, ?_⟩
  · unfold MvPolynomial.IsWeightedHomogeneous
    refine forall_congr' fun d => ?_
    rw [MvPolynomial.coeff_map, map_ne_zero_iff φ hφ]
  · intro τ gR gS ρ hg
    have hgS : gS = fun v => MvPolynomial.map φ (gR v) := funext fun v => (hg v).symm
    subst hgS
    rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_eq_bind₁, ← MvPolynomial.map_bind₁,
      ← MvPolynomial.map_rename]
    exact (MvPolynomial.map_injective φ hφ).eq_iff
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightedSumBis
section
open scoped ContDiff

namespace UpperTheory.Reformulated.B.weightedSumBis

theorem exists_eq_exp (f : ℝ → ℂ) (hc : Continuous f) (h0 : f 0 = 1) (hm : ∀ x y, f (x + y) = f x * f y) :
    ∃ c : ℂ, ∀ x : ℝ, f x = Complex.exp (c * x) := by
  set F : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..u, f t with hF
  have hFd : ∀ u, HasDerivAt F (f u) u := fun u =>
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  obtain ⟨a, ha⟩ : ∃ a, F a ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : F = fun _ => 0 := funext h
    have h2 := hFd 0
    rw [h1, h0] at h2
    exact one_ne_zero (h2.unique (hasDerivAt_const _ _))
  have key : ∀ x, f x = (F (x + a) - F x) / F a := by
    intro x
    rw [eq_div_iff ha]
    have h1 : F (x + a) - F x = ∫ t in x..(x + a), f t :=
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)
    have h2 : ∫ t in (0 : ℝ)..a, f (x + t) = ∫ t in x..(x + a), f t := by
      simp
    rw [h1, ← h2]
    simp only [hm, hF]
    rw [intervalIntegral.integral_const_mul]
  set c : ℂ := (f a - 1) / F a with hcdef
  have hfd : ∀ x, HasDerivAt f (c * f x) x := by
    intro x
    have h1 : HasDerivAt (fun y => (F (y + a) - F y) / F a) ((f (x + a) - f x) / F a) x :=
      (((hFd (x + a)).comp_add_const x a).sub (hFd x)).div_const _
    rw [← funext key] at h1
    convert h1 using 1
    rw [hm, hcdef]
    ring
  have hg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f y * Complex.exp (-c * y)) 0 x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (-c * y)) (Complex.exp (-c * x) * (-c * 1)) x :=
      ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-c)).cexp
    have h2 := (hfd x).mul h1
    have h3 : c * f x * Complex.exp (-c * x) + f x * (Complex.exp (-c * x) * (-c * 1)) = 0 := by
      ring
    rw [h3] at h2
    exact h2
  refine ⟨c, fun x => ?_⟩
  have h := is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt)
    (fun y => (hg y).deriv) x 0
  simp only [h0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  rw [neg_mul, Complex.exp_neg] at h
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp h

end UpperTheory.Reformulated.B.weightedSumBis
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightsCompactStabilizer
section
noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.GlRel.{u_1} :
    {A : Type u_1} → [Ring A] → {n : ℕ} → (Fin n → Fin n → A) → Prop :=
    fun {A : Type u_1} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) ↦
      ∀ (a b c d : Fin n),
        E a b * E c d - E c d * E a b = (if b = c then E a d else (0 : A)) - if d = a then E c b else (0 : A)

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.KUnit :
    {n : ℕ} →
      {V : Type} →
        [inst : NormedAddCommGroup V] →
          [inst_1 : InnerProductSpace ℂ V] → (Fin n → Bool) → (Fin n → Fin n → Module.End ℂ V) → Prop :=
    fun {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
        (E : Fin n → Fin n → Module.End ℂ V) ↦
      ∀ (a b : Fin n), ε a = ε b → ∀ (x y : V), Inner.inner ℂ ((E a b : V → V) x) y = Inner.inner ℂ x ((E b a : V → V) y)

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.KStab :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Bool) → (Fin n → Fin n → Module.End ℂ V) → Submodule ℂ V → Prop :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
        (S : Submodule ℂ V) ↦
      ∀ (a b : Fin n), ε a = ε b → ∀ v ∈ S, (E a b : V → V) v ∈ S

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.IsWeight.{u_1} :
    {V : Type u_1} →
      [inst : AddCommGroup V] →
        [inst_1 : _root_.Module ℂ V] → {n : ℕ} → (Fin n → Fin n → Module.End ℂ V) → (Fin n → ℝ) → V → Prop :=
    fun {V : Type u_1} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ)
        (w : V) ↦
      ∀ (a : Fin n), (E a a : V → V) w = (↑(μ a) : ℂ) • w

theorem UpperTheory.Reformulated.B.WeightsCompactStabilizer.exists_weight :
    ∀ {n : ℕ} {ε : Fin n → Bool} {V : Type} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℂ V]
      {E : Fin n → Fin n → Module.End ℂ V},
      UpperTheory.Reformulated.B.WeightsCompactStabilizer.GlRel E →
        UpperTheory.Reformulated.B.WeightsCompactStabilizer.KUnit ε E →
          ∀ {Q : Submodule ℂ V} [FiniteDimensional ℂ ↥Q],
            UpperTheory.Reformulated.B.WeightsCompactStabilizer.KStab ε E Q → Q ≠ ⊥ → ∃ (ν : Fin n → ℝ), ∃ x ∈ Q, x ≠ (0 : V) ∧ UpperTheory.Reformulated.B.WeightsCompactStabilizer.IsWeight E ν x := by
  intro n ε V _ _ E hG hU Q _ hS hQ
  classical
  let T : Fin n → Module.End ℂ Q := fun a => (E a a).restrict (fun v hv => hS a a rfl v hv)
  have hT : ∀ a (x : Q), ((T a x : Q) : V) = E a a x := fun a x => rfl
  have hsym : ∀ a, (T a).IsSymmetric := by
    intro a x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hT, hT]
    exact hU a a rfl x y
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a b hab
    have h := hG a a b b
    rw [if_neg hab, if_neg hab.symm, sub_zero, sub_eq_zero] at h
    change T a * T b = T b * T a
    ext x
    have := congrArg (fun f : Module.End ℂ V => f x) h
    simpa [hT] using this
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  have hex : ∃ α : Fin n → ℂ, (⨅ j, Module.End.eigenspace (T j) (α j)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    rw [iSup_eq_bot.mpr hcon] at htop
    have : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
    exact bot_ne_top htop
  obtain ⟨α, hα⟩ := hex
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  have hx' : ∀ a, x ∈ Module.End.eigenspace (T a) (α a) := fun a =>
    (Submodule.mem_iInf _).mp hx a
  have hre : ∀ a, (((α a).re : ℝ) : ℂ) = α a := fun a =>
    Complex.conj_eq_iff_re.mp
      ((hsym a).conj_eigenvalue_eq_self
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx' a, hx0⟩))
  refine ⟨fun a => (α a).re, x, x.2, fun h => hx0 (Subtype.ext h), fun a => ?_⟩
  have h := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp (hx' a))
  rw [hT] at h
  rw [hre a, h]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WithBotEqOfLeOfAddOneLe
section
theorem UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le :
    ∀ {x : WithBot ℕ∞} {c : ℕ},
      (↑c : WithBot ℕ∞) ≤ x → x + (1 : WithBot ℕ∞) ≤ (↑(c + (1 : ℕ)) : WithBot ℕ∞) → x = (↑c : WithBot ℕ∞) := by
  intro x c h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact le_antisymm bot_le h1
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞) := by exact_mod_cast h2
      rw [top_add, top_le_iff] at h3
      exact ENat.coe_ne_top _ h3
    | coe n =>
      have h3 : c ≤ n := by exact_mod_cast h1
      have h4 : n + 1 ≤ c + 1 := by exact_mod_cast h2
      have h5 : n = c := by omega
      subst h5
      rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WtGeProd
section
noncomputable def UpperTheory.Reformulated.B.Qk29.dot.{v} :
    {ι : Type v} → (ι →₀ ℕ) → (ι → ℝ) → ℝ :=
    fun {ι : Type v} (n : ι →₀ ℕ) (r : ι → ℝ) ↦ n.sum fun (i : ι) (k : ℕ) ↦ (↑k : ℝ) * r i

noncomputable def UpperTheory.Reformulated.B.Qk29.MonoWtGe.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → ℝ → (ι → ℝ) → ℝ → (ι →₀ ℕ) → K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (n : ι →₀ ℕ) (c : K) ↦
      ‖c‖ ≤ pi ^ (w - UpperTheory.Reformulated.B.Qk29.dot n r)

noncomputable def UpperTheory.Reformulated.B.Qk29.WtGe.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → ℝ → (ι → ℝ) → ℝ → MvPowerSeries ι K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (f : MvPowerSeries ι K) ↦
      ∀ (n : ι →₀ ℕ), UpperTheory.Reformulated.B.Qk29.MonoWtGe pi r w n ((MvPowerSeries.coeff n : MvPowerSeries ι K → K) f)

private theorem UpperTheory.Reformulated.B.Qk29.dot_add {ι : Type*} (a b : ι →₀ ℕ) (r : ι → ℝ) :
    UpperTheory.Reformulated.B.Qk29.dot (a + b) r = UpperTheory.Reformulated.B.Qk29.dot a r + UpperTheory.Reformulated.B.Qk29.dot b r := by
  unfold UpperTheory.Reformulated.B.Qk29.dot
  apply Finsupp.sum_add_index'
  · intro i; simp
  · intro i m n; push_cast; ring

private theorem UpperTheory.Reformulated.B.Qk29.wtGe_one {K : Type*} [NormedField K] {ι : Type*} {pi : ℝ}
    (hpi : 0 < pi) (r : ι → ℝ) : UpperTheory.Reformulated.B.Qk29.WtGe pi r 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h
    simp [UpperTheory.Reformulated.B.Qk29.dot]
  · rw [norm_zero]
    exact (Real.rpow_pos_of_pos hpi _).le

private theorem UpperTheory.Reformulated.B.Qk29.wtGe_mul {K : Type*} [NormedField K] {ι : Type*}
    [IsUltrametricDist K] {pi : ℝ} (hpi : 0 < pi) {r : ι → ℝ} {a b : ℝ}
    {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qk29.WtGe pi r a f)
    (hg : UpperTheory.Reformulated.B.Qk29.WtGe pi r b g) : UpperTheory.Reformulated.B.Qk29.WtGe pi r (a + b) (f * g) := by
  classical
  intro n
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe
  rw [MvPowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_pos_of_pos hpi _).le
  intro p hp
  have hn : p.1 + p.2 = n := by simpa using hp
  have h1 := hf p.1
  have h2 := hg p.2
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe at h1 h2
  have he : a + b - UpperTheory.Reformulated.B.Qk29.dot n r =
      (a - UpperTheory.Reformulated.B.Qk29.dot p.1 r) + (b - UpperTheory.Reformulated.B.Qk29.dot p.2 r) := by
    rw [← hn, UpperTheory.Reformulated.B.Qk29.dot_add]; ring
  rw [he, Real.rpow_add hpi, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_pos_of_pos hpi _).le

theorem UpperTheory.Reformulated.B.Qk29.wtGe_prod.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} [IsUltrametricDist K] {pi : ℝ},
      (0 : ℝ) < pi →
        ∀ {r : ι → ℝ} {α : Type w} (s : Finset α) (wt : α → ℝ) (F : α → MvPowerSeries ι K),
          (∀ i ∈ s, UpperTheory.Reformulated.B.Qk29.WtGe pi r (wt i) (F i)) → UpperTheory.Reformulated.B.Qk29.WtGe pi r (∑ i ∈ s, wt i) (∏ i ∈ s, F i) := by
  intro K inst ι _ pi hpi r α s wt F h
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UpperTheory.Reformulated.B.Qk29.wtGe_one hpi r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qk29.wtGe_mul hpi (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end

