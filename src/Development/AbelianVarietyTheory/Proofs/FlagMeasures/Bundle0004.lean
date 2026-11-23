module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSmulLe
section
namespace GlobalTheory.IntegerMultipleIntegral

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (k : K) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers K,
      algebraMap (NumberField.RingOfIntegers K) K a = M • k := by
  have h1 : IsAlgebraic ℚ k := Algebra.IsAlgebraic.isAlgebraic k
  have h2 : IsAlgebraic ℤ k := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr h1
  obtain ⟨M, hM, hint⟩ := h2.exists_integral_multiple
  exact ⟨M, hM, ⟨M • k, hint⟩, rfl⟩

theorem exists_int_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    (x : V) : ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ A := by
  have hx : x ∈ Submodule.span K (A : Set V) := by rw [hA]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨M, hM, hy⟩ := hy
    obtain ⟨N, hN, hz⟩ := hz
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.toAddSubgroup.zsmul_mem hy N
    · rw [mul_smul]; exact A.toAddSubgroup.zsmul_mem hz M
  | smul k y _ hy =>
    obtain ⟨N, hN, hy⟩ := hy
    obtain ⟨M, hM, a, ha⟩ := exists_int_mul_integral k
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have : (M * N) • k • y = a • (N • y) := by
      rw [← algebraMap_smul K a, ha, smul_assoc, mul_smul, smul_comm N k y]
    rw [this]
    exact A.smul_mem a hy

theorem exists_int_smul_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    {B : Submodule (NumberField.RingOfIntegers K) V} (hB : B.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ B, N • x ∈ A := by
  obtain ⟨s, rfl⟩ := hB
  choose f hf0 hf using exists_int_smul_mem hA
  refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.mpr fun y _ => hf0 y, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.mp hy)
    rw [hc, mul_comm, mul_smul]
    exact A.toAddSubgroup.zsmul_mem (hf y) c
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact A.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact A.smul_mem a hy

end GlobalTheory.IntegerMultipleIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSmulMemLattice
section
namespace GlobalTheory.IntMulIntegerSmulMemLattice

open NumberField

theorem exists_int_mul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ r : 𝓞 E, (r : E) = (d : E) * c := by
  have hQ : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hZ : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hQ
  obtain ⟨d, hd, hint⟩ := hZ.exists_integral_multiple
  refine ⟨d, hd, ⟨d • c, hint⟩, ?_⟩
  change d • c = (d : E) * c
  rw [zsmul_eq_mul]

theorem exists_int_smul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ (0 : ℤ) ∧ (m : 𝓞 E) • w ∈ Λ := by
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    rw [hΛ.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : ((a * b : ℤ) : 𝓞 E) • (x + y)
        = (b : 𝓞 E) • ((a : 𝓞 E) • x) + (a : 𝓞 E) • ((b : 𝓞 E) • y) := by
      rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (b : 𝓞 E) (a : 𝓞 E)]
    rw [h]
    exact Λ.add_mem (Λ.smul_mem _ hax) (Λ.smul_mem _ hby)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨d, hd, r, hr⟩ := exists_int_mul_eq_integer c
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    have h : ((d * a : ℤ) : 𝓞 E) • (c • x) = r • ((a : 𝓞 E) • x) := by
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_intCast, Algebra.algebraMap_self,
        RingHom.id_apply, Int.cast_mul, map_mul]
      have hr' : algebraMap (𝓞 E) E r = (d : E) * c := hr
      rw [hr', Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      ring
    rw [h]
    exact Λ.smul_mem _ hax

end GlobalTheory.IntMulIntegerSmulMemLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSubMemPow
section
namespace GlobalTheory.IntSubMemPow

theorem exists_int_sub_mem {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (P : Ideal R)
    (hP : P ≠ ⊤) (hc : Nat.card (R ⧸ P) = p) (a : R) : ∃ m : ℤ, a - (m : R) ∈ P := by
  have : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  have : Finite (R ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)

  have hord : addOrderOf (1 : R ⧸ P) = p := by
    have hdvd : addOrderOf (1 : R ⧸ P) ∣ p := hc ▸ addOrderOf_dvd_natCard 1
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) one_ne_zero
    · exact h1

  have htop : AddSubgroup.zmultiples (1 : R ⧸ P) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hc]
  have hmem : Ideal.Quotient.mk P a ∈ AddSubgroup.zmultiples (1 : R ⧸ P) := by
    rw [htop]; exact AddSubgroup.mem_top _
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine ⟨m, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, ← hm, zsmul_one, sub_self]

theorem span_sup_sq_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R)
    (hP : P.IsMaximal) (h0 : P ≠ ⊥) (x : R) (hx : x ∈ P) (hx2 : x ∉ P ^ 2) :
    Ideal.span {x} ⊔ P ^ 2 = P := by
  have hprime : Prime P := Ideal.prime_of_isPrime h0 hP.isPrime
  have hle : Ideal.span {x} ⊔ P ^ 2 ≤ P :=
    sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hx) (Ideal.pow_le_self two_ne_zero)

  have hdvd : Ideal.span {x} ⊔ P ^ 2 ∣ P ^ 2 := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hprime 2).mp hdvd
  rw [associated_iff_eq] at hassoc
  interval_cases i
  · exfalso
    rw [pow_zero, Ideal.one_eq_top] at hassoc
    exact hP.ne_top (top_le_iff.mp (hassoc ▸ hle))
  · simpa using hassoc
  · exfalso
    exact hx2 (hassoc ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))

private lemma pow_le_span_pow_sup_pow_succ {R : Type} [CommRing R] (P : Ideal R) (x : R) (hx : x ∈ P)
    (h : Ideal.span {x} ⊔ P ^ 2 = P) (k : ℕ) :
    P ^ k ≤ Ideal.span {x ^ k} ⊔ P ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun r hr s hs => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (ih hr)
    have hs' := hs
    rw [← h] at hs'
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hs'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hd
    have hsplit : (c * x ^ k + b) * (c' * x + e) =
        (c * c') * x ^ (k + 1) + (c * (x ^ k * e) + b * (c' * x + e)) := by ring
    rw [hsplit]
    refine Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) ?_
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) ?_
    · have : x ^ k * e ∈ P ^ k * P ^ 2 := Ideal.mul_mem_mul (Ideal.pow_mem_pow hx k) he
      rwa [← pow_add] at this
    · have : b * (c' * x + e) ∈ P ^ (k + 1) * P := Ideal.mul_mem_mul hb hs
      rwa [← pow_succ] at this

theorem exists_sub_mul_pow_mem {R : Type} [CommRing R] (P : Ideal R) (x : R) (hx : x ∈ P)
    (h : Ideal.span {x} ⊔ P ^ 2 = P) (k : ℕ) :
    ∀ y ∈ P ^ k, ∃ c : R, y - c * x ^ k ∈ P ^ (k + 1) := by
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (pow_le_span_pow_sup_pow_succ P x hx h k hy)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  exact ⟨c, by simpa using hb⟩

theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : Nat.Prime p)
    (P : Ideal (NumberField.RingOfIntegers E)) (hP : Ideal.IsMaximal P)
    (hpP : (p : NumberField.RingOfIntegers E) ∈ P) (hN : Ideal.absNorm P = p)
    (hp2 : (p : NumberField.RingOfIntegers E) ∉ P ^ (2 : ℕ)) (k : ℕ)
    (a : NumberField.RingOfIntegers E) :
    ∃ m : ℤ, a - (m : NumberField.RingOfIntegers E) ∈ P ^ k := by
  have h0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN
    exact hp.ne_zero hN.symm
  have hcard : Nat.card (NumberField.RingOfIntegers E ⧸ P) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hgen : Ideal.span {(p : NumberField.RingOfIntegers E)} ⊔ P ^ 2 = P := span_sup_sq_eq P hP h0 _ hpP hp2
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih

    obtain ⟨c, hc⟩ := exists_sub_mul_pow_mem P _ hpP hgen k _ hm
    obtain ⟨n, hn⟩ := exists_int_sub_mem hp P hP.ne_top hcard c
    refine ⟨m + n * (p : ℤ) ^ k, ?_⟩
    have hrest : (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k ∈ P ^ (k + 1) := by
      have : (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k ∈ P * P ^ k :=
        Ideal.mul_mem_mul hn (Ideal.pow_mem_pow hpP k)
      rwa [← pow_succ'] at this
    have heq : a - ((m + n * (p : ℤ) ^ k : ℤ) : NumberField.RingOfIntegers E) =
        (a - (m : NumberField.RingOfIntegers E) - c * (p : NumberField.RingOfIntegers E) ^ k) + (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k := by
      push_cast; ring
    rw [heq]
    exact Ideal.add_mem _ hc hrest

end GlobalTheory.IntSubMemPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricIntertwinerOfMatrixCoeffEq
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem inner_translate_translate_of_norm {G : Type} [Group G] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖) (w : H)
    (g h : G) : ⟪σ g w, σ h w⟫_ℂ = ⟪w, σ (g⁻¹ * h) w⟫_ℂ := by
  have hmul : σ h w = σ g (σ (g⁻¹ * h) w) := by
    show σ h w = (σ g * σ (g⁻¹ * h)) w
    rw [← map_mul, mul_inv_cancel_left]
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }
  rw [hmul]
  exact T.inner_map_map w (σ (g⁻¹ * h) w)

theorem exists_isometric_intertwiner_of_matrixCoeff_eq :
    ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (Hp : Type) [NormedAddCommGroup Hp]
      [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)),
      (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ g x, ‖π g x‖ = ‖x‖) → ∀ (w : H) (v : Hp),
      (∀ y : H, (∀ g, ⟪y, σ g w⟫_ℂ = 0) → y = 0) → (∀ g, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) →
      ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by
  intro G _ H _ _ _ σ Hp _ _ _ π hσ hπ w v hcyc hvw

  obtain ⟨A, hA⟩ : ∃ A : (G →₀ ℂ) →ₗ[ℂ] H, A = Finsupp.linearCombination ℂ (fun g => σ g w) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (G →₀ ℂ) →ₗ[ℂ] Hp, B = Finsupp.linearCombination ℂ (fun g => π g v) :=
    ⟨_, rfl⟩

  have hkey : ∀ g h : G, ⟪π g v, π h v⟫_ℂ = ⟪σ g w, σ h w⟫_ℂ := by
    intro g h
    rw [inner_translate_translate_of_norm π hπ, inner_translate_translate_of_norm σ hσ, hvw]
  have hinner : ∀ c d, ⟪B c, B d⟫_ℂ = ⟪A c, A d⟫_ℂ := by
    intro c d
    rw [hA, hB]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hkey]
  have hnorm : ∀ c, ‖B c‖ = ‖A c‖ := by
    intro c
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (A c), hinner]
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]

  obtain ⟨F, hF⟩ : ∃ F : LinearMap.range A →ₗ[ℂ] Hp,
      ∀ c, F ⟨A c, LinearMap.mem_range_self A c⟩ = B c :=
    ⟨(LinearMap.ker A).liftQ B hker ∘ₗ A.quotKerEquivRange.symm.toLinearMap, fun c => by simp⟩
  have hFn : ∀ y, ‖F y‖ = ‖y‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hF, hnorm]
    rfl
  let F' : LinearMap.range A →ₗᵢ[ℂ] Hp := { toLinearMap := F, norm_map' := hFn }

  have hclos : (LinearMap.range A).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    refine hcyc y fun g => inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp hy _ ?_)
    exact ⟨Finsupp.single g 1, by simp [hA]⟩
  have hdense : DenseRange (LinearMap.range A).subtypeL :=
    denseRange_subtype_val.mpr (Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos)
  have huni : IsUniformInducing (LinearMap.range A).subtypeL :=
    (LinearMap.range A).subtypeₗᵢ.isometry.isUniformInducing

  obtain ⟨X, hXdef⟩ : ∃ X : H →L[ℂ] Hp, X = F'.toContinuousLinearMap.extend (LinearMap.range A).subtypeL :=
    ⟨_, rfl⟩
  have hX : ∀ c, X (A c) = B c := fun c => by
    rw [hXdef]
    exact (ContinuousLinearMap.extend_eq F'.toContinuousLinearMap hdense huni
      ⟨A c, LinearMap.mem_range_self A c⟩).trans (hF c)
  have hXn : ∀ u, ‖X u‖ = ‖u‖ := by
    intro u
    refine hdense.induction_on (p := fun u => ‖X u‖ = ‖u‖) u
      (isClosed_eq (continuous_norm.comp X.continuous) continuous_norm) ?_
    rintro ⟨_, c, rfl⟩
    show ‖X (A c)‖ = ‖A c‖
    rw [hX, hnorm]

  have hshA : ∀ g c, σ g (A c) = A (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    rw [hA, Finsupp.linearCombination_mapDomain]
    change (σ g : H →ₗ[ℂ] H) _ = _
    rw [Finsupp.apply_linearCombination]
    refine congrArg (fun f => Finsupp.linearCombination ℂ f c) ?_
    funext h
    simp [map_mul]
  have hshB : ∀ g c, π g (B c) = B (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    rw [hB, Finsupp.linearCombination_mapDomain]
    change (π g : Hp →ₗ[ℂ] Hp) _ = _
    rw [Finsupp.apply_linearCombination]
    refine congrArg (fun f => Finsupp.linearCombination ℂ f c) ?_
    funext h
    simp [map_mul]
  have hXi : ∀ g u, X (σ g u) = π g (X u) := by
    intro g u
    refine hdense.induction_on (p := fun u => X (σ g u) = π g (X u)) u
      (isClosed_eq (X.continuous.comp (σ g).continuous) ((π g).continuous.comp X.continuous)) ?_
    rintro ⟨_, c, rfl⟩
    show X (σ g (A c)) = π g (X (A c))
    rw [hshA, hX, hX, hshB]
  have hw : A (Finsupp.single 1 1) = w := by simp [hA]
  have hv : B (Finsupp.single 1 1) = v := by simp [hB]
  refine ⟨{ toLinearMap := (X : H →ₗ[ℂ] Hp), norm_map' := hXn }, ?_, fun g u => hXi g u⟩
  show X w = v
  rw [← hw, hX, hv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCosetSection
section
open MeasureTheory

namespace GlobalTheory

open Filter Topology

theorem exists_measurable_invariant_index {G : Type} [Group G] [MetricSpace G]
    [ContinuousMul G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G) (y : ℕ → G)
    (r : ℝ) (Q : ℕ → G → Prop) (hQm : ∀ n, MeasurableSet {x | Q n x})
    (hQi : ∀ n, ∀ l ∈ L, ∀ x, Q n (l * x) ↔ Q n x)
    (hex : ∀ x, ∃ n, (∃ l ∈ L, dist (y n) (l * x) < r) ∧ Q n x) :
    ∃ s : G → ℕ, Measurable s ∧ (∀ x, ∃ l ∈ L, dist (y (s x)) (l * x) < r) ∧
      (∀ l ∈ L, ∀ x, s (l * x) = s x) ∧ ∀ x, Q (s x) x := by
  classical
  have hPm : ∀ n, MeasurableSet {x : G | (∃ l ∈ L, dist (y n) (l * x) < r) ∧ Q n x} := by
    intro n
    have hset : {x : G | ∃ l ∈ L, dist (y n) (l * x) < r} =
        ⋃ l : L, {x : G | dist (y n) ((l : G) * x) < r} := by
      ext x; simp
    have hopen : IsOpen {x : G | ∃ l ∈ L, dist (y n) (l * x) < r} := by
      rw [hset]
      exact isOpen_iUnion fun l =>
        isOpen_lt (continuous_const.dist (continuous_const.mul continuous_id)) continuous_const
    exact hopen.measurableSet.inter (hQm n)
  have hinv : ∀ l ∈ L, ∀ x n, ((∃ l' ∈ L, dist (y n) (l' * (l * x)) < r) ∧ Q n (l * x)) ↔
      ((∃ l' ∈ L, dist (y n) (l' * x) < r) ∧ Q n x) := by
    intro l hl x n
    refine and_congr ⟨?_, ?_⟩ (hQi n l hl x)
    · rintro ⟨m, hm, hd⟩
      exact ⟨m * l, L.mul_mem hm hl, by rwa [mul_assoc]⟩
    · rintro ⟨m, hm, hd⟩
      refine ⟨m * l⁻¹, L.mul_mem hm (L.inv_mem hl), ?_⟩
      simpa [mul_assoc] using hd
  refine ⟨fun x => Nat.find (hex x), measurable_find hex hPm, fun x => (Nat.find_spec (hex x)).1,
    fun l hl x => ?_, fun x => (Nat.find_spec (hex x)).2⟩
  exact le_antisymm (Nat.find_min' _ ((hinv l hl x _).2 (Nat.find_spec (hex x))))
    (Nat.find_min' _ ((hinv l hl x _).1 (Nat.find_spec (hex (l * x)))))

theorem exists_measurable_coset_section_metric {G : Type} [Group G] [MetricSpace G]
    [CompleteSpace G] [SecondCountableTopology G]
    [ContinuousMul G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : ℕ → G, DenseRange y := TopologicalSpace.exists_dense_seq G
  let S : ℕ → Type := fun k => {s : G → ℕ // Measurable s ∧ (∀ l ∈ L, ∀ x, s (l * x) = s x) ∧
    ∀ x, ∃ l ∈ L, dist (y (s x)) (l * x) < (1 / 2 : ℝ) ^ k}
  have hy_meas : ∀ s : G → ℕ, Measurable s → Measurable (fun x => y (s x)) :=
    fun s hs => measurable_from_nat.comp hs

  have h0 : Nonempty (S 0) := by
    obtain ⟨s, hs, hclose, hinv, -⟩ := exists_measurable_invariant_index L y 1 (fun _ _ => True)
      (fun _ => MeasurableSet.univ) (fun _ _ _ _ => Iff.rfl) (fun x => by
        obtain ⟨n, hn⟩ := hy.exists_dist_lt x one_pos
        exact ⟨n, ⟨1, L.one_mem, by rw [one_mul, dist_comm]; exact hn⟩, trivial⟩)
    exact ⟨⟨s, hs, hinv, fun x => by simpa using hclose x⟩⟩

  have hstep : ∀ k (s : S k), ∃ s' : S (k + 1),
      ∀ x, dist (y (s'.1 x)) (y (s.1 x)) < 2 * (1 / 2 : ℝ) ^ k := by
    intro k s
    obtain ⟨s, hsm, hsi, hsc⟩ := s
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 1) := by positivity
    have hhalf : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2 := by ring
    obtain ⟨s', hs'm, hclose, hinv, hQ⟩ := exists_measurable_invariant_index L y ((1 / 2 : ℝ) ^ (k + 1))
      (fun n x => dist (y n) (y (s x)) < 2 * (1 / 2 : ℝ) ^ k)
      (fun n => measurableSet_lt (measurable_const.dist (hy_meas s hsm)) measurable_const)
      (fun n l hl x => by simp only [hsi l hl x])
      (fun x => by
        obtain ⟨l, hl, hd⟩ := hsc x
        obtain ⟨n, hn⟩ := hy.exists_dist_lt (l * x) hpos
        refine ⟨n, ⟨l, hl, by rw [dist_comm]; exact hn⟩, ?_⟩
        have hk : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
        calc dist (y n) (y (s x)) ≤ dist (y n) (l * x) + dist (l * x) (y (s x)) := dist_triangle _ _ _
          _ < 2 * (1 / 2 : ℝ) ^ k := by
            rw [hhalf] at hn
            have e1 := dist_comm (y n) (l * x)
            have e2 := dist_comm (l * x) (y (s x))
            linarith)
    exact ⟨⟨s', hs'm, hinv, hclose⟩, hQ⟩
  choose step hstep using hstep
  let seq : (k : ℕ) → S k := fun k => Nat.rec (motive := S) h0.some (fun k s => step k s) k
  let f : ℕ → G → G := fun k x => y ((seq k).1 x)
  have hf_succ : ∀ k x, dist (f k x) (f (k + 1) x) ≤ 2 * (1 / 2 : ℝ) ^ k := fun k x => by
    rw [dist_comm]; exact (hstep k (seq k) x).le
  have hcauchy : ∀ x, CauchySeq (fun k => f k x) := fun x =>
    cauchySeq_of_le_geometric (1 / 2 : ℝ) 2 (by norm_num) (hf_succ · x)
  choose σ hσ using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨σ, ?_, ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable (fun k => hy_meas _ (seq k).2.1) (tendsto_pi_nhds.2 hσ)
  · intro x
    have hC : IsClosed {z : G | z * x⁻¹ ∈ L} := hL.preimage (continuous_id.mul continuous_const)
    suffices h : σ x ∈ closure {z : G | z * x⁻¹ ∈ L} by rwa [hC.closure_eq] at h
    rw [Metric.mem_closure_iff]
    intro ε hε
    have h1 : ∀ᶠ k in atTop, dist (f k x) (σ x) < ε / 2 :=
      (hσ x).eventually (Metric.ball_mem_nhds _ (half_pos hε))
    have h2 : ∀ᶠ k in atTop, (1 / 2 : ℝ) ^ k < ε / 2 :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
        (gt_mem_nhds (half_pos hε))
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    obtain ⟨l, hl, hd⟩ := (seq k).2.2.2 x
    refine ⟨l * x, by simpa using hl, ?_⟩
    calc dist (σ x) (l * x) ≤ dist (σ x) (f k x) + dist (f k x) (l * x) := dist_triangle _ _ _
      _ < ε := by rw [dist_comm] at hk1; change dist (f k x) (l * x) < _ at hd; linarith
  · intro l hl x
    have hfx : (fun k => f k (l * x)) = fun k => f k x := by
      funext k; simp only [f, (seq k).2.2.1 l hl x]
    have := hσ (l * x)
    rw [hfx] at this
    exact tendsto_nhds_unique this (hσ x)

theorem exists_measurable_coset_section (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable G
  exact exists_measurable_coset_section_metric L hL

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
section
open NumberField

namespace GlobalTheory


open NumberField in
theorem _root_.GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top (F E : Type) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ↔ differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  rw [← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact (dvd_differentIdeal_iff (P := M)).1 (Ideal.dvd_iff_le.2 hle) (h ⟨M, hM.isPrime⟩)
  · intro h P
    show Algebra.IsUnramifiedAt _ P.asIdeal
    rw [← not_dvd_differentIdeal_iff, h, Ideal.dvd_iff_le, top_le_iff]
    exact P.isPrime.ne_top

end GlobalTheory
end

