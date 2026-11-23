module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RelIndexMapMulLeftLatticeOfSqEqNeg
section
namespace GlobalTheory

theorem relIndex_map_mulLeft_lattice_of_sq_eq_neg :
    ∀ (L : PeriodPair) (α : ℂ) (N : ℕ), 0 < N → α ^ 2 = -(N : ℂ) →
      (∀ l ∈ L.lattice, α * l ∈ L.lattice) →
      (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex L.lattice.toAddSubgroup
        = N := by
  intro L α N hN hα hL
  have hα0 : α ≠ 0 := by
    rintro rfl
    have : (N : ℂ) = 0 := by simpa using hα
    exact hN.ne' (by exact_mod_cast this)
  have hinj : Function.Injective (AddMonoidHom.mulLeft α) := mul_right_injective₀ hα0
  set A := L.lattice.toAddSubgroup with hA
  set f := AddMonoidHom.mulLeft α with hf
  have h1 : A.map f ≤ A := by
    rintro _ ⟨l, hl, rfl⟩
    exact hL l hl
  have h2 : (A.map f).map f ≤ A.map f := AddSubgroup.map_mono h1
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ h2 h1
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj] at hmul
  have hr : Module.finrank ℤ L.lattice = 2 := by
    simpa using Module.finrank_eq_card_basis L.latticeBasis
  have hidx : ((A.map f).map f).relIndex A = N ^ 2 := by
    rw [← hr, ← AddSubgroup.index_range_nsmul, AddSubgroup.relIndex]
    congr 1
    ext x
    rw [AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, hx⟩
      refine ⟨⟨-l, L.lattice.neg_mem hl⟩, Subtype.ext ?_⟩
      have hx' : α * (α * l) = (x : ℂ) := hx
      show N • (-l) = (x : ℂ)
      rw [← hx', nsmul_eq_mul]
      linear_combination (-l) * hα
    · rintro ⟨l, hx⟩
      have hx' : N • (l : ℂ) = (x : ℂ) := congrArg Subtype.val hx
      refine ⟨_, ⟨-(l : ℂ), L.lattice.neg_mem l.2, rfl⟩, ?_⟩
      show α * (α * -(l : ℂ)) = (x : ℂ)
      rw [← hx', nsmul_eq_mul]
      linear_combination (-(l : ℂ)) * hα
  rw [hidx, ← sq] at hmul
  exact Nat.pow_left_injective two_ne_zero hmul

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelfDualHermitianLatticeExistsNormOneMod
section
namespace GlobalTheory

theorem padicNorm_prime_mul_sq_ne_sq (p : ℕ) [hp : Fact p.Prime] (s t : ℚ) (ht : t ≠ 0) :
    padicNorm p (s ^ 2) ≠ padicNorm p ((p : ℚ) * t ^ 2) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hpt : (p : ℚ) * t ^ 2 ≠ 0 := mul_ne_zero hp0 (pow_ne_zero _ ht)
  by_cases hs : s = 0
  · subst hs
    intro h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, padicNorm.zero] at h
    exact padicNorm.nonzero hpt h.symm
  · intro h
    rw [padicNorm.eq_zpow_of_nonzero (pow_ne_zero _ hs), padicNorm.eq_zpow_of_nonzero hpt,
      padicValRat.mul hp0 (pow_ne_zero _ ht), padicValRat.pow s, padicValRat.pow t,
      padicValRat.self hp.out.one_lt] at h
    have := zpow_right_injective₀ (by linarith) hp1.ne' h
    push_cast at this
    omega

theorem padicNorm_of_sq_add_prime_mul_sq (p : ℕ) [hp : Fact p.Prime] (s t : ℚ)
    (h : padicNorm p (s ^ 2 + (p : ℚ) * t ^ 2) = 1) :
    padicNorm p s ≤ 1 ∧ padicNorm p ((p : ℚ) * t ^ 2) < 1 := by
  have key : padicNorm p (s ^ 2) ≤ 1 ∧ padicNorm p ((p : ℚ) * t ^ 2) < 1 := by
    by_cases ht : t = 0
    · subst ht
      simp at h ⊢
      exact h.le
    · rw [padicNorm.add_eq_max_of_ne (padicNorm_prime_mul_sq_ne_sq p s t ht)] at h
      have h1 := padicNorm_prime_mul_sq_ne_sq p 1 t ht
      rw [one_pow, padicNorm.one] at h1
      exact ⟨h ▸ le_max_left _ _, lt_of_le_of_ne (h ▸ le_max_right _ _) h1.symm⟩
  refine ⟨?_, key.2⟩
  have h1 := key.1
  rw [sq, padicNorm.mul] at h1
  have := padicNorm.nonneg (p := p) s
  nlinarith

theorem selfDual_lattice_exists_norm_one_mod :
    ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → (∀ u v : ℚ, padicNorm p u = 1 → padicNorm p v = 1 → ∃ a b : ℤ, padicNorm p (u * (a : ℚ) ^ 2 + v * (b : ℚ) ^ 2 - 1) < 1) → (∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ x ∈ W, x ≠ 0) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p u = 1) → ∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ e ∈ W, h e e = 1) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1 := by
  intro K V _ _ _ _ σ h p d θ O L hp hd hθ hσθ hK hσO hω hO hh hdef hL hLO hbig hab hun W hW
    ⟨e, heW, he⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨y1, hy1L, hy1W, u1, hu1, hu1n⟩ := hun W hW ⟨e, heW, he0⟩
  have hu10 : u1 ≠ 0 := by
    rintro rfl
    simp at hu1n
  have hu10K : (u1 : K) ≠ 0 := by exact_mod_cast hu10
  have hinv : (u1 : K)⁻¹ ∈ O := by
    have : ((u1⁻¹ : ℚ) : K) ∈ O := by
      rw [hO, ← one_div, padicNorm.div, hu1n]
      simp
    simpa using this
  have hθO : θ ∈ O := by
    have h2 : θ = (1 + θ) / 2 + (1 + θ) / 2 - 1 := by ring
    rw [h2]
    exact O.sub_mem (O.add_mem hω hω) O.one_mem
  have hperp : ∀ y : V, h (y - (h y y1 * (u1 : K)⁻¹) • y1) y1 = 0 := by
    intro y
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu1]
    field_simp
    ring
  have hnorm : ∀ s t : ℚ, h (((s : K) + (t : K) * θ) • y1) (((s : K) + (t : K) * θ) • y1)
      = (((s ^ 2 + (d : ℚ) * t ^ 2) * u1 : ℚ) : K) := by
    intro s t
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hu1, map_add (f := _),
      map_mul, map_ratCast, hσθ]
    push_cast
    linear_combination (-(t : K) ^ 2 * (u1 : K)) * hθ
  set W' : Submodule K V := W ⊓ LinearMap.ker (h.flip y1) with hW'
  have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ h x y1 = 0 := by
    intro x
    simp [hW']
  by_cases hne : ∃ x ∈ W', x ≠ 0
  · have hsd : ∀ x ∈ W', (∀ y ∈ L, y ∈ W' → h x y ∈ O) → x ∈ L := by
      intro x hx hxO
      obtain ⟨hxW, hx1⟩ := (hmem x).1 hx
      refine hW x hxW fun y hyL hyW => ?_
      have := hxO (y - (h y y1 * (u1 : K)⁻¹) • y1)
        (L.sub_mem hyL (hL _ (O.mul_mem (hLO _ hyL _ hy1L) hinv) _ hy1L))
        ((hmem _).2 ⟨W.sub_mem hyW (W.smul_mem _ hy1W), hperp y⟩)
      simpa [map_sub, LinearMap.map_smulₛₗ, hx1] using this
    obtain ⟨y2, hy2L, hy2W', u2, hu2, hu2n⟩ := hun W' hsd hne
    obtain ⟨hy2W, h21⟩ := (hmem y2).1 hy2W'
    have h12 : h y1 y2 = 0 := by rw [hh, h21, map_zero]
    obtain ⟨a, b, hab'⟩ := hab u1 u2 hu1n hu2n
    refine ⟨(a : K) • y1 + (b : K) • y2,
      L.add_mem (hL _ (intCast_mem O a) _ hy1L) (hL _ (intCast_mem O b) _ hy2L),
      W.add_mem (W.smul_mem _ hy1W) (W.smul_mem _ hy2W), _, ?_, hab'⟩
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, hu1, hu2, h12, h21, map_intCast]
    push_cast
    ring
  · by_cases hpd : p = d
    · subst hpd
      have h0 : e - (h e y1 * (u1 : K)⁻¹) • y1 = 0 := by
        by_contra hc
        exact hne ⟨_, (hmem _).2 ⟨W.sub_mem heW (W.smul_mem _ hy1W), hperp e⟩, hc⟩
      obtain ⟨s, t, hst⟩ := hK (h e y1 * (u1 : K)⁻¹)
      rw [hst, sub_eq_zero] at h0
      have h1 := hnorm s t
      rw [← h0, he] at h1
      have h2 : (s ^ 2 + (p : ℚ) * t ^ 2) * u1 = 1 := by exact_mod_cast h1.symm
      have h3 : padicNorm p (s ^ 2 + (p : ℚ) * t ^ 2) = 1 := by
        have := congrArg (padicNorm p) h2
        rwa [padicNorm.mul, hu1n, mul_one, padicNorm.one] at this
      obtain ⟨hs, ht⟩ := padicNorm_of_sq_add_prime_mul_sq p s t h3
      have h4 := hnorm s 0
      refine ⟨_, hL _ ?_ _ hy1L, W.smul_mem _ hy1W, _, h4, ?_⟩
      · simpa using (hO s).2 hs
      · have : (s ^ 2 + (p : ℚ) * 0 ^ 2) * u1 - 1 = -((p : ℚ) * t ^ 2 * u1) := by
          linear_combination h2
        rw [this, padicNorm.neg, padicNorm.mul, hu1n, mul_one]
        exact ht
    · haveI : Fact d.Prime := ⟨hd⟩
      have hdn : padicNorm p (d : ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne hpd
      obtain ⟨a, b, hab'⟩ := hab u1 (u1 * d) hu1n (by rw [padicNorm.mul, hu1n, hdn, mul_one])
      have h4 := hnorm a b
      refine ⟨_, hL _ ?_ _ hy1L, W.smul_mem _ hy1W, _, h4, ?_⟩
      · push_cast
        exact O.add_mem (intCast_mem O a) (O.mul_mem (intCast_mem O b) hθO)
      · convert hab' using 2
        ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetAverageProdFundamentalDomainPlaneLatticePow
section
open MeasureTheory
open scoped BigOperators

namespace GlobalTheory.LatticeMean

theorem exists_strict_domain (Λ : AddSubgroup ℂ)
    (h : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    Countable Λ ∧ ∃ F : Set ℂ, MeasurableSet F ∧ ∀ x : ℂ, ∃! g : Λ, (g : ℂ) + x ∈ F := by
  obtain ⟨w₁, w₂, hli, hΛ⟩ := h
  let b : Module.Basis (Fin 2) ℝ ℂ :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : Set.range b = {w₁, w₂} := by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    ext x
    simp [or_comm]
  have hΛ' : Λ = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    rw [hΛ, hb, Submodule.span_int_eq_addSubgroupClosure]
  subst hΛ'
  refine ⟨?_, ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, fun x => ?_⟩
  · exact inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  · exact ZSpan.exist_unique_vadd_mem_fundamentalDomain b x

theorem setAverage_eq_of_domain {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (A : AddSubgroup V) [Countable A] (f : V → ℝ)
    (hf : ∀ a ∈ A, ∀ z, f (a + z) = f z) (P : Set V) (hP : IsAddFundamentalDomain A P μ) :
    ⨍ z in Classical.epsilon (fun Fd : Set V => IsAddFundamentalDomain A Fd μ), f z ∂μ
      = ⨍ z in P, f z ∂μ := by
  have hE := Classical.epsilon_spec (p := fun Fd : Set V => IsAddFundamentalDomain A Fd μ) ⟨P, hP⟩
  rw [setAverage_eq, setAverage_eq, hE.setIntegral_eq hP (fun g x => hf g g.2 x),
    measureReal_def, measureReal_def, hE.measure_eq hP]

theorem setAverage_pi (r : ℕ) (F : Set ℂ) (f : ℂ → ℝ) :
    ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) = (⨍ z in F, f z) ^ r := by
  rw [setAverage_eq, setAverage_eq, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_pow, measureReal_def, Measure.pi_pi]
  simp [measureReal_def, mul_pow]

theorem mean_prod_eq_pow : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ (f : ℂ → ℝ), (∀ ω ∈ Λ, ∀ z, f (ω + z) = f z) → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (r : ℕ) (e : V ≃ₗ[ℝ] (Fin r → ℂ)) (A : AddSubgroup V), (∀ x, x ∈ A ↔ ∀ k, e x k ∈ Λ) → ⨍ z in Classical.epsilon (fun Fd : Set V => MeasureTheory.IsAddFundamentalDomain A Fd μ), ∏ k, f (e z k) ∂μ = (⨍ z in Classical.epsilon (fun Fd : Set ℂ => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume), f z) ^ r := by
  intro Λ hΛ f hf V _ _ _ _ _ μ _ r e A hA
  obtain ⟨hc, F, hFm, hF⟩ := exists_strict_domain Λ hΛ
  let ec : V ≃L[ℝ] (Fin r → ℂ) := e.toContinuousLinearEquiv
  let em : V ≃ᵐ (Fin r → ℂ) := ec.toHomeomorph.toMeasurableEquiv
  have hem : ∀ x, em x = e x := fun _ => rfl
  have hAc : Countable A := by
    refine Function.Injective.countable
      (f := fun (a : A) (k : Fin r) => (⟨e a k, (hA a).1 a.2 k⟩ : Λ)) ?_
    intro a b hab
    apply Subtype.ext
    apply e.injective
    funext k
    exact congrArg Subtype.val (congrFun hab k)
  have hQm : MeasurableSet (Set.univ.pi (fun _ : Fin r => F)) :=
    MeasurableSet.univ_pi fun _ => hFm
  have hP : IsAddFundamentalDomain A (em ⁻¹' Set.univ.pi (fun _ : Fin r => F)) μ := by
    refine IsAddFundamentalDomain.mk' (em.measurable hQm).nullMeasurableSet fun x => ?_
    choose g hg hu using fun k => hF (e x k)
    refine ⟨⟨e.symm fun k => (g k : ℂ), (hA _).2 fun k => by simp⟩, ?_, ?_⟩
    · intro k _
      show e (e.symm (fun k => (g k : ℂ)) + x) k ∈ F
      simpa using hg k
    · intro a ha
      apply Subtype.ext
      apply e.injective
      funext k
      have h1 : e ((a : V) + x) k ∈ F := ha k (Set.mem_univ k)
      have h2 := hu k ⟨e a k, (hA a).1 a.2 k⟩ (by simpa using h1)
      simpa using congrArg Subtype.val h2
  have hF' : IsAddFundamentalDomain Λ F volume :=
    IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hF
  rw [setAverage_eq_of_domain μ A (fun z => ∏ k, f (e z k)) ?_ _ hP,
    setAverage_eq_of_domain volume Λ f hf F hF', ← setAverage_pi]
  swap
  · intro a ha z
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_add (f := _), Pi.add_apply, hf _ ((hA a).1 ha k)]
  haveI : (μ.map em).IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  have hs := Measure.isAddLeftInvariant_eq_smul (μ.map em) (volume : Measure (Fin r → ℂ))
  have hc0 : Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have h1 : ⨍ z in em ⁻¹' Set.univ.pi (fun _ : Fin r => F), ∏ k, f (e z k) ∂μ
      = ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) ∂(μ.map em) := by
    rw [setAverage_eq, setAverage_eq, setIntegral_map_equiv, measureReal_def, measureReal_def,
      em.map_apply]
    rfl
  rw [h1, hs, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply]
  have hc1 : ((Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast hc0
  rw [NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]
  field_simp

end GlobalTheory.LatticeMean
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothingIntegersTwoCharacters
section
namespace GlobalTheory

theorem exists_unit_dirichletCharacter_ne_one_ne_one {N : ℕ} (θ₁ θ₂ : DirichletCharacter ℂ N)
    (h₁ : θ₁ ≠ 1) (h₂ : θ₂ ≠ 1) :
    ∃ u : (ZMod N)ˣ, θ₁ (u : ZMod N) ≠ 1 ∧ θ₂ (u : ZMod N) ≠ 1 := by
  obtain ⟨u₁, hu₁⟩ := MulChar.ne_one_iff.1 h₁
  obtain ⟨u₂, hu₂⟩ := MulChar.ne_one_iff.1 h₂
  by_cases a : θ₂ (u₁ : ZMod N) = 1
  · by_cases b : θ₁ (u₂ : ZMod N) = 1
    · refine ⟨u₁ * u₂, ?_, ?_⟩
      · rw [Units.val_mul, map_mul, b, mul_one]; exact hu₁
      · rw [Units.val_mul, map_mul, a, one_mul]; exact hu₂
    · exact ⟨u₂, b, hu₂⟩
  · exact ⟨u₁, hu₁, a⟩

theorem sq_ne_pow_succ_mul_zpow {p e : ℕ} (hp : 1 < p) (he : 1 ≤ e) {x : ℂ} (hx : ‖x‖ = 1)
    (hx1 : x ≠ 1) {n : ℤ} (hn : n = 1 ∨ n = -1) :
    (p : ℂ) ^ 2 ≠ (p : ℂ) ^ (e + 1) * x ^ n := by
  have hy1 : x ^ n ≠ 1 := by
    rcases hn with rfl | rfl
    · simpa using hx1
    · rw [zpow_neg_one]; exact fun h => hx1 (inv_eq_one.1 h)
  have hyn : ‖x ^ n‖ = 1 := by rw [norm_zpow, hx, one_zpow]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  intro h
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · have : e = 1 := by omega
    subst this
    have h' : (p : ℂ) ^ 2 * x ^ n = (p : ℂ) ^ 2 := h.symm
    exact hy1 ((mul_eq_left₀ (pow_ne_zero 2 hp0)).1 h')
  · have h2 := congrArg norm h
    rw [norm_mul, hyn, mul_one, norm_pow, norm_pow, Complex.norm_natCast] at h2
    have hp' : (1 : ℝ) < p := by exact_mod_cast hp
    have := pow_lt_pow_right₀ hp' (show 2 < e + 1 by omega)
    linarith

theorem smoothing_integers_two_characters : ∀ (N l e : ℕ) (θ₁ θ₂ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l), 0 < N → l.Prime → ¬ l ∣ N → 1 ≤ e → θ₁ ≠ 1 → θ₂ ≠ 1 →
    ∃ c d : ℕ, 1 < c ∧ 1 < d ∧ c.Coprime (6 * N * l) ∧ d.Coprime (6 * N * l) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (c : ℂ) ^ e ≠ z) ∧
      ∀ n₁ n₂ : ℤ, (n₁ = 1 ∨ n₁ = -1) →
        (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₁ d ^ n₁ * ψ d ^ n₂) ∧
        (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₂ d ^ n₁ * ψ d ^ n₂) := by
  intro N l e θ₁ θ₂ ψ hN hl hlN he h₁ h₂
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : NeZero (N * l) := ⟨Nat.mul_ne_zero hN.ne' hl.ne_zero⟩
  have hcop : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN).symm
  have hM : 0 < 6 * N * l := Nat.mul_pos (Nat.mul_pos (by norm_num) hN) hl.pos
  obtain ⟨u, hu₁, hu₂⟩ := exists_unit_dirichletCharacter_ne_one_ne_one θ₁ θ₂ h₁ h₂
  obtain ⟨k, hkN, hkl⟩ := Nat.chineseRemainder hcop (u : ZMod N).val 1
  have hkN' : (k : ZMod N) = u := by
    rw [(ZMod.natCast_eq_natCast_iff k _ N).2 hkN, ZMod.natCast_zmod_val]
  have hkl' : (k : ZMod l) = 1 := by
    rw [(ZMod.natCast_eq_natCast_iff k 1 l).2 hkl, Nat.cast_one]
  have hk1 : k.Coprime N := (ZMod.isUnit_iff_coprime k N).1 (hkN' ▸ u.isUnit)
  have hk2 : k.Coprime l := (ZMod.isUnit_iff_coprime k l).1 (hkl' ▸ isUnit_one)
  have hunit : IsUnit (k : ZMod (N * l)) :=
    (ZMod.isUnit_iff_coprime k (N * l)).2 (Nat.Coprime.mul_right hk1 hk2)
  obtain ⟨p, hpgt, hp, hpk⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (6 * N * l)
  have hpN : (p : ZMod N) = u := by
    have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hpk
    rw [map_natCast, map_natCast] at this
    rw [this, hkN']
  have hpl : (p : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom (dvd_mul_left l N) (ZMod l)) hpk
    rw [map_natCast, map_natCast] at this
    rw [this, hkl']
  have hpcop : p.Coprime (6 * N * l) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hM hpgt)
  refine ⟨6 * N * l + 1, p, by omega, hp.one_lt, ?_, hpcop, ?_, ?_⟩
  · rw [add_comm, Nat.coprime_add_self_left]; exact Nat.coprime_one_left _
  · intro z hz h
    have h2 := congrArg norm h
    rw [norm_pow, Complex.norm_natCast, hz] at h2
    have hc' : (1 : ℝ) < ((6 * N * l + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < 6 * N * l + 1 by omega)
    have := one_lt_pow₀ hc' (show e ≠ 0 by omega)
    linarith
  · intro n₁ n₂ hn
    rw [hpl, map_one, one_zpow, mul_one, mul_one, hpN]
    exact ⟨sq_ne_pow_succ_mul_zpow hp.one_lt he (DirichletCharacter.unit_norm_eq_one _ _) hu₁ hn,
      sq_ne_pow_succ_mul_zpow hp.one_lt he (DirichletCharacter.unit_norm_eq_one _ _) hu₂ hn⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanEqTopOfSpanResidueEqTop
section
namespace GlobalTheory.ResidueSpanLift

open IsLocalRing

theorem mem_smul_top_of_entries {O : Type} [CommRing O] {a : ℕ} (I : Ideal O)
    (X : Matrix (Fin a) (Fin a) O) (h : ∀ i j, X i j ∈ I) :
    X ∈ I • (⊤ : Submodule O (Matrix (Fin a) (Fin a) O)) := by
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (h i j) Submodule.mem_top

theorem exists_lift {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O) (Y : Matrix (Fin a) (Fin a) (ResidueField O))
    (hY : Y ∈ Submodule.span (ResidueField O)
      (Set.range fun g : ι => (M g).map (residue O))) :
    ∃ Z ∈ Submodule.span O (Set.range M), Z.map (residue O) = Y := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨M g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by ext i j; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Z, hZ, rfl⟩ := hx
    obtain ⟨W, hW, rfl⟩ := hy
    exact ⟨Z + W, Submodule.add_mem _ hZ hW, by ext i j; simp⟩
  | smul c x _ hx =>
    obtain ⟨Z, hZ, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := residue_surjective c
    refine ⟨d • Z, Submodule.smul_mem _ _ hZ, ?_⟩
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem span_eq_top_of_span_residue_eq_top {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O)
    (h : Submodule.span (ResidueField O)
      (Set.range fun g : ι => (M g).map (residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  refine top_le_iff.mp ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O)
    Module.Finite.fg_top (maximalIdeal_le_jacobson _) ?_
  intro X _
  obtain ⟨Z, hZ, hZX⟩ := exists_lift M (X.map (residue O)) (h ▸ Submodule.mem_top)
  have hX : X = Z + (X - Z) := by abel
  rw [hX]
  refine Submodule.add_mem_sup hZ (mem_smul_top_of_entries _ _ fun i j => ?_)
  have := congrFun (congrFun hZX i) j
  simp only [Matrix.map_apply] at this
  rw [← residue_eq_zero_iff, Matrix.sub_apply, map_sub, this, sub_self]

end GlobalTheory.ResidueSpanLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitHeightSummableExpNegAbs
section
namespace GlobalTheory

open Finset


open Finset in
theorem _root_.GlobalTheory.splitHeight_summable_pi_prod {ι : Type} [Fintype ι] {α : ι → Type} {f : ∀ i, α i → ℝ}
    (h0 : ∀ i x, 0 ≤ f i x) (hf : ∀ i, Summable (f i)) :
    Summable fun n : ∀ i, α i => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' x, f i x)
    (fun n => Finset.prod_nonneg fun i _ => h0 i (n i)) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset fun i => s.image fun n : (∀ i, α i) => n i, ∏ i, f i (n i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ =>
          Finset.prod_nonneg fun i _ => h0 i (n i)
        intro n hn
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ hn
    _ = ∏ i, ∑ x ∈ s.image fun n : (∀ i, α i) => n i, f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' x, f i x := Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => h0 i x)
        fun i _ => (hf i).sum_le_tsum _ fun x _ => h0 i x

end GlobalTheory
end

