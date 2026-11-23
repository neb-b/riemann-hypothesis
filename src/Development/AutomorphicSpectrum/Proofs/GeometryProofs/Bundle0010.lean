module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIdealExtensionLocalDomain
section
namespace GlobalTheory.CompanionTheory.Ggeo.RegularDvd

def Div {R B : Type} [CommRing R] [CommRing B] (u : R →+* B) (m : Ideal B) (x y : B) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (ψ : B →+* O),
    (∀ b, b ∉ m → IsUnit (ψ b)) ∧ (∀ b ∈ m, ¬ IsUnit (ψ b)) ∧
      Function.Injective (ψ.comp u) ∧ ∃ c, ψ x = ψ y * c

theorem exists_uniformizer {R : Type} [CommRing R] [IsDedekindDomain R] (p : Ideal R)
    (hp : p.IsMaximal) (hne : p ≠ ⊥) (d : R) (hd : d ≠ 0) :
    ∃ π : R, π ≠ 0 ∧ π ∈ p ∧ (∀ x ∈ p, ∃ s, s ∉ p ∧ ∃ z, s * x = π * z) ∧
      ∃ (a : ℕ) (t t' : R), t ∉ p ∧ t' ∉ p ∧ t * d = t' * π ^ a := by
  haveI := hp.isPrime
  let A := Localization.AtPrime p
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hne A
  have hinj : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A p.primeCompl_le_nonZeroDivisors
  have hunit : ∀ x : R, IsUnit (algebraMap R A x) ↔ x ∉ p := fun x =>
    IsLocalization.AtPrime.isUnit_to_map_iff A p x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨⟨π, s⟩, hs⟩ := IsLocalization.surj p.primeCompl ϖ
  have hsu : IsUnit (algebraMap R A (s : R)) := (hunit _).2 s.2
  have hπ : Irreducible (algebraMap R A π) := by
    have : Associated ϖ (algebraMap R A π) := ⟨hsu.unit, by simpa using hs⟩
    exact this.irreducible hϖ
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact hπ.ne_zero (map_zero _)
  · by_contra h
    exact hπ.not_isUnit ((hunit π).2 h)
  · intro x hx
    have hmem : algebraMap R A x ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
      simpa using hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ, Ideal.mem_span_singleton] at hmem
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨⟨z0, s0⟩, hz0⟩ := IsLocalization.surj p.primeCompl z
    refine ⟨s0, s0.2, z0, hinj ?_⟩
    simp only [map_mul] at hz0 ⊢
    rw [hz, ← hz0]
    ring
  · have hd' : algebraMap R A d ≠ 0 := fun h => hd (hinj (by simpa using h))
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd' hπ
    obtain ⟨⟨w0, t0⟩, hw0⟩ := IsLocalization.surj p.primeCompl (w : A)
    have ht0 : IsUnit (algebraMap R A (t0 : R)) := (hunit _).2 t0.2
    have hw0u : w0 ∉ p := by
      rw [← hunit, ← hw0]
      exact w.isUnit.mul ht0
    refine ⟨n, w0, t0, hw0u, t0.2, hinj ?_⟩
    simp only [map_mul, map_pow] at hw0 ⊢
    rw [← hw, ← hw0]
    ring

theorem exists_maximal_not_mem {R B : Type} [CommRing R] [CommRing B] (u : R →+* B)
    (hft : u.FiniteType) (p : Ideal R) (hp : p.IsMaximal)
    (hprime : ∀ a b : B, a * b ∈ p.map u → a ∈ p.map u ∨ b ∈ p.map u)
    (g : B) (hg : g ∉ p.map u) : ∃ m : Ideal B, m.IsMaximal ∧ p.map u ≤ m ∧ g ∉ m := by
  have hPne : p.map u ≠ ⊤ := fun h => hg (h ▸ Submodule.mem_top)
  haveI hP : (p.map u).IsPrime := ⟨hPne, fun {a b} h => hprime a b h⟩
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  let q : R ⧸ p →+* B ⧸ p.map u := Ideal.quotientMap (p.map u) u Ideal.le_comap_map
  have hq : q.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk p)
    have : q.comp (Ideal.Quotient.mk p) = (Ideal.Quotient.mk (p.map u)).comp u :=
      Ideal.quotientMap_comp_mk _
    rw [this]
    exact (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hft
  haveI : IsJacobsonRing (B ⧸ p.map u) := hq.isJacobsonRing
  have hj : (⊥ : Ideal (B ⧸ p.map u)).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance Ideal.isPrime_bot.isRadical
  by_contra h
  push_neg at h
  have hmem : Ideal.Quotient.mk (p.map u) g ∈ (⊥ : Ideal (B ⧸ p.map u)).jacobson := by
    refine (Ideal.mem_sInf).2 ?_
    rintro J ⟨-, hJ⟩
    haveI := hJ
    have hc : (J.comap (Ideal.Quotient.mk (p.map u))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    refine h _ hc ?_
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact J.zero_mem
  rw [hj, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hg hmem

theorem exists_of_mem_map {R B : Type} [CommRing R] [CommRing B] (u : R →+* B) (p : Ideal R)
    (hp : p.IsPrime) (π : R) (hloc : ∀ x ∈ p, ∃ s, s ∉ p ∧ ∃ z, s * x = π * z)
    (g : B) (hg : g ∈ p.map u) : ∃ t, t ∉ p ∧ ∃ h, u t * g = u π * h := by
  refine Submodule.span_induction (p := fun g _ => ∃ t, t ∉ p ∧ ∃ h, u t * g = u π * h)
    ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, z, hz⟩ := hloc x hx
    exact ⟨s, hs, u z, by rw [← map_mul, hz, map_mul]⟩
  · exact ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), 0, by simp⟩
  · rintro x y - - ⟨t₁, ht₁, h₁, e₁⟩ ⟨t₂, ht₂, h₂, e₂⟩
    refine ⟨t₁ * t₂, fun h => (hp.mem_or_mem h).elim ht₁ ht₂, u t₂ * h₁ + u t₁ * h₂, ?_⟩
    rw [map_mul]
    linear_combination (u t₂) * e₁ + (u t₁) * e₂
  · rintro b x - ⟨t, ht, h, e⟩
    refine ⟨t, ht, b * h, ?_⟩
    rw [smul_eq_mul]
    linear_combination b * e

theorem map_not_mem {R B : Type} [CommRing R] [CommRing B] (u : R →+* B) (p : Ideal R)
    (hp : p.IsMaximal) (m : Ideal B) (hm : m.IsMaximal) (hpm : p.map u ≤ m) (t : R) (ht : t ∉ p) :
    u t ∉ m := by
  intro h
  have hle : p ≤ m.comap u := Ideal.map_le_iff_le_comap.1 hpm
  have hne : m.comap u ≠ ⊤ := (Ideal.comap_ne_top _ hm.ne_top)
  exact ht ((hp.eq_of_le hne hle).symm ▸ h)

theorem local_pow {R B : Type} [CommRing R] [CommRing B] (u : R →+* B) (hft : u.FiniteType)
    (p : Ideal R) (hp : p.IsMaximal)
    (hprime : ∀ a b : B, a * b ∈ p.map u → a ∈ p.map u ∨ b ∈ p.map u)
    (π : R) (hπ0 : π ≠ 0) (hπ : π ∈ p) (hloc : ∀ x ∈ p, ∃ s, s ∉ p ∧ ∃ z, s * x = π * z) (a : ℕ) :
    ∀ g : B, (∀ m : Ideal B, m.IsMaximal → p.map u ≤ m → Div u m g (u π ^ a)) →
      ∃ t, t ∉ p ∧ ∃ h, u t * g = u π ^ a * h := by
  have hpp := hp.isPrime
  induction a with
  | zero =>
    intro g _
    exact ⟨1, fun h => hpp.ne_top ((Ideal.eq_top_iff_one _).2 h), g, by simp⟩
  | succ a ih =>
    intro g hg
    have hgP : g ∈ p.map u := by
      by_contra hn
      obtain ⟨m, hm, hpm, hgm⟩ := exists_maximal_not_mem u hft p hp hprime g hn
      obtain ⟨O, _, _, ψ, hu, hnu, -, c, hc⟩ := hg m hm hpm
      have hπm : u π ∈ m := hpm (Ideal.mem_map_of_mem u hπ)
      refine hnu _ hπm ?_
      have h1 : IsUnit (ψ (u π) * (ψ (u π) ^ a * c)) := by
        have := hu g hgm
        rw [hc, map_pow] at this
        rwa [pow_succ', mul_assoc] at this
      exact isUnit_of_mul_isUnit_left h1
    obtain ⟨t, ht, g', e⟩ := exists_of_mem_map u p hpp π hloc g hgP
    obtain ⟨t₂, ht₂, h, e₂⟩ := ih g' (fun m hm hpm => by
      obtain ⟨O, i₁, i₂, ψ, hu, hnu, hinj, c, hc⟩ := hg m hm hpm
      refine ⟨O, i₁, i₂, ψ, hu, hnu, hinj, ψ (u t) * c, ?_⟩
      have hne : ψ (u π) ≠ 0 := fun h0 => hπ0 (hinj (by simpa using h0))
      have e' : ψ (u t) * ψ g = ψ (u π) * ψ g' := by rw [← map_mul, e, map_mul]
      apply mul_left_cancel₀ hne
      rw [← e', hc, map_pow, map_pow]
      ring)
    refine ⟨t₂ * t, fun h => (hpp.mem_or_mem h).elim ht₂ ht, h, ?_⟩
    rw [map_mul]
    linear_combination (u t₂) * e + (u π) * e₂

theorem dvd_of_local : ∀ (R B : Type) [CommRing R] [IsDedekindDomain R] [CommRing B] [IsDomain B]
    [IsNoetherianRing B] (u : R →+* B), u.FiniteType →
    (∀ p : Ideal R, p.IsMaximal → ∀ a b : B, a * b ∈ p.map u → a ∈ p.map u ∨ b ∈ p.map u) →
    ∀ (f : B) (d : R), d ≠ 0 →
    (∀ m : Ideal B, m.IsMaximal → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (ψ : B →+* O),
      (∀ b, b ∉ m → IsUnit (ψ b)) ∧ (∀ b ∈ m, ¬ IsUnit (ψ b)) ∧
        Function.Injective (ψ.comp u) ∧ ∃ c, ψ f = ψ (u d) * c) →
    ∃ a, f = u d * a := by
  intro R B _ _ _ _ _ u hft hprime f d hd H
  let I : Ideal R :=
    { carrier := {r | ∃ a, u r * f = u d * a}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by rw [map_add (f := _)]; linear_combination ha + hb⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        exact ⟨u c * a, by rw [smul_eq_mul, map_mul]; linear_combination (u c) * ha⟩ }
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, by simpa using ha⟩
  exfalso
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
  have hpp := hp.isPrime
  have hdI : d ∈ I := ⟨f, rfl⟩
  have hne : p ≠ ⊥ := fun h => hd (by simpa [h] using hIp hdI)
  obtain ⟨π, hπ0, hπ, hloc, a, t, t', ht, ht', e⟩ := exists_uniformizer p hp hne d hd
  obtain ⟨s, hs, h, es⟩ := local_pow u hft p hp (hprime p hp) π hπ0 hπ hloc a f
    (fun m hm hpm => by
      obtain ⟨O, i₁, i₂, ψ, hu, hnu, hinj, c, hc⟩ := H m hm
      obtain ⟨v, hv⟩ := (hu _ (map_not_mem u p hp m hm hpm t ht)).exists_left_inv
      refine ⟨O, i₁, i₂, ψ, hu, hnu, hinj, v * ψ (u t') * c, ?_⟩
      have e' : ψ (u t) * ψ (u d) = ψ (u t') * ψ (u π) ^ a := by
        rw [← map_mul, ← map_mul, ← map_pow, ← map_pow, ← map_mul, ← map_mul, e]
      rw [hc, map_pow]
      linear_combination (-(ψ (u d)) * c) * hv + c * v * e')
  have hmem : t' * s ∈ I := by
    refine ⟨u t * h, ?_⟩
    have e' : u t * u d = u t' * u π ^ a := by rw [← map_mul, e, map_mul, map_pow]
    rw [map_mul]
    linear_combination (u t') * es + h * (-e')
  exact (hpp.mem_or_mem (hIp hmem)).elim ht' hs

end GlobalTheory.CompanionTheory.Ggeo.RegularDvd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveElementPowersIndep
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HopfPrim

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

theorem comul_pow_of_primitive (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (i : ℕ) :
    Coalgebra.comul (R := k) (f ^ i) =
      ∑ l ∈ Finset.range (i + 1), (i.choose l : k) • ((f ^ l) ⊗ₜ[k] (f ^ (i - l))) := by
  have h1 : Coalgebra.comul (R := k) (f ^ i) = (f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) ^ i := by
    rw [← hf, ← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]
  rw [h1, add_pow]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_pow, mul_one, one_mul,
    Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]

noncomputable def convPow (y : A →ₗ[k] k) : ℕ → (A →ₗ[k] k)
  | 0 => Coalgebra.counit
  | m + 1 => LinearMap.mul' k k ∘ₗ TensorProduct.map y (convPow y m) ∘ₗ Coalgebra.comul

theorem convPow_succ_pow (y : A →ₗ[k] k) (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (m i : ℕ) :
    convPow y (m + 1) (f ^ i) =
      ∑ l ∈ Finset.range (i + 1), (i.choose l : k) * (y (f ^ l) * convPow y m (f ^ (i - l))) := by
  simp only [convPow, LinearMap.comp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comul_pow_of_primitive f hf i, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, map_smul, TensorProduct.map_tmul, LinearMap.mul'_apply, smul_eq_mul]

theorem convPow_pow (y : A →ₗ[k] k) (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f)
    (hy1 : y 1 = 0) (hyf : y f = 1) (m : ℕ) :
    (∀ i < m, convPow y m (f ^ i) = 0) ∧ convPow y m (f ^ m) = (m.factorial : k) := by
  induction m with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    simp [convPow]
  | succ m ih =>
    have hterm : ∀ i ≤ m + 1, ∀ l ∈ Finset.range (i + 1), l ≠ 1 →
        (i.choose l : k) * (y (f ^ l) * convPow y m (f ^ (i - l))) = 0 := by
      intro i hi l hl hl1
      rcases Nat.lt_or_ge l 2 with h | h
      · have : l = 0 := by omega
        subst this
        simp [hy1]
      · have hlt : i - l < m := by
          have := Finset.mem_range.mp hl
          omega
        rw [ih.1 _ hlt, mul_zero, mul_zero]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [convPow_succ_pow y f hf m i]
      refine Finset.sum_eq_zero (fun l hl => ?_)
      by_cases hl1 : l = 1
      · subst hl1
        have hlt : i - 1 < m := by
          have := Finset.mem_range.mp hl
          omega
        rw [ih.1 _ hlt, mul_zero, mul_zero]
      · exact hterm i hi.le l hl hl1
    · rw [convPow_succ_pow y f hf m (m + 1),
        Finset.sum_eq_single 1 (fun l hl hl1 => hterm (m + 1) le_rfl l hl hl1)
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
      rw [pow_one, hyf, Nat.add_sub_cancel, ih.2, Nat.choose_one_right, Nat.factorial_succ]
      push_cast
      ring

theorem counit_eq_zero_of_primitive [Nontrivial A] (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) :
    Coalgebra.counit (R := k) f = 0 := by
  have key := congrArg (fun t => TensorProduct.lid k A (LinearMap.rTensor A Coalgebra.counit t)) hf
  simp only [Coalgebra.rTensor_counit_comul, map_add (f := _), LinearMap.rTensor_tmul,
    TensorProduct.lid_tmul, Bialgebra.counit_one, one_smul] at key
  have h2 : Coalgebra.counit (R := k) f • (1 : A) = 0 := by
    have := congrArg (· - f) key
    simpa using this.symm
  rw [Algebra.smul_def, mul_one] at h2
  exact (algebraMap k A).injective (h2.trans (map_zero _).symm)

theorem exists_form_of_primitive (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (hf0 : f ≠ 0) :
    ∃ y : A →ₗ[k] k, y 1 = 0 ∧ y f = 1 := by
  have : Nontrivial A := nontrivial_of_ne f 0 hf0
  have hε := counit_eq_zero_of_primitive f hf
  let p : Submodule k A := k ∙ (1 : A)
  have hfp : Submodule.Quotient.mk (p := p) f ≠ 0 := by
    rw [ne_eq, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    rintro ⟨a, rfl⟩
    apply hf0
    rw [map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one] at hε
    rw [hε, zero_smul]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ p), φ (Submodule.Quotient.mk f) ≠ 0 := by
    by_contra h
    push Not at h
    exact hfp ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  refine ⟨(φ (Submodule.Quotient.mk f))⁻¹ • (φ ∘ₗ p.mkQ), ?_, ?_⟩
  · have h1 : Submodule.Quotient.mk (p := p) (1 : A) = 0 :=
      (Submodule.Quotient.mk_eq_zero p).mpr (Submodule.mem_span_singleton_self 1)
    simp [h1]
  · simp [inv_mul_cancel₀ hφ]

theorem powers_indep_of_primitive :
    ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] (f : A),
    Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f → f ≠ 0 →
    ∀ c : ℕ → k, ∑ i ∈ Finset.range p, c i • f ^ i = 0 → ∀ i < p, c i = 0 := by
  intro k _ p _ _ A _ _ _ _ f hf hf0 c hsum
  obtain ⟨y, hy1, hyf⟩ := exists_form_of_primitive f hf hf0
  have key : ∀ m < p, (∀ i, m < i → i < p → c i = 0) → c m = 0 := by
    intro m hm hgt
    have h := congrArg (convPow y m) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h
    simp only [map_smul, smul_eq_mul] at h
    rw [Finset.sum_eq_single m] at h
    · rw [(convPow_pow y f hf hy1 hyf m).2] at h
      have hfact : (m.factorial : k) ≠ 0 := by
        rw [ne_eq, CharP.cast_eq_zero_iff k p, Nat.Prime.dvd_factorial (Fact.out)]
        omega
      exact (mul_eq_zero.mp h).resolve_right hfact
    · intro i hi hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · rw [(convPow_pow y f hf hy1 hyf m).1 i h', mul_zero]
      · rw [hgt i h' (Finset.mem_range.mp hi), zero_mul]
    · intro h'
      exact absurd (Finset.mem_range.mpr hm) h'
  have hall : ∀ n, ∀ i < p, p - 1 - i < n → c i = 0 := by
    intro n
    induction n with
    | zero => intro i _ h; omega
    | succ n ih =>
      intro i hi hn
      exact key i hi (fun j hij hj => ih j hj (by omega))
  intro i hi
  exact hall p i hi (by omega)

end GlobalTheory.CompanionTheory.HopfPrim
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SurjectiveOfDualHomomorphismKernelKilled
section
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem finite_primeSpectrum_height_one {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {a : A} (ha : a ≠ 0) :
    {P : PrimeSpectrum A | a ∈ P.asIdeal ∧ P.asIdeal.height = 1}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).preimage
    (f := PrimeSpectrum.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_
  rintro ⟨P, hP⟩ ⟨haP, h1⟩
  simp only at haP h1
  refine ⟨⟨hP, (Ideal.span_singleton_le_iff_mem _).mpr haP⟩, fun Q hQ hQP => ?_⟩
  have := hQ.1
  have haQ : a ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.2
  have hQ0 : Q ≠ ⊥ := fun h => ha (by rw [h] at haQ; exact haQ)
  have hQ1 : P.height ≤ Q.height := by
    rw [h1]
    exact Order.one_le_iff_ne_zero.mpr (fun h => hQ0 (Ideal.height_eq_zero_iff_eq_bot.mp h))
  exact (Ideal.eq_of_le_of_height_le (I := Q) hQP hQ1).ge

theorem exists_primeSpectrum_height_one_le {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {a : A} (ha : a ≠ 0) (P : PrimeSpectrum A) (hP : a ∈ P.asIdeal) :
    ∃ Q : PrimeSpectrum A, a ∈ Q.asIdeal ∧ Q.asIdeal.height = 1 ∧ Q ≤ P := by
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a}) (J := P.asIdeal)
    ((Ideal.span_singleton_le_iff_mem _).mpr hP)
  have hQp : Q.IsPrime := hQ.1.1
  have haQ : a ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.1.2
  have hQ0 : Q ≠ ⊥ := fun h => ha (by rw [h] at haQ; exact haQ)
  refine ⟨⟨Q, hQp⟩, haQ, le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ)
    (Order.one_le_iff_ne_zero.mpr (fun h => hQ0 (Ideal.height_eq_zero_iff_eq_bot.mp h))), hQP⟩

theorem ringKrullDim_stalk_fromSpec {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(Z, U)) :
    ringKrullDim (Z.presheaf.stalk (hU.fromSpec P)) = P.asIdeal.height := by
  have hmem : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  letI := TopCat.Presheaf.algebra_section_stalk Z.presheaf (U := U) ⟨hU.fromSpec P, hmem⟩
  have := hU.isLocalization_stalk' P hmem
  exact @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ P.asIdeal _ _ _ _ this

theorem fromSpec_notMem_basicOpen_iff {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (f : Γ(Z, ⊤)) (P : PrimeSpectrum Γ(Z, U)) :
    hU.fromSpec P ∉ Z.basicOpen f ↔
      Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f ∈ P.asIdeal := by
  have hmem : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  have h := hU.fromSpec_preimage_basicOpen (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f)
  have h2 : hU.fromSpec P ∈ Z.basicOpen (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f) ↔
      Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f ∉ P.asIdeal := by
    rw [← PrimeSpectrum.mem_basicOpen, ← h]
    rfl
  rw [Scheme.basicOpen_res] at h2
  have h3 : hU.fromSpec P ∈ U ⊓ Z.basicOpen f ↔ hU.fromSpec P ∈ Z.basicOpen f :=
    ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩
  rw [← h3, h2, not_not]

theorem finite_codim_one_zero_set_and_exists :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsNoetherian Z] (ϖ : Γ(Z, ⊤)), ϖ ≠ 0 →
      {x : Z | x ∉ Z.basicOpen ϖ ∧ ringKrullDim (Z.presheaf.stalk x) = 1}.Finite ∧
      ∀ y : Z, y ∉ Z.basicOpen ϖ →
        ∃ x : Z, x ∉ Z.basicOpen ϖ ∧ ringKrullDim (Z.presheaf.stalk x) = 1 ∧
          y ∈ closure {x} := by
  intro Z _ _ ϖ hϖ
  have hex : ∀ y : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ y ∈ U := fun y => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨U, hU, hy⟩
  choose U hU hyU using hex
  have hne : ∀ y, Nonempty (U y) := fun y => ⟨⟨y, hyU y⟩⟩
  have hnoeth : ∀ y, IsNoetherianRing Γ(Z, U y) := fun y =>
    IsLocallyNoetherian.component_noetherian ⟨U y, hU y⟩
  have hres : ∀ y, Z.presheaf.map (homOfLE (le_top : U y ≤ ⊤)).op ϖ ≠ 0 := fun y h =>
    hϖ (map_injective_of_isIntegral Z (homOfLE (le_top : U y ≤ ⊤)) (h.trans (map_zero _).symm))
  constructor
  · obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : Z => (U y : Set Z))
      (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩)
    refine (t.finite_toSet.biUnion (fun y _ =>
      (finite_primeSpectrum_height_one (hres y)).image (hU y).fromSpec)).subset ?_
    rintro x ⟨hx, hx1⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
    rw [← (hU y).range_fromSpec] at hxy
    obtain ⟨P, rfl⟩ := hxy
    refine ⟨P, ⟨(fromSpec_notMem_basicOpen_iff (hU y) ϖ P).mp hx, ?_⟩, rfl⟩
    rw [ringKrullDim_stalk_fromSpec (hU y) P] at hx1
    exact_mod_cast hx1
  · intro y hy
    have hy' : y ∈ Set.range (hU y).fromSpec := by
      rw [(hU y).range_fromSpec]; exact hyU y
    obtain ⟨P, hP⟩ := hy'
    obtain ⟨Q, hQ, hQ1, hQP⟩ := exists_primeSpectrum_height_one_le (hres y) P
      ((fromSpec_notMem_basicOpen_iff (hU y) ϖ P).mp (by rw [hP]; exact hy))
    refine ⟨(hU y).fromSpec Q, (fromSpec_notMem_basicOpen_iff (hU y) ϖ Q).mpr hQ, ?_, ?_⟩
    · rw [ringKrullDim_stalk_fromSpec (hU y) Q, hQ1]; rfl
    · have := ((PrimeSpectrum.le_iff_specializes Q P).mp hQP).map (hU y).fromSpec.continuous
      rw [hP] at this
      exact specializes_iff_mem_closure.mp this

end GlobalTheory.CompanionTheory.Ar.Flat
end

