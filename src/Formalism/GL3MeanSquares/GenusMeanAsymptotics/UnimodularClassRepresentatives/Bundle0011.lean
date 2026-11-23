module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0008
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0009
public import Mathlib

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsHermSemilocalLocRing
section
open NumberField

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace BE

theorem exists_gen {R : Type*} [CommRing R] [IsDedekindDomain R] {I P Q : Ideal R} (hI : I ≠ ⊥)
    (hP : P.IsPrime) (hQ : Q.IsPrime) :
    ∃ r ∈ I, r ≠ 0 ∧ ∃ s : R, s ∉ P ∧ s ∉ Q ∧ ∀ x ∈ I, ∃ y : R, s * x = r * y := by
  have hIP : ∀ {P' : Ideal R}, P'.IsPrime → ¬ (I ≤ I * P') := by
    intro P' hP' hle
    have e : I * P' = I * ⊤ := by
      rw [Ideal.mul_top]
      exact le_antisymm (Ideal.mul_le_inf.trans inf_le_left) hle
    exact hP'.ne_top (mul_left_cancel₀ (by rwa [Ideal.zero_eq_bot]) e)
  have hnot : ¬ ((I : Set R) ⊆ ((I * P : Ideal R) : Set R) ∪ ((I * Q : Ideal R) : Set R)) := by
    rw [Ideal.subset_union]
    rintro (h | h)
    · exact hIP hP h
    · exact hIP hQ h
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.mp hnot
  simp only [Set.mem_union, SetLike.mem_coe, not_or] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr.1 (Submodule.zero_mem _)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {r} :=
    Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrI))
  have hJP : ∀ {P' : Ideal R}, r ∉ I * P' → ¬ (J ≤ P') := by
    intro P' hr' hJ'
    apply hr'
    have hrr : r ∈ Ideal.span {r} := Ideal.mem_span_singleton_self r
    rw [hJ] at hrr
    exact Ideal.mul_mono_right hJ' hrr
  have hnot2 : ¬ ((J : Set R) ⊆ (P : Set R) ∪ (Q : Set R)) := by
    rw [Ideal.subset_union]
    rintro (h | h)
    · exact hJP hr.1 h
    · exact hJP hr.2 h
  obtain ⟨s, hsJ, hs⟩ := Set.not_subset.mp hnot2
  simp only [Set.mem_union, SetLike.mem_coe, not_or] at hs
  refine ⟨r, hrI, hr0, s, hs.1, hs.2, fun x hx => ?_⟩
  have hmem : s * x ∈ Ideal.span {r} := by
    rw [hJ, mul_comm s x]
    exact Ideal.mul_mem_mul hx hsJ
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨y, by rw [← hy, mul_comm]⟩

theorem avoid_two {R : Type*} [CommRing R] {P Q : Ideal R} (hQ : Q.IsPrime) {a s m : R} (k : R)
    (ha : a ∈ P) (hsP : s ∉ P) (hsQ : s ∉ Q) (hm : m ∉ Q) :
    (s - k * a ∉ P ∧ s - k * a ∉ Q) ∨ (s - (k + m) * a ∉ P ∧ s - (k + m) * a ∉ Q) := by
  have hP : ∀ c : R, s - c * a ∉ P := fun c hc => hsP (by
    have := P.add_mem hc (P.mul_mem_left c ha)
    simpa using this)
  by_cases h1 : s - k * a ∈ Q
  · right
    refine ⟨hP _, fun h2 => ?_⟩
    have hma : m * a ∈ Q := by
      have := Q.sub_mem h1 h2
      have e : s - k * a - (s - (k + m) * a) = m * a := by ring
      rwa [e] at this
    rcases hQ.mem_or_mem hma with h | h
    · exact hm h
    · exact hsQ (by
        have := Q.add_mem h1 (Q.mul_mem_left k h)
        simpa using this)
  · left
    exact ⟨hP _, h1⟩

end BE

theorem principal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal)
    (A : AddSubgroup K) (hA : ∀ s ∈ locRing p, ∀ a ∈ A, s * a ∈ A) (h0 : ∃ a ∈ A, a ≠ 0)
    (ht : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ locRing p) :
    ∃ α ∈ A, α ≠ 0 ∧ ∀ a ∈ A, a * α⁻¹ ∈ locRing p := by
  obtain ⟨t, ht0, ht⟩ := ht
  have hpp := hp.isPrime
  let I : Ideal (𝓞 K) :=
    { carrier := {r | algebraMap (𝓞 K) K r * t⁻¹ ∈ A}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_add (f := _), add_mul] at *
        exact A.add_mem hx hy
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_assoc] at *
        exact hA _ (algebraMap_mem_locRing p c) _ hx }
  have hmemI : ∀ r : 𝓞 K, r ∈ I ↔ algebraMap (𝓞 K) K r * t⁻¹ ∈ A := fun r => Iff.rfl

  have hrep : ∀ a ∈ A, ∃ x ∈ I, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K x / (algebraMap (𝓞 K) K s * t) := by
    intro a ha
    obtain ⟨x, s, hs, hx⟩ := (mem_locR_iff hpp _).1 ((mem_locRing p _).1 (ht a ha))
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hpp hs
    have e : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K s * (t * a) := by
      rw [hx]; field_simp
    refine ⟨x, ?_, s, hs, ?_⟩
    · rw [hmemI, e]
      have : algebraMap (𝓞 K) K s * (t * a) * t⁻¹ = algebraMap (𝓞 K) K s * a := by field_simp
      rw [this]
      exact hA _ (algebraMap_mem_locRing p s) _ ha
    · rw [e]; field_simp
  have hI : I ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := h0
    obtain ⟨x, hx, s, hs, e⟩ := hrep a ha
    intro hbot
    rw [hbot, Ideal.mem_bot] at hx
    apply ha0
    rw [e, hx]; simp
  obtain ⟨r, hrI, hr0, s, hsP, hsQ, hgen⟩ := BE.exists_gen hI hpp (conjIdeal_isPrime hpp)
  have hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := (mem_hcompl_iff hpp s).2 ⟨hsP, hsQ⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hpp hs
  have hr0' : algebraMap (𝓞 K) K r ≠ 0 := by
    intro h
    exact hr0 ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 h)
  refine ⟨algebraMap (𝓞 K) K r * t⁻¹, (hmemI r).1 hrI, mul_ne_zero hr0' (inv_ne_zero ht0), ?_⟩
  intro a ha
  obtain ⟨x, hx, s', hs', e⟩ := hrep a ha
  have hs0' := algebraMap_ne_zero_of_mem_hcompl hpp hs'
  obtain ⟨y, hy⟩ := hgen x hx
  have hy' : algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K x
      = algebraMap (𝓞 K) K r * algebraMap (𝓞 K) K y := by
    rw [← map_mul, ← map_mul, hy]
  rw [mem_locRing, mem_locR_iff hpp]
  refine ⟨y, s * s', mul_mem hs hs', ?_⟩
  rw [e, map_mul]
  field_simp
  linear_combination hy'

theorem unit_or_locRing {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) (ha : a ∈ locRing p)
    (κ : K) (hκ : κ ∈ locRing p) (μ : K) (hna : a⁻¹ ∉ locRing p) (hμ : IsUnitIn (locRing p) μ) :
    IsUnitIn (locRing p) (1 - κ * a) ∨ IsUnitIn (locRing p) (1 - (κ + μ) * a) := by
  obtain ⟨a₁, s₁, hs₁, ea⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 ha)
  obtain ⟨k₁, s₂, hs₂, ek⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 hκ)
  obtain ⟨m₁, s₃, hs₃, em⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 hμ.2.1)
  have h1 := algebraMap_ne_zero_of_mem_hcompl hp hs₁
  have h2 := algebraMap_ne_zero_of_mem_hcompl hp hs₂
  have h3 := algebraMap_ne_zero_of_mem_hcompl hp hs₃
  have hm₁ : m₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := (isUnitIn_div_iff hp m₁ hs₃).1 (em ▸ hμ)
  have ha₁ : a₁ ∉ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    intro h
    have := (isUnitIn_div_iff hp a₁ hs₁).2 h
    rw [← ea] at this
    exact hna this.2.2
  have hQ := conjIdeal_isPrime hp
  set S : 𝓞 K := s₁ * s₂ * s₃ with hS
  have hSm : S ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem (mul_mem hs₁ hs₂) hs₃
  have hS' := (mem_hcompl_iff hp S).1 hSm
  have hM : m₁ * s₂ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem hm₁ hs₂
  have hM' := (mem_hcompl_iff hp _).1 hM
  have e1 : (1 - κ * a) = algebraMap (𝓞 K) K (S - (k₁ * s₃) * a₁) / algebraMap (𝓞 K) K S := by
    rw [ea, ek, hS]; simp only [map_sub, map_mul]; field_simp
  have e2 : (1 - (κ + μ) * a)
      = algebraMap (𝓞 K) K (S - (k₁ * s₃ + m₁ * s₂) * a₁) / algebraMap (𝓞 K) K S := by
    rw [ea, ek, em, hS]; simp only [map_sub, map_mul, map_add (f := _)]; field_simp
  rw [e1, e2, isUnitIn_div_iff hp _ hSm, isUnitIn_div_iff hp _ hSm, mem_hcompl_iff hp,
    mem_hcompl_iff hp]
  have hor : a₁ ∈ p ∨ a₁ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
    by_contra h
    push Not at h
    exact ha₁ ((mem_hcompl_iff hp a₁).2 h)
  rcases hor with h | h
  · exact BE.avoid_two hQ (k₁ * s₃) h hS'.1 hS'.2 hM'.2
  · rcases BE.avoid_two hp (k₁ * s₃) h hS'.2 hS'.1 hM'.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem isHermSemilocal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)}
    (hp : p.IsMaximal) : IsHermSemilocal (locRing p) := by
  exact ⟨fun _ ha => star_mem_locRing hp.isPrime ha, frac_locRing p, unram_locRing hK hp,
    principal_locRing hK hp, fun a ha κ hκ μ hna hμ => unit_or_locRing hp.isPrime a ha κ hκ μ hna hμ⟩

end Formalism.HermitianLattices.Ext.L3.WA
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LValEtaEqLValEtaF
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace Regroup

theorem tprod_eq_of_fibre {α β : Type*} {f : α → ℝ} (π : α → β) {g : β → ℝ} (hf : Multipliable f)
    (hg : ∀ b, HasProd (fun c : {x // π x = b} => f c.1) (g b)) : ∏' a, f a = ∏' b, g b := by
  have h1 : HasProd (fun p : (Σ b : β, {x // π x = b}) => f (Equiv.sigmaFiberEquiv π p))
      (∏' a, f a) := (Equiv.sigmaFiberEquiv π).hasProd_iff.2 hf.hasProd
  exact (HasProd.sigma h1 hg).tprod_eq.symm

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem comap_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
  haveI : P.IsMaximal := hP
  Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) P

theorem hasProd_fibre (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (M : ℕ) (hM : 1 ≤ M)
    (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    HasProd (fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1)
      (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
  classical
  obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
  have hmem : ∀ c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭},
      c.1.1 = P ∨ c.1.1 = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    intro c
    have h1 : c.1.1.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.1 := congrArg Subtype.val c.2
    exact (comap_eq_comap_iff hK hF hP c.1.2).1 (hP𝔭.trans h1.symm)
  have heta := etaF_comap hK hF hP
  rw [hP𝔭] at heta
  let c0 : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} := ⟨⟨P, hP⟩, Subtype.ext hP𝔭⟩
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have hN := absNorm_comap_inert hK hF hP hc
    rw [hP𝔭] at hN
    have hval : Formalism.HermitianLatticesTheory.eulerFac K M P =
        (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
      rw [← inv_inv (Formalism.HermitianLatticesTheory.eulerFac K M P), eulerFac_inv_inert hK hP hc, heta, if_pos hc, ← hN]
      push_cast
      rw [Real.sqrt_sq (Nat.cast_nonneg _)]
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (f := fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1) (s := {c0})
      (by
        intro b hb
        exfalso
        apply hb
        rw [Finset.mem_singleton]
        apply Subtype.ext
        apply Subtype.ext
        rcases hmem b with h | h
        · exact h
        · exact h.trans hc)
    rw [Finset.prod_singleton] at h
    rw [← hval]
    exact h
  · have hN := absNorm_comap_split hK hF hP hc
    rw [hP𝔭] at hN
    have hPb := conjIdeal_isMaximal hK hP
    have hPb𝔭 : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.1 := by
      rw [← hP𝔭]
      exact ((comap_eq_comap_iff hK hF hP hPb).2 (Or.inr rfl)).symm
    let c1 : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} :=
      ⟨⟨Formalism.HermitianLatticesTheory.conjIdeal (K := K) P, hPb⟩, Subtype.ext hPb𝔭⟩
    have hne : c0 ≠ c1 := by
      intro h
      exact hc (congrArg (fun c => c.1.1) h).symm
    have hval : Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) =
        (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
      rw [← inv_inv (Formalism.HermitianLatticesTheory.eulerFac K M P * _), eulerFac_mul_conj_inv_split hK hP hc M hM, heta,
        if_neg hc, hN, one_pow, one_mul]
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (f := fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1) (s := {c0, c1})
      (by
        intro b hb
        exfalso
        apply hb
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hmem b with h | h
        · exact Or.inl (Subtype.ext (Subtype.ext h))
        · exact Or.inr (Subtype.ext (Subtype.ext h)))
    rw [Finset.prod_pair hne] at h
    rw [← hval]
    exact h

end Regroup

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem lValEta_eq_lValEtaF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (M : ℕ) (hM : 2 ≤ M) :
    Formalism.HermitianLatticesTheory.lValEta K M = lValEtaF K F M := by
  unfold Formalism.HermitianLatticesTheory.lValEta lValEtaF
  exact Regroup.tprod_eq_of_fibre
    (fun x : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), Regroup.comap_isMaximal x.2⟩ :
        {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))
    (multipliable_eulerFac hK M hM) (Regroup.hasProd_fibre hK hF M (by omega))

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandG
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace GramDeterminantPositive

section

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem exists_ortho_ne_zero [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : k < finrank K V) : ∃ x : V, x ≠ 0 ∧ ∀ i, h (v i) x = 0 := by
  let f : V →ₗ[K] (Fin k → K) := LinearMap.pi fun i => h (v i)
  have hlt : finrank K (Fin k → K) < finrank K V := by
    rw [Module.finrank_fin_fun]; exact hk
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
  exact ⟨x, hx0, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩

theorem exists_basis_of_ortho [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : finrank K V = k) (ho : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (hne : ∀ i, h (v i) (v i) ≠ 0) : ∃ e : Basis (Fin k) K V, ∀ i, e i = v i := by
  have hli : LinearIndependent K v :=
    LinearMap.linearIndependent_of_isOrthoᵢ (B := h) (fun i j hij => ho i j hij) (fun i => hne i)
  have htop : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hk])
  exact ⟨Basis.mk hli htop.ge, fun i => Basis.mk_apply hli htop.ge i⟩

theorem exists_ortho_family [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) :
    ∀ k : ℕ, k ≤ finrank K V →
      ∃ v : Fin k → V, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, v i ≠ 0 := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, ho, hne⟩ := ih (by omega)
    obtain ⟨x, hx0, hx⟩ := exists_ortho_ne_zero h v (by omega)
    refine ⟨Fin.snoc v x, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hs.isRefl _ _ (hx j)
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hx i
      · intro hij
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact ho i j (fun e => hij (by rw [e]))
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.snoc_last]; exact hx0
      · rw [Fin.snoc_castSucc]; exact hne i

end

end GramDeterminantPositive

theorem orthBasisPos_holds : OrthBasisPos := by
  intro K _ _ _ hK V _ _ _ _ _ h hs hpos
  have hne0 : ∀ x : V, x ≠ 0 → h x x ≠ 0 := by
    intro x hx h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpos x hx φ
    rw [h0, map_zero] at this
    simp at this
  obtain ⟨v, ho, hne⟩ := GramDeterminantPositive.exists_ortho_family h hs (finrank K V) le_rfl
  obtain ⟨e, he⟩ := GramDeterminantPositive.exists_basis_of_ortho h v rfl ho (fun i => hne0 _ (hne i))
  refine ⟨e, fun i j hij => by rw [he, he]; exact ho i j hij, fun i => ⟨?_, ?_⟩⟩
  · exact hs.eq (e i) (e i)
  · exact hpos (e i) (e.ne_zero i)

section

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

end

namespace GramDeterminantPositive

end GramDeterminantPositive

end Formalism.HermitianLattices.Ext.L3
end
end

