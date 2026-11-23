module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFieldOfPoints
section
open Polynomial

namespace GlobalTheory.FiniteFieldOfPoints

theorem factor_of_range {C K₂ Ω : Type} [CommRing C] [Field K₂] [Field Ω]
    (j : K₂ →+* Ω) (ψ : C →+* Ω) (h : ∀ c, ∃ x, j x = ψ c) :
    ∃ ψ₀ : C →+* K₂, j.comp ψ₀ = ψ := by
  choose f hf using h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · apply j.injective; simp [hf]
  · intro a b; apply j.injective; simp [hf]
  · apply j.injective; simp [hf]
  · intro a b; apply j.injective; simp [hf]
  · ext c; simp [hf]

theorem exists_finite_field_of_points (K : Type) [Field K] (C : Type) [CommRing C] (φ : K →+* C)
    (hφ : RingHom.Finite φ) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)), FiniteDimensional K ↥E ∧
      ∀ (K₂ Ω : Type) [Field K₂] [Field Ω] (e : ↥E →+* K₂) (j : K₂ →+* Ω) (ψ : C →+* Ω),
        RingHom.comp ψ φ = RingHom.comp j (RingHom.comp e (algebraMap K ↥E)) →
        ∃ (ψ₀ : C →+* K₂), RingHom.comp j ψ₀ = ψ := by
  classical
  letI : Algebra K C := φ.toAlgebra
  haveI : Module.Finite K C := hφ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := C)
  have hint : ∀ c : C, IsIntegral K c := fun c => Algebra.IsIntegral.isIntegral c
  choose p hpm hpe using hint
  set P : K[X] := ∏ c ∈ s, p c with hP
  have hPm : P.Monic := monic_prod_of_monic _ _ (fun c _ => hpm c)
  have hsf : IsSplittingField K
      (IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K))) P :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  refine ⟨IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)),
    IsSplittingField.finiteDimensional _ P, ?_⟩
  generalize IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)) = E at hsf ⊢
  intro K₂ Ω _ _ e j ψ hc
  have hspl : (P.map (algebraMap K E)).Splits := hsf.splits'
  have hspl2 : (P.map (e.comp (algebraMap K E))).Splits := by
    rw [← Polynomial.map_map]; exact hspl.map e
  have hgen : ∀ c ∈ s, ψ c ∈ j.range := by
    intro c hcs
    have h0 : eval₂ φ c P = 0 := by
      rw [hP, eval₂_finsetProd]
      exact Finset.prod_eq_zero hcs (hpe c)
    have h1 : ((P.map (e.comp (algebraMap K E))).map j).IsRoot (ψ c) := by
      rw [Polynomial.map_map, ← hc, IsRoot, eval_map, ← hom_eval₂, h0, map_zero]
    exact hspl2.mem_range_of_isRoot (hPm.map _).ne_zero h1
  apply factor_of_range
  intro c
  have hmem : c ∈ Submodule.span K (s : Set C) := by rw [hs]; trivial
  change ψ c ∈ j.range
  induction hmem using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    refine ⟨e (algebraMap K E a), ?_⟩
    exact (RingHom.congr_fun hc a).symm

end GlobalTheory.FiniteFieldOfPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimesDvdOfDvdMulLocalization
section
namespace GlobalTheory

theorem localizedModule_mk_quotient_eq_zero_iff_dvd {R : Type} [CommRing R] (M : Submonoid R)
    (s c : R) :
    LocalizedModule.mkLinearMap M (R ⧸ Ideal.span {s}) (Ideal.Quotient.mk _ c) = 0 ↔
      algebraMap R (Localization M) s ∣ algebraMap R (Localization M) c := by
  rw [IsLocalizedModule.eq_zero_iff M, ← Ideal.mem_span_singleton, ← Set.image_singleton,
    ← Ideal.map_span, IsLocalization.algebraMap_mem_map_algebraMap_iff M]
  have key : ∀ m : R, m • (Ideal.Quotient.mk (Ideal.span {s}) c) = 0 ↔
      m * c ∈ Ideal.span {s} := by
    intro m
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    rfl
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, m.2, (key m).1 hm⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨⟨m, hm⟩, (key m).2 h⟩

theorem exists_finite_primes_dvd_of_dvd_mul_localization :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (s : R), s ≠ 0 → ∃ S : Set (PrimeSpectrum R), S.Finite ∧ ∀ (P : PrimeSpectrum R) (τ g : Localization.AtPrime P.asIdeal), (∀ Q ∈ S, Q ≤ P → τ ∉ Q.asIdeal.map (algebraMap R (Localization.AtPrime P.asIdeal))) → algebraMap R _ s ∣ g * τ → algebraMap R _ s ∣ g := by
  intro R _ _ _ s _
  refine ⟨PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R (R ⧸ Ideal.span {s}),
    (associatedPrimes.finite R _).preimage (fun _ _ _ _ h => PrimeSpectrum.ext h), ?_⟩
  intro P τ g hτ hd
  obtain ⟨a, v, rfl⟩ := IsLocalization.exists_mk'_eq P.asIdeal.primeCompl τ
  obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq P.asIdeal.primeCompl g
  have hab : algebraMap R (Localization.AtPrime P.asIdeal) s ∣ algebraMap R _ (a * b) := by
    rw [← IsLocalization.mk'_mul] at hd
    have h := hd.mul_right (algebraMap R _ ((u * v : P.asIdeal.primeCompl) : R))
    rwa [IsLocalization.mk'_spec, mul_comm b a] at h
  by_contra hg
  have hb : ¬ algebraMap R (Localization.AtPrime P.asIdeal) s ∣ algebraMap R _ b := by
    intro h
    apply hg
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact h.mul_right _
  have hx := mt (localizedModule_mk_quotient_eq_zero_iff_dvd P.asIdeal.primeCompl s b).1 hb
  have hax := (localizedModule_mk_quotient_eq_zero_iff_dvd P.asIdeal.primeCompl s (a * b)).2 hab
  obtain ⟨q, hq, hle⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing (Localization P.asIdeal.primeCompl) _ hx
  have hqp : q.IsPrime := hq.isPrime
  have haq : algebraMap R (Localization P.asIdeal.primeCompl) a ∈ q := by
    apply hle
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, algebraMap_smul, ← map_smul, ← hax,
      map_mul]
    rfl
  have hQ : q.comap (algebraMap R (Localization P.asIdeal.primeCompl)) ∈
      associatedPrimes R (R ⧸ Ideal.span {s}) :=
    Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      P.asIdeal.primeCompl (LocalizedModule.mkLinearMap P.asIdeal.primeCompl _) q hq
      (IsNoetherian.noetherian _)
  refine hτ ⟨q.comap (algebraMap R (Localization P.asIdeal.primeCompl)), hqp.comap _⟩ hQ ?_ ?_
  · intro r hr
    by_contra hrP
    exact hqp.ne_top (Ideal.eq_top_of_isUnit_mem q hr
      (IsLocalization.map_units (Localization P.asIdeal.primeCompl)
        (⟨r, hrP⟩ : P.asIdeal.primeCompl)))
  · rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ haq)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAwayOfAtPrime
section
namespace GlobalTheory.Desc

open scoped TensorProduct

theorem finiteType_away_of_pow_mul_mem {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (s : Finset C) (x : C) (h : ∀ c : C, ∃ n : ℕ, x ^ n * c ∈ Algebra.adjoin R (s : Set C)) :
    Algebra.FiniteType R (Localization.Away x) := by
  classical
  let φ := IsScalarTower.toAlgHom R C (Localization.Away x)
  let u : Localization.Away x := IsLocalization.Away.invSelf x
  have hu : φ x * u = 1 := IsLocalization.Away.mul_invSelf x
  refine ⟨⟨insert u (s.image φ), ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  have hU : u ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x)) :=
    Algebra.subset_adjoin (by simp)
  have hB : ∀ b ∈ Algebra.adjoin R (s : Set C),
      φ b ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x)) := by
    intro b hb
    have : φ b ∈ (Algebra.adjoin R (s : Set C)).map φ := ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    refine Algebra.adjoin_mono ?_ this
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_image]
    exact Or.inr hz
  obtain ⟨m, c, hc⟩ := IsLocalization.Away.surj x y
  obtain ⟨n, hn⟩ := h c
  have hc' : y * φ x ^ m = φ c := hc
  have : y = φ (x ^ n * c) * u ^ (n + m) := by
    rw [map_mul, map_pow, ← hc']
    calc y = y * (φ x * u) ^ (n + m) := by rw [hu]; simp
      _ = _ := by ring
  rw [this]
  exact mul_mem (hB _ hn) (pow_mem hU _)

theorem exists_pow_mul_mem_of_finiteType_away {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (f : R) (h : Algebra.FiniteType R (Localization.Away (algebraMap R C f))) :
    ∃ s : Finset C, ∀ c : C, ∃ n : ℕ, algebraMap R C f ^ n * c ∈ Algebra.adjoin R (s : Set C) := by
  classical
  set x := algebraMap R C f with hx
  let φ := algebraMap C (Localization.Away x)
  obtain ⟨t, ht⟩ := h.out
  choose m a ha using fun y : Localization.Away x => IsLocalization.Away.surj x y
  refine ⟨t.image a, fun c => ?_⟩
  set B := Algebra.adjoin R ((t.image a : Finset C) : Set C) with hB
  have hxB : x ∈ B := B.algebraMap_mem f
  have key : ∀ y ∈ Algebra.adjoin R (t : Set (Localization.Away x)),
      ∃ n : ℕ, ∃ b ∈ B, y * φ x ^ n = φ b := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      exact ⟨m y, a y, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), ha y⟩
    | algebraMap r =>
      exact ⟨0, algebraMap R C r, B.algebraMap_mem r, by
        rw [pow_zero, mul_one]; exact IsScalarTower.algebraMap_apply R C _ r⟩
    | add y z _ _ hy hz =>
      obtain ⟨n, b, hb, e⟩ := hy
      obtain ⟨k, d, hd, e'⟩ := hz
      refine ⟨n + k, b * x ^ k + d * x ^ n,
        add_mem (mul_mem hb (pow_mem hxB _)) (mul_mem hd (pow_mem hxB _)), ?_⟩
      rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← e, ← e']
      ring
    | mul y z _ _ hy hz =>
      obtain ⟨n, b, hb, e⟩ := hy
      obtain ⟨k, d, hd, e'⟩ := hz
      refine ⟨n + k, b * d, mul_mem hb hd, ?_⟩
      rw [map_mul, ← e, ← e']
      ring
  obtain ⟨n, b, hb, e⟩ := key (φ c) (by rw [ht]; trivial)
  rw [← map_pow, ← map_mul] at e
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq x e
  refine ⟨k + n, ?_⟩
  have : x ^ (k + n) * c = x ^ k * b := by rw [← hk]; ring
  rw [this]
  exact mul_mem (pow_mem hxB _) hb

theorem exists_smul_mem_of_finiteType_tensor {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (M : Submonoid R) (h : Algebra.FiniteType (Localization M) (Localization M ⊗[R] C)) :
    ∃ s : Finset C, ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ Algebra.adjoin R (s : Set C) := by
  classical
  let φ : C →ₐ[R] Localization M ⊗[R] C := Algebra.TensorProduct.includeRight
  have hloc : IsLocalizedModule M (TensorProduct.mk R (Localization M) C 1) :=
    (isLocalizedModule_iff_isBaseChange M (Localization M) _).2
      (TensorProduct.isBaseChange R C (Localization M))
  have hφ : ∀ c, TensorProduct.mk R (Localization M) C 1 c = φ c := fun _ => rfl
  obtain ⟨t, ht⟩ := h.out
  choose p hp using fun y => IsLocalizedModule.surj M (TensorProduct.mk R (Localization M) C 1) y
  refine ⟨t.image fun y => (p y).1, fun c => ?_⟩
  set B := Algebra.adjoin R ((t.image (fun y => (p y).1) : Finset C) : Set C) with hB
  have key : ∀ y ∈ Algebra.adjoin (Localization M) (t : Set (Localization M ⊗[R] C)),
      ∃ r ∈ M, ∃ b ∈ B, r • y = φ b := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      exact ⟨(p y).2, (p y).2.2, (p y).1, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), hp y⟩
    | algebraMap q =>
      obtain ⟨⟨a, r⟩, e⟩ := IsLocalization.surj M q
      refine ⟨r, r.2, algebraMap R C a, B.algebraMap_mem a, ?_⟩
      rw [φ.commutes, Algebra.smul_def, IsScalarTower.algebraMap_apply R (Localization M),
        IsScalarTower.algebraMap_apply R (Localization M) _ a, ← map_mul, mul_comm]
      exact congrArg _ e
    | add y z _ _ hy hz =>
      obtain ⟨n, hn, b, hb, e⟩ := hy
      obtain ⟨k, hk, d, hd, e'⟩ := hz
      refine ⟨n * k, mul_mem hn hk, k • b + n • d,
        add_mem (B.smul_mem hb _) (B.smul_mem hd _), ?_⟩
      rw [map_add (f := _), map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm k n]
    | mul y z _ _ hy hz =>
      obtain ⟨n, hn, b, hb, e⟩ := hy
      obtain ⟨k, hk, d, hd, e'⟩ := hz
      refine ⟨n * k, mul_mem hn hk, b * d, mul_mem hb hd, ?_⟩
      rw [map_mul, ← e, ← e', smul_mul_smul_comm]
  obtain ⟨r, hr, b, hb, e⟩ := key (φ c) (by rw [ht]; trivial)
  rw [← map_smul, ← hφ, ← hφ] at e
  obtain ⟨k, hk⟩ := IsLocalizedModule.exists_of_eq (S := M) e
  refine ⟨k * r, mul_mem k.2 hr, ?_⟩
  have : algebraMap R C (k * r) * c = (k : R) • b := by
    rw [← Algebra.smul_def, mul_smul]; exact hk
  rw [this]
  exact B.smul_mem hb _

theorem exists_mul_mem_of_mul_mem {R C : Type} [CommRing R] [CommRing C] [IsDomain C] [Algebra R C]
    (B : Subalgebra R C) [IsNoetherianRing B] (x : C) (hx : x ≠ 0) (M : Submonoid R)
    (h : ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ B) :
    ∃ g ∈ M, ∀ c : C, x * c ∈ B → algebraMap R C g * c ∈ B := by
  classical
  let J : Ideal B := (Ideal.span {x}).comap B.val
  obtain ⟨t, ht⟩ : J.FG := IsNoetherian.noetherian J
  choose r hrM hr using h
  have hJ : ∀ b : B, ∃ c : C, b ∈ J → (b : C) = x * c := by
    intro b
    by_cases hb : b ∈ J
    · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hb)
      exact ⟨c, fun _ => by rw [mul_comm]; exact hc.symm⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose q hq using hJ
  refine ⟨∏ b ∈ t, r (q b), prod_mem fun b _ => hrM _, ?_⟩
  set g := ∏ b ∈ t, r (q b) with hg
  have key : ∀ b ∈ Ideal.span (t : Set B), ∃ c : C, (b : C) = x * c ∧ algebraMap R C g * c ∈ B := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine ⟨q b, hq b (ht ▸ Ideal.subset_span hb), ?_⟩
      rw [hg, ← Finset.prod_erase_mul t _ hb, map_mul, mul_assoc]
      exact mul_mem (B.algebraMap_mem _) (hr _)
    | zero => exact ⟨0, by simp, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, e, hc⟩ := hy
      obtain ⟨d, e', hd⟩ := hz
      exact ⟨c + d, by rw [mul_add, ← e, ← e']; rfl, by rw [mul_add]; exact add_mem hc hd⟩
    | smul a y _ hy =>
      obtain ⟨c, e, hc⟩ := hy
      refine ⟨a * c, by rw [mul_left_comm, ← e]; rfl, ?_⟩
      rw [mul_left_comm]
      exact mul_mem a.2 hc
  intro c hc
  obtain ⟨d, e, hd⟩ := key ⟨x * c, hc⟩ (by
    rw [ht]
    exact Ideal.mem_comap.2 (Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩))
  rw [mul_left_cancel₀ hx e]
  exact hd

theorem exists_finiteType_away_of_atPrime (R C : Type) [CommRing R] [IsNoetherianRing R]
    [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hf : algebraMap R C f ≠ 0)
    (h₁ : Algebra.FiniteType R (Localization.Away (algebraMap R C f)))
    (h₂ : Algebra.FiniteType (Localization.AtPrime 𝔭)
      (TensorProduct R (Localization.AtPrime 𝔭) C)) :
    ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by
  classical
  obtain ⟨s₁, hs₁⟩ := exists_pow_mul_mem_of_finiteType_away f h₁
  obtain ⟨s₂, hs₂⟩ := exists_smul_mem_of_finiteType_tensor 𝔭.primeCompl h₂
  let B := Algebra.adjoin R ((s₁ ∪ s₂ : Finset C) : Set C)
  have hB₁ : Algebra.adjoin R (s₁ : Set C) ≤ B := Algebra.adjoin_mono (by simp)
  have hB₂ : Algebra.adjoin R (s₂ : Set C) ≤ B := Algebra.adjoin_mono (by simp)
  have : IsNoetherianRing B := isNoetherianRing_of_fg ⟨s₁ ∪ s₂, rfl⟩
  obtain ⟨g, hg, hgB⟩ := exists_mul_mem_of_mul_mem B _ hf 𝔭.primeCompl fun c =>
    (hs₂ c).imp fun r hr => ⟨hr.1, hB₂ hr.2⟩
  refine ⟨g, hg, finiteType_away_of_pow_mul_mem (s₁ ∪ s₂) _ fun c => ?_⟩
  have key : ∀ (n : ℕ) (c : C), algebraMap R C f ^ n * c ∈ B → algebraMap R C g ^ n * c ∈ B := by
    intro n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      rw [pow_succ, mul_assoc] at hc
      have h := ih _ hc
      rw [mul_left_comm] at h
      rw [pow_succ', mul_assoc]
      exact hgB _ h
  obtain ⟨n, hn⟩ := hs₁ c
  exact ⟨n, key n c (hB₁ hn)⟩

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAwayMapSubalgebraBijective
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem exists_finset_awayMap_subalgebra_bijective :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B),
      (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) →
      ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C →
        ∀ b ∈ g, ∀ hb : b ∈ C,
          Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
  intro R B _ _ _ g hg
  classical
  have key : ∀ b ∈ g, ∃ t : Finset B, ∀ C : Subalgebra R B, (↑t : Set B) ⊆ ↑C → b ∈ C →
      ∀ x : B, ∃ m : ℕ, b ^ m * x ∈ C := by
    intro b hb
    obtain ⟨t, ht⟩ := (hg b hb).out
    refine ⟨t.image fun z => (IsLocalization.sec (Submonoid.powers b) z).1, fun C hC hbC x => ?_⟩
    have main : ∀ z : Localization.Away b, ∃ (m : ℕ) (c : B), c ∈ C ∧
        z * algebraMap B _ b ^ m = algebraMap B _ c := by
      intro z
      have hz : z ∈ Algebra.adjoin R (t : Set (Localization.Away b)) := ht ▸ Algebra.mem_top
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        obtain ⟨m, hm⟩ := (IsLocalization.sec (Submonoid.powers b) z).2.2
        refine ⟨m, (IsLocalization.sec (Submonoid.powers b) z).1, hC ?_, ?_⟩
        · simp only [Finset.coe_image]
          exact ⟨z, hz, rfl⟩
        · rw [← map_pow]
          have := IsLocalization.sec_spec (Submonoid.powers b) z
          rw [← hm] at this
          exact this
      | algebraMap r =>
        exact ⟨0, algebraMap R B r, C.algebraMap_mem r, by
          rw [pow_zero, mul_one, IsScalarTower.algebraMap_apply R B]⟩
      | add x y _ _ hx hy =>
        obtain ⟨m, c, hc, e⟩ := hx
        obtain ⟨n, d, hd, e'⟩ := hy
        refine ⟨m + n, c * b ^ n + d * b ^ m,
          add_mem (mul_mem hc (pow_mem hbC _)) (mul_mem hd (pow_mem hbC _)), ?_⟩
        rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← e, ← e']
        ring
      | mul x y _ _ hx hy =>
        obtain ⟨m, c, hc, e⟩ := hx
        obtain ⟨n, d, hd, e'⟩ := hy
        refine ⟨m + n, c * d, mul_mem hc hd, ?_⟩
        rw [map_mul, ← e, ← e']
        ring
    obtain ⟨m, c, hc, e⟩ := main (algebraMap B _ x)
    rw [← map_pow, ← map_mul] at e
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers b) _).1 e
    refine ⟨k + m, ?_⟩
    have : b ^ (k + m) * x = b ^ k * c := by
      have hk' : b ^ k * (x * b ^ m) = b ^ k * c := hk
      rw [← hk']; ring
    rw [this]
    exact mul_mem (pow_mem hbC _) hc
  choose! t ht using key
  refine ⟨g ∪ g.biUnion t, by simp, fun C hC b hb hbC => ⟨?_, ?_⟩⟩
  · refine (Localization.awayMap_injective_iff).2 fun a ha => ⟨0, ?_⟩
    have : a = 0 := Subtype.ext ha
    simp [this]
  · refine (Localization.awayMap_surjective_iff).2 fun x => ?_
    obtain ⟨m, hm⟩ := ht b hb C (fun y hy => hC (by
      simp only [Finset.coe_union, Finset.coe_biUnion, Set.mem_union, Set.mem_iUnion]
      exact Or.inr ⟨b, hb, hy⟩)) hbC x
    exact ⟨⟨_, hm⟩, m, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetLeftTransversalOfRelIndexNeZero
section
namespace GlobalTheory

theorem exists_finset_leftTransversal_of_relIndex_ne_zero : ∀ {G : Type} [Group G] (H K : Subgroup G),
    K ≤ H → K.relIndex H ≠ 0 → ∃ R : Finset G, (∀ r ∈ R, r ∈ H) ∧ ∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K := by
  intro G _ H K _ hrel
  have hfin : Finite (H ⧸ K.subgroupOf H) := by
    apply Nat.finite_of_card_ne_zero
    simpa [Subgroup.relIndex, Subgroup.index] using hrel
  let f : H ⧸ K.subgroupOf H → G := fun q => ((Quotient.out q : H) : G)
  have hR : (Set.range f).Finite := Set.finite_range f
  refine ⟨hR.toFinset, ?_, ?_⟩
  · intro r hr
    rw [Set.Finite.mem_toFinset] at hr
    obtain ⟨q, rfl⟩ := hr
    exact (Quotient.out q : H).2
  · intro k hk
    refine ⟨f (QuotientGroup.mk (⟨k, hk⟩ : H)), ⟨?_, ?_⟩, ?_⟩
    · rw [Set.Finite.mem_toFinset]; exact ⟨_, rfl⟩
    · have h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : H) : H ⧸ K.subgroupOf H)) :
          H ⧸ K.subgroupOf H) = QuotientGroup.mk ⟨k, hk⟩ := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      simpa [f] using h1
    · rintro r ⟨hr, hrk⟩
      rw [Set.Finite.mem_toFinset] at hr
      obtain ⟨q, rfl⟩ := hr
      have h2 : (QuotientGroup.mk (Quotient.out q) : H ⧸ K.subgroupOf H) = QuotientGroup.mk ⟨k, hk⟩ := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [f] using hrk
      rw [QuotientGroup.out_eq'] at h2
      simp [f, h2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLocalOfCharacter
section
open scoped TensorProduct
universe u

namespace GlobalTheory

theorem exists_idem_local_of_character :
    ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A]
      (φ : A →ₐ[k] k), ∃ e : A, IsIdempotentElem e ∧ φ e = 1 ∧
        ∀ a, φ a = 0 → IsNilpotent (e * a) := by
  intro k _ A _ _ _ φ
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  set m : Ideal A := RingHom.ker φ with hm
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := A) (M := A)
    ⟨fun n => OrderDual.toDual (m ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  have hst : ∀ j, n ≤ j → m ^ n = m ^ j := fun j hj => hn j hj
  set N := n + 1 with hN
  have hI : IsIdempotentElem (m ^ N) := by
    show m ^ N * m ^ N = m ^ N
    rw [← pow_add, ← hst (N + N) (by omega), hst N (by omega)]
  have hfg : (m ^ N).FG := IsNoetherian.noetherian _
  obtain ⟨f, hf, hIf⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).1 hI
  refine ⟨1 - f, hf.one_sub, ?_, ?_⟩
  · have hfm : f ∈ m := by
      have : f ∈ m ^ N := by rw [hIf]; exact Ideal.subset_span rfl
      exact Ideal.pow_le_self (by omega) this
    have : φ f = 0 := hfm
    simp [this]
  · intro a ha
    have ham : a ∈ m := ha
    have haN : a ^ N ∈ m ^ N := Ideal.pow_mem_pow ham N
    rw [hIf, Ideal.mem_span_singleton'] at haN
    obtain ⟨y, hy⟩ := haN
    refine ⟨N, ?_⟩
    rw [mul_pow, hf.one_sub.pow_succ_eq n, ← hy]
    have : (1 - f) * f = 0 := by rw [sub_mul, one_mul, hf.eq, sub_self]
    calc (1 - f) * (y * f) = y * ((1 - f) * f) := by ring
      _ = 0 := by rw [this, mul_zero]

end GlobalTheory
end

