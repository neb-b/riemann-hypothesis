module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDomainOfIsIntegrallyClosedOfIsReduced
section
open IsLocalRing

namespace GlobalTheory

theorem eq_zero_of_mem_minimalPrimes {R : Type} [CommRing R] [IsReduced R] {y : R}
    (hy : ∀ P ∈ minimalPrimes R, y ∈ P) : y = 0 := by
  have : y ∈ nilradical R := by
    rw [nilradical_eq_sInf, Submodule.mem_sInf]
    intro J hJ
    haveI : Ideal.IsPrime J := hJ
    obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := J) bot_le
    exact hpJ (hy p hp)
  rw [nilradical_eq_zero] at this
  simpa using this

theorem isDomain_of_isIntegrallyClosed_of_isReduced :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R],
      IsIntegrallyClosed R → IsDomain R := by
  intro R _ _ _ _ hic
  classical
  suffices hbot : (⊥ : Ideal R).IsPrime by
    haveI : NoZeroDivisors R := ⟨fun {x y} h => by
      have : x * y ∈ (⊥ : Ideal R) := by simp [h]
      simpa using hbot.mem_or_mem this⟩
    exact NoZeroDivisors.to_isDomain R
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  obtain ⟨P, hP⟩ : ∃ P, P ∈ minimalPrimes R := by
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R))
      (J := IsLocalRing.maximalIdeal R) bot_le
    exact ⟨p, hp⟩
  have hPprime : P.IsPrime := hP.1.1
  have minle : ∀ {A B : Ideal R}, A ∈ minimalPrimes R → B ∈ minimalPrimes R → A ≤ B → A = B :=
    fun {A B} hA hB hAB => le_antisymm hAB (hB.2 hA.1 hAB)
  set T : Finset (Ideal R) := hfin.toFinset with hT
  have memT : ∀ Q, Q ∈ T ↔ Q ∈ minimalPrimes R := fun Q => by simp [T]
  set Q : Ideal R := (T.erase P).inf id with hQ
  have hQle : ∀ P' ∈ T.erase P, Q ≤ P' := fun P' h => Finset.inf_le (f := id) h
  by_cases hone : T.erase P = ∅
  ·
    have hPbot : P = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y = 0 := eq_zero_of_mem_minimalPrimes (fun P' hP' => by
        by_cases h : P' = P
        · exact h ▸ hy
        · have : P' ∈ T.erase P := Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩
          simp [hone] at this)
      simp [this]
    exact hPbot ▸ hPprime
  exfalso
  obtain ⟨P₂, hP₂⟩ := Finset.nonempty_iff_ne_empty.2 hone

  have hnot : ¬ ((P ⊔ Q : Ideal R) : Set R) ⊆ ⋃ i ∈ (↑T : Set (Ideal R)), (i : Set R) := by
    intro hsub
    obtain ⟨P', hP'T, hle⟩ := (Ideal.subset_union_prime (f := id) P P
      (fun i hi _ _ => ((memT i).1 hi).1.1)).1 hsub
    have hle' : P ⊔ Q ≤ P' := hle
    have h1 : P = P' := minle hP ((memT P').1 hP'T) (le_sup_left.trans hle')
    have hQP : Q ≤ P := by
      have h2 : Q ≤ P' := le_sup_right.trans hle'
      rw [← h1] at h2
      exact h2
    obtain ⟨P'', hP''e, hP''le⟩ := (Ideal.IsPrime.inf_le' (s := T.erase P) (f := id) hPprime).1 hQP
    have : P'' = P := minle ((memT P'').1 (Finset.mem_of_mem_erase hP''e)) hP hP''le
    exact Finset.ne_of_mem_erase hP''e this
  obtain ⟨s, hsPQ, hsout⟩ := Set.not_subset.1 hnot
  have hsnot : ∀ P' ∈ minimalPrimes R, s ∉ P' := fun P' hP' hs =>
    hsout (Set.mem_biUnion (x := P') (by simpa [memT] using hP') hs)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hsPQ
  have hsnzd : ∀ y : R, y * s = 0 → y = 0 := fun y hy =>
    eq_zero_of_mem_minimalPrimes (fun P' hP' => by
      have : y * s ∈ P' := by simp [hy]
      exact (hP'.1.1.mem_or_mem this).resolve_right (hsnot P' hP'))
  have hab0 : a * b = 0 := eq_zero_of_mem_minimalPrimes (fun P' hP' => by
    by_cases h : P' = P
    · exact h ▸ P.mul_mem_right b ha
    · exact P'.mul_mem_left a (hQle P' (Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩) hb))
  have hs : s ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_right.2 hsnzd
  let K := FractionRing R
  set e : K := IsLocalization.mk' K a ⟨s, hs⟩ with he_def
  have hspec : e * algebraMap R K s = algebraMap R K a := IsLocalization.mk'_spec K a ⟨s, hs⟩
  have ht : IsUnit (algebraMap R K s) := IsLocalization.map_units K (⟨s, hs⟩ : nonZeroDivisors R)
  have has : a * s = a * a := by rw [← hab, mul_add, hab0, add_zero]
  have hee : e * e = e := by
    refine (ht.mul ht).mul_left_inj.1 ?_
    calc e * e * (algebraMap R K s * algebraMap R K s)
        = (e * algebraMap R K s) * (e * algebraMap R K s) := by ring
      _ = algebraMap R K (a * a) := by rw [hspec, map_mul]
      _ = algebraMap R K (a * s) := by rw [has]
      _ = (e * algebraMap R K s) * algebraMap R K s := by rw [hspec, map_mul]
      _ = e * (algebraMap R K s * algebraMap R K s) := by ring
  have hint : IsIntegral R e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
    · simp [Polynomial.eval₂_sub, sq, hee]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hinj := IsFractionRing.injective R K
  have hrr : r * r = r := hinj (by rw [map_mul, hr, hee])
  have hrs : r * s = a := hinj (by rw [map_mul, hr, hspec])
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with hu | hu
  · have hr1 : r = 1 := hu.mul_left_cancel (by rw [hrr, mul_one])
    rw [hr1, one_mul] at hrs

    exact hsnot P hP (hrs ▸ ha)
  · have hr0 : r = 0 := by
      have : (1 - r) * r = 0 := by rw [sub_mul, one_mul, hrr, sub_self]
      exact (hu.mul_right_eq_zero).1 this
    rw [hr0, zero_mul] at hrs

    have hsb : s = b := by rw [← hab, ← hrs, zero_add]
    exact hsnot P₂ ((memT P₂).1 (Finset.mem_of_mem_erase hP₂)) (hsb ▸ hQle P₂ hP₂ hb)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPreconnectedPolydiscFirstCoordsNeZero
section
open Set

namespace GlobalTheory

theorem punctured_unit_disc_eq_exp_image :
    Metric.ball (0:ℂ) 1 \ {0} = Complex.exp '' {z : ℂ | z.re < 0} := by
  ext w
  constructor
  · rintro ⟨hb, h0⟩
    have h0' : w ≠ 0 := h0
    refine ⟨Complex.log w, ?_, Complex.exp_log h0'⟩
    rw [Set.mem_setOf_eq, Complex.log_re]
    rw [Metric.mem_ball, dist_zero_right] at hb
    exact Real.log_neg (norm_pos_iff.mpr h0') hb
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hz
    · exact Complex.exp_ne_zero z

theorem isPreconnected_punctured_unit_disc :
    IsPreconnected (Metric.ball (0:ℂ) 1 \ {0}) := by
  rw [punctured_unit_disc_eq_exp_image]
  exact (convex_halfSpace_re_lt 0).isPreconnected.image _ Complex.continuous_exp.continuousOn

theorem isPreconnected_polydisc_first_coords_ne_zero :
    ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  intro n a ha
  have hS : {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}
      = Set.pi univ (fun k : Fin n => if (k:ℕ) < a then Metric.ball (0:ℂ) 1 \ {0} else Metric.ball (0:ℂ) 1) := by
    ext z
    rw [ball_pi _ one_pos]
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Pi.zero_apply]
    constructor
    · rintro ⟨hb, hne⟩ k
      split_ifs with hk
      · exact ⟨hb k, fun h => hne ⟨k, hk⟩ (by simpa using h)⟩
      · exact hb k
    · intro h
      refine ⟨fun k => ?_, fun i => ?_⟩
      · have := h k
        split_ifs at this
        · exact this.1
        · exact this
      · have := h (Fin.castLE ha i)
        rw [if_pos (by simp)] at this
        exact this.2
  rw [hS]
  apply isPreconnected_univ_pi
  intro k
  split_ifs
  · exact isPreconnected_punctured_unit_disc
  · exact (convex_ball (0:ℂ) 1).isPreconnected

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsReducedOfNonZeroDivisorMemJacobsonOfAssociated
section
open IsLocalRing

namespace GlobalTheory

theorem mem_span_singleton_of_isNilpotent_of_associatedPrimes {R : Type} [CommRing R]
    [IsNoetherianRing R] (x : R)
    (hP : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      IsDomain (Localization.AtPrime P))
    {n : R} (hn : IsNilpotent n) : n ∈ Ideal.span {x} := by
  by_contra hnx
  have h0 : (Ideal.Quotient.mk (Ideal.span {x}) n) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hPa, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (Ideal.span {x}) n) h0
  haveI : P.IsPrime := hPa.isPrime
  haveI := hP P hPa
  have hz : algebraMap R (Localization.AtPrime P) n = 0 :=
    (hn.map (algebraMap R (Localization.AtPrime P))).eq_zero
  obtain ⟨⟨s, hs⟩, hsn⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ n).1 hz
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change Ideal.Quotient.mk (Ideal.span {x}) s * Ideal.Quotient.mk (Ideal.span {x}) n = 0
  rw [← map_mul, hsn, map_zero]

theorem isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R →
      x ∈ Ideal.jacobson (⊥ : Ideal R) →
      (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
        IsDomain (Localization.AtPrime P)) → IsReduced R := by
  intro R _ _ x hx hj hP
  refine ⟨fun n hn => ?_⟩
  have key : ∀ k : ℕ, ∀ m : R, IsNilpotent m → m ∈ Ideal.span {x} ^ k := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hm
      obtain ⟨m', rfl⟩ := Ideal.mem_span_singleton'.1
        (mem_span_singleton_of_isNilpotent_of_associatedPrimes x hP hm)
      have hm' : IsNilpotent m' := by
        obtain ⟨e, he⟩ := hm
        refine ⟨e, ?_⟩
        rw [mul_pow] at he
        exact (mem_nonZeroDivisors_iff_right.1 (pow_mem hx e)) _ he
      rw [pow_succ', mul_comm m' x]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (ih m' hm')
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := R) (Ideal.span {x})
    ((Ideal.span_singleton_le_iff_mem _).2 (by simpa only [Ideal.jacobson_bot] using hj))
  have : n ∈ (⨅ i : ℕ, (Ideal.span {x}) ^ i • ⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro i
    simpa [smul_eq_mul, Ideal.mul_top] using key i n hn
  rw [hK] at this
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitMapOfMemNonZeroDivisorsTensor
section
open TensorProduct

namespace GlobalTheory

theorem exists_base_denominator_of_finite {T C K : Type} [CommRing T] [IsDomain T] [CommRing C]
    [IsDomain C] [Field K] [Algebra T C] [Algebra C K] [IsFractionRing C K] [Algebra T K]
    [IsScalarTower T C K] [Module.Finite T C] (k : K) :
    ∃ t : T, t ≠ 0 ∧ ∃ c : C, algebraMap T K t * k = algebraMap C K c := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hint : IsIntegral T b := Algebra.IsIntegral.isIntegral b
  have h := Ideal.comap_ne_bot_of_integral_mem (R := T) (I := Ideal.span {b}) hb0
    (Ideal.mem_span_singleton_self b) hint
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at ht
  obtain ⟨d, hd⟩ := ht
  refine ⟨t, ht0, d * a, ?_⟩
  have hbK : algebraMap C K b ≠ 0 := by
    simpa using hb0
  rw [IsScalarTower.algebraMap_apply T C K, hd, map_mul, map_mul]
  field_simp

theorem finite_fractionRing_of_finite (T C F K : Type) [CommRing T] [IsDomain T] [CommRing C]
    [IsDomain C] [Field F] [Field K] [Algebra T C] [Algebra T F] [IsFractionRing T F]
    [Algebra C K] [IsFractionRing C K] [Algebra T K] [Algebra F K]
    [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C] : Module.Finite F K := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := T) (M := C)
  refine ⟨⟨s.image (algebraMap C K), ?_⟩⟩
  have key : ∀ c : C, algebraMap C K c ∈
      Submodule.span F ((s.image (algebraMap C K) : Finset K) : Set K) := by
    intro c
    have hc : c ∈ Submodule.span T (s : Set C) := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hx)))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro k _
  obtain ⟨t, ht, c, hc⟩ := exists_base_denominator_of_finite (T := T) (C := C) k
  have htF : algebraMap T F t ≠ 0 := by simpa using ht
  have : k = (algebraMap T F t)⁻¹ • algebraMap C K c := by
    rw [← hc, IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def, inv_smul_smul₀ htF]
  rw [this]
  exact Submodule.smul_mem _ _ (key c)

theorem isUnit_map_of_mem_nonZeroDivisors_tensor (T U C F K L : Type) [CommRing T] [IsDomain T]
    [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L]
    [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K]
    [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K]
    [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L]
    [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C]
    (φ : U ⊗[T] C →+* L ⊗[F] K) (hinj : Function.Injective φ)
    (hφ : ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) :
    ∀ s ∈ nonZeroDivisors (U ⊗[T] C), IsUnit (φ s) := by
  have hTU : ∀ t : T, t ≠ 0 → algebraMap T U t ≠ 0 := by
    intro t ht h0
    have h1 : algebraMap T L t = 0 := by
      rw [IsScalarTower.algebraMap_apply T U L, h0, map_zero]
    rw [IsScalarTower.algebraMap_apply T F L] at h1
    apply ht
    simpa using h1
  have den : ∀ ω : L ⊗[F] K, ∃ u : U, u ≠ 0 ∧ ∃ s', φ (u ⊗ₜ 1) * ω = φ s' := by
    intro ω
    induction ω using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul l k =>
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := U) l
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have hbL : algebraMap U L b ≠ 0 := by simpa using hb0
      obtain ⟨t, ht, c, hc⟩ := exists_base_denominator_of_finite (T := T) (C := C) k
      refine ⟨algebraMap T U t * b, mul_ne_zero (hTU t ht) hb0, a ⊗ₜ c, ?_⟩
      rw [hφ, hφ, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hc,
        IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def (algebraMap T F t) k,
        ← TensorProduct.smul_tmul,
        Algebra.smul_def, ← IsScalarTower.algebraMap_apply T F L, map_mul,
        ← IsScalarTower.algebraMap_apply T U L]
      congr 1
      field_simp
    | add x y hx hy =>
      obtain ⟨u, hu, s₁, h₁⟩ := hx
      obtain ⟨v, hv, s₂, h₂⟩ := hy
      refine ⟨u * v, mul_ne_zero hu hv, (v ⊗ₜ 1) * s₁ + (u ⊗ₜ 1) * s₂, ?_⟩
      have : ((u * v) ⊗ₜ[T] (1 : C)) = (u ⊗ₜ 1) * (v ⊗ₜ 1) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [this, map_add (f := _), map_mul, map_mul, map_mul, ← h₁, ← h₂]
      ring
  have : Module.Finite F K := finite_fractionRing_of_finite T C F K
  have : IsArtinianRing (L ⊗[F] K) := IsArtinianRing.of_finite L (L ⊗[F] K)
  intro s hs
  apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_right]
  intro ω hω
  obtain ⟨u, hu, s', h⟩ := den ω
  have h0 : s' * s = 0 := by
    apply hinj
    rw [map_mul, ← h, mul_assoc, hω, mul_zero, map_zero]
  have hs' : s' = 0 := (mem_nonZeroDivisors_iff_right.1 hs) s' h0
  have huL : algebraMap U L u ≠ 0 := by simpa using hu
  have hunit : IsUnit (φ (u ⊗ₜ 1)) := by
    rw [hφ, map_one]
    exact (IsUnit.mk0 _ huL).map (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := L) (B := K))
  rw [hs', map_zero] at h
  exact (hunit.mul_right_eq_zero).1 h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointEigenMemISup
section
namespace GlobalTheory.JointEigenSupremum

theorem joint_eigen_mem_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M]
    (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (E : κ → Submodule ℂ M)
    (hE : ∀ (k : κ), ∀ y ∈ E k, ∀ (i : ι), (op i : M → M) y = χ k i • y)
    (ψ : ι → ℂ) (x : M) (hx0 : x ≠ (0 : M)) (hx : ∀ i, (op i : M → M) x = ψ i • x)
    (hmem : x ∈ ⨆ k, E k) : ∃ k, χ k = ψ := by
  classical
  by_contra hne
  push_neg at hne
  have hstab : ∀ (s : Finset κ) (i : ι), ∀ z ∈ ⨆ k ∈ s, E k, (op i : M → M) z ∈ ⨆ k ∈ s, E k := by
    intro s i z hz
    have hle : (⨆ k ∈ s, E k) ≤ (⨆ k ∈ s, E k).comap (op i) := by
      refine iSup₂_le fun k hk y hy => ?_
      rw [Submodule.mem_comap, hE k y hy i]
      exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun k (_ : k ∈ s) => E k) k hk) hy)
    exact hle hz
  have key : ∀ s : Finset κ, ∀ x : M, (∀ i, (op i : M → M) x = ψ i • x) →
      x ∈ ⨆ k ∈ s, E k → x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ h; simpa using h
    | insert k0 s hk0 ih =>
      intro x hx h
      rw [Finset.iSup_insert, Submodule.mem_sup] at h
      obtain ⟨y, hy, z, hz, rfl⟩ := h
      obtain ⟨i, hi⟩ : ∃ i, χ k0 i ≠ ψ i := by
        by_contra h'
        push_neg at h'
        exact hne k0 (funext h')
      have hw : (op i : M → M) z - χ k0 i • z ∈ ⨆ k ∈ s, E k :=
        Submodule.sub_mem _ (hstab s i z hz) (Submodule.smul_mem _ _ hz)
      have h1 := hx i
      rw [map_add (f := _), hE k0 y hy i, smul_add] at h1
      have h2 : (op i : M → M) z = ψ i • y + ψ i • z - χ k0 i • y := by
        rw [← h1]; abel
      have hw' : (op i : M → M) z - χ k0 i • z = (ψ i - χ k0 i) • (y + z) := by
        rw [h2]; module
      rw [hw'] at hw
      have heig : ∀ j, (op j : M → M) ((ψ i - χ k0 i) • (y + z)) = ψ j • ((ψ i - χ k0 i) • (y + z)) := by
        intro j
        rw [map_smul, hx j, smul_comm]
      have h0 := ih _ heig hw
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hi
      · exact h
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  exact hx0 (key s x hx hs)

end GlobalTheory.JointEigenSupremum

theorem GlobalTheory.JointEigenSupremum.target : ∀ {ι κ M : Type} [inst : AddCommGroup M] [inst_1 : Module ℂ M] (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (E : κ → Submodule ℂ M), (∀ (k : κ), ∀ y ∈ E k, ∀ (i : ι), (op i : M → M) y = χ k i • y) → ∀ (ψ : ι → ℂ) (x : M), x ≠ (0 : M) → (∀ (i : ι), (op i : M → M) x = ψ i • x) → x ∈ ⨆ (k : κ), E k → ∃ (k : κ), χ k = ψ :=
  fun op χ E hE ψ x hx0 hx hmem => GlobalTheory.JointEigenSupremum.joint_eigen_mem_iSup op χ E hE ψ x hx0 hx hmem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KsFormBaseChange
section
namespace GlobalTheory

theorem _root_.GlobalTheory.ksForm_baseChange :
    ∀ {LL LL' Ks : Type} [Field LL] [Field LL'] [Field Ks] [Algebra Ks LL] [Algebra Ks LL']
      (ι : LL →+* LL'), (∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) →
      ∀ {n : ℕ} (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n → LL')),
      (∀ x, x ∈ WK ↔ (fun k => ι (x k)) ∈ WK') →
      (∀ x' ∈ WK', ∃ x ∈ WK, x' = fun k => ι (x k)) →
      (∃ (m : ℕ) (b : Fin m → (Fin n → LL)), (∀ i, b i ∈ WK) ∧ LinearIndependent Ks b ∧
        Submodule.span Ks (Set.range b) = WK ∧ LinearIndependent LL b ∧
        Submodule.span LL (Set.range b) = ⊤) →
      ∃ (m : ℕ) (b : Fin m → (Fin n → LL')), (∀ i, b i ∈ WK') ∧ LinearIndependent Ks b ∧
        Submodule.span Ks (Set.range b) = WK' ∧ LinearIndependent LL' b ∧
        Submodule.span LL' (Set.range b) = ⊤ := by
  intro LL LL' Ks _ _ _ _ _ ι hι n WK WK' hmem hsurj ⟨m, b, hbW, hKs, hspanK, hLL, hspanLL⟩
  let Φ : (Fin n → LL) →ₗ[Ks] (Fin n → LL') :=
    { toFun := fun x k => ι (x k)
      map_add' := fun x y => by ext k; simp
      map_smul' := fun c x => by ext k; simp [Algebra.smul_def, hι] }
  have hker : LinearMap.ker Φ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => funext fun k => ?_
    have hk : ι (x k) = 0 := congrFun hx k
    simpa using hk
  have hmn : m = n := by
    have h := Module.finrank_eq_card_basis (Module.Basis.mk hLL (by rw [hspanLL]))
    simp at h
    omega
  subst hmn
  have hLL' : LinearIndependent LL' (Φ ∘ b) := by
    have hu : IsUnit (Matrix.of b) := Matrix.linearIndependent_rows_iff_isUnit.1 hLL
    exact Matrix.linearIndependent_rows_iff_isUnit.2 (hu.map ι.mapMatrix)
  refine ⟨m, Φ ∘ b, fun i => (hmem _).1 (hbW i), hKs.map' Φ hker, ?_, hLL', ?_⟩
  · rw [Set.range_comp, Submodule.span_image, hspanK]
    ext x'
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).1 hx
    · intro hx'
      obtain ⟨x, hx, rfl⟩ := hsurj x' hx'
      exact ⟨x, hx, rfl⟩
  · exact hLL'.span_eq_top_of_card_eq_finrank' (by simp)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubOneLe
section
universe u_1

namespace GlobalTheory.NormPowSubOne

theorem norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] {ζ : K}
    (hζ : ‖ζ‖ = (1 : ℝ)) (a : ℕ) : ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ := by
  induction a with
  | zero => simp
  | succ n ih =>
    have h : ζ ^ (n + 1) - 1 = ζ * (ζ ^ n - 1) + (ζ - 1) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hζ, one_mul]
    exact ih

theorem main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] {ζ : K},
    ‖ζ‖ = (1 : ℝ) → ∀ (a : ℕ), ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ :=
  fun hζ a => norm_pow_sub_one_le hζ a

end GlobalTheory.NormPowSubOne
end

