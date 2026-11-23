module

public import Mathlib
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RingKrullDimQuotientOfMemAssociatedPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CorePowMem
section
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.core_pow_mem {R : Type} [CommRing R] (b c : Ideal R) (x : R)
    (hx : x ∈ (b ⊔ c).radical) (M : ℕ) : ∃ K, x ^ K ∈ b ^ M ⊔ c ^ M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨0, by simp⟩
  · have hx' : x ∈ (b ^ M ⊔ c ^ M).radical := by
      rw [Ideal.radical_sup, Ideal.radical_pow _ hM.ne', Ideal.radical_pow _ hM.ne',
        ← Ideal.radical_sup]
      exact hx
    exact hx'

private theorem UpperTheory.V.AlgebraTools.Conn.core_krull {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (P : Ideal R) (hP : P.IsPrime) (y r : R) (hy : y ∉ P)
    (h : ∀ n : ℕ, ∃ K : ℕ, y ^ K * r ∈ P ^ n) : r = 0 := by
  haveI := hP
  have hmem : ∀ n : ℕ, algebraMap R (Localization.AtPrime P) r ∈
      (maximalIdeal (Localization.AtPrime P)) ^ n := by
    intro n
    obtain ⟨K, hK⟩ := h n
    have h1 : algebraMap R (Localization.AtPrime P) (y ^ K * r) ∈
        (maximalIdeal (Localization.AtPrime P)) ^ n := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hK
    have hu : IsUnit (algebraMap R (Localization.AtPrime P) (y ^ K)) :=
      IsLocalization.map_units (Localization.AtPrime P)
        (⟨y ^ K, P.primeCompl.pow_mem hy K⟩ : P.primeCompl)
    rw [map_mul] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1
  have h0 : algebraMap R (Localization.AtPrime P) r = 0 := by
    have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (Localization.AtPrime P))
      (maximalIdeal.isMaximal _).ne_top
    rw [← Ideal.mem_bot, ← hb, Ideal.mem_iInf]
    exact hmem
  exact IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
    (h0.trans (map_zero _).symm)

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.AlgebraTools.Conn.core :
    ∀ {A R : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
      [FaithfulSMul A R] (I : Ideal A) [IsAdicComplete I A] (J : ℕ → Ideal A) (u v : A) (b c P Q : Ideal R) (y z : A),
      Antitone J → (∀ m, J m ≤ I ^ m) → (∀ m K, Reg2 (J m) (u ^ K) (v ^ K)) → (∀ m, ∃ N, I ^ N ≤ J m) →
      b * c ≤ (I.map (algebraMap A R)).radical →
      algebraMap A R u ∈ (b ⊔ c).radical → algebraMap A R v ∈ (b ⊔ c).radical →
      P.IsPrime → Q.IsPrime → b ≤ P → c ≤ Q → I.map (algebraMap A R) ≤ P → I.map (algebraMap A R) ≤ Q →
      algebraMap A R y ∈ (b ⊔ c).radical → algebraMap A R z ∈ (b ⊔ c).radical →
      algebraMap A R y ∉ P → algebraMap A R z ∉ Q → False := by
  intro A R _ _ _ _ _ _ _ _ I _ J u v b c P Q y z hJ hJI hreg hIJ hbc hu hv hP hQ hbP hcQ hIP hIQ
    hy hz hyP hzQ
  haveI : IsNoetherianRing R := IsNoetherianRing.of_finite A R
  obtain ⟨a, ha⟩ := UpperTheory.V.AlgebraTools.Conn.limit (R := R) I J u v b c hJ hJI hreg hIJ hbc
    (IsNoetherian.noetherian b) (IsNoetherian.noetherian c) hu hv
  obtain ⟨d, r, hd, hr⟩ := UpperTheory.V.AlgebraTools.Conn.bidual (M := R) a
  obtain ⟨k, hk⟩ := UpperTheory.V.AlgebraTools.Conn.formsAR (M := R) I
  have key : ∀ w : A, algebraMap A R w ∈ (b ⊔ c).radical → ∀ n : ℕ, ∃ N, n ≤ N ∧ ∃ K : ℕ,
      ∃ β ∈ b ^ N, ∃ γ ∈ c ^ N, β + γ = (algebraMap A R w) ^ K ∧
      algebraMap A R d * β - (algebraMap A R w) ^ K * r ∈ (I.map (algebraMap A R)) ^ n := by
    intro w hw n
    obtain ⟨N, hnN, hN⟩ := ha (n + k)
    obtain ⟨K, hK⟩ := core_pow_mem b c _ hw N
    obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hK
    refine ⟨N, le_trans (Nat.le_add_right n k) hnN, K, β, hβ, γ, hγ, hβγ, ?_⟩
    have hforms : ∀ l : Module.Dual A R, l (d • β - w ^ K • r) ∈ I ^ (n + k) := by
      intro l
      have h1 := hN (w ^ K) β γ hβ hγ (by rw [map_pow, hβγ]) l
      have h2 : l (d • β - w ^ K • r) = d * (l β - w ^ K * a l) := by
        rw [map_sub, map_smul, map_smul, hr, smul_eq_mul, smul_eq_mul]
        ring
      rw [h2]
      exact Ideal.mul_mem_left _ _ h1
    have h4 : d • β - w ^ K • r ∈ Ideal.map (algebraMap A R) (I ^ n) := by
      have h3 := hk n _ hforms
      rw [Ideal.smul_top_eq_map] at h3
      exact h3
    rw [← Ideal.map_pow]
    simpa [Algebra.smul_def] using h4
  have hr0 : r = 0 := by
    refine core_krull P hP (algebraMap A R y) r hyP fun n => ?_
    obtain ⟨N, hnN, K, β, hβ, γ, hγ, -, hdiff⟩ := key y hy n
    refine ⟨K, ?_⟩
    have hβP : β ∈ P ^ n := Ideal.pow_right_mono hbP n (Ideal.pow_le_pow_right hnN hβ)
    have hd' : algebraMap A R d * β - (algebraMap A R y) ^ K * r ∈ P ^ n :=
      Ideal.pow_right_mono hIP n hdiff
    have he : (algebraMap A R y) ^ K * r =
        algebraMap A R d * β - (algebraMap A R d * β - (algebraMap A R y) ^ K * r) := by ring
    rw [he]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hβP) hd'
  have hdr : algebraMap A R d - r = 0 := by
    refine core_krull Q hQ (algebraMap A R z) _ hzQ fun n => ?_
    obtain ⟨N, hnN, K, β, hβ, γ, hγ, hβγ, hdiff⟩ := key z hz n
    refine ⟨K, ?_⟩
    have hγQ : γ ∈ Q ^ n := Ideal.pow_right_mono hcQ n (Ideal.pow_le_pow_right hnN hγ)
    have hd' : algebraMap A R d * β - (algebraMap A R z) ^ K * r ∈ Q ^ n :=
      Ideal.pow_right_mono hIQ n hdiff
    have he : (algebraMap A R z) ^ K * (algebraMap A R d - r) =
        (algebraMap A R d * β - (algebraMap A R z) ^ K * r) + algebraMap A R d * γ := by
      rw [← hβγ]
      ring
    rw [he]
    exact Ideal.add_mem _ hd' (Ideal.mul_mem_left _ _ hγQ)
  rw [hr0, sub_zero] at hdr
  exact hd (FaithfulSMul.algebraMap_injective A R (hdr.trans (map_zero _).symm))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ExistsSystemOfParameters
section
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.exists_system_of_parameters {A : Type} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (J : Ideal A) (hle : J ≤ maximalIdeal A) :
    ∃ ys : List A, (∀ y ∈ ys, y ∈ maximalIdeal A) ∧
      (ys.length : WithBot ℕ∞) = ringKrullDim (A ⧸ J) ∧
      ∀ P : Ideal A, P.IsPrime → J ≤ P → (∀ y ∈ ys, y ∈ P) → P = maximalIdeal A := by
  have hne : J ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hle))
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (A ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set π := Ideal.Quotient.mk J with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsLocalHom π := IsLocalHom.of_surjective π hsurj
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (A ⧸ J))
  obtain ⟨g, hg⟩ := hsurj.hasRightInverse
  refine ⟨s.toList.map g, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have h1 : π (g z) ∈ maximalIdeal (A ⧸ J) := by
      rw [hg]
      exact hs.1.2 (Ideal.subset_span (Finset.mem_toList.1 hz))
    rw [mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun h => h1 (h.map π)
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hcard]
    simp
  · intro P hP hJP hy
    have hker : RingHom.ker π ≤ P := by rw [hπ, Ideal.mk_ker]; exact hJP
    have hP' : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
    have hs' : Ideal.span (s : Set (A ⧸ J)) ≤ P.map π := by
      rw [Ideal.span_le]
      intro z hz
      rw [← hg z]
      exact Ideal.mem_map_of_mem π (hy _ (List.mem_map.2 ⟨z, Finset.mem_toList.2 hz, rfl⟩))
    have hm : maximalIdeal (A ⧸ J) ≤ P.map π :=
      hs.2 ⟨hP', hs'⟩ (le_maximalIdeal hP'.ne_top)
    refine le_antisymm (le_maximalIdeal hP.ne_top) fun a ha => ?_
    have h1 : π a ∈ P.map π := hm (map_nonunit π a ha)
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective π hsurj, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.2 hker] at h1
    exact h1

private theorem UpperTheory.V.AlgebraTools.Conn.weakly_regular_mem_of_mul {A : Type} [CommRing A] (l w : List A) (a : A)
    (h : RingTheory.Sequence.IsWeaklyRegular A (l ++ a :: w)) (x : A)
    (hx : a * x ∈ Ideal.ofList l) : x ∈ Ideal.ofList l := by
  have h1 := h.regular_mod_prev l.length (by simp)
  simp only [List.getElem_append_right, le_refl, Nat.sub_self,
    List.getElem_cons_zero] at h1
  rw [List.take_left' rfl] at h1
  have e : (Ideal.ofList l • (⊤ : Submodule A A)) = Ideal.ofList l := by
    rw [smul_eq_mul, Ideal.mul_top]
  have h2 : (Submodule.Quotient.mk x : A ⧸ (Ideal.ofList l • (⊤ : Submodule A A))) = 0 := by
    apply h1
    show a • _ = a • _
    rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, e]
    exact hx
  rwa [Submodule.Quotient.mk_eq_zero, e] at h2

theorem UpperTheory.V.AlgebraTools.Conn.reg2 :
    ∀ {A : Type} [CommRing A] [IsLocalRing A], ReciprocityTheory.CA.IsCM A → ∀ xs : List A, (∀ x ∈ xs, x ∈ maximalIdeal A) →
      ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A → 2 ≤ ringKrullDim (A ⧸ Ideal.ofList xs) →
      ∃ u ∈ maximalIdeal A, ∃ v ∈ maximalIdeal A, ∀ m K : ℕ,
        Reg2 (Ideal.ofList (xs.map (· ^ (m + 1)))) (u ^ K) (v ^ K) := by
  intro A _ _ hA xs hxs hdim h2
  haveI := hA.1
  obtain ⟨ys, hys, hlen, hP⟩ := exists_system_of_parameters (Ideal.ofList xs) (Ideal.span_le.2 hxs)
  rw [← hlen] at hdim h2
  have h2' : 2 ≤ ys.length := by exact_mod_cast h2
  obtain ⟨u, v, w, rfl⟩ : ∃ u v w, ys = u :: v :: w := by
    match ys, h2' with
    | u :: v :: w, _ => exact ⟨u, v, w, rfl⟩
  have hu := hys u (by simp)
  have hv := hys v (by simp)
  refine ⟨u, hu, v, hv, fun m K => ?_⟩
  rcases K with _ | K
  · simpa using isWeaklyRegularPairMod_one_left _ _
  set l := xs.map (· ^ (m + 1)) with hl
  have hreg : RingTheory.Sequence.IsRegular A (l ++ u ^ (K + 1) :: v ^ (K + 1) :: w) := by
    refine hA.isRegular_of_isArtinianRing_quotient _ ?_ ?_ ?_
    · intro r hr
      simp only [hl, List.mem_append, List.mem_map, List.mem_cons] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl | rfl | hr
      · exact Ideal.pow_mem_of_mem _ (hxs x hx) _ (Nat.succ_pos _)
      · exact Ideal.pow_mem_of_mem _ hu _ (Nat.succ_pos _)
      · exact Ideal.pow_mem_of_mem _ hv _ (Nat.succ_pos _)
      · exact hys r (by simp [hr])
    · rw [← hdim]
      simp only [hl, List.length_append, List.length_map, List.length_cons]
      push_cast
      rw [add_comm]
    · set I := Ideal.ofList (l ++ u ^ (K + 1) :: v ^ (K + 1) :: w) with hI
      have : Ring.KrullDimLE 0 (A ⧸ I) := by
        rw [Ring.krullDimLE_zero_iff]
        intro Q hQ
        have hp : (Q.comap (Ideal.Quotient.mk I)).IsPrime := Ideal.comap_isPrime _ _
        have hmem : ∀ r ∈ l ++ u ^ (K + 1) :: v ^ (K + 1) :: w,
            r ∈ Q.comap (Ideal.Quotient.mk I) := by
          intro r hr
          have : r ∈ I := Ideal.subset_span hr
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 this]
          exact Q.zero_mem
        have := hP _ hp (Ideal.span_le.2 fun x hx => hp.mem_of_pow_mem (m + 1)
          (hmem _ (List.mem_append_left _ (List.mem_map.2 ⟨x, hx, rfl⟩)))) (by
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | rfl | hy
            · exact hp.mem_of_pow_mem (K + 1) (hmem _ (by simp))
            · exact hp.mem_of_pow_mem (K + 1) (hmem _ (by simp))
            · exact hmem _ (by simp [hy]))
        have hmax : (Q.comap (Ideal.Quotient.mk I)).IsMaximal := this ▸ maximalIdeal.isMaximal A
        rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q]
        refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
          hmax).resolve_left ?_
        rw [Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q]
        exact hQ.ne_top
      exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  refine ⟨weakly_regular_mem_of_mul l _ _ hreg.toIsWeaklyRegular, fun a ha => ?_⟩
  have e : Ideal.ofList (l ++ [u ^ (K + 1)]) = Ideal.ofList l ⊔ Ideal.span {u ^ (K + 1)} := by
    rw [Ideal.ofList_append, Ideal.ofList_singleton]
  rw [← e] at ha ⊢
  exact weakly_regular_mem_of_mul _ w _ (by simpa using hreg.toIsWeaklyRegular) a ha
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.PsBase
section
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem psBase_equiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (h : IsBase A) : IsBase B := by
  have hd : IsDomain A := h.dom
  have hn : IsIntegrallyClosed A := h.normal
  have hc : IsAdicComplete (maximalIdeal A) A := h.complete
  refine ⟨MulEquiv.isDomain A e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e, h.cm.of_ringEquiv e, ?_⟩
  have hm : Ideal.map e (maximalIdeal A) = maximalIdeal B := by
    ext x
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      intro hu
      apply hy
      simpa using hu.map e.symm
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      intro hu
      apply hx
      simpa using hu.map e
  rw [← hm]
  exact (IsAdicComplete.congr_ringEquiv _ e).2 hc

private theorem psBase_cm (R : Type) [CommRing R] [IsLocalRing R] [IsDomain R]
    (h : ReciprocityTheory.CA.IsCM R) : ReciprocityTheory.CA.IsCM (PowerSeries R) := by
  haveI := h.1
  have hker : Ideal.span {(PowerSeries.X : PowerSeries R)} =
      RingHom.ker (PowerSeries.constantCoeff : PowerSeries R →+* R) := by
    ext f
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, PowerSeries.X_dvd_iff]
  have hsurj : Function.Surjective (PowerSeries.constantCoeff : PowerSeries R →+* R) :=
    fun a => ⟨PowerSeries.C a, by simp⟩
  let e : (PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R)}) ≃+* R :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  haveI : IsLocalRing (PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R)}) :=
    e.symm.isLocalRing
  refine ReciprocityTheory.CA.isCM_of_quotient_span_singleton (x := PowerSeries.X) ?_
    (mem_nonZeroDivisors_of_ne_zero PowerSeries.X_ne_zero) (h.of_ringEquiv e.symm)
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simp

private theorem psBase_one (R : Type) [CommRing R] [IsLocalRing R] (h : IsBase R) :
    IsBase (PowerSeries R) := by
  haveI := h.dom
  haveI := h.normal
  haveI := h.cm.1
  haveI := h.complete
  exact ⟨inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries R,
    psBase_cm R h.cm, UpperTheory.V.abelian₂.adicComplete R⟩

theorem UpperTheory.V.AlgebraTools.Conn.psBase :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], IsBase O → ∀ n : ℕ, IsBase (MvPowerSeries (Fin n) O) := by
  intro O _ _ hO n
  induction n with
  | zero =>
    have hbij : Function.Bijective
        (MvPowerSeries.constantCoeff (σ := Fin 0) (R := O)) := by
      refine ⟨fun f g hfg => ?_, fun a => ⟨MvPowerSeries.C a, by simp⟩⟩
      ext d
      have hd : d = 0 := Subsingleton.elim _ _
      subst hd
      simpa using hfg
    exact psBase_equiv (RingEquiv.ofBijective _ hbij).symm hO
  | succ n ih =>
    exact psBase_equiv (MvPowerSeries.finSuccEquiv O n).toRingEquiv.symm (psBase_one _ ih)
end

