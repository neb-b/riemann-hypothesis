module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualHopfOrderGaussSum
section
open IsLocalRing Polynomial

namespace GlobalTheory.EtaleSpreadReg

theorem isDedekindDomain_atPrime (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) [p.IsPrime] (hp : p.height ≤ 1) :
    IsDedekindDomain (Localization.AtPrime p) := by
  have hic : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hd : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p]
    exact_mod_cast hp
  have : Ring.DimensionLEOne (Localization.AtPrime p) :=
    ⟨fun {P} hP hPp => Ring.krullDimLE_one_iff_of_isPrime_bot.mp hd P hP hPp⟩
  exact {}

theorem isRegularLocalRing_polynomial_atPrime (A : Type*) [CommRing A] (Q₀ : Ideal A[X])
    [Q₀.IsPrime] [IsRegularRing (Localization.AtPrime (Q₀.under A))] :
    IsRegularLocalRing (Localization.AtPrime Q₀) := by
  set p : Ideal A := Q₀.under A with hpdef
  let Ap := Localization.AtPrime p
  letI : Algebra A[X] Ap[X] := Polynomial.algebra A Ap
  let M : Submonoid A[X] := Submonoid.map C p.primeCompl
  haveI : IsLocalization M Ap[X] := Polynomial.isLocalization p.primeCompl Ap
  have hdisj : Disjoint (M : Set A[X]) (Q₀ : Set A[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haQ
    exact ha haQ
  let Q' : Ideal Ap[X] := Q₀.map (algebraMap A[X] Ap[X])
  haveI hQ' : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M Ap[X] Q₀ inferInstance hdisj
  have hc : Q'.comap (algebraMap A[X] Ap[X]) = Q₀ :=
    IsLocalization.under_map_of_isPrime_disjoint M Ap[X] inferInstance hdisj
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime Q') Q'
  have e : (Q'.comap (algebraMap A[X] Ap[X])).primeCompl = Q₀.primeCompl := by
    ext x; simp only [Ideal.mem_primeCompl_iff, hc]
  have h2 : IsLocalization Q₀.primeCompl (Localization.AtPrime Q') := by
    rw [← e]; exact h
  have hreg : IsRegularLocalRing (Localization.AtPrime Q') := isRegularRing_iff.mp inferInstance Q'
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Q₀.primeCompl (Localization.AtPrime Q') (Localization.AtPrime Q₀)).toRingEquiv

theorem isRegularLocalRing_atPrime_of_etale (S T : Type*) [CommRing S] [IsNoetherianRing S]
    [CommRing T] [Algebra S T] [Algebra.Etale S T] (q : Ideal T) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.under S))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing S T
  let p : Ideal S := q.under S
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hun : Algebra.IsUnramifiedAt S q := inferInstance
  have hm := ((Algebra.isUnramifiedAt_iff_map_eq S p q).mp hun).2
  have hm' : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [← hm, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h1 := Ideal.spanFinrank_map_le_of_fg
    (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).fg_of_isNoetherianRing
  rw [hm'] at h1
  have h2 : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_self_add
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
  refine le_trans ?_ (WithBot.coe_le_coe.mpr h2)
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    ← hreg.spanFinrank_maximalIdeal]
  exact_mod_cast h1

theorem isRegularLocalRing_atPrime :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime] (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
    (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
    IsRegularLocalRing (Localization.AtPrime P) := by
  intro A _ _ _ _ EA _ _ _ _ _ QA _ P _ hP
  let Q : Ideal EA := P.comap (algebraMap EA (Localization.AtPrime QA))
  haveI hLoc : IsLocalization.AtPrime (Localization.AtPrime P) Q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization QA.primeCompl
      (Localization.AtPrime P) P
  have hpe : (Q.under (Polynomial A)).under A = P.comap (algebraMap A (Localization.AtPrime QA)) := by
    rw [Ideal.under_under]
    show Ideal.comap (algebraMap A EA) (Ideal.comap (algebraMap EA (Localization.AtPrime QA)) P) = _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  haveI : IsDedekindDomain (Localization.AtPrime ((Q.under (Polynomial A)).under A)) :=
    isDedekindDomain_atPrime A _ (hpe ▸ hP)
  have h0 := isRegularLocalRing_polynomial_atPrime A (Q.under (Polynomial A))
  have h1 := isRegularLocalRing_atPrime_of_etale (Polynomial A) EA Q h0
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) (Localization.AtPrime P)).toRingEquiv

end GlobalTheory.EtaleSpreadReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrExistsUnitPowEqMulUniformizer
section
namespace GlobalTheory

theorem dvr_pow_mul_eq_unit_mul_pow_unif :
    ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V], Function.Injective (algebraMap T V) →
    ∀ (α : V) (ϖ u : T) (m k : ℕ), Irreducible ϖ → IsUnit u → 0 < k →
    α ^ (m * k) = algebraMap T V (u * ϖ ^ k) →
    ∃ γ : V, IsUnit γ ∧ α ^ m = γ * algebraMap T V ϖ ∧ γ ^ k = algebraMap T V u := by
  intro T V _ _ _ _ _ _ _ hinj α ϖ u m k hϖ hu hk h
  have hw : algebraMap T V ϖ ≠ 0 := by
    intro h0
    apply hϖ.ne_zero
    apply hinj
    rw [h0, map_zero]
  have hu' : IsUnit (algebraMap T V u) := hu.map _
  have hxk : (α ^ m) ^ k = algebraMap T V u * (algebraMap T V ϖ) ^ k := by
    rw [← pow_mul, h, map_mul, map_pow]
  have hwk : (algebraMap T V ϖ) ^ k ≠ 0 := pow_ne_zero _ hw
  rcases ValuationRing.dvd_total (α ^ m) (algebraMap T V ϖ) with ⟨c, hc⟩ | ⟨c, hc⟩
  ·
    have heq : (c ^ k * algebraMap T V u) * (algebraMap T V ϖ) ^ k = 1 * (algebraMap T V ϖ) ^ k := by
      calc c ^ k * algebraMap T V u * (algebraMap T V ϖ) ^ k
          = c ^ k * (α ^ m) ^ k := by rw [hxk]; ring
        _ = (α ^ m * c) ^ k := by ring
        _ = (algebraMap T V ϖ) ^ k := by rw [← hc]
        _ = 1 * (algebraMap T V ϖ) ^ k := by ring
    have h1 := mul_right_cancel₀ hwk heq
    have hc' : IsUnit c := (isUnit_pow_iff hk.ne').mp (IsUnit.of_mul_eq_one _ h1)
    obtain ⟨cu, rfl⟩ := hc'
    refine ⟨↑cu⁻¹, Units.isUnit _, ?_, ?_⟩
    · rw [hc, mul_comm (α ^ m), ← mul_assoc, Units.inv_mul, one_mul]
    · calc ((↑cu⁻¹ : V)) ^ k = (↑cu⁻¹ : V) ^ k * ((↑cu : V) ^ k * algebraMap T V u) := by
            rw [h1, mul_one]
        _ = algebraMap T V u := by
            rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  ·
    have heq : c ^ k * (algebraMap T V ϖ) ^ k = algebraMap T V u * (algebraMap T V ϖ) ^ k := by
      rw [← hxk, hc]; ring
    have h1 := mul_right_cancel₀ hwk heq
    exact ⟨c, (isUnit_pow_iff hk.ne').mp (h1 ▸ hu'), by rw [hc, mul_comm], h1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrLocPrincipalPrime
section
noncomputable section

namespace GlobalTheory

theorem dvr_loc_principal_prime : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by
  intro L _ A t hN ht hp hfr
  set p : Ideal A := Ideal.span {t} with hpdef
  haveI : IsFractionRing A L := IsFractionRing.of_field A L fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
      show z = a / b
      rw [← h, mul_div_cancel_right₀ _ hb0]⟩
  let V0 : Subalgebra A L := Localization.subalgebra.ofField L p.primeCompl p.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime V0 p := Localization.subalgebra.isLocalization_ofField _ _ _
  haveI : IsLocalRing V0 := IsLocalization.AtPrime.isLocalRing V0 p
  haveI : IsNoetherianRing V0 := IsLocalization.isNoetherianRing p.primeCompl V0 hN
  have hmax : IsLocalRing.maximalIdeal V0 = Ideal.span {algebraMap A V0 t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p V0, hpdef, Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap A V0 t ≠ 0 := fun h => ht (congrArg Subtype.val h)
  have hnf : ¬ IsField V0 := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact ht0
  have hdvr : IsDiscreteValuationRing V0 :=
    ((IsDiscreteValuationRing.TFAE V0 hnf).out 1 5).2
      (⟨⟨_, hmax⟩⟩ : (IsLocalRing.maximalIdeal V0).IsPrincipal)
  haveI : IsFractionRing V0 L := IsFractionRing.of_field V0 L fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr z
    exact ⟨algebraMap A V0 ⟨a, ha⟩, algebraMap A V0 ⟨b, hb⟩, by
      show z = a / b
      rw [← h, mul_div_cancel_right₀ _ hb0]⟩
  let V : ValuationSubring L :=
    { V0.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger V0 x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact Or.inl (hy ▸ y.2)
        · exact Or.inr (hy ▸ y.2) }
  have hA : ∀ a ∈ A, a ∈ V := fun a ha => V0.algebraMap_mem (⟨a, ha⟩ : A)
  refine ⟨V, hA, hdvr, ?_, ?_, ?_, ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  · intro s hs
    exact IsLocalization.map_units V0 (⟨s, hs⟩ : p.primeCompl)
  · intro f
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective p.primeCompl (show V0 from f)
    refine ⟨x, y, y.2, ?_⟩
    have := congrArg (algebraMap V0 L) (IsLocalization.mk'_spec V0 x y)
    have hxy' : IsLocalization.mk' V0 x y = (show V0 from f) := hxy
    rw [hxy', map_mul] at this
    exact this
  · have h := (RingHom.essFiniteType_algebraMap (R := A) (S := V0)).2
      (Algebra.EssFiniteType.of_isLocalization V0 p.primeCompl)
    exact h

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrSubringEqTop
section
open IsLocalRing

namespace GlobalTheory

theorem dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) :
    ∀ N : ℕ, ∀ s ∈ S, s ∉ (IsLocalRing.maximalIdeal V) ^ N →
      ∃ k : ℕ, ∃ u ∈ S, u ∉ IsLocalRing.maximalIdeal V ∧ s = π ^ k * u := by
  intro N
  induction N with
  | zero => intro s _ hs; simp at hs
  | succ N ih =>
    intro s hs hsN
    by_cases hm : s ∈ IsLocalRing.maximalIdeal V
    · obtain ⟨t, htS, rfl⟩ := hdiv s hs hm
      have htN : t ∉ (IsLocalRing.maximalIdeal V) ^ N := by
        intro ht
        apply hsN
        rw [pow_succ']
        exact Ideal.mul_mem_mul hπm ht
      obtain ⟨k, u, huS, hum, rfl⟩ := ih t htS htN
      exact ⟨k + 1, u, huS, hum, by ring⟩
    · exact ⟨0, s, hs, hm, by simp⟩

theorem dvrSubring_factor {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t)
    (s : V) (hs : s ∈ S) (h0 : s ≠ 0) :
    ∃ k : ℕ, ∃ u ∈ S, u ∉ IsLocalRing.maximalIdeal V ∧ s = π ^ k * u := by
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  have : ∃ N : ℕ, s ∉ (maximalIdeal V) ^ N := by
    by_contra hc
    push_neg at hc
    have : s ∈ ⨅ i : ℕ, (maximalIdeal V) ^ i := Ideal.mem_iInf.2 hc
    rw [hinf, Ideal.mem_bot] at this
    exact h0 this
  obtain ⟨N, hN⟩ := this
  exact dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow S π hπm hdiv N s hs hN

theorem dvrSubring_eq_top (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπS : π ∈ S) (hπ0 : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hinv : ∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t)
    (hfrac : ∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) : S = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨a, haS, b, hbS, hb0, hvb⟩ := hfrac v
  by_cases ha0 : a = 0
  · subst ha0
    have : v = 0 := (mul_eq_zero.1 hvb).resolve_right hb0
    rw [this]; exact S.zero_mem
  obtain ⟨k, u, huS, hum, rfl⟩ := dvrSubring_factor S π hπm hdiv a haS ha0
  obtain ⟨l, u', hu'S, hu'm, rfl⟩ := dvrSubring_factor S π hπm hdiv b hbS hb0
  obtain ⟨t', ht'S, ht'⟩ := hinv u' hu'S hu'm
  have hπl : π ^ l ≠ 0 := pow_ne_zero _ hπ0
  by_cases hkl : l ≤ k
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    have h1 : v * u' = π ^ d * u := by
      apply mul_left_cancel₀ hπl
      rw [pow_add] at hvb
      linear_combination hvb
    have h2 : v = π ^ d * u * t' := by
      linear_combination t' * h1 - v * ht'
    rw [h2]
    exact S.mul_mem (S.mul_mem (S.pow_mem hπS _) huS) ht'S
  · push_neg at hkl
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hkl
    subst hd
    have hπk : π ^ k ≠ 0 := pow_ne_zero _ hπ0
    have h1 : v * π ^ (d + 1) * u' = u := by
      apply mul_left_cancel₀ hπk
      rw [show k + d + 1 = k + (d + 1) by ring, pow_add] at hvb
      linear_combination hvb
    apply absurd _ hum
    rw [← h1, pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hπm))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompBaseChange
section
open Matrix

namespace GlobalTheory

theorem eigen_decomp_base_change :
  ∀ (K C : Type) [CommRing K] [CommRing C] (n a : ℕ) (ω : K) (tr nm : ℤ), ω ^ 2 - (tr : K) * ω + (nm : K) = 0 → ∀ (f : K →+* Matrix (Fin n) (Fin n) C) (ρ : C), ρ ^ 2 - (tr : C) * ρ + (nm : C) = 0 → IsUnit (2 * ρ - (tr : C)) → ∀ (t : Fin a → (K →+* C)), (∀ i, t i ω = ρ) → (∀ v : Fin n → C, Matrix.mulVec (f ω) v = ρ • v → ∃ w : Fin a → Fin n → C, (∀ i (c : K), Matrix.mulVec (f c) (w i) = t i c • w i) ∧ v = ∑ i, w i) → ∀ (R' : Type) [CommRing R'] (g : C →+* R') (v : Fin n → R'), Matrix.mulVec ((f ω).map g) v = g ρ • v → ∃ w : Fin a → Fin n → R', (∀ i (c : K), Matrix.mulVec ((f c).map g) (w i) = g (t i c) • w i) ∧ v = ∑ i, w i := by
  intro K C _ _ n a ω tr nm hω f ρ hρ hu t ht H R' _ g v hv
  obtain ⟨uinv, huinv⟩ : ∃ uinv : C, uinv * (2 * ρ - (tr : C)) = 1 := by
    obtain ⟨u, hu'⟩ := hu
    exact ⟨↑u⁻¹, by rw [← hu']; simp⟩
  set Ω := f ω with hΩdef

  have hΩΩ : Ω * Ω = (tr : Matrix (Fin n) (Fin n) C) * Ω - (nm : Matrix (Fin n) (Fin n) C) := by
    have h1 : ω * ω = (tr : K) * ω - (nm : K) := by linear_combination hω
    have h2 := congrArg f h1
    simpa [map_mul, map_sub, map_intCast] using h2
  have key : ∀ x : Fin n → C, Ω *ᵥ (Ω *ᵥ x) = (tr : C) • (Ω *ᵥ x) - (nm : C) • x := by
    intro x
    rw [mulVec_mulVec, hΩΩ, sub_mulVec, ← mulVec_mulVec, intCast_mulVec, intCast_mulVec]
  have eig : ∀ x : Fin n → C, Ω *ᵥ (Ω *ᵥ x - ((tr : C) - ρ) • x) = ρ • (Ω *ᵥ x - ((tr : C) - ρ) • x) := by
    intro x
    rw [mulVec_sub, mulVec_smul, key]
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(x k)) * hρ
  let e : Fin n → Fin n → C := fun j => uinv • (Ω *ᵥ Pi.single j 1 - ((tr : C) - ρ) • Pi.single j 1)
  have he : ∀ j, Ω *ᵥ e j = ρ • e j := by
    intro j
    simp only [e, mulVec_smul, eig]
    rw [smul_comm]
  choose W hW hWsum using fun j => H (e j) (he j)

  have hmap : ∀ (M : Matrix (Fin n) (Fin n) C) (x : Fin n → C), M.map g *ᵥ (g ∘ x) = g ∘ (M *ᵥ x) := by
    intro M x
    funext k
    simp only [Function.comp_apply]
    rw [RingHom.map_mulVec]
  have hvsum : v = ∑ j, v j • (g ∘ e j) := by
    funext k
    have hv' := congrFun hv k
    simp only [mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hv'
    simp only [e, Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.sub_apply,
      mulVec_single_one, col_apply, Pi.single_apply, map_mul, map_sub, mul_ite, mul_one, mul_zero,
      map_zero]
    have hterm : ∀ x, v x * (g uinv * (g (Ω k x) - g (if k = x then (tr : C) - ρ else 0))) =
        g uinv * (g (Ω k x) * v x) - (if k = x then g uinv * g ((tr : C) - ρ) * v k else 0) := by
      intro x
      split_ifs with h
      · subst h; ring
      · simp only [map_zero, sub_zero]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_sub_distrib, ← Finset.mul_sum, hv',
      Finset.sum_ite_eq]
    have hg := congrArg g huinv
    simp only [map_mul, map_sub, map_intCast, map_one, map_ofNat] at hg ⊢
    simp only [Finset.mem_univ, if_true]
    linear_combination (-(v k)) * hg
  refine ⟨fun i => ∑ j, v j • (g ∘ W j i), ?_, ?_⟩
  · intro i c
    rw [mulVec_sum]
    simp only [mulVec_smul, hmap, hW]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
    congr 1
    funext k
    simp [Function.comp_apply]
  · conv_lhs => rw [hvsum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.smul_sum]
    congr 1
    rw [hWsum j]
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finset.sum_apply, map_sum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIdempotentsOfComaximal
section
universe u

namespace GlobalTheory

theorem eigenIdempotents_of_comaximal
    {C : Type} [CommRing C] {A : Type} [CommRing A] {W : Type u} [AddCommGroup W] [Module C W]
    (σ : A →+* Module.End C W) (a : ℕ) (χ : Fin a → A →+* C) :
    (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
    ∃ e : Fin a → Module.End C W,
      (∀ i (T : Module.End C W), (∀ c, T * σ c = σ c * T) → T * e i = e i * T) ∧
      (∀ i w, (∀ c, σ c w = χ i c • w) → e i w = w) ∧
      (∀ i j w, j ≠ i → (∀ c, σ c w = χ j c • w) → e i w = 0) := by
  classical
  intro hcom
  have hc : ∀ i j, ∃ c : A →₀ C, i ≠ j → (c.sum fun x r => r * (χ i x - χ j x)) = 1 := by
    intro i j
    by_cases h : i = j
    · exact ⟨0, fun h' => absurd h h'⟩
    · have h1 : (1 : C) ∈ Ideal.span (Set.range fun x => χ i x - χ j x) := by
        rw [hcom i j h]; trivial
      obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1
      exact ⟨c, fun _ => by simpa [smul_eq_mul] using hc⟩
  choose c hc using hc
  let Z : Fin a → Fin a → Module.End C W := fun i j =>
    (c i j).sum fun x r => r • (σ x - χ j x • (1 : Module.End C W))
  have hZ : ∀ i j k (w : W), (∀ x, σ x w = χ k x • w) →
      Z i j w = ((c i j).sum fun x r => r * (χ k x - χ j x)) • w := by
    intro i j k w hw
    simp only [Z, Finsupp.sum, LinearMap.sum_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [hw, sub_smul, mul_smul, smul_sub]
  have hZc : ∀ i j (T : Module.End C W), (∀ c, T * σ c = σ c * T) → Commute T (Z i j) := by
    intro i j T hT
    simp only [Z, Finsupp.sum]
    refine Commute.sum_right _ _ _ fun x _ => ?_
    exact ((show Commute T (σ x) from hT x).sub_right ((Commute.one_right T).smul_right _)).smul_right _
  have hlist : ∀ (i : Fin a) (s : Fin a → C) (w : W) (L : List (Fin a)),
      (∀ j ∈ L, Z i j w = s j • w) → (L.map (Z i)).prod w = (L.map s).prod • w := by
    intro i s w L hL
    induction L with
    | nil => simp
    | cons j L ih =>
      have ih' := ih (fun k hk => hL k (List.mem_cons_of_mem _ hk))
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih', map_smul,
        hL j List.mem_cons_self, smul_smul]
      rw [mul_comm]
  refine ⟨fun i => (((List.finRange a).filter (· ≠ i)).map (Z i)).prod, ?_, ?_, ?_⟩
  · intro i T hT
    exact (Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 hy
      exact hZc i j T hT).eq
  · intro i w hw
    rw [hlist i (fun j => (c i j).sum fun x r => r * (χ i x - χ j x)) w _
      (fun j _ => hZ i j i w hw)]
    rw [List.prod_eq_one, one_smul]
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    have hji : j ≠ i := by simpa using (List.mem_filter.1 hj).2
    exact hc i j (Ne.symm hji)
  · intro i j w hji hw
    rw [hlist i (fun k => (c i k).sum fun x r => r * (χ j x - χ k x)) w _
      (fun k _ => hZ i k j w hw)]
    rw [List.prod_eq_zero, zero_smul]
    refine List.mem_map.2 ⟨j, ?_, ?_⟩
    · exact List.mem_filter.2 ⟨List.mem_finRange j, by simpa using hji⟩
    · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvectorMemSpanTwistedTraceImage
section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory


open scoped BigOperators Matrix in
open Polynomial in
theorem _root_.GlobalTheory.eigenvector_mem_span_twistedTrace_image :
    ∀ (H K V : Type) [Group H] [Fintype H] [Field K] [CharZero K] [AddCommGroup V] [Module K V] (st : H → V →ₗ[K] V), (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (s : Set V), Submodule.span K s = ⊤ → ∀ x : V, (∀ h, st h x = ((χ h : Kˣ) : K) • x) → x ∈ Submodule.span K ((fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) '' s) := by
  intro H K V _ _ _ _ _ _ st _ χ s hs x hx
  let P : V →ₗ[K] V := ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h
  have hP : (fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) = ⇑P := by
    funext y
    simp [P, LinearMap.sum_apply]
  have hPx : P x = (Fintype.card H : K) • x := by
    rw [← hP]
    simp only [hx, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hcard : (Fintype.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hxP : x = P ((Fintype.card H : K)⁻¹ • x) := by
    rw [map_smul, hPx, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hP, Submodule.span_image, hs, hxP]
  exact Submodule.mem_map_of_mem Submodule.mem_top

end GlobalTheory
end

