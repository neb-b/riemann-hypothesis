module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHermitianDiagonalizationUnits
section
namespace GlobalTheory

theorem surj_mod_of_surj_mod_map_sup_of_pow_map_le :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (I : Ideal B) (K : Ideal A) (N : ℕ),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ I.map (algebraMap B A) ⊔ K) →
      (I ^ N).map (algebraMap B A) ≤ K → ∀ a : A, ∃ b : B, a - algebraMap B A b ∈ K := by
  intro B A _ _ _ I K N hsurj hN
  set f := algebraMap B A with hf
  set J := I.map f with hJ

  have key : ∀ n : ℕ, ∀ a : A, ∃ b : B, a - f b ∈ J ^ n ⊔ K := by
    intro n
    induction n with
    | zero =>
      intro a
      exact ⟨0, by simp⟩
    | succ n ih =>

      have hspan : ∀ x ∈ J ^ n, ∀ c : A, ∃ b : B, c * x - f b ∈ J ^ (n + 1) ⊔ K := by
        intro x hx
        rw [hJ, ← Ideal.map_pow] at hx
        unfold Ideal.map at hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, hi, rfl⟩ := hx
          intro c
          obtain ⟨b', hb'⟩ := hsurj c
          obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hb'
          refine ⟨b' * i, ?_⟩
          have hfi : f i ∈ J ^ n := by
            rw [hJ, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hi
          have hc : c = f b' + y + z := by rw [add_assoc, hyz]; ring
          have e : c * f i - f (b' * i) = f i * y + z * f i := by
            rw [hc, map_mul]; ring
          rw [e]
          refine Submodule.add_mem_sup ?_ (K.mul_mem_right _ hz)
          rw [pow_succ]
          exact Ideal.mul_mem_mul hfi hy
        | zero =>
          intro c; exact ⟨0, by simp⟩
        | add x y _ _ hx hy =>
          intro c
          obtain ⟨b1, h1⟩ := hx c
          obtain ⟨b2, h2⟩ := hy c
          refine ⟨b1 + b2, ?_⟩
          have e : c * (x + y) - f (b1 + b2) = (c * x - f b1) + (c * y - f b2) := by
            rw [map_add (f := _)]; ring
          rw [e]; exact add_mem h1 h2
        | smul d x _ hx =>
          intro c
          obtain ⟨b, h⟩ := hx (c * d)
          refine ⟨b, ?_⟩
          rw [smul_eq_mul, ← mul_assoc]; exact h
      intro a
      obtain ⟨b, hb⟩ := ih a
      obtain ⟨x, hx, k, hk, hxk⟩ := Submodule.mem_sup.mp hb
      obtain ⟨b2, hb2⟩ := hspan x hx 1
      refine ⟨b + b2, ?_⟩
      have e : a - f (b + b2) = (1 * x - f b2) + k := by
        rw [map_add (f := _), one_mul]; linear_combination -hxk
      rw [e]
      refine add_mem hb2 (Submodule.mem_sup_right hk)
  intro a
  obtain ⟨b, hb⟩ := key N a
  refine ⟨b, ?_⟩
  have hle : J ^ N ⊔ K ≤ K := by
    refine sup_le ?_ le_rfl
    rw [hJ, ← Ideal.map_pow]; exact hN
  exact hle hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingPointsIdealCriterion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem exists_ideal_factor_closedImmersion_iff (A : Type) [CommRing A] (X Y : Scheme.{0})
    (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X) [IsClosedImmersion j] :
    ∃ I : Ideal A, ∀ (R : Type) [CommRing R] (ψ : A →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔
        I ≤ RingHom.ker ψ := by
  obtain ⟨I, e, hf⟩ := (IsClosedImmersion.Spec_iff (f := pullback.snd j a)).mp inferInstance
  refine ⟨I, fun R _ ψ => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    let z : Spec (CommRingCat.of R) ⟶ pullback j a := pullback.lift y (Spec.map (CommRingCat.ofHom ψ)) hy
    have hz : z ≫ pullback.snd j a = Spec.map (CommRingCat.ofHom ψ) := pullback.lift_snd _ _ _
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (z ≫ e.hom)
    have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ χ) = Spec.map (CommRingCat.ofHom ψ) := by
      rw [Spec.map_comp, hχ, Category.assoc, ← hf, hz]
    have h2 := Spec.map_injective h1
    intro x hx
    have := congrArg (fun g => g.hom x) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this
    rw [RingHom.mem_ker, ← this, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro h
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun x hx => h hx))) ≫ e.inv ≫ pullback.fst j a, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition, hf, Category.assoc, Iso.inv_hom_id_assoc,
      ← Spec.map_comp_assoc]
    congr 2

theorem factor_closedImmersion_iff_of_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (X Y : Scheme.{0}) (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X), IsClosedImmersion j → ∀ J : Ideal A, (∀ (R : Type) [CommRing R] [IsLocalRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ) → ∀ (R : Type) [CommRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ := by
  intro A _ _ X Y a j hj J H
  obtain ⟨I, hI⟩ := exists_ideal_factor_closedImmersion_iff A X Y a j
  have key : ∀ (K : Ideal A), K ≠ ⊤ → (I ≤ K ↔ J ≤ K) := by
    intro K hK
    haveI : Nontrivial (A ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hK
    haveI : IsLocalRing (A ⧸ K) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have := (hI (A ⧸ K) (Ideal.Quotient.mk K)).symm.trans (H (A ⧸ K) (Ideal.Quotient.mk K))
    simpa [Ideal.mk_ker] using this
  have hIJ : I = J := by
    apply le_antisymm
    · by_cases hJ : J = ⊤
      · rw [hJ]; exact le_top
      · exact (key J hJ).mpr le_rfl
    · by_cases hI' : I = ⊤
      · rw [hI']; exact le_top
      · exact (key I hI').mp le_rfl
  intro R _ ψ
  rw [← hIJ]
  exact hI R ψ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayInjectiveAtPrimeOfDvd
section
namespace GlobalTheory

theorem localization_away_injective_of_dvd (R : Type) [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    ∃ t ∉ 𝔭, ∀ (c : R), t ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭,
      κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) →
      Function.Injective κ := by
  classical
  set I : Ideal R := RingHom.ker (algebraMap R (Localization.AtPrime 𝔭)) with hI
  obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
  have key : ∀ s : Finset R, (∀ x ∈ s, algebraMap R (Localization.AtPrime 𝔭) x = 0) →
      ∃ t ∉ 𝔭, ∀ x ∈ s, t * x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, fun h => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
    | insert a s ha ih =>
      intro h
      obtain ⟨t, ht, hts⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl (Localization.AtPrime 𝔭) a).mp
        (h a (Finset.mem_insert_self a s))
      refine ⟨(m : R) * t, 𝔭.primeCompl.mul_mem m.2 ht, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_comm (m : R) t, mul_assoc, hm, mul_zero]
      · rw [mul_assoc, hts x hx, mul_zero]
  obtain ⟨t, ht, hts⟩ := key s (fun x hx => by
    have : x ∈ I := hs ▸ Submodule.subset_span hx
    simpa [hI] using this)
  have hker : ∀ x ∈ I, t * x = 0 := by
    have hle : I ≤ LinearMap.ker (LinearMap.mulLeft R t) := by
      rw [← hs, Submodule.span_le]
      intro x hx
      simp [hts x hx]
    intro x hx
    simpa using hle hx
  refine ⟨t, ht, ?_⟩
  intro c ⟨d, hd⟩ κ hκ
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers c) x
  have hspec := IsLocalization.mk'_spec (Localization.Away c) a m
  have h1 : algebraMap R (Localization.AtPrime 𝔭) a = 0 := by
    have := congrArg κ hspec
    rw [map_mul, hx, zero_mul] at this
    rw [← hκ, RingHom.comp_apply, ← this]
  have hta : t * a = 0 := hker a (by simpa [hI] using h1)
  have hu : IsUnit (algebraMap R (Localization.Away c) t) := by
    have hc := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away c) c
    have hc' : IsUnit (algebraMap R (Localization.Away c) t * algebraMap R (Localization.Away c) d) := by
      rw [← map_mul, ← hd]; exact hc
    exact isUnit_of_mul_isUnit_left hc'
  have ha : algebraMap R (Localization.Away c) a = 0 := by
    have : algebraMap R (Localization.Away c) t * algebraMap R (Localization.Away c) a = 0 := by
      rw [← map_mul, hta, map_zero]
    exact (hu.mul_right_eq_zero).mp this
  show IsLocalization.mk' (Localization.Away c) a m = 0
  rw [IsLocalization.mk'_eq_mul_mk'_one, ha, zero_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIntegralClosureArtinianReducedDomain
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

open Polynomial

theorem exists_mul_mul_eq_self_of_isArtinian_isReduced {A : Type} [CommRing A] [IsArtinianRing A]
    [IsReduced A] (a : A) : ∃ y : A, a * a * y = a := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : A)
  simp only [smul_eq_mul, mul_one] at hy
  have hy' : a ^ (n + 1) * y = a ^ n := hy
  refine ⟨y, ?_⟩
  have hc : IsNilpotent (a - a * a * y) := ⟨n + 1, by
    calc (a - a * a * y) ^ (n + 1) = (a * (1 - a * y)) ^ (n + 1) := by ring
    _ = a ^ (n + 1) * (1 - a * y) ^ (n + 1) := mul_pow _ _ _
    _ = (a ^ (n + 1) - a * (a ^ (n + 1) * y)) * (1 - a * y) ^ n := by rw [pow_succ (1 - a * y)]; ring
    _ = 0 := by rw [hy', ← pow_succ', sub_self, zero_mul]⟩
  exact (sub_eq_zero.mp hc.eq_zero).symm

theorem idempotent_mul_aeval_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (x : A) (p : R[X]) : f * aeval (f * x) p = f * aeval x p := by
  simp only [aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, mul_smul_comm, mul_pow, ← mul_assoc, ← pow_succ', hf.pow_succ_eq]

theorem isIntegral_of_isIdempotentElem {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {e : A}
    (he : IsIdempotentElem e) : IsIntegral R e :=
  ⟨X * (X - C 1), monic_X.mul (monic_X_sub_C 1), by
    simp only [eval₂_mul, eval₂_X, eval₂_sub, eval₂_C, eval₂_one, map_one, mul_sub, mul_one,
      he.eq, sub_self]⟩

theorem localization_integralClosure_isDomain_isIntegrallyClosed
    (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [IsArtinianRing A] [IsReduced A]
    (Q : Ideal (integralClosure R A)) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  classical
  have hidem : ∀ e : A, IsIdempotentElem e → e ∈ integralClosure R A := fun e he =>
    (show IsIntegral R e from isIntegral_of_isIdempotentElem he)
  have hcompl : ∀ e : integralClosure R A, e ∈ Q → (1 - e) ∈ Q.primeCompl := by
    intro e he h1
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr (by
      simpa using Q.add_mem he h1))
  let T : Submonoid A := Algebra.algebraMapSubmonoid A Q.primeCompl
  let J : Ideal A := RingHom.ker (algebraMap A (Localization T))
  have memJ : ∀ a : A, a ∈ J ↔ ∃ s ∈ Q.primeCompl, (s : A) * a = 0 := by
    intro a
    rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff T]
    constructor
    · rintro ⟨⟨m, hm⟩, hma⟩
      obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hm
      exact ⟨s, hs, hma⟩
    · rintro ⟨s, hs, hsa⟩
      exact ⟨⟨(s : A), Submonoid.mem_map.mpr ⟨s, hs, rfl⟩⟩, hsa⟩
  have hS : ∀ s ∈ Q.primeCompl, (s : A) ∉ J := by
    intro s hs h
    obtain ⟨t, ht, hts⟩ := (memJ _).mp h
    have h0 : t * s = 0 := Subtype.ext (by simpa using hts)
    exact (Q.primeCompl.mul_mem ht hs) (h0 ▸ Q.zero_mem)
  have hJprime : J.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      exact hS 1 Q.primeCompl.one_mem (by simp [htop])
    · intro a c hac
      obtain ⟨y, hy⟩ := exists_mul_mul_eq_self_of_isArtinian_isReduced a
      have hei : IsIdempotentElem (a * y) := by
        unfold IsIdempotentElem
        calc a * y * (a * y) = (a * a * y) * y := by ring
        _ = a * y := by rw [hy]
      let e : integralClosure R A := ⟨a * y, hidem _ hei⟩
      by_cases he : e ∈ Q
      · left
        refine (memJ a).mpr ⟨1 - e, hcompl e he, ?_⟩
        simp only [e, Subalgebra.coe_sub, OneMemClass.coe_one]
        linear_combination -hy
      · right
        obtain ⟨s, hs, hsac⟩ := (memJ _).mp hac
        refine (memJ c).mpr ⟨s * e, Q.primeCompl.mul_mem hs he, ?_⟩
        simp only [e, MulMemClass.coe_mul]
        linear_combination y * hsac
  haveI : J.IsPrime := hJprime
  haveI hJm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  let g : integralClosure R A →+* A ⧸ J := algebraMap (integralClosure R A) (A ⧸ J)
  have g_eq : ∀ b, g b = Ideal.Quotient.mk J (b : A) := fun b => rfl
  have hunit : ∀ s : Q.primeCompl, IsUnit (g s) := by
    intro s
    rw [isUnit_iff_ne_zero, g_eq, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hS s.1 s.2
  have hB0 : ∀ b : integralClosure R A,
      algebraMap (integralClosure R A) (Localization.AtPrime Q) b = 0 ↔ g b = 0 := by
    intro b
    rw [IsLocalization.map_eq_zero_iff Q.primeCompl, g_eq, Ideal.Quotient.eq_zero_iff_mem, memJ]
    constructor
    · rintro ⟨⟨s, hs⟩, hsb⟩
      exact ⟨s, hs, by simpa using congrArg Subtype.val hsb⟩
    · rintro ⟨s, hs, hsb⟩
      exact ⟨⟨s, hs⟩, Subtype.ext (by simpa using hsb)⟩
  let ψ : Localization.AtPrime Q →+* A ⧸ J := IsLocalization.lift (M := Q.primeCompl) hunit
  have hinj : Function.Injective ψ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [← sub_eq_zero, ← map_sub, hB0, map_sub, sub_eq_zero]
  haveI hdom : IsDomain (Localization.AtPrime Q) := Function.Injective.isDomain ψ hinj
  refine ⟨hdom, ?_⟩
  letI : Algebra (Localization.AtPrime Q) (A ⧸ J) := ψ.toAlgebra
  haveI : IsScalarTower (integralClosure R A) (Localization.AtPrime Q) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.lift_eq hunit b).symm
  have hclosed : ∀ z : A ⧸ J, IsIntegral (Localization.AtPrime Q) z → ∃ w, ψ w = z := by
    intro z hz
    obtain ⟨⟨s, hs⟩, hint⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization Q.primeCompl z hz
    have hint' : IsIntegral R ((⟨s, hs⟩ : Q.primeCompl) • z) := isIntegral_trans _ hint
    obtain ⟨p, hpm, hp⟩ := hint'
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((⟨s, hs⟩ : Q.primeCompl) • z)
    have hpa : aeval a p ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_algHom_apply,
        Ideal.Quotient.mkₐ_eq_mk, ha]
      exact hp
    obtain ⟨t, ht, htp⟩ := (memJ _).mp hpa
    obtain ⟨w, hw⟩ := exists_mul_mul_eq_self_of_isArtinian_isReduced (t : A)
    have hfi : IsIdempotentElem ((t : A) * w) := by
      unfold IsIdempotentElem
      calc (t : A) * w * ((t : A) * w) = ((t : A) * t * w) * w := by ring
      _ = (t : A) * w := by rw [hw]
    let f : integralClosure R A := ⟨(t : A) * w, hidem _ hfi⟩
    have hf : f ∈ Q.primeCompl := by
      intro hfQ
      apply hS t ht
      refine (memJ _).mpr ⟨1 - f, hcompl f hfQ, ?_⟩
      simp only [f, Subalgebra.coe_sub, OneMemClass.coe_one]
      linear_combination -hw
    have hfp : (t : A) * w * aeval a p = 0 := by linear_combination w * htp
    have hfa : IsIntegral R ((t : A) * w * a) := by
      refine ⟨X * p, monic_X.mul hpm, ?_⟩
      rw [← aeval_def, map_mul, aeval_X]
      calc (t : A) * w * a * aeval ((t : A) * w * a) p
          = a * ((t : A) * w * aeval ((t : A) * w * a) p) := by ring
      _ = 0 := by rw [idempotent_mul_aeval_mul hfi, hfp, mul_zero]
    let c : integralClosure R A := ⟨(t : A) * w * a, (show IsIntegral R ((t : A) * w * a) from hfa)⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime Q) c (⟨s, hs⟩ : Q.primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    have hf1 : g f = 1 := by
      have hne : g f ≠ 0 := by
        rw [g_eq, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hS f hf
      have hid : g f * g f = g f := by
        rw [← map_mul]; exact congrArg g (Subtype.ext hfi.eq)
      have : g f * (g f - 1) = 0 := by rw [mul_sub, hid, mul_one, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
    have hsz : (⟨s, hs⟩ : Q.primeCompl) • z = g s * z := by
      rw [Submonoid.smul_def, Algebra.smul_def]
    have hgc : g c = g f * Ideal.Quotient.mk J a := by
      rw [g_eq, g_eq, ← map_mul]
    rw [hgc, hf1, one_mul, ha, hsz]
  rw [isIntegrallyClosed_iff (FractionRing (Localization.AtPrime Q))]
  intro x hx
  have hinj' : Function.Injective (algebraMap (Localization.AtPrime Q) (A ⧸ J)) := hinj
  let ι := IsFractionRing.liftAlgHom (R := Localization.AtPrime Q) (A := Localization.AtPrime Q)
    (K := FractionRing (Localization.AtPrime Q)) (L := A ⧸ J)
    (g := Algebra.ofId (Localization.AtPrime Q) (A ⧸ J)) hinj'
  obtain ⟨w, hw⟩ := hclosed (ι x) (hx.map ι)
  refine ⟨w, ι.toRingHom.injective ?_⟩
  change ι (algebraMap _ _ w) = ι x
  rw [AlgHom.commutes]
  exact hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationMaximalIdealEqSpanNilpotentArtinian
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem localization_maximalIdeal_eq_span_of_nilpotent
    (D : Type) [CommRing D] [IsArtinianRing D] (x : D) (hx : IsNilpotent x)
    (hred : IsReduced (D ⧸ Ideal.span {x})) (P : Ideal D) [P.IsMaximal] :
    IsLocalRing.maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap D (Localization.AtPrime P) x} := by
  set L := Localization.AtPrime P
  apply le_antisymm
  · intro a ha

    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := L)
    have hJ : (⊥ : Ideal L).jacobson = IsLocalRing.maximalIdeal L :=
      IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top
    have han : a ^ n = 0 := by
      have : a ^ n ∈ (⊥ : Ideal L).jacobson ^ n := Ideal.pow_mem_pow (hJ ▸ ha) n
      rw [hn] at this
      simpa using this
    obtain ⟨⟨d, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
    simp only at han ⊢
    rw [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_zero_iff] at han
    obtain ⟨t, ht⟩ := han
    have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {x}) ((t : D) * d)) := by
      refine ⟨n + 1, ?_⟩
      rw [← map_pow, mul_pow, pow_succ d, ← mul_assoc, pow_succ (t : D), mul_assoc _ (t : D), ht]
      simp
    have hmem : (t : D) * d ∈ Ideal.span {x} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (hnil.eq_zero)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    refine Ideal.mem_span_singleton'.mpr ⟨IsLocalization.mk' L c (t * s), ?_⟩
    rw [IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_mul_mk'_one d s,
      mul_right_comm, ← map_mul, hc, ← IsLocalization.mk'_eq_mul_mk'_one,
      ← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_iff_eq]
    congr 1
    push_cast
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
    obtain ⟨m, hm⟩ := hx.map (algebraMap D L)
    exact not_isUnit_zero (hm ▸ hu.pow m)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationQuotientComapEquiv
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem localization_quotient_comap_equiv :
    ∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B), Function.Surjective φ →
      ∀ (p q : Ideal B) [q.IsPrime],
        Nonempty ((Localization.AtPrime (q.comap φ) ⧸
            (p.comap φ).map (algebraMap S (Localization.AtPrime (q.comap φ)))) ≃+*
          (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) := by
  intro S B _ _ φ hφ p q _
  let ψ := Localization.localRingHom (q.comap φ) q φ rfl
  let f := (Ideal.Quotient.mk (p.map (algebraMap B (Localization.AtPrime q)))).comp ψ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨a, rfl⟩ := hφ b
    obtain ⟨t₀, ht₀⟩ := hφ (t : B)
    have ht₀' : t₀ ∈ (q.comap φ).primeCompl := by
      show t₀ ∉ q.comap φ
      rw [Ideal.mem_comap, ht₀]
      exact t.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime (q.comap φ)) a ⟨t₀, ht₀'⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht₀
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hψ
  have hker : RingHom.ker f = (p.comap φ).map (algebraMap S (Localization.AtPrime (q.comap φ))) := by
    ext x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (q.comap φ).primeCompl x
    simp only [RingHom.mem_ker, f, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ψ,
      Localization.localRingHom_mk']
    rw [IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨t, ht, hta⟩
      obtain ⟨t₀, rfl⟩ := hφ t
      refine ⟨t₀, ?_, ?_⟩
      · show t₀ ∉ q.comap φ
        simpa [Ideal.mem_comap] using ht
      · simpa [Ideal.mem_comap, map_mul] using hta
    · rintro ⟨t₀, ht, hta⟩
      refine ⟨φ t₀, ?_, ?_⟩
      · show φ t₀ ∉ q
        simpa [Ideal.mem_comap] using ht
      · simpa [Ideal.mem_comap, map_mul] using hta
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hf)⟩

end GlobalTheory
end

