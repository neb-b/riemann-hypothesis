module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdMulPowEtaleNbhdZeroLocus
section
open GlobalTheory.AffineCurveNbhd

noncomputable section

namespace GlobalTheory.LocDivEtale

open IsLocalRing

theorem span_singleton_eq_maximalIdeal_pow {L : Type} [CommRing L] [IsLocalRing L] [IsNoetherianRing L] (π : L)
    (hπ : maximalIdeal L = Ideal.span {π}) (x : L) (hx : x ≠ 0) :
    ∃ n : ℕ, Ideal.span {x} = maximalIdeal L ^ n := by
  classical
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal L) (maximalIdeal.isMaximal L).ne_top
  have hex : ∃ n, x ∉ maximalIdeal L ^ (n + 1) := by
    by_contra h
    push_neg at h
    apply hx
    have : x ∈ ⨅ i, maximalIdeal L ^ i := by
      rw [Ideal.mem_iInf]; intro i
      cases i with
      | zero => simp
      | succ k => exact h k
    rw [hK] at this; exact this
  obtain ⟨n, hn, hn'⟩ : ∃ n, x ∉ maximalIdeal L ^ (n + 1) ∧ x ∈ maximalIdeal L ^ n := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  clear hex
  refine ⟨n, ?_⟩
  rw [hπ, Ideal.span_singleton_pow] at hn' hn ⊢
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hn'
  have hyu : IsUnit y := by
    by_contra hy'
    apply hn
    have : y ∈ maximalIdeal L := (mem_maximalIdeal _).2 hy'
    rw [hπ] at this
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    rw [Ideal.mem_span_singleton']
    exact ⟨z, by rw [← hy, ← hz]; ring⟩
  rw [← hy]
  exact Ideal.span_singleton_mul_left_unit hyu _

theorem exists_local_uniformizer (B : Type) [CommRing B] [IsDedekindDomain B] (m : Ideal B) [m.IsPrime]
    (hm0 : m ≠ ⊥) : ∃ π ∈ m, ∀ b ∈ m, ∃ t ∉ m, ∃ c : B, t * b = π * c := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime m) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hm0 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime m)
  obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj m.primeCompl ϖ
  simp only at hπt
  have hmax := hϖ.maximalIdeal_eq
  refine ⟨π, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m, ← hπt]
    exact Ideal.mul_mem_right _ _ (hϖ.not_isUnit)
  · intro b hb
    have hb' : algebraMap B (Localization.AtPrime m) b ∈ maximalIdeal (Localization.AtPrime m) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m b).2 hb
    rw [hmax] at hb'
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hb'
    obtain ⟨⟨c, u⟩, hcu⟩ := IsLocalization.surj m.primeCompl z
    simp only at hcu
    have heq : algebraMap B (Localization.AtPrime m) (b * (t * u)) =
        algebraMap B (Localization.AtPrime m) (π * c) := by
      rw [map_mul, map_mul, map_mul, ← hz, ← hπt, ← hcu]; ring
    obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists m.primeCompl (Localization.AtPrime m)).1 heq
    refine ⟨w * (t * u), ?_, w * c, ?_⟩
    · exact (m.primeCompl).mul_mem w.2 ((m.primeCompl).mul_mem t.2 u.2)
    · rw [show (w : B) * (t * u) * b = w * (b * (t * u)) by ring, hw]; ring

theorem exists_dvd_mul_pow : ∀ (B A' : Type) [CommRing B] [IsDedekindDomain B] [CommRing A'] [Algebra B A']
    [Algebra.Etale B A'] (f : B), f ≠ 0 → IsNbhd B A' f → ∀ a ∈ nonZeroDivisors A', ∀ M : Ideal A', M.IsMaximal →
    algebraMap B A' f ∈ M → ∃ s ∉ M, ∃ N : ℕ, a ∣ s * algebraMap B A' f ^ N := by
  intro B A' _ _ _ _ _ f hf hN a ha M hM hfM
  classical
  set m : Ideal B := M.comap (algebraMap B A') with hm_def
  haveI : m.IsPrime := Ideal.comap_isPrime _ _
  have hfm : f ∈ m := hfM
  have hm0 : m ≠ ⊥ := by
    intro h; apply hf
    rw [h] at hfm; exact (Submodule.mem_bot _).1 hfm
  obtain ⟨π, hπm, hπ⟩ := exists_local_uniformizer B m hm0
  let L := Localization.AtPrime M
  haveI : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing B A'
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing M.primeCompl L inferInstance
  let φ : B →+* L := (algebraMap A' L).comp (algebraMap B A')
  have hmem : ∀ b ∈ m, φ b ∈ Ideal.span {φ π} := by
    intro b hb
    obtain ⟨t, ht, c, htc⟩ := hπ b hb
    have hu : IsUnit (φ t) := IsLocalization.map_units L (⟨algebraMap B A' t, ht⟩ : M.primeCompl)
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul, htc, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hmax : maximalIdeal L = Ideal.span {φ π} := by
    apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨b, hb⟩ := hN.1 x
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
      have hbm : b ∈ m := by
        show algebraMap B A' b ∈ M
        have : algebraMap B A' b = x - c * algebraMap B A' f := by rw [hc]; ring
        rw [this]; exact M.sub_mem hx (M.mul_mem_left _ hfM)
      have hx' : x = algebraMap B A' b + c * algebraMap B A' f := by rw [hc]; ring
      show algebraMap A' L x ∈ Ideal.span {φ π}
      rw [hx', map_add (f := _), map_mul]
      exact Ideal.add_mem _ (hmem b hbm) (Ideal.mul_mem_left _ _ (hmem f hfm))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).2 hπm
  have ha0 : algebraMap A' L a ≠ 0 := by
    intro h
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff M.primeCompl L a).1 h
    have : (s : A') = 0 := (mem_nonZeroDivisors_iff.1 ha).2 _ hs
    exact s.2 (this ▸ M.zero_mem)
  obtain ⟨n, hn⟩ := span_singleton_eq_maximalIdeal_pow (φ π) hmax _ ha0
  have hfL : φ f ^ n ∈ Ideal.span {algebraMap A' L a} := by
    rw [hn]; exact Ideal.pow_mem_pow ((IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).2 hfM) n
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hfL
  obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj M.primeCompl z
  simp only at hys
  have heq : algebraMap A' L (algebraMap B A' f ^ n * s) = algebraMap A' L (y * a) := by
    rw [map_mul, map_mul, map_pow, ← hys]
    show φ f ^ n * _ = _
    rw [← hz]; ring
  obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists M.primeCompl L).1 heq
  refine ⟨w * s, (M.primeCompl).mul_mem w.2 s.2, n, w * y, ?_⟩
  rw [show (w : A') * s * algebraMap B A' f ^ n = w * (algebraMap B A' f ^ n * s) by ring, hw]; ring

end GlobalTheory.LocDivEtale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionOfEssentiallyEtaleLocal
section
open TensorProduct IsLocalRing

namespace GlobalTheory

theorem tensorLift_injective_of_flat {R S A K L : Type} [CommRing R] [CommRing S] [IsDomain S]
    [CommRing A] [Field K] [Field L] [Algebra R S] [Module.Flat R S] [Algebra R A] [Algebra R K]
    [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] (i : A →ₐ[R] K)
    (hi : Function.Injective i) (f : K →+* L)
    (hf : ∀ r, f (algebraMap R K r) = algebraMap S L (algebraMap R S r)) (g : A ⊗[R] S →+* L)
    (hg : ∀ a s, g (a ⊗ₜ s) = f (i a) * algebraMap S L s) : Function.Injective g := by
  letI : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  let fK : K →ₐ[R] L := { toRingHom := f, commutes' := hf }
  let H : K ⊗[R] S →ₐ[R] L :=
    Algebra.TensorProduct.lift fK (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  have hH : ∀ k s, H (k ⊗ₜ s) = f k * algebraMap S L s := fun k s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hgH : ∀ x, g x = H (LinearMap.rTensor S i.toLinearMap x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a s => rw [hg, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hH]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  have hloc : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K S 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).mpr (TensorProduct.isBaseChange R S K)
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have hHinj : Function.Injective H := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨s, r⟩, hr⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K S 1) y
    have hs : s = 0 := by
      have h1 : H (r • y) = 0 := by
        rw [Submonoid.smul_def, show H (r.1 • y) = r.1 • H y from H.toLinearMap.map_smul r.1 y, hy, smul_zero]
      rw [hr, TensorProduct.mk_apply, hH, map_one, one_mul] at h1
      exact IsFractionRing.injective S L (h1.trans (map_zero _).symm)
    have ha : algebraMap R K r.1 ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
    have h2 : algebraMap R K r.1 • y = 0 := by
      rw [algebraMap_smul, ← Submonoid.smul_def, hr, hs, TensorProduct.mk_apply, TensorProduct.tmul_zero]
    rw [← one_smul K y, ← inv_mul_cancel₀ ha, mul_smul, h2, smul_zero]
  intro x y hxy
  rw [hgH, hgH] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := S) i.toLinearMap hi (hHinj hxy)

def rangeValuationSubring {B L : Type} [CommRing B] [IsDomain B] [ValuationRing B] [Field L]
    (j : B →+* L) (hj : ∀ x : L, ∃ a b : B, j b ≠ 0 ∧ x = j a / j b) : ValuationSubring L where
  toSubring := j.range
  mem_or_inv_mem' x := by
    obtain ⟨a, b, hb, rfl⟩ := hj x
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · right
      have ha : j a ≠ 0 := fun h => hb (by rw [← hc, map_mul, h, zero_mul])
      exact ⟨c, by rw [inv_div, ← hc, map_mul, mul_div_cancel_left₀ _ ha]⟩
    · left
      exact ⟨c, by rw [← hc, map_mul, mul_div_cancel_left₀ _ hb]⟩

theorem exists_valuationSubring_extend_of_formallyEtale : ∀ {K K' R S : Type} [Field K] [Field K']
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K]
    [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S)
    [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType →
    φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K,
    IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) →
    ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧
      (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧
      (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by
  intro K K' R S _ _ _ _ _ _ _ _ _ _ _ _ φ σ _ hfl het hef hc V hV hRV
  letI : Algebra R S := σ.toAlgebra
  haveI : Module.Flat R S := hfl
  haveI : Algebra.FormallyEtale R S := het
  haveI : Algebra.EssFiniteType R S := hef
  haveI : IsLocalHom (algebraMap R S) := ‹IsLocalHom σ›
  haveI : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  letI : Algebra R V := ((algebraMap R K).codRestrict V hRV).toAlgebra
  letI : Algebra R K' := ((algebraMap S K').comp σ).toAlgebra
  haveI : IsScalarTower R S K' := .of_algebraMap_eq fun _ => rfl
  let fV : V →ₐ[R] K' := { toRingHom := φ.comp V.subtype, commutes' := fun r => RingHom.congr_fun hc r }
  let iV : V →ₐ[R] K := { toRingHom := V.subtype, commutes' := fun _ => rfl }
  let g : V ⊗[R] S →ₐ[R] K' :=
    Algebra.TensorProduct.lift fV (IsScalarTower.toAlgHom R S K') (fun _ _ => Commute.all _ _)
  have hg' : ∀ (a : V) (s : S), g (a ⊗ₜ s) = φ a * algebraMap S K' s := fun a s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hg1 : ∀ s : S, g (1 ⊗ₜ s) = algebraMap S K' s := fun s => by
    rw [hg']; simp
  have hg : Function.Injective g :=
    tensorLift_injective_of_flat (S := S) (L := K') iV Subtype.val_injective φ (RingHom.congr_fun hc) g.toRingHom hg'
  let C := V ⊗[R] S
  haveI : IsDomain C := Function.Injective.isDomain g.toRingHom hg
  obtain ⟨⟨Q, hQ⟩, hQm⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := V) (B := C)
    ⟨maximalIdeal V, inferInstance⟩
  have hQm' : Q.comap (algebraMap V C) = maximalIdeal V := congrArg PrimeSpectrum.asIdeal hQm
  let B := Localization.AtPrime Q
  haveI : Module.Flat V B := Module.Flat.trans V C B
  haveI : Algebra.EssFiniteType V B := .comp V C B
  haveI : Algebra.FormallyEtale V B := .comp V C B
  have hQB : ∀ c : C, IsUnit (algebraMap C B c) ↔ c ∉ Q := fun c =>
    IsLocalization.AtPrime.isUnit_to_map_iff B Q c
  haveI : IsLocalHom (algebraMap V B) := ⟨fun v hv => by
    by_contra hn
    have h1 : algebraMap V C v ∈ Q := by rw [← Ideal.mem_comap, hQm']; exact hn
    rw [IsScalarTower.algebraMap_apply V C B] at hv
    exact (hQB _).mp hv h1⟩
  obtain ⟨_, hB⟩ := exists_isDiscreteValuationRing_of_unramified V B
  have hunit : ∀ y : Q.primeCompl, IsUnit (g.toRingHom y) := fun y => by
    refine Ne.isUnit fun h0 => y.2 ?_
    rw [hg (h0.trans (map_zero g).symm)]
    exact Q.zero_mem
  let j : B →+* K' := IsLocalization.lift (M := Q.primeCompl) (S := B) hunit
  have hjC : ∀ c, j (algebraMap C B c) = g c := IsLocalization.lift_eq (M := Q.primeCompl) (S := B) hunit
  have hj : Function.Injective j := IsLocalization.injective_of_map_algebraMap_zero (M := Q.primeCompl) B j fun x hx => by
    rw [hjC] at hx
    rw [hg (hx.trans (map_zero g).symm), map_zero]
  have hgen : ∀ x : K', ∃ a b : B, j b ≠ 0 ∧ x = j a / j b := fun x => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    refine ⟨algebraMap C B (1 ⊗ₜ a), algebraMap C B (1 ⊗ₜ b), ?_, ?_⟩
    · rw [hjC, hg1]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [hjC, hjC, hg1, hg1]
  let V' := rangeValuationSubring j hgen
  have hVV' : ∀ x ∈ V, φ x ∈ V' := fun x hx =>
    ⟨algebraMap C B (⟨x, hx⟩ ⊗ₜ 1), by rw [hjC, hg', map_one, mul_one]⟩
  let e₀ : B →+* V' := j.codRestrict V' fun b => ⟨b, rfl⟩
  have he₀ : Function.Bijective e₀ :=
    ⟨fun a b h => hj (congrArg Subtype.val h), fun y => by
      obtain ⟨b, hb⟩ := y.2
      exact ⟨b, Subtype.ext hb⟩⟩
  let e : B ≃+* V' := RingEquiv.ofBijective e₀ he₀
  have he : ∀ b, (e b : K') = j b := fun _ => rfl
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  have htQ : algebraMap V C t ∈ Q := by
    rw [← Ideal.mem_comap, hQm']
    exact (mem_maximalIdeal _).mpr ht.not_isUnit
  have htB : ¬ IsUnit (algebraMap C B (algebraMap V C t)) := fun h => (hQB _).mp h htQ
  have hφt : φ t ≠ 0 := by
    rw [map_ne_zero]
    exact fun h => ht.ne_zero (Subtype.ext h)
  have hjt : j (algebraMap C B (algebraMap V C t)) = φ t := by
    rw [hjC, Algebra.TensorProduct.algebraMap_apply, hg']
    simp
  have key : (φ t)⁻¹ ∉ V' := by
    rintro ⟨b, hb⟩
    refine htB (IsUnit.of_mul_eq_one b (hj ?_))
    rw [map_mul, hb, map_one, hjt, mul_inv_cancel₀ hφt]
  refine ⟨V', hVV', ?_, fun b => ⟨algebraMap C B (1 ⊗ₜ b), by rw [hjC, hg1]⟩, ?_, ?_⟩
  · obtain ⟨b, hbm, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (IsDiscreteValuationRing.not_a_field B)
    exact
      { toIsPrincipalIdealRing := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
        toIsLocalRing := inferInstance
        not_a_field' := fun h => by
          have h1 : e b ∈ maximalIdeal V' := fun hu => hbm (by simpa using hu.map e.symm.toRingHom)
          rw [h] at h1
          exact hb0 (e.injective (by simpa using h1)) }
  · intro x hx
    by_contra hxV
    have hinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
    have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨x⁻¹, hinv⟩ : V)) (fun h => inv_ne_zero hx0 (congrArg Subtype.val h)) ht
    have hn' : x⁻¹ = (u : K) * (t : K) ^ n := congrArg Subtype.val hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => hxV ?_)
      have h2 : ((u : V) : K) * (((u⁻¹ : Vˣ) : V) : K) = 1 := by
        exact_mod_cast congrArg Subtype.val u.mul_inv
      have hn0 : x⁻¹ = (u : K) := by rw [hn', h0, pow_zero, mul_one]
      have : x = (((u⁻¹ : Vˣ) : V) : K) := by
        rw [← inv_inv x, hn0]
        exact inv_eq_of_mul_eq_one_right h2
      exact this ▸ Subtype.property _
    apply key
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have : (φ t)⁻¹ = φ ((t ^ m * u : V) : K) * φ x := by
      rw [← map_inv₀, ← map_mul]
      congr 1
      have hu0 : ((u : V) : K) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
      have hx' : x = ((u : K) * (t : K) ^ (m + 1))⁻¹ := by rw [← hn', inv_inv]
      rw [hx']
      push_cast
      field_simp
      ring
    rw [this]
    exact mul_mem (hVV' _ (t ^ m * u : V).2) hx
  · letI : Algebra V V' := (φ.restrict V V' hVV').toAlgebra
    let eA : B ≃ₐ[V] V' := AlgEquiv.ofRingEquiv (f := e) fun v => Subtype.ext (by
      rw [he, IsScalarTower.algebraMap_apply V C B, hjC, Algebra.TensorProduct.algebraMap_apply,
        hg']
      simp
      rfl)
    exact ⟨Algebra.FormallyEtale.of_equiv eA, Algebra.EssFiniteType.of_surjective eA.toAlgHom eA.surjective⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleChartSmoothAlgebraLocalPoint
section
open IsLocalRing

noncomputable section
namespace GlobalTheory.DenseSec

open KaehlerDifferential
open scoped TensorProduct

theorem formallyEtale_of_bijective_kaehler_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P] [CommRing B]
    [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Algebra.FormallySmooth R B]
    (h : Function.Bijective (mapBaseChange R P B)) : Algebra.FormallyEtale P B := by
  have h1 : Subsingleton Ω[B⁄P] := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := map_surjective R P B x
    exact (exact_mapBaseChange_map R P B y).mpr (h.2 y)
  have h2 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have h3 : Algebra.H1Cotangent.δ R P B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B x).mp h3
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨h1, h2⟩

theorem exists_etChart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A),
      (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by
  intro R _ _ A _ _ _ ε
  classical
  let p : Ideal A := (maximalIdeal R).comap ε
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)
  let t : κ → A := fun i => a i - algebraMap R A (ε (a i))
  have hDt : ∀ i, D R A (t i) = D R A (a i) := by intro i; simp [t]
  have hεt : ∀ i, ε (t i) = 0 := by intro i; simp [t]
  let e : (κ →₀ A) →ₗ[A] Ω[A⁄R] :=
    Finsupp.linearCombination A fun i : κ ↦ D R A (t i)
  let l₁ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime p))
  let l₂ : Ω[A⁄R] →ₗ[A] Ω[Localization.AtPrime p⁄R] := map R R A (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb, hDt]
  have heₚ : Function.Bijective eₚ := this ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A _)
  let l₂ₜ : Ω[A⁄R] →ₗ[A] Ω[Localization.Away g⁄R] :=
    map R R A (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  let bB : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R] :=
    .ofRepr (LinearEquiv.ofBijective eₜ' h).symm
  have hbB : ∀ i, bB i = D R _ (algebraMap A (Localization.Away g) (t i)) := by
    intro i
    have h1 : bB i = eₜ' (Finsupp.single i 1) := by
      rfl
    rw [h1]
    trans IsLocalizedModule.map (Submonoid.powers g) l₁ₜ l₂ₜ e <| l₁ₜ <| Finsupp.single i 1
    · simp [eₜ', -IsLocalizedModule.map_apply, l₁ₜ]
    · simp [l₂ₜ, e]
  let eκ : κ ≃ Fin (Nat.card κ) := Finite.equivFin κ
  refine ⟨Nat.card κ, t ∘ eκ.symm, g, fun i => hεt _, ?_, ?_⟩
  · have hg' : ε g ∉ maximalIdeal R := hg
    exact (IsLocalRing.notMem_maximalIdeal.mp hg')
  · unfold EtChart
    letI inst : Algebra (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) :=
      ((algebraMap A (Localization.Away g)).comp (MvPolynomial.aeval (t ∘ eκ.symm)).toRingHom).toAlgebra
    show Algebra.Etale (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g)
    have hsc : IsScalarTower R (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R (Localization.Away g) r =
          algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.C r))
        rw [MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
    have hX : ∀ i, algebraMap (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) (MvPolynomial.X i) =
        algebraMap A (Localization.Away g) (t (eκ.symm i)) := by
      intro i
      change algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X]; rfl
    haveI : Algebra.FormallySmooth A (Localization.Away g) := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers g)
    haveI : Algebra.FormallySmooth R (Localization.Away g) := Algebra.FormallySmooth.comp R A (Localization.Away g)
    let P := MvPolynomial (Fin (Nat.card κ)) R
    let bP : Module.Basis (Fin (Nat.card κ)) (Localization.Away g) ((Localization.Away g) ⊗[P] Ω[P⁄R]) :=
      (mvPolynomialBasis R (Fin (Nat.card κ))).baseChange (Localization.Away g)
    let bB' := bB.reindex eκ
    have hbij : Function.Bijective (mapBaseChange R P (Localization.Away g)) := by
      have : mapBaseChange R P (Localization.Away g) = (bP.equiv bB' (Equiv.refl _)).toLinearMap := by
        refine bP.ext fun i => ?_
        rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
        simp [bP, bB', hbB, ← hX, P]
      rw [this]
      exact (bP.equiv bB' (Equiv.refl _)).bijective
    haveI : Algebra.FormallyEtale P (Localization.Away g) :=
      formallyEtale_of_bijective_kaehler_mapBaseChange R P (Localization.Away g) hbij
    haveI : Algebra.FinitePresentation R (Localization.Away g) :=
      Algebra.FinitePresentation.trans R A (Localization.Away g)
    haveI : Algebra.FinitePresentation P (Localization.Away g) :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R P (Localization.Away g)
    exact ⟨inferInstance, inferInstance⟩
end GlobalTheory.DenseSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicUnitMultipleFractionRingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubic_unit_multiple_fractionRing : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (κ₀ : X → (FractionRing R)ˣ), (∀ a, ∃ u : Rˣ, ((κ₀ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) → (∀ a a' b, ∃ u : Rˣ, ((κ₀ (a + a' + b) * κ₀ a * κ₀ a' * κ₀ b : (FractionRing R)ˣ) : FractionRing R) = ((κ₀ (a + a') * κ₀ (a + b) * κ₀ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) → ∃ κ : X → (FractionRing R)ˣ, (∀ a, κ (-a) = κ a) ∧ (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) ∧ ∀ a, ∃ u : Rˣ, ((κ a : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  first | exact @GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple | exact GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple | (intros; apply GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensModNsmulOfFgNumberFieldStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gens_mod_nsmul_of_fg_numberField : ∀ (E : Type) [Field E] [NumberField E] (r M : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → Λ.FG → ∃ e : Fin r → Fin r → E, (∀ i, e i ∈ Λ) ∧ ∀ x ∈ Λ, ∃ o : Fin r → 𝓞 E, ∃ y ∈ Λ, x = ∑ i, o i • e i + M • y := by
  first | exact @GlobalTheory.GensModNsmul.exists_gens_mod_nsmul | exact GlobalTheory.GensModNsmul.exists_gens_mod_nsmul | (intros; apply GlobalTheory.GensModNsmul.exists_gens_mod_nsmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfCompatibleStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheafData_of_compatible_ideals : ∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) → (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)), (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W), (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') → ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W := by
  first | (exact @GlobalTheory.AffineIdealGlue.exists_idealSheafData_of_compatible) | (exact GlobalTheory.AffineIdealGlue.exists_idealSheafData_of_compatible) | (intros; apply GlobalTheory.AffineIdealGlue.exists_idealSheafData_of_compatible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftAdicCompleteFreeAlgebraStatement
section
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_lift_adicComplete_free_algebra : ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Free A Λ] [Module.Finite A Λ] (x : Λ), x * x - x ∈ I • (⊤ : Submodule A Λ) → ∃ e : Λ, IsIdempotentElem e ∧ e - x ∈ I • (⊤ : Submodule A Λ) := by
  first | (exact @GlobalTheory.IdemNewton.exists_idem) | (exact GlobalTheory.IdemNewton.exists_idem) | (intros; apply GlobalTheory.IdemNewton.exists_idem  <;> assumption)
end

