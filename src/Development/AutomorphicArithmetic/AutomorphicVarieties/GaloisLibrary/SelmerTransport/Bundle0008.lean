module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0002
public import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.PrincZl
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.princZl :
    ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup ℤ_[l]ˣ), IsClosed (H : Set ℤ_[l]ˣ) → H ≤ KStar.TotallyRealRoots.princ l (qExp l) → H ≠ ⊥ →
      Nonempty (H ≃ₜ* Multiplicative ℤ_[l]) ∧ ∀ u ∈ H, IsOfFinOrder u → u = 1 := by
  intro l _ H hHc hHp hH1
  have tors : ∀ u ∈ H, IsOfFinOrder u → u = 1 := by
    intro u hu hfin
    have hpr := hHp hu
    have hmem : u ∈ CommGroup.torsion ℤ_[l]ˣ := (CommGroup.mem_torsion u).2 hfin
    by_cases h2 : l = 2
    · subst h2
      rcases (GroundTheory.Global.Cyclotomic.mem_torsion_two_iff u).1 hmem with h | h
      · exact h
      · exfalso
        rw [KStar.TotallyRealRoots.mem_princ, h] at hpr
        obtain ⟨c, hc⟩ := hpr
        have hc2 : (2 : ℤ_[2]) * (1 + 2 * c) = 0 := by
          push_cast [qExp] at hc
          linear_combination -hc
        have h2ne : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
        have h1 : (1 : ℤ_[2]) + 2 * c = 0 := (mul_eq_zero.1 hc2).resolve_left h2ne
        have hn : ‖(2 : ℤ_[2]) * c‖ = 1 := by
          rw [show (2 : ℤ_[2]) * c = -1 by linear_combination h1, norm_neg, norm_one]
        have hn2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
          have := PadicInt.norm_p (p := 2)
          norm_num at this ⊢
          exact this
        rw [norm_mul, hn2] at hn
        have := PadicInt.norm_le_one c
        linarith
    · have ht : u ^ GroundTheory.Global.Cyclotomic.torsionExponent l = 1 :=
        (GroundTheory.Global.Cyclotomic.mem_torsion_iff l u).1 hmem
      have hq : qExp l = 1 := by simp [qExp, h2]
      rw [hq] at hpr
      have hte : GroundTheory.Global.Cyclotomic.torsionExponent l = l - 1 := by
        simp [GroundTheory.Global.Cyclotomic.torsionExponent, h2]
      rw [hte] at ht
      have hl := (Fact.out : l.Prime).two_le
      refine KStar.TotallyRealRoots.eq_one_of_mem_princ_one (o := l - 1) ?_ ?_ hpr
      · intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      · rw [mem_rootsOfUnity]
        exact ht
  refine ⟨?_, tors⟩
  classical
  let L : ℤ_[l]ˣ →* Multiplicative ℤ_[l] := GroundTheory.Global.Cyclotomic.padicUnitsLog l
  have hker : L.ker = CommGroup.torsion ℤ_[l]ˣ := GroundTheory.Global.Cyclotomic.ker_padicUnitsLog l
  let f : H → ℤ_[l] := fun h => Multiplicative.toAdd (L h)
  have hfc : Continuous f :=
    (GroundTheory.Global.Cyclotomic.continuous_padicUnitsLog l).comp continuous_subtype_val
  have hmul : ∀ a b : H, f (a * b) = f a + f b := by
    intro a b
    simp [f, L]
  have hpow : ∀ (a : H) (n : ℤ), f (a ^ n) = n * f a := by
    intro a n
    simp [f, L, zsmul_eq_mul]
  have hf1 : f 1 = 0 := by simp [f, L]
  have hinj : Function.Injective f := by
    intro a b hab
    have hL : L a = L b := hab
    have hk : (a : ℤ_[l]ˣ) * (b : ℤ_[l]ˣ)⁻¹ ∈ L.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hL, mul_inv_cancel]
    rw [hker, CommGroup.mem_torsion] at hk
    have := tors _ (H.mul_mem a.2 (H.inv_mem b.2)) hk
    exact Subtype.ext (mul_inv_eq_one.1 this)
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hHc.isCompact
  have hcl : IsClosed (Set.range f) := (isCompact_range hfc).isClosed
  let I : Ideal ℤ_[l] :=
    { carrier := Set.range f
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, hmul a b⟩
      zero_mem' := ⟨1, hf1⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        have hm : Continuous (fun t : ℤ_[l] => t * f a) := continuous_mul_const (f a)
        have hsub := hm.range_subset_closure_image_dense (PadicInt.denseRange_intCast (p := l))
        have himg : (fun t : ℤ_[l] => t * f a) '' Set.range (Int.cast : ℤ → ℤ_[l]) ⊆ Set.range f := by
          rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
          exact ⟨a ^ n, hpow a n⟩
        exact closure_minimal himg hcl (hsub ⟨c, rfl⟩) }
  have hI : ∀ y, y ∈ Set.range f ↔ ∃ c, c * Submodule.IsPrincipal.generator I = y := by
    intro y
    have h : y ∈ I ↔ y ∈ Ideal.span {Submodule.IsPrincipal.generator I} := by
      rw [Ideal.span_singleton_generator]
    rw [Ideal.mem_span_singleton'] at h
    exact h
  set g := Submodule.IsPrincipal.generator I with hgdef
  obtain ⟨a0, ha0⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hH1
  have hg0 : g ≠ 0 := by
    intro hg
    obtain ⟨c, hc⟩ := (hI (f a0)).1 ⟨a0, rfl⟩
    rw [hg, mul_zero, ← hf1] at hc
    exact ha0 (hinj hc).symm
  let e : H → ℤ_[l] := fun h => Classical.choose ((hI (f h)).1 ⟨h, rfl⟩)
  have he : ∀ h, e h * g = f h := fun h => Classical.choose_spec ((hI (f h)).1 ⟨h, rfl⟩)
  have hminj : Function.Injective (fun t : ℤ_[l] => t * g) := mul_left_injective₀ hg0
  have hmemb := ((continuous_mul_const g).isClosedEmbedding hminj).isEmbedding
  have hec : Continuous e := by
    rw [hmemb.continuous_iff]
    have : ((fun t : ℤ_[l] => t * g) ∘ e) = f := funext he
    rw [this]
    exact hfc
  have hemul : ∀ a b : H, e (a * b) = e a + e b := by
    intro a b
    apply hminj
    simp only
    rw [he, add_mul, he, he, hmul]
  have heinj : Function.Injective e := by
    intro a b hab
    apply hinj
    rw [← he, ← he, hab]
  have hesurj : Function.Surjective e := by
    intro c
    obtain ⟨h, hh⟩ := (hI (c * g)).2 ⟨c, rfl⟩
    refine ⟨h, hminj ?_⟩
    simp only
    rw [he, hh]
  let φ : H →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun h => Multiplicative.ofAdd (e h)) (by
      intro a b
      rw [hemul]
      rfl)
  let E : H ≃* Multiplicative ℤ_[l] := MulEquiv.ofBijective φ ⟨heinj, hesurj⟩
  have hEc : Continuous E := hec
  let Φ := Continuous.homeoOfEquivCompactToT2 (f := E.toEquiv) hEc
  exact ⟨{ toMulEquiv := E, continuous_toFun := hEc, continuous_invFun := Φ.symm.continuous }⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RamFinite
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem mem_of_int {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := Ω) (hy.tower_top (A := A))
  exact hz ▸ z.2

open Polynomial in
private theorem key {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : ℤ[X]) {a b : Ω} (ha : a ∈ A) (hb : b ∈ A)
    (fa : aeval a f = 0) (fb : aeval b f = 0) (hab : A.valuation (b - a) < 1)
    (hd : ¬ A.valuation (aeval a (derivative f)) < 1) : b = a := by
  by_contra hne
  apply hd
  obtain ⟨c, hc⟩ := (f.map (algebraMap ℤ A)).binomExpansion ⟨a, ha⟩ (⟨b, hb⟩ - ⟨a, ha⟩)
  have e : ∀ (g : ℤ[X]) (x : A), ((eval x (g.map (algebraMap ℤ A)) : A) : Ω) = aeval (x : Ω) g := fun g x => by
    rw [eval_map_algebraMap]
    exact (aeval_algHom_apply (A.subtype.toIntAlgHom) x g).symm
  rw [add_sub_cancel, derivative_map] at hc
  have h2 := congrArg (fun x : A => (x : Ω)) hc
  push_cast at h2
  simp only [e, fa, fb] at h2
  have h3 : aeval a (derivative f) = -(c : Ω) * (b - a) := by
    apply mul_right_cancel₀ (sub_ne_zero.2 hne)
    linear_combination -h2
  rw [h3, map_mul, Valuation.map_neg]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (A.valuation_le_one c)) hab

open Polynomial in
private theorem fix_int {k E' Ω : Type} [Field k] [NumberField k] [Field E'] [NumberField E'] [Field Ω] [Algebra k Ω]
    [Algebra E' Ω] (α : 𝓞 E') : ∃ d : ℤ, d ≠ 0 ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (d : Ω) < 1 →
      ∀ σ ∈ Ine (F := k) A, σ (algebraMap E' Ω α) = algebraMap E' Ω α := by
  have hi : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hne : aeval α (derivative (minpoly ℤ α)) ≠ 0 := by
    intro h
    have h1 := minpoly.isIntegrallyClosed_dvd hi h
    have h2 := minpoly.natDegree_pos hi
    have h3 : derivative (minpoly ℤ α) ≠ 0 := fun h0 => by
      have := natDegree_eq_zero_of_derivative_eq_zero h0
      omega
    have h4 := natDegree_le_of_dvd h1 h3
    have h5 := natDegree_derivative_lt (p := minpoly ℤ α) (by omega)
    omega
  set δ := aeval α (derivative (minpoly ℤ α)) with hδ
  have hm : (Algebra.norm ℤ δ : 𝓞 E') ∈ Ideal.span {δ} := by
    have := Ideal.absNorm_mem (Ideal.span {δ})
    rw [Ideal.absNorm_span_singleton] at this
    rcases Int.natAbs_eq (Algebra.norm ℤ δ) with h | h
    · rw [h]; simpa using this
    · rw [h]; simpa using this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  refine ⟨Algebra.norm ℤ δ, Algebra.norm_ne_zero_iff.2 hne, fun A hA σ hσ => ?_⟩
  let φ : 𝓞 E' →ₐ[ℤ] Ω := ((algebraMap E' Ω).comp (algebraMap (𝓞 E') E')).toIntAlgHom
  have hφ : ∀ x, φ x ∈ A := fun x => mem_of_int A ((Algebra.IsIntegral.isIntegral x).map φ)
  let ψ : Ω →ₐ[ℤ] Ω := σ.toRingEquiv.toRingHom.toIntAlgHom
  have fa : aeval (φ α) (minpoly ℤ α) = 0 := by rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  change ψ (φ α) = φ α
  refine key A (minpoly ℤ α) (hφ α) (mem_of_int A ((hi.map φ).map ψ)) fa
    (by rw [aeval_algHom_apply, fa, map_zero]) (hσ.2 _ ((A.valuation_le_one_iff _).2 (hφ α))) fun h => hA ?_
  rw [aeval_algHom_apply, ← hδ] at h
  have e : ((Algebra.norm ℤ δ : ℤ) : Ω) = φ t * φ δ := by rw [← map_mul, ht, map_intCast]
  rw [e, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hφ t))) h

open Polynomial in
private theorem fix_root {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {N : ℕ} (hN : N ≠ 0)
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (N : Ω) < 1) {σ : G k Ω} (hσ : σ ∈ Ine (F := k) A) {z : Ω}
    (hz : z ^ N = 1) : σ z = z := by
  have hm : ∀ {y : Ω}, y ^ N = 1 → y ∈ A := fun {y} hy =>
    mem_of_int A (IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (hy ▸ isIntegral_one))
  have hz' : (σ z) ^ N = 1 := by rw [← map_pow, hz, map_one]
  refine key A (X ^ N - 1) (hm hz) (hm hz') (by simp [hz]) (by simp [hz'])
    (hσ.2 _ ((A.valuation_le_one_iff _).2 (hm hz))) fun h => hA ?_
  have e : (N : Ω) = z * aeval z (derivative (X ^ N - 1 : ℤ[X])) := by
    simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_mul, map_natCast, map_pow, aeval_X]
    rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hN), hz, mul_one]
  rw [e, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hm hz))) h

theorem UpperTheory.V.Base.ramFinite :
    ∀ (k E E' Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
      [Algebra k Ω] [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [Algebra k E] [IsScalarTower k E Ω] [IsScalarTower E E' Ω]
      [IsAlgClosure k Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω],
      (∃ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        galOf k E Ω ⊓ Ine (F := k) A ≤ galOf k E' Ω) ∧
      ∀ (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} E E'] (A : ValuationSubring Ω), ¬ A.valuation (N : Ω) < 1 →
        galOf k E Ω ⊓ Ine (F := k) A ≤ galOf k E' Ω := by
  intro k E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  refine ⟨?_, fun N _ hc A hA σ hσ x => ?_⟩
  · choose d hd0 hd using fun α : 𝓞 E' => fix_int (k := k) (Ω := Ω) α
    have hfin : ∀ i, {v : HeightOneSpectrum (𝓞 E) |
        v.asIdeal ∣ Ideal.span {((d (RingOfIntegers.basis E' i) : ℤ) : 𝓞 E)}}.Finite := fun i =>
      Ideal.finite_factors (by simpa using hd0 _)
    refine ⟨(Set.finite_iUnion hfin).toFinset, fun v hv A hA σ hσ x => ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, Ideal.dvd_span_singleton] at hv
    have h : (σ.toRingEquiv.toRingHom.comp (algebraMap E' Ω)).toRatAlgHom.toLinearMap =
        (algebraMap E' Ω).toRatAlgHom.toLinearMap := (integralBasis E').ext fun i => by
      rw [integralBasis_apply]
      refine hd _ A (fun h => hv i ((hA _).1 ?_)) σ hσ.2
      simpa using h
    exact LinearMap.congr_fun h x
  · have hx := hc.adjoin_roots x
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨n, hn, h0, hy⟩ := hy
      obtain rfl : n = N := hn
      exact fix_root h0 A hA hσ.2 (by rw [← map_pow, hy, map_one])
    | algebraMap r => rw [← IsScalarTower.algebraMap_apply]; exact hσ.1 r
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
end

