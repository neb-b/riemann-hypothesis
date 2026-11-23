module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsPrimeDegree
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

private theorem pIdx_range_eq (p : ℕ) {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    pIdx p j.range = (pows p (⊤ : Subgroup U)).index := by
  unfold pIdx
  rw [← Subgroup.index_comap]
  congr 1
  ext x
  simp only [pows, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_comap,
    powMonoidHom_apply, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨y, hj (by simpa using h)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨j y, ⟨y, rfl⟩, by simp⟩

private theorem index_pows_top_eq (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    (pows p (⊤ : Subgroup U)).index = pIdx p U := by
  rw [← pIdx_range_eq p U.subtype U.subtype_injective, Subgroup.range_subtype]

private theorem pIdx_top_eq (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pIdx p (⊤ : Subgroup U) = pIdx p U := by
  rw [← index_pows_top_eq p U, pIdx, Subgroup.relIndex_top_right]

private theorem pTor_range_eq (p : ℕ) {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    pTor p j.range = pTor p (⊤ : Subgroup U) := by
  unfold pTor
  symm
  refine Nat.card_eq_of_bijective
    (fun x => ⟨j x.1, ⟨x.1, rfl⟩, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext (hj (congrArg Subtype.val h))
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨⟨y, Subgroup.mem_top _, hj (by rw [map_pow, h, map_one])⟩, rfl⟩

private theorem pTor_top_eq (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pTor p (⊤ : Subgroup U) = pTor p U := by
  rw [← pTor_range_eq p U.subtype U.subtype_injective, Subgroup.range_subtype]

private theorem arith_first_ineq (p m n c e r t : ℕ) (hp : p.Prime) (hd : m ∣ n) (hn : n ≠ 0)
    (h : n ^ (p - 1) * p ^ (e + p * r) * p ^ p = 1 ^ (p - 1) * p * (p ^ (c + r)) ^ p)
    (hs : p * c ≤ e + (p - 1) * t) : m ≠ 0 ∧ p * m ≤ p ^ t := by
  refine ⟨fun h0 => hn (by subst h0; simpa using hd), ?_⟩
  have hmn : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  have hq : q ≠ 0 := by have := hp.two_le; omega
  simp only [Nat.add_sub_cancel, one_pow, one_mul] at h hs
  set p := q + 1 with hpq
  have hpos : 0 < p := hp.pos
  have h1 : (p * p ^ (e + p * r)) * (p * n) ^ q ≤ (p * p ^ (e + p * r)) * (p ^ t) ^ q := by
    calc (p * p ^ (e + p * r)) * (p * n) ^ q
        = n ^ q * p ^ (e + p * r) * p ^ (q + 1) := by rw [mul_pow, pow_succ]; ring
      _ = p * (p ^ (c + r)) ^ p := h
      _ = p * p ^ (p * c + p * r) := by rw [← pow_mul]; congr 2; ring
      _ ≤ p * p ^ (e + q * t + p * r) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos (by omega))
      _ = (p * p ^ (e + p * r)) * (p ^ t) ^ q := by
        rw [← pow_mul, mul_assoc, ← pow_add]; congr 2; ring
  have h2 : (p * n) ^ q ≤ (p ^ t) ^ q := Nat.le_of_mul_le_mul_left h1 (by positivity)
  have h3 : p * n ≤ p ^ t := (Nat.pow_le_pow_iff_left hq).1 h2
  exact le_trans (Nat.mul_le_mul_left _ hmn) h3

theorem first_inequality_sUnits_prime :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ)
      (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S →
      δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) →
      (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧
        p * (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ p ^ tNon p F δ S := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns
  obtain ⟨E, _, _, θ, σ, hq⟩ := exists_isKum p F ζ δ hp hζ hns
  obtain ⟨hfd, hrk, hper, hfix, -, -, hnorm⟩ := _root_.GlobalTheory.CNorm.kummer_basic p F E ζ δ θ σ hq
  obtain ⟨-, -, hgal, -⟩ := kummer_galois p F E ζ δ θ σ hq
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : IsTotallyComplex E := isTotallyComplex_of_algebra F E
  obtain ⟨SE, hSE⟩ := (places_over F E).1 S
  obtain ⟨hup, hσ⟩ := sUnits_over_and_aut F E S SE hSE
  have h90 := _root_.GlobalTheory.CNorm.hilbert90_sUnits_kummer p F E ζ δ θ σ hq S SE hSE hS ((mem_sUnits F S δ).1 hδ)
  have hcf := _root_.GlobalTheory.CNorm.prime_mul_card_le_card_over p F E ζ δ θ σ hq S SE hSE
  have hζE : IsPrimitiveRoot (algebraMap F E ζ) p := hζ.map_of_injective (algebraMap F E).injective
  obtain ⟨htF, hiF⟩ := pTor_pIdx_sUnits p F ζ S hp hζ
  obtain ⟨htE, hiE⟩ := pTor_pIdx_sUnits p E _ SE hp hζE
  have hinf : Fintype.card (InfinitePlace E) = p * Fintype.card (InfinitePlace F) := by
    have h1 := IsTotallyComplex.finrank F
    have h2 := IsTotallyComplex.finrank E
    have h3 := Module.finrank_mul_finrank ℚ F E
    have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h5 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] at h4 h5
    rw [h4, h5]
    rw [h1, h2, hrk] at h3
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    rw [← h3]; ring
  let τ : sUnits E SE →* sUnits E SE :=
    ((Units.map (σ : E →* E)).comp (sUnits E SE).subtype).codRestrict _ (fun y => hσ σ y y.2)
  have hτ : ∀ y : sUnits E SE, (((τ y : sUnits E SE) : Eˣ) : E) = σ ((y : Eˣ) : E) :=
    fun _ => rfl
  have hτi : ∀ (i : ℕ) (y : sUnits E SE),
      (((τ^[i] y : sUnits E SE) : Eˣ) : E) = σ^[i] ((y : Eˣ) : E) := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih => intro y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, ih]
  have hN : ∀ y : sUnits E SE, (((nrm τ p y : sUnits E SE) : Eˣ) : E) =
      ∏ i ∈ Finset.range p, σ^[i] ((y : Eˣ) : E) := by
    intro y
    rw [nrm_apply]
    change ((sUnits E SE).subtype (∏ i ∈ Finset.range p, τ^[i] y) : E) = _
    rw [map_prod, Units.coe_prod]
    exact Finset.prod_congr rfl (fun i _ => hτi i y)
  let j : sUnits F S →* sUnits E SE :=
    ((Units.map (algebraMap F E : F →* E)).comp (sUnits F S).subtype).codRestrict _
      (fun y => (hup y).2 y.2)
  have hj : ∀ y : sUnits F S, (((j y : sUnits E SE) : Eˣ) : E) = algebraMap F E ((y : Fˣ) : F) :=
    fun _ => rfl
  have hext : ∀ a b : sUnits E SE, ((a : Eˣ) : E) = ((b : Eˣ) : E) → a = b :=
    fun a b h => Subtype.ext (Units.ext h)
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    apply (algebraMap F E).injective
    rw [← hj, ← hj, h]
  have hrange : fix τ = j.range := by
    ext y
    rw [MonoidHom.mem_range, mem_fix]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := hfix ((y : Eˣ) : E) (by rw [← hτ, h])
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact (y : Eˣ).ne_zero (by simpa using ha)
      have hy : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = y :=
        Units.ext (by simpa using ha.symm)
      refine ⟨⟨Units.mk0 a ha0, (hup _).1 (hy ▸ y.2)⟩, hext _ _ ?_⟩
      rw [hj, ha]; rfl
    · rintro ⟨x, rfl⟩
      apply hext
      rw [hτ, hj, AlgEquiv.commutes]
  have hone : (dif τ).range.relIndex (nrm τ p).ker = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro a ha
    have h1 : ∏ i ∈ Finset.range p, σ^[i] ((a : Eˣ) : E) = 1 := by
      rw [← hN, MonoidHom.mem_ker.1 ha]; rfl
    obtain ⟨y, hy, h⟩ := h90 a a.2 h1
    refine ⟨⟨y, hy⟩, hext _ _ ?_⟩
    rw [h, dif_apply, Subgroup.coe_div, Units.val_div_eq_div_val, hτ]
  obtain ⟨h0, -, -, -, key⟩ := _root_.GlobalTheory.CNorm.herbrand_prime_order p (sUnits E SE) τ hp
    (fun a => hext _ _ (by rw [hτi, hper]))
    (by rw [pIdx_top_eq, hiE]; exact pow_ne_zero _ hp.ne_zero)
    (by rw [pTor_top_eq, htE]; exact hp.ne_zero)
  rw [hone, hrange, pIdx_range_eq p j hjinj, pTor_range_eq p j hjinj, index_pows_top_eq,
    pIdx_top_eq, pTor_top_eq, pTor_top_eq, htF, htE, hiF, hiE, hinf,
    ← Subgroup.index_comap] at key
  rw [hrange, ← Subgroup.index_comap] at h0
  refine arith_first_ineq p _ _ _ _ _ _ hp ?_ h0 key hcf
  apply Subgroup.index_dvd_of_le
  rintro x ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, hnorm]
  exact ⟨((y : Eˣ) : E), by rw [← hN, hy, hj]⟩

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatComponentMemRatPolysVanishingOnMatrixSet
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_component_mem_vanI_of_mem_span {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (l : ℂ →ₗ[ℚ] ℚ) (f : MvPolynomial (ι × ι) ℂ)
    (hf : f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ)) :
    ∀ c : ℂ, ∃ f' ∈ vanI Γ, ∀ m, AddMonoidAlgebra.coeff f' m = l (c * AddMonoidAlgebra.coeff f m) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    intro c
    have hvan : l c • p ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (l c • p) g = 0
      intro g hg
      have h0 : ev p g = 0 := hp g hg
      simp only [ev] at h0 ⊢
      rw [map_smul, h0, smul_zero]
    refine ⟨l c • p, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, mul_comm c,
      ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  | zero =>
    intro c
    have hvan : (0 : MvPolynomial (ι × ι) ℚ) ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (0 : MvPolynomial (ι × ι) ℚ) g = 0
      intro g _
      simp [ev]
    exact ⟨0, hvan, fun m => by simp⟩
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨a, ha, ha'⟩ := hx c
    obtain ⟨b, hb, hb'⟩ := hy c
    have hvan : a + b ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (a + b) g = 0
      intro g hg
      have h1 : ev a g = 0 := ha g hg
      have h2 : ev b g = 0 := hb g hg
      simp only [ev] at h1 h2 ⊢
      rw [map_add (f := _), h1, h2, add_zero]
    refine ⟨a + b, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_add, ha', hb', MvPolynomial.coeff_add, mul_add, map_add (f := _)]
  | smul a x _ hx =>
    intro c
    obtain ⟨f', hf', h'⟩ := hx (c * a)
    exact ⟨f', hf', fun m => by rw [h', MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]⟩

theorem component_mem_vanI : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, AddMonoidAlgebra.coeff f' m = l (AddMonoidAlgebra.coeff f m)) → f' ∈ vanI Γ := by
  intro ι _ _ Γ hΓ f hf l f' hf'
  obtain ⟨p, hp, hpc⟩ :=
    exists_component_mem_vanI_of_mem_span Γ l f (_root_.GlobalTheory.ClassFin.mem_span_vanI_of_vanish ι Γ hΓ f hf) 1
  have hfp : f' = p := by
    ext m
    rw [hf', hpc, one_mul]
  exact hfp ▸ hp

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowLeIndexLocalNormsSqrtExtension
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem norm_of_isSquare_mul {L : Type} [Field L] {x y δ : L} (hx : x ≠ 0)
    (h : IsSquare (x * y)) (hn : ∃ a b : L, x = a ^ 2 - δ * b ^ 2) :
    ∃ a b : L, y = a ^ 2 - δ * b ^ 2 := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨a, b, hab⟩ := hn
  refine ⟨a * s / x, b * s / x, ?_⟩
  field_simp
  linear_combination x * hs + s ^ 2 * hab

theorem mem_normSub_real_of_pos {F : Type} [Field F] (σ : F →+* ℝ) (δ : F) (x : Fˣ)
    (h : 0 < σ (x : F)) : x ∈ normSub σ δ :=
  ⟨Real.sqrt (σ (x : F)), 0, by rw [Real.sq_sqrt h.le]; ring⟩

theorem locSq_le_locNorm_of_delta (F : Type) [Field F] [NumberField F] (δ : F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : locSq F S ≤ locNorm F δ S := by
  unfold locSq locNorm finSq
  exact inf_le_inf (iInf_mono fun v => iInf_mono fun _ => sqSub_le_normSub _ _)
    (iInf_mono fun σ => sqSub_le_normSub _ _)

theorem two_pow_le_index_locNorm :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))),
      δ ≠ 0 → (locNorm F δ S).index ≠ 0 ∧
        2 ^ (tFin F δ S + tReal F δ) ≤ (locNorm F δ S).index := by
  intro F _ _ δ S hδ
  classical
  have h0 : (locNorm F δ S).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (_root_.GlobalTheory.QNorm.index_locSq_le F S).1
      (Subgroup.index_dvd_of_le (locSq_le_locNorm_of_delta F δ S))
  refine ⟨h0, ?_⟩
  set A : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ S ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) δ)} with hA
  set B : Set (F →+* ℝ) := {σ | σ δ < 0} with hB
  have hAf : A.Finite := S.finite_toSet.subset fun v hv => hv.1
  have hBf : B.Finite := Set.toFinite _
  letI : Fintype A := hAf.fintype
  letI : Fintype B := hBf.fintype
  let K : A ⊕ B → Subgroup Fˣ := Sum.elim
    (fun v => normSub (algebraMap F (v.1.adicCompletion F)) δ) (fun σ => normSub σ.1 δ)
  have hle : locNorm F δ S ≤ ⨅ i, K i := by
    refine le_iInf ?_
    rintro (v | σ)
    · exact inf_le_left.trans (iInf₂_le v.1 v.2.1)
    · exact inf_le_right.trans (iInf_le _ σ.1)
  have hdvd := Subgroup.index_dvd_of_le hle
  have hcard : Fintype.card (A ⊕ B) = tFin F δ S + tReal F δ := by
    rw [Fintype.card_sum, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rfl
  rw [← hcard]
  refine le_trans (_root_.GlobalTheory.QNorm.two_pow_card_le_index_iInf Fˣ (A ⊕ B) K ?_ (ne_zero_of_dvd_ne_zero h0 hdvd))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)
  rintro (v | σ)
  · obtain ⟨y, hy0, hy⟩ := _root_.GlobalTheory.QNorm.exists_local_nonnorm F v.1 (algebraMap F _ δ) (by simpa using hδ) v.2.2
    obtain ⟨x, hx0, hxv, hxσ⟩ := _root_.GlobalTheory.QNorm.exists_approx_mod_squares F S
      (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1 y)
      (fun _ => 1) (by
        intro w
        by_cases hw : w = v.1
        · subst hw; simpa using hy0
        · simp [Function.update_of_ne hw]) (by simp)
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · intro hm
      have h1 := hxv v.1 v.2.1
      rw [Function.update_self] at h1
      exact hy (norm_of_isSquare_mul (by simpa using hx0) h1 hm)
    · rintro (w | τ) hj
      · have hw : w.1 ≠ v.1 := fun h => hj (congrArg Sum.inl (Subtype.ext h))
        have h1 := hxv w.1 w.2.1
        rw [Function.update_of_ne hw, mul_one] at h1
        exact sqSub_le_normSub _ _ h1
      · exact mem_normSub_real_of_pos _ _ _ (by simpa using hxσ τ.1)
  · obtain ⟨x, hx0, hxv, hxσ⟩ := _root_.GlobalTheory.QNorm.exists_approx_mod_squares F S (fun _ => 1)
      (fun τ => if τ = σ.1 then -1 else 1) (by simp) (by
        intro τ
        split_ifs <;> simp)
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · rintro ⟨a, b, hab⟩
      have h1 := hxσ σ.1
      have h2 : σ.1 δ < 0 := σ.2
      simp only [if_true] at h1
      have h3 : σ.1 x = a ^ 2 - σ.1 δ * b ^ 2 := hab
      nlinarith [sq_nonneg a, mul_nonneg (neg_nonneg.2 h2.le) (sq_nonneg b)]
    · rintro (w | τ) hj
      · have h1 := hxv w.1 w.2.1
        rw [mul_one] at h1
        exact sqSub_le_normSub _ _ h1
      · have hw : τ.1 ≠ σ.1 := fun h => hj (congrArg Sum.inr (Subtype.ext h))
        exact mem_normSub_real_of_pos _ _ _ (by simpa [hw] using hxσ τ.1)

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryEqQuasiReflectionMulTransvections
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Gen

end GlobalTheory.UTrans.Gen

namespace GlobalTheory.UTrans

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private theorem refl_eq_tv_sub_one_div_hf {F E : Type} [Field F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) :
    _root_.GlobalTheory.UnRep.refl c G x u =
      _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x ((u - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, _root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec,
    _root_.GlobalTheory.UTrans.Model.tv_mulVec]
  change v + ((u - 1) * _root_.GlobalTheory.UTrans.hf (c : E →+* E) G v x /
    _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) • x = _
  congr 2
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private theorem det_refl_eq_of_hermE_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E)
    (hx : _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0) :
    (_root_.GlobalTheory.UnRep.refl c G x u).det = u := by
  unfold _root_.GlobalTheory.UnRep.refl
  have hw : (G.mulVec fun b => c (x b)) ⬝ᵥ x = _root_.GlobalTheory.UnRep.hermE c G x x :=
    (_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot c G x x).symm
  have hmat : ((u - 1) / _root_.GlobalTheory.UnRep.hermE c G x x) •
      Matrix.vecMulVec x (G.mulVec fun b => c (x b)) =
      Matrix.replicateCol Unit (((u - 1) / _root_.GlobalTheory.UnRep.hermE c G x x) • x) *
        Matrix.replicateRow Unit (G.mulVec fun b => c (x b)) := by
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, mul_assoc]
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hw, smul_eq_mul]
  field_simp
  ring


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.UTrans.isU_eq_tv_mul_tvGen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ _root_.GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ γ, _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G γ → (∀ x, _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G, γ = _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x ((γ.det - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) * m) ∧ (γ.det = 1 → γ ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G) := by
  intro F E _ _ _ _ _ c n G hG hiso γ hγ
  have hG' : _root_.GlobalTheory.UnRep.IsHermForm c G := by
    refine ⟨hG.invol, ?_, hG.herm,
      hG.det_ne⟩
    intro h1
    obtain ⟨a, ha⟩ := hG.ne_id
    apply ha
    rw [h1]
    rfl
  have hγ' : _root_.GlobalTheory.UnRep.IsUnE c G γ := fun v w => hγ v w
  obtain ⟨l, hl, hγl⟩ := _root_.GlobalTheory.UnRep.isUnE_eq_prod_refl F E c n G hG' γ hγ'
  have hnorm := (_root_.GlobalTheory.UTrans.tvGen_normal E n (c : E →+* E) G hG).2
  have main : ∀ x, _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 →
      ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G,
        γ = _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x
          ((γ.det - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) * m := by
    intro x hx
    have hx' : _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0 := hx
    obtain ⟨_, _, hmul, hunit⟩ := _root_.GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG' x hx'

    have key : ∀ l' : List ((Fin n → E) × E),
        (∀ p ∈ l', _root_.GlobalTheory.UnRep.hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) →
        ∃ M ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G, ∃ U : E, U * c U = 1 ∧
          (l'.map fun p => _root_.GlobalTheory.UnRep.refl c G p.1 p.2).prod =
            M * _root_.GlobalTheory.UnRep.refl c G x U := by
      intro l' hl'
      induction l' with
      | nil =>
        refine ⟨1, Submonoid.one_mem _, 1, by simp, ?_⟩
        obtain ⟨_, h1, _, _⟩ := _root_.GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG' x hx'
        simp [h1]
      | cons p l' ih =>
        obtain ⟨M, hM, U, hU, hprod⟩ := ih fun q hq => hl' q (List.mem_cons_of_mem _ hq)
        obtain ⟨hp1, hp2⟩ := hl' p List.mem_cons_self
        obtain ⟨m₁, hm₁, hq₁⟩ := _root_.GlobalTheory.UTrans.quasiReflection_eq_tvGen_mul E n (c : E →+* E) G hG hiso
          p.1 x p.2 hp1 hx hp2
        obtain ⟨M', hM', hcomm, _⟩ := (hnorm M hM).2.2.2 _ ((hunit p.2 hp2) : _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G _)
        refine ⟨m₁ * M', Submonoid.mul_mem _ hm₁ hM', p.2 * U, ?_, ?_⟩
        · rw [map_mul]
          calc p.2 * U * (c p.2 * c U) = (p.2 * c p.2) * (U * c U) := by ring
            _ = 1 := by rw [hp2, hU, one_mul]
        · rw [List.map_cons, List.prod_cons, hprod, refl_eq_tv_sub_one_div_hf, hq₁,
            ← refl_eq_tv_sub_one_div_hf, ← hmul]
          calc m₁ * _root_.GlobalTheory.UnRep.refl c G x p.2 * (M * _root_.GlobalTheory.UnRep.refl c G x U)
              = m₁ * (_root_.GlobalTheory.UnRep.refl c G x p.2 * M) * _root_.GlobalTheory.UnRep.refl c G x U := by
                simp only [mul_assoc]
            _ = m₁ * (M' * _root_.GlobalTheory.UnRep.refl c G x p.2) * _root_.GlobalTheory.UnRep.refl c G x U := by
                rw [hcomm]
            _ = _ := by simp only [mul_assoc]
    obtain ⟨M, hM, U, hU, hprod⟩ := key l hl
    have hγM : γ = M * _root_.GlobalTheory.UnRep.refl c G x U := hγl.trans hprod
    have hdet : γ.det = U := by
      rw [hγM, Matrix.det_mul, (hnorm M hM).2.1, one_mul, det_refl_eq_of_hermE_ne_zero c G x U hx']
    obtain ⟨_, _, _, m'', hm'', hcomm⟩ := (hnorm M hM).2.2.2 _ ((hunit U hU) : _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G _)
    refine ⟨m'', hm'', ?_⟩
    rw [hdet, hγM, hcomm, refl_eq_tv_sub_one_div_hf]
  refine ⟨main, fun h1 => ?_⟩
  obtain ⟨z, hz, _⟩ := hiso
  obtain ⟨i, -⟩ := Function.ne_iff.mp hz
  obtain ⟨y, hyy, -, -⟩ := _root_.GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis F E c n G hG'
  obtain ⟨m, hm, hγm⟩ := main (y i) (hyy i)
  have h0 : _root_.GlobalTheory.UTrans.tv (c : E →+* E) G (y i) 0 = 1 := by
    unfold _root_.GlobalTheory.UTrans.tv
    ext a b
    simp
  rw [h1, sub_self, zero_div, h0, one_mul] at hγm
  rw [hγm]
  exact hm

end GlobalTheory.UTrans
end

