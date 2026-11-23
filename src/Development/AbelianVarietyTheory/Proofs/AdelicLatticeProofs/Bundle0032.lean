module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationUnramifiedOfUnit
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRational
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.GaloisDescent

private theorem exists_rational_support_subset_of_galois_stable {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) :
    ∀ n : ℕ, ∀ w ∈ W, w ≠ 0 → (b.repr w).support.card = n →
      ∃ u ∈ W, u ≠ 0 ∧ (∀ k, ∃ q : ℚ, b.repr u k = q) ∧
        (b.repr u).support ⊆ (b.repr w).support := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hw0 hcard
  have hrepr0 : b.repr w ≠ 0 := fun h => hw0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨k₀, hk₀⟩ := Finsupp.support_nonempty_iff.mpr hrepr0
  have hk₀' : b.repr w k₀ ≠ 0 := Finsupp.mem_support_iff.mp hk₀

  have hvW : (b.repr w k₀)⁻¹ • w ∈ W := W.smul_mem _ hw
  have hvk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w) k = (b.repr w k₀)⁻¹ * b.repr w k := by
    intro k; simp
  have hv1 : b.repr ((b.repr w k₀)⁻¹ • w) k₀ = 1 := by
    rw [hvk, inv_mul_cancel₀ hk₀']
  by_cases hfix : ∀ σ : ℂ ≃+* ℂ, ∀ k,
      σ (b.repr ((b.repr w k₀)⁻¹ • w) k) = b.repr ((b.repr w k₀)⁻¹ • w) k
  ·
    refine ⟨_, hvW, ?_, fun k => _root_.GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed _ (fun σ => hfix σ k), ?_⟩
    · intro h0
      rw [h0, map_zero, Finsupp.zero_apply] at hv1
      exact zero_ne_one hv1
    · intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      rw [hvk] at hk
      exact right_ne_zero_of_mul hk
  ·
    push Not at hfix
    obtain ⟨σ, k₁, hk₁⟩ := hfix
    obtain ⟨v', hv'W, hv'⟩ := hW σ _ hvW
    have hdW : (b.repr w k₀)⁻¹ • w - v' ∈ W := W.sub_mem hvW hv'W
    have hdk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w - v') k =
        b.repr ((b.repr w k₀)⁻¹ • w) k - σ (b.repr ((b.repr w k₀)⁻¹ • w) k) := by
      intro k; rw [map_sub, Finsupp.sub_apply, hv']
    have hd0 : (b.repr w k₀)⁻¹ • w - v' ≠ 0 := by
      intro h
      have := hdk k₁
      rw [h, map_zero, Finsupp.zero_apply] at this
      exact hk₁ (sub_eq_zero.mp this.symm).symm
    have hsub : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support ⊆ (b.repr w).support := by
      intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      intro hwk
      apply hk
      rw [hdk, hvk, hwk]
      simp
    have hk₀d : k₀ ∉ (b.repr ((b.repr w k₀)⁻¹ • w - v')).support := by
      rw [Finsupp.mem_support_iff, not_not, hdk, hv1, map_one, sub_self]
    have hlt : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support.card < n := by
      rw [← hcard]
      exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k₀, hk₀, hk₀d⟩)
    obtain ⟨u, huW, hu0, hurat, husub⟩ := ih _ hlt _ hdW hd0 rfl
    exact ⟨u, huW, hu0, hurat, husub.trans hsub⟩

theorem exists_rational_support_subset {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) (n : ℕ) :
    ∀ w ∈ W, w ≠ 0 → (b.repr w).support.card = n →
      ∃ u ∈ W, u ≠ 0 ∧ (∀ k, ∃ q : ℚ, b.repr u k = q) ∧
        (b.repr u).support ⊆ (b.repr w).support :=
  fun w hw hw0 hcard => exists_rational_support_subset_of_galois_stable b W hW n w hw hw0 hcard

private theorem mem_span_rational_of_galois_stable_of_support_card {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) :
    ∀ n : ℕ, ∀ w ∈ W, (b.repr w).support.card = n →
      w ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hcard
  by_cases hw0 : w = 0
  · rw [hw0]; exact Submodule.zero_mem _
  obtain ⟨u, huW, hu0, hurat, husub⟩ :=
    exists_rational_support_subset b W hW n w hw hw0 hcard
  have hru : b.repr u ≠ 0 := fun h => hu0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hru
  have huk : b.repr u k ≠ 0 := Finsupp.mem_support_iff.mp hk

  have hdk : ∀ j, b.repr (w - (b.repr w k / b.repr u k) • u) j =
      b.repr w j - (b.repr w k / b.repr u k) * b.repr u j := by
    intro j; simp
  have hsub : (b.repr (w - (b.repr w k / b.repr u k) • u)).support ⊆ (b.repr w).support := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj ⊢
    intro hwj
    apply hj
    have huj : b.repr u j = 0 := by
      by_contra h
      exact Finsupp.mem_support_iff.mp (husub (Finsupp.mem_support_iff.mpr h)) hwj
    rw [hdk, hwj, huj]
    simp
  have hkout : k ∉ (b.repr (w - (b.repr w k / b.repr u k) • u)).support := by
    rw [Finsupp.mem_support_iff, not_not, hdk, div_mul_cancel₀ _ huk, sub_self]
  have hlt : (b.repr (w - (b.repr w k / b.repr u k) • u)).support.card < n := by
    rw [← hcard]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k, husub hk, hkout⟩)
  have h1 := ih _ hlt _ (W.sub_mem hw (W.smul_mem _ huW)) rfl
  have h2 : u ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} :=
    Submodule.subset_span ⟨huW, hurat⟩
  have h3 := Submodule.add_mem _ h1 (Submodule.smul_mem _ (b.repr w k / b.repr u k) h2)
  rwa [sub_add_cancel] at h3

theorem le_span_rational :
    ∀ (V κ : Type) [AddCommGroup V] [Module ℂ V] (b : Module.Basis κ ℂ V) (W : Submodule ℂ V), (∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) → W ≤ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  intro V κ _ _ b W hW w hw
  exact mem_span_rational_of_galois_stable_of_support_card b W hW _ w hw rfl

end GlobalTheory.ClassFin.GaloisDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HerbrandPrimeOrder
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem herbPhi_arith (q h0 h1 a t bI bT cI cT i c : ℕ) (hi : i ≠ 0) (hcT : cT ≠ 0)
    (e1 : a * bT * cT = bI * cI * t) (e2 : cI * c ^ q = i ^ q * cT)
    (e3 : h0 * i * bT = bI * h1 * c) :
    h0 ^ q * a * bT ^ (q + 1) = h1 ^ q * t * bI ^ (q + 1) := by
  have hne : i ^ q * cT ≠ 0 := mul_ne_zero (pow_ne_zero _ hi) hcT
  apply mul_right_cancel₀ hne
  calc h0 ^ q * a * bT ^ (q + 1) * (i ^ q * cT) = (h0 * i * bT) ^ q * (a * bT * cT) := by ring
    _ = (bI * h1 * c) ^ q * (bI * cI * t) := by rw [e1, e3]
    _ = h1 ^ q * t * bI ^ (q + 1) * (cI * c ^ q) := by ring
    _ = _ := by rw [e2]

theorem herbPhi_nrm_dif {A : Type} [CommGroup A] (σ : A →* A) (n : ℕ) (a : A) :
    nrm σ n (dif σ a) = σ^[n] a / a := by
  induction n with
  | zero => simp [nrm_apply]
  | succ n ih =>
    rw [nrm_apply] at ih ⊢
    rw [Finset.prod_range_succ, ih, dif_apply, iterate_map_div, Function.iterate_succ_apply,
      mul_comm, div_mul_div_cancel]

theorem herbPhi_stable (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A) (hp : p.Prime)
    (C : Subgroup A) (hst : ∀ x ∈ C, σ x ∈ C) (hn : ∀ x ∈ C, nrm σ p x = 1)
    (hI : pIdx p C ≠ 0) (hT : pTor p C ≠ 0) :
    (C.map (dif σ)).relIndex C ≠ 0 ∧ Nat.card ↥(C ⊓ fix σ) ≠ 0 ∧
      pIdx p C * Nat.card ↥(C ⊓ fix σ) ^ (p - 1) =
        (C.map (dif σ)).relIndex C ^ (p - 1) * pTor p C := by
  let τ : C →* C := (σ.comp C.subtype).codRestrict C (fun x => hst x x.2)
  have hτ : ∀ x : C, (τ x : A) = σ x := fun x => rfl
  have hit : ∀ (k : ℕ) (x : C), ((τ^[k] x : C) : A) = σ^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, ih]
  let lam : Monoid.End C := dif τ
  have hnτ : ∀ a, nrm τ p a = 1 := by
    intro a
    apply Subtype.ext
    have := hn a a.2
    rw [nrm_apply] at this ⊢
    rw [SubmonoidClass.coe_finsetProd]
    simp only [hit]
    exact this
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CNorm.pows_eq_range_dif_pow p C τ lam hp (fun _ => rfl) hnτ
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = k + 1 := ⟨p - 2, by have := hp.two_le; omega⟩
  rw [hk] at h1 h2 ⊢
  have eI : pIdx p C = (MonoidHom.range (lam ^ (k + 1) : Monoid.End C)).index := by
    rw [← h1, pIdx, Subgroup.relIndex]
    congr 1
    ext x
    simp only [pows, Subgroup.mem_subgroupOf, Subgroup.mem_map, powMonoidHom_apply]
    constructor
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, hy⟩, trivial, Subtype.ext e⟩
    · rintro ⟨y, -, e⟩
      exact ⟨y, y.2, congrArg Subtype.val e⟩
  have eT : pTor p C = Nat.card (MonoidHom.ker (lam ^ (k + 1) : Monoid.End C)) := by
    rw [pTor]
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, (h2 _).1 (Subtype.ext x.2.2)⟩,
      fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val ((h2 _).2 y.2)⟩, fun _ => rfl, fun _ => rfl⟩
  have ei : (C.map (dif σ)).relIndex C = (MonoidHom.range lam).index := by
    rw [Subgroup.relIndex]
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, hy⟩, Subtype.ext e⟩
    · rintro ⟨y, e⟩
      exact ⟨y, y.2, congrArg Subtype.val e⟩
  have ec : Nat.card ↥(C ⊓ fix σ) = Nat.card (MonoidHom.ker lam) := by
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext (div_eq_one.2 x.2.2)⟩,
      fun y => ⟨y.1.1, y.1.2, div_eq_one.1 (congrArg Subtype.val y.2)⟩, fun _ => rfl, fun _ => rfl⟩
  rw [eI] at hI ⊢
  rw [eT] at hT ⊢
  rw [ei, ec]
  exact _root_.GlobalTheory.CNorm.index_ker_iterate C lam k hI hT

theorem herbrand_prime_order : ∀ (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A), p.Prime → (∀ a, σ^[p] a = a) → pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → (nrm σ p).range.relIndex (fix σ) ≠ 0 ∧ (dif σ).range.relIndex (nrm σ p).ker ≠ 0 ∧ pIdx p (fix σ) ≠ 0 ∧ pTor p (fix σ) ≠ 0 ∧ (nrm σ p).range.relIndex (fix σ) ^ (p - 1) * pIdx p (⊤ : Subgroup A) * pTor p (fix σ) ^ p = (dif σ).range.relIndex (nrm σ p).ker ^ (p - 1) * pTor p (⊤ : Subgroup A) * pIdx p (fix σ) ^ p := by
  intro p A _ σ hp hσ ha ht
  have hker : (dif σ).ker = fix σ := by
    ext x
    rw [MonoidHom.mem_ker, dif_apply, div_eq_one, mem_fix]
  have hcT : pTor p (dif σ).range ≠ 0 := by
    unfold pTor at ht ⊢
    have hfin : Finite {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1} := Nat.finite_of_card_ne_zero ht
    have : Finite {x : A // x ∈ (dif σ).range ∧ x ^ p = 1} :=
      Finite.of_injective (β := {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1})
        (fun x => ⟨x.1, trivial, x.2.2⟩) (fun x y h => Subtype.ext (by simpa using h))
    have : Nonempty {x : A // x ∈ (dif σ).range ∧ x ^ p = 1} := ⟨⟨1, one_mem _, one_pow _⟩⟩
    exact Nat.card_pos.ne'
  obtain ⟨hbI, hbT, hcI⟩ := _root_.GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero p A A (dif σ) ha ht hcT
  obtain ⟨-, -, e1⟩ := _root_.GlobalTheory.CNorm.pIdx_pTor_ker_range p A A (dif σ) hbI hbT hcI hcT
  rw [hker] at hbI hbT e1
  obtain ⟨hi, hc, e2⟩ := herbPhi_stable p A σ hp (dif σ).range
    (by rintro _ ⟨y, rfl⟩; exact ⟨σ y, by rw [dif_apply, dif_apply, _root_.map_div]⟩)
    (by rintro _ ⟨y, rfl⟩; rw [herbPhi_nrm_dif, hσ, div_self']) hcI hcT
  have e3 := _root_.GlobalTheory.CNorm.herb_index_identity p A σ hσ
  have hle : pows p (fix σ) ≤ (nrm σ p).range := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ?_⟩
    have hy' : σ y = y := hy
    rw [nrm_apply, Finset.prod_congr rfl (fun i _ => Function.iterate_fixed hy' i)]
    simp
  have h0 : (nrm σ p).range.relIndex (fix σ) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hbI (Subgroup.relIndex_dvd_of_le_left _ hle)
  have h1 : (dif σ).range.relIndex (nrm σ p).ker ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at e3
    exact mul_ne_zero (mul_ne_zero h0 hi) hbT e3
  refine ⟨h0, h1, hbI, hbT, ?_⟩
  have := herbPhi_arith (p - 1) _ _ _ _ _ _ _ _ _ _ hi hcT e1 e2 e3
  rwa [Nat.sub_add_cancel hp.one_le] at this

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsQuadraticExtension
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma eq_one_of_sq_eq_one_withZero_int {r : WithZero (Multiplicative ℤ)} (h : r ^ 2 = 1) :
    r = 1 := by
  rcases lt_trichotomy r 1 with hr | hr | hr
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' hr two_ne_zero))
  · exact hr
  · exact absurd h (ne_of_gt (one_lt_pow₀ hr two_ne_zero))

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma valuation_algebraMap_eq_of_unit_at_under {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
    (hq : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (w : HeightOneSpectrum (𝓞 E))
    (h2 : (w.under (𝓞 F)).valuation F 2 = 1) (hδ : (w.under (𝓞 F)).valuation F δ = 1) (c : F) :
    w.valuation E (algebraMap F E c) = (w.under (𝓞 F)).valuation F c := by
  obtain ⟨-, -, hram⟩ := _root_.GlobalTheory.QNorm.places_over F E
  obtain ⟨e, he0, hw⟩ := hram w
  set v := w.under (𝓞 F)
  set V := w.valuation E
  suffices he : e = 1 by rw [hw, he, pow_one]
  have hV2 : V 2 = 1 := by
    have := hw 2
    rw [map_ofNat] at this
    rw [this, h2, one_pow]
  have hθ : V θ = 1 := by
    apply eq_one_of_sq_eq_one_withZero_int
    rw [← map_pow, hq.sq, hw, hδ, one_pow]
  have hσθ := hq.conj
  have hθ0 := hq.root_ne_zero
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  obtain ⟨a, b, hab⟩ := hq.span x
  have hσx : σ x = algebraMap F E a - algebraMap F E b * θ := by
    rw [hab, map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hσθ]; ring
  obtain ⟨-, -, -, hnorm, -⟩ := _root_.GlobalTheory.QNorm.isQuad_basic F E δ θ σ hq
  obtain ⟨a', b', hN⟩ := hnorm x
  have hbθ : V (algebraMap F E b * θ) = V (algebraMap F E b) := by rw [map_mul, hθ, mul_one]
  have hA : V x ≤ max (V (algebraMap F E a)) (V (algebraMap F E b)) := by
    rw [hab, ← hbθ]; exact Valuation.map_add _ _ _
  have hB : V (σ x) ≤ max (V (algebraMap F E a)) (V (algebraMap F E b)) := by
    rw [hσx, ← hbθ]; exact Valuation.map_sub _ _ _
  have ha : V (algebraMap F E a) ≤ max (V x) (V (σ x)) := by
    have h' : algebraMap F E a = (x + σ x) * (2 : E)⁻¹ := by
      rw [hσx, hab]; field_simp; ring
    rw [h', map_mul, map_inv₀, hV2, inv_one, mul_one]
    exact Valuation.map_add _ _ _
  have hb : V (algebraMap F E b) ≤ max (V x) (V (σ x)) := by
    have h' : algebraMap F E b = (x - σ x) * (2 * θ)⁻¹ := by
      rw [hσx, hab]; field_simp; ring
    rw [h', map_mul, map_inv₀, map_mul, hV2, hθ, one_mul, inv_one, mul_one]
    exact Valuation.map_sub _ _ _
  have hmax : max (V x) (V (σ x)) = max (V (algebraMap F E a)) (V (algebraMap F E b)) :=
    le_antisymm (max_le hA hB) (max_le ha hb)
  have hx0 : V x ≠ 0 := by rw [hx]; exact WithZero.exp_ne_zero
  have key : ∃ d : F, V x = v.valuation F d ^ e := by
    have hmem : max (V x) (V (σ x)) = V (algebraMap F E a) ∨
        max (V x) (V (σ x)) = V (algebraMap F E b) := by
      rw [hmax]; exact max_choice _ _
    rcases le_total (V (σ x)) (V x) with hle | hle
    · rw [max_eq_left hle] at hmem
      rcases hmem with h | h
      · exact ⟨a, h.trans (hw a)⟩
      · exact ⟨b, h.trans (hw b)⟩
    · rw [max_eq_right hle] at hmem
      have hc : ∃ c : F, V (σ x) = V (algebraMap F E c) := by
        rcases hmem with h | h
        · exact ⟨a, h⟩
        · exact ⟨b, h⟩
      obtain ⟨c, hc⟩ := hc
      have hσ0 : V (σ x) ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hx0) hle)
      refine ⟨(a' ^ 2 - δ * b' ^ 2) / c, ?_⟩
      rw [← hw, map_div₀, map_div₀, ← hN, ← hc, map_mul, mul_div_cancel_right₀ _ hσ0]
  obtain ⟨d, hd⟩ := key
  rw [hx] at hd
  have hl := congrArg WithZero.log hd
  rw [WithZero.log_exp, WithZero.log_pow, nsmul_eq_mul] at hl
  rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hl.symm with h1 | h1 <;> omega


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → _root_.GlobalTheory.QNorm.admitted F S →
    (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ _root_.GlobalTheory.QNorm.sUnits E SE →
    (u : E) * σ u = 1 → ∃ y : Eˣ, y ∈ _root_.GlobalTheory.QNorm.sUnits E SE ∧ (u : E) = y / σ y := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hSE hS hδ u hu hnu
  classical
  obtain ⟨-, -, -, -, h90, -⟩ := _root_.GlobalTheory.QNorm.isQuad_basic F E δ θ σ hq
  obtain ⟨y, hy0, hy⟩ := h90 u hnu
  obtain ⟨-, hover, -⟩ := _root_.GlobalTheory.QNorm.places_over F E
  obtain ⟨-, hdich⟩ := _root_.GlobalTheory.QNorm.conj_places_transitive F E δ θ σ hq
  choose ch hch using hover
  rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hu
  have hadm := hS
  unfold _root_.GlobalTheory.QNorm.admitted at hadm
  have hinv : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE →
      w.valuation E (σ y) = w.valuation E y := by
    intro w hw
    have h1 := hu w hw
    rw [hy, map_div₀] at h1
    have hσy0 : w.valuation E (σ y) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr ((map_ne_zero σ).mpr hy0)
    exact ((div_eq_one_iff_eq hσy0).mp h1).symm
  have hfib : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE →
      w.valuation E y = (ch (w.under (𝓞 F))).valuation E y := by
    intro w hw
    have hv : (ch (w.under (𝓞 F))).under (𝓞 F) = w.under (𝓞 F) := hch _
    have hw0 : ch (w.under (𝓞 F)) ∉ SE := by
      rw [hSE, hv]; rwa [hSE] at hw
    rcases hdich (ch (w.under (𝓞 F))) w hv.symm with h | h
    · rw [← h]
    · rw [h y, hinv _ hw0]
  let n : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    if v ∈ S then 0 else -((ch v).valuation E y).log
  have hfin := _root_.GlobalTheory.QNorm.finite_valuation_ne_one E (Units.mk0 y hy0)
  let T : Finset (HeightOneSpectrum (𝓞 F)) :=
    hfin.toFinset.image (fun w => w.under (𝓞 F))
  have hnT : ∀ v ∉ T, n v = 0 := by
    intro v hv
    by_cases hvS : v ∈ S
    · simp [n, hvS]
    · have h1 : (ch v).valuation E y = 1 := by
        by_contra hne
        apply hv
        refine Finset.mem_image.mpr ⟨ch v, ?_, hch v⟩
        rw [Set.Finite.mem_toFinset]
        exact hne
      simp [n, hvS, h1]
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.QNorm.exists_unit_valuation_eq_of_adm F S T n hS hnT
  have ha0 : algebraMap F E a ≠ 0 := by simp
  refine ⟨Units.mk0 (y * algebraMap F E a) (mul_ne_zero hy0 ha0), ?_, ?_⟩
  · rw [_root_.GlobalTheory.QNorm.mem_sUnits]
    intro w hw
    have hvS : w.under (𝓞 F) ∉ S := by rwa [hSE] at hw
    show w.valuation E (y * algebraMap F E a) = 1
    rw [map_mul, valuation_algebraMap_eq_of_unit_at_under hq w (hadm _ hvS).1 (hδ _ hvS), ha _ hvS,
      hfib w hw]
    have h0 : (ch (w.under (𝓞 F))).valuation E y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    simp only [n, if_neg hvS]
    nth_rewrite 1 [← WithZero.exp_log h0]
    rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · show (u : E) = y * algebraMap F E a / σ (y * algebraMap F E a)
    rw [hy, map_mul, AlgEquiv.commutes, mul_div_mul_right _ _ ha0]

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemUnitsLocalKummerNormsOfBaseChangeNorm
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem isUnit_of_norm_ne_zero {L A : Type} [Field L] [CommRing A] [Algebra L A]
    [Module.Finite L A] (y : A) (h : Algebra.norm L y ≠ 0) : IsUnit y := by
  have h1 : IsUnit (Algebra.lmul L A y) := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (by rwa [Algebra.norm_apply] at h)
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp h1).surjective 1
  exact IsUnit.of_mul_eq_one z (by simpa using hz)

theorem IsKum.nonempty_tensor_equiv {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E]
    {ζ δ : F} {θ : E} {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (L : Type) [Field L] [Algebra F L] :
    Nonempty ((L ⊗[F] E) ≃ₐ[L] AdjoinRoot (X ^ p - C (algebraMap F L δ) : L[X])) := by
  have hp := h.prime
  have hmin := h.minpoly_eq
  have hint : IsIntegral F θ :=
    ⟨X ^ p - C δ, monic_X_pow_sub_C δ hp.ne_zero, by simp [h.pow]⟩
  let pb : PowerBasis F E := PowerBasis.ofAdjoinEqTop hint h.gen
  have hgen : pb.gen = θ := PowerBasis.ofAdjoinEqTop_gen hint h.gen
  set g : L[X] := X ^ p - C (algebraMap F L δ) with hg
  have hroot : AdjoinRoot.root g ^ p = algebraMap F (AdjoinRoot g) δ := by
    have := AdjoinRoot.eval₂_root g
    rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
    rw [IsScalarTower.algebraMap_apply F L (AdjoinRoot g)]
    exact this
  let ψ : E →ₐ[F] AdjoinRoot g := pb.lift (AdjoinRoot.root g) (by
    rw [hgen, hmin]; simp [hroot])
  have hψ : ψ θ = AdjoinRoot.root g := (congrArg _ hgen.symm).trans (pb.lift_gen _ _)
  let a : (L ⊗[F] E) →ₐ[L] AdjoinRoot g :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ψ (fun _ _ => Commute.all _ _)
  let b : AdjoinRoot g →ₐ[L] (L ⊗[F] E) :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId L _) ((1 : L) ⊗ₜ[F] θ) (by
      rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero, Algebra.TensorProduct.tmul_pow,
        one_pow, h.pow]
      change _ = algebraMap L (L ⊗[F] E) (algebraMap F L δ)
      rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',])
  have hb : b (AdjoinRoot.root g) = (1 : L) ⊗ₜ[F] θ := AdjoinRoot.liftAlgHom_root ..
  have ha : a ((1 : L) ⊗ₜ[F] θ) = AdjoinRoot.root g := by
    simp [a, hψ]
  refine ⟨AlgEquiv.ofAlgHom a b ?_ ?_⟩
  · apply AdjoinRoot.algHom_ext
    simp [ha, hb]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply pb.algHom_ext
      rw [hgen]
      simp [ha, hb]

theorem mem_kNorm_of_tNorm : ∀ (p : ℕ) (F E L : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field L] [Algebra F L] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ x : Fˣ, TNorm F E L (x : F) → x ∈ kNorm p (algebraMap F L) δ := by
  intro p F E L _ _ _ _ _ _ ζ δ θ σ h x ⟨y, hy⟩
  obtain ⟨e⟩ := h.nonempty_tensor_equiv L
  have : Module.Finite L (AdjoinRoot (X ^ p - C (algebraMap F L δ) : L[X])) :=
    (AdjoinRoot.powerBasis' (monic_X_pow_sub_C _ h.prime.ne_zero)).finite
  have hn : Algebra.norm L (e y) = algebraMap F L x := by
    rw [Algebra.norm_eq_of_algEquiv, hy]
  have hu : IsUnit (e y) := isUnit_of_norm_ne_zero _ (by
    rw [hn]; exact (_root_.map_ne_zero _).mpr x.ne_zero)
  rw [mem_kNorm]
  exact ⟨hu.unit, hn⟩

end GlobalTheory.CNorm
end

