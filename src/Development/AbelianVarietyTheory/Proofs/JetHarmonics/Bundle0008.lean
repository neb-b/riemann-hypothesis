module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LeastExponentCompare
open NumberField NumberField.IsCMField TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace


set_option autoImplicit false in
open NumberField NumberField.IsCMField TensorProduct in
theorem _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj (E : Type) [Field E] [NumberField E] (cj : E → E)
    (h : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) (hne : ∃ z : E, cj z ≠ z) :
    IsCMField E := by
  let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
  have inj := φ₀.injective
  have hadd : ∀ a b, cj (a + b) = cj a + cj b := fun a b =>
    inj (by rw [h, map_add (f := _), map_add (f := _), h, h, star_add])
  have hmul : ∀ a b, cj (a * b) = cj a * cj b := fun a b =>
    inj (by rw [h, map_mul, map_mul, h, h, star_mul'])
  have hinv : ∀ z, cj (cj z) = z := fun z => inj (by rw [h, h, star_star])
  let e : E ≃+* E :=
    { toFun := cj, invFun := cj, left_inv := hinv, right_inv := hinv,
      map_mul' := hmul, map_add' := hadd }
  let σ : E ≃ₐ[ℚ] E := e.toRatAlgEquiv
  have hσ : ∀ z, σ z = cj z := fun _ => rfl
  have hsq : σ ^ 2 = 1 := AlgEquiv.ext fun z => by
    rw [pow_two, AlgEquiv.mul_apply, hσ, hσ, hinv, AlgEquiv.one_apply]
  have hne1 : σ ≠ 1 := by
    obtain ⟨z, hz⟩ := hne
    intro h1
    exact hz (by rw [← hσ, h1, AlgEquiv.one_apply])
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq hne1
  have hfix : ∀ x, x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) ↔ cj x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun hx => hx σ (Subgroup.mem_zpowers σ), fun hx f hf => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    clear hf
    have hσx : σ x = x := hx
    have hσx' : σ⁻¹ x = x := by
      calc σ⁻¹ x = (σ⁻¹ * σ) x := by rw [AlgEquiv.mul_apply, hσx]
        _ = x := by rw [inv_mul_cancel, AlgEquiv.one_apply]
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hσx, ih]
    | pred k ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hσx', ih]
  have hS : maximalRealSubfield E =
      (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield := by
    ext x
    rw [mem_maximalRealSubfield_iff, IntermediateField.mem_toSubfield, hfix]
    exact ⟨fun hx => inj ((h φ₀ x).trans (hx φ₀)), fun hx φ => by rw [← h φ x, hx]⟩
  have hfin : Module.finrank (maximalRealSubfield E) E = 2 := by
    rw [hS]
    exact (IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)).trans
      (by rw [Nat.card_zpowers, hord])
  haveI : IsTotallyComplex E := ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mp fun hv => by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hv
    obtain ⟨z, hz⟩ := hne
    exact hz (v.embedding.injective ((h _ z).trans (RingHom.congr_fun hv z)))⟩
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield E) E := ⟨hfin⟩
  exact ⟨⟩


set_option autoImplicit false in
open NumberField NumberField.IsCMField TensorProduct in
theorem _root_.GlobalTheory.LeastExponentCompare.conj_iff (E : Type) [Field E] [NumberField E]
    (cj : E → E) :
    ((∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ ∃ z : E, cj z ≠ z) ↔
      ∃ _ : IsCMField E, cj = fun z => complexConj E z := by
  constructor
  · rintro ⟨h, hne⟩
    haveI := _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj E cj h hne
    refine ⟨this, funext fun z => ?_⟩
    let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
    exact φ₀.injective (by rw [h, complexEmbedding_complexConj, RCLike.star_def])
  · rintro ⟨_, rfl⟩
    refine ⟨fun φ z => by rw [complexEmbedding_complexConj, RCLike.star_def], ?_⟩
    by_contra hall
    push_neg at hall
    exact complexConj_ne_one E (AlgEquiv.ext hall)

section Comparison₂
variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]

def IntegralAreSums (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ l : S →ₗ[ℝ] ℝ, (∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z) →
    ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : S, l β = ∑ i, (β : Bil Y) (x i) (x' i)

end Comparison₂

section AtLattice
variable (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

variable [IsCMField E]

end AtLattice

section Families

abbrev SpaceRule : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Bil Y)

abbrev ValueRule (S : SpaceRule) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ

variable {S : SpaceRule} {φ : ValueRule S}

end Families

end GlobalTheory.LeastExponentCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSeparatingModPrimePow
section
namespace GlobalTheory

private lemma ringHom_pow_sub_mem_span {A O : Type} [CommRing A] [CommRing O] (g : ℕ)
    (hA : ∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) (σ : A →+* O) (x : A) :
    σ x ^ g - σ x ∈ Ideal.span {(g : O)} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hA x)
  exact Ideal.mem_span_singleton'.mpr
    ⟨σ c, by rw [← map_natCast σ g, ← map_mul, hc, map_sub, map_pow]⟩

theorem _root_.GlobalTheory.exists_separating_mod_prime_pow : ∀ (A O : Type) [CommRing A] [Module.Finite ℤ A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ (T : Type) [Fintype T] [DecidableEq T] (σ : T → A →+* O), Function.Injective σ → ∀ (K : ℕ) (t₀ : T), ∃ e : A, ∀ t, σ t e - (if t = t₀ then 1 else 0) ∈ Ideal.span {(g : O) ^ K} := by
  intro A O _ _ _ _ g hg hgO hA T _ _ σ hσ K t₀
  have h2 : 2 ≤ g := hg.two_le
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hgO)
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  have hb : ∀ t, t ≠ t₀ → ∃ b : A, σ t b ∈ Ideal.span {(g : O)} ∧ IsUnit (σ t₀ b) := by
    intro t ht
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.exists_isUnit_sub_of_ringHom_ne A O g hg hgO hA (σ t₀) (σ t)
      (fun h => ht (hσ h).symm)
    obtain ⟨⟨i, hi⟩, -⟩ := _root_.GlobalTheory.hom_value_congruent_int_mod_prime A O g hg hgO hA (σ t) a
    refine ⟨a - (i : A), by rwa [map_sub, map_intCast], ?_⟩
    rw [map_sub, map_intCast]
    by_contra hn
    have h1 : σ t₀ a - (i : O) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hn)
    have h3 : σ t₀ a - σ t a ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ h1 (hspan hi)
      rwa [sub_sub_sub_cancel_right] at this
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h3)) ha
  choose! b hb1 hb2 using hb
  obtain ⟨c, hc0, hct⟩ : ∃ c : A, IsUnit (σ t₀ c) ∧ ∀ t, t ≠ t₀ → σ t c ∈ Ideal.span {(g : O)} := by
    refine ⟨∏ t ∈ Finset.univ.erase t₀, b t, ?_, fun t ht => ?_⟩
    · rw [map_prod]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        (fun t ht => hb2 t (Finset.ne_of_mem_erase ht))
    · rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩)]
      exact Ideal.mul_mem_right _ _ (hb1 t ht)
  obtain ⟨f, hf0, hft⟩ : ∃ f : A, σ t₀ f - 1 ∈ Ideal.span {(g : O)} ∧
      ∀ t, t ≠ t₀ → σ t f ∈ Ideal.span {(g : O)} := by
    refine ⟨c ^ (g - 1), ?_, fun t ht => ?_⟩
    · rw [map_pow]
      have hz : σ t₀ c * (σ t₀ c ^ (g - 1) - 1) = σ t₀ c ^ g - σ t₀ c := by
        rw [mul_sub, mul_one, ← pow_succ']
        congr 2
        omega
      have : σ t₀ c ^ (g - 1) - 1 = (σ t₀ c ^ g - σ t₀ c) * ↑hc0.unit⁻¹ := by
        rw [← hz, mul_comm (σ t₀ c), mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ (ringHom_pow_sub_mem_span g hA (σ t₀) c)
    · rw [map_pow]
      exact Ideal.pow_mem_of_mem _ (hct t ht) _ (by omega)
  refine ⟨1 - (1 - f ^ K) ^ K, fun t => ?_⟩
  rw [← Ideal.span_singleton_pow]
  split_ifs with ht
  · subst ht
    simp only [map_sub, map_one, map_pow]
    have h1 : 1 - σ t f ^ K ∈ Ideal.span {(g : O)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hf0 ⊢
      rw [map_sub, map_one, map_pow]
      rw [map_sub, map_one, sub_eq_zero] at hf0
      rw [hf0, one_pow, sub_self]
    have : 1 - (1 - σ t f ^ K) ^ K - 1 = -((1 - σ t f ^ K) ^ K) := by ring
    rw [this]
    exact neg_mem (Ideal.pow_mem_pow h1 K)
  · simp only [map_sub, map_one, map_pow]
    have hw : σ t f ^ K ∈ Ideal.span {(g : O)} ^ K := Ideal.pow_mem_pow (hft t ht) K
    have hgs := geom_sum_mul (1 - σ t f ^ K) K
    have : 1 - (1 - σ t f ^ K) ^ K - 0 =
        (∑ i ∈ Finset.range K, (1 - σ t f ^ K) ^ i) * σ t f ^ K := by
      linear_combination hgs
    rw [this]
    exact Ideal.mul_mem_left _ _ hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueMaximalAbovePlace
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.OnePrime

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

theorem nontrivial_Ow (w : Place p R) : Nontrivial w.Ow := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  rw [Ideal.span_singleton_eq_top] at h
  have h1 : (1 - w.e) * (1 - w.e) = (1 - w.e) * 1 := by
    rw [mul_one]; exact w.idem.one_sub
  exact w.ne_zero (sub_eq_self.mp (h.mul_left_cancel h1))

theorem idem_Ow (w : Place p R) {d : w.Ow} (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  have hx : x * x - x ∈ Ideal.span {1 - w.e} :=
    Ideal.Quotient.eq.mp (by rw [map_mul]; exact hd)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
  have hee : w.e * w.e = w.e := w.idem
  have he1 : Ideal.Quotient.mk (Ideal.span {1 - w.e}) w.e = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩
  have hf : IsIdempotentElem (w.e * x) := by
    show w.e * x * (w.e * x) = w.e * x
    linear_combination (x * x - c) * hee - w.e * hc
  have hfe : w.e * x * w.e = w.e * x := by linear_combination x * hee
  have hmk : Ideal.Quotient.mk (Ideal.span {1 - w.e}) (w.e * x) =
      Ideal.Quotient.mk (Ideal.span {1 - w.e}) x := by
    rw [map_mul, he1, one_mul]
  rcases w.primitive _ hf hfe with h0 | h1
  · left
    rw [← hmk, h0, map_zero]
  · right
    rw [← hmk, h1, he1]

theorem maximal_unique [Module.Finite ℤ R] (w : Place p R) (M N : Ideal w.Ow) (hM : M.IsMaximal)
    (hN : N.IsMaximal) : N = M := by
  have : HenselianLocalRing ℤ_[p] := GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[p]
  have := hM
  obtain ⟨d, hd, hmem⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian ℤ_[p] (S := w.Ow) M
  rcases idem_Ow w hd with rfl | rfl
  · exact absurd M.zero_mem ((hmem M hM).mpr rfl)
  · exact (hmem N hN).mp (fun h => hN.ne_top ((Ideal.eq_top_iff_one _).mpr h))

private theorem exists_eq_one_tmul_add_mul (x : Op p R) :
    ∃ (r : R) (t : Op p R), x = (1 : ℤ_[p]) ⊗ₜ r + (p : Op p R) * t := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z r =>
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := z)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨(n : R) * r, t ⊗ₜ r, ?_⟩
    have hz : z = (n : ℤ_[p]) + t * p := by rw [ht]; ring
    have h1 : (n : ℤ_[p]) ⊗ₜ[ℤ] r = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by
      calc (n : ℤ_[p]) ⊗ₜ[ℤ] r = ((n : ℤ_[p]) ⊗ₜ[ℤ] (1 : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        _ = (n : Op p R) * ((1 : ℤ_[p]) ⊗ₜ r) := by rw [Algebra.TensorProduct.natCast_def]
        _ = ((1 : ℤ_[p]) ⊗ₜ[ℤ] (n : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by
            rw [Algebra.TensorProduct.natCast_def']
        _ = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (t * p) ⊗ₜ[ℤ] r = (p : Op p R) * (t ⊗ₜ r) := by
      rw [Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
    rw [hz, TensorProduct.add_tmul, h1, h2]
  | add x y hx hy =>
    obtain ⟨r₁, t₁, h₁⟩ := hx
    obtain ⟨r₂, t₂, h₂⟩ := hy
    exact ⟨r₁ + r₂, t₁ + t₂, by rw [h₁, h₂, TensorProduct.tmul_add]; ring⟩

theorem exists_eq_add (w : Place p R) (s : w.Ow) :
    ∃ (r : R) (t : w.Ow), s = w.toOw r + (p : w.Ow) * t := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, t, h⟩ := exists_eq_one_tmul_add_mul x
  refine ⟨r, Ideal.Quotient.mk _ t, ?_⟩
  rw [h, map_add (f := _), map_mul, map_natCast]
  rfl

theorem exists_prime_under (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDedekindDomain R]
    [CharZero R] [Module.Finite ℤ R] (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p R) :
    ∃ P : Ideal R, P.IsMaximal ∧ (p : R) ∈ P ∧ (P.map w.toOw).IsMaximal ∧
      ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤ := by
  have : HenselianLocalRing ℤ_[p] := GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[p]
  have : Nontrivial w.Ow := nontrivial_Ow w
  have : IsLocalRing w.Ow := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal w.Ow
    exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => maximal_unique w M N hM hN⟩
  set m := IsLocalRing.maximalIdeal w.Ow with hm
  set P := m.comap w.toOw with hP
  have hpm : (p : w.Ow) ∈ m := by
    have hc := GlobalTheory.comap_eq_maximalIdeal_of_finite (R := ℤ_[p]) (S := w.Ow) m
    have h0 : (p : ℤ_[p]) ∈ m.comap (algebraMap ℤ_[p] w.Ow) := by
      rw [hc, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at h0
    exact h0
  have hpP : (p : R) ∈ P := by
    rw [hP, Ideal.mem_comap, map_natCast]
    exact hpm
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hpP
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPne
  have hmap : P.map w.toOw = m := by
    refine le_antisymm Ideal.map_comap_le fun s hs => ?_
    obtain ⟨r, t, rfl⟩ := exists_eq_add w s
    have hpt : (p : w.Ow) * t ∈ P.map w.toOw := by
      rw [← map_natCast w.toOw p]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hpP)
    have hr : w.toOw r ∈ m := by
      have h1 := m.sub_mem hs (m.mul_mem_right t hpm)
      rwa [add_sub_cancel_right] at h1
    exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ (show r ∈ P from hr)) hpt
  refine ⟨P, hPmax, hpP, by rw [hmap]; infer_instance, fun Q hQ hQP => ?_⟩
  by_contra hne
  have hle : Q.map w.toOw ≤ m := IsLocalRing.le_maximalIdeal hne
  exact hQP (hQ.eq_of_le hPmax.ne_top fun q hq => hle (Ideal.mem_map_of_mem _ hq))

end GlobalTheory.OnePrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqLowering
section
open Finset

noncomputable section

namespace GlobalTheory.WigSh.LowerBound

private theorem prod_erase_succAbove {n : ℕ} (f : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∏ j ∈ univ.erase l, f j = ∏ j : Fin n, f (l.succAbove j) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ]
  · rw [Finset.prod_image]
    intro a _ b _ hab
    exact Fin.succAbove_right_injective hab

private theorem ratio_pos_case {a b c : ℝ} (hb : 0 < b) (h : c ≤ a) :
    c * b / b ^ 2 ≤ a / b := by
  have : c * b / b ^ 2 = c / b := by field_simp
  rw [this]
  exact div_le_div_of_nonneg_right h hb.le

private theorem factor_lower {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (l : Fin (n + 1))
    (hs : StrictAnti L) (j : Fin n) (h1 : L j.succ < M j) (h2 : M j ≤ L j.castSucc)
    (h3 : M j ≠ L l) (G : Fin (n + 1) → ℤ)
    (hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i))) :
    (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2 ≤
      ((M j : ℝ) - L l) / ((L (l.succAbove j) : ℝ) - L l) := by
  have g1 := hG j.succ
  have g2 := hG j.castSucc
  rcases lt_or_ge j.castSucc l with hl | hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ hl]
    have a1 : L l < L j.castSucc := hs hl
    have a2 : L l ≤ L j.succ := hs.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)
    have e : G j.castSucc = L j.castSucc - L l := by omega
    have e' : (L j.castSucc : ℝ) - L l = G j.castSucc := by rw [e]; push_cast; ring
    rw [e']
    apply ratio_pos_case
    · have : (0 : ℤ) < G j.castSucc := by omega
      exact_mod_cast this
    · have : G j.succ ≤ M j - L l := by omega
      exact_mod_cast this
  · rw [Fin.succAbove_of_le_castSucc _ _ hl]
    have a2 : L j.castSucc ≤ L l := hs.antitone hl
    have e : G j.succ = L l - L j.succ := by omega
    have e' : (L j.succ : ℝ) - L l = -G j.succ := by rw [e]; push_cast; ring
    rw [e', div_neg, ← neg_div, mul_comm]
    apply ratio_pos_case
    · have : (0 : ℤ) < G j.succ := by omega
      exact_mod_cast this
    · have : G j.castSucc ≤ -(M j - L l) := by omega
      exact_mod_cast this

end GlobalTheory.WigSh.LowerBound

namespace GlobalTheory.WigSh

open LowerBound

theorem inv_sq_le_wM (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hs : StrictAnti L) (hbox : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hlast : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by
  set G : Fin (n + 1) → ℤ := fun i => max 1 (max (L i - L l) (L l - L i)) with hGdef
  have hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i)) := fun i => rfl
  have hpos : ∀ i, (0 : ℝ) < G i := fun i => by
    have : (0 : ℤ) < G i := by rw [hG]; omega
    exact_mod_cast this
  have hl : G l = 1 := by rw [hG]; omega
  have hG0 : (G 0 : ℝ) ≤ D := by
    have a : L l ≤ L 0 := hs.antitone (Fin.zero_le l)
    have : G 0 = 1 ∨ G 0 = L 0 - L l := by rw [hG]; omega
    rcases this with e | e <;> rw [e] <;> push_cast <;> assumption
  have hGl : (G (Fin.last n) : ℝ) ≤ D := by
    have a : L (Fin.last n) ≤ L l := hs.antitone (Fin.le_last l)
    have : G (Fin.last n) = 1 ∨ G (Fin.last n) = L l - L (Fin.last n) := by rw [hG]; omega
    rcases this with e | e <;> rw [e] <;> push_cast <;> assumption
  set P : ℝ := ∏ i, (G i : ℝ) with hP
  have hPpos : 0 < P := Finset.prod_pos fun i _ => hpos i
  have p1 : ∏ j : Fin n, (G j.succ : ℝ) = P / G 0 := by
    rw [eq_div_iff (hpos 0).ne', hP, Fin.prod_univ_succ, mul_comm]
  have p2 : ∏ j : Fin n, (G j.castSucc : ℝ) = P / G (Fin.last n) := by
    rw [eq_div_iff (hpos _).ne', hP, Fin.prod_univ_castSucc]
  have p3 : ∏ j : Fin n, (G (l.succAbove j) : ℝ) = P := by
    rw [hP, Fin.prod_univ_succAbove _ l, hl]; simp
  unfold wM
  rw [prod_erase_succAbove, ← Finset.prod_div_distrib]
  refine le_trans ?_ (Finset.prod_le_prod₀
    (f := fun j : Fin n => (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2)
    (fun j _ => ?_) (fun j _ => factor_lower l hs j (hbox j).1 (hbox j).2 (hne j) G hG))
  · rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow, p1, p2, p3]
    have q0 := hpos 0
    have ql := hpos (Fin.last n)
    have : P / G 0 * (P / G (Fin.last n)) / P ^ 2 = ((G 0 : ℝ) * G (Fin.last n))⁻¹ := by
      field_simp
    rw [this]
    apply inv_anti₀ (mul_pos q0 ql)
    rw [sq]
    exact mul_le_mul hG0 hGl ql.le (by linarith)
  · have := hpos j.succ
    have := hpos j.castSucc
    positivity

end GlobalTheory.WigSh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerExtremeNeZero
section
open Finset

namespace GlobalTheory.WigSh

theorem wigner_den_ne_zero {n : ℕ} (L : Fin (n+1) → ℤ) (l : Fin (n+1)) (hL : StrictAnti L) :
    (∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have h1 : j ≠ l := (Finset.mem_erase.mp hj).1
  have h2 : L j ≠ L l := fun h => h1 (hL.injective h)
  exact sub_ne_zero.mpr (by exact_mod_cast h2)

theorem wigner_extreme_ne_zero : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (l : Fin (n+1)), StrictAnti L → ((∀ j, L j ≠ L l + 1) → GlobalTheory.WigSh.wP L (fun j : Fin n => L j.castSucc) l ≠ 0) ∧ ((∀ j, L j ≠ L l - 1) → GlobalTheory.WigSh.wM L (fun j : Fin n => L j.succ + 1) l ≠ 0) := by
  intro n L l hL
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold wP
    refine div_ne_zero ?_ (wigner_den_ne_zero L l hL)
    rw [Finset.prod_ne_zero_iff]
    intro j _
    have h1 : L j.castSucc - 1 - L l ≠ 0 := by
      have := h j.castSucc
      omega
    exact_mod_cast h1
  · unfold wM
    refine div_ne_zero ?_ (wigner_den_ne_zero L l hL)
    rw [Finset.prod_ne_zero_iff]
    intro j _
    have h1 : L j.succ + 1 - L l ≠ 0 := by
      have := h j.succ
      omega
    exact_mod_cast h1

end GlobalTheory.WigSh
end

