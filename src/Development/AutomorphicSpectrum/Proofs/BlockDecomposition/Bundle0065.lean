module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0044
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0048
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardZero
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.NormZero

variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

abbrev Fx (τ : E →+* E) : Type := {a : E // τ a = a}

def zeroFx (τ : E →+* E) : Fx τ := ⟨0, map_zero τ⟩

theorem finite_of_resAlg (h : ResAlg E τ q ε) : Finite E := by
  apply Nat.finite_of_card_ne_zero
  rw [h.card]
  have := h.one_lt
  positivity

theorem nontrivial_of_resAlg (h : ResAlg E τ q ε) : Nontrivial E := by
  haveI := finite_of_resAlg h
  apply Finite.one_lt_card_iff_nontrivial.1
  rw [h.card]
  have := h.one_lt
  nlinarith

theorem card_fx (h : ResAlg E τ q ε) : Nat.card (Fx τ) = q := by
  obtain ⟨u, hu, hb⟩ := h.basis
  let φ : Fx τ × Fx τ → E := fun p => (p.1 : E) + (p.2 : E) * u
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      have h1 : x + y * u = x' + y' * u := hxy
      have h2 : x + y * τ u = x' + y' * τ u := by
        have := congrArg τ h1
        simpa [hx, hy, hx', hy'] using this
      have h3 : (y - y') * (u - τ u) = 0 := by linear_combination h1 - h2
      have h4 : y = y' := sub_eq_zero.1 (hu.mul_left_eq_zero.1 h3)
      have h5 : x = x' := by
        subst h4
        exact add_right_cancel h1
      subst h4 h5
      rfl
    · intro a
      obtain ⟨x, y, hx, hy, rfl⟩ := hb a
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have h1 : Nat.card (Fx τ × Fx τ) = Nat.card E := Nat.card_congr (Equiv.ofBijective φ hφ)
  rw [Nat.card_prod, h.card] at h1
  have h2 : Nat.card (Fx τ) ^ 2 = q ^ 2 := by rw [← h1]; ring
  exact (Nat.pow_left_inj (by norm_num)).1 h2

theorem exists_idem (h : ResAlg E τ q ε) (hf : ¬ IsField E) :
    ∃ e : E, e * e = e ∧ τ e = 1 - e := by
  haveI := nontrivial_of_resAlg h
  obtain ⟨a, ha0, hau⟩ : ∃ a : E, a ≠ 0 ∧ ¬ IsUnit a := by
    by_contra hc
    push_neg at hc
    refine hf ⟨exists_pair_ne E, mul_comm, fun {a} ha => ?_⟩
    obtain ⟨b, hb⟩ := (hc a ha).exists_right_inv
    exact ⟨b, hb⟩
  obtain ⟨u, hu, -⟩ := h.basis
  have hN : a * τ a = 0 := by
    by_contra hN
    have hfix : τ (a * τ a) = a * τ a := by rw [map_mul, h.inv, mul_comm]
    exact hau (isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hN))
  have htfix : τ (a + τ a) = a + τ a := by rw [map_add (f := _), h.inv, add_comm]
  by_cases ht : a + τ a = 0
  · exfalso
    have hτa : τ a = -a := by linear_combination ht
    have hfix : τ (a * (u - τ u)) = a * (u - τ u) := by
      rw [map_mul, map_sub, h.inv, hτa]
      ring
    have hne : a * (u - τ u) ≠ 0 := fun h0 => ha0 (hu.mul_left_eq_zero.1 h0)
    exact hau (isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hne))
  · obtain ⟨s, hs⟩ := (h.fixedUnit _ htfix ht).exists_right_inv
    have hτs : τ s = s := by
      have h1 : (a + τ a) * τ s = 1 := by
        have := congrArg τ hs
        rwa [map_mul, htfix, map_one] at this
      calc τ s = (s * (a + τ a)) * τ s := by rw [mul_comm s, hs, one_mul]
        _ = s * ((a + τ a) * τ s) := by ring
        _ = s := by rw [h1, mul_one]
    have hτe : τ (a * s) = 1 - a * s := by
      rw [map_mul, hτs]
      linear_combination hs
    refine ⟨a * s, ?_, hτe⟩
    linear_combination (-(s * s)) * hN + (a * s) * hs

theorem card_axes {F : Type} [Finite F] (z : F) :
    Nat.card {p : F × F // p.1 = z ∨ p.2 = z} + 1 = 2 * Nat.card F := by
  classical
  haveI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (Finset.univ.filter fun p : F × F => p.1 = z ∨ p.2 = z)
      = (({z} : Finset F) ×ˢ (Finset.univ : Finset F)) ∪ ((Finset.univ : Finset F) ×ˢ ({z} : Finset F)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, and_true, true_and]
  have h2 : (({z} : Finset F) ×ˢ (Finset.univ : Finset F)) ∩ ((Finset.univ : Finset F) ×ˢ ({z} : Finset F))
      = {(z, z)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true,
      true_and, Prod.mk.injEq]
  have h3 := Finset.card_union_add_card_inter (({z} : Finset F) ×ˢ (Finset.univ : Finset F))
    ((Finset.univ : Finset F) ×ˢ ({z} : Finset F))
  rw [h2] at h3
  rw [h1]
  simp only [Finset.card_product, Finset.card_singleton, Finset.card_univ, one_mul, mul_one] at h3
  omega

theorem card_zero_split (h : ResAlg E τ q ε) {e : E} (he : e * e = e) (hτ : τ e = 1 - e) :
    Nat.card {a : E // a * τ a = 0} + 1 = 2 * q := by
  have hτf : τ (1 - e) = e := by rw [map_sub, map_one, hτ]; ring
  let g : Fx τ × Fx τ → E := fun p => (p.1 : E) * e + (p.2 : E) * (1 - e)
  have hnorm : ∀ p, g p * τ (g p) = (p.1 : E) * (p.2 : E) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    show (x * e + y * (1 - e)) * τ (x * e + y * (1 - e)) = x * y
    rw [map_add (f := _), map_mul, map_mul, hx, hy, hτ, hτf]
    linear_combination (2 * x * y - x ^ 2 - y ^ 2) * he
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      have h1 : x * e + y * (1 - e) = x' * e + y' * (1 - e) := hxy
      have h2 : x * (1 - e) + y * e = x' * (1 - e) + y' * e := by
        have := congrArg τ h1
        simpa only [map_add (f := _), map_mul, hx, hy, hx', hy', hτ, hτf] using this
      have hxe : x * e = x' * e := by
        linear_combination e * h1 + (y - y' - x + x') * he
      have hye : y * e = y' * e := by
        linear_combination e * h2 + (x - x' - y + y') * he
      have h5 : x = x' := by linear_combination h2 + hxe - hye
      have h6 : y = y' := by linear_combination h1 - hxe + hye
      subst h5 h6
      rfl
    · intro a
      refine ⟨(⟨a * e + τ a * (1 - e), ?_⟩, ⟨a * (1 - e) + τ a * e, ?_⟩), ?_⟩
      · rw [map_add (f := _), map_mul, map_mul, h.inv, hτ, hτf]; ring
      · rw [map_add (f := _), map_mul, map_mul, h.inv, hτ, hτf]; ring
      · show (a * e + τ a * (1 - e)) * e + (a * (1 - e) + τ a * e) * (1 - e) = a
        linear_combination (2 * a - 2 * τ a) * he
  have hz : ∀ p : Fx τ × Fx τ, (p.1 = zeroFx τ ∨ p.2 = zeroFx τ) ↔ g p * τ (g p) = 0 := by
    intro p
    rw [hnorm]
    constructor
    · rintro (h0 | h0)
      · rw [h0]; simp [zeroFx]
      · rw [h0]; simp [zeroFx]
    · intro h0
      by_cases hx : (p.1 : E) = 0
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr (Subtype.ext ((h.fixedUnit _ p.1.2 hx).mul_right_eq_zero.1 h0))
  have hcard : Nat.card {p : Fx τ × Fx τ // p.1 = zeroFx τ ∨ p.2 = zeroFx τ}
      = Nat.card {a : E // a * τ a = 0} :=
    Nat.card_congr ((Equiv.ofBijective g hg).subtypeEquiv hz)
  haveI := finite_of_resAlg h
  rw [← hcard, card_axes, card_fx h]

theorem card_norm_zero : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    (Nat.card {a : E // a * τ a = 0} : ℤ) = q * (1 + ε) - ε := by
  intro E _ τ q ε h
  rcases h.eps with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
  · haveI : IsDomain E := hf.isDomain
    have hu : ∀ a : {a : E // a * τ a = 0}, a = ⟨0, by simp⟩ := by
      rintro ⟨a, ha⟩
      apply Subtype.ext
      rcases mul_eq_zero.1 ha with h0 | h0
      · exact h0
      · have := h.inv a
        rw [h0, map_zero] at this
        exact this.symm
    have h1 : Nat.card {a : E // a * τ a = 0} = 1 := by
      haveI : Unique {a : E // a * τ a = 0} := ⟨⟨⟨0, by simp⟩⟩, hu⟩
      exact Nat.card_unique
    rw [h1]
    simp
  · obtain ⟨e, he, hτ⟩ := exists_idem h hf
    have h1 := card_zero_split h he hτ
    have h2 : (Nat.card {a : E // a * τ a = 0} : ℤ) + 1 = 2 * q := by exact_mod_cast h1
    linarith

end GlobalTheory.CompanionTheory.UnrDens.NormZero
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondProperty
section
open scoped TensorProduct
open Algebra.TensorProduct (includeRight)

namespace GlobalTheory.CompanionTheory.NormLoc

section

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O']

theorem trace_fixed (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1) (u : O') :
    τ (∑ j ∈ Finset.range ℓ, (τ ^ j) u) = ∑ j ∈ Finset.range ℓ, (τ ^ j) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have e := (Finset.sum_range_succ' (fun j => (τ ^ j) u) ℓ).symm.trans
    (Finset.sum_range_succ (fun j => (τ ^ j) u) ℓ)
  rw [hτ, pow_zero] at e
  rw [← add_right_cancel e]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

theorem exists_trace_one [IsLocalRing O] [Module.Finite O O'] (ℓ : ℕ) (τ : O' ≃ₐ[O] O')
    (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O'))
    (hdual : ∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) :
    ∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1 := by
  obtain ⟨x, y, hxy⟩ := hdual
  have hc : ∀ i, ∃ c : O, algebraMap O O' c = ∑ j ∈ Finset.range ℓ, (τ ^ j) (y i) := fun i =>
    hfix _ (GlobalTheory.CompanionTheory.NormLoc.trace_fixed ℓ τ hτ (y i))
  choose c hc using hc
  have hsum : ∑ i, x i * algebraMap O O' (c i) = 1 := by
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j hj => hxy j (Finset.mem_range.mp hj)]
    simp [hℓ]
  by_cases hunit : ∃ i, IsUnit (c i)
  · obtain ⟨i, u, hu⟩ := hunit
    refine ⟨algebraMap O O' (↑u⁻¹ : O) * y i, ?_⟩
    have h : ∀ j, (τ ^ j) (algebraMap O O' (↑u⁻¹ : O) * y i) =
        algebraMap O O' (↑u⁻¹ : O) * (τ ^ j) (y i) := by
      intro j
      rw [map_mul, AlgEquiv.commutes]
    simp_rw [h]
    rw [← Finset.mul_sum, ← hc i, ← map_mul, ← hu, Units.inv_mul, map_one]
  · push_neg at hunit
    have htop : (⊤ : Submodule O O') ≤ IsLocalRing.maximalIdeal O • ⊤ := by
      intro z _
      have hz : z = ∑ i, c i • (z * x i) := by
        simp_rw [Algebra.smul_def]
        calc z = z * 1 := (mul_one z).symm
          _ = _ := by
            rw [← hsum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
      rw [hz]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hunit i
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) ⊤
      Module.Finite.fg_top htop (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have h1 : (1 : O') = 0 := by
      have : (1 : O') ∈ (⊤ : Submodule O O') := Submodule.mem_top
      rw [hbot] at this
      exact this
    haveI : Subsingleton O' := subsingleton_of_zero_eq_one h1.symm
    exact ⟨0, Subsingleton.elim _ _⟩

variable {R : Type} [CommRing R] [Algebra O R]

theorem map_pow_succ_apply (τ : O' ≃ₐ[O] O') (j : ℕ) (t : O' ⊗[O] R) :
    Algebra.TensorProduct.map ((τ ^ (j + 1) : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t =
      Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R)
        (Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u r => simp [Algebra.TensorProduct.map_tmul, pow_succ']
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_pow_fixed (τ : O' ≃ₐ[O] O') (s : O' ⊗[O] R)
    (hs : Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s) (j : ℕ) :
    Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) s = s := by
  induction j with
  | zero =>
    clear hs
    induction s using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy]
  | succ j ih => rw [GlobalTheory.CompanionTheory.NormLoc.map_pow_succ_apply, ih, hs]

theorem trace_tensor_mem (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (t : O' ⊗[O] R) :
    ∑ j ∈ Finset.range ℓ,
        Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t ∈
      Set.range (includeRight : R →ₐ[O] O' ⊗[O] R) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x r =>
    obtain ⟨c, hc⟩ := hfix _ (GlobalTheory.CompanionTheory.NormLoc.trace_fixed ℓ τ hτ x)
    refine ⟨c • r, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
    rw [← TensorProduct.sum_tmul, ← hc, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb]⟩

theorem fixed_mem_range (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (a : O')
    (ha : ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) (s : O' ⊗[O] R)
    (hs : Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s) :
    s ∈ Set.range (includeRight : R →ₐ[O] O' ⊗[O] R) := by
  have key : ∑ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom)
      (AlgHom.id O R) ((a ⊗ₜ[O] (1 : R)) * s) = s := by
    simp only [map_mul, GlobalTheory.CompanionTheory.NormLoc.map_pow_fixed τ s hs]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, map_one]
    rw [← Finset.sum_mul, ← TensorProduct.sum_tmul, ha, ← Algebra.TensorProduct.one_def, one_mul]
  rw [← key]
  exact GlobalTheory.CompanionTheory.NormLoc.trace_tensor_mem ℓ τ hτ hfix _

theorem prod_one_add_tmul_sub_mem (J : Ideal R) (m : ℕ) (hm : 1 ≤ m) (r : R) (hr : r ∈ J ^ m)
    (S : Finset ℕ) (b : ℕ → O') :
    (∏ j ∈ S, (1 + b j ⊗ₜ[O] r)) - (1 + (∑ j ∈ S, b j) ⊗ₜ[O] r) ∈
      Ideal.map (includeRight : R →ₐ[O] O' ⊗[O] R) (J ^ (m + 1)) := by
  classical
  have hrr : r * r ∈ J ^ (m + 1) := by
    have h := Ideal.mul_mem_mul hr hr
    rw [← pow_add] at h
    exact Ideal.pow_le_pow_right (by omega) h
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk]
    have h : (1 + b k ⊗ₜ[O] r) * ∏ j ∈ S, (1 + b j ⊗ₜ[O] r) - (1 + (b k + ∑ j ∈ S, b j) ⊗ₜ[O] r)
        = (1 + b k ⊗ₜ[O] r) * (∏ j ∈ S, (1 + b j ⊗ₜ[O] r) - (1 + (∑ j ∈ S, b j) ⊗ₜ[O] r))
          + (b k * ∑ j ∈ S, b j) ⊗ₜ[O] (r * r) := by
      rw [TensorProduct.add_tmul, ← Algebra.TensorProduct.tmul_mul_tmul]
      ring
    rw [h]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) ?_
    have h' : (b k * ∑ j ∈ S, b j) ⊗ₜ[O] (r * r) =
        ((b k * ∑ j ∈ S, b j) ⊗ₜ[O] (1 : R)) * (includeRight : R →ₐ[O] O' ⊗[O] R) (r * r) := by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul]
    rw [h']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hrr)

end

theorem fixedRing_traceOne_firstOrder : PositivityTheory.Rg.Tf.Loc.N2 := by
  unfold PositivityTheory.Rg.Tf.Loc.N2
  intro O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hdual
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.NormLoc.exists_trace_one ℓ τ hℓ hτ hfix hdual
  refine ⟨fun s hs => GlobalTheory.CompanionTheory.NormLoc.fixed_mem_range ℓ τ hτ hfix a ha s hs, a, ha, ?_⟩
  intro m hm r hr
  have key := GlobalTheory.CompanionTheory.NormLoc.prod_one_add_tmul_sub_mem (O := O) (O' := O') (Ideal.jacobson (⊥ : Ideal R)) m hm r hr
    (Finset.range ℓ) (fun j => (τ ^ j) a)
  have e1 : ∏ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom)
      (AlgHom.id O R) (1 + a ⊗ₜ[O] r) = ∏ j ∈ Finset.range ℓ, (1 + (τ ^ j) a ⊗ₜ[O] r) :=
    Finset.prod_congr rfl fun j _ => by simp
  have e2 : (includeRight : R →ₐ[O] O' ⊗[O] R) (1 + r) =
      1 + (∑ j ∈ Finset.range ℓ, (τ ^ j) a) ⊗ₜ[O] r := by
    rw [ha, Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_add,
      ← Algebra.TensorProduct.one_def]
  rw [← e1, ← e2] at key
  exact key

end GlobalTheory.CompanionTheory.NormLoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFrobeniusRootSolution
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem solv_of_solv_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (m n k : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Pf p B → Solv B (fun t j => a t j ^ p ^ k) (fun t => c t ^ p ^ k) → Solv B a c := by
  intro p _ A _ B _ _ m n k a c hB hS
  obtain ⟨y, hy⟩ := hS
  obtain ⟨-, -, hroot, hinj, -⟩ := pf_facts p B hB
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p B hB.char k
  choose y' hy' using fun j => hroot k (y j)
  refine ⟨y', fun i => hinj k _ _ ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hF, ← hF, map_sum, hF, ← map_pow, ← hy i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hF, Algebra.smul_def, Algebra.smul_def, mul_pow, map_pow, hy' j]

end GlobalTheory.CompanionTheory.PerfectRing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorProduct
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem frobenius_symm_smul {p : ℕ} {A C : Type} [CommRing A] [CommRing C] [Algebra A C]
    (FA : A ≃+* A) (hFA : ∀ x, FA x = x ^ p) (FC : C ≃+* C) (hFC : ∀ x, FC x = x ^ p)
    (a : A) (c : C) : FC.symm (a • c) = FA.symm a • FC.symm c := by
  apply FC.injective
  rw [RingEquiv.apply_symm_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
    RingEquiv.apply_symm_apply, hFC, ← map_pow (algebraMap A C), ← hFA (FA.symm a),
    RingEquiv.apply_symm_apply]

private theorem exists_ringEquiv_frobenius_of_pf (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (h : Pf p A) :
    ∃ F : A ≃+* A, ∀ x, F x = x ^ p := by
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p A h.char 1
  have hg' : ∀ x, g x = x ^ p := fun x => by rw [hg, pow_one]
  have hb : Function.Bijective g := by
    have e : (g : A → A) = fun x => x ^ p := funext hg'
    rw [e]
    exact h.bij
  exact ⟨RingEquiv.ofBijective g hb, fun x => by rw [RingEquiv.ofBijective_apply, hg']⟩

theorem pf_tensor : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (B : Type) [CommRing B]
    [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K →
    Pf p (B ⊗[A] K) := by
  intro p _ A _ B _ _ K _ _ hA hB hK
  obtain ⟨FA, hFA⟩ := exists_ringEquiv_frobenius_of_pf p A hA
  obtain ⟨FB, hFB⟩ := exists_ringEquiv_frobenius_of_pf p B hB
  obtain ⟨FK, hFK⟩ := exists_ringEquiv_frobenius_of_pf p K hK
  have hchar : (p : B ⊗[A] K) = 0 := by
    have h := map_natCast (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] K) p
    rw [← h, hB.char, map_zero]
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (B ⊗[A] K) hchar 1
  have hg' : ∀ x, g x = x ^ p := fun x => by rw [hg, pow_one]
  let f : B →+ K →+ B ⊗[A] K :=
    AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun k => FB.symm b ⊗ₜ[A] FK.symm k)
      (fun k k' => by rw [map_add (f := _), TensorProduct.tmul_add]))
      (fun b b' => by
        ext k
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add (f := _), TensorProduct.add_tmul])
  have hf : ∀ (a : A) (b : B) (k : K), f (a • b) k = f b (a • k) := by
    intro a b k
    simp only [f, AddMonoidHom.mk'_apply]
    rw [frobenius_symm_smul FA hFA FB hFB, frobenius_symm_smul FA hFA FK hFK, TensorProduct.smul_tmul]
  have hψ : ∀ x, TensorProduct.liftAddHom f hf (g x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b k =>
      rw [hg', Algebra.TensorProduct.tmul_pow, TensorProduct.liftAddHom_tmul]
      simp only [f, AddMonoidHom.mk'_apply]
      rw [← hFB b, ← hFK k, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hgfun : (fun x : B ⊗[A] K => x ^ p) = g := funext fun x => (hg' x).symm
  refine ⟨hchar, ?_⟩
  rw [hgfun]
  refine ⟨Function.LeftInverse.injective hψ, ?_⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero g⟩
  | tmul b k =>
    obtain ⟨b', hb'⟩ := hB.bij.2 b
    obtain ⟨k', hk'⟩ := hK.bij.2 k
    have hb'' : b' ^ p = b := hb'
    have hk'' : k' ^ p = k := hk'
    refine ⟨b' ⊗ₜ[A] k', ?_⟩
    rw [hg', Algebra.TensorProduct.tmul_pow, hb'', hk'']
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add (f := _), hx', hy']⟩

end GlobalTheory.CompanionTheory.PerfectRing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialRootsOfClosedQuotientStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_roots_of_closed_quotient : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Roots ϖ := by
  first | exact @GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich | exact GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich | (intros; apply GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleOfPermStatement
section
open Zc.Comb
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_of_perm : ∀ {T : Type u} (us us' : List (List T)) (w : List T), Shuffle us w → us.Perm us' → Shuffle us' w := by
  first | exact @GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm | exact GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm | (intros; apply GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm <;> assumption)
end

