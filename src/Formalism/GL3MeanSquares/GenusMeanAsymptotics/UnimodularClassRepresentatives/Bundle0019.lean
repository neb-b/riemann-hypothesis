module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthUnitFrame
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0014
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0001

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LinearIndependentOfGramDetNeZero
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocF

open Formalism.HermitianLattices.Ext.L3.WA

section Units

variable {K : Type*} [Field K] {S : Subring K}

theorem isUnitIn_mul {a b : K} (ha : IsUnitIn S a) (hb : IsUnitIn S b) : IsUnitIn S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

theorem isUnitIn_one : IsUnitIn S (1 : K) :=
  ⟨one_ne_zero, S.one_mem, by rw [inv_one]; exact S.one_mem⟩

theorem isUnitIn_prod {ι : Type*} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, IsUnitIn S (f i)) :
    IsUnitIn S (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IsUnitIn S) (fun _ _ => isUnitIn_mul) isUnitIn_one hf

end Units

section Ring

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private lemma exists_int_algebraMap_eq_star (x : 𝓞 K) : ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = star (algebraMap (𝓞 K) K x) := by
  have hx : IsIntegral ℤ (algebraMap (𝓞 K) K x) := x.isIntegral_coe
  have : IsIntegral ℤ (star (algebraMap (𝓞 K) K x)) := hx.map (starRingEnd K).toIntAlgHom
  exact IsIntegralClosure.isIntegral_iff.mp this

private lemma hcompl_mem_prime_ideal_property {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    s ∉ p ∧ ∀ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) → t ∉ p := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h), fun t ht h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr ?_)⟩
    have : t = 1 := IsFractionRing.injective (𝓞 K) K (by rw [ht, map_one, star_one])
    rwa [this] at h
  | mul x y _ _ hx hy =>
    refine ⟨fun h => (hp.mem_or_mem h).elim hx.1 hy.1, fun t ht h => ?_⟩
    obtain ⟨x', hx'⟩ := exists_int_algebraMap_eq_star x
    obtain ⟨y', hy'⟩ := exists_int_algebraMap_eq_star y
    have : t = x' * y' := IsFractionRing.injective (𝓞 K) K (by
      rw [ht, map_mul, map_mul, hx', hy', star_mul, mul_comm])
    rw [this] at h
    exact (hp.mem_or_mem h).elim (hx.2 x' hx') (hy.2 y' hy')

private lemma hcompl_unit_property_of_isPrime {p : Ideal (𝓞 K)} (hp : p.IsPrime) {N S : 𝓞 K} (hS : S ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p)
    (hN : N ∉ p) (hfix : star (algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) =
      algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) := by
  have inj := IsFractionRing.injective (𝓞 K) K
  obtain ⟨hS1, hS2⟩ := hcompl_mem_prime_ideal_property hp hS
  have ne0 : ∀ {u : 𝓞 K}, u ∉ p → algebraMap (𝓞 K) K u ≠ 0 := fun hu h0 =>
    hu (by rw [(map_eq_zero_iff _ inj).mp h0]; exact p.zero_mem)
  obtain ⟨S', hS'⟩ := exists_int_algebraMap_eq_star S
  obtain ⟨N', hN'⟩ := exists_int_algebraMap_eq_star N
  have hS'p := hS2 S' hS'

  have key : N' * S = N * S' := inj (by
    have h := hfix
    rw [star_div₀, div_eq_div_iff (by rw [← hS']; exact ne0 hS'p) (ne0 hS1)] at h
    rw [map_mul, map_mul, hN', hS', h])
  have hN'p : N' ∉ p := fun h =>
    (hp.mem_or_mem (show N * S' ∈ p from key ▸ p.mul_mem_right S h)).elim hN hS'p
  have hNc : N ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p :=
    Submonoid.subset_closure ⟨hN, fun t ht => by rw [inj (ht.trans hN'.symm)]; exact hN'p⟩
  refine ⟨div_ne_zero (ne0 hN) (ne0 hS1), ?_, ?_⟩
  · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨S, hS, Submodule.mem_one.mpr ⟨N, by rw [mul_div_cancel₀ _ (ne0 hS1)]⟩⟩
  · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR, inv_div]
    exact ⟨N, hNc, Submodule.mem_one.mpr ⟨S, by rw [mul_div_cancel₀ _ (ne0 hN)]⟩⟩

theorem fixed_nonunit {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p)
    (hfix : star a = a) (hnu : ¬ IsUnitIn (locRing p) a) :
    ∃ r ∈ p, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s := by
  have ha' : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := ha
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at ha'
  obtain ⟨s, hs, hsa⟩ := ha'
  obtain ⟨t, ht⟩ := Submodule.mem_one.mp hsa
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := fun h0 => (hcompl_mem_prime_ideal_property hp hs).1
    (by rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mp h0]; exact p.zero_mem)
  have hat : a = algebraMap (𝓞 K) K t / algebraMap (𝓞 K) K s := by
    rw [ht, mul_div_cancel_left₀ a hs0]
  refine ⟨t, ?_, s, hs, hat⟩
  by_contra htp
  rw [hat] at hnu hfix
  exact hnu (hcompl_unit_property_of_isPrime hp hs htp hfix)

theorem locRing_local {p : Ideal (𝓞 K)} (hp : p.IsPrime) :
    ∀ a ∈ locRing p, ∀ b ∈ locRing p, star a = a → star b = b → ¬ IsUnitIn (locRing p) a →
      ¬ IsUnitIn (locRing p) b → IsUnitIn (locRing p) (a + b + 1) := by
  intro a ha b hb hfa hfb hna hnb
  have inj := IsFractionRing.injective (𝓞 K) K
  obtain ⟨r1, hr1, s1, hs1, rfl⟩ := fixed_nonunit hp ha hfa hna
  obtain ⟨r2, hr2, s2, hs2, rfl⟩ := fixed_nonunit hp hb hfb hnb
  have ne0 : ∀ {u : 𝓞 K}, u ∉ p → algebraMap (𝓞 K) K u ≠ 0 := fun hu h0 =>
    hu (by rw [(map_eq_zero_iff _ inj).mp h0]; exact p.zero_mem)
  have h1 := ne0 (hcompl_mem_prime_ideal_property hp hs1).1
  have h2 := ne0 (hcompl_mem_prime_ideal_property hp hs2).1
  have hS : s1 * s2 ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := Submonoid.mul_mem _ hs1 hs2
  have hN : r1 * s2 + r2 * s1 + s1 * s2 ∉ p := by
    intro h
    have : s1 * s2 ∈ p := by
      have := p.sub_mem h (p.add_mem (p.mul_mem_right s2 hr1) (p.mul_mem_right s1 hr2))
      simpa using this
    exact (hcompl_mem_prime_ideal_property hp hS).1 this
  have e : algebraMap (𝓞 K) K r1 / algebraMap (𝓞 K) K s1 + algebraMap (𝓞 K) K r2 / algebraMap (𝓞 K) K s2 + 1 =
      algebraMap (𝓞 K) K (r1 * s2 + r2 * s1 + s1 * s2) / algebraMap (𝓞 K) K (s1 * s2) := by
    simp only [map_add (f := _), map_mul]
    field_simp
  have hf := congrArg id (show star (algebraMap (𝓞 K) K r1 / algebraMap (𝓞 K) K s1 +
      algebraMap (𝓞 K) K r2 / algebraMap (𝓞 K) K s2 + 1) = _ by rw [star_add, star_add, star_one, hfa, hfb])
  rw [e] at hf ⊢
  exact hcompl_unit_property_of_isPrime hp hS hN hf

theorem isUnitIn_algebraMap_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r) ↔ r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have inj := IsFractionRing.injective (𝓞 K) K
  constructor
  · rintro ⟨h0, -, hinv⟩
    have hinv' : (algebraMap (𝓞 K) K r)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := hinv
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at hinv'
    obtain ⟨s, hs, hsr⟩ := hinv'
    obtain ⟨t, ht⟩ := Submodule.mem_one.mp hsr
    have hst : s = t * r := inj (by rw [map_mul, ht, mul_assoc, inv_mul_cancel₀ h0, mul_one])
    obtain ⟨hs1, hs2⟩ := hcompl_mem_prime_ideal_property hp hs
    refine Submonoid.subset_closure ⟨fun h => hs1 (hst ▸ p.mul_mem_left t h), fun u hu hup => ?_⟩
    obtain ⟨t', ht'⟩ := exists_int_algebraMap_eq_star t
    apply hs2 (t' * u) _ (p.mul_mem_left t' hup)
    rw [map_mul, ht', hu, hst, map_mul, star_mul, mul_comm]
  · intro hr
    obtain ⟨hr1, -⟩ := hcompl_mem_prime_ideal_property hp hr
    have h0 : algebraMap (𝓞 K) K r ≠ 0 := fun h0 =>
      hr1 (by rw [(map_eq_zero_iff _ inj).mp h0]; exact p.zero_mem)
    refine ⟨h0, ?_, ?_⟩
    · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
      rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
      exact ⟨1, Submonoid.one_mem _, Submodule.mem_one.mpr ⟨r, by rw [map_one, one_mul]⟩⟩
    · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
      rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
      exact ⟨r, hr, Submodule.mem_one.mpr ⟨1, by rw [map_one, mul_inv_cancel₀ h0]⟩⟩

end Ring

section Gram

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}

theorem gram_mulVec (x : Fin n → V) (c : Fin n → K) (i : Fin n) :
    ((Matrix.of fun i j => h (x i) (x j)) *ᵥ c) i = h (x i) (∑ j, c j • x j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_smul, smul_eq_mul, mul_comm]

theorem linearIndependent_of_gram_det_ne_zero (x : Fin n → V)
    (hdet : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0) : LinearIndependent K x := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hG : (Matrix.of fun i j => h (x i) (x j)) *ᵥ c = 0 := by
    funext i
    rw [gram_mulVec h x c i, hc, map_zero, Pi.zero_apply]
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hG) i

theorem gram_det_ne_zero (hd : ∀ x, h x x = 0 → x = 0) (x : Fin n → V)
    (hli : LinearIndependent K x) : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have e : ∀ i, h (x i) (∑ j, v j • x j) = 0 := fun i => by
    rw [← gram_mulVec h x v i, hv, Pi.zero_apply]
  have e' : ∀ i, h (v i • x i) (∑ j, v j • x j) = 0 := fun i => by
    rw [map_smulₛₗ, LinearMap.smul_apply, e, smul_zero]
  have hy : h (∑ j, v j • x j) (∑ j, v j • x j) = 0 := by
    have hs : h (∑ j, v j • x j) = ∑ j, h (v j • x j) := map_sum h _ _
    rw [hs, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => e' i
  have := Fintype.linearIndependent_iff.mp hli v (hd _ hy)
  exact hv0 (funext this)

theorem star_gram_det (hs : h.IsSymm) (x : Fin n → V) :
    star (Matrix.of fun i j => h (x i) (x j)).det = (Matrix.of fun i j => h (x i) (x j)).det := by
  rw [← Matrix.det_conjTranspose]
  congr 1
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  first
  | exact hs.eq (x j) (x i)
  | exact hs (x j) (x i)

end Gram

section Cramer

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}

theorem det_smul_mem {L : Submodule (𝓞 K) V} (x : Fin n → V) (hx : ∀ i, x i ∈ L)
    (hspan : Submodule.span K (Set.range x) = ⊤) (g : Matrix (Fin n) (Fin n) (𝓞 K))
    (hg : ∀ i j, algebraMap (𝓞 K) K (g i j) = h (x i) (x j)) (y : V)
    (hy : ∀ i, h (x i) y ∈ (1 : Submodule (𝓞 K) K)) : g.det • y ∈ L := by
  have hy' : y ∈ Submodule.span K (Set.range x) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy'
  choose β hβ using fun i => Submodule.mem_one.mp (hy i)
  set G := Matrix.of fun i j => h (x i) (x j) with hGdef
  have hGg : (algebraMap (𝓞 K) K).mapMatrix g = G := by
    ext i j
    simp [RingHom.mapMatrix_apply, hg, hGdef]
  have hGc : G *ᵥ c = fun i => algebraMap (𝓞 K) K (β i) := by
    funext i
    rw [hGdef, gram_mulVec h x c i, hc, hβ]

  have hdetc : G.det • c = fun j => algebraMap (𝓞 K) K ((g.adjugate *ᵥ β) j) := by
    funext j
    have h1 : G.det • c = G.adjugate *ᵥ (G *ᵥ c) := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
      first
      | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      | simp
    rw [h1, hGc, RingHom.map_mulVec, ← hGg, ← RingHom.map_adjugate]
    rfl
  have hdet : algebraMap (𝓞 K) K g.det = G.det := by rw [RingHom.map_det, hGg]
  rw [← algebraMap_smul K g.det y, hdet, ← hc, Finset.smul_sum]
  have hj : ∀ j, G.det • (c j • x j) = (g.adjugate *ᵥ β) j • x j := by
    intro j
    have := congrFun hdetc j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [smul_smul, this, algebraMap_smul]
  rw [Finset.sum_congr rfl fun j _ => hj j]
  exact L.sum_mem fun j _ => L.smul_mem _ (hx j)

end Cramer

end Formalism.HermitianLattices.Ext.L3.LocF
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MeanB

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_star_ne (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ θ : K, star θ ≠ θ := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 K)
  obtain ⟨θ, t, e, h⟩ := hK.2.2 P hP
  refine ⟨algebraMap (𝓞 K) K θ, fun h' => h ?_⟩
  rw [h'] at e
  have : t = θ := RingOfIntegers.coe_injective e
  rw [this, sub_self]; exact P.zero_mem

theorem star_algebraMap (hF : IsFixF K F) (a : F) : star (algebraMap F K a) = algebraMap F K a :=
  (hF _).2 ⟨a, rfl⟩

theorem finrank_eq_two (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) : finrank F K = 2 := by
  obtain ⟨θ, hθ⟩ := exists_star_ne hK
  set δ : K := θ - star θ with hδ
  have hδ0 : δ ≠ 0 := fun h => hθ (sub_eq_zero.1 h).symm
  have hsδ : star δ = -δ := by rw [hδ, star_sub, star_star]; ring
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hli : LinearIndependent F ![(1 : K), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t e
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at e
    have e' := congrArg star e
    rw [star_add, star_mul', star_algebraMap hF, star_algebraMap hF, hsδ, star_zero] at e'
    have hs : algebraMap F K s = 0 := by
      have : 2 * algebraMap F K s = 0 := by linear_combination e + e'
      exact (mul_eq_zero.1 this).resolve_left h2
    have ht : algebraMap F K t = 0 := by
      rw [hs, zero_add] at e
      exact (mul_eq_zero.1 e).resolve_right hδ0
    exact ⟨(map_eq_zero _).1 hs, (map_eq_zero _).1 ht⟩
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), δ]) := by
    intro a _
    obtain ⟨f1, hf1⟩ := (hF ((a + star a) / 2)).1 (by
      rw [star_div₀, star_add, star_star, star_ofNat, add_comm])
    obtain ⟨f2, hf2⟩ := (hF ((a - star a) / (2 * δ))).1 (by
      rw [star_div₀, star_sub, star_star, star_mul', star_ofNat, hsδ]
      field_simp
      ring)
    have : Set.range ![(1 : K), δ] = {1, δ} := by
      simp [Matrix.range_cons, Set.pair_comm]
    rw [this, Submodule.mem_span_pair]
    refine ⟨f1, f2, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, hf1, hf2]
    field_simp
    ring
  have := finrank_eq_card_basis (Basis.mk hli hsp)
  simpa using this

theorem algebraMap_comp (a : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (a : F) := rfl

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem card_quot_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V * k) := by
  let _ : Module F V := Module.compHom V (algebraMap F K)
  have t1 : IsScalarTower F K V := ⟨fun a b v => by
    change (a • b) • v = (algebraMap F K a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let _ : Module (𝓞 F) V := Module.compHom V (algebraMap (𝓞 F) (𝓞 K))
  have t2 : IsScalarTower (𝓞 F) (𝓞 K) V := ⟨fun a b v => by
    change (a • b) • v = (algebraMap (𝓞 F) (𝓞 K) a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have t3 : IsScalarTower (𝓞 F) F V := ⟨fun a b v => by
    change (algebraMap F K (a • b)) • v = (algebraMap (𝓞 F) (𝓞 K) a) • ((algebraMap F K b) • v)
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) a), algebraMap_comp, Algebra.smul_def, map_mul,
      mul_smul]⟩
  have : FiniteDimensional F V := FiniteDimensional.trans F K V
  have hrank : finrank F V = 2 * finrank K V := by
    rw [← finrank_mul_finrank F K V, finrank_eq_two hK hF]
  let M : Submodule (𝓞 F) V := L.restrictScalars (𝓞 F)
  let e : ↥M ≃ₗ[𝓞 F] ↥L := (Submodule.restrictScalarsEquiv (𝓞 F) (𝓞 K) V L).restrictScalars (𝓞 F)
  have hfg : M.FG := by
    have : Module.Finite (𝓞 K) ↥L := Module.Finite.iff_fg.2 hL.fg
    have : Module.Finite (𝓞 F) ↥L := Module.Finite.trans (𝓞 K) ↥L
    exact Module.Finite.iff_fg.1 (Module.Finite.equiv e.symm)
  have hspan : Submodule.span F (M : Set V) = ⊤ := by
    have key : ∀ (a : K), ∀ w ∈ Submodule.span F (M : Set V), a • w ∈ Submodule.span F (M : Set V) := by
      intro a w hw
      induction hw using Submodule.span_induction with
      | mem l hl =>
        obtain ⟨d, hd, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2
          (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a)).exists_integral_multiple
        let z : 𝓞 K := ⟨d • a, hint⟩
        have hz : algebraMap (𝓞 K) K z = d • a := rfl
        have hd' : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
        have : a • l = ((d : F)⁻¹) • (z • l) := by
          rw [← algebraMap_smul K z l, hz, ← algebraMap_smul K ((d : F)⁻¹), smul_smul, map_inv₀,
            map_intCast, zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Int.cast_ne_zero.2 hd), one_mul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (L.smul_mem z hl))
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul f x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro v hv0
    clear hv0
    have hv : v ∈ Submodule.span K (L : Set V) := hL.span_eq_top ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem l hl => exact Submodule.subset_span hl
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact key a x hx
  have main := MeanA.card_quot_pow_smul_top (F := F) M hfg hspan h𝔭 k
  have hQ : Nat.card (𝓞 F ⧸ 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ k := by
    rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hmap : (𝔭 ^ k • ⊤ : Submodule (𝓞 F) ↥M).map (e : ↥M →ₗ[𝓞 F] ↥L) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L).restrictScalars (𝓞 F) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, extP, ← Ideal.map_pow,
      Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  have e1 := Submodule.Quotient.equiv _ _ e hmap
  have e2 := Submodule.Quotient.restrictScalarsEquiv (𝓞 F)
    ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)
  rw [← Nat.card_congr e2.toEquiv, ← Nat.card_congr e1.toEquiv, main, hQ, hrank, ← pow_mul]
  congr 1; ring

theorem exists_star_int (a : 𝓞 K) : ∃ a' : 𝓞 K, algebraMap (𝓞 K) K a' = star (algebraMap (𝓞 K) K a) :=
  ⟨⟨star (algebraMap (𝓞 K) K a), map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe a)⟩, rfl⟩

theorem star_mem_extP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    ∃ z' ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z' = star (algebraMap (𝓞 K) K z) := by
  rw [extP, ← Ideal.map_pow, Ideal.map] at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨_, Ideal.subset_span ⟨t, ht, rfl⟩, by rw [algebraMap_comp, star_algebraMap hF]⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    exact ⟨x' + y', add_mem hx' hy', by rw [map_add (f := _), map_add (f := _), star_add, ex, ey]⟩
  | smul a x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨a', ea⟩ := exists_star_int a
    exact ⟨a' * x', Ideal.mul_mem_left _ _ hx', by
      rw [smul_eq_mul, map_mul, map_mul, star_mul', ex, ea]⟩

theorem comap_extP_pow (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (extP K 𝔭 ^ k).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 ^ k := by
  rw [extP, ← Ideal.map_pow, Ideal.comap_map_eq_self_of_faithfullyFlat]

theorem congrP_algebraMap_iff_sub_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a b : 𝓞 F) :
    CongrP (K := K) 𝔭 k (algebraMap F K (a : F)) (algebraMap F K (b : F)) ↔ a - b ∈ 𝔭 ^ k := by
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    have : z = algebraMap (𝓞 F) (𝓞 K) (t * (a - b)) := by
      apply RingOfIntegers.coe_injective
      rw [e, algebraMap_comp]
      simp
    rw [this, ← Ideal.mem_comap, comap_extP_pow] at hz
    exact MeanA.mem_pow_of_mul_mem h𝔭 ht hz
  · intro h
    refine ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), algebraMap (𝓞 F) (𝓞 K) (a - b), ?_, ?_⟩
    · rw [← Ideal.mem_comap, comap_extP_pow]; exact h
    · rw [algebraMap_comp]; simp

section form

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}

theorem exists_val (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (y : ↥L) :
    ∃ n : 𝓞 F, h (y : V) (y : V) = algebraMap F K (n : F) := by
  obtain ⟨a, ha⟩ := (hF (h y y)).1 (hs.eq y y)
  obtain ⟨z, hz⟩ := Submodule.mem_one.1 (hLi y y.2 y y.2)
  have hint : IsIntegral ℤ a := by
    rw [← isIntegral_algebraMap_iff (B := K), ha, ← hz]
    exact RingOfIntegers.isIntegral_coe z
  exact ⟨⟨a, hint⟩, ha.symm⟩

theorem form_mem_right (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (u : ↥L) {w : ↥L}
    (hw : w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (u : V) (w : V) := by
  induction hw using Submodule.smul_induction_on' with
  | smul a ha v _ =>
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hLi u u.2 v v.2)
    refine ⟨a * c, Ideal.mul_mem_right _ _ ha, ?_⟩
    rw [map_mul, hc, Submodule.coe_smul, ← algebraMap_smul K a (v : V), map_smul, smul_eq_mul]
  | add a _ b _ ha hb =>
    obtain ⟨x', hx', ex⟩ := ha
    obtain ⟨y', hy', ey⟩ := hb
    exact ⟨x' + y', add_mem hx' hy', by rw [map_add (f := _), ex, ey, Submodule.coe_add, map_add (f := _)]⟩

theorem val_congr (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (𝔭 : Ideal (𝓞 F)) (k : ℕ) {y y' : ↥L} {n n' : 𝓞 F}
    (hy : y - y' ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L))
    (e : h (y : V) (y : V) = algebraMap F K (n : F))
    (e' : h (y' : V) (y' : V) = algebraMap F K (n' : F)) : n - n' ∈ 𝔭 ^ k := by
  obtain ⟨z1, hz1, e1⟩ := form_mem_right hLi 𝔭 k y' hy
  obtain ⟨z2, hz2, e2⟩ := form_mem_right hLi 𝔭 k (y - y') hy
  obtain ⟨z3, hz3, e3⟩ := star_mem_extP hF 𝔭 k hz1
  rw [← comap_extP_pow (K := K), Ideal.mem_comap]
  have : algebraMap (𝓞 F) (𝓞 K) (n - n') = z1 + z2 + z3 := by
    apply RingOfIntegers.coe_injective
    have h3 : star (h (y' : V) ((y - y' : ↥L) : V)) = h ((y - y' : ↥L) : V) (y' : V) := hs.eq _ _
    rw [algebraMap_comp, map_add (f := _), map_add (f := _), e1, e2, e3, e1, h3]
    have : algebraMap F K ((n - n' : 𝓞 F) : F) = algebraMap F K (n : F) - algebraMap F K (n' : F) := by
      simp
    rw [this, ← e, ← e']
    simp only [Submodule.coe_sub, map_sub, LinearMap.sub_apply]
    ring
  rw [this]
  exact add_mem (add_mem hz1 hz2) hz3

end form

end Formalism.HermitianLattices.Ext.L3.MeanB
end
end

