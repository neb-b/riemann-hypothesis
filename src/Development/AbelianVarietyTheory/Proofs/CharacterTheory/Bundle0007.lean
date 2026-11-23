module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumSubspaceStabilizerMulBlockFunctions
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_stabiliser_mul_blocks (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (W : Submodule F V) (Φ : Module.End F W → ℂ)
    (Φ' : Module.End F (V ⧸ W) → ℂ) :
    ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
        Φ (g.1.restrict g.2) * Φ' (W.mapQ W g.1 (fun x hx => g.2 x hx)) =
      (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) *
        ((∑ᶠ a, Φ a) * ∑ᶠ b, Φ' b) := by
  classical
  obtain ⟨s, hs⟩ := W.mkQ.exists_rightInverse_of_surjective W.range_mkQ
  have hs' : ∀ y, W.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  have hmem : ∀ x : V, (LinearMap.id - s ∘ₗ W.mkQ : V →ₗ[F] V) x ∈ W := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs',
      sub_self]
  let p : V →ₗ[F] W := LinearMap.codRestrict W _ hmem
  have hp : ∀ x : V, (p x : V) = x - s (W.mkQ x) := fun x => rfl
  have hπ : ∀ x : W, W.mkQ (x : V) = 0 := fun x => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact x.2
  have hpι : ∀ x : W, p (x : V) = x := fun x => Subtype.ext (by rw [hp, hπ, map_zero, sub_zero])
  have hps : ∀ y, p (s y) = 0 := fun y => Subtype.ext (by rw [hp, hs', sub_self]; rfl)
  let G : Module.End F W × Module.End F (V ⧸ W) × ((V ⧸ W) →ₗ[F] W) → Module.End F V :=
    fun t => W.subtype ∘ₗ t.1 ∘ₗ p + s ∘ₗ t.2.1 ∘ₗ W.mkQ + W.subtype ∘ₗ t.2.2 ∘ₗ W.mkQ
  have hG : ∀ t x, G t x = (t.1 (p x) : V) + s (t.2.1 (W.mkQ x)) + (t.2.2 (W.mkQ x) : V) :=
    fun t x => rfl
  have hGι : ∀ t (x : W), G t x = (t.1 x : V) := by
    intro t x
    rw [hG, hpι, hπ]; simp
  have hGW : ∀ t, ∀ x ∈ W, G t x ∈ W := by
    intro t x hx
    rw [hGι t ⟨x, hx⟩]; exact (t.1 _).2
  have h1 : ∀ t, (G t).restrict (hGW t) = t.1 := by
    intro t
    ext x
    rw [LinearMap.restrict_coe_apply, hGι]
  have h2 : ∀ t, W.mapQ W (G t) (fun x hx => hGW t x hx) = t.2.1 := by
    intro t
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, ← Submodule.mkQ_apply, hG, map_add (f := _), map_add (f := _),
      hπ, hπ, hs', zero_add, add_zero, Submodule.mkQ_apply]
  have h3 : ∀ t, p ∘ₗ G t ∘ₗ s = t.2.2 := by
    intro t
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply]
    rw [hG, hps, hs', map_add (f := _), map_add (f := _), hps, hpι, hpι, map_zero, zero_add, zero_add]
  let e : (Module.End F W × Module.End F (V ⧸ W) × ((V ⧸ W) →ₗ[F] W)) ≃
      {g : Module.End F V // ∀ x ∈ W, g x ∈ W} :=
    { toFun := fun t => ⟨G t, hGW t⟩
      invFun := fun g => (g.1.restrict g.2, W.mapQ W g.1 (fun x hx => g.2 x hx), p ∘ₗ g.1 ∘ₗ s)
      left_inv := fun t => Prod.ext (h1 t) (Prod.ext (h2 t) (h3 t))
      right_inv := by
        intro g
        refine Subtype.ext (LinearMap.ext fun x => ?_)
        show G _ x = _
        rw [hG]
        simp only [LinearMap.restrict_coe_apply, LinearMap.comp_apply]
        have hq : W.mapQ W g.1 (fun x hx => g.2 x hx) (W.mkQ x) = W.mkQ (g.1 (s (W.mkQ x))) := by
          conv_lhs => rw [← hs' (W.mkQ x)]
          rfl
        rw [hq, hp, hp, map_sub]
        abel }
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F W) := Module.finite_of_finite F
  haveI : Finite (Module.End F (V ⧸ W)) := Module.finite_of_finite F
  haveI : Finite ((V ⧸ W) →ₗ[F] W) := Module.finite_of_finite F
  haveI := Fintype.ofFinite (Module.End F W)
  haveI := Fintype.ofFinite (Module.End F (V ⧸ W))
  haveI := Fintype.ofFinite ((V ⧸ W) →ₗ[F] W)
  have hcard : Fintype.card ((V ⧸ W) →ₗ[F] W) =
      Nat.card F ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F),
      Module.finrank_linearMap, mul_comm]
  rw [← finsum_comp_equiv e]
  have : ∀ t, Φ ((e t).1.restrict (e t).2) * Φ' (W.mapQ W (e t).1 (fun x hx => (e t).2 x hx))
      = Φ t.1 * Φ' t.2.1 := by
    intro t
    show Φ ((G t).restrict (hGW t)) * Φ' (W.mapQ W (G t) (fun x hx => hGW t x hx)) = _
    rw [h1, h2]
  rw [finsum_congr this, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_pow]

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusCharacterOrthogonality
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem finsum_rootsOfUnity_pow_mul_star {K : Type} [Field K] (θ : K →* ℂ) {N : ℕ} (hN : 0 < N)
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) (hω : IsPrimitiveRoot (θ ζ) N) (k l : ℕ) :
    ∑ᶠ α ∈ {α : K | α ^ N = 1}, θ α ^ k * star (θ α ^ l) =
      if k ≡ l [MOD N] then ((N : ℕ) : ℂ) else 0 := by
  classical
  set ω := θ ζ with hωdef
  have hNe : N ≠ 0 := hN.ne'
  have : NeZero N := ⟨hNe⟩

  have hset : {α : K | α ^ N = 1} = (fun i : ℕ => ζ ^ i) '' (↑(Finset.range N) : Set ℕ) := by
    ext α
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one h
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i) (↑(Finset.range N) : Set ℕ) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hζ.pow_inj hi hj h
  rw [hset, finsum_mem_image hinj, finsum_mem_coe_finset]
  have hnorm : ‖ω‖ = 1 := hω.norm'_eq_one hNe
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hstar : star ω = ω⁻¹ := by
    rw [Complex.inv_eq_conj hnorm]
    rfl

  set u := ω ^ k * (ω ^ l)⁻¹ with hu
  have hterm : ∀ i, θ (ζ ^ i) ^ k * star (θ (ζ ^ i) ^ l) = u ^ i := by
    intro i
    rw [map_pow, star_pow, star_pow, hstar, hu]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hm : ∀ a, ω ^ a = ω ^ (a % N) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a N]
    rw [pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  have huN : u ^ N = 1 := by
    rw [hu, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k N, mul_comm l N, pow_mul, pow_mul,
      hω.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
  split_ifs with hkl
  · have hu1 : u = 1 := by
      rw [hu, hm k, hm l, show k % N = l % N from hkl]
      exact mul_inv_cancel₀ (pow_ne_zero _ hω0)
    simp [hu1]
  · have hu1 : u ≠ 1 := by
      intro h
      have hkl' : ω ^ k = ω ^ l := (mul_inv_eq_one₀ (pow_ne_zero _ hω0)).mp (hu ▸ h)
      apply hkl
      exact hω.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) (by rw [← hm, ← hm]; exact hkl')
    rw [geom_sum_eq hu1, huN, sub_self, zero_div]

theorem torus_orthogonality : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → (∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (Nat.card F ^ n - 1) ∧ IsPrimitiveRoot (θ ζ) (Nat.card F ^ n - 1)) ∧ ∀ k l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, θ α ^ k * star (θ α ^ l) = if k ≡ l [MOD Nat.card F ^ n - 1] then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
  intro F _ _ θ hθ n hn
  classical
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqF : ((Nat.card F : ℕ) : F) = 0 := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero F
  set q := Nat.card F with hqdef
  have hqn : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
  set N := q ^ n - 1 with hNdef
  have hN : 0 < N := by omega

  have hNF : (N : F) ≠ 0 := by
    intro h
    have h1 : ((N + 1 : ℕ) : F) = 0 := by
      rw [show N + 1 = q ^ n by omega, Nat.cast_pow, hqF, zero_pow hn.ne']
    rw [Nat.cast_add, h, zero_add, Nat.cast_one] at h1
    exact one_ne_zero h1
  have : NeZero (N : F) := ⟨hNF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'

  have hω : IsPrimitiveRoot (θ ζ) N :=
    ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl =>
      hζ.dvd_of_pow_eq_one l (hθ _ _ (pow_ne_zero _ hζ0) one_ne_zero (by rw [map_pow, hl, map_one]))⟩
  exact ⟨⟨ζ, hζ, hω⟩, fun k l => finsum_rootsOfUnity_pow_mul_star θ hN hζ hω k l⟩

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] [Finite F]


open Polynomial in
variable {F : Type} [Field F] [Finite F] in
theorem _root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow (α : AlgebraicClosure F) (m : ℕ) :
    (minpoly F α).natDegree ∣ m ↔ α ^ Nat.card F ^ m = α := by
  rw [(minpoly.irreducible (Algebra.IsIntegral.isIntegral α)).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X,
    minpoly.dvd_iff]
  simp [sub_eq_zero]


open Polynomial in
variable {F : Type} [Field F] [Finite F] in
theorem _root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range (α : AlgebraicClosure F) :
    ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots =
      (Multiset.range (minpoly F α).natDegree).map fun i => α ^ Nat.card F ^ i := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F)
  have hσ : ∀ (i : ℕ) (x : AlgebraicClosure F), (σ ^ i) x = x ^ Nat.card F ^ i := fun i x => by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Nat.card_eq_fintype_card]
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hne : (minpoly F α).map (algebraMap F (AlgebraicClosure F)) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  have key : ∀ i j, i < j → j < (minpoly F α).natDegree →
      α ^ Nat.card F ^ i = α ^ Nat.card F ^ j → False := by
    intro i j hij hj h
    have hfix : α ^ Nat.card F ^ (j - i) = α := by
      apply (σ ^ i).injective
      rw [hσ, hσ, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
      exact h.symm
    have hdvd := (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α (j - i)).mpr hfix
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hnodup : ((Multiset.range (minpoly F α).natDegree).map
      fun i => α ^ Nat.card F ^ i).Nodup := by
    refine (Multiset.nodup_range _).map_on ?_
    intro i hi j hj hij
    rw [Multiset.mem_range] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj hij).elim
    · exact h
    · exact (key j i h hi hij.symm).elim
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · rw [Multiset.le_iff_subset hnodup]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    rw [mem_roots hne, IsRoot, eval_map_algebraMap, ← hσ, aeval_algHom_apply, minpoly.aeval,
      map_zero]
  · calc ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots.card
        ≤ ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).natDegree := card_roots' _
      _ = (minpoly F α).natDegree := natDegree_map _
      _ = _ := by simp

open Polynomial in
variable {F : Type} [Field F] [Finite F] in
private theorem sum_range_mul_eq_nsmul_of_periodic {M : Type} [AddCommMonoid M] (f : ℕ → M) (d : ℕ)
    (hf : ∀ i j, f (d * j + i) = f i) (e : ℕ) :
    ∑ i ∈ Finset.range (d * e), f i = e • ∑ i ∈ Finset.range d, f i := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hf i e


open Polynomial in
variable {F : Type} [Field F] [Finite F] in
theorem _root_.GlobalTheory.CuspGL.torus_minpoly : ∀ (F : Type) [Field F] [Finite F]
    (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n →
    ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
      (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧
        ∀ k : ℕ, _root_.GlobalTheory.CuspGL.rootSum θ k
            (minpoly F α ^ (n / (minpoly F α).natDegree)) =
          ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by
  intro F _ _ θ n hn α hα
  rw [Set.mem_setOf_eq] at hα
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqn : 1 < Nat.card F ^ n := Nat.one_lt_pow (by omega) hq
  have hfix : α ^ Nat.card F ^ n = α := by
    calc α ^ Nat.card F ^ n = α ^ (Nat.card F ^ n - 1) * α := by
          rw [← pow_succ, Nat.sub_add_cancel hqn.le]
      _ = α := by rw [hα, one_mul]
  have hd := (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α n).mpr hfix
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hα
    exact zero_ne_one hα
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  refine ⟨hd, minpoly.coeff_zero_ne_zero hint hα0, fun k => ?_⟩
  obtain ⟨e, he⟩ := hd
  have hdpos : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hint
  have hper : ∀ i j, α ^ Nat.card F ^ ((minpoly F α).natDegree * j + i) =
      α ^ Nat.card F ^ i := fun i j => by
    rw [pow_add, pow_mul,
      (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α _).mp (dvd_mul_right _ _)]
  rw [he, Nat.mul_div_cancel_left e hdpos,
    sum_range_mul_eq_nsmul_of_periodic (fun i => θ (α ^ Nat.card F ^ i) ^ k) _
      (fun i j => by simp only [hper]) e]
  unfold _root_.GlobalTheory.CuspGL.rootSum
  rw [Polynomial.map_pow, roots_pow, _root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range, Multiset.map_nsmul,
    Multiset.sum_nsmul, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.GeneralLinearFunctionExtendZeroEndProperties
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] {d : ℕ}

theorem extZero_toLin_injective :
    Function.Injective fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := fun _ _ h => Units.ext (Matrix.toLin'.injective h)

theorem extZero_isUnit_iff (g : Module.End F (Fin d → F)) :
    IsUnit g ↔ ∃ x : GL (Fin d) F, Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := LinearMap.isUnit_toMatrix'_iff.mpr h
    exact ⟨u, by rw [hu, Matrix.toLin'_toMatrix']⟩
  · rintro ⟨x, rfl⟩
    exact Matrix.isUnit_toLin'_iff.mpr x.isUnit

theorem extZero_toLin (χ : GL (Fin d) F → ℂ) (x : GL (Fin d) F) :
    extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x := by
  unfold extZero
  have hs : {y : GL (Fin d) F | Matrix.toLin' (y : Matrix (Fin d) (Fin d) F) =
      Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)} = {x} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact extZero_toLin_injective.eq_iff
  rw [hs, finsum_mem_singleton]

theorem extZero_of_not_isUnit (χ : GL (Fin d) F → ℂ) (g : Module.End F (Fin d → F))
    (hg : ¬ IsUnit g) : extZero χ g = 0 := by
  unfold extZero
  have hs : {x : GL (Fin d) F | Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact hg ((extZero_isUnit_iff _).mpr ⟨x, rfl⟩)
  rw [hs, finsum_mem_empty]

theorem ipGL_eq_finsum_GL (φ φ' : Module.End F (Fin d → F) → ℂ) :
    ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) *
      star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) := by
  unfold ipGL
  have hs : {g : Module.End F (Fin d → F) | IsUnit g} =
      Set.range fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by
    ext g
    exact extZero_isUnit_iff g
  rw [hs, finsum_mem_range extZero_toLin_injective]

theorem isClassFn_extZero (χ : GL (Fin d) F → ℂ)
    (hχ : ∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) : IsClassFn (extZero χ) := by
  intro e g

  let Φ : GL (Fin d) F ≃* (Module.End F (Fin d → F))ˣ :=
    Units.mapEquiv (Matrix.toLinAlgEquiv' (R := F) (n := Fin d)).toMulEquiv
  have hcoe : ∀ x : GL (Fin d) F, ((Φ x : (Module.End F (Fin d → F))ˣ) : Module.End F (Fin d → F)) =
      Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by
    intro x
    refine LinearMap.ext fun v => ?_
    change Matrix.toLinAlgEquiv' (x : Matrix (Fin d) (Fin d) F) v = _
    rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

  let E : (Module.End F (Fin d → F))ˣ :=
    ⟨e.toLinearMap, e.symm.toLinearMap, LinearMap.ext fun v => e.apply_symm_apply v,
      LinearMap.ext fun v => e.symm_apply_apply v⟩
  have hconj : ∀ f : Module.End F (Fin d → F),
      e.conj f = (E : Module.End F (Fin d → F)) * f * ((E⁻¹ : (Module.End F (Fin d → F))ˣ) :
        Module.End F (Fin d → F)) := by
    intro f
    exact LinearMap.ext fun v => rfl
  by_cases hg : IsUnit g
  · obtain ⟨y, rfl⟩ := (extZero_isUnit_iff g).mp hg
    have hy : e.conj (Matrix.toLin' (y : Matrix (Fin d) (Fin d) F)) =
        Matrix.toLin' ((Φ.symm E * y * (Φ.symm E)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
      rw [← hcoe (Φ.symm E * y * (Φ.symm E)⁻¹), map_mul, map_mul, map_inv, Φ.apply_symm_apply, Units.val_mul, Units.val_mul,
        hcoe y, hconj]
    rw [hy, extZero_toLin, extZero_toLin]
    simpa using hχ y (Φ.symm E)⁻¹
  · have hg' : ¬ IsUnit (e.conj g) := by
      rw [hconj, Units.isUnit_mul_units, Units.isUnit_units_mul]
      exact hg
    rw [extZero_of_not_isUnit χ _ hg', extZero_of_not_isUnit χ _ hg]

theorem extZero_spec : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), (∀ x : GL (Fin d) F, extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x) ∧ (∀ g, ¬ IsUnit g → extZero χ g = 0) ∧ (∀ φ φ' : Module.End F (Fin d → F) → ℂ, ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) * star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)))) ∧ ((∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) → IsClassFn (extZero χ)) := by
  intro F _ _ d χ
  exact ⟨fun x => extZero_toLin χ x, fun g hg => extZero_of_not_isUnit χ g hg,
    fun φ φ' => ipGL_eq_finsum_GL φ φ', fun h => isClassFn_extZero χ h⟩

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedClassFunctionFromSubgroupEqFinsumCosets
section
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

theorem subgroupFunctionExtendByZero_conj_of_mem {L G : Type} [Field L] [Group G] (H : Subgroup G) (ψ : H → L)
    (hψ : ∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) (a : G) (y : H) :
    ext0 H ψ ((y : G)⁻¹ * a * y) = ext0 H ψ a := by
  unfold ext0
  by_cases ha : a ∈ H
  · have h1 : (y : G)⁻¹ * a * y ∈ H := H.mul_mem (H.mul_mem (H.inv_mem y.2) ha) y.2
    rw [dite_eq_left ha, dite_eq_left h1]
    exact hψ ⟨a, ha⟩ y
  · have h1 : ¬ (y : G)⁻¹ * a * y ∈ H := by
      intro h
      apply ha
      have h2 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem y.2 h) (H.inv_mem y.2)
      have h3 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ = a := by group
      rwa [h3] at h2
    rw [dite_eq_right ha, dite_eq_right h1]

theorem out_mul_bijective {G : Type} [Group G] (H : Subgroup G) :
    Function.Bijective (fun p : (G ⧸ H) × H => p.1.out * (p.2 : G)) := by
  constructor
  · rintro ⟨q, y⟩ ⟨q', y'⟩ h
    simp only at h
    have hq : q = q' := by
      have h1 : ((q.out * (y : G) : G) : G ⧸ H) = ((q'.out * (y' : G) : G) : G ⧸ H) := by rw [h]
      rw [QuotientGroup.mk_mul_of_mem _ y.2, QuotientGroup.mk_mul_of_mem _ y'.2,
        QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
      exact h1
    subst hq
    have : y = y' := Subtype.ext (mul_left_cancel h)
    rw [this]
  · intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul H x
    refine ⟨((x : G ⧸ H), y⁻¹), ?_⟩
    simp [hy]

theorem ind_eq_finsum_cosets : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), (∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) → ∀ g : G, ind H ψ g = ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) := by
  intro L _ _ G _ _ H ψ hψ g
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (G ⧸ H)
  have := Fintype.ofFinite H
  have hc : (Nat.card H : L) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold ind
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← (out_mul_bijective H).sum_comp (fun x : G => ext0 H ψ (x⁻¹ * g * x)), Fintype.sum_prod_type]
  have h1 : ∀ q : G ⧸ H, ∑ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G)))
      = (Nat.card H : L) * ext0 H ψ (q.out⁻¹ * g * q.out) := by
    intro q
    have h2 : ∀ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G)))
        = ext0 H ψ (q.out⁻¹ * g * q.out) := by
      intro y
      rw [← subgroupFunctionExtendByZero_conj_of_mem H ψ hψ (q.out⁻¹ * g * q.out) y]
      congr 1
      group
    simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  simp only [h1]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.BI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemOfMulMemOfForallPrimeNotDvdStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_of_mul_mem_of_forall_prime_exists_not_dvd : ∀ (X : Type) [Finite X] (S : AddSubgroup (X → ℤ)), (∀ f ∈ S, ∀ g ∈ S, f * g ∈ S) → (∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) → (1 : X → ℤ) ∈ S := by
  first | exact @GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd | exact GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd | (intros; apply GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd <;> assumption)
end

