module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletion
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pIdx_range_of_injective (p : ℕ) {A B : Type} [CommGroup A] [CommGroup B] (j : A →* B)
    (hj : Function.Injective j) : pIdx p j.range = pIdx p (⊤ : Subgroup A) := by
  have h : pows p j.range = (pows p (⊤ : Subgroup A)).map j := by
    ext x
    simp only [pows, Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_top,
      true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, map_pow _ _ _⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, (map_pow _ _ _).symm⟩
  unfold pIdx
  rw [h, MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hj]

theorem pTor_range_of_injective (p : ℕ) {A B : Type} [CommGroup A] [CommGroup B] (j : A →* B)
    (hj : Function.Injective j) : pTor p j.range = pTor p (⊤ : Subgroup A) := by
  unfold pTor
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨j x.1, ⟨x.1, rfl⟩, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩)
  · intro x y h
    exact Subtype.ext (hj (congrArg Subtype.val h))
  · rintro ⟨_, ⟨a, rfl⟩, h⟩
    exact ⟨⟨a, trivial, hj (by rw [map_pow, h, map_one])⟩, rfl⟩

theorem pTor_pIdx_subgroup_int (p : ℕ) (hp : 0 < p) (H : Subgroup (Multiplicative ℤ))
    (hH : H ≠ ⊥) : pTor p H = 1 ∧ pIdx p H = p := by
  have htor : ∀ U : Subgroup (Multiplicative ℤ), pTor p U = 1 := by
    intro U
    unfold pTor
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, U.one_mem, one_pow _⟩⟩⟩
    rw [(pow_eq_one_iff_left hp.ne').1 x.2.2, (pow_eq_one_iff_left hp.ne').1 y.2.2]
  refine ⟨htor H, ?_⟩
  obtain ⟨d, hd⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).1 inferInstance
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hH (by rw [← hd, Subgroup.zpowers_one_eq_bot])
  have hr : H = (zpowersHom (Multiplicative ℤ) d).range := by
    rw [← hd]; rfl
  have hinj : Function.Injective (zpowersHom (Multiplicative ℤ) d) := by
    intro a b h
    simp only [zpowersHom_apply] at h
    have h2 := congrArg Multiplicative.toAdd h
    simp only [toAdd_zpow, smul_eq_mul] at h2
    have hd0 : d.toAdd ≠ 0 := fun h0 => hd1 (by simpa using h0)
    exact Multiplicative.toAdd.injective (mul_right_cancel₀ hd0 h2)
  rw [hr, pIdx_range_of_injective p _ hinj]
  have h := (pIdx_top_of_fg p (Multiplicative ℤ) hp).2
  have hf : Module.finrank ℤ (Additive (Multiplicative ℤ)) = 1 := by
    rw [(AddEquiv.additiveMultiplicative ℤ).toIntLinearEquiv.finrank_eq]
    exact Module.finrank_self ℤ
  rw [h, htor, hf, pow_one, mul_one]

theorem pIdx_of_ker_eq_range (p : ℕ) (hp : 0 < p) {A B : Type} [CommGroup A] [CommGroup B]
    (j : A →* B) (hj : Function.Injective j) (g : B →* Multiplicative ℤ) (hk : g.ker = j.range)
    (hg : g.range ≠ ⊥) (N : ℕ) (hN : N ≠ 0) (h1 : pTor p (⊤ : Subgroup A) ≠ 0)
    (h2 : pIdx p (⊤ : Subgroup A) = N * pTor p (⊤ : Subgroup A)) :
    pTor p (⊤ : Subgroup B) ≠ 0 ∧ pIdx p (⊤ : Subgroup B) = p * N * pTor p (⊤ : Subgroup B) := by
  obtain ⟨r1, r2⟩ := pTor_pIdx_subgroup_int p hp g.range hg
  have k1 : pTor p g.ker = pTor p (⊤ : Subgroup A) := by
    rw [hk, pTor_range_of_injective p j hj]
  have k2 : pIdx p g.ker = N * pTor p (⊤ : Subgroup A) := by
    rw [hk, pIdx_range_of_injective p j hj, h2]
  obtain ⟨-, a2, a3⟩ := pIdx_pTor_ker_range p B (Multiplicative ℤ) g
    (by rw [k2]; exact mul_ne_zero hN h1) (by rw [k1]; exact h1) (by rw [r2]; exact hp.ne')
    (by rw [r1]; exact one_ne_zero)
  refine ⟨a2, ?_⟩
  rw [k1, k2, r1, r2] at a3
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h1)
  linarith

theorem pIdx_units_finite_extension_adicCompletion (p : ℕ) (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : ℕ) (L : Type) [Field L] [Algebra (v.adicCompletion F) L]
    [FiniteDimensional (v.adicCompletion F) L] (hp : 0 < p)
    (he : v.valuation F (p : F) = WithZero.exp (-(e : ℤ))) :
    pTor p (⊤ : Subgroup Lˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Lˣ) =
      p * (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L *
        pTor p (⊤ : Subgroup Lˣ) := by
  letI : Algebra (v.adicCompletionIntegers F) L :=
    ((algebraMap (v.adicCompletion F) L).comp
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra
  haveI : IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  haveI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap (v.adicCompletion F) L).injective
  have hinjRL : Function.Injective (algebraMap (v.adicCompletionIntegers F) L) :=
    (algebraMap (v.adicCompletion F) L).injective.comp Subtype.val_injective
  haveI : FaithfulSMul (v.adicCompletionIntegers F) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinjRL
  let O : Type := integralClosure (v.adicCompletionIntegers F) L
  haveI : Module.Finite (v.adicCompletionIntegers F) O :=
    IsIntegralClosure.finite (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  haveI : Module.Free (v.adicCompletionIntegers F) O :=
    IsIntegralClosure.module_free (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  have hrank : Module.finrank (v.adicCompletionIntegers F) O =
      Module.finrank (v.adicCompletion F) L :=
    IsIntegralClosure.rank (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  obtain ⟨⟨π₀, -, hπ₀⟩, hval, -⟩ := exists_uniformizer_and_residue_representatives F v
  obtain ⟨hc, hcard⟩ := isAdicComplete_and_card_quotient_adicCompletionIntegers F v
  have hlt : (WithZero.exp (-1) : ℤᵐ⁰) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  let π : v.adicCompletionIntegers F := ⟨algebraMap F (v.adicCompletion F) π₀, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hπ₀]; exact hlt.le⟩
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1) := hπ₀
  have hπK : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hπL : algebraMap (v.adicCompletion F) L π ≠ 0 := by
    simpa using hπK
  have hvp : Valued.v (((p : v.adicCompletionIntegers F)) : v.adicCompletion F) =
      WithZero.exp (-(e : ℤ)) := by
    rw [← he, ← hval]; simp
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hπO : algebraMap (v.adicCompletionIntegers F) O π ≠ 0 := by
    intro h
    exact hπL (congrArg Subtype.val h)
  have hcomp := isAdicComplete_span_algebraMap_of_free_finite (v.adicCompletionIntegers F) O π
    (hc π (by rw [hπ]; exact hlt))
  have hc1 : Nat.card (O ⧸ Ideal.span {(p : O)}) =
      (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L := by
    have := card_quot_span_algebraMap (v.adicCompletionIntegers F) O (p : _)
    rw [map_natCast, hcard _ e hvp, hrank] at this
    exact this
  have hc2 : Nat.card (O ⧸ Ideal.span
      {(p : O) * algebraMap (v.adicCompletionIntegers F) O π}) ≠ 0 := by
    have := card_quot_span_algebraMap (v.adicCompletionIntegers F) O ((p : _) * π)
    rw [map_mul, map_natCast, hcard _ (e + 1) (by
      rw [MulMemClass.coe_mul, map_mul, hvp, hπ, ← WithZero.exp_add]
      congr 1; push_cast; ring)] at this
    rw [this]
    exact pow_ne_zero _ (pow_ne_zero _ hq)
  obtain ⟨u1, u2⟩ := _root_.GlobalTheory.CNorm.pIdx_units_of_isAdicComplete p O _ hp hπO hcomp hc2
  rw [hc1] at u2
  have hN : ∀ x : Lˣ, Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) ≠ 0 := by
    intro x
    rw [Ne, map_eq_zero, Algebra.norm_eq_zero_iff]
    exact x.ne_zero
  let g : Lˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd
        (WithZero.log (Valued.v (Algebra.norm (v.adicCompletion F) (x : L))))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [Units.val_mul, map_mul, map_mul, WithZero.log_mul (hN x) (hN y), ofAdd_add] }
  have hg : ∀ x : Lˣ, g x = 1 ↔ Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) = 1 := by
    intro x
    change Multiplicative.ofAdd (WithZero.log _) = 1 ↔ _
    rw [ofAdd_eq_one]
    constructor
    · intro h
      rw [← WithZero.exp_log (hN x), h, WithZero.exp_zero]
    · intro h
      rw [h, WithZero.log_one]
  have hmul : ∀ x : Lˣ, Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) *
      Valued.v (Algebra.norm (v.adicCompletion F) ((x⁻¹ : Lˣ) : L)) = 1 := by
    intro x
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  let j : Oˣ →* Lˣ := Units.map ((integralClosure (v.adicCompletionIntegers F) L).val : O →* L)
  refine pIdx_of_ker_eq_range p hp j (Units.map_injective Subtype.val_injective) g ?_ ?_ _
    (pow_ne_zero _ (pow_ne_zero _ hq)) u1 u2
  · ext x
    rw [MonoidHom.mem_ker, hg]
    constructor
    · intro h
      have h' := hmul x
      rw [h, one_mul] at h'
      have i1 := (isIntegral_iff_valued_norm_le_one F v L (x : L)).2 h.le
      have i2 := (isIntegral_iff_valued_norm_le_one F v L ((x⁻¹ : Lˣ) : L)).2 h'.le
      exact ⟨⟨⟨x, i1⟩, ⟨(x⁻¹ : Lˣ), i2⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩,
        Units.ext rfl⟩
    · rintro ⟨u, rfl⟩
      have i1 := (isIntegral_iff_valued_norm_le_one F v L ((j u : Lˣ) : L)).1 (u : O).2
      have i2 := (isIntegral_iff_valued_norm_le_one F v L (((j u)⁻¹ : Lˣ) : L)).1
        ((u⁻¹ : Oˣ) : O).2
      exact eq_one_of_one_le_mul_left i1 i2 (hmul _).ge
  · intro h
    have h1 : g (Units.mk0 _ hπL) = 1 := by
      rw [← Subgroup.mem_bot, ← h]; exact ⟨_, rfl⟩
    rw [hg, Units.val_mk0, Algebra.norm_algebraMap, map_pow, hπ] at h1
    exact (pow_lt_one₀ zero_le' hlt Module.finrank_pos.ne').ne h1

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqUnitaryTransvectionMul
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Chain

theorem eventually_quad_ne {E : Type} [Field E] [CharZero E] (a b c : E) (ha : a ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, a + (t : E) * b + (t : E) ^ 2 * c ≠ 0 := by
  classical
  set p : Polynomial E := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hp
  have hp0 : p ≠ 0 := by
    intro h
    have h0 := congrArg (fun q : Polynomial E => q.coeff 0) h
    simp [p] at h0
    exact ha h0
  rw [Filter.eventually_cofinite]
  refine (Set.Finite.preimage (fun _ _ _ _ h => Rat.cast_injective h)
    (Finset.finite_toSet p.roots.toFinset)).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq, not_not] at ht
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hp0]
  show Polynomial.eval (t : E) p = 0
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  linear_combination ht

variable {E : Type} [Field E] [CharZero E] {n : ℕ}

theorem hf_line_left (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G (x + t • w) z = hf σ G x z + t * hf σ G w z := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hf_line_right (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G z (x + t • w) = hf σ G z x + σ t * hf σ G z w := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem eventually_aniso (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w : Fin n → E)
    (hx : hf σ G x x ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) (x + (t : E) • w) ≠ 0 := by
  filter_upwards [eventually_quad_ne (hf σ G x x) (hf σ G w x + hf σ G x w) (hf σ G w w) hx]
    with t ht
  have hσ : σ (t : E) = t := map_ratCast σ t
  rw [hf_line_left, hf_line_right, hf_line_right, hσ]
  intro h
  apply ht
  linear_combination h

theorem eventually_pair (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E)
    (hx : hf σ G x z ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) z ≠ 0 := by
  filter_upwards [eventually_quad_ne (hf σ G x z) (hf σ G w z) 0 hx] with t ht
  rw [hf_line_left]
  intro h
  apply ht
  linear_combination h

theorem eventually_chain (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    {ι : Type} (z : ι → Fin n → E) (l : ι → E) (x : Fin n → E) (u : E) (hx : hf σ G x x ≠ 0)
    (hu : u * σ u = 1) (hz : ∀ i, hf σ G (z i) (z i) = 0) (hxz : ∀ i, hf σ G x (z i) ≠ 0)
    (S : Finset ι) :
    ∀ᶠ t : ℚ in Filter.cofinite, ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) =
      m * tv σ G (x + (t : E) • ∑ i ∈ S, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ S, l i • z i) (x + (t : E) • ∑ i ∈ S, l i • z i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine Filter.Eventually.of_forall fun t => ⟨1, (TvGen σ G).one_mem, ?_⟩
    simp
  | @insert j S hj ih =>
    have hpair := eventually_pair σ G x (∑ i ∈ S, l i • z i) (z j) (hxz j)
    have ha1 := eventually_aniso σ G x (∑ i ∈ S, l i • z i) hx
    have ha2 := eventually_aniso σ G x (∑ i ∈ insert j S, l i • z i) hx
    filter_upwards [ih, hpair, ha1, ha2] with t hih h1 h2 h3
    obtain ⟨m, hm, hmeq⟩ := hih
    have hsplit : x + (t : E) • ∑ i ∈ insert j S, l i • z i =
        (x + (t : E) • ∑ i ∈ S, l i • z i) + ((t : E) * l j) • z j := by
      rw [Finset.sum_insert hj, smul_add, mul_smul]
      abel
    rw [hsplit] at h3 ⊢
    obtain ⟨m', hm', hm'eq⟩ :=
      GlobalTheory.T.quasiReflection_eq_mul_transvections_of_hyperbolicPlane E n σ G hG _ (z j) ((t : E) * l j) u (hz j) h1 h2 h3 hu
    exact ⟨m * m', (TvGen σ G).mul_mem hm hm', by rw [hmeq, hm'eq, mul_assoc]⟩

end GlobalTheory.UTrans.Chain

theorem GlobalTheory.UTrans.quasiReflection_eq_tvGen_mul : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) → ∀ (x y : Fin n → E) (u : E), hf σ G x x ≠ 0 → hf σ G y y ≠ 0 → u * σ u = 1 → ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) = m * tv σ G y ((u - 1) / hf σ G y y) := by
  intro E _ _ n σ G hG hiso x y u hx hy hu
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp [hf])
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (by simp [hf])
  obtain ⟨z, hli, hzp⟩ := GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors E n σ G hG hiso x y hx0 hy0
  have : Nonempty (Fin n) := by
    by_contra hne
    exact hx0 (funext fun i => (hne ⟨i⟩).elim)
  have hspan : Submodule.span E (Set.range z) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hmem : y - x ∈ Submodule.span E (Set.range z) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hmem
  have hz : ∀ i, hf σ G (z i) (z i) = 0 := fun i => (hzp i).1
  have hxz : ∀ i, hf σ G x (z i) ≠ 0 := fun i => (hzp i).2.1
  have hyz : ∀ i, hf σ G y (z i) ≠ 0 := fun i => (hzp i).2.2
  have h1 := GlobalTheory.UTrans.Chain.eventually_chain σ G hG z l x u hx hu hz hxz Finset.univ
  have h2 := GlobalTheory.UTrans.Chain.eventually_chain σ G hG z (fun i => -l i) y u hy hu hz hyz
    Finset.univ
  have hT : Filter.Tendsto (fun t : ℚ => 1 - t) Filter.cofinite Filter.cofinite :=
    (sub_right_injective : Function.Injective fun t : ℚ => 1 - t).tendsto_cofinite
  obtain ⟨t, ⟨m1, hm1, e1⟩, ⟨m2, hm2, e2⟩⟩ := (h1.and (hT.eventually h2)).exists
  have hv : y + (((1 - t : ℚ)) : E) • ∑ i ∈ Finset.univ, (-l i) • z i =
      x + (t : E) • ∑ i ∈ Finset.univ, l i • z i := by
    simp only [neg_smul, Finset.sum_neg_distrib, hl]
    push_cast
    module
  have e2' : tv σ G y ((u - 1) / hf σ G y y) =
      m2 * tv σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)
          (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)) := by
    rw [← hv]
    exact e2
  obtain ⟨-, hdet, hinv, -⟩ := (_root_.GlobalTheory.UTrans.tvGen_normal E n σ G hG).2 m2 hm2
  have hunit : IsUnit m2.det := by
    rw [hdet]
    exact isUnit_one
  refine ⟨m1 * m2⁻¹, (TvGen σ G).mul_mem hm1 hinv, ?_⟩
  rw [e1, e2', mul_assoc m1, ← mul_assoc m2⁻¹, Matrix.nonsing_inv_mul _ hunit, one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ReflGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}

omit [NumberField F] [NumberField E] in
theorem isUnE_mul {a b : Matrix (Fin n) (Fin n) E} (ha : IsUnE c G a) (hb : IsUnE c G b) :
    IsUnE c G (a * b) := by
  intro x y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]

theorem isUnE_prod (hG : IsHermForm c G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) :
    IsUnE c G (l.map fun p => refl c G p.1 p.2).prod := by
  induction l with
  | nil => intro x y; simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons]
    have hp := hl p List.mem_cons_self
    exact isUnE_mul ((GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).2.2.2 p.2 hp.2)
      (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem exists_inv (hG : IsHermForm c G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) :
    ∃ l' : List ((Fin n → E) × E), (∀ p ∈ l', hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧
      (l'.map fun p => refl c G p.1 p.2).prod * (l.map fun p => refl c G p.1 p.2).prod = 1 := by
  induction l with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    obtain ⟨-, r1, r2, -⟩ := GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1
    refine ⟨l' ++ [(p.1, c p.2)], ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact h1 q hq
      · rw [List.mem_singleton] at hq
        subst hq
        refine ⟨hp.1, ?_⟩
        show c p.2 * c (c p.2) = 1
        rw [hG.1, mul_comm]
        exact hp.2
    · rw [List.map_append, List.prod_append, List.map_cons, List.map_cons, List.prod_cons,
        List.prod_cons, List.map_nil, List.prod_nil, mul_one, mul_assoc,
        ← mul_assoc (refl c G p.1 (c p.2)), r2, mul_comm (c p.2), hp.2, r1, one_mul, h2]

theorem prod_fix (hG : IsHermForm c G) (v : Fin n → E) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ hermE c G v p.1 = 0) :
    (l.map fun p => refl c G p.1 p.2).prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
      (GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).1, hp.2]
    simp

omit [NumberField F] [NumberField E] in
theorem herm_span {v x z y : Fin n → E} (hx : hermE c G v x = 0) (hz : hermE c G v z = 0)
    (hy : y ∈ Submodule.span E {x, z}) : hermE c G v y = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hy
  have : hermE c G v (a • x + b • z) = c a * hermE c G v x + c b * hermE c G v z := by
    simp only [hermE, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, map_add, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, hx, hz]
  simp

theorem exists_fix (hG : IsHermForm c G) {γ : Matrix (Fin n) (Fin n) E} (hγ : IsUnE c G γ)
    (x : Fin n → Fin n → E) (h1 : ∀ i, hermE c G (x i) (x i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) (k : ℕ) :
    ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧
      ∀ i : Fin n, i.val < k → ((l.map fun p => refl c G p.1 p.2).prod * γ) *ᵥ x i = x i := by
  induction k with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    obtain ⟨l, hl, hfix⟩ := ih
    by_cases hk : k < n
    · have hU := isUnE_mul (isUnE_prod hG l hl) hγ
      set δ := (l.map fun p => refl c G p.1 p.2).prod * γ with hδ
      obtain ⟨m, hm, hmx⟩ := _root_.GlobalTheory.UnRep.exists_refl_prod_mulVec_eq F E c n G hG (x ⟨k, hk⟩) (δ *ᵥ x ⟨k, hk⟩) (h1 _) (hU _ _)
      refine ⟨m ++ l, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨(hm p hp).1, (hm p hp).2.1⟩
        · exact hl p hp
      · intro i hi
        rw [List.map_append, List.prod_append, mul_assoc, ← hδ, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · have hne : i ≠ ⟨k, hk⟩ := fun h => by simp [h] at hi
          rw [hfix i hi]
          refine prod_fix hG _ m fun p hp => ⟨(hm p hp).1, herm_span (h2 _ _ hne) ?_ (hm p hp).2.2⟩
          rw [← h2 _ _ hne, ← hU (x i) (x ⟨k, hk⟩), hfix i hi]
        · have : i = ⟨k, hk⟩ := Fin.ext hi
          rw [this]
          exact hmx
    · exact ⟨l, hl, fun i _ => hfix i (lt_of_lt_of_le i.2 (not_lt.1 hk))⟩

end GlobalTheory.UnRep.ReflGen

theorem GlobalTheory.UnRep.isUnE_eq_prod_refl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ γ, IsUnE c G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧ γ = (l.map fun p => refl c G p.1 p.2).prod := by
  intro F E _ _ _ _ _ c n G hG γ hγ
  obtain ⟨x, h1, h2, h3⟩ := _root_.GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis F E c n G hG
  obtain ⟨l, hl, hfix⟩ := ReflGen.exists_fix hG hγ x h1 h2 n
  obtain ⟨l', hl', hinv⟩ := ReflGen.exists_inv hG l hl
  refine ⟨l', hl', ?_⟩
  have hone : (l.map fun p => refl c G p.1 p.2).prod * γ = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range h3 fun i => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix i i.2, Matrix.one_mulVec]
  rw [← one_mul γ, ← hinv, mul_assoc, hone, mul_one]
end

