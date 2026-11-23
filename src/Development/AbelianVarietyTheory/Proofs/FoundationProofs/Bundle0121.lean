module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankGeOfGenericFreeRowsFirst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankLeRootExchange
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelIdempotentLowerBoundGeneric
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem one_le_rk_of_not_sharp (g : ℕ) [Fact g.Prime] (N : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M) (hρ : IsGeneric ρ) (L : Lev g N)
    (hL : L.sharp = false) : 1 ≤ rk ρ L.e := by
  obtain ⟨L₀, h₀, x, hx, hu⟩ := hρ
  let L' : Lev g N := { L₀ with s := L.s, k := L.k, hk := L.hk }
  have hs : L'.sharp = false := h₀
  rw [_root_.GlobalTheory.BadShare.CoDiag.rk_e_eq g N M ρ L L' (hL.trans hs.symm) rfl rfl]
  obtain ⟨a1, a2, a3, a4, -⟩ := _root_.GlobalTheory.BadShare.LevGroup.lev_group g N L'
  obtain ⟨-, -, -, h⟩ := _root_.GlobalTheory.BadShare.EpsProj.eps_spec (GG g N) M ρ L'.Mem L'.chi a1 a2 a3 a4
  refine h 1 (fun _ => x) (linearIndependent_unique_iff.2 hx) ?_
  intro i u hm
  have hchi : L'.chi u = L₀.chi u := by
    simp only [Lev.chi, Lev.Edge, hs, h₀, Bool.false_eq_true, if_false]
    rfl
  rw [hchi]
  exact hu u hm.1

theorem rk_lower_of_sharp (g : ℕ) [Fact g.Prime] (N : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M) (hρ : IsGeneric ρ) (s : ℕ) :
    ∀ L : Lev g N, L.sharp = true → L.s = s → (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  induction s with
  | zero => exact fun L h1 h2 => _root_.GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero g N M ρ hρ L h1 h2
  | succ s ih =>
    intro L h1 h2
    have hk : s + L.k < N := by have := L.hk; omega
    let L' : Lev g N := { L with s := s, hk := hk }
    have h3 := ih L' h1 rfl
    have h4 := _root_.GlobalTheory.BadShare.RxStep.rk_le_step g N M ρ L L' h1 h1 rfl h2
    exact h3.trans (by exact_mod_cast h4)

theorem rk_lev_lower : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, (1 - 1 / (g : ℝ)) * (g : ℝ) ^ (if L.sharp = true then L.k else 0) ≤ (rk ρ L.e : ℝ) := by
  intro g _ N M _ _ _ ρ hρ L
  by_cases h : L.sharp = true
  · rw [if_pos h]
    exact rk_lower_of_sharp g N M ρ hρ L.s L h rfl
  · rw [if_neg h, pow_zero, mul_one]
    have h1 : (1 : ℝ) ≤ rk ρ L.e := by
      exact_mod_cast one_le_rk_of_not_sharp g N M ρ hρ L (by simpa using h)
    have h2 : (0 : ℝ) ≤ 1 / (g : ℝ) := by positivity
    linarith

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueLinearDisjointnessCoeffLtOneStatement
section
open scoped MatrixGroups NNReal
open Polynomial GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_linear_disjointness_coeff_lt_one :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) →
      v (p : Ω) < 1 → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω),
      IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p),
      (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) →
      v (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) < 1 →
      ∀ r : ℤ, v (∑ t, e t * zp Ω ((a t).coeff r)) < 1 := by
  intro p hp Ω _ _ hC v hv hvp T n ψ hψ d e a he hsum r
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hqq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hq) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hint : ∀ x, ψ x ∈ v.valuationSubring := by
    intro x
    have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [hψ.rng] at hx
    exact (hv _).2 (adjoin_le_integralClosure hqq hx)
  have hzp : ∀ z : ℤ_[p], ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z)) = zp Ω z := by
    intro z
    refine hψ.sub _ _ (fun i => ?_) (fun r hr => ?_)
    · by_cases hi : i = 0
      · simp [hi]
      · have : (p : ℤ) ^ n * i ≠ 0 := mul_ne_zero (by exact_mod_cast hq) hi
        simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne this, HahnSeries.coeff_single_of_ne hi]
    · have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
      simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne this]
  let A := v.valuationSubring
  let k := IsLocalRing.ResidueField A
  let ρ : A →+* k := IsLocalRing.residue A
  have hρ : ∀ x : A, ρ x = 0 ↔ v (x : Ω) < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  let g : Lau p →+* A := (ψ.comp (algebraMap (Lau p) (O0 p))).codRestrict A (fun x => hint _)
  have hp0 : (p : k) = 0 := by
    rw [← map_natCast ρ, hρ]
    simpa using hvp
  have : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 hp0
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have hker : RingHom.ker (LauZ.red p) ≤ RingHom.ker (ρ.comp g) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (Basic.dvd_iff_map p x).2 hx
    rw [RingHom.mem_ker, map_mul, map_natCast, hp0, zero_mul]
  let φ : LaurentSeries (ZMod p) →+* k :=
    RingHom.liftOfRightInverse (LauZ.red p) (LauZ.lift p) (LauZ.red_lift p) ⟨ρ.comp g, hker⟩
  have hφ : ∀ x, φ (LauZ.red p x) = ρ (g x) := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨ρ.comp g, hker⟩ x
  have hCz : ∀ z : ℤ_[p], ρ (g (HahnSeries.C z)) = algebraMap (ZMod p) k (PadicInt.toZMod z) := by
    intro z
    have h1 : LauZ.red p (HahnSeries.C z) = HahnSeries.C (PadicInt.toZMod z) := by
      ext i
      rw [LauZ.red_coeff]
      by_cases hi : i = 0
      · simp [hi]
      · simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hi]
    rw [← hφ, h1]
    exact DFunLike.congr_fun (Subsingleton.elim (φ.comp HahnSeries.C) (algebraMap (ZMod p) k)) _
  let E : Fin d → A := fun t => ⟨e t, (hv _).2 (he t).1⟩
  let g0 : ℤ_[p] →+* A := g.comp HahnSeries.C
  have hg0 : (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p)) = A.subtype.comp g0 := by
    ext z
    have h2 : algebraMap ℤ_[p] (O0 p) z = algebraMap (Lau p) (O0 p) (HahnSeries.single 0 z) := by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] (Lau p) (O0 p)]
      congr 1
      ext i
      simp [HahnSeries.algebraMap_apply']
    show algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) z) = ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z))
    rw [hzp, h2, zp]
  have exists_prim (P : ℤ_[p][X]) (hP : P ≠ 0) :
      ∃ (c : ℤ_[p]) (Q : ℤ_[p][X]), c ≠ 0 ∧ P = C c * Q ∧ Q.map (PadicInt.toZMod (p := p)) ≠ 0 := by
    classical
    let : NormalizedGCDMonoid ℤ_[p] := Classical.arbitrary _
    refine ⟨P.content, P.primPart, by rwa [Ne, content_eq_zero_iff], P.eq_C_content_mul_primPart, ?_⟩
    intro h0
    have hd : ∀ n, (p : ℤ_[p]) ∣ P.primPart.coeff n := by
      intro n
      have := congrArg (fun Q => Q.coeff n) h0
      simp only [coeff_map, coeff_zero] at this
      rwa [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton] at this
    exact PadicInt.prime_p.not_isUnit
      (isPrimitive_primPart P (p : ℤ_[p]) ((C_dvd_iff_dvd_coeff _ _).2 hd))
  have halg : ∀ t, IsAlgebraic (ZMod p) (ρ (E t)) := by
    intro t
    obtain ⟨P, hP, hPe⟩ := (he t).2
    obtain ⟨c, Q, hc, rfl, hQ⟩ := exists_prim P hP
    refine ⟨_, hQ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hg0, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hPe
    have hc' : (A.subtype.comp g0) c ≠ 0 := by
      have : CharZero Ω := Basic.charZero_of_isClo hC
      obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc PadicInt.irreducible_p
      rw [map_mul, map_pow, map_natCast]
      exact mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
    have h1 := (mul_eq_zero.1 hPe).resolve_left hc'
    have h2 : Q.eval₂ g0 (E t) = 0 := by
      apply A.subtype_injective
      rw [Polynomial.hom_eval₂, map_zero]
      exact h1
    have h3 := congrArg ρ h2
    rw [Polynomial.hom_eval₂, map_zero] at h3
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← h3]
    congr 1
    ext z
    exact (hCz z).symm
  obtain ⟨f, hf, hfix⟩ := ResDisj.exists_pow_eq _ halg
  have hrel : ∑ t, ρ (E t) * φ (LauZ.red p (a t)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hφ, ← map_mul, ← map_sum]
    rw [hρ]
    convert hsum using 2
    exact map_sum A.subtype _ _
  have hres :=
    ResDisj.coeff_rel_of_pow φ hf _ hfix Finset.univ _ (fun t ht => absurd (Finset.mem_univ t) ht) hrel r
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LauZ.red_coeff, ← hCz, ← map_mul, ← map_sum] at hres
  rw [hρ] at hres
  convert hres using 2
  refine Eq.trans ?_ (map_sum A.subtype _ _).symm
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← hzp]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueTowerPowersLinearIndependent
section
open GlobalTheory.K5

namespace GlobalTheory.K5.ResidueIndep

open Polynomial

theorem field_indep {k : Type} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (K : Subfield k)
    (N : ℕ) (t : k) (ha : t ^ p ^ N ∈ K) (hna : ∀ b ∈ K, b ^ p ≠ t ^ p ^ N)
    (c : ℕ → k) (hc : ∀ j < p ^ N, c j ∈ K)
    (hs : ∑ j ∈ Finset.range (p ^ N), c j * t ^ j = 0) : ∀ j < p ^ N, c j = 0 := by
  classical
  haveI : ExpChar K p := ExpChar.prime hp.out
  obtain ⟨n, y, hf⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C (F := K) p (x := t)).1
    ((minpoly.natSepDegree_eq_one_iff_pow_mem (F := K) p (x := t)).2 ⟨N, ⟨⟨_, ha⟩, rfl⟩⟩)
  have hy : t ^ p ^ n = (y : k) := by
    have := minpoly.aeval K t
    rw [hf] at this
    simp only [map_sub, map_pow, aeval_X, aeval_C] at this
    exact sub_eq_zero.1 this
  have hNn : N ≤ n := by
    by_contra h
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.1 h)
    refine hna ((y : k) ^ p ^ r) (K.pow_mem y.2 _) ?_
    rw [← hy, ← pow_mul, ← pow_mul, pow_add, pow_add, pow_one, mul_assoc]
  let c' : ℕ → K := fun j => if h : j < p ^ N then ⟨c j, hc j h⟩ else 0
  let P : K[X] := ∑ j ∈ Finset.range (p ^ N), monomial j (c' j)
  have hP : aeval t P = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hs, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [aeval_monomial]
    simp only [c', dif_pos (Finset.mem_range.1 hj)]
    rfl
  have hP0 : P = 0 := by
    by_contra h
    have h1 := minpoly.degree_le_of_ne_zero K t h hP
    have h2 : P.degree < ((p ^ N : ℕ) : WithBot ℕ) := by
      refine (degree_sum_le _ _).trans_lt ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro j hj
      exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast Finset.mem_range.1 hj)
    rw [hf, degree_X_pow_sub_C (pow_pos hp.out.pos n)] at h1
    have h3 := h1.trans_lt h2
    have h4 : p ^ n < p ^ N := by exact_mod_cast h3
    exact absurd (Nat.pow_le_pow_right hp.out.pos hNn) (not_le.2 h4)
  intro j hj
  have h1 : P.coeff j = c' j := by
    simp [P, coeff_monomial, Finsupp.single_apply] <;> omega
  rw [hP0, coeff_zero] at h1
  have h2 := congrArg Subtype.val h1
  simp only [c', dif_pos hj] at h2
  exact h2.symm

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem mem_rad_iff (h : IsClo p Ω) (x : integralClosure (O0 p) Ω) :
    x ∈ (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical ↔
      ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((x : Ω) ^ m / (p : Ω)) := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hn
    refine ⟨n + 1, n.succ_pos, ?_⟩
    have h1 : (z : Ω) * p = (x : Ω) ^ n := by exact_mod_cast congrArg Subtype.val hz
    have h2 : (x : Ω) ^ (n + 1) / p = ((z * x : integralClosure (O0 p) Ω) : Ω) := by
      rw [pow_succ, ← h1]; push_cast; field_simp
    rw [h2]
    exact (z * x).2
  · rintro ⟨m, -, hm⟩
    refine ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hm⟩, Subtype.ext ?_⟩⟩
    push_cast
    field_simp

theorem isInt_inv (h : IsClo p Ω) (x : Ω)
    (hx : ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) (x ^ m / (p : Ω))) : x ≠ 0 ∧ IsInt (p := p) x⁻¹ := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpi : IsIntegral (O0 p) (p : Ω) := by exact_mod_cast Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx ⟨1, one_pos, by simpa [IsInt] using isIntegral_zero⟩
  refine ⟨hx0, ?_⟩
  have hIntegral : ∃ (a : ℤ) (b : ℕ), 0 < b ∧
      IsIntegral (O0 p) (x ^ b / (p : Ω) ^ a) ∧
      IsIntegral (O0 p) ((p : Ω) ^ a / x ^ b) := by
    obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hmax]
      exact o0_isAdicComplete_span_p p
    have : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj
    let _ : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
    have : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
      FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
    have : Algebra.IsAlgebraic (O0 p) Ω := h.alg
    have : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
      Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
    simpa only [map_natCast] using
      exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p) hirr x hx0
  obtain ⟨a, b, hb, h1, h2⟩ := hIntegral
  by_cases ha : 0 < a
  · exfalso
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = (n + 1 : ℕ) := ⟨(a - 1).toNat, by push_cast; omega⟩
    refine hx ⟨b, hb, ?_⟩
    have : x ^ b / (p : Ω) = x ^ b / (p : Ω) ^ ((n + 1 : ℕ) : ℤ) * (p : Ω) ^ n := by
      rw [zpow_natCast]; field_simp; ring
    rw [this]
    exact IsIntegral.mul h1 (hpi.pow n)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -(n : ℤ) := ⟨(-a).toNat, by omega⟩
    refine IsIntegral.of_pow hb ?_
    have : x⁻¹ ^ b = (p : Ω) ^ (-(n : ℤ)) / x ^ b * (p : Ω) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]; field_simp
    rw [this]
    exact IsIntegral.mul h2 (hpi.pow n)

theorem rad_isMaximal (h : IsClo p Ω) :
    (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical.IsMaximal := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [Ideal.isMaximal_iff]
  constructor
  · rw [mem_rad_iff h]
    rintro ⟨m, -, hm⟩
    refine Basic.not_cong_one_zero h 1 one_ne_zero ⟨_, hm, ?_⟩
    simp [hp0]
  · intro J x _ hx hxJ
    rw [mem_rad_iff h] at hx
    obtain ⟨h0, h1⟩ := isInt_inv h _ hx
    have : (1 : integralClosure (O0 p) Ω) = ⟨_, h1⟩ * x :=
      Subtype.ext (inv_mul_cancel₀ h0).symm
    rw [this]
    exact J.mul_mem_left _ hxJ

theorem residue_indep : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ E : Subfield Ω, Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) →
  (∀ y ∈ E, IsInt (p := p) y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω))) →
  ∀ (T : Tower p Ω) (N : ℕ) (d : ℕ → Ω), (∀ j < p ^ N, d j ∈ E ∧ IsInt (p := p) (d j)) →
  (∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j) ^ m / (p : Ω))) →
  ∀ j < p ^ N, ∃ m : ℕ, 0 < m ∧ IsInt (p := p) (d j ^ m / (p : Ω)) := by
  intro p hp Ω _ _ h E hE hq T N d hd hs
  classical
  set M := (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical with hM
  have hmem : ∀ x : integralClosure (O0 p) Ω, Ideal.Quotient.mk M x = 0 ↔
      ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((x : Ω) ^ m / (p : Ω)) := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hM, mem_rad_iff h]
  haveI : M.IsMaximal := rad_isMaximal h
  letI : Field (integralClosure (O0 p) Ω ⧸ M) := Ideal.Quotient.field M
  haveI : CharP (integralClosure (O0 p) Ω ⧸ M) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk M),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
  let K : Subfield (integralClosure (O0 p) Ω ⧸ M) :=
    { (E.toSubring.comap (integralClosure (O0 p) Ω).val.toRingHom).map (Ideal.Quotient.mk M) with
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases h0 : Ideal.Quotient.mk M y = 0
        · exact ⟨0, E.zero_mem, by rw [h0, inv_zero, map_zero]⟩
        · obtain ⟨h1, h2⟩ := isInt_inv h (y : Ω) (fun hh => h0 ((hmem y).2 hh))
          refine ⟨⟨_, h2⟩, E.inv_mem hy, ?_⟩
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← map_mul, ← map_one (Ideal.Quotient.mk M)]
          congr 1
          exact Subtype.ext (inv_mul_cancel₀ h1) }
  have hqi : IsIntegral (O0 p) (T.qq N) :=
    IsIntegral.of_pow (pow_pos hp.out.pos N) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : integralClosure (O0 p) Ω := ⟨_, hqi⟩
  have ht : ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) = algebraMap (O0 p) Ω (qO p) := by
    rw [← Basic.qq_pow T N]; rfl
  let d' : ℕ → integralClosure (O0 p) Ω := fun j => if hj : j < p ^ N then ⟨d j, (hd j hj).2⟩ else 0
  have hd' : ∀ j < p ^ N, (d' j : Ω) = d j := fun j hj => by simp only [d', dif_pos hj]
  have key := field_indep p K N (Ideal.Quotient.mk M t)
    ⟨t ^ p ^ N, by
      show ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) ∈ E
      rw [ht]; exact hE ⟨_, rfl⟩, map_pow _ _ _⟩
    (by
      rintro _ ⟨y, hy, rfl⟩ hb
      refine hq y hy y.2 ?_
      rw [← ht]
      have hz : Ideal.Quotient.mk M (y ^ p - t ^ p ^ N) = 0 := by
        rw [RingHom.map_sub, RingHom.map_pow, RingHom.map_pow, hb, sub_self]
      have := (hmem (y ^ p - t ^ p ^ N)).1 hz
      exact this)
    (fun j => Ideal.Quotient.mk M (d' j))
    (fun j hj => ⟨d' j, by
      show (d' j : Ω) ∈ E
      rw [hd' j hj]; exact (hd j hj).1, rfl⟩)
    (by
      have e : ((∑ j ∈ Finset.range (p ^ N), d' j * t ^ j : integralClosure (O0 p) Ω) : Ω) =
          ∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j := by
        push_cast
        exact Finset.sum_congr rfl fun j hj => by rw [hd' j (Finset.mem_range.1 hj)]
      have := (hmem _).2 (e ▸ hs)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, map_mul, map_pow] using this)
  intro j hj
  rw [← hd' j hj]
  exact (hmem _).1 (key j hj)

end GlobalTheory.K5.ResidueIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceLiftLevel
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNCongLift

theorem cong_of_dvd {M N : ℕ} (hMN : M ∣ N) {d : ℤ} {γ γ' : SL(2, ℤ)} (h : Cong N d γ γ') : Cong M d γ γ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have key : ∀ x y : ZMod N, x = y → ZMod.castHom hMN (ZMod M) x = ZMod.castHom hMN (ZMod M) y :=
    fun x y hxy => by rw [hxy]
  have k1 := key _ _ h1
  have k2 := key _ _ h2
  have k3 := key _ _ h3
  have k4 := key _ _ h4
  simp only [map_mul, map_intCast] at k1 k2 k3 k4
  exact ⟨k1, k2, k3, k4⟩

theorem cong_congr_d {M : ℕ} {d d' : ℤ} (h : (d : ZMod M) = d') {γ γ' : SL(2, ℤ)} (hc : Cong M d γ γ') :
    Cong M d' γ γ' := by
  unfold Cong at hc ⊢
  rw [← h]
  exact hc

theorem en_eq_of_cong {M : ℕ} {d : ℤ} (hd : IsUnit (d : ZMod M)) {γ γ' γ'' : SL(2, ℤ)}
    (h' : Cong M d γ γ') (h'' : Cong M d γ γ'') :
    ∀ i j, (en γ' i j : ZMod M) = en γ'' i j := by
  obtain ⟨a1, a2, a3, a4⟩ := h'
  obtain ⟨b1, b2, b3, b4⟩ := h''
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; rw [a1, b1]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; rw [a2, b2]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    exact hd.mul_left_cancel (a3.trans b3.symm)
  · simp only [Fin.isValue, Fin.mk_one]; rw [a4, b4]

theorem mem_Gamma_iff_en {M : ℕ} (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma M ↔
      (en γ 0 0 : ZMod M) = 1 ∧ (en γ 0 1 : ZMod M) = 0 ∧ (en γ 1 0 : ZMod M) = 0 ∧ (en γ 1 1 : ZMod M) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [en]

theorem mul_inv_mem_Gamma {M : ℕ} {γ' γ'' : SL(2, ℤ)} (h : ∀ i j, (en γ' i j : ZMod M) = en γ'' i j) :
    γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem']
  have : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ' = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ'' := by
    ext i j
    simpa [en] using h i j
  rw [map_mul, map_inv, this, mul_inv_cancel]

theorem cong_lift : ∀ (M N : ℕ) (d d' : ℤ), 0 < N → M ∣ N → (d : ZMod M) = d' → IsUnit (d' : ZMod N) → (∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → ∃ γ'' : SL(2, ℤ), Cong N d' γ γ'' ∧ γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M) ∧ ∀ δ' ∈ CongruenceSubgroup.Gamma M, ∃ δ ∈ CongruenceSubgroup.Gamma M, Cong N d' δ δ' := by
  intro M N d d' hN hMN hdd' hu
  haveI : NeZero N := ⟨hN.ne'⟩
  have hdM : IsUnit (d : ZMod M) := by
    have := (hu.map (ZMod.castHom hMN (ZMod M)))
    rw [hdd']; simpa using this
  have hdM' : (d' : ZMod M) = d := hdd'.symm
  obtain ⟨u, hu'⟩ := hu
  obtain ⟨ex1, ex2⟩ := _root_.GlobalTheory.FN.dg_conj_lift N u
  refine ⟨fun γ γ' hγ => ?_, fun δ' hδ' => ?_⟩
  · obtain ⟨γ'', hγ''⟩ := ex1 γ
    have hc : Cong N d' γ γ'' := (_root_.GlobalTheory.FNCong.cong_iff_dg N d' u hu' γ γ'').2 hγ''
    refine ⟨γ'', hc, mul_inv_mem_Gamma (en_eq_of_cong hdM hγ ?_)⟩
    exact cong_congr_d hdM' (cong_of_dvd hMN hc)
  · obtain ⟨δ, hδ⟩ := ex2 δ'
    have hc : Cong N d' δ δ' := (_root_.GlobalTheory.FNCong.cong_iff_dg N d' u hu' δ δ').2 hδ
    refine ⟨δ, ?_, hc⟩
    have hcM := cong_congr_d hdM' (cong_of_dvd hMN hc)
    obtain ⟨c1, c2, c3, c4⟩ := hcM
    obtain ⟨g1, g2, g3, g4⟩ := (mem_Gamma_iff_en δ').1 hδ'
    rw [mem_Gamma_iff_en]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← c1, g1]
    · have : (d : ZMod M) * en δ 0 1 = d * 0 := by rw [← c2, g2, mul_zero]
      exact hdM.mul_left_cancel this
    · rw [← c3, g3, mul_zero]
    · rw [← c4, g4]

end GlobalTheory.FNCongLift
end

