module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GPureSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem pure_type_periods_span_whole_space {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {n : ℕ} (hn : 0 < n)
    (h : ∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) :
    Submodule.span ℂ {v : Fin g → ℂ | ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = v} = ⊤ := by
  classical
  set S := {v : Fin g → ℂ | ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = v} with hS
  have hsub : Set.range P ⊆ (Submodule.span ℂ S : Set (Fin g → ℂ)) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := h y
    have h1 : P a ∈ Submodule.span ℂ S := Submodule.subset_span ⟨true, ⟨a, ha⟩, rfl⟩
    have h2 : P b ∈ Submodule.span ℂ S := Submodule.subset_span ⟨false, ⟨b, hb⟩, rfl⟩
    have h3 : (n : ℂ) • P y = P a + P b := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hab, map_add (f := _)]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h4 : P y = (n : ℂ)⁻¹ • (P a + P b) := by
      rw [← h3, smul_smul, inv_mul_cancel₀ hn', one_smul]
    rw [SetLike.mem_coe, h4]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 h2)
  have hR := hP.2.2.2.1
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by rw [hR]; trivial
  have hle : Submodule.span ℝ (Set.range P) ≤ (Submodule.span ℂ S).restrictScalars ℝ :=
    Submodule.span_le.mpr hsub
  exact hle hz

theorem periods_span_pure_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (n : ℕ), 0 < n → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), ∀ z : Fin g → ℂ, ∃ s : Fin g → ℂ, z = ∑ k, s k • P (a k) := by
  intro E _ _ _ H D g ty P hP n hn h
  classical
  refine ⟨?_, ?_⟩
  · have h1 := (GlobalTheory.FibreExp.free_finite_finrank_of_isPeriod hP).2.2
    have h2 := GlobalTheory.datum_finrank_int D
    exact Nat.eq_of_mul_eq_mul_left two_pos (h1.symm.trans h2)
  · have hspan := pure_type_periods_span_whole_space hP hn h
    set S := {v : Fin g → ℂ | ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = v} with hS
    obtain ⟨s, hsS, hs, hli⟩ := exists_linearIndependent ℂ S
    have hst : Submodule.span ℂ (Set.range ((↑) : s → (Fin g → ℂ))) = ⊤ := by
      rw [Subtype.range_coe, hs, hspan]
    let bs := Module.Basis.mk hli (le_of_eq hst.symm)
    let e : Fin g ≃ s := (bs.indexEquiv (Pi.basisFun ℂ (Fin g))).symm
    have hmem : ∀ k, ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = (e k : Fin g → ℂ) :=
      fun k => hsS (e k).2
    choose bf af haf using hmem
    refine ⟨bf, af, fun z => ?_⟩
    have hz : z ∈ Submodule.span ℂ (Set.range fun k => P (af k)) := by
      have hr : (Set.range fun k => P (af k)) = Set.range ((↑) : s → (Fin g → ℂ)) := by
        ext v
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨e k, (haf k).symm⟩
        · rintro ⟨t, rfl⟩
          exact ⟨e.symm t, by simp [haf]⟩
      rw [hr, hst]
      trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hz
    exact ⟨c, hc.symm⟩

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.SqrtDiscriminantBoundsCmField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

section SlopeTestRemainingChoices

variable {O J : Type} [CommRing O] [Fintype J] [DecidableEq J]

theorem prime_dvd_trace_of_sq (b : Module.Basis J ℤ O) (d : ℕ) (hd : d.Prime) (y z : O) (h : y ^ 2 = (d : O) * z) :
    (d : ℤ) ∣ Algebra.trace ℤ O y := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  rw [Algebra.trace_eq_matrix_trace b y, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hnil : IsNilpotent ((Algebra.leftMulMatrix b y).map (Int.castRingHom (ZMod d))) := by
    refine ⟨2, ?_⟩
    have e : (d : O) * z = (d : ℤ) • z := by simp [zsmul_eq_mul]
    rw [← Matrix.map_pow, ← map_pow, h, e, map_zsmul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, eq_intCast,
      Int.cast_mul, Int.cast_natCast, ZMod.natCast_self]
    simp
  have htr := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have hc : ((Algebra.leftMulMatrix b y).map (Int.castRingHom (ZMod d))).trace
      = (((Algebra.leftMulMatrix b y).trace : ℤ) : ZMod d) := by
    simp [Matrix.trace, Matrix.map_apply]
  rw [← hc]
  exact htr

theorem traceMatrix_mul_leftMulMatrix (b : Module.Basis J ℤ O) (r : O) (i j : J) :
    (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j = Algebra.trace ℤ O (b i * (r * b j)) := by
  rw [Matrix.mul_apply]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← b.sum_repr (r * b j), Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem discriminant_bound_sqrt_neg_prime (b : Module.Basis J ℤ O) (d : ℕ) (hd : d.Prime) (r : O) (hr : r ^ 2 = -(d : O))
    (h0 : Algebra.discr ℤ b ≠ 0) : (d : ℤ) ^ Fintype.card J ≤ Algebra.discr ℤ b ^ 2 := by
  classical
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hent : ∀ i j, (d : ℤ) ∣ (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j := by
    intro i j
    rw [traceMatrix_mul_leftMulMatrix b r i j]
    refine prime_dvd_trace_of_sq b d hd (b i * (r * b j)) (-((b i) ^ 2 * (b j) ^ 2)) ?_
    have e : (b i * (r * b j)) ^ 2 = (b i) ^ 2 * (b j) ^ 2 * r ^ 2 := by ring
    rw [e, hr]
    ring
  let C : Matrix J J ℤ := fun i j => (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j / d
  have hTL : Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r = (d : ℤ) • C := by
    ext i j
    simp only [C, Matrix.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hent i j)).symm
  have hL2 : (Algebra.leftMulMatrix b r).det ^ 2 = (-(d : ℤ)) ^ Fintype.card J := by
    rw [sq, ← Matrix.det_mul, ← map_mul, ← sq, hr]
    have e : (-(d : O)) = algebraMap ℤ O (-(d : ℤ)) := by simp
    rw [e, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one,
      _root_.mul_one]
  have h1 : (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r).det ^ 2
      = ((d : ℤ) ^ Fintype.card J) ^ 2 * C.det ^ 2 := by
    rw [hTL, Matrix.det_smul]
    ring
  rw [Matrix.det_mul, mul_pow, hL2, ← Algebra.discr_def, neg_pow] at h1
  have key2 : Algebra.discr ℤ b ^ 2 * (-1) ^ Fintype.card J = (d : ℤ) ^ Fintype.card J * C.det ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero (Fintype.card J) hd0)
    linear_combination h1
  have hdv : (d : ℤ) ^ Fintype.card J ∣ Algebra.discr ℤ b ^ 2 := by
    have h2 : (d : ℤ) ^ Fintype.card J ∣ Algebra.discr ℤ b ^ 2 * (-1) ^ Fintype.card J := ⟨_, key2⟩
    rcases neg_one_pow_eq_or ℤ (Fintype.card J) with h | h <;> rw [h] at h2 <;> simpa using h2
  exact Int.le_of_dvd (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))) hdv

end SlopeTestRemainingChoices

theorem sqrt_discriminant_bounds_cm_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 1 ≤ Real.sqrt H.d ∧ Real.sqrt H.d ≤ rootDiscr E := by
  intro E _ _ _ H
  classical
  have hd := H.d_prime
  have hd1 : (1 : ℝ) ≤ H.d := by exact_mod_cast hd.one_lt.le
  refine ⟨by simpa using Real.sqrt_le_sqrt hd1, ?_⟩
  set n := Module.finrank ℚ E with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  have hD : (H.d : ℤ) ^ n ≤ (discr E) ^ 2 := by
    have h := discriminant_bound_sqrt_neg_prime (RingOfIntegers.basis E) H.d hd H.rt H.rt_sq (discr_ne_zero E)
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank] at h
    exact h
  have hR : ((Real.sqrt H.d) ^ n) ^ 2 ≤ |((discr E : ℤ) : ℝ)| ^ 2 := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by positivity), sq_abs]
    exact_mod_cast hD
  have hR2 : (Real.sqrt H.d) ^ n ≤ |((discr E : ℤ) : ℝ)| :=
    (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).mp hR
  rw [rootDiscr_def]
  rw [Int.cast_abs]
  calc Real.sqrt H.d = ((Real.sqrt H.d) ^ n) ^ ((n : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (Real.sqrt_nonneg _) hn0).symm
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hR2 (by positivity)

end PositivityTheory.Xgf
end

