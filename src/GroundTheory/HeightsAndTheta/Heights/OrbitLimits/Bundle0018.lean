module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMoriwakiBigCurve
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsPairPoly
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

namespace ComponentsGenericCount

theorem exists_pair_poly {n d : ℕ} (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hJJ' : ¬ J' ≤ J) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ x ∈ zeroSet J, x ∈ zeroSet J' → eval (A *ᵥ x) c = 0 := by
  obtain ⟨f, hfJ', hfJ⟩ := SetLike.not_le_iff_exists.1 hJJ'
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra
  have := hJ
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) := hA.finite.to_isIntegral _
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨c, hc0, fun x hx hx' => ?_⟩
  have h1 : Ideal.Quotient.mk J (pullback A c) = Ideal.Quotient.mk J (r * f) := by
    rw [map_mul]; exact hr.symm
  have h2 := hx _ (Ideal.Quotient.eq.1 h1)
  rwa [map_sub, map_mul, hx' f hfJ', mul_zero, sub_zero, ComplexSets.FibreBound.eval_pullback] at h2

theorem encard_biUnion_le {ι α : Type*} (F : Finset ι) (S : ι → Set α) :
    (⋃ i ∈ F, S i).encard ≤ ∑ i ∈ F, (S i).encard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (by gcongr)

theorem encard_biUnion_eq {ι α : Type*} (F : Finset ι) (S : ι → Set α)
    (h : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j)) :
    (⋃ i ∈ F, S i).encard = ∑ i ∈ F, (S i).encard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq, ih]
    · exact fun i hi j hj hij =>
        h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    · refine Set.disjoint_iUnion₂_right.2 fun j hj =>
        h a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) ?_
      rintro rfl
      exact ha hj

theorem exists_prod_ne_zero {ι : Type*} {k : ℕ} (F : Finset ι) (p : ι → MvPolynomial (Fin k) ℂ → Prop)
    (h : ∀ i ∈ F, ∃ P, P ≠ 0 ∧ p i P) :
    ∃ Δ : MvPolynomial (Fin k) ℂ, Δ ≠ 0 ∧
      ∀ y, eval y Δ ≠ 0 → ∀ i ∈ F, ∃ P, p i P ∧ eval y P ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨Δ, hΔ, hΔy⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨P, hP, hPa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨P * Δ, mul_ne_zero hP hΔ, fun y hy i hi => ?_⟩
    rw [map_mul] at hy
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨P, hPa, left_ne_zero_of_mul hy⟩
    · exact hΔy y (right_ne_zero_of_mul hy) i hi

end ComponentsGenericCount

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeComplexBaseChange
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace ConeComplexBaseChange

variable {σ : Type} [Fintype σ]


omit [Fintype σ] in
theorem map_int_complex_eq :
    (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℂ) =
      (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) := by
  apply MvPolynomial.ringHom_ext <;> intro <;> simp

theorem comap_of_minimal (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
  have hP' : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hm
    rw [hP] at this
    exact this
  obtain ⟨hpr, hco, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have : (P.map (MvPolynomial.map (Int.castRingHom ℚ))).IsPrime := hpr
  rw [map_int_complex_eq, ← Ideal.map_map] at hQ
  have h := ReciprocityTheory.AnForm.R.BaseChangeC.comap_of_mem_minimalPrimes_map _ Q hQ
  rw [map_int_complex_eq, ← Ideal.comap_comap, h]
  exact hco

theorem dim_cancel_one {d : WithBot ℕ∞} {N : ℕ} (h : d + 1 = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    d = (N : WithBot ℕ∞) := by
  refine ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel (h := 1) (N := N + 1) ?_ ?_
  · rw [add_comm]; exact_mod_cast h
  · push_cast; rw [add_comm]

end ConeComplexBaseChange


end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFCoord
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PFCoord.of_found (hGD : GenDegStatement)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hGF : GenFibreExistsStatement) (hFD : FibreDimStatement) (hCF : CoordFibreDeg.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v Ω _ _ y d L L' hv hP' hP hL hLL'
  obtain ⟨G⟩ := hGF K ι K' ι' κ v (mCoordIdeal y) d hv hP'
  obtain ⟨J, hJ, -⟩ := hR4 G.Φ (FibreBlock κ) (fibreIdx ι' κ)
  have hV : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 := hFD K ι K' ι' κ v (mCoordIdeal y) d 0 G hv hP' hP
  choose i hi using hV.1.2.2
  have h0 := hJ.1 (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) Fin.elim0 i hV hi
  rw [hGD I hI K ι K' ι' κ v (mCoordIdeal y) d G J L L' hv hP' hP hJ hL hLL', h0,
    hCF K ι K' ι' κ v Ω y d G i hv hP' hP hi, Int.cast_natCast]

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PMoriwakiBigCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter

theorem chartLat_le_chartLatNm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := fun _ hs c hc =>
  (mem_integralClosure_iff _ _).mpr (isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hs c hc⟩))

theorem MoriwakiBigCurve.proof (hL : CurveCountLower.Statement)
    (hPk : HilbertSamuel.SmallPacking.Statement) : MoriwakiBigCurve.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII hP hB _ hS hC _ _
  set Q := IsSmallH (mCoordIdeal y) y A
  set La := chartLat y A.a
  set T := II K ι (mCoordIdeal y) (0 + 1) (fun _ => A)
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII hP hB hS.1 hC
  obtain ⟨C', hC'⟩ := (hPk K ι Ω y 0 A La hP hB hS.1 fun τ => chartLat_le_chartLatNm y A.a τ).2
  have h0 : ∀ τ, 0 ≤ smallSectionCount Q La τ := fun τ => Real.log_natCast_nonneg _
  have hf : (fun k : ℕ => smallSectionCount Q La (1 * k) / (((1 * k : ℕ) : ℝ) ^ (0 + 1) / ((0 + 1).factorial : ℝ))) =
      fun k : ℕ => smallSectionCount Q La k / k := by
    funext k
    simp
  unfold arVolP
  rw [hf]
  have hC'0 : 0 ≤ C' := by simpa using (h0 0).trans (hC' 0)
  have hbdd : IsBoundedUnder (· ≤ ·) atTop fun k : ℕ => smallSectionCount Q La k / k := by
    refine ⟨2 * C', eventually_map.mpr ((eventually_ge_atTop 1).mono fun k hk => ?_)⟩
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    show smallSectionCount Q La k / k ≤ 2 * C'
    rw [div_le_iff₀ (by linarith)]
    have h1 : smallSectionCount Q La k ≤ C' * ((k : ℝ) + 1) := by simpa using hC' k
    nlinarith
  refine le_of_forall_sub_le fun ε hε => le_limsup_of_frequently_le ?_ hbdd
  refine Eventually.frequently ((eventually_ge_atTop (⌈C / ε⌉₊ + 1)).mono fun k hk => ?_)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.le_add_left 1 _).trans hk
  have hkC : C ≤ ε * k := by
    have h1 : C / ε ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hk)
    rwa [div_le_iff₀ hε, mul_comm] at h1
  have hτ : (k : ℝ) * T - C ≤ smallSectionCount Q La k := hC k ((Nat.le_add_left 1 _).trans hk)
  rw [le_div_iff₀ (by linarith)]
  show (T - ε) * k ≤ _
  nlinarith

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNefCountAlongMultiples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace NefCountAlongMultiples

section Transport

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem count_shift_le {y : (Σ k, ι k) → Ω} {A N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {e : Ω} {C : ℝ} {p q n : ℕ}
    (he0 : e ≠ 0)
    (hmap : ∀ s : Ω, s ∈ chartLat y N.a n → s * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
      ∀ c : ℝ, IsBoundedH (mCoordIdeal y) y N n c s →
        IsBoundedH (mCoordIdeal y) y A (q * n) (c * Real.exp (((p * n : ℕ) : ℝ) * C)) (s * e ^ (p * n)))
    (hfin : {s : chartLat y A.a (q * n) | IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)}.Finite) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)))
        (chartLat y (HermLine.constShift N ((p : ℝ) * C)).a) n ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (q * n) := by
  have hc : Real.exp (-((p : ℝ) * C)) ^ n * Real.exp (((p * n : ℕ) : ℝ) * C) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 2
    push_cast
    ring
  have hsm : ∀ s : {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)},
      (s.1 : Ω) * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
        IsSmallH (mCoordIdeal y) y A (q * n) ((s.1 : Ω) * e ^ (p * n)) := by
    rintro ⟨⟨x, hx⟩, hxs⟩
    have hxs' : IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n x := hxs
    rw [constShift_a] at hx
    show x * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧ IsSmallH (mCoordIdeal y) y A (q * n) (x * e ^ (p * n))
    obtain ⟨hm, hb⟩ := hmap x hx
    refine ⟨hm, fun dg dh g h z hg hh hdeg heq hz => ?_⟩
    have hB : IsBoundedH (mCoordIdeal y) y N n (Real.exp (-((p : ℝ) * C)) ^ n) x := by
      intro dg' dh' g' h' z' hg' hh' hdeg' heq' hz'
      have := hxs' dg' dh' g' h' z' hg' hh' (by rw [constShift_a]; exact hdeg') heq' hz'
      rw [constShift_h, mul_pow] at this
      exact this.trans (le_of_eq (by ring))
    have := hb _ hB dg dh g h z hg hh hdeg heq hz
    rwa [hc, one_mul] at this
  have : Finite {s : chartLat y A.a (q * n) // IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)} :=
    hfin.to_subtype
  have hcard : Nat.card {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
        IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)} ≤
      Nat.card {s : chartLat y A.a (q * n) // IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨(s.1 : Ω) * e ^ (p * n), (hsm s).1⟩, (hsm s).2⟩) fun s s' h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext (mul_right_cancel₀ (pow_ne_zero _ he0) h))
  unfold smallSectionCount
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end Transport

theorem num_bound {T ε I G g C q : ℝ} {D : ℕ} (hε : 0 < ε) (hq : 0 < q) (hC : 0 ≤ C)
    (hI : |I / q ^ (D + 1) - T| < ε / 4) (hG : |G / q ^ D - g| < ε / 4)
    (hqC : ((D : ℝ) + 1) * C * (g + ε / 4) < q * (ε / 4)) :
    (T - ε) * q ^ (D + 1) + ε / 4 * q ^ (D + 1) ≤ I - ((D : ℝ) + 1) * (((1 : ℕ) : ℝ) * C) * G := by
  have hQ : 0 < q ^ (D + 1) := by positivity
  have hQD : 0 < q ^ D := by positivity
  rw [abs_sub_lt_iff] at hI hG
  have h1 : (T - ε / 4) * q ^ (D + 1) < I := (lt_div_iff₀ hQ).1 (by linarith [hI.2])
  have h2 : G < (g + ε / 4) * q ^ D := (div_lt_iff₀ hQD).1 (by linarith [hG.1])
  have h3 : ((D : ℝ) + 1) * (((1 : ℕ) : ℝ) * C) * G ≤ ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) := by
    rw [Nat.cast_one, one_mul]
    exact mul_le_mul_of_nonneg_left h2.le (by positivity)
  have h4 : ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) ≤ ε / 4 * q ^ (D + 1) :=
    calc ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) = (((D : ℝ) + 1) * C * (g + ε / 4)) * q ^ D := by ring
      _ ≤ (q * (ε / 4)) * q ^ D := (mul_lt_mul_of_pos_right hqC hQD).le
      _ = ε / 4 * q ^ (D + 1) := by ring
  nlinarith [mul_pos hε hQ]

theorem le_arithmeticVolume_of_alongMultiples {Ω : Type} [Field Ω] {Pr : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω} {D : ℕ}
    {T Cp : ℝ} (hC : ∀ τ, smallSectionCount Pr La τ ≤ Cp * ((τ : ℝ) + 1) ^ (D + 1))
    (h : ∀ ε : ℝ, 0 < ε → ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (T - ε) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤ smallSectionCount Pr La (a * k)) :
    T ≤ arVolP Pr La 1 D := by
  obtain ⟨B, hB⟩ := NormCountBounded.norm_count_bounded D hC
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ => smallSectionCount Pr La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) := by
    refine ⟨B, ?_⟩
    simpa using hB
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, hev⟩ := h ε hε
  have hfreq : ∃ᶠ k : ℕ in atTop, T - ε ≤ smallSectionCount Pr La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
    rw [frequently_atTop]
    intro N
    obtain ⟨k, hk⟩ := (hev.and (eventually_ge_atTop (N + 1))).exists
    refine ⟨a * k, le_trans (by omega) (Nat.le_mul_of_pos_left k ha), ?_⟩
    have hak : 0 < a * k := Nat.mul_pos ha (by omega)
    have hpos : (0 : ℝ) < ((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) :=
      div_pos (pow_pos (by exact_mod_cast hak) _) (by exact_mod_cast Nat.factorial_pos _)
    rw [one_mul, le_div_iff₀ hpos]
    exact hk.1
  have := le_limsup_of_frequently_le hfreq hbdd
  unfold arVolP
  linarith

end NefCountAlongMultiples

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChart
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre isOpen_blockNonzero)

def expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  HermLine.ofWeight (fun z => -v z) fun c z hc => by rw [hv.2 c z hc]

theorem pot_cons_expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    pot (Fin.cons (expLine v hv) L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.cons v (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [pot, expLine, HermLine.ofWeight]
  · simp [pot]

theorem isSmoothHerm_cons_expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ j, IsSmoothHerm ((Fin.cons (expLine v hv) L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) := by
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact Real.contDiff_exp.comp_contDiffOn hv.1.neg.neg
  · simpa using hL j

theorem SegreChart.proof (hDim : SegreChartDim.Statement) (hInt : SegreChartIntegral.Statement) :
    SegreChart.Statement := by
  classical
  intro K _ _ ι _ P n L u v i δ hP hL hu hv hδ hsupp
  let σ := (Fintype.equivFin ((k : K) → ι k)).symm
  let lam := chartLift σ i
  let χ : ContDiffBump (0 : Fin (Fintype.card ((k : K) → ι k)) → ℂ) :=
    ⟨1 / δ + 1, 1 / δ + 2, by positivity, by linarith⟩
  let U := fun x => χ x * u (lam x)
  let V := fun x => v (lam x)
  let Φ : Fin n → _ := fun j x => pot L j (lam x)
  have hlam : ContDiff ℝ ∞ lam := contDiff_chartLift σ i

  let Ω := lam ⁻¹' {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}
  have hΩ : IsOpen Ω := isOpen_blockNonzero.preimage hlam.continuous
  have hsm : ∀ f : ((Σ k, ι k) → ℂ) → ℝ, ContDiffOn ℝ ∞ f {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} →
      ContDiffOn ℝ ∞ (f ∘ lam) Ω := fun f hf => hf.comp hlam.contDiffOn fun _ hx => hx
  have hpot : ∀ j, ContDiffOn ℝ ∞ (pot L j) {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} := fun j =>
    (hL j).log fun z hz => ((L j).pos z hz).ne'

  have key : ∀ x ∈ segreChartSet P σ i, U =ᶠ[𝓝 x] u ∘ lam := by
    rintro _ ⟨z, -, hzi, rfl⟩
    by_cases hr : ‖fun a => segre z (σ a)‖ < 1 / δ + 1
    · filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hr)] with y hy
      simp [U, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    · have hle : ‖fun a => segre z (σ a)‖ ≤ ‖segre z‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => norm_le_pi_norm (segre z) (σ a)
      have hcont : Continuous fun y => segre (lam y) :=
        continuous_pi fun i' => continuous_finsetProd _ fun k _ =>
          (continuous_apply (⟨k, i' k⟩ : Σ k, ι k)).comp hlam.continuous
      have hO : IsOpen {y | ‖segre (lam y) i‖ < δ * ‖segre (lam y)‖} :=
        isOpen_lt ((continuous_apply i).comp hcont).norm (continuous_const.mul hcont.norm)
      have hx : ‖segre (lam fun a => segre z (σ a)) i‖ < δ * ‖segre (lam fun a => segre z (σ a))‖ := by
        rw [segre_chartLift σ i z hzi, hzi, norm_one]
        have h1 : 1 / δ < ‖segre z‖ := by linarith
        calc (1 : ℝ) = δ * (1 / δ) := by field_simp
          _ < δ * ‖segre z‖ := mul_lt_mul_of_pos_left h1 hδ
      filter_upwards [hO.mem_nhds hx] with y hy
      simp [U, hsupp _ hy]
  have hJ : ∀ J ∈ segreChartComponents P σ i, ComplexSets.zeroSet J ⊆ Ω := fun J hJ x hx =>
    chartLift_blockNonzero σ i (chart_coord_eq_one hJ hx)
  refine ⟨Fintype.card ((k : K) → ι k), segreChartComponents P σ i, U, V, Φ,
    fun J hJs => ⟨(mem_segreChartComponents.1 hJs).1.1,
      hDim K ι P (n + 1) _ σ i hP J hJs,
      ⟨Ω, hΩ, hJ J hJs, (χ.contDiff.contDiffOn).mul (hsm u hu.1)⟩,
      ⟨Ω, hΩ, hJ J hJs, hsm v hv.1⟩, fun j => ⟨Ω, hΩ, hJ J hJs, hsm _ (hpot j)⟩⟩,
    χ.hasCompactSupport.mul_right, ?_, ?_⟩
  · rw [← pot_cons_expLine v hv L]
    refine hInt K ι P n _ σ i _ u δ U _ hP (isSmoothHerm_cons_expLine v hv L hL) hu hδ (Or.inl hsupp)
      fun x hx => ⟨key x hx, fun j => EventuallyEq.of_eq ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · funext y; simp [V, lam, pot, expLine, HermLine.ofWeight]
    · rfl
  · rw [← pot_cons_expLine u hu L]
    refine hInt K ι P n _ σ i _ v δ V _ hP (isSmoothHerm_cons_expLine u hu L hL) hv hδ
      (Or.inr fun z hz => by rw [pot_cons_expLine u hu L]; exact hsupp z hz)
      fun x hx => ⟨EventuallyEq.rfl, fun j => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · have h0 : pot (Fin.cons (expLine u hu) L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) 0 = u := by
        rw [pot_cons_expLine u hu L]; rfl
      simpa [h0] using key x hx
    · exact EventuallyEq.rfl

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem PoincareLelongAlt.of_found (hSt : StokesStatement) (hReg : PoincareLelongRegularised.Statement)
    (hLim : PoincareLelongLimit.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hS : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) =
        ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (regLog A s ε) := by
    intro ε hε
    have h := hSt K ι P n L (regLine A s ε ha hsa) B hP hL (isSmoothHerm_regLine hA hε ha hsa) hB
      (regLine_a A s ε ha hsa) hBa
    rw [log_regLine] at h
    exact h.symm
  exact tendsto_nhds_unique (hReg K ι P n L A B s hP hL hA hB hBa hs)
    ((hLim K ι P n L A B s hP hL hA hB hBa hs).congr' (eventually_nhdsWithin_of_forall hS))

end GroundTheory.Heights₂.Heights.Targets
end

