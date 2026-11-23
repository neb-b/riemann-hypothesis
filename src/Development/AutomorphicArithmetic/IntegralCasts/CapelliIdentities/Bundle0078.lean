module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Formalism.ConjugateSelfDual.Statement
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0040
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0052
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0022
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0013
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementT
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0036
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoPoint
section
theorem UpperTheory.Reformulated.B.CoPoint.coPt :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) [UpperTheory.V.Fr.IsCoef l ↥c.O] (R : Type)
    [inst_2 : CommRing R] [inst_3 : Algebra (↥c.O) R] [inst_4 : UpperTheory.V.Alg.IsCO (↥c.O) R]
    (y : R →ₐ[↥c.O] Formalism.ConjugateSelfDual.Qbar l),
    Module.Finite ↥c.O ↥y.range ∧
      (∀ (a : R), ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ ≤ (1 : ℝ)) ∧
        ∀ a ∈ IsLocalRing.maximalIdeal R,
          ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ <
            (1 :
              ℝ) := by
  intro l _ c _ R _ _ _ y
  obtain ⟨hint, hO, hm⟩ := UpperTheory.integral_dvr_norm l c.O
  have hO' : ∀ a : c.O, ‖algebraMap c.O (Formalism.ConjugateSelfDual.Qbar l) a‖ ≤ 1 := hO
  have hres : ∀ x : R, ∃ a : c.O, x - algebraMap c.O R a ∈ IsLocalRing.maximalIdeal R :=
    UpperTheory.V.Alg.IsCO.res_surj
  obtain ⟨hb1, hb2⟩ := UpperTheory.residue_hom_norm (O := c.O) (Ω := Formalism.ConjugateSelfDual.Qbar l) hres hO' hint y
  refine ⟨?_, hb1, hb2⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hJ : ∀ x : R, ∃ P : Polynomial c.O, P.Monic ∧ Polynomial.aeval x P ∈ RingHom.ker y := fun x => by
    obtain ⟨P, hP, h0⟩ := hint (y x) (hb1 x)
    refine ⟨P, hP, ?_⟩
    rw [RingHom.mem_ker]
    have h1 : Polynomial.aeval (y x) P = 0 := h0
    rw [Polynomial.aeval_algHom_apply] at h1
    exact h1
  have hfin := UpperTheory.monic_ideal_completion hres (RingHom.ker y) hJ ϖ hϖ
  have hlt : ‖algebraMap c.O (Formalism.ConjugateSelfDual.Qbar l) ϖ‖ < 1 :=
    hm ϖ hϖ.not_isUnit
  classical
  letI := Fintype.ofFinite (R ⧸ (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}))
  have key := UpperTheory.digit_expansion_lattice hO' ϖ hϖ hlt (Subalgebra.toSubmodule y.range)
    (fun s hs => by
      obtain ⟨r, rfl⟩ := hs
      exact hb1 r)
    (Finset.univ.image fun q : R ⧸ (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}) => y (Quotient.out q))
    (fun e he => by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 he
      exact ⟨_, rfl⟩)
    (fun s hs => by
      obtain ⟨r, rfl⟩ := hs
      have hq : r - Quotient.out (Ideal.Quotient.mk (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}) r) ∈
          RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ} := by
        rw [← Ideal.Quotient.eq]
        simp [Ideal.Quotient.mk_out]
      obtain ⟨j, hj, t, ht, hjt⟩ := Submodule.mem_sup.1 hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ht
      refine ⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ r, Finset.mem_univ _, rfl⟩, y a, ⟨a, rfl⟩, ?_⟩
      have h2 := congrArg y hjt
      rw [map_add (f := _), RingHom.mem_ker.1 hj, map_sub, map_mul, AlgHom.commutes] at h2
      rw [Algebra.smul_def, mul_comm]
      linear_combination -h2)
  exact key
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalTheoryWindows
section
attribute [local instance] Formalism.MainNotions.S.starE

theorem UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult :
    ∀ (D : Formalism.BasicNotions.D7)
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.VS D).V},
    Submodule.IsFullLattice D.host.E Λ →
      ∀ (v : (Formalism.MainNotions.S.VS D).V),
        ∃ (n : ℤ),
          n ≠ (0 : ℤ) ∧
            (↑n : D.host.E) • v ∈
              Λ := by
  intro D Λ h v
  obtain ⟨⟨t, ht⟩, hv⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E (Λ : Set (Formalism.MainNotions.S.VS D).V) v
    (h.span_eq_top ▸ Submodule.mem_top)
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) t).exists_nonzero_dvd ht
  refine ⟨n, hn, ?_⟩
  have hc' : (n : NumberField.RingOfIntegers D.host.E) = c * t := by rw [mul_comm]; simpa using hc
  have e : (n : D.host.E) • v = c • t • v := by
    rw [smul_smul, ← hc', ← algebraMap_smul D.host.E (n : NumberField.RingOfIntegers D.host.E) v, map_intCast]
  rw [Submodule.span_eq] at hv
  exact e ▸ Λ.smul_mem c hv
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeriesSubgroup
section
open PowerSeries

namespace UpperTheory.Reformulated.B.SeriesSubgroup

private def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rwa [norm_neg]

private def ser {R : Type} [CommRing R] (S : Subring R) : Subring R⟦X⟧ where
  carrier := {f | ∀ n, coeff n f ∈ S}
  mul_mem' := fun {a b} ha hb n => by
    rw [coeff_mul]
    exact S.sum_mem fun p _ => S.mul_mem (ha _) (hb _)
  one_mem' := fun n => by
    rw [coeff_one]
    split_ifs
    exacts [S.one_mem, S.zero_mem]
  add_mem' := fun {a b} ha hb n => by
    rw [map_add (f := _)]
    exact S.add_mem (ha n) (hb n)
  zero_mem' := fun n => by
    rw [map_zero]
    exact S.zero_mem
  neg_mem' := fun {a} ha n => by
    rw [map_neg]
    exact S.neg_mem (ha n)

private lemma C_mem {R : Type} [CommRing R] (S : Subring R) {a : R} (ha : a ∈ S) :
    (C a : R⟦X⟧) ∈ ser S := fun n => by
  rw [coeff_C]
  split_ifs
  exacts [ha, S.zero_mem]

private lemma X_mem {R : Type} [CommRing R] (S : Subring R) : (X : R⟦X⟧) ∈ ser S := fun n => by
  rw [coeff_X]
  split_ifs
  exacts [S.one_mem, S.zero_mem]

private lemma inv_mem {R : Type} [CommRing R] (S : Subring R) {f : R⟦X⟧} (hf : f ∈ ser S)
    (h : constantCoeff f = 1) : invOfUnit f 1 ∈ ser S := UpperTheory.invOfUnit_coeff_mem R S f hf h

open Formalism.L2.Th1.A in
private lemma xS_const {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    constantCoeff (xS W) = 1 := by
  simp [xS]

open Formalism.L2.Th1.A in
private lemma xS_mem {R : Type} [CommRing R] (S : Subring R) (W : WeierstrassCurve R)
    (h₁ : W.a₁ ∈ S) (h₂ : W.a₂ ∈ S) (h₃ : W.a₃ ∈ S) (h₄ : W.a₄ ∈ S) (h₆ : W.a₆ ∈ S) :
    xS W ∈ ser S := by
  have hw : Formalism.ELL.WFixed W (wSer W) := (Formalism.ELL.wSeriesUnique R W).choose_spec.1
  have hm := UpperTheory.formal_group_coeff_mem R S W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ (wSer W) h₁ h₂ h₃ h₄ h₆ hw.1 hw.2
  refine inv_mem S (fun n => ?_) ?_
  · rw [wU, coeff_mk]
    exact hm _
  · rw [← coeff_zero_eq_constantCoeff_apply, wU, coeff_mk]
    exact (Formalism.ELL.wSeriesLead R W _ hw).2.2.2

open Formalism.L2.Th1.A in
private lemma xPlus_mem {R : Type} [CommRing R] (S : Subring R) (W : WeierstrassCurve R)
    (h₁ : W.a₁ ∈ S) (h₂ : W.a₂ ∈ S) (h₃ : W.a₃ ∈ S) (h₄ : W.a₄ ∈ S) (h₆ : W.a₆ ∈ S)
    {x y : R} (hx : x ∈ S) (hy : y ∈ S) : xPlus W x y ∈ ser S := by
  have hs := xS_mem S W h₁ h₂ h₃ h₄ h₆
  have hX := X_mem S
  have two : (2 : R) ∈ S := ofNat_mem S 2
  have three : (3 : R) ∈ S := ofNat_mem S 3
  have hd : invOfUnit (tDen W x) 1 ∈ ser S :=
    inv_mem S (sub_mem hs (mul_mem (C_mem S hx) (pow_mem hX 2))) (by simp [tDen, xS_const])
  have hn : nS W x y ∈ ser S :=
    add_mem (sub_mem
      (mul_mem (mul_mem (C_mem S (add_mem (add_mem (sub_mem h₄ (mul_mem h₁ hy))
        (mul_mem (mul_mem two h₂) hx)) (mul_mem three (pow_mem hx 2)))) hX) hs)
      (mul_mem (C_mem S (add_mem (add_mem (mul_mem two hy) (mul_mem h₁ hx)) h₃)) (neg_mem hs)))
      (mul_mem (C_mem S (sub_mem (sub_mem (add_mem (mul_mem two h₆) (mul_mem h₄ hx))
        (mul_mem h₃ hy)) (pow_mem hx 3))) (pow_mem hX 3))
  exact add_mem (C_mem S hx) (mul_mem (mul_mem hX hn) (pow_mem hd 2))

open Formalism.L2.Th1.A in
private lemma xPlus_coeff {R : Type} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    coeff 0 (xPlus W x y) = x ∧ coeff 1 (xPlus W x y) = 2 * y + W.a₁ * x + W.a₃ ∧
      (2 * y + W.a₁ * x + W.a₃ = 0 →
        coeff 2 (xPlus W x y) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) := by
  refine ⟨by simp [xPlus], ?_, fun h => ?_⟩
  · rw [xPlus, mul_assoc, map_add (f := _), coeff_succ_X_mul, coeff_C, if_neg one_ne_zero, zero_add,
      coeff_zero_eq_constantCoeff_apply]
    simp [nS, yS, xS_const]
  · have e : xPlus W x y = C x + X ^ 2 *
        ((C (W.a₄ - W.a₁ * y + 2 * W.a₂ * x + 3 * x ^ 2) * xS W
          + C (2 * W.a₆ + W.a₄ * x - W.a₃ * y - x ^ 3) * X ^ 2) *
          invOfUnit (tDen W x) 1 ^ 2) := by
      rw [xPlus, nS, h, map_zero]
      ring
    rw [e, map_add (f := _), coeff_C, if_neg two_ne_zero, zero_add, coeff_X_pow_mul', if_pos le_rfl,
      Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
    simp only [map_mul, map_add (constantCoeff (R := R)), map_pow, constantCoeff_C, constantCoeff_X,
      xS_const, constantCoeff_invOfUnit]
    simp
    ring

theorem XTShape_holds : Formalism.L2.Th1.E.XTShape := by
  intro K _ _ _ W hW P _ hx hy
  obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := hW
  exact ⟨xPlus_mem (ball K) W h₁ h₂ h₃ h₄ h₆ hx hy, xPlus_coeff W _ _⟩

end UpperTheory.Reformulated.B.SeriesSubgroup
end

