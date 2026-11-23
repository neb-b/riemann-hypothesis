module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0017

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.LocalIntegralClosureChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem exists_mul_isIntegral_of_eq_mul_inv {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (R A : Subalgebra F Ω) (hRA : R ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    {x : Ω} (hx : IsIntegral A x) : ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ IsIntegral R (d * x) := by
  let M : Submonoid R :=
    { carrier := {d | (d : Ω) ≠ 0 ∧ (d : Ω)⁻¹ ∈ A}
      mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, by
        rw [Subalgebra.coe_mul, mul_inv]; exact A.mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_ne_zero, by rw [Subalgebra.coe_one, inv_one]; exact A.one_mem⟩ }
  let _ : Algebra R A := (Subalgebra.inclusion hRA).toAlgebra
  have : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization M A := by
    refine (isLocalization_iff M A).mpr ⟨fun d => ?_, fun a => ?_, fun {a b} h => ⟨1, ?_⟩⟩
    · exact ⟨⟨_, ⟨_, d.2.2⟩, Subtype.ext (mul_inv_cancel₀ d.2.1), Subtype.ext (inv_mul_cancel₀ d.2.1)⟩, rfl⟩
    · obtain ⟨r, hr, d, hd, hd0, hdA, he⟩ := hloc a a.2
      refine ⟨(⟨r, hr⟩, ⟨⟨d, hd⟩, hd0, hdA⟩), Subtype.ext ?_⟩
      change (a : Ω) * d = r
      rw [he, mul_assoc, inv_mul_cancel₀ hd0, mul_one]
    · have e : ((algebraMap R A a : A) : Ω) = (algebraMap R A b : A) := congrArg Subtype.val h
      have e' : (a : Ω) = b := e
      rw [Subtype.ext e']
  obtain ⟨⟨d, hd0, hdA⟩, hint⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (M := M) (Rₘ := A) x hx
  exact ⟨d, d.2, hd0, hdA, hint⟩


open IntermediateField.algebraAdjoinAdjoin in
theorem exists_finset_integral_span (hN : NoetherIntegralClosureFinite.Statement.{u})
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] {S : Set Ω} (hS : S.Finite)
    (A : Subalgebra F Ω) (L : IntermediateField F Ω) (hRA : Algebra.adjoin F S ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin F S, ∃ d ∈ Algebra.adjoin F S,
      d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    (hEL : IntermediateField.adjoin F S ≤ L)
    (hfin : FiniteDimensional (IntermediateField.adjoin F S) (IntermediateField.extendScalars hEL)) :
    ∃ s : Finset Ω, (∀ e ∈ s, e ∈ L ∧ IsIntegral A e) ∧
      ∀ x ∈ L, IsIntegral A x → x ∈ Submodule.span A (s : Set Ω) := by
  classical
  let L' := IntermediateField.extendScalars hEL
  let _ : Algebra (Algebra.adjoin F S) L' :=
    ((algebraMap (IntermediateField.adjoin F S) L').comp
      (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S))).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S) L' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType F (Algebra.adjoin F S) := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨t, ht⟩ := Module.finite_def.mp
    (hN F (Algebra.adjoin F S) (IntermediateField.adjoin F S) L')
  let ι₀ : L' →ₐ[Algebra.adjoin F S] Ω := { L'.val.toRingHom with commutes' := fun _ => rfl }
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective
  let _ : Algebra (Algebra.adjoin F S) A := (Subalgebra.inclusion hRA).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨t.image fun y => ι₀ y.1, ?_, fun x hx hxA => ?_⟩
  · intro e he
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp he
    exact ⟨(IntermediateField.mem_extendScalars hEL).mp y.1.2,
      ((isIntegral_algHom_iff ι₀ hι₀).mpr y.2).tower_top⟩
  obtain ⟨d, hd, hd0, hdA, hint⟩ := exists_mul_isIntegral_of_eq_mul_inv _ A hRA hloc hxA
  let z : integralClosure (Algebra.adjoin F S) L' :=
    ⟨⟨d * x, (IntermediateField.mem_extendScalars hEL).mpr
      (mul_mem (hEL (IntermediateField.algebra_adjoin_le_adjoin F S hd)) hx)⟩,
      (isIntegral_algHom_iff ι₀ hι₀).mp hint⟩
  have hz : ι₀ z ∈ Submodule.span (Algebra.adjoin F S) ((t.image fun y => ι₀ y.1 : Finset Ω) : Set Ω) := by
    have hzt : z ∈ Submodule.span (Algebra.adjoin F S) (t : Set _) := ht ▸ Submodule.mem_top
    have := Submodule.mem_map_of_mem
      (f := ι₀.toLinearMap.comp (integralClosure (Algebra.adjoin F S) L').val.toLinearMap) hzt
    rw [Submodule.map_span] at this
    rw [Finset.coe_image]
    exact this
  have e : (⟨d⁻¹, hdA⟩ : A) • (d * x) = x := by
    rw [Subalgebra.smul_def, smul_eq_mul, ← mul_assoc]
    change d⁻¹ * d * x = x
    rw [inv_mul_cancel₀ hd0, one_mul]
  rw [← e]
  exact Submodule.smul_mem _ _ (Submodule.span_le_restrictScalars (Algebra.adjoin F S) A _ hz)

section Chart

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem isMultiHomog_chartMonomial (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have hb : (∑ k, b k • blockWeight ι ⟨k, u k⟩) = b := by
    funext k
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  have h := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (b k)
  unfold IsMultiHomog chartMonomial
  convert h using 1
  exact hb.symm


omit [DecidableEq K] in
theorem chartMonomial_not_mem_of_notMem (W : Ideal (MRing ι F)) [W.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (b : K → ℕ) : chartMonomial u b ∉ W :=
  (Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (hu k) _ : chartMonomial u b ∈ W.primeCompl)

theorem degZeroLoc_map_eq_mul_inv (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) {Ω : Type*} [Field Ω]
    [Algebra F Ω] (φ : FractionRing (MRing ι F ⧸ P) →ₐ[F] Ω) :
    Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) ≤ (degZeroLoc P {W}).map φ ∧
      ∀ a ∈ (degZeroLoc P {W}).map φ,
        ∃ r ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
        ∃ d ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
          d ≠ 0 ∧ d⁻¹ ∈ (degZeroLoc P {W}).map φ ∧ a = r * d⁻¹ := by
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k h => hu k (hPW h)
  have hW1 : ∀ W' ∈ ({W} : Set (Ideal (MRing ι F))), W'.IsPrime := fun W' h => by
    rw [Set.mem_singleton_iff.mp h]; infer_instance
  have hmem : ∀ p, φ (chartMap P u p) ∈
      Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) := fun p => by
    rw [← aeval_range]
    refine ⟨p, ?_⟩
    change aeval _ p = (φ.comp (chartMap P u)) p
    rw [chartMap, comp_aeval]
    simp
  have hq : ∀ g : MRing ι F, g ∉ P → algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P g) ≠ 0 := fun g hg => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  refine ⟨Algebra.adjoin_le ?_, fun a ha => ?_⟩
  · rintro _ ⟨v, rfl⟩
    refine Subalgebra.mem_map.mpr ⟨_, div_mem_degZeroLoc P {W} (b := blockWeight ι v)
      (isWeightedHomogeneous_X F _ v) (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩)
      (huP v.1) (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hu v.1), ?_⟩
    simp [chartMap]
  obtain ⟨a, haA, rfl⟩ := Subalgebra.mem_map.mp ha
  obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := hQ F K ι P {W} hW1 a haA
  have hm := chartMonomial_not_mem_of_notMem (F := F) W u hu b
  have hm0 := hq _ fun h => hm (hPW h)
  have hg0 := hq g hgP
  refine ⟨φ (chartMap P u f), hmem f, φ (chartMap P u g), hmem g, ?_, ?_, ?_⟩
  · rw [hD F K ι P u huP g b hg, map_ne_zero]
    exact div_ne_zero hg0 hm0
  · rw [hD F K ι P u huP g b hg, ← map_inv₀, inv_div]
    exact Subalgebra.mem_map.mpr ⟨_, div_mem_degZeroLoc P {W} (isMultiHomog_chartMonomial u b) hg
      hgP (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hgW W rfl), rfl⟩
  · rw [hD F K ι P u huP f b hf, hD F K ι P u huP g b hg, ← map_inv₀, ← map_mul]
    congr 1
    field_simp

end Chart

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConePolyLocalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u


set_option maxHeartbeats 400000 in
theorem ConePolyLocalization.proof (h₀ : DegZeroLocLocal.Statement.{u}) (h₁ : ConeVarUnit.Statement.{u})
    (h₂ : ConeVarSurj.Statement.{u}) (h₃ : ConeVarInj.Statement.{u}) :
    ConePolyLocalization.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  have hA : IsLocalRing (degZeroLoc P {W}) := h₀ F K ι P hP W hW hPW
  refine ⟨hA, ?_⟩
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have hQ : ∀ q : MvPolynomial K (degZeroLoc P {W}),
      q ∈ ((maximalIdeal (degZeroLoc P {W})).map
        (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl ↔ ∃ e, IsUnit (q.coeff e) := by
    intro q
    rw [Ideal.mem_primeCompl_iff, mem_map_C_iff]
    push Not
    simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · obtain ⟨e, he⟩ := (hQ y).mp y.2
    exact h₁ F K ι P hP W hW hPW v hv y e he
  · obtain ⟨p, q, e, he, hz⟩ := h₂ F K ι P hP W hW hPW v hv z
    exact ⟨⟨p, ⟨q, (hQ q).mpr ⟨e, he⟩⟩⟩, hz⟩
  · refine ⟨1, ?_⟩
    rw [h₃ F K ι P hP W hW hPW v hv hxy]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem ConeVarInj.proof (hNum : ConeVarNumerator.Statement.{u}) : ConeVarInj.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨B, g, h, -, hgW, hh, hc, hφ⟩ := hNum F K ι P hP W hW hPW v hv p

  have hu : ∀ d : K →₀ ℕ, IsMultiHomog (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) ⇑d := fun d => by
    unfold IsMultiHomog
    convert IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, v k⟩).pow (d k)) using 1
    ext k
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  have huW : ∀ d : K →₀ ℕ, ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∉ W := fun d => by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (hW.isPrime.mem_of_pow_mem _ hk)
  have hN : ∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∈ P := by
    have hg0 : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact fun hg => hgW (hPW hg)
    rw [hp, ZeroMemClass.coe_zero, eq_comm, div_eq_zero_iff, or_iff_left hg0,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hφ
    exact hφ
  refine MvPolynomial.ext _ _ fun d => ?_
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hd
  have hcomp := hP.multiHomog _ hN (B + ⇑d)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single d] at hcomp
  · rw [((hh d).mul (hu d)).weightedHomogeneousComponent_same] at hcomp
    have hhd : h d ∈ P := (hP.isPrime.mem_or_mem hcomp).resolve_right fun hm => huW d (hPW hm)
    apply hd
    apply Subtype.ext
    rw [hc d, Ideal.Quotient.eq_zero_iff_mem.mpr hhd, map_zero, zero_div]
    rfl
  · intro d' _ hne
    refine ((hh d').mul (hu d')).weightedHomogeneousComponent_ne _ fun heq => hne ?_
    ext k
    have := congrFun heq k
    simp only [Pi.add_apply] at this
    omega
  · exact fun hn => absurd (mem_support_iff.mpr hd) hn

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarNumerator
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem ConeVarNumerator.proof (hDZ : DegZeroLocQuot.Statement.{u}) :
    ConeVarNumerator.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v _
  have := hP.isPrime
  have := hW.isPrime
  intro p
  have hne : ∀ g : MRing ι F, g ∉ W →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
    intro g hg
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h' => hg (hPW h')
  have h𝒲 : ∀ W' ∈ ({W} : Set (Ideal (MRing ι F))), W'.IsPrime := by
    intro W' hW'
    rw [Set.mem_singleton_iff.mp hW']
    infer_instance

  have step : ∀ D : Finset (K →₀ ℕ), ∃ (b : K → ℕ) (g : MRing ι F) (hn : (K →₀ ℕ) → MRing ι F),
      IsMultiHomog g b ∧ g ∉ W ∧ (∀ d, IsMultiHomog (hn d) b) ∧ (∀ d, d ∉ D → hn d = 0) ∧
      ∀ d ∈ D, ((p.coeff d : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (hn d)) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      refine ⟨0, 1, fun _ => 0, isWeightedHomogeneous_one F _, fun h1 => ?_,
        fun _ => isWeightedHomogeneous_zero F _ _, fun _ _ => rfl, fun d hd => absurd hd (Finset.notMem_empty d)⟩
      exact Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one W).mpr h1)
    | insert d₀ D hd₀ ih =>
      obtain ⟨b, g, hn, hg, hgW, hh, h0, hD⟩ := ih
      obtain ⟨b', f', g', hf', hg', -, hg'W, he⟩ := hDZ F K ι P {W} h𝒲 _ (p.coeff d₀).2
      have hg'W' : g' ∉ W := hg'W W rfl
      refine ⟨b + b', g * g', fun d => if d = d₀ then g * f' else hn d * g',
        IsWeightedHomogeneous.mul hg hg', fun hm => ?_, fun d => ?_, fun d hd => ?_, fun d hd => ?_⟩
      · exact (Ideal.IsPrime.mem_or_mem inferInstance hm).elim hgW hg'W'
      · dsimp only
        split_ifs
        · exact IsWeightedHomogeneous.mul hg hf'
        · exact IsWeightedHomogeneous.mul (hh d) hg'
      · rw [Finset.mem_insert, not_or] at hd
        dsimp only
        rw [if_neg hd.1, h0 d hd.2, zero_mul]
      · rcases Finset.mem_insert.mp hd with rfl | hd
        · dsimp only
          rw [if_pos rfl, he]
          simp only [map_mul]
          rw [mul_div_mul_left _ _ (hne g hgW)]
        · have hdd : d ≠ d₀ := fun e => hd₀ (e ▸ hd)
          dsimp only
          rw [if_neg hdd, hD d hd]
          simp only [map_mul]
          rw [mul_div_mul_right _ _ (hne g' hg'W')]
  obtain ⟨b, g, hn, hg, hgW, hh, h0, hD⟩ := step p.support
  refine ⟨b, g, hn, hg, hgW, hh, fun d => ?_, ?_⟩
  · by_cases hd : d ∈ p.support
    · exact hD d hd
    · rw [notMem_support_iff.mp hd, h0 d hd]
      simp

  have hφ : ∀ x : MvPolynomial K (degZeroLoc P {W}),
      ((coneVarMap P W hPW v x : coneLocal P W hPW) : FractionRing (MRing ι F ⧸ P)) =
        eval₂ (degZeroLoc P {W}).val.toRingHom (fun k => algebraMap (MRing ι F ⧸ P)
          (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, v k⟩))) x := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a =>
      rw [coneVarMap, aeval_C, degZeroLoc.algebraMap_cone_coe, eval₂_C]
      rfl
    | add x y hx hy =>
      rw [map_add (coneVarMap P W hPW v) x y, Subalgebra.coe_add, hx, hy, eval₂_add]
    | mul_X x k hx =>
      rw [map_mul, Subalgebra.coe_mul, hx, eval₂_mul, eval₂_X, coneVarMap, aeval_X]
      rfl
  rw [hφ, eval₂_eq']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, map_pow, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [mul_div_right_comm, ← hD d hd]
  rfl

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarSurj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option maxHeartbeats 400000 in
theorem ConeVarSurj.proof : ConeVarSurj.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  classical
  intro z
  set L := FractionRing (MRing ι F ⧸ P)
  let π : MRing ι F → L := fun x => algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P x)
  have hπ : ∀ x, x ∉ P → π x ≠ 0 := fun x hx => by
    simp only [π, Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  let U : (K → ℕ) → MRing ι F := fun d => ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k
  have hUh : ∀ d, IsMultiHomog (U d) d := fun d => by
    have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩) (fun k _ => (isWeightedHomogeneous_X _ _ _).pow _)
    have hd : ∑ k, d k • blockWeight ι ⟨k, v k⟩ = d := by
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hd] at this
    exact this
  have hUW : ∀ d, U d ∉ W := fun d =>
    W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hv k) _
  let comp : MRing ι F → (K → ℕ) → MRing ι F := fun h d =>
    weightedHomogeneousComponent (blockWeight ι) d h
  let c : MRing ι F → (K → ℕ) → degZeroLoc P {W} := fun h d =>
    ⟨π (comp h d) / π (U d), div_mem_degZeroLoc P {W}
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (hUh d) (fun h' => hUW d (hPW h')) (by rintro _ rfl; exact hUW d)⟩
  let D : MRing ι F → Finset (K → ℕ) := fun h => h.support.image (Finsupp.weight (blockWeight ι))
  have hsum : ∀ h, ∑ d ∈ D h, comp h d = h := fun h => by
    rw [← finsum_eq_sum_of_support_subset _ (s := D h) (fun d hd => by
      by_contra hd'
      exact hd (weightedHomogeneousComponent_eq_zero_of_notMem _ h d hd'))]
    exact sum_weightedHomogeneousComponent (blockWeight ι) h
  let Q : MRing ι F → MvPolynomial K (degZeroLoc P {W}) := fun h =>
    ∑ d ∈ D h, monomial (Finsupp.equivFunOnFinite.symm d) (c h d)
  have hQ : ∀ h, coneVarMap P W hPW v (Q h) =
      algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h) := fun h => by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← hsum h, map_sum, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coneVarMap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, degZeroLoc.algebraMap_cone_coe, SubmonoidClass.coe_finsetProd,
      SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, Finsupp.coe_equivFunOnFinite_symm]
    have hU : ∏ k, algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P (X ⟨k, v k⟩)) ^ d k =
        π (U d) := by
      simp [π, U, map_prod, map_pow]
    rw [hU]
    exact div_mul_cancel₀ _ (hπ _ fun h' => hUW d (hPW h'))
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (W.primeCompl.map (Ideal.Quotient.mk P)) z
  obtain ⟨g, hg, hgs⟩ := Submonoid.mem_map.mp s.2
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨d, hdD, hdW⟩ : ∃ d ∈ D g, comp g d ∉ W := by
    by_contra hne
    push Not at hne
    exact hg (hsum g ▸ W.sum_mem hne)
  refine ⟨Q f, Q g, Finsupp.equivFunOnFinite.symm d, ?_, ?_⟩
  · have hcoeff : (Q g).coeff (Finsupp.equivFunOnFinite.symm d) = c g d := by
      simp only [Q, coeff_sum, coeff_monomial, EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.sum_ite_eq', if_pos hdD]
    rw [hcoeff]
    refine isUnit_iff_exists_inv.mpr ⟨⟨π (U d) / π (comp g d), div_mem_degZeroLoc P {W} (hUh d)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (fun h' => hdW (hPW h'))
      (by rintro _ rfl; exact hdW)⟩, Subtype.ext ?_⟩
    simp only [c, Subalgebra.coe_mul, Subalgebra.coe_one]
    rw [div_mul_div_cancel₀ (hπ _ fun h' => hUW d (hPW h')), div_self (hπ _ fun h' => hdW (hPW h'))]
  · rw [hQ, hQ, hgs]
    exact hxs

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

