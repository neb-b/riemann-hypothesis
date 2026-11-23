module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
public import GroundTheory.AutomorphicForms.GL2.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001
public import GroundTheory.GlobalFields.TateThesis.Bundle0008
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import GroundTheory.LocalFields.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IsCompactBoxSet
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

open GroundTheory.LocalField

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def boxSet (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℤ) : Set (Matrix (Fin 2) (Fin 2) K) :=
  {m | ∀ i j, m i j ∈ valBall K n}

private theorem isOpen_boxSet (n : ℤ) : IsOpen (boxSet K n) := by
  have : boxSet K n = ⋂ i, ⋂ j, (fun X : Matrix (Fin 2) (Fin 2) K => X i j) ⁻¹'
      (valBall K n : Set K) := by
    ext X; simp [boxSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_valBall _).preimage ((continuous_apply j).comp (continuous_apply i))

private theorem isCompact_boxSet (n : ℤ) : IsCompact (boxSet K n) := by
  have : boxSet K n = Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
      (valBall K n : Set K) := by
    ext X
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_valBall n

private def boxGrp (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℤ) : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) K)) where
  carrier := Multiplicative.toAdd ⁻¹' boxSet K n
  one_mem' := fun _ _ => zero_mem _
  mul_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
  inv_mem' := fun ha i j => neg_mem (ha i j)

private theorem lgrp_matrix : Lgrp (Multiplicative (Matrix (Fin 2) (Fin 2) K)) := by
  intro N hN
  have hS : Multiplicative.ofAdd ⁻¹' N ∈ 𝓝 (0 : Matrix (Fin 2) (Fin 2) K) :=
    (continuous_ofAdd.tendsto (0 : Matrix (Fin 2) (Fin 2) K)) hN
  obtain ⟨r, hr⟩ := GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset hS
  refine ⟨boxGrp K r, (isOpen_boxSet (r : ℤ)).preimage continuous_toAdd, ?_, ?_⟩
  · have := (isCompact_boxSet (K := K) (r : ℤ)).image continuous_ofAdd
    convert this using 1
    ext x
    constructor
    · intro hx
      exact ⟨Multiplicative.toAdd x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  · intro x hx
    exact hr hx

private def cgrp (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := {g | g.1 - 1 ∈ boxSet K ((n : ℤ) + 1)}
  one_mem' := by
    intro i j
    simp
  mul_mem' := by
    intro a b ha hb i j
    have e : (a * b).1 - 1 = (a.1 - 1) * (b.1 - 1) + (a.1 - 1) + (b.1 - 1) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]; noncomm_ring
    rw [e]
    refine add_mem (add_mem ?_ (ha i j)) (hb i j)
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    exact valBall_antitone (by omega) (mul_mem_valBall (ha i l) (hb l j))
  inv_mem' := by
    intro g hg i j
    have e : (g⁻¹).1 = !![g.1 1 1, -g.1 0 1; -g.1 1 0, g.1 0 0] := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    have h00 := hg 0 0
    have h01 := hg 0 1
    have h10 := hg 1 0
    have h11 := hg 1 1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h00 h11
    simp only [Matrix.sub_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h01 h10
    rw [e]
    fin_cases i <;> fin_cases j <;> simp
    · exact h11
    · exact h01
    · exact h10
    · exact h00

private theorem isOpen_cgrp (n : ℕ) :
    IsOpen (cgrp K n : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  have hc : Continuous fun g : Matrix.SpecialLinearGroup (Fin 2) K => g.1 - 1 :=
    continuous_subtype_val.sub continuous_const
  exact (isOpen_boxSet _).preimage hc

private theorem isCompact_cgrp [T2Space K] (n : ℕ) :
    IsCompact (cgrp K n : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  refine (Subtype.isCompact_iff (p := fun A : Matrix (Fin 2) (Fin 2) K => A.det = 1)).2 ?_
  have hC : IsCompact ((fun m : Matrix (Fin 2) (Fin 2) K => m + 1) '' boxSet K ((n : ℤ) + 1)) :=
    (isCompact_boxSet _).image (continuous_id.add continuous_const)
  have hD : IsClosed {m : Matrix (Fin 2) (Fin 2) K | m.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  convert hC.inter_right hD using 1
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g.1 - 1, hg, by simp⟩, g.2⟩
  · rintro ⟨⟨y, hy, rfl⟩, hd⟩
    refine ⟨⟨y + 1, hd⟩, ?_, rfl⟩
    change (y + 1) - 1 ∈ boxSet K ((n : ℤ) + 1)
    simpa using hy

private theorem lgrp_sl [T2Space K] : Lgrp (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro N hN
  obtain ⟨W, hW', hWN⟩ := (mem_nhds_subtype {A : Matrix (Fin 2) (Fin 2) K | A.det = 1} (1 : Matrix.SpecialLinearGroup (Fin 2) K) N).1 hN
  have hW : W ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) K) := hW'
  have hS : (fun m : Matrix (Fin 2) (Fin 2) K => m + 1) ⁻¹' W ∈ 𝓝 (0 : Matrix (Fin 2) (Fin 2) K) := by
    have hc : Continuous fun m : Matrix (Fin 2) (Fin 2) K => m + 1 :=
      continuous_id.add continuous_const
    have := hc.tendsto (0 : Matrix (Fin 2) (Fin 2) K)
    rw [zero_add] at this
    exact this hW
  obtain ⟨r, hr⟩ := GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset hS
  refine ⟨cgrp K r, isOpen_cgrp r, isCompact_cgrp r, fun g hg => hWN ?_⟩
  have h1 : g.1 - 1 ∈ (fun m : Matrix (Fin 2) (Fin 2) K => m + 1) ⁻¹' W :=
    hr fun i j => valBall_antitone (m := (r : ℤ)) (n := (r : ℤ) + 1) (by omega) (hg i j)
  have h2 : (g.1 - 1) + 1 ∈ W := h1
  rw [sub_add_cancel] at h2
  exact h2

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.lgrp :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), Lgrp (SL v) ∧ Lgrp (Multiplicative (M2 v)) := by
  intro F _ _ v
  exact ⟨lgrp_sl, lgrp_matrix⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.MatLaws
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

section

variable {F : Type} [Field F] [NumberField F] (v : P F)

private theorem cp_cont : Continuous (cp v) := by
  have h1 : Continuous (pLoc F v) :=
    RestrictedProduct.continuous_eval (R := fun v : P F => v.adicCompletion F) v
  have h2 : Continuous (pFin F) := continuous_snd
  exact h1.comp h2

private theorem cp_rt (c : F) : cp v (rt c) = algebraMap F (Kv v) c := rfl

private theorem cp_sg (x : Kv v) : cp v (sg v x) = x := (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.2.1 x

private theorem sg_cp (a : A F) : sg v (cp v a) = a * sg v 1 := by
  rw [(UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.1 a 1, mul_one]

private theorem e_idem : sg v 1 * sg v 1 = sg v 1 := by
  rw [← sg_cp v (sg v 1), cp_sg]

private theorem away_eq (X : V4 F) (i : Fin 4) : away v X i = (1 - sg v 1) * X i := by
  change X i - sg v (cp v (X i)) = _
  rw [sg_cp]; ring

private theorem cp_away (X : V4 F) (i : Fin 4) : cp v (away v X i) = 0 := by
  change cp v (X i - sg v (cp v (X i))) = 0
  rw [map_sub, cp_sg, sub_self]

private theorem sg_add' (x y : Kv v) : sg v (x + y) = sg v x + sg v y :=
  (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).1 x y

private theorem two_ne : (2 : Kv v) ≠ 0 := by
  intro h
  have h' : algebraMap F (Kv v) 2 = algebraMap F (Kv v) 0 := by
    rw [map_ofNat, map_zero]; exact h
  exact two_ne_zero ((algebraMap F (Kv v)).injective h')

end

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.matLaws :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (δ : F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) δ → θ ≠ 0 →
      (∀ m : M2 v, ∃ y : V4 F, ∀ X, mat v θ (X + y) = mat v θ X + m ∧ away v (X + y) = away v X) ∧
      (∀ X Y, B4 δ Y X = B4 δ (away v Y) (away v X) + sg v (BM (mat v θ Y) (mat v θ X))) ∧
      (∀ b X, sg v b * q4 δ X = sg v (-(b * (mat v θ X).det))) ∧
      Continuous (mat v θ) ∧ Continuous (away v) ∧ (∀ X, away v (away v X) = away v X) ∧
      ∀ X, mat v θ (away v X) = 0 := by
  intro F _ _ v δ θ hθ hθ0
  have h2 := two_ne v
  have hc := cp_cont v
  have hs : Continuous (sg v) := (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    refine ⟨![sg v (m 1 1), sg v (m 0 0), sg v ((m 0 1 + m 1 0) / 2), sg v ((m 0 1 - m 1 0) / (2 * θ))],
      fun X => ⟨?_, ?_⟩⟩
    · have e1 : (m 0 1 + m 1 0) / 2 + (m 0 1 - m 1 0) / (2 * θ) * θ = m 0 1 := by
        field_simp
        ring
      have e2 : (m 0 1 + m 1 0) / 2 - (m 0 1 - m 1 0) / (2 * θ) * θ = m 1 0 := by
        field_simp
        ring
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j
      · change cp v (X 1 + sg v (m 0 0)) = cp v (X 1) + m 0 0
        rw [map_add (f := _), cp_sg]
      · change cp v (X 2 + sg v ((m 0 1 + m 1 0) / 2)) +
            cp v (X 3 + sg v ((m 0 1 - m 1 0) / (2 * θ))) * θ = cp v (X 2) + cp v (X 3) * θ + m 0 1
        rw [map_add (f := _), map_add (f := _), cp_sg, cp_sg]
        linear_combination e1
      · change cp v (X 2 + sg v ((m 0 1 + m 1 0) / 2)) -
            cp v (X 3 + sg v ((m 0 1 - m 1 0) / (2 * θ))) * θ = cp v (X 2) - cp v (X 3) * θ + m 1 0
        rw [map_add (f := _), map_add (f := _), cp_sg, cp_sg]
        linear_combination e2
      · change cp v (X 0 + sg v (m 1 1)) = cp v (X 0) + m 1 1
        rw [map_add (f := _), cp_sg]
    · funext i
      change (X i + _) - sg v (cp v (X i + _)) = X i - sg v (cp v (X i))
      rw [map_add (f := _), sg_add']
      fin_cases i <;> simp [cp_sg] <;> ring
  · intro X Y
    have hB : BM (mat v θ Y) (mat v θ X) = cp v (B4 δ Y X) := by
      simp only [BM, mat, B4, map_sub, map_add (f := _), map_mul, cp_rt, ← hθ, map_ofNat]
      simp
      ring
    rw [hB, sg_cp]
    have he := e_idem v
    simp only [B4, away_eq]
    generalize sg v 1 = e at he
    generalize rt δ = d
    linear_combination (-(2 * (Y 2 * X 2 - d * (Y 3 * X 3)) - Y 1 * X 0 - Y 0 * X 1)) * he
  · intro b X
    have hq : -(b * (mat v θ X).det) = cp v (q4 δ X) * b := by
      simp only [mat, q4, Matrix.det_fin_two_of, map_sub, map_mul, map_pow, cp_rt, ← hθ]
      ring
    rw [hq, mul_comm, (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.1]
  · refine continuous_matrix fun i j => ?_
    have h : ∀ k : Fin 4, Continuous fun X : V4 F => cp v (X k) := fun k => hc.comp (continuous_apply k)
    fin_cases i <;> fin_cases j <;> simp [mat]
    · exact h 1
    · exact (h 2).add ((h 3).mul continuous_const)
    · exact (h 2).sub ((h 3).mul continuous_const)
    · exact h 0
  · refine continuous_pi fun i => ?_
    exact (continuous_apply i).sub (hs.comp (hc.comp (continuous_apply i)))
  · intro X
    funext i
    change away v X i - sg v (cp v (away v X i)) = _
    rw [cp_away]
    have : sg v 0 = 0 := by
      have := sg_add' v 0 0
      simpa using this
    rw [this, sub_zero]
  · intro X
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, cp_away]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem sg_eq_incl {F : Type} [Field F] [NumberField F] (v : P F) (x : Kv v) :
    sg v x = finitePlaceIncl v x := by
  obtain ⟨-, -, h3, -, -, -, -, h8, -, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws F v
  refine Prod.ext ?_ ?_
  · rw [(h8 x).1, finitePlaceIncl_apply, finiteAdeleInr_fst]
  · rw [finitePlaceIncl_apply, finiteAdeleInr_snd]
    refine Subtype.ext (funext fun u => ?_)
    by_cases hu : u = v
    · subst hu
      exact (h3 x).trans (finiteAdeleSingleAdd_apply_self u x).symm
    · exact ((h8 x).2 u hu).trans (finiteAdeleSingleAdd_apply_of_ne hu x).symm

private theorem exists_char_ne {F : Type} [Field F] [NumberField F] (v : P F) :
    ∃ y, localAdelicChar F v y ≠ 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (FractionalIdeal.count F v ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) + 1))
  have h := (forall_localAdelicChar_mul_eq_one_iff v z).1 fun a _ => hc _
  rw [mem_localInvDifferent_iff_valued, hz, WithZero.exp_le_exp] at h
  omega

private theorem locConst_of_char {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (χ : AddChar G Circle) (H : AddSubgroup G)
    (hH : IsOpen (H : Set G)) (h1 : ∀ y ∈ H, χ y = 1) :
    IsLocallyConstant fun x => ((χ x : Circle) : ℂ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h0 := hH.mem_nhds (zero_mem H)
  have hcc : Continuous fun y : G => y - x := continuous_id.sub continuous_const
  have hc : Filter.Tendsto (fun y : G => y - x) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self] using hcc.tendsto x
  filter_upwards [hc h0] with y hy
  have e := AddChar.map_add_eq_mul χ (y - x) x
  rw [h1 _ hy, one_mul, sub_add_cancel] at e
  rw [e]

private theorem psi_locConst {F : Type} [Field F] [NumberField F] (v : P F) :
    IsLocallyConstant (ψl v) :=
  locConst_of_char (localAdelicChar F v) (localInvDifferent v) (isOpen_localInvDifferent v)
    fun _ hy => localAdelicChar_eq_one_of_mem hy

private theorem ab_idl_eq {F : Type} [Field F] [NumberField F] (v : P F) (t : (Kv v)ˣ) :
    ab (idl v t) = (GroundTheory.LocalField.modulus (t : Kv v) : ℝ) := by
  obtain ⟨-, -, -, -, -, h6, h7, -, -, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws F v
  let f0 : (Kv v)ˣ →* ℝ :=
    { toFun := fun t => ab (idl v t)
      map_one' := by simp [ab, idl]
      map_mul' := fun a b => by simp [ab, idl] }
  have hz : ∀ (x : (Kv v)ˣ) (n : ℤ), f0 (x ^ n) = f0 x ^ n := fun x n => by
    have := congrArg Units.val (map_zpow f0.toHomUnits x n)
    simpa using this
  set ϖ := GroundTheory.LocalField.unifUnit (Kv v) with hϖ
  have hϖ1 : GroundTheory.LocalField.ord (ϖ : Kv v) = 1 := by
    simpa using GroundTheory.LocalField.ord_unifUnit_zpow (K := Kv v) 1
  have hU : IsU ϖ := by
    show Valued.v (ϖ : Kv v) = _
    rw [valued_eq_exp_neg_ord ϖ.ne_zero, hϖ1]
    rfl
  have hu : f0 (ϖ ^ (-GroundTheory.LocalField.ord (t : Kv v)) * t) = 1 := h7 _ (by
    rw [valued_eq_one_iff_ord (Units.ne_zero _), GroundTheory.LocalField.ord_units_mul,
      GroundTheory.LocalField.ord_unifUnit_zpow]
    omega)
  have e : f0 t = f0 ϖ ^ GroundTheory.LocalField.ord (t : Kv v) := by
    conv_lhs => rw [GroundTheory.LocalField.eq_unifUnit_zpow_mul t]
    rw [map_mul, hz, hu, mul_one]
  show f0 t = _
  rw [e, show f0 ϖ = _ from h6 ϖ hU, GroundTheory.LocalField.modulus_of_ne_zero t.ne_zero,
    residueCard_adicCompletion]
  push_cast
  rw [_root_.inv_zpow, _root_.zpow_neg]

theorem UpperTheory.ConvolutionTheory.R2.I.psiLaws :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), localAdelicChar F v ≠ 1 ∧ (∀ x, ψ (sg v x) = ψl v x) ∧ (∀ x y, ψl v (x + y) = ψl v x * ψl v y) ∧
      IsLocallyConstant (ψl v) ∧ (∀ x : Kv v, x ≠ 0 → ∃ s, ψl v (s * x) ≠ 1) ∧
      ∀ t : (Kv v)ˣ, ab (idl v t) = (GroundTheory.LocalField.modulus (t : Kv v) : ℝ) := by
  intro F _ _ v
  refine ⟨fun h => ?_, fun x => ?_, fun x y => ?_, psi_locConst v, fun x hx => ?_, ab_idl_eq v⟩
  · obtain ⟨y, hy⟩ := exists_char_ne v
    exact hy (by rw [h]; rfl)
  · simp only [ψ, ψl, sg_eq_incl, localAdelicChar_apply]
  · simp only [ψl, AddChar.map_add_eq_mul, Circle.coe_mul]
  · obtain ⟨y, hy⟩ := exists_char_ne v
    refine ⟨y / x, fun h => hy ?_⟩
    rw [div_mul_cancel₀ y hx] at h
    exact Circle.coe_eq_one.1 h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.TendstoPowZeroOfValuation
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem tendsto_pow_zero_of_valuation {K : Type} [Field K] [NumberField K] (v : P K) (y : Kv v)
    (hy : Valued.v y < 1) : Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero (Kv v) _).tendsto_right_iff]
  intro γ _
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hy (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := ((Valued.v : Valuation (Kv v) (WithZero (Multiplicative ℤ))) : Kv v →*₀ WithZero (Multiplicative ℤ)))).toMonoidHom γ)
  filter_upwards [eventually_ge_atTop n] with m hm
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hy.le hm) hn

private theorem valuation_lt_one_of_tendsto {K : Type} [Field K] [NumberField K] (v : P K) (y : Kv v)
    (hy : Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0)) : Valued.v y < 1 := by
  have h1 := (Valued.hasBasis_nhds_zero (Kv v) _).mem_of_mem (i := 1) trivial
  obtain ⟨n, hn⟩ := (hy.eventually h1 |>.and (eventually_gt_atTop 0)).exists
  obtain ⟨hn1, hn0⟩ := hn
  simp only [Set.mem_setOf_eq, Units.val_one, Valuation.restrict_lt_one_iff] at hn1
  rw [map_pow] at hn1
  by_contra hc
  exact absurd hn1 (not_lt.mpr (one_le_pow₀ (not_lt.mp hc)))

theorem UpperTheory.ConvolutionTheory.R2.I.below :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : P K) (w : P L) (i : Kv v →+* Kv w),
      Continuous i → (∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → Below v w := by
  intro K L _ _ _ _ _ v w i hi hx
  have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) := by
    intro x hxv
    rw [Ideal.mem_comap]
    have h1 : Valued.v (algebraMap K (Kv v) (x : K)) < 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) x).mpr hxv
      rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    have h2 := tendsto_pow_zero_of_valuation v _ h1
    have h3 : Tendsto (fun n : ℕ => (i (algebraMap K (Kv v) (x : K))) ^ n) atTop (𝓝 0) := by
      have := (hi.tendsto 0).comp h2
      simpa [Function.comp_def, map_pow] using this
    have h4 := valuation_lt_one_of_tendsto w _ h3
    rw [hx] at h4
    have h5 : algebraMap K L (x : K) = ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) := rfl
    rw [h5] at h4
    apply (w.valuation_lt_one_iff_mem (K := L) _).mp
    rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) hle
end

