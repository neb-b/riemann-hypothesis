module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTranslateIndicator
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.StepAvg

open MeasureTheory ValuativeRel Matrix Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
private lemma measurableSet_Cgrp_of_isCO {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J) (h : GL (n ⊕ Fin c) k) :
    MeasurableSet (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
  have hJ' : IsOpen (J : Set (GL (n ⊕ Fin c) k)) ∧ IsCompact (J : Set (GL (n ⊕ Fin c) k)) := hJ
  have hset : (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)) =
      (_root_.GlobalTheory.RootEx.R k n c 1 : Set (GL (n ⊕ Fin c) k)) ∩
        (fun x => h⁻¹ * x * h) ⁻¹' (J : Set (GL (n ⊕ Fin c) k)) := by
    ext x
    exact _root_.GlobalTheory.StepData.mem_Cgrp
  have hopen : IsOpen ((fun x : GL (n ⊕ Fin c) k => h⁻¹ * x * h) ⁻¹' (J : Set (GL (n ⊕ Fin c) k))) :=
    hJ'.1.preimage (by fun_prop)
  rw [hset]
  exact (_root_.GlobalTheory.RootEx.VolN.isClosed_R 1).measurableSet.inter hopen.measurableSet

open MeasureTheory ValuativeRel Matrix Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
private lemma integral_indicator_embed_mul_unipotent_lemma (ν : Measure k) [ν.IsAddHaarMeasure]
    {J : Subgroup (GL (n ⊕ Fin c) k)} (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J) (h : GL (n ⊕ Fin c) k)
    (x : GL n k) :
    ∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
        (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
          (_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k))
        ∂(_root_.GlobalTheory.RootEx.volN ν n c 1) =
      (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h) : Set (GL n k)).indicator
        (fun _ => (((_root_.GlobalTheory.RootEx.volN ν n c 1)
          ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal
            : ℂ)) x := by
  haveI := _root_.GlobalTheory.RootEx.VolN.isHaarMeasure_volN (c := c) (n := n) ν 1
  set C := _root_.GlobalTheory.StepData.Cgrp J h
  set E := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  by_cases hx : x ∈ _root_.GlobalTheory.StepData.prX C
  · obtain ⟨u₁, hu₁N, hu₁C⟩ := _root_.GlobalTheory.StepData.mem_prX.mp hx
    let w : _root_.GlobalTheory.RootEx.N k n c 1 :=
      ⟨E x⁻¹ * u₁⁻¹ * (E x⁻¹)⁻¹, _root_.GlobalTheory.RootEx.Radical.conj_mem x⁻¹
        (Subgroup.inv_mem _ hu₁N)⟩
    have key : ∀ u : _root_.GlobalTheory.RootEx.N k n c 1,
        (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (E x * (u : GL (n ⊕ Fin c) k)) =
          ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
            Set (_root_.GlobalTheory.RootEx.N k n c 1))).indicator (fun _ => (1 : ℂ)) (w * u) := by
      intro u
      have hwu : ((w * u : _root_.GlobalTheory.RootEx.N k n c 1) : GL (n ⊕ Fin c) k) =
          (u₁ * E x)⁻¹ * (E x * u) := by
        simp only [w, Subgroup.coe_mul, map_inv, inv_inv, _root_.mul_inv_rev, mul_assoc]
      have hiff : E x * (u : GL (n ⊕ Fin c) k) ∈ C ↔
          w * u ∈ C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) := by
        rw [Subgroup.mem_subgroupOf, hwu, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hu₁C)]
      by_cases hu : E x * (u : GL (n ⊕ Fin c) k) ∈ C
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show w * u ∈ _ from hiff.mp hu)]
      · rw [Set.indicator_of_notMem hu,
          Set.indicator_of_notMem (show w * u ∉ ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
            Set (_root_.GlobalTheory.RootEx.N k n c 1))) from fun h' => hu (hiff.mpr h'))]
    have hmeas : MeasurableSet ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
        Set (_root_.GlobalTheory.RootEx.N k n c 1))) :=
      measurable_subtype_coe (measurableSet_Cgrp_of_isCO hJ h)
    simp_rw [key]
    rw [integral_mul_left_eq_self (fun u => ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
        Set (_root_.GlobalTheory.RootEx.N k n c 1))).indicator (fun _ => (1 : ℂ)) u) w,
      integral_indicator_const _ hmeas, Set.indicator_of_mem hx, measureReal_def, Complex.real_smul,
      mul_one]
  · rw [Set.indicator_of_notMem hx]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
    refine Set.indicator_of_notMem (fun hu => hx ?_) _
    refine _root_.GlobalTheory.StepData.mem_prX.mpr ⟨E x * u * (E x)⁻¹,
      _root_.GlobalTheory.RootEx.Radical.conj_mem x u.2, ?_⟩
    convert hu using 1
    simp [E]


open MeasureTheory ValuativeRel Matrix Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
theorem _root_.GlobalTheory.StepAvg.integral_translate_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c → ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J → ∀ (h : GL (n ⊕ Fin c) k), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h)) → ∀ (m : Measure (GL n k)) [m.IsHaarMeasure], ∀ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : _root_.GlobalTheory.RootEx.N k n c 1, (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * _root_.GlobalTheory.RootEx.embX c g₀)) ∂(_root_.GlobalTheory.RootEx.volN ν n c 1)) ∂m = ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ * ((_root_.GlobalTheory.RootEx.volN ν n c 1 ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal * (m (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h))).toReal) : ℝ) : ℂ) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c hc J hJ h hpr m _ u₀ hu₀ g₀
  haveI := _root_.GlobalTheory.RootEx.VolN.isMulRightInvariant_volN (c := c) (n := n) ν 1
  haveI := _root_.GlobalTheory.SplitFlip.isMulRightInvariant_of_haar (k := k) m
  set C := _root_.GlobalTheory.StepData.Cgrp J h
  set E := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  set V : ℂ := (((_root_.GlobalTheory.RootEx.volN ν n c 1)
    (C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal : ℂ)
  have hinv : _root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) =
      (_root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← _root_.GlobalTheory.SplitWeil.nabs_mul, ← map_mul, inv_mul_cancel, map_one,
      _root_.GlobalTheory.SplitWeil.nabs_one]
  have hpos := _root_.GlobalTheory.SplitWeil.nabs_pos k (Matrix.GeneralLinearGroup.det g₀)
  have ha0 : _root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) ^
      (-((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ))) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ := by
    rw [hinv, Real.inv_rpow hpos.le, Real.rpow_neg hpos.le, inv_inv,
      show ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) = (((c : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring,
      Real.rpow_intCast]
    rfl
  have inner : ∀ g : GL n k,
      ∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
          (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
            (E g * (u : GL (n ⊕ Fin c) k) * (u₀ * E g₀)) ∂(_root_.GlobalTheory.RootEx.volN ν n c 1) =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ •
          (_root_.GlobalTheory.StepData.prX C : Set (GL n k)).indicator (fun _ => V) (g * g₀) := by
    intro g
    have e1 : ∀ u : _root_.GlobalTheory.RootEx.N k n c 1,
        E g * (u : GL (n ⊕ Fin c) k) * (u₀ * E g₀) =
          E (g * g₀) * (E g₀⁻¹ * ((u * ⟨u₀, hu₀⟩ : _root_.GlobalTheory.RootEx.N k n c 1) :
            GL (n ⊕ Fin c) k) * (E g₀⁻¹)⁻¹) := by
      intro u
      simp only [map_mul, map_inv, inv_inv, Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left]
    simp_rw [e1]
    rw [integral_mul_right_eq_self (fun u : _root_.GlobalTheory.RootEx.N k n c 1 =>
        (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
          (E (g * g₀) * (E g₀⁻¹ * (u : GL (n ⊕ Fin c) k) * (E g₀⁻¹)⁻¹))) ⟨u₀, hu₀⟩,
      _root_.GlobalTheory.RootEx.VolN.integral_conj_volN ν le_rfl hc g₀⁻¹
        (fun y => (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (E (g * g₀) * y)),
      integral_indicator_embed_mul_unipotent_lemma ν hJ h (g * g₀), ha0]
    all_goals simp only [C, V]
  have hpr' : IsOpen (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) ∧
      IsCompact (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) := hpr
  have hborel := (_root_.GlobalTheory.SplitWeil.volGL_haar k n ν).1
  have hmeas : MeasurableSet (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) := hpr'.1.measurableSet

  simp_rw [inner]
  rw [integral_smul, integral_mul_right_eq_self (fun g : GL n k =>
      (_root_.GlobalTheory.StepData.prX C : Set (GL n k)).indicator (fun _ => V) g) g₀,
    integral_indicator_const _ hmeas, measureReal_def]
  simp only [V, Complex.real_smul]
  push_cast
  ring

end GlobalTheory.StepAvg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCOPrXCgrp
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.PrCompactOpen

theorem eq_one_of_isCompact {G : Type} [Group G] [TopologicalSpace G] (f : G → ℝ)
    (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x * f y) (hp : ∀ x, 0 < f x)
    {P : Subgroup G} (hP : IsCompact (P : Set G)) {g : G} (hg : g ∈ P) : f g = 1 := by
  have h1 : f 1 = 1 := by
    have e : f 1 * f 1 = f 1 * 1 := by rw [mul_one, ← hm, one_mul]
    exact mul_left_cancel₀ (hp 1).ne' e
  have hpow : ∀ x : G, ∀ m : ℕ, f (x ^ m) = f x ^ m := by
    intro x m
    induction m with
    | zero => simp [h1]
    | succ m ih => rw [pow_succ, hm, ih, pow_succ]
  obtain ⟨B, hB⟩ := (hP.image hc).bddAbove
  have hle : ∀ x ∈ P, f x ≤ 1 := by
    intro x hx
    by_contra hlt
    have hlt := not_le.mp hlt
    obtain ⟨m, hm'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop B).exists
    have : f (x ^ m) ≤ B := hB ⟨x ^ m, P.pow_mem hx m, rfl⟩
    rw [hpow] at this
    linarith
  have hprod : f g * f g⁻¹ = 1 := by rw [← hm, mul_inv_cancel, h1]
  have a := hle g hg
  have b := hle g⁻¹ (P.inv_mem hg)
  nlinarith [mul_le_mul_of_nonneg_left b (hp g).le, hp g⁻¹]

theorem isCO_prX_Cgrp (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (hJ : IsCO J) (h : GL (n ⊕ Fin c) k) :
    IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h),
      valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by
  have := GlobalTheory.SplitWeil.t2Space k
  have key : ∀ F : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k, Continuous (fun x => (F x).val) →
      IsClosed {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} := by
    intro F hF
    have e : {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} = ⋂ r, ⋂ s, {x | lev 1 s ≤ lev 1 r →
        (r.isRight ∨ s.isRight) → (F x).val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, GlobalTheory.RootEx.VolN.InR]
    rw [e]
    exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_imp isOpen_const
      (isClosed_imp isOpen_const (isClosed_eq (hF.matrix_elem r s) continuous_const))
  have hRcl : IsClosed (R k n c 1 : Set (GL (n ⊕ Fin c) k)) := by
    have e : (R k n c 1 : Set (GL (n ⊕ Fin c) k)) =
        {x | GlobalTheory.RootEx.VolN.InR 1 (id x)} ∩ {x | GlobalTheory.RootEx.VolN.InR 1 x⁻¹} := by
      ext x
      exact GlobalTheory.RootEx.VolN.mem_R_iff
    rw [e]
    exact (key id Units.continuous_val).inter (key (fun x => x⁻¹) Units.continuous_coe_inv)
  have hconj : {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} = (fun y => h * y * h⁻¹) '' (J : Set _) := by
    ext x
    constructor
    · intro hx
      exact ⟨h⁻¹ * x * h, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      show h⁻¹ * (h * y * h⁻¹) * h ∈ J
      have e : h⁻¹ * (h * y * h⁻¹) * h = y := by group
      rw [e]
      exact hy
  have hCset : (Cgrp J h : Set (GL (n ⊕ Fin c) k)) =
      {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} ∩ (R k n c 1 : Set _) := by
    ext x
    exact GlobalTheory.StepData.mem_Cgrp.trans and_comm
  have hCc : IsCompact (Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
    rw [hCset, hconj]
    exact (hJ.2.image ((continuous_const.mul continuous_id).mul continuous_const)).inter_right hRcl
  have hOpen : IsOpen (prX (Cgrp J h) : Set (GL n k)) := by
    apply Subgroup.isOpen_of_mem_nhds
    have hV : IsOpen {g : GL n k | h⁻¹ * embX c g * h ∈ J} :=
      hJ.1.preimage ((continuous_const.mul GlobalTheory.QuotInt.continuous_embX).mul continuous_const)
    have h1V : (1 : GL n k) ∈ {g : GL n k | h⁻¹ * embX c g * h ∈ J} := by
      show h⁻¹ * embX c 1 * h ∈ J
      rw [map_one, mul_one, inv_mul_cancel]
      exact J.one_mem
    refine Filter.mem_of_superset (hV.mem_nhds h1V) ?_
    intro g hg
    refine GlobalTheory.StepData.mem_prX.mpr ⟨1, one_mem _, GlobalTheory.StepData.mem_Cgrp.mpr ⟨?_, ?_⟩⟩
    · rw [one_mul]
      exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    · rw [one_mul]
      exact hg
  have hblk : ∀ {A : GL (n ⊕ Fin c) k → Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}, Continuous A →
      Continuous (fun r => (A r).toBlocks₁₁) :=
    fun hA => continuous_pi fun i => continuous_pi fun j => hA.matrix_elem _ _
  have hΦ : Continuous (fun r : GL (n ⊕ Fin c) k =>
      ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁,
        MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) :=
    (hblk Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hblk Units.continuous_coe_inv))
  have himg : Units.embedProduct (Matrix n n k) '' (prX (Cgrp J h) : Set (GL n k)) =
      (fun r : GL (n ⊕ Fin c) k =>
        ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁,
          MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) ''
        (Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨u, hu, huC⟩ := GlobalTheory.StepData.mem_prX.mp hg
      refine ⟨u * embX c g, huC, ?_⟩
      have hinv : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      simp only [hinv, GlobalTheory.QuotInt.block_right g hu, GlobalTheory.QuotInt.block_left g⁻¹ (inv_mem hu),
        Units.embedProduct_apply]
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hrR, -⟩ := GlobalTheory.StepData.mem_Cgrp.mp hr
      obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hrR
      refine ⟨x, GlobalTheory.StepData.mem_prX.mpr ⟨embX c x * u * (embX c x)⁻¹,
        GlobalTheory.RootEx.Radical.conj_mem x hu, by rwa [inv_mul_cancel_right]⟩, ?_⟩
      have hinv : (embX c x * u)⁻¹ = u⁻¹ * embX c x⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      simp only [hinv, GlobalTheory.QuotInt.block_left x hu, GlobalTheory.QuotInt.block_right x⁻¹ (inv_mem hu),
        Units.embedProduct_apply]
  have hcpt : IsCompact (prX (Cgrp J h) : Set (GL n k)) := by
    rw [Units.isEmbedding_embedProduct.isCompact_iff, himg]
    exact hCc.image hΦ
  refine ⟨⟨hOpen, hcpt⟩, fun g hg => ?_⟩
  have hdet : Continuous (fun g : GL n k => Matrix.GeneralLinearGroup.det g) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · have e : (Units.val ∘ fun g : GL n k => Matrix.GeneralLinearGroup.det g) =
          fun g : GL n k => (g : Matrix n n k).det := by
        funext g
        exact Matrix.GeneralLinearGroup.val_det_apply g
      rw [e]
      exact Units.continuous_val.matrix_det
    · have e : (fun g : GL n k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
          fun g : GL n k => ((g⁻¹ : GL n k) : Matrix n n k).det := by
        funext g
        rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
      rw [e]
      exact Units.continuous_coe_inv.matrix_det
  have h1 := eq_one_of_isCompact (fun g : GL n k => nabs k (Matrix.GeneralLinearGroup.det g))
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).continuous.comp hdet)
    (fun x y => by
      simp only [map_mul]
      exact GlobalTheory.SplitWeil.nabs_mul k _ _)
    (fun x => GlobalTheory.SplitWeil.nabs_pos k _) hcpt hg
  refine ⟨(GlobalTheory.SplitWeil.nabs_eq_one_iff _).mp h1, ?_⟩
  show nabs k (Matrix.GeneralLinearGroup.det g) ^ ((c : ℤ) - 1) = 1
  rw [h1, _root_.one_zpow]

end GlobalTheory.PrCompactOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingTopEmb
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology
open scoped TensorProduct

namespace GlobalTheory.RankStrataProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lower

variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]


open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype b] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [DecidableEq d] in
theorem _root_.GlobalTheory.RankStrataProof.mul_apply_of_cols {n : Type} (e : c ⊕ d ≃ a) {x : Matrix b a k} (hx : ∀ i j, x i (e (.inr j)) = 0)
    (g : Matrix a n k) (i : b) (l : n) : (x * g) i l = ∑ m, x i (e (.inl m)) * g (e (.inl m)) l := by
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp [hx]

def rAct (s : Set ℕ) (x : RankIn k a b s) (g : GL a k) : RankIn k a b s :=
  ⟨act x.1 (g, 1), by rw [rank_act]; exact x.2⟩

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL a k) : (_root_.GlobalTheory.RankStrataProof.rAct s x g).1 = x.1 * g.val := by
  unfold _root_.GlobalTheory.RankStrataProof.rAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.rAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val]
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL a k) :
    _root_.GlobalTheory.RankStrataProof.rAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.rAct s (_root_.GlobalTheory.RankStrataProof.rAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, Units.val_mul, Matrix.mul_assoc]




open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
theorem _root_.GlobalTheory.RankStrataProof.isSmoothChar_omChar {μ : kˣ →* ℂˣ} (hμ : _root_.GlobalTheory.SmGL.IsSmoothChar μ) : _root_.GlobalTheory.SmGL.IsSmoothChar (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar a b μ) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar
  apply _root_.GlobalTheory.SmGL.IsSmoothChar.mul
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_fst
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul
      (_root_.GlobalTheory.SmGL.IsSmoothChar.inv hμ)
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_snd
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul hμ
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))

end Lower

section Open

variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]






def lAct (s : Set ℕ) (x : RankIn k a b s) (h : GL b k) : RankIn k a b s :=
  ⟨act x.1 (1, h), by rw [rank_act]; exact x.2⟩

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL b k) : (_root_.GlobalTheory.RankStrataProof.lAct s x g).1 = (g⁻¹).val * x.1 := by
  unfold _root_.GlobalTheory.RankStrataProof.lAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.lAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.lAct_val]
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL b k) :
    _root_.GlobalTheory.RankStrataProof.lAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.lAct s (_root_.GlobalTheory.RankStrataProof.lAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.lAct_val, _root_.GlobalTheory.RankStrataProof.lAct_val, _root_.GlobalTheory.RankStrataProof.lAct_val, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
theorem _root_.GlobalTheory.RankStrataProof.continuous_lAct (s : Set ℕ) : Continuous fun p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s × GL b k => _root_.GlobalTheory.RankStrataProof.lAct s p.1 p.2 := by
  have h : Continuous fun p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s × GL b k => ((p.2⁻¹ : GL b k) : Matrix b b k) * p.1.1 :=
    (Units.continuous_val.comp (continuous_inv.comp continuous_snd)).matrix_mul
      (continuous_subtype_val.comp continuous_fst)
  refine Continuous.subtype_mk (h.congr fun p => (_root_.GlobalTheory.RankStrataProof.lAct_val s p.1 p.2).symm) _

end Open

end GlobalTheory.RankStrataProof
end
end

