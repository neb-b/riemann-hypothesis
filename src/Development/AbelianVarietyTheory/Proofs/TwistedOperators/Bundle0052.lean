module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsQuotIntCosetFn
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.CosetQuotInt


open MeasureTheory ValuativeRel Matrix Topology in
theorem _root_.GlobalTheory.CosetQuotInt.isQuotInt_cosetFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J)
    (h : GL (n ⊕ Fin c) k)
    (m : Measure (GL n k)) (v : ℝ) (hv : v ≠ 0)
    (hvol : ∀ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1, ∀ g₀ : GL n k, ∫ g,
      (∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
      (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
        (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
          (u₀ * _root_.GlobalTheory.RootEx.embX c g₀))
          ∂(_root_.GlobalTheory.RootEx.volN ν n c 1)) ∂m
          = ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ * v : ℝ) : ℂ))
    (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ)
    (hf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCosetFn J h f) :
    _root_.GlobalTheory.RootEx.IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by
  classical
  haveI : BorelSpace (GL (n ⊕ Fin c) k) :=
    (_root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν).1
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) :=
    (_root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν).2.2.1
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO at hJ
  obtain ⟨hJo, hJc⟩ := hJ
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCosetFn at hf
  obtain ⟨hleft, hright, hsupp⟩ := hf
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hv
  have hembP : ∀ g : GL n k,
      _root_.GlobalTheory.RootEx.embX c g ∈ _root_.GlobalTheory.RootEx.R k n c 1 := by
    intro g
    unfold _root_.GlobalTheory.RootEx.R
    exact Subgroup.mem_sup_left ⟨g, rfl⟩
  have hNP : ∀ u ∈ _root_.GlobalTheory.RootEx.N k n c 1,
      u ∈ _root_.GlobalTheory.RootEx.R k n c 1 := by
    intro u hu
    unfold _root_.GlobalTheory.RootEx.R
    exact Subgroup.mem_sup_right hu
  obtain ⟨F, hFdef⟩ : ∃ F : GL (n ⊕ Fin c) k → ℂ,
      ∀ x, F x = if h⁻¹ * x ∈ J then f h / (v : ℂ) else 0 := ⟨_, fun _ => rfl⟩
  unfold _root_.GlobalTheory.RootEx.IsQuotInt
  refine ⟨F, ?_, fun x => ?_, ?_⟩
  · have hSB := _root_.GlobalTheory.QuotInt.sb_of_quot J hJo hJc
      {(h : GL (n ⊕ Fin c) k ⧸ J)}
      (fun q => if q = (h : GL (n ⊕ Fin c) k ⧸ J) then f h / (v : ℂ) else 0)
      (fun q hq => by
        simp only [Finset.mem_singleton] at hq
        simp [hq])
    have hFq : F = fun y : GL (n ⊕ Fin c) k => (fun q : GL (n ⊕ Fin c) k ⧸ J =>
        if q = (h : GL (n ⊕ Fin c) k ⧸ J) then f h / (v : ℂ) else 0) (y : GL (n ⊕ Fin c) k ⧸ J) := by
      funext y
      rw [hFdef]
      dsimp only
      by_cases hy : h⁻¹ * y ∈ J
      · rw [if_pos hy, if_pos (QuotientGroup.eq.2 hy).symm]
      · rw [if_neg hy, if_neg (fun (he : (y : GL (n ⊕ Fin c) k ⧸ J) = h) =>
          hy (QuotientGroup.eq.1 he.symm))]
    rw [hFq]
    exact hSB
  · by_cases hx : DoubleCoset.mk (_root_.GlobalTheory.RootEx.R k n c 1) J h =
        DoubleCoset.mk (_root_.GlobalTheory.RootEx.R k n c 1) J x
    · obtain ⟨p, hp, j, hj, rfl⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hx
      obtain ⟨x₀, u', hu', rfl⟩ := _root_.GlobalTheory.RootEx.VolN.exists_of_mem_R hp
      obtain ⟨u₀, hu₀, hpeq⟩ : ∃ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1,
          _root_.GlobalTheory.RootEx.embX c x₀ * u' = u₀ * _root_.GlobalTheory.RootEx.embX c x₀ :=
        ⟨_, _root_.GlobalTheory.RootEx.Radical.conj_mem x₀ hu', by group⟩
      rw [hpeq, hright _ j hj, hleft u₀ hu₀ x₀ h]
      have hpt : ∀ (g : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c 1),
          F (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) =
          f h / (v : ℂ) * (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator
            (fun _ => (1 : ℂ)) (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) := by
        intro g u
        have hyP : _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀) ∈ _root_.GlobalTheory.RootEx.R k n c 1 :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (hembP g) (hNP _ u.2))
            (Subgroup.mul_mem _ (hNP _ hu₀) (hembP x₀))
        have hiff : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) ∈ J ↔
            h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h ∈ J := by
          have heq : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) =
              h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h * j := by group
          rw [heq, J.mul_mem_cancel_right hj]
        rw [hFdef]
        by_cases hin : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h ∈ J
        · rw [if_pos (hiff.2 hin), Set.indicator_of_mem
            (show _ ∈ _root_.GlobalTheory.StepData.Cgrp J h from
              _root_.GlobalTheory.StepData.mem_Cgrp.2 ⟨hyP, hin⟩), mul_one]
        · rw [if_neg (fun h' => hin (hiff.1 h')), Set.indicator_of_notMem
            (show _ ∉ _root_.GlobalTheory.StepData.Cgrp J h from
              fun h' => hin (_root_.GlobalTheory.StepData.mem_Cgrp.1 h').2), mul_zero]
      simp_rw [hpt, integral_const_mul]
      rw [hvol u₀ hu₀ x₀]
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR
      rw [Complex.ofReal_mul, div_mul_eq_mul_div, eq_div_iff hv']
      ring
    · have hfx : f x = 0 := hsupp x (fun he => hx he.symm)
      rw [hfx]
      have hpt : ∀ (g : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c 1),
          F (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * x) = 0 := by
        intro g u
        rw [hFdef, if_neg]
        intro hmem
        apply hx
        refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(_root_.GlobalTheory.RootEx.embX c g *
          (u : GL (n ⊕ Fin c) k))⁻¹, Subgroup.inv_mem _ (Subgroup.mul_mem _ (hembP g)
            (hNP _ u.2)), h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * x),
          hmem, by group⟩
      simp_rw [hpt, integral_zero]
  · have hFind : F = ((fun y => h⁻¹ * y) ⁻¹' (J : Set (GL (n ⊕ Fin c) k))).indicator
        (fun _ => f h / (v : ℂ)) := by
      funext y
      rw [hFdef]
      by_cases hy : h⁻¹ * y ∈ J
      · rw [if_pos hy, Set.indicator_of_mem (show y ∈ (fun y => h⁻¹ * y) ⁻¹' (J : Set _) from hy)]
      · rw [if_neg hy,
          Set.indicator_of_notMem (show y ∉ (fun y => h⁻¹ * y) ⁻¹' (J : Set _) from hy)]
    rw [hFind, integral_indicator_const _
      (hJo.measurableSet.preimage (measurable_const_mul h⁻¹)), measureReal_def,
      measure_preimage_mul, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.CosetQuotInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixEntrywiseProductMeasureUniformizerPowerBox
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.BoxVolume

theorem prod_zpow_nnreal {ι : Type} (d : ℝ≥0) (hd : d ≠ 0) (f : ι → ℤ) (s : Finset ι) :
    ∏ i ∈ s, d ^ f i = d ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hd]

theorem volM_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [Fintype D] (c : A → D → ℤ),
    volM ν A D {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} =
      ν (𝒪[k] : Set k) ^ (Fintype.card A * Fintype.card D) *
        ENNReal.ofReal ((resCard k : ℝ) ^ (-∑ i, ∑ j, c i j)) := by
  intro k _ _ _ _ _ _ ν _ ϖ hϖ A D _ _ c
  haveI := secondCountable k
  haveI := t2Space k
  have hset : ({y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} :
      Set (A → D → k)) = Set.univ.pi fun i => Set.univ.pi fun j => cball (ϖ ^ c i j) := by
    ext y
    simp only [Set.mem_univ_pi, cball, Set.mem_setOf_eq, Units.val_zpow_eq_zpow_val]
    rfl
  set d : ℝ≥0 := distribHaarChar k ϖ with hd
  have hdq : (d : ℝ) = (resCard k : ℝ)⁻¹ := nabs_unif hϖ
  have hd0 : d ≠ 0 := (distribHaarChar_pos (A := k) (g := ϖ)).ne'
  have hcb : ∀ i j, ν (cball (ϖ ^ c i j)) = ((d ^ c i j : ℝ≥0) : ℝ≥0∞) * ν (𝒪[k] : Set k) := by
    intro i j
    rw [measure_cball, map_zpow]
  rw [volM]
  erw [hset, Measure.pi_pi]
  simp_rw [Measure.pi_pi, hcb, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm (ν _ ^ _)]
  rw [Nat.mul_comm (Fintype.card D)]
  congr 1
  have hz : ∏ i, ∏ j, d ^ c i j = d ^ (∑ i, ∑ j, c i j) := by
    simp_rw [prod_zpow_nnreal d hd0]
  have hz' : (∏ i, ∏ j, ((d ^ c i j : ℝ≥0) : ℝ≥0∞)) =
      ((d ^ (∑ i, ∑ j, c i j) : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast hz
  rw [hz', ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_zpow, hdq, _root_.inv_zpow']

end GlobalTheory.BoxVolume
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureRealDoubleCosetEqRelIndexConjMul
section
open MeasureTheory Pointwise

namespace GlobalTheory

theorem mem_map_conj_iff_conj_mem {G : Type} [Group G] (J : Subgroup G) (g x : G) :
    x ∈ J.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem measureReal_doubleCoset_eq_relIndex_mul :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ g : G,
    μ.real (DoubleCoset.doubleCoset g (J : Set G) (J : Set G)) =
      ((J.map (MulAut.conj g).toMonoidHom).relIndex J : ℝ) * μ.real (J : Set G) := by
  intro G _ _ _ _ _ μ _ J hJo hJc g
  set K := J.map (MulAut.conj g).toMonoidHom with hK
  set H : Subgroup J := K.subgroupOf J with hH
  haveI : CompactSpace J := isCompact_iff_compactSpace.1 hJc
  have hKo : IsOpen (K : Set G) := by
    have : (K : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (J : Set G) := by
      ext x; rw [SetLike.mem_coe, hK, mem_map_conj_iff_conj_mem]; rfl
    rw [this]; exact hJo.preimage (by fun_prop)
  have hHo : IsOpen (H : Set J) := by
    have : (H : Set J) = Subtype.val ⁻¹' (K : Set G) := by
      ext x; simp [hH, Subgroup.mem_subgroupOf]
    rw [this]; exact hKo.preimage continuous_subtype_val
  haveI : Finite (J ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (J ⧸ H) := Fintype.ofFinite _
  let f : J ⧸ H → Set G := fun q => ((q.out : J) * g : G) • (J : Set G)
  have hcover : DoubleCoset.doubleCoset g (J : Set G) (J : Set G) = ⋃ q, f q := by
    ext x
    simp only [DoubleCoset.doubleCoset, Set.mem_mul, Set.mem_singleton_iff, Set.mem_iUnion, f,
      Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ⟨j, hj, b, hb, rfl⟩, k, hk, rfl⟩
      rw [hb]
      refine ⟨(QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H), ?_⟩
      set o := (Quotient.out (QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H) : J) with ho
      have h1 : (QuotientGroup.mk o : J ⧸ H) = QuotientGroup.mk (⟨j, hj⟩ : J) := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq] at h1
      have h2 : ((o : G))⁻¹ * j ∈ K := by
        have := Subgroup.mem_subgroupOf.1 (hH ▸ h1)
        simpa using this
      rw [hK, mem_map_conj_iff_conj_mem] at h2
      refine ⟨g⁻¹ * ((o : G)⁻¹ * j) * g * k, J.mul_mem h2 hk, ?_⟩
      group
    · rintro ⟨q, y, hy, rfl⟩
      exact ⟨(q.out : J) * g, ⟨(q.out : J), (q.out : J).2, g, rfl, rfl⟩, y, hy, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 ?_
    rintro x hx hx'
    simp only [f, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe] at hx hx'
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', hxy⟩ := hx'
    apply hqq'
    have e : ((q.out : J) : G) = (q'.out : J) * g * y' * y⁻¹ * g⁻¹ := by
      rw [hxy]; group
    have hmem : (q.out)⁻¹ * q'.out ∈ H := by
      change _ ∈ K.subgroupOf J
      rw [Subgroup.mem_subgroupOf, hK, mem_map_conj_iff_conj_mem]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      have : g⁻¹ * ((((q'.out : J) : G) * g * y' * y⁻¹ * g⁻¹)⁻¹ * (q'.out : J)) * g = y * y'⁻¹ := by group
      rw [this]
      exact J.mul_mem hy (J.inv_mem hy')
    have := (QuotientGroup.eq (s := H)).2 hmem
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  have hmeas : ∀ q, MeasurableSet (f q) := fun q =>
    (hJo.smul ((q.out : J) * g : G)).measurableSet
  have hval : ∀ q, μ (f q) = μ (J : Set G) := fun q => measure_smul μ _ _
  have hfin : μ (J : Set G) ≠ ⊤ := (hJc.measure_lt_top).ne
  rw [hcover, measureReal_def, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def, Subgroup.relIndex,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.FourierJacobiGroup

theorem uni_conj {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ι → ℕ}
    {A B M : Matrix ι ι k} (hA : ∀ r s, b r ≠ b s → A r s = 0) (hB : ∀ r s, b r ≠ b s → B r s = 0)
    (hAB : A * B = 1) (hM : Radical.Uni b M) : Radical.Uni b (A * M * B) := by
  intro r s hrs
  have : (A * M * B) r s = (A * (1 : Matrix ι ι k) * B) r s := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => ?_
    by_cases h1 : b r = b t
    · by_cases h2 : b u = b s
      · rw [hM t u (by omega)]
      · rw [hB u s h2, mul_zero, mul_zero]
    · simp only [hA r t h1, zero_mul]
  rw [this, Matrix.mul_one, hAB]

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem colE_add (q : ℕ) (β γ : n → k) : colE c q β * colE c q γ = colE c q (β + γ) := by
  apply Units.ext
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply]
  congr 1 <;> simp
  ext r i
  by_cases h : i.val + 1 = q <;> simp [h, add_comm]

theorem colE_inv (q : ℕ) (β : n → k) : (colE c q β)⁻¹ = colE c q (-β) :=
  inv_eq_of_mul_eq_one_right (QuotStep.colE_neg q β)

theorem colE_zero (q : ℕ) : colE c q (0 : n → k) = 1 := by
  have := QuotStep.colE_neg (c := c) q (0 : n → k)
  rwa [colE_add, add_neg_cancel] at this

theorem colE_offdiag (q : ℕ) (β : n → k) (r s : n ⊕ Fin c) (h : lev q r ≠ lev q s) :
    (colE c q β).val r s = 0 := by
  rcases r with r | r <;> rcases s with s | s
  · simp [lev] at h
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at h
    simp [colE, upU, h.symm]
  · simp [colE, upU]
  · have : r ≠ s := by
      rintro rfl
      exact h rfl
    simp [colE, upU, this]

theorem colE_conj_mem (q : ℕ) (β : n → k) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c q) :
    colE c q β * u * (colE c q β)⁻¹ ∈ N k n c q := by
  rw [Radical.mem_N_iff] at hu ⊢
  rw [colE_inv]
  exact uni_conj (b := lev q) (colE_offdiag q β) (colE_offdiag q (-β))
    (congrArg Units.val (QuotStep.colE_neg q β)) hu

theorem exists_of_mem_N {p : ℕ} (hp : p < c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    ∃ u ∈ N k n c (p + 1), ∃ β : n → k, g = u * colE c (p + 1) β := by
  let β : n → k := fun x => g.val (Sum.inl x) (Sum.inr ⟨p, hp⟩)
  refine ⟨g * colE c (p + 1) (-β), ?_, β, by rw [mul_assoc, colE_add, neg_add_cancel, colE_zero, mul_one]⟩
  have h1 := (Radical.mem_N_iff _).1 (mul_mem hg (Radical.colE_mem (-β) (Nat.lt_succ_self p)))
  have h0 := (Radical.mem_N_iff _).1 hg
  rw [Radical.mem_N_iff]
  intro r s hrs
  by_cases h : lev p s ≤ lev p r
  · exact h1 r s h
  rcases r with r | r <;> rcases s with s | s <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h hrs
  · omega
  · obtain rfl : s = ⟨p, hp⟩ := Fin.ext (by simp only; omega)
    have h2 : ∀ y, g.val (Sum.inl r) (Sum.inl y) = (1 : Matrix n n k) r y := fun y => by
      rw [h0 _ _ (by simp [lev])]; simp [Matrix.one_apply]
    simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, h2, Matrix.one_apply, β]
  · omega
  · omega

theorem colE_conj_mem_R (q : ℕ) (β : n → k) {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c q) :
    ∃ r' ∈ R k n c q, ∃ γ : n → k, colE c q β * r = r' * colE c q γ := by
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  refine ⟨embX c x * (colE c q ((x⁻¹).val.mulVec β) * u * (colE c q ((x⁻¹).val.mulVec β))⁻¹),
    mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right (colE_conj_mem q _ hu)),
    (x⁻¹).val.mulVec β, ?_⟩
  rw [← QuotStep.conj_colE, map_inv]
  group

theorem mem_RFJ_iff : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ RFJ k n c ρ ↔ ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β) ∧ ∀ β : n → k, ∀ u ∈ N k n c (ρ + 1), colE c (ρ + 1) β * u * (colE c (ρ + 1) β)⁻¹ ∈ N k n c (ρ + 1) := by
  intro k _ n _ _ c ρ _ hρ
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, fun β u hu => colE_conj_mem _ β hu⟩
  · let S : Subgroup (GL (n ⊕ Fin c) k) :=
      { carrier := {g | ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β}
        one_mem' := ⟨1, one_mem _, 0, by rw [colE_zero, mul_one]⟩
        mul_mem' := by
          rintro _ _ ⟨r, hr, β, rfl⟩ ⟨r₂, hr₂, β₂, rfl⟩
          obtain ⟨r', hr', γ, e⟩ := colE_conj_mem_R (ρ + 1) β hr₂
          refine ⟨r * r', mul_mem hr hr', γ + β₂, ?_⟩
          rw [← colE_add, mul_assoc r, ← mul_assoc _ r₂, e]
          simp only [mul_assoc]
        inv_mem' := by
          rintro _ ⟨r, hr, β, rfl⟩
          obtain ⟨r', hr', γ, e⟩ := colE_conj_mem_R (ρ + 1) (-β) (inv_mem hr)
          exact ⟨r', hr', γ, by rw [_root_.mul_inv_rev, colE_inv, e]⟩ }
    have hR : R k n c (ρ + 1) ≤ S := fun r hr => ⟨r, hr, 0, by rw [colE_zero, mul_one]⟩
    have : RFJ k n c ρ ≤ S := by
      refine sup_le (sup_le (le_trans le_sup_left hR) fun g hg => ?_) hR
      obtain ⟨u, hu, β, rfl⟩ := exists_of_mem_N hρ hg
      exact ⟨u, Subgroup.mem_sup_right hu, β, rfl⟩
    exact this hg
  · rintro ⟨r, hr, β, rfl⟩
    exact mul_mem (Subgroup.mem_sup_right hr)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Radical.colE_mem β (Nat.lt_succ_self ρ))))

end GlobalTheory.RootEx.FourierJacobiGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntegralGLOfInParahoricDatumSupportMulBlockDi
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.SuppFirstBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem toBlocks₁₁_mul_diag {A D E : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (z : Matrix (A ⊕ E) (A ⊕ D) k) (x : GL A k) (y : GL D k) :
    (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₁ = z.toBlocks₁₁ * x.val := by
  have he : (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k) =
      fromBlocks x.val 0 0 y.val := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [emb₂, leviEmb, leviTwo, two, Matrix.blockDiagonal']
  rw [he]
  conv_lhs => rw [← fromBlocks_toBlocks z]
  simp [fromBlocks_multiply]

theorem exists_GL_of_int {A : Type} [Fintype A] [DecidableEq A] (M : Matrix A A k)
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hd : valuation k M.det = 1) :
    ∃ g : GL A 𝒪[k], (GeneralLinearGroup.map (n := A) (algebraMap 𝒪[k] k) g : Matrix A A k) = M := by
  let N : Matrix A A 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  have hN : (algebraMap 𝒪[k] k).mapMatrix N = M := rfl
  have hu : IsUnit N.det := by
    rw [(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one, RingHom.map_det, hN]
    exact hd
  refine ⟨((Matrix.isUnit_iff_isUnit_det N).2 hu).unit, ?_⟩
  exact hN

end GlobalTheory.SuppFirstBlock

open GlobalTheory.SuppFirstBlock in
theorem GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (z : Matrix (A ⊕ E) (A ⊕ D) k) (x : GL A k) (y : GL D k),
    InSupp z → InSupp (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)) → x ∈ KO k A := by
  intro k _ _ _ _ A D E _ _ _ _ _ _ z x y hz hw
  have hb := toBlocks₁₁_mul_diag z x y
  obtain ⟨g, hg⟩ := exists_GL_of_int z.toBlocks₁₁ (fun i j => hz.1 _ _) hz.2.1
  obtain ⟨h, hh⟩ := exists_GL_of_int (z.toBlocks₁₁ * x.val)
    (fun i j => by rw [← hb]; exact hw.1 _ _) (by rw [← hb]; exact hw.2.1)
  have key : GeneralLinearGroup.map (n := A) (algebraMap 𝒪[k] k) g * x =
      GeneralLinearGroup.map (n := A) (algebraMap 𝒪[k] k) h := by
    ext1
    rw [Units.val_mul, hg, hh]
  refine ⟨g⁻¹ * h, ?_⟩
  rw [map_mul, map_inv, ← key, inv_mul_cancel_left]
end

