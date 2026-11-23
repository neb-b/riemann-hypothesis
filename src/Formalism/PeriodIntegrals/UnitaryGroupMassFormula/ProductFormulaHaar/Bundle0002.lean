module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrBase

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.CardQuotientEqAbsNorm
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace PI.ProdFormulaE

private theorem intValuation_le_iff_mem_maxPowDividing {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) (r s : R) (hs : s ≠ 0) :
    v.intValuation r ≤ v.intValuation s ↔ r ∈ v.maxPowDividing (Ideal.span {s}) := by
  rw [v.intValuation_if_neg hs, ← Ideal.dvd_span_singleton]
  exact v.intValuation_le_pow_iff_dvd r _

private theorem exists_valuation_sub_algebraMap_le {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) {f : K}
    (hf : v.valuation K f ≤ 1) {a : R} (ha : a ≠ 0) :
    ∃ x : R, v.valuation K (f - algebraMap R K x) ≤ v.valuation K (algebraMap R K a) := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap R K c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hc0
  have hpos : 0 < v.valuation K (algebraMap R K c) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcK)
  have hbc : v.intValuation b ≤ v.intValuation c := by
    rw [map_div₀, div_le_one₀ hpos] at hf
    simpa only [HeightOneSpectrum.valuation_of_algebraMap] using hf
  have hca : c * a ≠ 0 := mul_ne_zero hc0 ha
  obtain ⟨N, hN⟩ : ∃ N : ℕ, v.maxPowDividing (Ideal.span {c * a}) = v.asIdeal ^ N := ⟨_, rfl⟩
  have hS : Ideal.span {c} ⊔ v.asIdeal ^ N ∣ v.asIdeal ^ N := Ideal.dvd_iff_le.2 le_sup_right
  obtain ⟨k, -, hk⟩ := (dvd_prime_pow v.prime N).1 hS
  rw [associated_iff_eq] at hk
  have hbk : b ∈ v.asIdeal ^ k := by
    rw [← Ideal.dvd_span_singleton]
    apply (v.intValuation_le_pow_iff_dvd b k).1
    refine hbc.trans ((v.intValuation_le_pow_iff_dvd c k).2 ?_)
    rw [← hk]
    exact Ideal.dvd_iff_le.2 le_sup_left
  rw [← hk] at hbk
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hbk
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  refine ⟨x, ?_⟩
  have hzle : v.intValuation z ≤ v.intValuation (c * a) := by
    rw [intValuation_le_iff_mem_maxPowDividing v z _ hca, hN]
    exact hz
  have hsub : algebraMap R K b / algebraMap R K c - algebraMap R K x =
      algebraMap R K z / algebraMap R K c := by
    rw [← hyz, map_add (f := _), map_mul, add_div, mul_div_assoc, div_self hcK, mul_one,
      add_sub_cancel_left]
  rw [hsub, map_div₀, div_le_iff₀ hpos]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  exact hzle.trans_eq (by rw [map_mul, mul_comm])

private theorem isOpen_setOf_valuation_le_of_ne_zero {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {r : K} (hr : r ≠ 0) :
    IsOpen {y : K | ValuativeRel.valuation K y ≤ ValuativeRel.valuation K r} := by
  have h := Valuation.isOpen_closedBall (v := ValuativeRel.valuation K)
    (r := (ValuativeRel.valuation K).restrict r) (by simpa using hr)
  simpa using h

theorem card_quotient_eq_absNorm : CardStep := by
  unfold CardStep
  intro F _ _ p K _ _ _ _ ι hι hv a ha t ht
  have hcomp : ∀ x y : F, (ValuativeRel.valuation K) (ι x) ≤ (ValuativeRel.valuation K) (ι y) ↔ p.valuation F x ≤ p.valuation F y := by
    intro x y
    rw [← hv x y]
    exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) (ι x) (ι y)).symm
  have haF : (a : F) ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha
  have htK : (t : K) ≠ 0 := by
    rw [ht]
    exact (map_ne_zero ι).2 haF
  have hdvd : ∀ u w : 𝒪[K], u ∣ w ↔ (ValuativeRel.valuation K) (w : K) ≤ (ValuativeRel.valuation K) (u : K) := fun u w =>
    (Valuation.integer.integers (ValuativeRel.valuation K)).dvd_iff_le
  have hint_r : ∀ x : 𝓞 F, ι (algebraMap (𝓞 F) F x) ∈ 𝒪[K] := by
    intro x
    rw [Valuation.mem_integer_iff]
    have h := (hcomp (algebraMap (𝓞 F) F x) 1).2 (by
      rw [map_one]
      exact p.valuation_le_one x)
    simpa using h
  let ι₀ : 𝓞 F →+* 𝒪[K] := (ι.comp (algebraMap (𝓞 F) F)).codRestrict 𝒪[K] hint_r
  let φ : 𝓞 F →+* 𝒪[K] ⧸ Ideal.span {t} := (Ideal.Quotient.mk _).comp ι₀
  have hker : RingHom.ker φ = p.maxPowDividing (Ideal.span {a}) := by
    ext x
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk (Ideal.span {t}) (ι₀ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hdvd, ht]
    show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x)) ≤ (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F a)) ↔ _
    rw [hcomp, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact intValuation_le_iff_mem_maxPowDividing p x a ha
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hU : IsOpen {y : K | (ValuativeRel.valuation K) (y - s) ≤ (ValuativeRel.valuation K) t} := by
      have hB := isOpen_setOf_valuation_le_of_ne_zero htK
      exact hB.preimage (continuous_sub_right (s : K))
    obtain ⟨f, hf⟩ := hι.exists_mem_open hU ⟨(s : K), by simp⟩
    have hf' : (ValuativeRel.valuation K) (ι f - s) ≤ (ValuativeRel.valuation K) t := hf
    have hfK : (ValuativeRel.valuation K) (ι f) ≤ 1 := by
      have h1 : (ValuativeRel.valuation K) (ι f - s) ≤ 1 := hf'.trans ((Valuation.mem_integer_iff _ _).1 t.2)
      have h2 : (ValuativeRel.valuation K) (s : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 s.2
      simpa using (ValuativeRel.valuation K).map_add_le h1 h2
    have hf1 : p.valuation F f ≤ 1 := by
      have := (hcomp f 1).1 (by simpa using hfK)
      simpa using this
    obtain ⟨x, hx⟩ := exists_valuation_sub_algebraMap_le p hf1 ha
    refine ⟨x, ?_⟩
    show Ideal.Quotient.mk _ (ι₀ x) = Ideal.Quotient.mk _ s
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, hdvd]
    have h3 : (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x) - ι f) ≤ (ValuativeRel.valuation K) t := by
      rw [← map_sub, ht]
      show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x - f)) ≤ (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F a))
      rw [hcomp, ← neg_sub, Valuation.map_neg]
      exact hx
    have h4 : ι (algebraMap (𝓞 F) F x) - (s : K) =
        (ι (algebraMap (𝓞 F) F x) - ι f) + (ι f - s) := by ring
    show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x) - (s : K)) ≤ (ValuativeRel.valuation K) t
    rw [h4]
    exact (ValuativeRel.valuation K).map_add_le h3 hf'
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv.symm

end PI.ProdFormulaE
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarScale
section
noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise

namespace PI.ProdFormulaE.HaarBox

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_ball_of_isCompact {C : Set K} (hC : IsCompact C) :
    ∃ y : K, y ≠ 0 ∧ C ⊆ {x | valuation K x ≤ valuation K y} := by
  classical
  have hopen : ∀ y : K, y ≠ 0 → IsOpen {x : K | valuation K x ≤ valuation K y} := by
    intro y hy
    have h := isOpen_box (Basis.singleton Unit K) (fun _ => valuation K y)
      (fun _ => (Valuation.ne_zero_iff _).mpr hy)
    convert h using 1
    ext x
    simp [box, Basis.singleton_repr]
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun y : {y : K // y ≠ 0} => {x : K | valuation K x ≤ valuation K y.1})
    (fun y => hopen y.1 y.2) (by
      intro x _
      by_cases hx : x = 0
      · refine Set.mem_iUnion.mpr ⟨⟨1, one_ne_zero⟩, ?_⟩
        simp [hx]
      · exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, show valuation K x ≤ valuation K x from le_rfl⟩)
  rcases t.eq_empty_or_nonempty with h0 | hne
  · refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    have h1 := ht hx
    simp [h0] at h1
  · obtain ⟨y, hy, hmax⟩ := t.exists_max_image (fun y => valuation K y.1) hne
    refine ⟨y.1, y.2, fun x hx => ?_⟩
    have hx' := ht hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨y', hy', hxy'⟩ := hx'
    have hxy'' : valuation K x ≤ valuation K y'.1 := hxy'
    exact le_trans hxy'' (hmax y' hy')

variable [MeasurableSpace E] [BorelSpace E]

theorem scale_box (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (i : ι) (a : K)
    (ha : a ≠ 0) :
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' box b 1) =
      (distribHaarChar K (Units.mk0 a ha) : ℝ≥0∞) * μ (box b 1) := by
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup K E
  haveI := locallyCompact b
  haveI := secondCountableE b
  haveI := secondCountable K
  obtain ⟨c, hc⟩ : ∃ c : E → K, c = fun x => b.repr x i := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Set E, P = {x | ∀ j, j ≠ i → valuation K (b.repr x j) ≤ 1} :=
    ⟨_, rfl⟩
  have hcc : Continuous c := by rw [hc]; exact continuous_coord b i
  have hcm : Measurable c := hcc.measurable
  have hPo : IsOpen P := by
    have h : P = ⋂ j ∈ (Finset.univ.filter (· ≠ i)),
        (fun x : E => b.repr x j) ⁻¹' {z : K | valuation K z ≤ 1} := by
      rw [hP]; ext x; simp
    rw [h]
    exact isOpen_biInter_finset
      (fun j _ => (isOpen_ball 1 one_ne_zero).preimage (continuous_coord b j))
  let ν : Measure K := (μ.restrict P).map c
  have hνA : ∀ A : Set K, MeasurableSet A → ν A = μ (P ∩ c ⁻¹' A) := by
    intro A hA
    show ((μ.restrict P).map c) A = _
    rw [Measure.map_apply hcm hA, Measure.restrict_apply (hcm hA), Set.inter_comm]
  have hrepr_add : ∀ (t : K) (x : E) (j : ι),
      b.repr (t • b i + x) j = (if i = j then t else 0) + b.repr x j := by
    intro t x j
    rw [map_add (f := _), map_smul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun t => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add t) hA, hνA _ hA,
      hνA _ (measurable_const_add t hA)]
    have hset : P ∩ c ⁻¹' ((fun x => t + x) ⁻¹' A) =
        (fun x : E => t • b i + x) ⁻¹' (P ∩ c ⁻¹' A) := by
      ext x
      rw [hP, hc]
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hrepr_add]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun j hj => by rw [if_neg (Ne.symm hj), zero_add]; exact h1 j hj, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun j hj => ?_, h2⟩
        have := h1 j hj
        rwa [if_neg (Ne.symm hj), zero_add] at this
    rw [hset, measure_preimage_add]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨y, hy0, hCy⟩ := exists_ball_of_isCompact hC
    have hyv : valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
    have hB : IsOpen {x : K | valuation K x ≤ valuation K y} := isOpen_ball _ hyv
    calc ν C ≤ ν {x | valuation K x ≤ valuation K y} := measure_mono hCy
      _ = μ (P ∩ c ⁻¹' {x | valuation K x ≤ valuation K y}) := hνA _ hB.measurableSet
      _ ≤ μ (box b (Function.update 1 i (valuation K y))) := by
          apply measure_mono
          rintro x ⟨hx1, hx2⟩ j
          by_cases hj : j = i
          · subst hj
            rw [Function.update_self]
            rw [Set.mem_preimage, hc] at hx2
            exact hx2
          · rw [Function.update_of_ne hj]
            rw [hP] at hx1
            exact hx1 j hj
      _ < ⊤ := (isCompact_box b _).measure_lt_top
  haveI : IsOpenPosMeasure ν := by
    refine ⟨fun U hU hne => ?_⟩
    obtain ⟨u, hu⟩ := hne
    rw [hνA U hU.measurableSet]
    have hO : IsOpen (P ∩ c ⁻¹' U) := hPo.inter (hU.preimage hcc)
    refine hO.measure_ne_zero μ ⟨u • b i, ?_, ?_⟩
    · rw [hP]
      intro j hj
      rw [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
        if_neg (Ne.symm hj), smul_zero, map_zero]
      exact zero_le'
    · rw [Set.mem_preimage, hc]
      simpa using hu
  haveI : ν.IsAddHaarMeasure := { }
  let g : Kˣ := Units.mk0 a ha
  have hOo : IsOpen {x : K | valuation K x ≤ 1} := isOpen_ball 1 one_ne_zero
  have hgO : IsOpen (g • {x : K | valuation K x ≤ 1}) := hOo.smul g
  have hscale : ν (g • {x : K | valuation K x ≤ 1}) =
      (distribHaarChar K g : ℝ≥0∞) * ν {x | valuation K x ≤ 1} := by
    have h1 : (DomMulAct.mk g • ν) {x : K | valuation K x ≤ 1} =
        ν (g • {x : K | valuation K x ≤ 1}) := by
      simp [domSMul_apply]
    rw [← h1, measure_isAddHaarMeasure_eq_smul_of_isOpen _ ν hOo,
      addHaarScalarFactor_smul_eq_distribHaarChar, ENNReal.smul_def, smul_eq_mul]
  have hrepr : ∀ (d : ι → K) (x : E) (j : ι),
      b.repr (Matrix.toLin b b (Matrix.diagonal d) x) j = d j * b.repr x j := by
    intro d x j
    rw [Matrix.repr_toLin, Matrix.mulVec_diagonal]
  have hR : box b 1 = P ∩ c ⁻¹' {x : K | valuation K x ≤ 1} := by
    ext x
    rw [hP, hc]
    constructor
    · intro h
      exact ⟨fun j _ => h j, h i⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; exact h2
      · exact h1 j hj
  have hL : (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a))) '' box b 1 =
      P ∩ c ⁻¹' (g • {x : K | valuation K x ≤ 1}) := by
    ext y
    rw [hP, hc]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun j hj => ?_, ?_⟩
      · show valuation K (b.repr _ j) ≤ 1
        rw [hrepr, Function.update_of_ne hj, Pi.one_apply, one_mul]
        exact hx j
      · show b.repr _ i ∈ g • {x : K | valuation K x ≤ 1}
        rw [hrepr, Function.update_self]
        exact Set.mem_smul_set.2 ⟨b.repr x i, hx i, rfl⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨z, hz, hzy⟩ := Set.mem_smul_set.1 h2
      have hzy' : a * z = b.repr y i := hzy
      let T' := Matrix.toLin b b (Matrix.diagonal (Function.update (1 : ι → K) i a⁻¹))
      refine ⟨T' y, fun j => ?_, ?_⟩
      · show valuation K (b.repr (T' y) j) ≤ 1
        rw [hrepr]
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, ← hzy', ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
          exact hz
        · rw [Function.update_of_ne hj, Pi.one_apply, one_mul]
          exact h1 j hj
      · show Matrix.toLin b b _ (Matrix.toLin b b _ y) = y
        rw [← LinearMap.comp_apply, ← Matrix.toLin_mul, Matrix.diagonal_mul_diagonal]
        have hdd : (fun k => Function.update (1 : ι → K) i a k * Function.update (1 : ι → K) i a⁻¹ k) =
            (1 : ι → K) := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [ha]
          · simp [Function.update_of_ne hk]
        rw [hdd, Pi.one_def, Matrix.diagonal_one, Matrix.toLin_one, LinearMap.id_apply]
  rw [hL, hR, ← hνA _ hgO.measurableSet, ← hνA _ hOo.measurableSet, hscale]

end PI.ProdFormulaE.HaarBox
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarTransv
section
noncomputable section

open ValuativeRel Module Matrix

namespace PI.ProdFormulaE.HaarBox

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem repr_toLin (b : Basis ι K E) (A : Matrix ι ι K) (x : E) :
    b.repr (Matrix.toLin b b A x) = A *ᵥ b.repr x := by
  have h := LinearMap.toMatrix_mulVec_repr b b (Matrix.toLin b b A) x
  rw [LinearMap.toMatrix_toLin] at h
  exact h.symm

theorem transvection_mulVec (t : Matrix.TransvectionStruct ι K) (v : ι → K) (k : ι) :
    (t.toMatrix *ᵥ v) k = v k + if k = t.i then t.c * v t.j else 0 := by
  simp only [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
    Matrix.one_mulVec, Pi.add_apply, add_right_inj]
  by_cases hk : k = t.i
  · rw [if_pos hk, hk]
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, ite_mul]
  · rw [if_neg hk]
    simp [Matrix.mulVec, dotProduct, Ne.symm hk]

def tγ (t : Matrix.TransvectionStruct ι K) : ι → ValueGroupWithZero K :=
  Function.update 1 t.i (max (valuation K t.c) 1)

theorem tγ_inv (t : Matrix.TransvectionStruct ι K) : tγ t.inv = tγ t := by
  simp [tγ, Matrix.TransvectionStruct.inv, Valuation.map_neg]

private theorem tGamma_apply_of_ne (t : Matrix.TransvectionStruct ι K) {k : ι}
    (hk : k ≠ t.i) : tγ t k = 1 := by
  simp [tγ, hk]

private theorem tGamma_apply_self (t : Matrix.TransvectionStruct ι K) :
    tγ t t.i = max (valuation K t.c) 1 := by
  simp [tγ]

theorem toLin_mem_box (b : Basis ι K E) (t : Matrix.TransvectionStruct ι K) (x : E)
    (hx : x ∈ box b (tγ t)) : Matrix.toLin b b t.toMatrix x ∈ box b (tγ t) := by
  change ∀ k, valuation K (b.repr x k) ≤ tγ t k at hx
  change ∀ k, valuation K (b.repr (Matrix.toLin b b t.toMatrix x) k) ≤ tγ t k
  intro k
  have e : b.repr (Matrix.toLin b b t.toMatrix x) k
      = b.repr x k + if k = t.i then t.c * b.repr x t.j else 0 := by
    rw [congrFun (repr_toLin b t.toMatrix x) k, transvection_mulVec]
  rw [e]
  by_cases hk : k = t.i
  · rw [if_pos hk]
    have hj : valuation K (b.repr x t.j) ≤ 1 := by
      have h := hx t.j
      rwa [tGamma_apply_of_ne t t.hij.symm] at h
    have hR : tγ t k = max (valuation K t.c) 1 := by
      rw [hk]; exact tGamma_apply_self t
    have hxi : valuation K (b.repr x k) ≤ max (valuation K t.c) 1 := by
      rw [← hR]; exact hx k
    rw [hR]
    refine (Valuation.map_add _ _ _).trans (max_le hxi ?_)
    rw [Valuation.map_mul]
    calc valuation K t.c * valuation K (b.repr x t.j) ≤ valuation K t.c * 1 := by
          first
          | exact mul_le_mul_left' hj _
          | gcongr
      _ = valuation K t.c := mul_one _
      _ ≤ max (valuation K t.c) 1 := le_max_left _ _
  · rw [if_neg hk, add_zero]
    exact hx k

theorem transvection_box (b : Basis ι K E) (t : Matrix.TransvectionStruct ι K) :
    ∃ γ : ι → ValueGroupWithZero K, (∀ i, γ i ≠ 0) ∧
      Matrix.toLin b b t.toMatrix '' box b γ = box b γ := by
  refine ⟨tγ t, ?_, ?_⟩
  · intro i
    have h1 : (1 : ValueGroupWithZero K) ≤ tγ t i := by
      by_cases hi : i = t.i
      · rw [hi, tGamma_apply_self]
        exact le_max_right _ _
      · rw [tGamma_apply_of_ne t hi]
    exact (lt_of_lt_of_le zero_lt_one h1).ne'
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact toLin_mem_box b t x hx
    · intro y hy
      refine ⟨Matrix.toLin b b t.inv.toMatrix y, ?_, ?_⟩
      · have h := toLin_mem_box b t.inv y (by rwa [tγ_inv])
        rwa [tγ_inv] at h
      · show ((Matrix.toLin b b t.toMatrix).comp (Matrix.toLin b b t.inv.toMatrix)) y = y
        rw [← Matrix.toLin_mul, Matrix.TransvectionStruct.mul_inv, Matrix.toLin_one,
          LinearMap.id_apply]

end PI.ProdFormulaE.HaarBox

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
section
noncomputable section

open IsDedekindDomain NumberField TensorProduct

namespace PI.ProdFormulaE.Tr

theorem trace_one_tmul {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] [CommRing A] [Algebra R A] (s : S) :
    Algebra.trace A (A ⊗[R] S) (1 ⊗ₜ s) = algebraMap R A (Algebra.trace R S s) := by
  have h : Algebra.lmul A (A ⊗[R] S) (1 ⊗ₜ s) = (Algebra.lmul R S s).baseChange A := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a t
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

theorem trace_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → Type*) [∀ i, CommRing (K i)] [∀ i, Algebra R (K i)] [∀ i, Module.Free R (K i)]
    [∀ i, Module.Finite R (K i)] (z : ∀ i, K i) :
    Algebra.trace R (∀ i, K i) z = ∑ i, Algebra.trace R (K i) (z i) := by
  classical
  let bs := fun i => Module.Free.chooseBasis R (K i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis bs), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (bs i), Matrix.trace]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr, bs]

theorem trSum_of (hI : TrInj) (hS : TrSurj) : TrSum := by
  classical
  intro F _ _ ℓ _ ι _ D hD y
  let e : ℚ_[ℓ] ⊗[ℚ] F ≃ₐ[ℚ_[ℓ]] (∀ i, D.K i) :=
    AlgEquiv.ofBijective D.Φ ⟨hI F ℓ ι D hD, hS F ℓ ι D hD⟩
  have h1 : e (1 ⊗ₜ y) = fun i => D.ιF i y := by
    funext i
    simp [e, LocFam.Φ, Algebra.TensorProduct.lift_tmul]
  rw [← trace_one_tmul, ← Algebra.trace_eq_of_algEquiv e, h1, trace_pi]

end PI.ProdFormulaE.Tr
end
end

