module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

namespace MassFinite

theorem exists_frame {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j := by
  classical
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 fun j => star (U i j)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i k
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    simp [v, PiLp.inner_apply, Matrix.star_apply, mul_comm]
  refine ⟨OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge,
    fun i z => ?_⟩
  rw [OrthonormalBasis.coe_mk]
  simp [v, PiLp.inner_apply, mul_comm]

theorem eval_pullback {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (P : MvPolynomial (Fin d) ℂ)
    (x : Fin n → ℂ) : eval x (ComplexSets.pullback A P) = eval (A *ᵥ x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [ComplexSets.pullback]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [ComplexSets.pullback, ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem dim_sup_lt {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (f : MvPolynomial (Fin n) ℂ) (hf : f ∉ J) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) < d := by
  have := hJ
  have hr : Ideal.Quotient.mk J f ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have h := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.factor (le_sup_left : J ≤ J ⊔ Ideal.span {f}))
    (Ideal.Quotient.factor_surjective _) hr
    (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  rw [hd] at h
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    have he : e ≠ ⊤ := fun he => by simp [he] at h'
    exact_mod_cast (ENat.add_one_le_iff he).mp h'

theorem ball_lt_top {ι : Type*} [Fintype ι] (R : ℝ) :
    μH[((2 * Fintype.card ι : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R) < ⊤ := by
  have hfr : Module.finrank ℝ (ι × Fin 2 → ℝ) = Module.finrank ℝ (EuclideanSpace ℂ ι) := by
    rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι),
      Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, mul_comm]
  let e := (LinearEquiv.ofFinrankEq _ _ hfr).toContinuousLinearEquiv
  have hcard : ((2 * Fintype.card ι : ℕ) : ℝ) = ((Fintype.card (ι × Fin 2) : ℕ) : ℝ) := by
    simp [mul_comm]
  have hsub : Metric.ball (0 : EuclideanSpace ℂ ι) R ⊆ e '' (e.symm '' Metric.ball 0 R) := by
    rw [Set.image_image]
    simp
  have hb : Bornology.IsBounded (e.symm '' Metric.ball (0 : EuclideanSpace ℂ ι) R) :=
    e.symm.lipschitzWith.isBounded_image Metric.isBounded_ball
  rw [hcard]
  calc μH[((Fintype.card (ι × Fin 2) : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R)
      ≤ μH[((Fintype.card (ι × Fin 2) : ℕ) : ℝ)] (e '' (e.symm '' Metric.ball 0 R)) := measure_mono hsub
    _ ≤ _ := e.lipschitzWith.hausdorffMeasure_image_le (by positivity) _
    _ < ⊤ := by
      refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by exact Nat.cast_nonneg (Fintype.card (ι × Fin 2))) ENNReal.coe_ne_top) ?_
      rw [hausdorffMeasure_pi_real]
      exact hb.measure_lt_top

theorem count_le {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hb : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j)
    (I : Finset (Fin n)) (hI : I.card = d) (S : Set (EuclideanSpace ℂ (Fin n)))
    (hS : S ⊆ zeroSetEuc J) (N : ℕ)
    (hN : ∀ y, (ComplexSets.fibre J (U.submatrix (I.orderEmbOfFin hI) id) y).Finite ∧
      (ComplexSets.fibre J (U.submatrix (I.orderEmbOfFin hI) id) y).ncard ≤ N)
    (x : I → ℂ) : frameFibreCount b I S x ≤ N := by
  set e := I.orderIsoOfFin hI
  set A := U.submatrix (I.orderEmbOfFin hI) id
  let y : Fin d → ℂ := fun k => x (e k)
  have hsub : WithLp.ofLp '' {z ∈ S | frameProj b I z = x} ⊆ ComplexSets.fibre J A y := by
    rintro _ ⟨z, ⟨hzS, hzx⟩, rfl⟩
    refine ⟨fun q hq => hS hzS q hq, ?_⟩
    funext k
    have h1 := congrFun hzx (e k)
    simp only [frameProj, hb] at h1
    simp only [y, ← h1, A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id,
      Finset.coe_orderIsoOfFin_apply, e]
  have hinj : Set.InjOn (WithLp.ofLp (p := 2)) {z ∈ S | frameProj b I z = x} :=
    (WithLp.ofLp_injective 2).injOn
  unfold frameFibreCount
  rw [← hinj.encard_image, ← (hN y).1.subset hsub |>.cast_ncard_eq]
  have h2 := Set.ncard_le_ncard hsub (hN y).1
  have h3 := (hN y).2
  exact_mod_cast h2.trans h3

theorem good_localGraph {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hb : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j)
    (I₀ : Finset (Fin n)) (hI : I₀.card = d) (P : MvPolynomial (Fin d) ℂ)
    (hP : ∀ y : Fin d → ℂ, eval y P ≠ 0 →
      ∀ x ∈ ComplexSets.fibre J (U.submatrix (I₀.orderEmbOfFin hI) id) y,
        ∃ (U' : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ)) (g : (Fin d → ℂ) → (Fin n → ℂ)),
          IsOpen U' ∧ y ∈ U' ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ g U' ∧ g y = x ∧
          (∀ w ∈ U', U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ g w = w) ∧
          ComplexSets.zeroSet J ∩ V = g '' U') :
    ∀ z ∈ zeroSetEuc J ∩ {z | eval (U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ WithLp.ofLp z) P ≠ 0},
      ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
        (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
          DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
          (zeroSetEuc J ∩ {z | eval (U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ WithLp.ofLp z) P ≠ 0}) ∩ V =
            g '' Ω := by
  set A := U.submatrix (I₀.orderEmbOfFin hI) id
  set e := I₀.orderIsoOfFin hI
  rintro z ⟨hzZ, hzP⟩
  obtain ⟨U', V, g, hU', -, hV, hzV, hg, -, hAg, hZV⟩ := hP _ hzP (WithLp.ofLp z) ⟨hzZ, rfl⟩
  let σ : (I₀ → ℂ) →L[ℂ] (Fin d → ℂ) := ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e k)
  have hσ : ∀ w k, σ w k = w (e k) := fun _ _ => rfl
  let L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm
  have hL : ∀ v, L v = WithLp.toLp 2 v := fun _ => rfl
  have hcP : Continuous fun w : Fin d → ℂ => eval w P := MvPolynomial.continuous_eval P
  have hcA : Continuous fun z' : EuclideanSpace ℂ (Fin n) => A *ᵥ WithLp.ofLp z' :=
    (Continuous.matrix_mulVec continuous_const continuous_id).comp (PiLp.continuous_ofLp 2 _)
  refine ⟨σ ⁻¹' (U' ∩ {w | eval w P ≠ 0}),
    {z' | WithLp.ofLp z' ∈ V ∧ eval (A *ᵥ WithLp.ofLp z') P ≠ 0}, fun w => L (g (σ w)),
    (hU'.inter (isOpen_ne_fun hcP continuous_const)).preimage σ.continuous,
    (hV.preimage (PiLp.continuous_ofLp 2 _)).inter (isOpen_ne_fun (hcP.comp hcA) continuous_const),
    ⟨hzV, hzP⟩, L.differentiable.comp_differentiableOn (hg.comp σ.differentiable.differentiableOn
      fun w hw => hw.1), fun w hw => ?_, ?_⟩
  · funext i
    have h1 := congrFun (hAg _ hw.1) (e.symm i)
    simp only [A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, hσ,
      ← Finset.coe_orderIsoOfFin_apply, e, OrderIso.apply_symm_apply] at h1
    simp only [frameProj, hb, hL]
    simpa using h1
  · ext z'
    constructor
    · rintro ⟨⟨hz'Z, -⟩, hz'V, hz'P⟩
      have hmem : WithLp.ofLp z' ∈ ComplexSets.zeroSet J ∩ V := ⟨hz'Z, hz'V⟩
      rw [hZV] at hmem
      obtain ⟨w0, hw0, hgw0⟩ := hmem
      have hσw : σ (fun i => w0 (e.symm i)) = w0 := by
        funext k
        simp [hσ]
      refine ⟨fun i => w0 (e.symm i), ⟨by rw [hσw]; exact hw0, ?_⟩, ?_⟩
      · rw [Set.mem_ofPred_eq, hσw, ← hAg w0 hw0, hgw0]
        exact hz'P
      · simp only [hσw, hL, hgw0]
    · rintro ⟨w, ⟨hwU, hwP⟩, rfl⟩
      have hmem : g (σ w) ∈ ComplexSets.zeroSet J ∩ V := hZV ▸ ⟨σ w, hwU, rfl⟩
      have hA : A *ᵥ WithLp.ofLp (L (g (σ w))) = σ w := hAg _ hwU
      refine ⟨⟨fun q hq => hmem.1 q hq, ?_⟩, hmem.2, ?_⟩
      · rw [Set.mem_ofPred_eq, hA]
        exact hwP
      · rw [hA]
        exact hwP

end MassFinite

theorem MassFinite.proof (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hF : ComplexSets.FibreBound.Statement) (hD : ComplexSets.DiscriminantCover.Statement)
    (hN : NullSmaller.Statement) (hL : LocalGraphMass.Statement) : MassFinite.Statement := by
  intro n d J hJ hd R
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  obtain ⟨U, hU, hUfin⟩ := (hG n d J hJ hd).2.2.2 1 (fun _ => 1)
  obtain ⟨b, hb⟩ := MassFinite.exists_frame U hU
  have hfin : ∀ (I : Finset (Fin n)) (hI : I.card = d),
      ComplexSets.IsFiniteProjection J (U.submatrix (I.orderEmbOfFin hI) id) := fun I hI => by
    simpa using hUfin 0 (I.orderEmbOfFin hI).toEmbedding
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hdn)
  set A := U.submatrix (I₀.orderEmbOfFin hI₀) id
  obtain ⟨P, hP0, hP⟩ := hD n d J A hJ hd (hfin I₀ hI₀)
  set G := zeroSetEuc J ∩ {z | eval (A *ᵥ WithLp.ofLp z) P ≠ 0}
  have hPJ : ComplexSets.pullback A P ∉ J := fun hmem => hP0 <| (hfin I₀ hI₀).injective <| by
    rw [map_zero, ComplexSets.projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hbad : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) = 0 :=
    hN n d _ (MassFinite.dim_sup_lt J hJ hd _ hPJ)
  have hsub : zeroSetEuc J ∩ Metric.ball 0 R ⊆
      zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ Metric.ball 0 R := by
    rintro z ⟨hz, hzR⟩
    by_cases hzP : eval (A *ᵥ WithLp.ofLp z) P = 0
    · left
      intro q hq
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have hzj : eval (fun i => z i) j = 0 := hz j hj
      have hpb : eval (fun i => z i) (ComplexSets.pullback A P) = 0 := by
        rw [MassFinite.eval_pullback]
        exact hzP
      simp [hzj, hpb]
    · exact Or.inr ⟨⟨hz, hzP⟩, hzR⟩
  have hgood := hL n d b I₀ G hI₀ (MassFinite.good_localGraph J U b hb I₀ hI₀ P
    (fun y hy x hx => ((hP y hy).2.2 x hx))) R
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball 0 R)
      ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪
          G ∩ Metric.ball 0 R) := measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) +
          μH[((2 * d : ℕ) : ℝ)] (G ∩ Metric.ball 0 R) := measure_union_le _ _
    _ < ⊤ := by
      rw [hbad, zero_add]
      refine lt_of_le_of_lt hgood (ENNReal.sum_lt_top.mpr fun I hI => ENNReal.mul_lt_top ?_ ?_)
      · have hIc := (Finset.mem_powersetCard.mp hI).2
        refine lt_of_le_of_lt (iSup_le fun x => MassFinite.count_le J U b hb I hIc G
          (fun z hz => hz.1) (ComplexSets.projDegree J (U.submatrix (I.orderEmbOfFin hIc) id))
          (fun y => ?_) x) ENNReal.coe_lt_top
        have h := hF n d J _ hJ hd (hfin I hIc) y
        exact ⟨h.2.1, h.2.2⟩
      · have h := MassFinite.ball_lt_top (ι := I) R
        rwa [Fintype.card_coe, (Finset.mem_powersetCard.mp hI).2] at h

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalLocalDepthTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

theorem NormalLocalDepthTwo.mem_span_of_maximalIdeal_mul_le {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (hm : ¬ (maximalIdeal B).IsPrincipal)
    {x y : B} (hx : x ≠ 0) (hy : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b) : ∃ c, y = x * c := by
  let K := FractionRing B
  by_cases h : ∀ a ∈ maximalIdeal B, ∀ b, a * y = x * b → b ∈ maximalIdeal B
  ·
    set u : K := algebraMap B K y / algebraMap B K x with hu
    have hxK : algebraMap B K x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hx
    let N : Submodule B K := Submodule.map (Algebra.linearMap B K) (maximalIdeal B)
    have hmbot : maximalIdeal B ≠ ⊥ := fun h0 => hm (h0 ▸ ⟨⟨0, by simp⟩⟩)
    have hN : N ≠ ⊥ := by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
      intro hN0
      have : algebraMap B K a ∈ N := Submodule.mem_map_of_mem ha
      rw [hN0, Submodule.mem_bot] at this
      exact ha0 ((map_eq_zero_iff _ (IsFractionRing.injective B K)).mp this)
    have hNfg : N.FG := (IsNoetherian.noetherian (maximalIdeal B)).map _
    have hstab : ∀ n ∈ N, u • n ∈ N := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := hy a ha
      refine ⟨b, h a ha b hb, ?_⟩
      change algebraMap B K b = u * algebraMap B K a
      rw [hu, div_mul_eq_mul_div, eq_div_iff hxK, ← map_mul, ← map_mul]
      congr 1
      linear_combination -hb
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (isIntegral_of_smul_mem_submodule N hN hNfg u hstab)
    refine ⟨c, IsFractionRing.injective B K ?_⟩
    rw [map_mul, hc, hu]
    exact (mul_div_cancel₀ _ hxK).symm
  ·
    push Not at h
    obtain ⟨a, ha, b, hab, hb⟩ := h
    have hbu : IsUnit b := by
      by_contra hb'
      exact hb ((mem_maximalIdeal b).mpr hb')
    by_cases hy0 : y = 0
    · exact ⟨0, by simp [hy0]⟩
    exfalso
    apply hm
    refine ⟨⟨a, le_antisymm ?_ ?_⟩⟩
    · intro a' ha'
      obtain ⟨b', hb'⟩ := hy a' ha'
      have hab' : a' * b = a * b' := mul_right_cancel₀ hy0 (by linear_combination b * hb' - b' * hab)
      refine Submodule.mem_span_singleton.mpr ⟨b' * ↑hbu.unit⁻¹, ?_⟩
      rw [smul_eq_mul, show b' * ↑hbu.unit⁻¹ * a = (a * b') * ↑hbu.unit⁻¹ by ring, ← hab', mul_assoc,
        hbu.mul_val_inv, mul_one]
    · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact ha

theorem NormalLocalDepthTwo.proof : NormalLocalDepthTwo.Statement := by
  intro B _ _ _ _ _
  by_cases hfield : IsField B
  · refine ⟨[], by simp, IsWeaklyRegular.nil B B, ?_⟩
    rw [ringKrullDim_eq_zero_of_isField hfield]
    simp
  have hmbot : maximalIdeal B ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp hfield
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
  have hxreg : IsSMulRegular B x := fun a b h => mul_left_cancel₀ hx0 h
  by_cases hp : (maximalIdeal B).IsPrincipal
  ·
    have : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hfield).out 5 1).mp hp
    refine ⟨[x], by simpa using hxm,
      (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hxreg, IsWeaklyRegular.nil _ _⟩, ?_⟩
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp

  have hreg : ∃ y ∈ maximalIdeal B, IsSMulRegular (QuotSMulTop x B) y := by
    by_contra hcon
    push Not at hcon
    have hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆
        ⋃ p ∈ associatedPrimes B (QuotSMulTop x B), (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      intro y hy
      have h1 := hcon y hy
      rw [isSMulRegular_iff_right_eq_zero_of_smul] at h1
      push Not at h1
      obtain ⟨z, hz, hz0⟩ := h1
      exact ⟨z, hz0, hz⟩
    have hmem := (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
      (associatedPrimes.finite B (QuotSMulTop x B)) ⊥ ⊥
      (fun I hI _ _ => IsAssociatedPrime.isPrime hI) bot_ne_top bot_ne_top).mp hsub
    obtain ⟨-, z, hz⟩ := isAssociatedPrime_iff.mp hmem
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hyx : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b := by
      intro a ha
      rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at ha
      obtain ⟨b, -, hb⟩ := ha
      exact ⟨b, by simpa [smul_eq_mul] using hb.symm⟩
    obtain ⟨c, hc⟩ := NormalLocalDepthTwo.mem_span_of_maximalIdeal_mul_le hp hx0 hyx
    have h1 : (1 : B) ∈ maximalIdeal B := by
      rw [hz, Submodule.mem_colon_singleton, one_smul, Submodule.mem_bot,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨c, trivial, by rw [hc, smul_eq_mul]⟩
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨y, hym, hy⟩ := hreg
  refine ⟨[x, y], ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · exact (isWeaklyRegular_cons_iff _ _ _).mpr
      ⟨hxreg, (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hy, IsWeaklyRegular.nil _ _⟩⟩
  · exact (min_le_left _ _).trans (by simp)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParametrisationSheetsConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter MeasureTheory

theorem exists_clm_ne_zero_of_countable {σ : Type} [Fintype σ] {T : Set (σ → ℂ)} (hT : T.Countable)
    (h0 : (0 : σ → ℂ) ∉ T) : ∃ ℓ : (σ → ℂ) →L[ℂ] ℂ, ∀ u ∈ T, ℓ u ≠ 0 := by
  classical
  let φ : (σ → ℂ) → ((σ → ℂ) →ₗ[ℝ] ℂ) := fun u =>
    { toFun := fun v => ∑ i, v i * u i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum, mul_assoc] }
  have hφ : ∀ u v, φ u v = ∑ i, v i * u i := fun _ _ => rfl
  have hker : ∀ u ∈ T, volume (LinearMap.ker (φ u) : Set (σ → ℂ)) = 0 := by
    intro u hu
    refine Measure.addHaar_submodule volume _ fun htop => ?_
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact h0 (by rwa [show u = 0 from funext h] at hu)
    have hm : Pi.single i 1 ∈ LinearMap.ker (φ u) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hφ] at hm
    simp [Pi.single_apply] at hm
    exact hi hm
  have hnull : volume (⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ))) = 0 :=
    (measure_biUnion_null_iff hT).2 hker
  obtain ⟨v, hv⟩ : ∃ v, v ∉ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := by
    by_contra h
    push Not at h
    have hu : (Set.univ : Set (σ → ℂ)) ⊆ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := fun x _ => h x
    have hpos := isOpen_univ.measure_pos (volume : Measure (σ → ℂ)) Set.univ_nonempty
    exact hpos.ne' (measure_mono_null hu hnull)
  refine ⟨∑ i, v i • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i, fun u hu => ?_⟩
  have hvu : φ u v ≠ 0 := fun h => hv (Set.mem_biUnion hu (LinearMap.mem_ker.2 h))
  rw [hφ] at hvu
  simpa [ContinuousLinearMap.sum_apply] using hvu

theorem ParametrisationSheetsConnected.proof (h₁ : SheetPieceProductAnalytic.Statement)
    (h₂ : SheetPieceReachesCentre.Statement) : ParametrisationSheetsConnected.Statement := by
  classical
  intro σ _ X w B d A D δ N hP hirr
  obtain ⟨hB, hwXB, hD, -, hmaps, -, -, -, -, hcard, -, hdense⟩ := id hP
  set S := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} with hS
  by_contra hnc
  rw [IsPreconnected] at hnc
  push Not at hnc
  obtain ⟨u, v, hu, hv, hSuv, hSu, hSv, hdisj⟩ := hnc
  have hdisj' : S ∩ (v ∩ u) = ∅ := by rwa [Set.inter_comm v u]
  have hSvu : S ⊆ v ∪ u := by rwa [Set.union_comm]
  have hwu := h₂ σ X w B d A D δ N u v hP hu hv hSuv hdisj hSu
  have hwv := h₂ σ X w B d A D δ N v u hP hv hu hSvu hdisj' hSv
  obtain ⟨p, hpS, hpw⟩ := mem_closure_iff_seq_limit.1 hwu
  obtain ⟨q, hqS, hqw⟩ := mem_closure_iff_seq_limit.1 hwv

  have hfin : ∀ (U' : Set (σ → ℂ)), ∀ x ∈ S, {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A x}.Finite :=
    fun U' x hx => (Set.finite_of_encard_eq_coe (hcard (A x) (hmaps hx.1) hx.2)).subset
      fun x' hx' => ⟨hx'.1, hx'.2.2⟩
  set T : Set (σ → ℂ) :=
    (⋃ n, (fun x' => p n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ v ∧ A x' = A (p n)}) ∪
      ⋃ n, (fun x' => q n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ u ∧ A x' = A (q n)} with hT
  have hTc : T.Countable :=
    (Set.countable_iUnion fun n => ((hfin v (p n) (hpS n).1).image _).countable).union
      (Set.countable_iUnion fun n => ((hfin u (q n) (hqS n).1).image _).countable)
  have hT0 : (0 : σ → ℂ) ∉ T := by
    have key : ∀ (r : σ → ℂ) (U₁ U₂ : Set (σ → ℂ)), r ∈ S ∩ U₁ → S ∩ (U₁ ∩ U₂) = ∅ →
        ∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U₂ ∧ A x' = A r}, r - x' ≠ 0 := by
      intro r U₁ U₂ hr hd x' hx' h0
      have hrx : r = x' := sub_eq_zero.1 h0
      have hx'S : x' ∈ S := ⟨hx'.1, by rw [hx'.2.2]; exact hr.1.2⟩
      exact (Set.eq_empty_iff_forall_notMem.1 hd x') ⟨hx'S, hrx ▸ hr.2, hx'.2.1⟩
    rintro (h | h) <;> obtain ⟨n, x', hx', hx0⟩ := Set.mem_iUnion.1 h
    · exact key (p n) u v (hpS n) hdisj x' hx' hx0
    · exact key (q n) v u (hqS n) hdisj' x' hx' hx0
  obtain ⟨ℓ, hℓ⟩ := exists_clm_ne_zero_of_countable hTc hT0
  obtain ⟨f, hfan, hfeq⟩ := h₁ σ X w B d A D δ N u v ℓ hP hu hv hSuv hdisj
  obtain ⟨g, hgan, hgeq⟩ := h₁ σ X w B d A D δ N v u ℓ hP hv hu hSvu hdisj'

  have hzero : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) →
      ∀ x ∈ S, x ∈ U' → F x = 0 := by
    intro U' F hF x hx hxU
    rw [hF x (hmaps hx.1) hx.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' x hx)]
    exact Finset.prod_eq_zero ((hfin U' x hx).mem_toFinset.2 ⟨hx.1, hxU, rfl⟩) (sub_self _)

  have hne : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ) (r : σ → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) → r ∈ S →
      (∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A r}, r - x' ∈ T) → F r ≠ 0 := by
    intro U' F r hF hr hrT
    rw [hF r (hmaps hr.1) hr.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' r hr)]
    refine Finset.prod_ne_zero_iff.2 fun x' hx' => ?_
    rw [← map_sub]
    exact hℓ _ (hrT x' ((hfin U' r hr).mem_toFinset.1 hx'))
  have hfq : ∀ n, f (q n) ≠ 0 := fun n => hne u f (q n) hfeq (hqS n).1
    fun x' hx' => Or.inr (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)
  have hgp : ∀ n, g (p n) ≠ 0 := fun n => hne v g (p n) hgeq (hpS n).1
    fun x' hx' => Or.inl (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)

  have hprod : ∀ z ∈ X ∩ B, f z * g z = 0 := by
    intro z hz
    have hc : ContinuousAt (fun z => f z * g z) z :=
      (hfan z (hmaps hz)).continuousAt.mul (hgan z (hmaps hz)).continuousAt
    have := mem_closure_iff_nhdsWithin_neBot.1 (hdense hz)
    have h2 : (fun z => f z * g z) =ᶠ[𝓝[S] z] fun _ => 0 :=
      eventually_nhdsWithin_of_forall fun x hx => by
        rcases hSuv hx with hxu | hxv
        · simp [hzero u f hfeq x hx hxu]
        · simp [hzero v g hgeq x hx hxv]
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' h2.symm)
  have hw : A w ∈ D := hmaps hwXB
  have hev : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0 := by
    filter_upwards [hB.mem_nhds hwXB.2] with z hzB hzX using hprod z ⟨hzX, hzB⟩
  rcases hirr.2 f g (hfan w hw) (hgan w hw) hev with hf0 | hg0
  · obtain ⟨n, hn⟩ := (hqw.eventually hf0).exists
    exact hfq n (hn (hqS n).1.1.1)
  · obtain ⟨n, hn⟩ := (hpw.eventually hg0).exists
    exact hgp n (hn (hpS n).1.1.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

