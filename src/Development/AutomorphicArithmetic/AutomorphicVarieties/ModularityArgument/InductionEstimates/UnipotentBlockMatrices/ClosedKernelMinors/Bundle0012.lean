module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.OrthCt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0005
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ContLv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PmLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.RepZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtZero
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

set_option synthInstance.maxHeartbeats 400000 in
private theorem intD {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) {E : Type} [NormedAddCommGroup E]
    {h : G1 K n → E} (hh : Continuous h) : Integrable h D.ν := by
  have := D.prob
  have h1 : IntegrableOn h (D.U : Set (G1 K n)) D.ν := hh.continuousOn.integrableOn_compact (typeFin D).1
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem D.supp] at h1

private theorem intR {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (w : L2 μ) : Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k w) D.ν :=
  intD D (D.cont.smul ((rightRegularRep (Gam K n) μ).continuous_orbit w))

private theorem fixClosed {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] : ∃ S : Submodule ℂ (L2 μ), IsClosed (S : Set (L2 μ)) ∧ ∀ w, w ∈ S ↔ D.FixedByTypeProjector μ w := by
  let T₀ : L2 μ →ₗ[ℂ] L2 μ :=
    { toFun := fun w => ∫ k, D.e k • rightRegularRep (Gam K n) μ k w ∂D.ν
      map_add' := fun a b => by
        rw [← integral_add (intR D μ a) (intR D μ b)]
        simp only [map_add (f := _), smul_add]
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        simp only [smul_comm c] }
  have hb : ∀ w, ‖T₀ w‖ ≤ (∫ k, ‖D.e k‖ ∂D.ν) * ‖w‖ := by
    intro w
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← integral_mul_const]
    congr 1
    ext k
    rw [norm_smul, UnitaryRep.norm_map]
  let T : L2 μ →L[ℂ] L2 μ := T₀.mkContinuous _ hb
  refine ⟨LinearMap.eqLocus (T : L2 μ →ₗ[ℂ] L2 μ) LinearMap.id, isClosed_eq T.continuous continuous_id, fun w => Iff.rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
private theorem fixRep {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] {v : L2 μ} {Φ : G1 K n → ℂ} (h : IsContRep μ v Φ) {C : ℝ} (hC : ∀ g, ‖Φ g‖ ≤ C)
    (hfix : D.Fix Φ) : D.FixedByTypeProjector μ v := by
  have := D.prob
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have hQ := h.ae_eq_quotFun
  have hQc := continuous_quotFun h.2.1 h.1
  set Q := quotFun Φ h.2.1 with hQd
  have hQb : ∀ x, ‖Q x‖ ≤ C := fun x => by
    obtain ⟨y, rfl⟩ := mk_surjective (Gam K n) x
    exact hC y
  refine ext_inner_left ℂ fun w => ?_
  have hw : Integrable (fun x => conj (w x)) (quotientMeasure (Gam K n) μ) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp ((Lp.memLp w).integrable one_le_two)
  have hcoef : ∀ k, ⟪w, D.e k • rightRegularRep (Gam K n) μ k v⟫_ℂ =
      ∫ x, D.e k * conj (w x) * Q (rightMul (Gam K n) k x) ∂quotientMeasure (Gam K n) μ := by
    intro k
    rw [inner_smul_right, L2.inner_def, ← integral_const_mul]
    have h2 : (fun x => v (rightMul (Gam K n) k x)) =ᵐ[quotientMeasure (Gam K n) μ]
        fun x => Q (rightMul (Gam K n) k x) :=
      (measurePreserving_rightMul μ k).quasiMeasurePreserving.ae_eq_comp hQ
    refine integral_congr_ae ?_
    filter_upwards [coeFn_rightRegularRep (Gam K n) μ k v, h2] with x h3 h4
    rw [h3, h4, RCLike.inner_apply', mul_assoc]
  have hI : Integrable (Function.uncurry fun k x => D.e k * conj (w x) * Q (rightMul (Gam K n) k x))
      (D.ν.prod (quotientMeasure (Gam K n) μ)) := by
    have h0 : Integrable D.e D.ν := intD D D.cont
    have h1 : Integrable (fun p : G1 K n × RightCosetSpace (Gam K n) => D.e p.1 * conj (w p.2))
        (D.ν.prod (quotientMeasure (Gam K n) μ)) := Integrable.mul_prod (f := D.e) (g := fun x => conj (w x)) h0 hw
    have hc : Continuous fun p : G1 K n × RightCosetSpace (Gam K n) => Q (rightMul (Gam K n) p.1 p.2) := by
      have hr : Continuous fun p : RightCosetSpace (Gam K n) × G1 K n => rightMul (Gam K n) p.2 p.1 :=
        continuous_rightMul_prod (Gam K n)
      have h3 : Continuous fun p : G1 K n × RightCosetSpace (Gam K n) => (p.2, p.1) :=
        continuous_snd.prodMk continuous_fst
      have h4 := hr.comp h3
      have h5 := hQc.comp h4
      exact h5
    have h2 := Integrable.mul_bdd (c := C) h1 hc.aestronglyMeasurable (Eventually.of_forall fun p => hQb _)
    exact h2
  rw [← integral_inner (intR D μ v)]
  simp only [hcoef]
  rw [integral_integral_swap hI, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hQ] with x hx
  rw [RCLike.inner_apply', hx]
  obtain ⟨y, rfl⟩ := mk_surjective (Gam K n) x
  simp only [rightMul_mk, hQd, quotFun_mk]
  rw [← hfix y, ← integral_const_mul]
  congr 1
  ext k
  ring

private theorem thFix {K : Type} [Field K] [NumberField K] (D : TypeDat K (2 + 2)) {F : G1 K (2 + 2) → ℂ}
    (hF : Continuous F)
    (hfin : ∀ C : Set (G1 K (2 + 2)), IsCompact C → {q : Cos K | ∃ g ∈ C, F ((q.out : G1 K (2 + 2)) * g) ≠ 0}.Finite)
    (hfix : D.Fix F) : D.Fix (th F) := by
  intro g
  have hc : IsCompact ((fun k => g * k) '' (D.U : Set (G1 K (2 + 2)))) :=
    (typeFin D).1.image (continuous_const_mul g)
  have hS := hfin _ hc
  have hs : ∀ k ∈ D.U, th F (g * k) = ∑ q ∈ hS.toFinset, F ((q.out : G1 K (2 + 2)) * g * k) := by
    intro k hk
    simp only [mul_assoc]
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    rw [Finite.coe_toFinset]
    exact ⟨g * k, ⟨k, hk, rfl⟩, hq⟩
  have h1 := hs 1 D.U.one_mem
  simp only [mul_one] at h1
  rw [h1, ← Finset.sum_congr rfl fun q _ => hfix ((q.out : G1 K (2 + 2)) * g), ← integral_finsetSum]
  · refine integral_congr_ae ?_
    filter_upwards [D.supp] with k hk
    rw [hs k hk, Finset.mul_sum]
  · intro q _
    exact intD D (D.cont.mul (hF.comp (continuous_const_mul _)))

private theorem bfFix {K : Type} [Field K] [NumberField K] (D : TypeDat K (2 + 2)) (β : ℝ → ℂ) {f : G1 K (2 + 2) → ℂ}
    (hfix : D.Fix f) : D.Fix (bf β f) := by
  intro g
  unfold bf
  rw [← hfix g, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [D.supp] with k hk
  have h1 : HP 2 2 (g * k) = HP 2 2 g := (hpSpec.2.1 k ((typeFin D).2.1 hk)).2 g
  rw [h1]
  ring

private theorem ctRep {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] {v : L2 μ} {Φ : G1 K n → ℂ} (h : IsContRep μ v Φ) (r : ℕ)
    (h0 : ∀ g, ∫ X in unipFundamentalDomain K n r, Φ (unipOne (K := _) (n := _) r X * g) ∂unipMeasure K n r = 0) :
    constantTermL2 μ r v =ᵐ[μ] 0 := by
  filter_upwards [ae_ctFun_congr μ r h.ae_eq_quotFun] with y hy
  rw [constantTermL2, hy]
  exact h0 y

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctZero :
    CtZeroC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D d d' A A'
  obtain ⟨S₀, hS₀, h₀⟩ := fixClosed D μ
  obtain ⟨S₁, hS₁, h₁⟩ := ctClosed μ 1
  obtain ⟨S₃, hS₃, h₃⟩ := ctClosed μ 3
  let S : Submodule ℂ (L2 μ) := (cuspidalL2 μ)ᗮ ⊓ (S₀ ⊓ (S₁ ⊓ S₃))
  have hS : IsClosed (S : Set (L2 μ)) :=
    (Submodule.isClosed_orthogonal _).inter (hS₀.inter (hS₁.inter hS₃))
  have hgen : Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d), Continuous β ∧ HasCompactSupport β ∧
      ∀ᵐ x : ℝ, u x = β x • v} ≤ S.comap A.J.toLinearMap := by
    rw [Submodule.span_le]
    rintro u ⟨β, v, hβ, hβc, hu⟩
    have hrep : Reps μ (A.J u) (th (bf β (A.sec v))) := A.spec β v u hβ hβc hu
    obtain ⟨hsec, hfix⟩ := (A.onto (A.sec v)).1 ⟨v, rfl⟩
    obtain ⟨hp, hband, hdec⟩ := bfFun _ β (secFun μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ _ hsec hfix) hβ hβc
    obtain ⟨hfin, hcont, hinv, hb⟩ := thBasic μ _ hp.cont hp.rat hband
    obtain ⟨-, ⟨C, hC⟩, -⟩ := hb hdec
    have hcr : IsContRep μ (A.J u) (th (bf β (A.sec v))) := ⟨hcont, hinv, hrep⟩
    refine ⟨?_, (h₀ _).2 ?_, (h₁ _).2 ?_, (h₃ _).2 ?_⟩
    · refine (Submodule.mem_orthogonal' _ _).2 fun w hw => ?_
      exact orthCt μ _ hp.cont hp.rat hband hdec hp.unip _ w hrep (hw 2 (by norm_num) (by norm_num))
    · exact fixRep D μ hcr hC (thFix D hp.cont hfin (bfFix D β hfix))
    · exact ctRep μ hcr 1 fun g => (thCt _ hp hband g).1
    · exact ctRep μ hcr 3 fun g => (thCt _ hp hband g).2.1
  intro u
  have hu : A.J u ∈ S :=
    closure_minimal (s := _) (t := A.J ⁻¹' (S : Set (L2 μ))) hgen (hS.preimage A.J.continuous) ((denseCc d).1 u)
  obtain ⟨e, e₀, e₁, e₃⟩ := hu
  exact ⟨(Submodule.starProjection_apply_eq_zero_iff _).2 e, (h₀ _).1 e₀, (h₁ _).1 e₁, (h₃ _).1 e₃⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LineEx
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem frame_ex {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (B : V → V → ℂ)
    (hlin : ∀ f ∈ S, ∀ f' ∈ S, ∀ f'' ∈ S, ∀ a : ℂ, B f (a • f' + f'') = a * B f f' + B f f'')
    (hsym : ∀ f ∈ S, ∀ f' ∈ S, conj (B f f') = B f' f)
    (hpos : ∀ f ∈ S, f ≠ 0 → 0 < (B f f).re) :
    ∃ (d : ℕ) (sec : Eu d →ₗ[ℂ] V), Function.Injective sec ∧ LinearMap.range sec = S ∧
      ∀ v v', B (sec v) (sec v') = ⟪v, v'⟫_ℂ := by
  have h0 : ∀ f ∈ S, B f 0 = 0 := by
    intro f hf
    have h := hlin f hf 0 S.zero_mem 0 S.zero_mem 1
    simp only [smul_zero, add_zero, one_mul] at h
    simpa using h
  let core : InnerProductSpace.Core ℂ S :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => hsym _ y.2 _ x.2
      re_inner_nonneg := fun x => by
        by_cases hx : (x : V) = 0
        · show 0 ≤ (B x x).re
          have : B x x = 0 := by
            have := h0 _ x.2
            rw [← hx] at this
            simpa [hx] using this
          simp [this]
        · exact (hpos _ x.2 hx).le
      add_left := fun x y z => by
        show B ((x : V) + y) z = B x z + B y z
        have h := hlin _ z.2 _ x.2 _ y.2 1
        rw [one_smul, one_mul] at h
        rw [← hsym _ z.2 _ (S.add_mem x.2 y.2), h, map_add (f := _), hsym _ z.2 _ x.2, hsym _ z.2 _ y.2]
      smul_left := fun x y r => by
        show B (r • (x : V)) y = conj r * B x y
        have h := hlin _ y.2 _ x.2 _ S.zero_mem r
        rw [add_zero, h0 _ y.2, add_zero] at h
        rw [← hsym _ y.2 _ (S.smul_mem r x.2), h, map_mul, hsym _ y.2 _ x.2]
      definite := fun x hx => by
        by_contra hne
        have h := hpos _ x.2 (fun h => hne (Subtype.ext h))
        have hx' : B x x = 0 := hx
        rw [hx'] at h
        simp at h }
  letI : NormedAddCommGroup S := @InnerProductSpace.Core.toNormedAddCommGroup ℂ S _ _ _ core
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore core.toCore
  let e := (stdOrthonormalBasis ℂ S).repr.symm
  refine ⟨Module.finrank ℂ S, S.subtype ∘ₗ (e.toLinearEquiv : _ →ₗ[ℂ] S), ?_, ?_, ?_⟩
  · exact S.injective_subtype.comp e.injective
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  · intro v v'
    exact e.inner_map_map v v'

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.lineEx :
    LineExC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) :=
    ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.mp hK
  haveI : LocallyCompactSpace (KG K (2 + 2)) := hK.isClosed.locallyCompactSpace
  let κ : Measure (KG K (2 + 2)) := Measure.haar
  obtain ⟨⟨c, hc⟩, hvol⟩ := unf μ μ₂ κ
  obtain ⟨S, hfd, hS⟩ := secFD μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂
  have hsf : ∀ f ∈ S, SFun f := fun f hf =>
    secFun μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ f ((hS f).1 hf).1 ((hS f).1 hf).2
  have hsl : ∀ f ∈ S, Slices τ₁ τ₂ f := fun f hf =>
    ((secCrit μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ f ((hS f).1 hf).2).1 ((hS f).1 hf).1).2.2.2.2
  obtain ⟨hz, hl, hp, -⟩ := pmLaws μ₂ κ
  obtain ⟨d, sec, hinj, hr, hB⟩ := frame_ex S
    (fun f f' => ((c * volN K : ℝ) : ℂ) * ∫ k : KG K (2 + 2), pm μ₂ f f' k k ∂κ)
    (fun f hf f' hf' f'' hf'' a => by
      rw [(hl f f' f'' (hsf f hf) (hsf f' hf') (hsf f'' hf'') a).1]; ring)
    (fun f hf f' hf' => by
      rw [map_mul, (hl f f' f' (hsf f hf) (hsf f' hf') (hsf f' hf') 1).2, Complex.conj_ofReal])
    (fun f hf h => by
      rw [Complex.re_ofReal_mul]
      exact mul_pos (mul_pos hc.1 hvol) (hp f (hsf f hf) h))
  have hmem : ∀ v, sec v ∈ S := fun v => hr ▸ LinearMap.mem_range_self sec v
  have hex : ∀ (β : ℝ → ℂ) (v : Eu d), ∃ w : L2 μ, Continuous β → HasCompactSupport β → Reps μ w (theta β (sec v)) := by
    intro β v
    by_cases h : Continuous β ∧ HasCompactSupport β
    · obtain ⟨h1, h2, h3⟩ := bfFun (sec v) β (hsf _ (hmem v)) h.1 h.2
      obtain ⟨w, hw⟩ := ((thBasic μ _ h1.cont h1.rat h2).2.2.2 h3).2.2
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨0, fun a b => (h ⟨a, b⟩).elim⟩
  choose T hT using hex
  obtain ⟨J, hJ⟩ := isoExt d T (by
    intro β β' v v' h1 h2 h3 h4
    rw [pairF μ μ₂ κ c hc (sec v) (sec v') β β' (hsf _ (hmem v)) (hsf _ (hmem v')) h1 h2 h3 h4 _ _
      (hT β v h1 h2) (hT β' v' h3 h4), ← hB v v']
    have h0 : ∀ x y, pw μ₂ (sec v) (sec v') x y = 0 := fun x y =>
      (hz τ₁ τ₂ τ₁ τ₂ _ _ (hsf _ (hmem v)) (hsf _ (hmem v')) (hsl _ (hmem v)) (hsl _ (hmem v')) x y).2 hP.orth
    simp only [h0, mul_zero, integral_zero, add_zero]
    push_cast
    ring)
  refine ⟨d, ⟨⟨sec, hinj, fun f => by rw [hr]; exact hS f, J, ?_⟩⟩⟩
  intro β v u h1 h2 hu
  rw [hJ β v u h1 h2 hu]
  exact hT β v h1 h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PairFacts
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem ext_two {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T T' : E →L[ℂ] H) (S S' : F →L[ℂ] H) (a : Set E) (b : Set F)
    (h : ∀ u ∈ a, ∀ v ∈ b, ⟪T u, S v⟫_ℂ = ⟪T' u, S' v⟫_ℂ) :
    ∀ u ∈ closure (Submodule.span ℂ a : Set E), ∀ v ∈ closure (Submodule.span ℂ b : Set F),
      ⟪T u, S v⟫_ℂ = ⟪T' u, S' v⟫_ℂ := by
  have h1 : ∀ u ∈ a, ∀ v ∈ closure (Submodule.span ℂ b : Set F), ⟪T u, S v⟫_ℂ = ⟪T' u, S' v⟫_ℂ := by
    intro u hu v hv
    have hc : IsClosed {v : F | ⟪T u, S v⟫_ℂ = ⟪T' u, S' v⟫_ℂ} := isClosed_eq (by fun_prop) (by fun_prop)
    refine hc.closure_subset_iff.2 (fun w hw => ?_) hv
    induction hw using Submodule.span_induction with
    | mem x hx => exact h u hu x hx
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [mem_setOf_eq] at hx hy ⊢
      rw [map_add (f := _), map_add (f := _), inner_add_right, inner_add_right, hx, hy]
    | smul c x _ hx =>
      simp only [mem_setOf_eq] at hx ⊢
      rw [map_smul, map_smul, inner_smul_right, inner_smul_right, hx]
  intro u hu v hv
  have hc : IsClosed {u : E | ⟪T u, S v⟫_ℂ = ⟪T' u, S' v⟫_ℂ} := isClosed_eq (by fun_prop) (by fun_prop)
  refine hc.closure_subset_iff.2 (fun w hw => ?_) hu
  induction hw using Submodule.span_induction with
  | mem x hx => exact h1 x hx v hv
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [mem_setOf_eq] at hx hy ⊢
    rw [map_add (f := _), map_add (f := _), inner_add_left, inner_add_left, hx, hy]
  | smul c x _ hx =>
    simp only [mem_setOf_eq] at hx ⊢
    rw [map_smul, map_smul, inner_smul_left, inner_smul_left, hx]

private theorem pure_pair {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K (2 + 2)))
    [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (hP : Pair μ₂ τ₁ τ₂)
    (D : TypeDat K (2 + 2)) (d d' : ℕ) (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d') :
    ∃ (c : ℝ) (κ : Measure (KG K (2 + 2))), ∀ (β β' : ℝ → ℂ) (e : Eu d) (e' : Eu d') (u : L (Eu d)) (v : L (Eu d')),
      Continuous β → HasCompactSupport β → Continuous β' → HasCompactSupport β' → (∀ᵐ x : ℝ, u x = β x • e) →
      (∀ᵐ x : ℝ, v x = β' x • e') → ⟪A.J u, A'.J v⟫_ℂ = c * ∫ t : ℝ, ∫ k : KG K (2 + 2), ∫ X,
        conj (β t) * β' (HH (w0 K * nn X * k.1) - t) * Complex.exp (2 * (HH (w0 K * nn X * k.1) : ℂ)) *
          pw μ₂ (A.sec e) (A'.sec e') k (w0 K * nn X * k.1) ∂unipMeasure K (2 + 2) 2 ∂κ := by
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) :=
    ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.1 hK
  haveI : LocallyCompactSpace (KG K (2 + 2)) := hK.isClosed.locallyCompactSpace
  obtain ⟨c, hc⟩ := (unf μ μ₂ (Measure.haar : Measure (KG K (2 + 2)))).1
  refine ⟨c, Measure.haar, fun β β' e e' u v hβ hβc hβ' hβc' hu hv => ?_⟩
  obtain ⟨hs, hf⟩ := (A.onto (A.sec e)).1 ⟨e, rfl⟩
  obtain ⟨hs', hf'⟩ := (A'.onto (A'.sec e')).1 ⟨e', rfl⟩
  have hS := secFun μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ _ hs hf
  have hS' := secFun μ₂ τ₂ τ₁ D hP.irr₂ hP.irr₁ _ hs' hf'
  have hl := ((secCrit μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ _ hf).1 hs).2.2.2.2
  have hl' := ((secCrit μ₂ τ₂ τ₁ D hP.irr₂ hP.irr₁ _ hf').1 hs').2.2.2.2
  have h0 : ∀ x y, pm μ₂ (A.sec e) (A'.sec e') x y = 0 := fun x y =>
    ((pmLaws μ₂ (Measure.haar : Measure (KG K (2 + 2)))).1 τ₁ τ₂ τ₂ τ₁ _ _ hS hS' hl hl' x y).1 hP.orth
  rw [pairF μ μ₂ Measure.haar c hc _ _ β β' hS hS' hβ hβc hβ' hβc' _ _ (A.spec β e u hβ hβc hu)
    (A'.spec β' e' v hβ' hβc' hv)]
  simp only [h0, integral_zero, mul_zero, zero_add]

private theorem sh_pure {d : ℕ} (s : ℝ) (β : ℝ → ℂ) (e : Eu d) (u : L (Eu d)) (hu : ∀ᵐ x : ℝ, u x = β x • e) :
    ∀ᵐ x : ℝ, UpperTheory.V.Z.IntegralApplyAeEq.sh (Eu d) s u x = β (x + s) • e := by
  filter_upwards [UpperTheory.V.Z.IntegralApplyAeEq.sh_ae (Eu d) s u,
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae hu] with x h1 h2
  rw [h1, h2]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pairFacts :
    UnipotentBlockPairs := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D d d' A A'
  obtain ⟨c, κ, hpure⟩ := pure_pair μ μ₂ τ₁ τ₂ hP D d d' A A'
  refine ⟨fun s u u' v v' hu hv => ?_, fun s u v hu hv => ?_⟩
  · have e1 : u' = UpperTheory.V.Z.IntegralApplyAeEq.sh (Eu d) s u := Lp.ext (by
      filter_upwards [hu, UpperTheory.V.Z.IntegralApplyAeEq.sh_ae (Eu d) s u] with x h1 h2
      rw [h1, h2])
    have e2 : v' = UpperTheory.V.Z.IntegralApplyAeEq.sh (Eu d') s v := Lp.ext (by
      filter_upwards [hv, UpperTheory.V.Z.IntegralApplyAeEq.sh_ae (Eu d') s v] with x h1 h2
      rw [h1, h2])
    subst e1 e2
    refine ext_two (A.J.toContinuousLinearMap ∘L UpperTheory.V.Z.IntegralApplyAeEq.sh (Eu d) s) A.J.toContinuousLinearMap
      A'.J.toContinuousLinearMap (A'.J.toContinuousLinearMap ∘L UpperTheory.V.Z.IntegralApplyAeEq.sh (Eu d') s) _ _ ?_
      u ((denseCc d).1 u) v ((denseCc d').1 v)
    rintro p ⟨β, e, hβ, hβc, hp⟩ q ⟨β', e', hβ', hβc', hq⟩
    have a1 := hpure (fun x => β (x + s)) β' e e' _ q (by fun_prop)
      (hβc.comp_homeomorph (Homeomorph.addRight s)) hβ' hβc' (sh_pure s β e p hp) hq
    have a2 := hpure β (fun x => β' (x + s)) e e' p _ hβ hβc (by fun_prop)
      (hβc'.comp_homeomorph (Homeomorph.addRight s)) hp (sh_pure s β' e' q hq)
    refine a1.trans (Eq.trans ?_ a2.symm)
    congr 1
    refine Eq.trans ?_ (integral_add_right_eq_self _ s)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have : ∀ h : ℝ, h - (t + s) + s = h - t := fun h => by ring
    simp only [this]
  · have := ext_two A.J.toContinuousLinearMap 0 A'.J.toContinuousLinearMap 0 _ _ ?_
      u ((denseCc d).2.2 s u hu) v ((denseCc d').2.2 (2 * 0 - s) v hv)
    · simpa using this
    rintro p ⟨β, e, hβ, hβc, hz, hp⟩ q ⟨β', e', hβ', hβc', hz', hq⟩
    have a1 := hpure β β' e e' p q hβ hβc hβ' hβc' hp hq
    refine a1.trans ?_
    have h0 : ∀ (t : ℝ) (k : KG K (2 + 2)) (X : UPos (2 + 2) 2 → 𝔸[K]),
        conj (β t) * β' (HH (w0 K * nn X * k.1) - t) = 0 := by
      intro t k X
      rcases le_or_gt t s with h | h
      · rw [hz t h, map_zero, zero_mul]
      · have := (longCell (K := K)).1 X k.1 k.2
        rw [hz' _ (by linarith), mul_zero]
    simp only [h0, zero_mul, integral_zero, mul_zero, ContinuousLinearMap.zero_apply, inner_zero_left]
end

