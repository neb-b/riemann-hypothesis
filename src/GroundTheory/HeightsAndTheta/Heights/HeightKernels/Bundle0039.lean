module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0030

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyIntegrableAlt

theorem quad_pos {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (y : Fin e → ℂ) :
    0 < (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re := by
  have hx : (Fin.cons 1 y : Fin (e + 1) → ℂ) ≠ 0 := fun h => by
    have := congr_fun h 0
    simp at this
  exact hM.re_dotProduct_pos hx

theorem measurable_hermChartPot {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    Measurable (hermChartPot M) := by
  have hz : Continuous fun y : Fin e → ℂ => (Fin.cons 1 y : Fin (e + 1) → ℂ) :=
    continuous_const.finCons continuous_id
  have hc : Continuous fun y : Fin e → ℂ =>
      star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) :=
    hz.star.dotProduct (continuous_const.matrix_mulVec hz)
  exact Real.measurable_log.comp (Real.continuous_sqrt.measurable.comp (Complex.measurable_re.comp hc.measurable))

theorem pot_sub_bound (hCmp : HermFormCompare.Statement) {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hM : M.PosDef) (hN : N.PosDef) :
    ∃ K : ℝ, ∀ y : Fin e → ℂ, ‖hermChartPot M y - hermChartPot N y‖ ≤ K := by
  obtain ⟨c, hc, h1⟩ := hCmp _ M N hM hN
  obtain ⟨c', hc', h2⟩ := hCmp _ N M hN hM
  refine ⟨|Real.log c| + |Real.log c'|, fun y => ?_⟩
  have hqM := quad_pos hM y
  have hqN := quad_pos hN y
  have a1 := Real.log_le_log hqM (h1 (Fin.cons 1 y))
  have a2 := Real.log_le_log hqN (h2 (Fin.cons 1 y))
  rw [Real.log_mul hc.ne' hqN.ne'] at a1
  rw [Real.log_mul hc'.ne' hqM.ne'] at a2
  simp only [hermChartPot, Real.log_sqrt hqM.le, Real.log_sqrt hqN.le, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log c), le_abs_self (Real.log c'), abs_nonneg (Real.log c),
    abs_nonneg (Real.log c')]

theorem abs_maDensity_mix_le {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (k : ℕ) (C : ℝ) (y : Fin e → ℂ)
    (hMp : (cxHessian (hermChartPot M) y).PosSemidef) (hNp : (cxHessian (hermChartPot N) y).PosSemidef)
    (hle : ((C : ℂ) • cxHessian (hermChartPot N) y - cxHessian (hermChartPot M) y).PosSemidef) :
    ‖maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y‖ ≤
      max C 1 ^ e * maDensity (fun _ : Fin e => hermChartPot N) y := by
  set HM := cxHessian (hermChartPot M) y
  set HN := cxHessian (hermChartPot N) y
  set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => if (j : ℕ) < k then HM else HN with hAdef
  have hA : (fun j : Fin e => cxHessian (if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) = A := by
    funext j
    simp only [hAdef]
    split_ifs <;> rfl
  set B : Fin e → Matrix (Fin e) (Fin e) ℂ := fun _ => ((max C 1 : ℝ) : ℂ) • HN with hBdef
  have hApsd : ∀ j, (A j).PosSemidef := fun j => by
    simp only [hAdef]
    split_ifs
    · exact hMp
    · exact hNp
  have hsm : ∀ r : ℝ, 0 ≤ r → (((r : ℝ) : ℂ) • HN).PosSemidef := fun r hr =>
    hNp.smul (Complex.zero_le_real.2 hr)
  have hAB : ∀ j, (B j - A j).PosSemidef := fun j => by
    simp only [hBdef, hAdef]
    split_ifs
    · have h : ((max C 1 : ℝ) : ℂ) • HN - HM = ((C : ℂ) • HN - HM) + (((max C 1 - C : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul]
        abel
      rw [h]
      exact hle.add (hsm _ (sub_nonneg.2 (le_max_left C 1)))
    · have h : ((max C 1 : ℝ) : ℂ) • HN - HN = (((max C 1 - 1 : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul, one_smul]
      rw [h]
      exact hsm _ (sub_nonneg.2 (le_max_right C 1))
  have hmono : (mixedDisc A).re ≤ (mixedDisc B).re := ReciprocityTheory.AnForm.A.mdisc_re_mono A B hApsd hAB
  have hnn : 0 ≤ (mixedDisc A).re := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hApsd).2
  have hB : mixedDisc B = ((max C 1 : ℝ) : ℂ) ^ e * HN.det := by
    have h := ReciprocityTheory.AnForm.A.mdisc_const (((max C 1 : ℝ) : ℂ) • HN)
    rw [det_smul, Fintype.card_fin] at h
    exact h
  have hN1 : mixedDisc (fun _ : Fin e => HN) = HN.det := ReciprocityTheory.AnForm.A.mdisc_const HN
  have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDensity
  rw [hA, hN1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_of_nonneg hnn]
  rw [hB, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmono
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (max C 1 ^ e * HN.det.re) :=
        mul_le_mul_of_nonneg_left hmono hc
    _ = _ := by ring

end ChartEnergyIntegrableAlt


open ChartEnergyIntegrableAlt in
theorem ChartEnergyIntegrable.proof (hCmp : HermFormCompare.Statement) (hHess : ChartHessCompare.Statement) :
    ChartEnergyIntegrable.Statement := by
  intro e M N hM hN k
  obtain ⟨C, hC⟩ := hHess e M N hM hN
  obtain ⟨C₀, hC₀⟩ := hHess e N N hN hN
  obtain ⟨K, hK⟩ := pot_sub_bound hCmp hM hN
  have hmix : Integrable (fun y : Fin e → ℂ =>
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) := by
    refine Integrable.mono' ((ChartDensityIntegrable.proof e N hN).const_mul (max C 1 ^ e))
      (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity _).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    exact abs_maDensity_mix_le k C y (hC y).1.posSemidef (hC₀ y).1.posSemidef (hC y).2
  exact hmix.bdd_mul ((measurable_hermChartPot M).sub (measurable_hermChartPot N)).aestronglyMeasurable
    (Eventually.of_forall hK)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcLinear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalLinearForms

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]
  {k : Type} [Field k] {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')}
  {α : T → k} {M : T → Fin i → k}

theorem span_alpha (h : IsExcResidueData b b' α M) : Submodule.span ℤ (Set.range α) = ⊤ := by
  obtain ⟨-, ρ', -, -, hρ', -, -, -, -, hα, -⟩ := h
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨φ, rfl⟩ := hρ' x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b'.sum_repr φ, map_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [map_zsmul, ← hα t]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem linFormsIndep (h : IsExcResidueData b b' α M) : LinFormsIndep M := by
  obtain ⟨-, -, σ, -, -, hσ, -, -, -, -, hM⟩ := h
  intro w hw
  funext j
  obtain ⟨φ, hφ⟩ := hσ (Pi.single j 1)
  have hcomb : ∀ j', σ φ j' = ∑ t, (b.repr φ t : k) * M t j' := by
    intro j'
    have hs : σ φ = ∑ t, b.repr φ t • M t := by
      conv_lhs => rw [← b.sum_repr φ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [map_zsmul, hM]
    rw [hs, Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
  have key : ∑ j', σ φ j' * w j' = 0 := by
    simp only [hcomb, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum, hw t, mul_zero]
  rw [hφ] at key
  simpa [Pi.single_apply] using key

end StackedExceptionalLinearForms


open StackedExceptionalLinearForms in
theorem DualStackedExcLinear.proof (hEx : DualStackedExcResidueExists.Statement)
    (hBase : DualStackedExcBaseLe.Statement) (hLe : DualStackedExcLinPrimeLe.Statement) :
    DualStackedExcLinear.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab E hE
  obtain ⟨k, hk, hkf, α, M, hD, hcard⟩ := hEx K i F F' T b b' a hi hlt hcov hab
  have h1 : stackedBase b' a ≤ linPrime α M := hBase K i F F' T b b' a hi hlt hcov hab k α M hD
  have h2 : linPrime α M ≤ E := hLe K i F F' T b b' a hi hlt hcov hab k α M hD E hE.1.1.1 hE.1.1.2 hE.2
  have hprime : (linPrime α M).IsPrime := RingHom.ker_isPrime _
  exact ⟨k, hk, hkf, α, M, span_alpha hD, linFormsIndep hD, le_antisymm (hE.1.2 ⟨hprime, h1⟩ h2) h2, hcard⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdFibreRatios
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

namespace StandardDualFibreRatios

theorem nonempty_of_basis {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) (hi : 1 ≤ i) : Nonempty T := by
  by_contra hT
  rw [not_nonempty_iff] at hT
  have h := DualArithmeticVariety.span_basis (K := K) b
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  have h1 : (Pi.single (⟨0, hi⟩ : Fin i) 1 : Fin i → K) ∈ (⊥ : Submodule K (Fin i → K)) := h ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at h1
  have h2 := congrFun h1 ⟨0, hi⟩
  simp at h2

end StandardDualFibreRatios


open StandardDualFibreRatios in
theorem DualStdFibreRatios.proof (hTr : GenFibreModelTransport.Statement) (hMod : DualStdGraphModel.Statement)
    (hRk : DualStdModelRank.Statement) (hTc : DualStdModelTransc.Statement) : DualStdFibreRatios.Statement := by
  intro K _ _ i T _ _ b G hi
  obtain ⟨c⟩ := nonempty_of_basis b hi
  let Φ₀ : Subfield (dualStdModelField K i) :=
    Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i)))
  have hΦ₀ : (algebraMap Φ₀ (dualStdModelField K i)).fieldRange = Φ₀ := Subfield.fieldRange_subtype _
  obtain ⟨h0, hrk, htr⟩ := hTr Unit (PBlk i) (Unit ⊕ Unit) (Sum.elim (dualBlocks T) (PBlk i))
    (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
    (graphIdeal (dualIdeal b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b))) G (dualStdModelField K i)
    (dualStdModelPt b) (hMod K i T b) Φ₀ hΦ₀ T
    (fun t => (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))
    (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)
  obtain ⟨hz, hrk₀⟩ := hRk K i T b Φ₀ hΦ₀ hi c
  refine ⟨c, fun h => hz (h0.mp h), ?_, ?_⟩
  · exact hrk.trans hrk₀
  · exact htr.mpr (hTc K i T b Φ₀ hΦ₀ hi c)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdGraphModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StandardDualGraphModel

open StandardDualImageBottom

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

theorem mConeMap_linForm (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (q : Σ _ : Unit, Fin i) :
    mConeMap (dualLatticeCoord b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b) q) =
      C (aeval (dualLatticeCoord b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b) q)) * X () := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ReciprocityTheory.ChartRestriction.G.AI.I4.linForm, map_sum, map_mul, Finset.sum_mul, mConeMap, aeval_X, eq_intCast, map_intCast]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]

def coneLift (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MRing (dualBlocks T) ⧸ dualIdeal b →+* MvPolynomial Unit (ProjField K i) :=
  Ideal.Quotient.lift (dualIdeal b)
    (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i)) fun _ ha => ha

omit [Fintype T] in
theorem coneLift_mk (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (f : MRing (dualBlocks T)) :
    coneLift b (Ideal.Quotient.mk _ f) = mConeMap (dualLatticeCoord b) f :=
  rfl

omit [Fintype T] in
theorem coneLift_injective (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (coneLift b) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ fun _ ha => ha

def modelMap (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MvPolynomial Unit (MRing (dualBlocks T) ⧸ dualIdeal b) →+* dualStdModelField K i :=
  (algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _).comp (MvPolynomial.map (coneLift b))

omit [Fintype T] in
theorem modelMap_injective (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (modelMap b) :=
  (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) (dualStdModelField K i)).comp
    (MvPolynomial.map_injective _ (coneLift_injective b))

theorem modelMap_comp_graphMap [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    (modelMap b).comp (graphMap (dualIdeal b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b))) =
      (eval₂Hom (Int.castRingHom (dualStdModelField K i)) (dualStdModelPt b) :
        MRing (Sum.elim (dualBlocks T) (PBlk i)) →+* dualStdModelField K i) := by
  refine MvPolynomial.ringHom_ext (fun r => by simp) ?_
  rintro ⟨(u | u), j⟩ <;> cases u
  · simp [graphMap, modelMap, coneLift_mk, dualStdModelPt, dualStdModelEmb, dualStdModelS,
      mConeMap]
  · have h := mConeMap_linForm b ⟨(), j⟩
    rw [aeval_linForm] at h
    simp only [RingHom.comp_apply, graphMap, eval₂Hom_X', modelMap, map_mul, map_C, map_X, coneLift_mk, h,
      dualStdModelPt, dualStdModelEmb, dualStdModelS, dualStdModelT, GroundTheory.Heights₂.Heights.StandardDualImageBottom.genPt]

end StandardDualGraphModel


open StandardDualGraphModel in
theorem DualStdGraphModel.proof : DualStdGraphModel.Statement := by
  intro K _ _ i T _ _ b
  rw [← modelMap_comp_graphMap b]
  ext f
  rw [graphIdeal, RingHom.mem_ker, RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ (modelMap_injective b)]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdModelTransc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StandardDualModelTranscendence

variable {L : Type} [Field L]

def scaleHom (a : L) :
    MvPolynomial Unit (MvPolynomial Unit L) →+* MvPolynomial Unit (MvPolynomial Unit L) :=
  eval₂Hom ((C : MvPolynomial Unit L →+* MvPolynomial Unit (MvPolynomial Unit L)).comp
      (aeval fun _ : Unit => C a * X ()).toRingHom) fun _ => C (C a⁻¹) * X ()

theorem scaleHom_CC (a c : L) : scaleHom a (C (C c)) = C (C c) := by simp [scaleHom]

theorem scaleHom_S (a : L) : scaleHom a (C (X ())) = C (C a) * C (X ()) := by simp [scaleHom]

theorem scaleHom_alt (a : L) : scaleHom a (X ()) = C (C a⁻¹) * X () := by simp [scaleHom]

theorem scaleHom_comp {a : L} (ha : a ≠ 0) : (scaleHom a⁻¹).comp (scaleHom a) = RingHom.id _ := by
  have hC : ((scaleHom a⁻¹).comp (scaleHom a)).comp C =
      (C : MvPolynomial Unit L →+* MvPolynomial Unit (MvPolynomial Unit L)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
    · simp only [RingHom.comp_apply, scaleHom_CC]
    · cases v
      simp only [RingHom.comp_apply, scaleHom_S, map_mul, scaleHom_CC]
      rw [← mul_assoc, ← map_mul, ← map_mul, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  refine MvPolynomial.ringHom_ext (fun p => ?_) (fun u => ?_)
  · exact RingHom.congr_fun hC p
  · cases u
    simp only [RingHom.comp_apply, scaleHom_alt, map_mul, scaleHom_CC, RingHom.id_apply]
    rw [← mul_assoc, ← map_mul, ← map_mul, inv_inv, inv_mul_cancel₀ ha, map_one, map_one, one_mul]

theorem scaleHom_injective {a : L} (ha : a ≠ 0) : Function.Injective (scaleHom a) :=
  Function.LeftInverse.injective (g := scaleHom a⁻¹) fun p => RingHom.congr_fun (scaleHom_comp ha) p

def scale {a : L} (ha : a ≠ 0) :
    FractionRing (MvPolynomial Unit (MvPolynomial Unit L)) →+*
      FractionRing (MvPolynomial Unit (MvPolynomial Unit L)) :=
  IsFractionRing.lift (A := MvPolynomial Unit (MvPolynomial Unit L))
    (g := (algebraMap _ (FractionRing (MvPolynomial Unit (MvPolynomial Unit L)))).comp (scaleHom a))
    ((IsFractionRing.injective _ _).comp (scaleHom_injective ha))

theorem scale_algebraMap {a : L} (ha : a ≠ 0) (p : MvPolynomial Unit (MvPolynomial Unit L)) :
    scale ha (algebraMap _ _ p) = algebraMap _ _ (scaleHom a p) :=
  IsFractionRing.lift_algebraMap _ p

theorem transcendental_of_scale {R Ω : Type} [CommRing R] [Field Ω] [CharZero Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {z : Ω} (hz : z ≠ 0)
    (h : ∀ n : ℕ, ∃ σ : Ω →+* Ω, (∀ y ∈ A, σ y = y) ∧ σ z = ((n : Ω) + 1) * z) : Transcendental A z := by
  rintro ⟨p, hp0, hp⟩
  rw [Polynomial.aeval_def] at hp
  have hroot : ∀ n : ℕ, Polynomial.eval₂ (algebraMap A Ω) (((n : Ω) + 1) * z) p = 0 := by
    intro n
    obtain ⟨σ, hfix, hσz⟩ := h n
    have hcomp : σ.comp (algebraMap A Ω) = algebraMap A Ω := RingHom.ext fun y => hfix y y.2
    have h' := Polynomial.hom_eval₂ p (algebraMap A Ω) σ z
    rw [hp, map_zero, hcomp, hσz] at h'
    exact h'.symm
  have hq : p.map (algebraMap A Ω) ≠ 0 := (Polynomial.map_ne_zero_iff fun x y h => Subtype.ext h).mpr hp0
  refine hq (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : Ω) + 1) * z) (fun n m hnm => ?_) fun n => ?_
  · exact Nat.cast_injective (add_right_cancel (mul_right_cancel₀ hz hnm))
  · change Polynomial.IsRoot _ _
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact hroot n

variable {K : Type} [Field K] {i : ℕ}

theorem scale_emb {a : ProjField K i} (ha : a ≠ 0) (x : ProjField K i) :
    scale ha (dualStdModelEmb K i x) = dualStdModelEmb K i x := by
  simp only [dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_CC]

theorem scale_S {a : ProjField K i} (ha : a ≠ 0) :
    scale ha (dualStdModelS K i) = dualStdModelEmb K i a * dualStdModelS K i := by
  simp only [dualStdModelS, dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_S, map_mul]

theorem scale_alt {a : ProjField K i} (ha : a ≠ 0) :
    scale ha (dualStdModelT K i) = dualStdModelEmb K i a⁻¹ * dualStdModelT K i := by
  simp only [dualStdModelT, dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_alt, map_mul]

variable [NumberField K] {F : HermLattice K i} {T : Type} (b : Module.Basis T ℤ (dualLattice F))

theorem scale_inl {a : ProjField K i} (ha : a ≠ 0) (t : T) :
    scale ha (dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      dualStdModelEmb K i a * dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) := by
  simp only [dualStdModelPt, map_mul, scale_emb, scale_S]
  ring

theorem scale_inr {a : ProjField K i} (ha : a ≠ 0) (j : PBlk i ()) :
    scale ha (dualStdModelPt b (⟨Sum.inr (), j⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      dualStdModelPt b (⟨Sum.inr (), j⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) := by
  have h : dualStdModelEmb K i a * dualStdModelEmb K i a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  simp only [dualStdModelPt, map_mul, scale_emb, scale_S, scale_alt]
  linear_combination
    (dualStdModelEmb K i (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)) * dualStdModelS K i *
      dualStdModelT K i) * h

end StandardDualModelTranscendence


open DualArithmeticVariety StandardDualModelTranscendence in
theorem DualStdModelTransc.proof : DualStdModelTransc.Statement := by
  intro K _ _ i T _ _ b Φ₀ _ _ hΦ _ c
  have hy : dualLatticeCoord b ⟨(), c⟩ ≠ 0 := by
    rw [dualLatticeCoord_eq]
    exact evalForm_ne_zero fun h => b.ne_zero c (Subtype.ext h)
  have hS : dualStdModelS K i ≠ 0 := by
    intro h
    have h' := IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
      (dualStdModelField K i) (h.trans (map_zero _).symm)
    simp at h'
  refine transcendental_of_scale _ (mul_ne_zero ((map_ne_zero _).mpr hy) hS) fun n => ?_
  have ha : ((n : ProjField K i) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hΦfix : ∀ x : Φ₀, scale ha (algebraMap Φ₀ _ x) = algebraMap Φ₀ _ x := by
    intro x
    have hx : algebraMap Φ₀ (dualStdModelField K i) x ∈
        Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) :=
      hΦ ▸ RingHom.mem_fieldRange.mpr ⟨x, rfl⟩
    refine RingHom.eqOn_field_closure (g := RingHom.id _) ?_ hx
    rintro _ ⟨⟨u, j⟩, rfl⟩
    cases u
    exact scale_inr b ha j
  let σ : dualStdModelField K i →ₐ[Φ₀] dualStdModelField K i := { scale ha with commutes' := hΦfix }
  refine ⟨scale ha, fun y hyA => AlgHom.adjoin_le_equalizer σ (AlgHom.id Φ₀ _) ?_ hyA, ?_⟩
  · rintro _ ⟨t, rfl⟩
    change scale ha _ = _
    rw [map_div₀, scale_inl b ha, scale_inl b ha, mul_div_mul_left _ _ ((map_ne_zero _).mpr ha)]
    rfl
  · rw [scale_inl b ha]
    simp

end

end GroundTheory.Heights₂.Heights
end

