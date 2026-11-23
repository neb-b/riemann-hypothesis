module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0075
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralComplexInvPowAddNormSqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_inv_pow_add_norm_sq : ∀ (m : ℕ) (a : ℝ), 0 < a → ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹) = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  first | exact @GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq | exact GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq | (intros; apply GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFinite
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.GJInt

theorem det_blk {k : Type} [Field k] {n : ℕ} (x : k) (u v : Fin n → k) (M : Matrix (Fin n) (Fin n) k) :
    (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det =
      x * M.det + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det := by
  rw [det_succ_row_zero, det_succ_row_zero (Matrix.of _), Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Matrix.submatrix]
  exact Or.inl rfl

theorem mem_intM_blk {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (x : k) (u v : Fin n → k) (M : Matrix (Fin n) (Fin n) k) :
    Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))) ∈ intM k (Fin (n + 1)) (Fin (n + 1)) ↔
      x ∈ 𝒪[k] ∧ (∀ j, u j ∈ 𝒪[k]) ∧ (∀ i, v i ∈ 𝒪[k]) ∧ M ∈ intM k (Fin n) (Fin n) := by
  simp only [intM, Set.mem_setOf_eq, Fin.forall_fin_succ, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, forall_and]
  tauto

theorem det_mem_int {k : Type} [Field k] [ValuativeRel k] {n : ℕ} {X : Matrix (Fin n) (Fin n) k}
    (hX : X ∈ intM k (Fin n) (Fin n)) : X.det ∈ 𝒪[k] := by
  have h1 := (𝒪[k].subtype).map_det (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k]))
  have h2 : (𝒪[k].subtype).mapMatrix (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k])) = X := by ext; rfl
  rw [h2] at h1
  rw [← h1]
  exact SetLike.coe_mem _

theorem intdet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (n : ℕ) (s : ℝ), -1 < s →
    ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
  intro k _ _ _ _ _ _ μ _ n s hs
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hOm : MeasurableSet (𝒪[k] : Set k) := GlobalTheory.SplitWeil.Model.isOpen_int.measurableSet
  have hO : μ (𝒪[k] : Set k) ≠ ⊤ := GlobalTheory.SplitWeil.Model.isCompact_int.measure_lt_top.ne
  set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP
  show ∫⁻ X, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ∂(volM μ (Fin n) (Fin n)) < ⊤
  rcases le_or_gt 0 s with hs0 | hs0
  · have hb : ∀ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ≤
        (intM k (Fin n) (Fin n)).indicator 1 X := by
      intro X
      by_cases hX : X ∈ intM k (Fin n) (Fin n)
      · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX]
        have hdet := det_mem_int hX
        simp only [P, Pi.one_apply]
        split_ifs with h
        · rcases hs0.eq_or_lt with h0 | h0
          · simp [← h0]
          · simp [ENNReal.zero_rpow_of_pos h0]
        · exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.2 (GlobalTheory.SplitWeil.Model.nabs_le_one _ hdet)) hs0
      · simp [Set.indicator_of_notMem hX]
    have hint : intM k (Fin n) (Fin n) = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (𝒪[k] : Set k) : Set (Fin n → Fin n → k)) := by
      ext X; exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    have hm : MeasurableSet (intM k (Fin n) (Fin n)) := by
      rw [hint]; exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hOm
    calc _ ≤ ∫⁻ X, (intM k (Fin n) (Fin n)).indicator 1 X ∂(volM μ (Fin n) (Fin n)) := lintegral_mono hb
      _ = volM μ (Fin n) (Fin n) (intM k (Fin n) (Fin n)) := lintegral_indicator_one hm
      _ < ⊤ := by
        rw [hint, volM]; erw [Measure.pi_pi]
        simp only [Measure.pi_pi]
        exact ENNReal.prod_lt_top fun _ _ => ENNReal.prod_lt_top fun _ _ => hO.lt_top
  · set K : ℝ≥0∞ := ∫⁻ x, (𝒪[k] : Set k).indicator P x ∂μ + μ (𝒪[k] : Set k) with hK
    have hKt : K ≠ ⊤ := ENNReal.add_ne_top.2 ⟨(GlobalTheory.T.lintegral_abs_pow_integers_finite k μ s hs).ne, hO⟩
    induction n with
    | zero =>
      calc _ ≤ ∫⁻ X, 1 ∂(volM μ (Fin 0) (Fin 0)) := lintegral_mono fun X => ?_
        _ < ⊤ := by rw [lintegral_one, volM]; erw [Measure.pi_univ]; simp
      by_cases hX : X ∈ intM k (Fin 0) (Fin 0)
      · rw [Set.indicator_of_mem hX]
        simp [P, GlobalTheory.SplitWeil.Model.nabs_one]
      · simp [Set.indicator_of_notMem hX]
    | succ n ih =>
      let U : Set (Fin n → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
      have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => hOm
      have hUv : (Measure.pi fun _ : Fin n => μ) U = μ 𝒪[k] ^ n := by simp [U, Measure.pi_pi]
      have hUt : μ 𝒪[k] ^ n ≠ ⊤ := ENNReal.pow_ne_top hO
      set I := fun M : Matrix (Fin n) (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) M with hI
      have inner : ∀ M v u, ∫⁻ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
          (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) ∂μ ≤
          U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u := by
        intro M v u
        by_cases h : u ∈ U ∧ v ∈ U ∧ M ∈ intM k (Fin n) (Fin n)
        · obtain ⟨hu, hv, hM⟩ := h
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hv]
          simp only [I, Set.indicator_of_mem hM]
          have he : ∀ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
              (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) =
              (𝒪[k] : Set k).indicator (fun y => P (M.det * y + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det)) x := by
            intro x
            by_cases hx : x ∈ (𝒪[k] : Set k)
            · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((mem_intM_blk x u v M).2 ⟨hx, fun j => hu j trivial, fun i => hv i trivial, hM⟩), det_blk, mul_comm x]
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((mem_intM_blk x u v M).1 h).1)]
          simp_rw [he]
          refine (GlobalTheory.T.lintegral_affine_abs_pow_bound k μ s hs0 M.det _).trans (le_of_eq ?_)
          rw [mul_comm]
        · rw [show (fun x => (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
              (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))) = fun _ => 0 from ?_]
          · simp
          funext x
          refine Set.indicator_of_notMem (fun hx => h ?_) _
          obtain ⟨_, hu, hv, hM⟩ := (mem_intM_blk x u v M).1 hx
          exact ⟨fun j _ => hu j, fun i _ => hv i, hM⟩
      calc _ ≤ _ := _root_.GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner k μ n _
        _ ≤ ∫⁻ M, ∫⁻ v, ∫⁻ u, U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u
              ∂(Measure.pi fun _ : Fin n => μ) ∂(Measure.pi fun _ : Fin n => μ) ∂(volM μ (Fin n) (Fin n)) :=
            lintegral_mono fun M => lintegral_mono fun v => lintegral_mono fun u => inner M v u
        _ = ∫⁻ M, K * I M * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) ∂(volM μ (Fin n) (Fin n)) := by
            refine lintegral_congr fun M => ?_
            simp_rw [lintegral_indicator_const hU, hUv]
            rw [lintegral_mul_const' _ _ hUt, lintegral_indicator_const hU, hUv, mul_assoc]
        _ = K * (∫⁻ M, I M ∂(volM μ (Fin n) (Fin n))) * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) := by
            rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hUt hUt), lintegral_const_mul' _ _ hKt]
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hKt.lt_top ih) (ENNReal.mul_lt_top hUt.lt_top hUt.lt_top)

end GlobalTheory.GJInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem loc_val (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (i j : Fin n) :
    (Matrix.GeneralLinearGroup.map (pLoc E w) g).1 i j = pLoc E w (g.1 i j) := rfl

theorem loc_inv_val (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (i j : Fin n) :
    ((Matrix.GeneralLinearGroup.map (pLoc E w) g)⁻¹).1 i j = pLoc E w ((g⁻¹).1 i j) := by
  rw [← map_inv]; rfl

theorem gl_ext {g h : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (H : ∀ w : Pl E, Matrix.GeneralLinearGroup.map (pLoc E w) g = Matrix.GeneralLinearGroup.map (pLoc E w) h) :
    g = h :=
  Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w =>
    congrArg (fun x : GLw n w => x.1 i j) (H w)))

theorem mem_KGL_iff {w : Pl E} {x : GLw n w} : x ∈ GlobalTheory.LFun.KGL w (n := n) ↔
    (∀ i j, x.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (x⁻¹).1 i j ∈ w.adicCompletionIntegers E :=
  GlobalTheory.AdelicU.mem_GLint_iff

theorem mem_Kglob {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)} :
    g ∈ Kglob E n ↔ ∀ w : Pl E, Matrix.GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  simp only [Kglob, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem coe_Kglob : (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) =
    (PIW.ClassFinD.KGL E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  ext g
  change g ∈ Kglob E n ↔ PIW.ClassFinD.MatInt g.val ∧ PIW.ClassFinD.MatInt (g⁻¹).val
  rw [mem_Kglob]
  simp only [mem_KGL_iff, loc_val, loc_inv_val]
  exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
    fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩

theorem isCompact_Kglob : IsCompact (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  rw [coe_Kglob]; exact GlobalTheory.isCompact_KGL E n

theorem isOpen_Kglob : IsOpen (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  have hO : IsOpen ((PIW.ClassFinD.Ohat E : Subring (FiniteAdeleRing (𝓞 E) E)) : Set (FiniteAdeleRing (𝓞 E) E)) :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hM : IsOpen {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) | PIW.ClassFinD.MatInt M} := by
    have e : {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) | PIW.ClassFinD.MatInt M} =
        ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) => M i j) ⁻¹'
          ((PIW.ClassFinD.Ohat E : Subring (FiniteAdeleRing (𝓞 E) E)) : Set (FiniteAdeleRing (𝓞 E) E)) := by
      ext M; simp [PIW.ClassFinD.MatInt]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage ((continuous_apply j).comp (continuous_apply i))
  rw [coe_Kglob]
  exact (hM.preimage Units.continuous_val).inter (hM.preimage Units.continuous_coe_inv)

theorem mem_orb_iff (u w : Pl E) :
    w ∈ orb E u ↔ w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) := by
  rw [orb, Finset.mem_insert, Finset.mem_singleton, GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]; exact GlobalTheory.SplitPts.conjPl_self_conjSrc u
  · have e := eq_conjSrc h
    change w = conjSrc (IsCMField.complexConj E).toRingEquiv u
    rw [e]
    exact (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w).symm

end GlobalTheory.EulerTwRestr

namespace GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.EulerTwRestr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTestFactorNeZeroOfGlobalProductNeZero
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.SuppFin

theorem factor_ne_zero_of_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ y : finU (E := E) (n := n), (∀ᶠ w in cofinite, cLoc w y.1 ∈ GlobalTheory.LFun.KGL w (n := n)) → globFn S f y ≠ 0 → ∀ w ∈ S, f w (toSub _ (cLoc w y.1)) ≠ 0 := by
  intro E _ _ _ n S K' f hT y hy hne w hw h0
  set F : Pl E → ℂ := fun w => f w (toSub _ (cLoc w y.1)) with hF
  have hev : ∀ᶠ v in cofinite, F v = 1 := by
    filter_upwards [hT.2, hy] with v hv hyv
    simp only [hF, hv]
    have hmem : toSub (UL n v) (cLoc v y.1) ∈ KL n v := by
      unfold toSub
      split_ifs with h
      · exact (Subgroup.mem_subgroupOf).2 hyv
      · exact Subgroup.one_mem _
    exact Set.indicator_of_mem (show toSub (UL n v) (cLoc v y.1) ∈ ((KL n v : Subgroup (UL n v)) : Set (UL n v)) from hmem) _
  have hfin : (Function.mulSupport F).Finite := by
    have := Filter.eventually_cofinite.1 hev
    exact this
  have hfin' : (S ∩ Function.mulSupport F).Finite := hfin.subset Set.inter_subset_right
  apply hne
  show ∏ᶠ v ∈ S, F v = 0
  rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod F hfin']
  apply Finset.prod_eq_zero (i := w)
  · rw [Set.Finite.mem_toFinset]
    refine ⟨hw, ?_⟩
    rw [Function.mem_mulSupport]
    change f w (toSub _ (cLoc w y.1)) ≠ 1
    rw [h0]; exact zero_ne_one
  · exact h0

end GlobalTheory.BCT.SuppFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsCompEqOfFunctionFieldMapsAgree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem Dbl.p_comp_eq_of_isHom : ∀ (F : Type) [Field F] (X Y : Var F) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), (ratOf X).IsHom (ratOf Y) φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → W.p₁ ≫ f = W.p₂ ≫ f := by
  intro F _ X Y φ f hf W hW
  haveI : IsDominant (W.Z.fromSpecStalk (genericPoint W.Z)) := ⟨by
    rw [DenseRange, dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec W.Z).def]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩)⟩
  haveI : IsSeparated X.str := (ratOf X).sep
  have hs : f ≫ X.str = Y.str := hf.inducedModelMorphism_comp_structureMap
  refine ext_of_isDominant_of_isSeparated X.str ?_ (W.Z.fromSpecStalk (genericPoint W.Z)) ?_
  · change (W.p₁ ≫ f) ≫ X.str = (W.p₂ ≫ f) ≫ X.str
    rw [Category.assoc, Category.assoc, hs, W.str_eq]
  · have e₁ := specMap_functionFieldMap W.p₁
    have e₂ := specMap_functionFieldMap W.p₂
    have hφ : (functionFieldMap W.p₁).comp φ.toRingHom = (functionFieldMap W.p₂).comp φ.toRingHom :=
      RingHom.ext hW
    have key : ∀ (α : Y.Fn →+* W.Z.functionField),
        Spec.map (CommRingCat.ofHom α) ≫ genericFieldPoint Y.X ≫ f =
          Spec.map (CommRingCat.ofHom (α.comp φ.toRingHom)) ≫ (ratOf X).pt := by
      intro α
      have hf' : genericFieldPoint Y.X ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hf
      rw [hf', CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    change genericFieldPoint W.Z ≫ W.p₁ ≫ f = genericFieldPoint W.Z ≫ W.p₂ ≫ f
    rw [← Category.assoc, ← e₁, Category.assoc, ← Category.assoc (genericFieldPoint W.Z), ← e₂, Category.assoc,
      key, key, hφ]

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatGoodOfBlockExtensionTwist
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace.FullRankSum

theorem joint_inj {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L] [IsFractionRing O L] {a b c : ℕ}
    (B : Mx O a c) (C : Mx O b c) (h : ∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) (x : Fin c → L)
    (hB : (B.map (algebraMap O L)).mulVec x = 0) (hC : (C.map (algebraMap O L)).mulVec x = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6; revert O L h_2 h_3 h_4 h_5 h_6 a b c B C h x hB hC; exact @_root_.GlobalTheory.MulVecZeroDenominator.target)
  | exact @_root_.GlobalTheory.MulVecZeroDenominator.target
  | exact _root_.GlobalTheory.MulVecZeroDenominator.target
  | (apply _root_.GlobalTheory.MulVecZeroDenominator.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulVecZeroDenominator.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulVecZeroDenominator.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulVecZeroDenominator.target ..)

theorem exists_equiv {L : Type} [Field L] {n : ℕ} (B : Mx L n (n + 1)) (C : Mx L 1 (n + 1))
    (h : ∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) :
    ∃ e : (Fin (n + 1) → L) ≃ₗ[L] (Fin n → L) × (Fin 1 → L), ∀ v, e v = (B.mulVec v, C.mulVec v) := by
  let φ : (Fin (n + 1) → L) →ₗ[L] (Fin n → L) × (Fin 1 → L) := (Matrix.toLin' B).prod (Matrix.toLin' C)
  have hi : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact h v (congrArg Prod.fst hv) (congrArg Prod.snd hv)
  exact ⟨φ.linearEquivOfInjective hi (by simp), fun v => rfl⟩

variable {l : ℕ} [Fact l.Prime] {K LL : FinExt l}

theorem tw_mulVec {a b : ℕ} {r : ↥(GK K) →* GL (Fin b) ↥(OL LL)} {r' : ↥(GK K) →* GL (Fin a) ↥(OL LL)}
    {A : Mx ↥(OL LL) a b} (hA : Tw r r' A) (g : ↥(GK K)) (y : Fin b → ↥LL.1) :
    (A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec (repOf r g y) =
      repOf r' g ((A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec y) := by
  rw [repOf_apply, repOf_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul,
    hA g]

theorem matGood_sum : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (ρ : ↥(GK K) →* GL (Fin 1) ↥(OL LL)) (r₂ : ↥(GK K) →* GL (Fin (n + 1)) ↥(OL LL)) (U U' : ZMod f → Multiset ℤ) (B : Mx ↥(OL LL) n (n + 1)) (C : Mx ↥(OL LL) 1 (n + 1)), MatGood P emb r U → MatGood P emb ρ U' → Tw r₂ r B → Tw r₂ ρ C → (∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) → MatGood P emb r₂ (fun i => U i + U' i) := by
  intro l _ P AI T K LL f n emb r ρ r₂ U U' B C hr hρ hB hC hinj
  obtain ⟨_, -, -, -, -, -, hF⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨e, he⟩ := exists_equiv (B.map (algebraMap ↥(OL LL) ↥LL.1)) (C.map (algebraMap ↥(OL LL) ↥LL.1))
    (joint_inj B C hinj)
  have hq : ∀ g v, e (repOf r₂ g v) = (repOf r g (e v).1, repOf ρ g (e v).2) := fun g v => by
    rw [he, he, tw_mulVec hB, tw_mulVec hC]
  obtain ⟨-, hc, hm⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T K LL _ (repOf r₂) _ (repOf r) _ (repOf ρ) e hq
  refine ⟨fun a b => ?_, hc.2 ⟨hr.2.1, hρ.2.1⟩, fun i τ hτ a => ?_⟩
  · have c1 : Continuous (e.symm.toLinearMap ∘ₗ LinearMap.inl _ _ _) := LinearMap.continuous_on_pi _
    have c2 : Continuous (e.symm.toLinearMap ∘ₗ LinearMap.inr _ _ _) := LinearMap.continuous_on_pi _
    have d1 : Continuous fun g => repOf r g (e (Pi.single b 1)).1 := (latOf r hr.1).cont _
    have d2 : Continuous fun g => repOf ρ g (e (Pi.single b 1)).2 := (latOf ρ hρ.1).cont _
    have d := (continuous_apply a).comp ((c1.comp d1).add (c2.comp d2))
    refine d.congr fun g => ?_
    have : repOf r₂ g (Pi.single b 1) = e.symm (repOf r g (e (Pi.single b 1)).1, 0) +
        e.symm (0, repOf ρ g (e (Pi.single b 1)).2) := by
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add, ← hq, e.symm_apply_apply]
    have h2 := congrFun this a
    rw [repOf_apply, Matrix.mulVec_single_one] at h2
    exact h2.symm
  · rw [hm, hr.2.2 i τ hτ a, hρ.2.2 i τ hτ a, Multiset.count_add]
    push_cast
    rfl

end GlobalTheory.WachPlace.FullRankSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtPLoc
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

theorem pLoc_ext {a b : FiniteAdeleRing (𝓞 E) E} (h : ∀ v, pLoc E v a = pLoc E v b) : a = b :=
  Subtype.ext (funext h)

theorem matrix_ext_pLoc {A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (h : ∀ v, A.map (pLoc E v) = B.map (pLoc E v)) : A = B := by
  refine Matrix.ext fun i j => ?_
  exact pLoc_ext E fun v => congrFun (congrFun (h v) i) j

end GlobalTheory.EulerTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFixesLowRankProjectorOfFixesRationalKernel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.RatFix

theorem ratfix_mul_eq (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E) (hBA : B₀ * A₀ = 1) (G : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (hG : ∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) :
    G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) := by
  set ι : E →+* R ⊗[F] E := inclR (F := F) R with hι
  have hN : (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) - A₀.map ι * B₀.map ι = (1 - A₀ * B₀).map ι := by
    rw [Matrix.map_sub _ (map_sub ι), Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]
  rw [hN]
  have hBN : B₀ * (1 - A₀ * B₀) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBA, Matrix.one_mul, sub_self]
  ext i j
  have hv : B₀.mulVec (fun k => ((1 : Matrix (Fin M) (Fin M) E) - A₀ * B₀) k j) = 0 := by
    funext a
    have := congrFun (congrFun hBN a) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have := congrFun (hG _ hv) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem ratfix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E), B₀ * A₀ = 1 → ∀ G : Matrix (Fin M) (Fin M) (R ⊗[F] E), (∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) → G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) :=
  fun F E _ _ _ R _ _ M A₀ B₀ hBA G hG => ratfix_mul_eq F E R M A₀ B₀ hBA G hG

end GlobalTheory.RatFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBoundedStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maxCompactGL_of_commute_etale_charpoly_bounded : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N t : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    t * N = N * t → IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) (w.adicCompletion E)))) →
    t ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.StabInt.mem_KGL_of_commute | exact GlobalTheory.StabInt.mem_KGL_of_commute | (intros; apply GlobalTheory.StabInt.mem_KGL_of_commute <;> assumption)
end

