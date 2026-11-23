module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0026
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import ReciprocityTheory.SemistableReduction.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.GenericSectionMinimumIntegral

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountQAtStGenericSectionPrimes
section
namespace GlobalTheory.SecCount

open MvPolynomial

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ)


variable {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem mem_one (k : Fin N) : emb X la N (X.inc wL (w k)) ∈ Vw X la N (addL (wt0 D j) wL 1) := by
  rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k)

theorem sfr_eq_sum (i : Fin (WeightFamilies.dimY D j + 1)) :
    sfr X la w i = ∑ k, algebraMap (Kp X la N) ↥(Frac0 X la w) (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k))) *
      CurveLoc.fr0 X la N w 1 (X.inc wL (w k)) (mem_one X la N w k) := by
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_sfr, Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, ← Algebra.smul_def]
  rfl

theorem sfr_zero : sfr X la w 0 = 1 := by
  apply Subtype.ext
  rw [coe_sfr, frac_apply, pow_one, section_mul_inverse_eq_one]
  rfl



set_option maxHeartbeats 1000000 in
theorem countQAt_of_trdeg_le {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (htr : Algebra.trdeg B.KO Ω ≤ WeightFamilies.dimY D j) : CurveLoc.CountQAt X la N w gF := by
  by_cases h0 : ∃ a, gF (X.inc wL (w a)) ≠ 0
  · obtain ⟨a, ha⟩ := h0
    exact CurveLoc.countQAt_of X la N w gF (fun i => gF (X.inc wL (w i))) (fun _ => rfl)
      ⟨a, ha, (trdeg_le_of_injective (IntermediateField.val _) Subtype.val_injective).trans htr⟩
  · intro 𝔮 h𝔮 _ hK
    exfalso
    push Not at h0
    refine h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← sfr_zero X la N w, sfr_eq_sum X la N w 0]
    refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hK ?_)
    rw [RingHom.mem_ker, CurveLoc.phiZ_fraction_base, h0, map_zero, zero_mul]

end Rec



set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem countQAtSt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), CountQAtSt h j hj hG hT := by
  intro D T h j hj hG hT ka wL wF G S g0 la _ Z
  exact countQAt_of_trdeg_le (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    ((GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj).2 Z).le

end GlobalTheory.SecCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveModelExistsAllPrimesAllPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CurveRecord

theorem ev_ne_zero_of_nonZeroComp {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    {wF wL : WeightFamilies.Wt D j} (g0 : B.Cusp j wF) (hg : X.NonZeroComp wF g0) (Z : ι) (g : B.Cusp j wL)
    (h1 : gF Z (X.inc wL g) ≠ 0) (h2 : ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0) : gF Z (X.inc wF g0) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul wF wL g0 g
  have hz : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases e : Z' = Z
    · subst e
      rw [h0, zero_mul]
    · rw [h2 Z' e, mul_zero]
  have hg0 : g = 0 := hg wL g (by rw [hH, hz, map_zero])
  exact h1 (by rw [hg0, map_zero, map_zero])

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)


include hT in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem evC_ne_zero (hV : GenValInjSt h j hG) (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) (g0 : (recB h.toLawsCore).Cusp j wF)
    (hg : (recPlus h j hj).NonZeroComp wF g0) (Z : Comp (T.Q.Xo j) T.Q.c) :
    evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0 := by
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, h1, h2⟩ := split_of h j hj hG hT hC G Z k
  have := ev_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z)
    (fun u F hF => hV u F fun Z => (formsEvR_inc h j hj hG hT Z u F).symm.trans (hF Z)) g0 hg Z g
    (fun h0 => hk ((formsEvR_inc h j hj hG hT Z wL (G.w k)).symm.trans (h1.symm.trans h0))) h2
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z wF g0).trans h0)

end Inst


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem curveInst : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), GenValInjSt h j hG → CompSplitSt h j hG → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → CurveInstSt h j hj := by
  intro D T h j hj hG hT hV hC hB
  haveI : Finite (Comp (T.Q.Xo j) T.Q.c) := CompFin.finite_comp _ _
  letI : Fintype (Comp (T.Q.Xo j) T.Q.c) := Fintype.ofFinite _
  obtain ⟨hfg, htr⟩ := GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj
  have hQ := countQAtSt_holds h j hj hG hT
  have hinj : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ f : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Z, phiI h j hj hG hT la G Z f = 0) → f = 0 :=
    fun ka wL wF G S g0 la _ f hf => curveInj h j hj hG hT hV G la f hf
  have hone := hone_of h j hj hG hT hC
  have hloc : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a := by
    intro ka wL wF G S g0 la hH Z r
    exact CurveLoc.loc_of_bir (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
      (birAt_of h j hj hG hT G (hB ka wL wF G hH.2.1) Z) (hQ ka wL wF G S g0 la hH Z) r
  have hS1 := finite_reduced_section h j hj hG hT hfg htr
  refine curveInst_of h j hj hG hT hinj hone hloc hS1 ?_ ?_
  · intro ka wL wF G S g0 la hH e w' θ hw hθ
    have h1 := LocalUnitReduction.finRed (Kp (recPlus h j hj) la G.N) ↥(Frac0 (recPlus h j hj) la G.w)
      (Jid (recPlus h j hj) la G.w) (Comp (T.Q.Xo j) T.Q.c)
      (fun Z => RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (fun Z => phiI h j hj hG hT la G Z) (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
      (hloc _ _ _ G S g0 la hH) (hS1 _ _ _ G S g0 la hH)
    exact unit_ideal_cusp_form_record h j hj hG hT G la g0 θ hw (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
      (hloc _ _ _ G S g0 la hH) h1.1 (evC_ne_zero h j hj hG hT hV hC G hH.2.1 g0 hH.2.2.2) hθ
  · intro ka wL wF G S g0 la hH
    exact nonzero_divisor_cusp_form_record h j hj hG hT G la g0 (hinj _ _ _ G S g0 la hH)
      (evC_ne_zero h j hj hG hT hV hC G hH.2.1 g0 hH.2.2.2)

end GlobalTheory.CurveRecord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.GaussValuationDensityGenerationLocalisationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_valuation_density_generation_localisation : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (ψ : Kp X la N →+* U), (∀ a : Op X la N, v (ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ a)) ≤ 1) → v (ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ (unifO X la N))) < 1 → (∀ (f : B.KO →+* U), (∀ a, f a = ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) → ∀ p : MvPolynomial (Idx D j N) B.KO, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) → v (MvPolynomial.eval₂ f (fun q => ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N q))) p) = 1) ∧ (∀ (c : X.Ol la) (γ : WithZero (Multiplicative ℤ)), γ ≠ 0 → ∃ a : B.KO, v (ψ (algebraMap (X.Ol la) (Kp X la N) c) - ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) < γ) ∧ ∀ S : Subfield U, (∀ c : X.Ol la, ψ (algebraMap (X.Ol la) (Kp X la N) c) ∈ S) → (∀ q, ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N q)) ∈ S) → ∀ c : Kp X la N, ψ c ∈ S := by
  first | exact @GlobalTheory.GaussVal.gauss_dense_gen | exact GlobalTheory.GaussVal.gauss_dense_gen | (intros; apply GlobalTheory.GaussVal.gauss_dense_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralElementsGenericLinearSectionGaussPointStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_elements_generic_linear_section_gauss_point : ∀ (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω] (f : Ω →+* U) (D N : ℕ), Algebra.trdeg K Ω = D → ∀ (v : Valuation U (WithZero (Multiplicative ℤ))) (t : Fin (D + 1) × Fin N → U) (x : Fin N → Ω), (∃ k, x k ≠ 0) → (∀ i : Fin D, ∑ k, t (i.succ, k) * f (x k) = 0) → (∀ p, v (t p) ≤ 1) → (∀ p : MvPolynomial (Fin (D + 1) × Fin N) K, (∀ α, v (f (algebraMap K Ω (p.coeff α))) ≤ 1) → (∃ α, v (f (algebraMap K Ω (p.coeff α))) = 1) → v (MvPolynomial.eval₂ (f.comp (algebraMap K Ω)) t p) = 1) → ∀ g ∈ Subfield.closure (Set.range f ∪ Set.range t), v g ≤ 1 → ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range t), ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range t), v d = 1 ∧ g * d = a := by
  first | exact @GlobalTheory.GaussSection.integral_elements | exact GlobalTheory.GaussSection.integral_elements | (intros; apply GlobalTheory.GaussSection.integral_elements <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionRatiosIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Reg


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem section_ratios_integral : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → Nonempty (CurveModel (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g0) → GenericSectionMinimumIntegral (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la := by
  intro D T h j hj hG _ ka wL wF G S g0 la _ _ _ _ _
  exact Formalism.L2.Pj.GenericSectionMinimum.generic_section_minimum_integral (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SubalgebraEqIntegralClosureOfValuesResiduesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subalgebra_eq_integralClosure_of_values_residues : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] (ϖ : O), IsUnif A ϖ → ∀ [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)] [Module.Finite O ↥(As O A)] (C : Subalgebra O A), C ≤ As O A → (∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, ord ϖ ζ c = (((n ζ : ℕ) : ℤ) : WithTop ℤ)) → (∀ (ζ : Pts O A), ∀ b ∈ As O A, ∃ c ∈ C, ∃ d ∈ C, ord ϖ ζ d = 0 ∧ 0 < ord ϖ ζ (d * b - c)) → As O A ≤ C := by
  first | exact @GlobalTheory.LocStructNak.as_le_of_val_of_residue | exact GlobalTheory.LocStructNak.as_le_of_val_of_residue | (intros; apply GlobalTheory.LocStructNak.as_le_of_val_of_residue <;> assumption)
end

