module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralLinearOfDensityEqSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentComplexSectionValuesOfInt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.IndepCx

theorem finiteType_int {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have h1 : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).FiniteType :=
    (p.finiteType_appLE (isAffineOpen_top _) hU _).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have := hX.finite
  have h0 : (algebraMap ℤ k).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h2 := h1.comp h0
  rw [RingHom.ext_int ((ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).comp (algebraMap ℤ k)) (algebraMap ℤ Γ(X, U))] at h2
  exact RingHom.finiteType_algebraMap.1 h2

end GlobalTheory.HSAmp.IndepCx

namespace GlobalTheory.HSAmp


open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
theorem linearIndependent_vals : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (ι : Type) [Fintype ι] (f : ι → X.functionField),
    (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → ∀ c : ι → ℂ,
    (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∑ i, c i * val P a b σ y (f i) = 0) → c = 0 := by
  intro k _ X _ p D hX P a b ι _ f hf hli c hc
  classical
  obtain ⟨i, hi⟩ := exists_chart P.L.isLB (genericPoint X)
  obtain ⟨j, hj⟩ := exists_chart P.A.isLB (genericPoint X)
  obtain ⟨U, hU, hgU, hle⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X)
    (U := P.L.B.U i ⊓ P.A.B.U j) ⟨hi, hj⟩
  have hl : U ≤ P.L.B.U i := fun x hx => (hle hx).1
  have hr : U ≤ P.A.B.U j := fun x hx => (hle hx).2
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have : CharZero Γ(X, U) :=
    ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero
  have := IndepCx.finiteType_int hX hU
  choose g hg using fun l => exists_fnOf_eq hgU fun x hx => hf l x i j (hl hx) (hr hx)
  have hu0 : (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (P.r i).ne_zero) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hloc : ∀ l, P.loc a b (f l) i j = f l * ((P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b) :=
    fun l => by simp only [Pair.loc]; ring
  have hgli : LinearIndependent ℤ g := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro n hn
    apply hli n
    have h1 := congrArg (fnOf U hgU) hn
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h1
    simp only [map_zsmul, hg, hloc] at h1
    have h2 : (∑ l, n l • f l) * ((P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b) = 0 := by
      rw [Finset.sum_mul]; simpa only [smul_mul_assoc] using h1
    exact (mul_eq_zero.1 h2).resolve_right hu0
  set e := Fintype.equivFin ι
  obtain ⟨x, hx⟩ := GlobalTheory.CxPointsSep.exists_det_ne_zero Γ(X, U) (Fintype.card ι) (g ∘ e.symm)
    (hgli.comp _ e.symm.injective)
  have key : ∀ s, ∑ l, c l * x s (g l) = 0 := by
    intro s
    have hy : ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl) ∈ ptsIn p ((x s).comp (algX p U)) U :=
      ofHom_mem hU _ _
    obtain ⟨θ, hθ, hval⟩ := _root_.GlobalTheory.HSAmp.val_frame k X p P a b _ _ i j (ptsIn_mono hl hy) (ptsIn_mono hr hy)
    have h0 := hc _ (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl))
    have hθ0 : θ ≠ 0 := by
      intro h; rw [h, norm_zero] at hθ; exact zero_ne_one hθ
    set E : ℂ := ((Real.exp (-(a * (P.L.φ ((x s).comp (algX p U))).φ i
      (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl)) +
      b * (P.A.φ ((x s).comp (algX p U))).φ j (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl))) / 2) : ℝ) : ℂ)
      with hEdef
    have hE : E ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    have hv : ∀ l, val P a b _ (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl)) (f l) =
        θ * E * x s (g l) := by
      intro l
      rw [hval (f l) (hf l), ← hg l, ratVal_fnOf hy hgU, ev_ofHom]
      ring
    simp only [hv] at h0
    have h3 : θ * E * ∑ l, c l * x s (g l) = 0 := by
      rw [Finset.mul_sum, ← h0]
      exact Finset.sum_congr rfl fun l _ => by ring
    exact (mul_eq_zero.1 h3).resolve_left (mul_ne_zero hθ0 hE)
  have hM : Matrix.mulVec (Matrix.of fun s t => x s ((g ∘ e.symm) t)) (c ∘ e.symm) = 0 := by
    funext s
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp_apply, Pi.zero_apply]
    rw [← key s, ← e.symm.sum_comp (fun l => c l * x s (g l))]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hx hM
  funext l
  simpa using congrFun hz (e l)

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearRelationMixedDensitiesIntegrals
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ENNReal
set_option autoImplicit false
noncomputable section

theorem GlobalTheory.Mix.part_eq_zero_off_charts {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (ε : ℤˣ) {S : Set (CxPts p σ)} (hS : MeasurableSet S)
    (h : ∀ c : AlgChart p σ D, Disjoint c.e.source S) : part L ε S = 0 := by
  have key : part L ε ≤ (part L ε).restrict Sᶜ := iSup_le fun c => by
    have e : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) S = 0 := by
      rw [chartMeas_apply _ _ hS, (h c).inter_eq, image_empty, Measure.restrict_empty,
        lintegral_zero_measure]
    rw [← Measure.restrict_eq_self_of_ae_mem (s := Sᶜ) (compl_mem_ae_iff.2 e)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart p σ D =>
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) c)
  refine le_antisymm ((key S).trans_eq ?_) zero_le
  rw [Measure.restrict_apply hS, inter_compl_self, measure_empty]

theorem GlobalTheory.Mix.sum_int_eq_zero_of_dens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (J : Type) [Fintype J] (a : J → ℝ) (L : J → Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ∑ i, a i * dens (L i) c y = 0) → ∀ f : CxPts p σ → ℝ, (∀ i, Intg (L i) f) → ∑ i, a i * Mix.int (L i) f = 0 := by
  intro k _ X p σ _ D J _ a N hlin g hint
  classical
  set P : J → ℤˣ → Measure (CxPts p σ) := fun j ε => part (N j) ε with hPdef
  let ap : J → ℝ := fun j => max (a j) 0
  let an : J → ℝ := fun j => max (-a j) 0
  let μ : (J → ℝ) → (J → ℝ) → Measure (CxPts p σ) := fun u w =>
    ∑ j, (ENNReal.ofReal (u j) • P j 1 + ENNReal.ofReal (w j) • P j (-1))

  have hcont : ∀ j (c : AlgChart p σ D), ContinuousOn (fun v => dens (N j) c (c.e.symm v)) c.e.target :=
    fun j c => (_root_.GlobalTheory.Mix.continuousOn_dens k X p σ D (N j) c).comp c.e.continuousOn_symm c.e.mapsTo_symm

  have hchart : ∀ (u w : J → ℝ) (c : AlgChart p σ D) (A : Set (CxPts p σ)), MeasurableSet A → A ⊆ c.e.source →
      μ u w A = ∫⁻ v in c.e '' A, ∑ j, (ENNReal.ofReal (u j) * ENNReal.ofReal (1 * dens (N j) c (c.e.symm v)) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * dens (N j) c (c.e.symm v))) := by
    intro u w c A hA hAc
    have hsub : c.e '' A ⊆ c.e.target := fun _ ⟨y, hy, e⟩ => e ▸ c.e.map_source (hAc hy)
    have hm : ∀ j (s : ℝ), AEMeasurable (fun v => ENNReal.ofReal (s * dens (N j) c (c.e.symm v)))
        (volume.restrict (c.e '' A)) := fun j s =>
      ((((hcont j c).aemeasurable c.e.open_target.measurableSet).const_mul s).ennreal_ofReal).mono_measure
        (Measure.restrict_mono hsub le_rfl)
    have hP : ∀ j (ε : ℤˣ), P j ε A = ∫⁻ v in c.e '' A, ENNReal.ofReal ((ε : ℤ) * dens (N j) c (c.e.symm v)) :=
      fun j ε => _root_.GlobalTheory.Mix.part_apply k X p σ D (N j) ε c A hA hAc
    have hm2 : ∀ j ∈ (Finset.univ : Finset J), AEMeasurable (fun v =>
        ENNReal.ofReal (u j) * ENNReal.ofReal (1 * dens (N j) c (c.e.symm v)) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * dens (N j) c (c.e.symm v))) (volume.restrict (c.e '' A)) :=
      fun j _ => ((hm j 1).const_mul _).add ((hm j (-1)).const_mul _)
    rw [lintegral_finsetSum' _ hm2]
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lintegral_add_left' ((hm j 1).const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hP, hP]
    simp

  set U : Set (CxPts p σ) := ⋃ c : AlgChart p σ D, c.e.source with hUdef
  have hUo : IsOpen U := isOpen_iUnion fun c => c.e.open_source
  have hzero : ∀ u w : J → ℝ, μ u w Uᶜ = 0 := by
    intro u w
    have h0 : ∀ j (ε : ℤˣ), P j ε Uᶜ = 0 := fun j ε =>
      GlobalTheory.Mix.part_eq_zero_off_charts (N j) ε hUo.measurableSet.compl fun c =>
        Set.disjoint_compl_right_iff_subset.2 (Set.subset_iUnion (fun c : AlgChart p σ D => c.e.source) c)
    simp [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply, Measure.smul_apply, h0]

  have hbal : μ ap an = μ an ap := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun c : AlgChart p σ D => c.e.source)
      fun c => c.e.open_source
    let s : Option (AlgChart p σ D) → Set (CxPts p σ) := fun o => o.elim Uᶜ fun c => c.e.source
    refine Measure.ext_of_biUnion_eq_univ (S := insert none (some '' T)) (s := s) ((hTc.image _).insert _) ?_ ?_
    · refine Set.eq_univ_of_forall fun y => ?_
      by_cases hy : y ∈ U
      · rw [hUdef, ← hT] at hy
        obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.1 hy
        exact Set.mem_iUnion₂.2 ⟨some c, Set.mem_insert_of_mem _ ⟨c, hc, rfl⟩, hyc⟩
      · exact Set.mem_iUnion₂.2 ⟨none, Set.mem_insert _ _, hy⟩
    · rintro (_ | c) -
      · show (μ ap an).restrict Uᶜ = (μ an ap).restrict Uᶜ
        rw [Measure.restrict_eq_zero.2 (hzero _ _), Measure.restrict_eq_zero.2 (hzero _ _)]
      · show (μ ap an).restrict c.e.source = (μ an ap).restrict c.e.source
        ext B hB
        have hBs := hB.inter c.e.open_source.measurableSet
        rw [Measure.restrict_apply hB, Measure.restrict_apply hB, hchart _ _ c _ hBs Set.inter_subset_right,
          hchart _ _ c _ hBs Set.inter_subset_right]
        refine setLIntegral_congr_fun (GlobalTheory.ChartGlue.measurableSet_image _ hBs Set.inter_subset_right) fun v hv => ?_
        obtain ⟨y, hy, rfl⟩ := hv
        have h0 := hlin c (c.e.symm (c.e y)) (c.e.map_target (c.e.map_source hy.2))
        have := GlobalTheory.GoodMetric.ChernLin.ofReal_balance a fun j => dens (N j) c (c.e.symm (c.e y))
        rw [h0, mul_zero, mul_zero, ENNReal.ofReal_zero, zero_add, zero_add] at this
        exact this.symm

  have hI : ∀ u w : J → ℝ, (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ w j) → ∫ y, g y ∂μ u w =
      ∑ j, (u j * ∫ y, g y ∂P j 1 + w j * ∫ y, g y ∂P j (-1)) := by
    intro u w hu hw
    simp only [μ]
    rw [integral_finsetSum_measure fun j _ => ((hint j).1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((hint j).2.smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add_measure ((hint j).1.smul_measure ENNReal.ofReal_ne_top)
      ((hint j).2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (hu j), ENNReal.toReal_ofReal (hw j), smul_eq_mul, smul_eq_mul]
  have e := congrArg (fun m : Measure (CxPts p σ) => ∫ y, g y ∂m) hbal
  rw [hI _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _),
    hI _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _)] at e
  have key : ∑ j, a j * Mix.int (N j) g =
      ∑ j, (ap j * ∫ y, g y ∂P j 1 + an j * ∫ y, g y ∂P j (-1)) -
      ∑ j, (an j * ∫ y, g y ∂P j 1 + ap j * ∫ y, g y ∂P j (-1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have ha : ap j - an j = a j := GlobalTheory.GoodMetric.ChernLin.max_sub_max_neg (a j)
    rw [Mix.int]
    simp only [P]
    linear_combination (-(∫ y, g y ∂part (N j) 1) + ∫ y, g y ∂part (N j) (-1)) * ha
  rw [key, e, sub_self]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralSectionsExtendOverFiniteModificat
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

private theorem secK_extend_locInt {X X' Y Z : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (l : Y ⟶ X')
    (α : Y ⟶ X) (e : l ≫ f = α) {k : ℕ} (σ : SecK L f k) (s : SecK L α k) (j' : Fin 1 → L.ι)
    (hσ : (l.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') =
      (Y.presheaf.map (homOfLE (extLI_le_wchart L f l α e j')).op).hom (s.f j'))
    (p' : Z ⟶ Y) (z : Z) (hz : (p' ≫ l) z ∈ LB.wchart L (K := Fin 1) (fun _ => f) j') :
    gs (p' ≫ l) z (LB.wchart L (K := Fin 1) (fun _ => f) j') (σ.f j') =
      gs p' z (LB.wchart L (K := Fin 1) (fun _ => α) j') (s.f j') := by
  have hz' : p' z ∈ LB.wchart L (K := Fin 1) (fun _ => α) j' := extLI_le_wchart L f l α e j' hz
  unfold gs
  rw [dite_eq_left hz, dite_eq_left hz']
  calc _ = (p'.stalkMap z).hom (Y.presheaf.germ (l ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j') (p' z) hz
          ((l.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j'))) :=
        (Scheme.Hom.germ_stalkMap_apply p' _ z hz _).symm
    _ = (p'.stalkMap z).hom (Y.presheaf.germ (l ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j') (p' z) hz
          ((Y.presheaf.map (homOfLE (extLI_le_wchart L f l α e j')).op).hom (s.f j'))) := by rw [hσ]
    _ = (p'.stalkMap z).hom (Y.presheaf.germ (LB.wchart L (K := Fin 1) (fun _ => α) j') (p' z) hz' (s.f j')) := by
        congr 1
        exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    _ = _ := Scheme.Hom.germ_stalkMap_apply p' _ z hz' _

theorem extend_locInt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (I : Type) [Finite I] (k : I → ℕ) (s : ∀ i, SecK L α (k i)), (∀ i, LocInt M G L α t hpb.w (s i)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h ∧ M'.gp ≫ h = M.gp ∧ h ≫ M.π = M'.π ∧ ∀ i, ∃ σ : SecK L (pullback.fst G.hom h) (k i), Agree L σ (s i) := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb I _ k s hs
  obtain ⟨n, j, W, U, hcov, hWj, hWU, hWaff, hUaff⟩ := _root_.GlobalTheory.Mum.exists_finite_affine_chart_cover R M G hqc L hL
  have key : ∀ (i : I) (b : Fin n), ∃ (nn : ℕ) (c : Fin nn → Γ(G.left, W b))
      (bb : Fin nn → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U b)),
      (∀ m, (M.gp.app (U b)).hom.IsIntegralElem (bb m)) ∧
      (Y.presheaf.map (homOfLE (locInt_le_chart L α (j b) (W b) (hWj b))).op).hom ((s i).f (fun _ => j b)) =
        ∑ m, (α.app (W b)).hom (c m) *
          (t.appLE (M.gp ⁻¹ᵁ U b) (α ⁻¹ᵁ W b) (locInt_le_gen G.hom α t M.gp hpb.w (W b) (U b) (hWU b))).hom (bb m) :=
    fun i b => hs i (j b) (W b) (U b) (hWj b) (hWU b) (hWaff b) (hUaff b)
  choose nn c bb hint heq using key
  let Ix := Σ (p : I × Fin n), Fin (nn p.1 p.2)
  let e : Ix ≃ Fin (Nat.card Ix) := Finite.equivFin Ix
  obtain ⟨M', h, hgp, hfin, hπ, hlift⟩ := _root_.GlobalTheory.Mum.finiteModif_regular R M (Nat.card Ix) (fun q => U (e.symm q).1.2)
    (fun q => bb (e.symm q).1.1 (e.symm q).1.2 (e.symm q).2) (fun q => hUaff _) (fun q => hint _ _ _)
  have hlift' : ∀ x : Ix, ∃ cc : Γ(M'.S, h ⁻¹ᵁ U x.1.2),
      (M'.gp.appLE (h ⁻¹ᵁ U x.1.2) (M.gp ⁻¹ᵁ U x.1.2) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U x.1.2))).hom cc =
        bb x.1.1 x.1.2 x.2 := by
    intro x
    have hx := hlift (e x)
    rw [Equiv.symm_apply_apply] at hx
    exact hx
  choose cc hcc using hlift'
  refine ⟨M', h, hfin, hgp, hπ, fun i => ?_⟩
  obtain ⟨l, hl1, hl2⟩ : ∃ l : Y ⟶ pullback G.hom h,
      l ≫ pullback.fst G.hom h = α ∧ l ≫ pullback.snd G.hom h = t ≫ M'.gp :=
    ⟨pullback.lift α (t ≫ M'.gp) (by rw [hpb.w, Category.assoc, hgp]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have hout : IsPullback (l ≫ pullback.fst G.hom h) t G.hom (M'.gp ≫ h) := by
    rw [hl1, hgp]; exact hpb
  have hpb' : IsPullback l t (pullback.snd G.hom h) M'.gp :=
    IsPullback.of_right hout hl2 (IsPullback.of_hasPullback G.hom h)
  haveI := hsm
  haveI : Flat G.hom := inferInstance
  have hflat : Flat (pullback.snd G.hom h) := inferInstance
  have hinj := _root_.GlobalTheory.Mum.genFib_app_injective (FractionRing R) (pullback.snd G.hom h) M'.gp l t hpb' hflat M'.integral M'.dominant
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_pulledBackPowerSection_of_local_lifts L (pullback.fst G.hom h) l α hl1 (k i) hinj (s i) n j
    (fun b => pullback.fst G.hom h ⁻¹ᵁ W b) ((pullback.fst G.hom h).iSup_preimage_eq_top hcov)
    (fun b => extLI_preimage_mono _ (hWj b)) (fun b => by
      obtain ⟨y, hy⟩ := _root_.GlobalTheory.Mum.exists_app_eq_sum_mul_of_comm G.hom h M.gp M'.gp hgp (pullback.fst G.hom h) (pullback.snd G.hom h)
        pullback.condition α t hpb.w l hl1 hl2 (W b) (U b) (hWU b) (nn i b) (c i b) (bb i b)
        (fun m => cc ⟨(i, b), m⟩) (fun m => hcc ⟨(i, b), m⟩)
      refine ⟨y, hy.trans ?_⟩
      rw [← heq i b]
      exact extLI_res_res _ _ _ _)
  refine ⟨σ, ?_⟩
  intro Z p p' hp z J hJ
  have hp2 : p ≫ pullback.snd G.hom h = p' ≫ t ≫ M'.gp := by
    have := _root_.GlobalTheory.Mum.finite_modif_eq_gp R M M' h hfin hgp Z (p ≫ pullback.snd G.hom h) (p' ≫ t) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hp, Category.assoc, hpb.w, Category.assoc])
    rw [this, Category.assoc]
  have hpl : p = p' ≫ l := pullback.hom_ext (by rw [hp, Category.assoc, hl1]) (by rw [hp2, Category.assoc, hl2])
  subst hpl
  unfold sval
  simp only []
  rw [Category.assoc, hl1]
  have hJ' : ∀ ψ : Z ⟶ G.left, ψ z ∈ L.U (J ψ) := hJ
  have hz : (p' ≫ l) z ∈ LB.wchart L (K := Fin 1) (fun _ => pullback.fst G.hom h) (fun _ => J (p' ≫ α)) := by
    unfold LB.wchart
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    intro _
    convert hJ' (p' ≫ α) using 1
    rw [← hl1]
    simp
  exact secK_extend_locInt L (pullback.fst G.hom h) l α hl1 σ (s i) _ (hσ _) p' z hz

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLatticePointsQuadraticBallEstimate
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem log_ellCount_near : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ R : ℝ), 0 ≤ ρ → 0 < R → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → 2 * Fintype.card ι * ρ ≤ R → {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧ |Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ Fintype.card ι * Real.log 2 := by
  intro ι _ _ A hA T ρ R hρ hR hT hTz hRρ
  set n : ℕ := Fintype.card ι with hn
  set s : ℝ := n * ρ with hs
  have hs0 : 0 ≤ s := by positivity
  have hsR : s ≤ R / 2 := by rw [hs]; linarith
  have hnear := exists_int_near_of_closure_short ι A hA T ρ hρ hT hTz
  have hup := ellCount_volume ι A hA s R hs0 hR.le hnear
  have hlo := (ellCount_volume ι A hA s (R - s) hs0 (by linarith) hnear).2.1
  rw [sub_add_cancel] at hlo
  refine ⟨hup.1, ?_⟩
  obtain ⟨-, hω0, hωt⟩ := volume_ellipsoid ι A hA 0 le_rfl
  set ω : ENNReal := volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} with hω
  have hVr : ∀ r : ℝ, 0 ≤ r → (volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r ^ 2}).toReal
      = r ^ n / Real.sqrt A.det * ω.toReal := by
    intro r hr
    rw [(volume_ellipsoid ι A hA r hr).1, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hVfin : ∀ r : ℝ, 0 ≤ r → volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r ^ 2} ≠ ⊤ := by
    intro r hr
    rw [(volume_ellipsoid ι A hA r hr).1]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωt.ne
  have hmono : ∀ r r' : ℝ, 0 ≤ r → r ≤ r' → volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r ^ 2}
      ≤ volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r' ^ 2} := by
    intro r r' hr hrr
    apply measure_mono
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    nlinarith
  have hlo' := (hmono (R / 2) (R - s) (by positivity) (by linarith)).trans hlo
  have hup' := hup.2.2.trans (hmono (R + s) (2 * R) (by linarith) (by linarith))
  have hloR : (R / 2) ^ n / Real.sqrt A.det * ω.toReal ≤ (ellCount A R : ℝ) := by
    rw [← hVr _ (by positivity)]
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hlo'
    simpa using this
  have hupR : (ellCount A R : ℝ) ≤ (2 * R) ^ n / Real.sqrt A.det * ω.toReal := by
    rw [← hVr _ (by positivity)]
    have := ENNReal.toReal_mono (hVfin _ (by positivity)) hup'
    simpa using this
  have hdet := hA.det_pos
  have hωr : 0 < ω.toReal := ENNReal.toReal_pos hω0.ne' hωt.ne
  set K : ℝ := ω.toReal / Real.sqrt A.det with hK
  have hK0 : 0 < K := by positivity
  have hlogK : Real.log K = Real.log ω.toReal - Real.log A.det / 2 := by
    rw [hK, Real.log_div hωr.ne' (Real.sqrt_pos.2 hdet).ne', Real.log_sqrt hdet.le]
  have e1 : (R / 2) ^ n / Real.sqrt A.det * ω.toReal = (R / 2) ^ n * K := by rw [hK]; ring
  have e2 : (2 * R) ^ n / Real.sqrt A.det * ω.toReal = (2 * R) ^ n * K := by rw [hK]; ring
  rw [e1] at hloR
  rw [e2] at hupR
  have hp1 : 0 < (R / 2) ^ n * K := by positivity
  have hc : 0 < (ellCount A R : ℝ) := hp1.trans_le hloR
  have l1 := Real.log_le_log hp1 hloR
  have l2 := Real.log_le_log hc hupR
  rw [Real.log_mul (by positivity) hK0.ne', Real.log_pow, Real.log_div hR.ne' two_ne_zero] at l1
  rw [Real.log_mul (by positivity) hK0.ne', Real.log_pow, Real.log_mul two_ne_zero hR.ne'] at l2
  rw [mul_sub] at l1
  rw [mul_add] at l2
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorPairingFactorInclusionPeriodsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorPairing_factorInclusion_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.Mum.pairing_factor | exact GlobalTheory.Mum.pairing_factor | (intros; apply GlobalTheory.Mum.pairing_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianSchemeDescendsFiniteTypeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarised_abelian_scheme_descends_finite_type : ∀ (B : Type) [CommRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ (B₀ : Subring B) (A₀ : Over (Sp B₀)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left), Algebra.FiniteType ℤ B₀ ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap B₀.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) ∧ (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) ∧ LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) ∧ Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  first | (exact @GlobalTheory.PolModel.polarised_descends) | (exact GlobalTheory.PolModel.polarised_descends) | (intros; apply GlobalTheory.PolModel.polarised_descends  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField), f ∈ P.H a b → ∀ i j, ContinuousOn (ratVal (q := p) (σ := σ) (P.loc a b f i j)) (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) ∧ ∀ (D : ℕ) (c : AlgChart p σ D), DifferentiableOn ℂ (fun v => ratVal (P.loc a b f i j) (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j))) := by
  first | exact @GlobalTheory.HSAmp.loc_continuousOn_holo | exact GlobalTheory.HSAmp.loc_continuousOn_holo | (intros; apply GlobalTheory.HSAmp.loc_continuousOn_holo <;> assumption)
end

