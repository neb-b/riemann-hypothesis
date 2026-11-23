module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericP
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

noncomputable section

namespace GlobalTheory.MixNull

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.ChernNull

theorem chart_null_dom {k : Type} [CommRing k] [IsDomain k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (σ : k →+* ℂ) (hσ : Function.Injective σ) {D : ℕ} {Z : Set X} (hZ : IsClosed Z)
    (hgen : genericPoint X ∉ Z) (c : AlgChart p σ D) :
    volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · simp [hs]
  have hne : (c.U : Set X).Nonempty := ⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩
  haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩
  obtain ⟨g, hg0, hgZ⟩ := exists_sec_vanish c.affine hne hZ hgen
  obtain ⟨Q, hQ, r, hQr⟩ := exists_poly_dvd _ c.etale g hg0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ hσ (by rw [e, map_zero]))
  refine measure_mono_null ?_ (volume_poly_zero D _ hP)
  rintro _ ⟨y, ⟨hys, hyZ⟩, rfl⟩
  have hyU := c.source_subset hys
  have hgy : ev p σ c.U g y = 0 := by
    by_contra hne'
    exact hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun a => c.e y a) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq y hys]
  have := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at this
  show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy,
    zero_mul]

theorem part_compl_null : ∀ (k : Type) [CommRing k] [IsDomain k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (U : X.Opens), genericPoint X ∈ U → part L ε (ptsIn p σ U)ᶜ = 0 := by
  intro k _ _ X _ p σ hσ _ D L ε U hU
  have hZ : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have hgen : genericPoint X ∉ (U : Set X)ᶜ := fun h => h hU
  exact GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl
    fun c => by
      have e : (ptsIn p σ U)ᶜ = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} := by
        ext y
        simp [mem_ptsIn]
      rw [e]
      exact chart_null_dom σ hσ hZ hgen c

end GlobalTheory.MixNull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProj
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open ReciprocityTheory.L2DbarEstimates (V cHess)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem MLine.Isom.hess_eq {L M : MLine p σ} (h : L.Isom M) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) {a : M.B.ι} {b : L.B.ι} (ha : y ∈ ptsIn p σ (M.B.U a)) (hb : y ∈ ptsIn p σ (L.B.U b)) :
    c.hess M.φ a y = c.hess L.φ b y := by
  obtain ⟨w, -, h⟩ := h
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U a ⊓ L.B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo _ (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (M.B.U a ⊓ L.B.U b),
      (ev p σ _ (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 :=
    fun v hv => ev_ne_zero hv.2 (w.s _).isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (L.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ _ (w.s (a, b)).val ∘ c.e.symm) v‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext a b
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 a b
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [h _ _ _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem dens_congr_isom {L M : Fin D → MLine p σ} (h : ∀ i, (L i).Isom (M i)) (c : AlgChart p σ D)
    {y : CxPts p σ} (hy : y ∈ c.e.source) : dens L c y = dens M c y := by
  have e (i : Fin D) := (h i).hess_eq c hy (mem_pick (M i).φ.isLB y) (mem_pick (L i).φ.isLB y)
  simp only [dens, e]

theorem part_congr_isom {L M : Fin D → MLine p σ} (h : ∀ i, (L i).Isom (M i)) (ε : ℤˣ) :
    part L ε = part M ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun ?_ ?_
  · exact measurableSet_image c.e (c.e.open_source.measurableSet.inter hS) inter_subset_left
  · rintro _ ⟨y, hy, rfl⟩
    simp only [c.e.left_inv hy.1, dens_congr_isom h c hy.1]

theorem part_eq_of_isom : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L M : Fin D → MLine p σ), (∀ i, (L i).Isom (M i)) → ∀ ε : ℤˣ, part L ε = part M ε :=
  fun _ _ _ _ _ _ _ _ _ h ε => part_congr_isom h ε

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureNegEqZeroSemiPosi
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

section
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexOrder ComplexConjugate

theorem cHess_posSemidef_of_levi {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    (cHess n (fun v => ((f v : ℝ) : ℂ)) x).PosSemidef := by
  classical
  set g : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hg
  have hg2 : ContDiffAt ℝ 2 g x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  have hgc : (fun w => conj (g w)) = g := funext fun w => by simp [g]
  have hH : (cHess n g x).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show conj (wd n k (wdb n j g) x) = wd n j (wdb n k g) x
    have h1 : (fun w => conj (wdb n j g w)) = wd n j g := by
      funext w
      rw [← ChartWirtingerDerivatives.wd_conj' n j g w, hgc]
    rw [← ChartWirtingerDerivatives.wdb_conj' n k (wdb n j g) x, h1, comm_wd_wdb g x hg2 j k]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  have hre : dotProduct (star y) (Matrix.mulVec (cHess n g x) y) = leviV n g x (fun k => conj (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self y
  refine Complex.le_def.2 ⟨?_, ?_⟩
  · rw [hre]; exact hL _
  · simpa using him.symm

theorem re_sum_perm_det_nonneg {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    0 ≤ (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det).re := by
  have h := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hA).2
  have h0 : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have e : (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det) =
      ((D.factorial : ℝ) : ℂ) * ReciprocityTheory.AnForm.mdisc A := by
    rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm, Complex.ofReal_natCast, ← mul_assoc, mul_one_div_cancel h0, one_mul]
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _) h

end

theorem dens_nonneg_of_semiPosReg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {L : Fin D → MLine p σ} (h : ∀ i, (L i).φ.SemiPosReg D) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : 0 ≤ dens L c y :=
  mul_nonneg (by positivity) (re_sum_perm_det_nonneg (fun i => c.hess (L i).φ (pick (L i).φ.isLB y) y) fun i =>
    cHess_posSemidef_of_levi ((L i).cInf.contDiffAt c hy (mem_pick _ y)) (h i _ c y ⟨hy, mem_pick _ y⟩))

theorem part_neg_eq_zero_of_semiPosReg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → part L (-1) = 0 := by
  intro k _ X p σ _ D L h
  refine le_antisymm (iSup_le fun c => le_of_eq (Measure.measure_univ_eq_zero.1 ?_)) bot_le
  rw [chartMeas_apply _ _ MeasurableSet.univ, inter_univ, c.e.image_source_eq_target]
  refine setLIntegral_eq_zero c.e.open_target.measurableSet fun v hv => ?_
  have := dens_nonneg_of_semiPosReg h c (c.e.map_target hv)
  exact ENNReal.ofReal_eq_zero.2 (by simpa using this)

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSectionValueProductExpansionTerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix
namespace GlobalTheory.Mum.Two.Mix
open GlobalTheory.UT.MixedConv

theorem val_mixed_eval : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), Act D₁ D₂ b h g g' → ∀ (j j' : ℕ) (w : Frm D₂ F j g'.b) (w' : Frm D₁ F j' g.b) (χ : D₂.X) (δ : D₁.X) (u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ)), Nrm u → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' δ) (y y' : F), MixedConv.IsCoefB j g' w χ f y → MixedConv.IsCoefB j' g w' δ f' y' → ∀ (z : (TF (R := R) F).left) (J), Good (JN D₁ D₂) z J → sval f (g.b.left ≫ b.left) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J * val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J)).val = cst F z (y * y') * (rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s (h χ + δ)) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹).val := by
  intro R _ _ D₁ D₂ F _ _ b h g g' hg j j' w w' χ δ u hu f f' y y' hy hy' z J hJ
  have h₁ : Good D₁.P.L z (rl J) := (isPart_inl D₁.P.L D₂.P.L).good hJ
  have h₂ : Good D₂.P.L z (rr J) := (isPart_inr D₁.P.L D₂.P.L).good hJ
  have c₂ : val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J) =
      th D₁ z (rl J) (cP D₁ _ (h χ)) (cP D₁ _ δ) g.b := by
    refine (val_cub D₁.cub g.b h₁ _ _ _).trans ?_
    rw [comp_cP, comp_cP, Category.comp_id]
  have c₃ := gt_mul (𝟙 (TF (R := R) F)) h₁ g (h χ) δ
  have c₄ := hy z (rr J) h₂
  have c₅ := hy' z (rl J) h₁
  have c₆ : g.b.left ≫ b.left = g'.b.left := (congrArg (fun q => q.left) hg.1).symm
  have c₉ := hg.2 χ u hu z J hJ
  rw [Category.id_comp, Over.id_left] at c₃
  rw [c₉, CoefBasic.cst_eq] at c₄
  rw [CoefBasic.cst_eq] at c₅
  rw [c₂, c₆, CoefBasic.cst_eq, map_mul, eq_comm, Units.val_mul, ← _root_.mul_assoc, Units.mul_inv_eq_iff_eq_mul]
  have c₇ := congrArg Units.val c₃
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c₄ c₅ c₇ ⊢
  have c₈ := congrArg₂ (· * ·) c₄ c₅
  linear_combination c₈ - sval f (Over.Hom.left g'.b) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J).val *
    (val w (𝟙 _) z (rr J)).val * (val w' (𝟙 _) z (rl J)).val * c₇

end GlobalTheory.Mum.Two.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialsDifferByUnitsPositiveBoundaryCombinatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
namespace GlobalTheory.TInj

theorem coneval : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (r m N n : ℕ), 1 ≤ n → ∀ (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin r → ℤ)) (s₁ s₂ : (Fin m ⊕ Fin N) → V) (ga : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)), (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → (∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (a) (b))) → ∃ c₁ c₂ : Fin m → ℕ, (∀ k, 0 < c₁ k) ∧ (∀ k, 0 < c₂ k) ∧ ∑ k, c₁ k • ε (.inl k) = ∑ k, c₂ k • pull ga.toLinearMap (ε (.inl k)) := by
  intro V _ _ _ r m N n hn ε s₁ s₂ ga h1m h1u h2m h2u hprod
  classical
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  let ℓ : FractionRing V → ℤ := fun x => WithZero.log (v x)
  have hinj := IsFractionRing.injective V (FractionRing V)
  have hne : ∀ x : V, x ≠ 0 → algebraMap V (FractionRing V) x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ hinj).2 hx
  have hv0 : ∀ x : FractionRing V, x ≠ 0 → v x ≠ 0 := fun x hx => (Valuation.ne_zero_iff v).2 hx
  have ℓmul : ∀ x y : FractionRing V, x ≠ 0 → y ≠ 0 → ℓ (x * y) = ℓ x + ℓ y := fun x y hx hy => by
    simp only [ℓ, map_mul, WithZero.log_mul (hv0 x hx) (hv0 y hy)]
  have ℓzpow : ∀ (x : FractionRing V) (z : ℤ), ℓ (x ^ z) = z * ℓ x := fun x z => by
    simp only [ℓ, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  have ℓprod : ∀ (J : Type) (t : Finset J) (g : J → FractionRing V), (∀ i, g i ≠ 0) →
      ℓ (∏ i ∈ t, g i) = ∑ i ∈ t, ℓ (g i) := by
    intro J t g hg
    induction t using Finset.induction_on with
    | empty => simp [ℓ]
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ℓmul _ _ (hg j)
        (Finset.prod_ne_zero_iff.2 fun i _ => hg i), ih]
  have hunit : ∀ x : V, IsUnit x → ℓ (algebraMap V (FractionRing V) x) = 0 := by
    intro x hx
    have h1 : v (algebraMap V (FractionRing V) x) = 1 := by
      refine le_antisymm (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ x) ?_
      by_contra hlt
      have := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal V) x).1 (lt_of_not_ge hlt)
      exact (IsLocalRing.mem_maximalIdeal x).1 this hx
    simp only [ℓ, h1, WithZero.log_one]
  have hneg : ∀ x : V, x ∈ maximalIdeal V → x ≠ 0 → ℓ (algebraMap V (FractionRing V) x) < 0 := by
    intro x hm hx
    have h1 : v (algebraMap V (FractionRing V) x) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal V) x).2 hm
    have := (WithZero.log_lt_log (hv0 _ (hne x hx)) one_ne_zero).2 h1
    simpa [ℓ, WithZero.log_one] using this
  have hs0 : ∀ (s : (Fin m ⊕ Fin N) → V), (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) →
      (∀ k, IsUnit (s (.inr k))) → ∀ i, algebraMap V (FractionRing V) (s i) ≠ 0 := by
    intro s hm hu i
    rcases i with k | k
    · exact hne _ (hm k).2
    · exact hne _ (hu k).ne_zero
  have hsum : ∀ (s : (Fin m ⊕ Fin N) → V), (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) →
      (∀ k, IsUnit (s (.inr k))) → ∀ z : (Fin m ⊕ Fin N) → ℤ,
      ℓ (∏ i, algebraMap V (FractionRing V) (s i) ^ z i) =
        ∑ k, z (.inl k) * ℓ (algebraMap V (FractionRing V) (s (.inl k))) := by
    intro s hm hu z
    rw [ℓprod _ _ _ (fun i => zpow_ne_zero _ (hs0 s hm hu i)), Fintype.sum_sum_type]
    simp only [ℓzpow, hunit _ (hu _), mul_zero, Finset.sum_const_zero, add_zero]
  let c₁ : Fin m → ℕ := fun k => (-ℓ (algebraMap V (FractionRing V) (s₁ (.inl k)))).toNat
  let c₂ : Fin m → ℕ := fun k => (-ℓ (algebraMap V (FractionRing V) (s₂ (.inl k)))).toNat
  have hc₁ : ∀ k, (c₁ k : ℤ) = -ℓ (algebraMap V (FractionRing V) (s₁ (.inl k))) := fun k => by
    have := hneg _ (h1m k).1 (h1m k).2
    simp only [c₁]; omega
  have hc₂ : ∀ k, (c₂ k : ℤ) = -ℓ (algebraMap V (FractionRing V) (s₂ (.inl k))) := fun k => by
    have := hneg _ (h2m k).1 (h2m k).2
    simp only [c₂]; omega
  refine ⟨c₁, c₂, fun k => ?_, fun k => ?_, ?_⟩
  · have := hc₁ k; have := hneg _ (h1m k).1 (h1m k).2; omega
  · have := hc₂ k; have := hneg _ (h2m k).1 (h2m k).2; omega
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  obtain ⟨u, hu⟩ := hprod a b
  have key := congrArg ℓ hu
  rw [ℓmul _ _ (hne _ u.ne_zero) (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hs0 s₁ h1m h1u i)),
    hunit _ u.isUnit, zero_add, hsum s₂ h2m h2u, hsum s₁ h1m h1u] at key
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, nsmul_eq_mul]
  beta_reduce at key
  have key' : (n:ℤ) * ∑ k, ((c₂ k : ℤ) * ε (.inl k) (ga a) (ga b)) = (n:ℤ) * ∑ k, ((c₁ k:ℤ) * ε (.inl k) a b) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      Finset.sum_congr rfl (fun k _ => show (n:ℤ) * ((c₂ k : ℤ) * ε (.inl k) (ga a) (ga b)) = -((n:ℤ) * ε (.inl k) (ga a) (ga b) * ℓ (algebraMap V (FractionRing V) (s₂ (.inl k)))) by rw [hc₂]; ring),
      Finset.sum_congr rfl (fun k _ => show (n:ℤ) * ((c₁ k : ℤ) * ε (.inl k) a b) = -((n:ℤ) * ε (.inl k) a b * ℓ (algebraMap V (FractionRing V) (s₁ (.inl k)))) by rw [hc₁]; ring),
      Finset.sum_neg_distrib, Finset.sum_neg_distrib, key]
  have := (mul_left_cancel₀ hn' key').symm
  exact this

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbacksDifferByUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicationPullbacks_differ_by_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    u.IsGen →
    ∀ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    uG.IsGen → ∀ (b : W) (σ' : H0 T.U.LG.L 1) (σ : SecK C.P.L.L T.β 1), T.Carries b σ' σ →
    ∀ (σ₂ : SecK C.P.L.L T.β (m ^ 2)) (σ'' : H0 T.U.LG.L (m ^ 2)),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
      sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) →
    ∃ v : Wˣ, T.Carries (b * v) σ'' σ₂ := by
  first | exact @GlobalTheory.Mum.Trait.carries_mulPull | exact GlobalTheory.Mum.Trait.carries_mulPull | (intros; apply GlobalTheory.Mum.Trait.carries_mulPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCrystalPairingSwapEqNegFlip
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pairing_swap_eq_neg_flip : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → AbDual.IsCorrForm (dp0 R) (𝟙 _) B A (AbDual.swap P) (-φ.flip) := by
  intro R _ A B _ _ P _ φ H
  exact SymmPoincare.isCorrForm_swap H

end GlobalTheory
end

