module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2541
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsPullbackMetricFlagRefinement
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem contDiffOn_holoMap {n d : ℕ} {U : Set (V n)} (hU : IsOpen U) {p : V n → V d}
    (hp : DifferentiableOn ℂ p U) : ContDiffOn ℂ ∞ p U := by
  rw [contDiffOn_piLp]
  intro i
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ U hU
    ((EuclideanSpace.proj i : V d →L[ℂ] ℂ).differentiable.comp_differentiableOn hp)

theorem pull_chern_of_eventually {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n)
    (A' : HolAtlas M' n') {r : Type} [Fintype r] [DecidableEq r] {f : M' → M} (hf : A.IsHolo A' f) (G : M → Matrix r r ℂ)
    (G' T : M' → Matrix r r ℂ) (p : A'.Pt) (c : A.ι) (hc : f p.pt ∈ (A.e c).source) (hG : SmoothUnitAt A G (f p.pt))
    (hT : HolUnitAt A' T p.pt) (h : ∀ᶠ z in 𝓝 p.pt, G' z = T z * G (f z) * (T z)ᴴ) (j : ℕ) :
    pull (fderiv ℂ (A.e c ∘ f ∘ p.ch.symm) p.crd) (A.chern G j ⟨(c, f p.pt), hc⟩ : Alt n) = (A'.chern G' j p : Alt n') := by
  have hp : p.pt ∈ p.ch.source := p.2
  have hinv : p.ch.symm p.crd = p.pt := p.ch.left_inv hp
  have hU : IsOpen (p.ch.target ∩ p.ch.symm ⁻¹' (f ⁻¹' (A.e c).source)) :=
    p.ch.isOpen_inter_preimage_symm ((A.e c).open_source.preimage hf.1)
  have hmem : p.crd ∈ p.ch.target ∩ p.ch.symm ⁻¹' (f ⁻¹' (A.e c).source) :=
    ⟨p.ch.map_source hp, by rw [Set.mem_preimage, hinv]; exact hc⟩
  set ψ : V n' → V n := A.e c ∘ f ∘ p.ch.symm with hψ
  have hs : ContDiffAt ℂ ∞ ψ p.crd := (contDiffOn_holoMap hU (hf.2 p.1.1 c)).contDiffAt (hU.mem_nhds hmem)
  have hv : ψ p.crd = A.e c (f p.pt) := by simp only [hψ, Function.comp_apply, hinv]
  have hg : MContDiffAt ∞ (fun u => G ((A.e c).symm u)) (ψ p.crd) := hv ▸ (hG.2 c hc).self_of_nhds
  have hu : IsUnit (G ((A.e c).symm (ψ p.crd))).det := by rw [hv, (A.e c).left_inv hc]; exact hG.1
  have h1 := ((_root_.GlobalTheory.ChernCalc.curv_pow_chern_comp_holo n n' r (fun u => G ((A.e c).symm u)) ψ p.crd (hs.of_le (by norm_cast)) hg hu).2 j).2
  have hg' : MContDiffAt ∞ (fun x => G ((A.e c).symm (ψ x))) p.crd := fun a b =>
    (hg a b).comp p.crd (hs.restrict_scalars ℝ)
  have hTu : IsUnit (T (p.ch.symm p.crd)).det := by rw [hinv]; exact hT.1
  have hTd := hT.2 p.1.1 hp
  have ht : Tendsto p.ch.symm (𝓝 p.crd) (𝓝 p.pt) := by
    have := p.ch.continuousAt_symm (p.ch.map_source hp)
    rwa [ContinuousAt, p.ch.left_inv hp] at this
  have he : ∀ᶠ x in 𝓝 p.crd, G' (p.ch.symm x) =
      T (p.ch.symm x) * G ((A.e c).symm (ψ x)) * (T (p.ch.symm x))ᴴ := by
    filter_upwards [ht.eventually h, hU.mem_nhds hmem] with x hx hx'
    rw [hx]
    simp only [hψ, Function.comp_apply]
    rw [(A.e c).left_inv hx'.2]
  have h2 := (_root_.GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame n' r _ _ (fun x => G' (p.ch.symm x)) (fun x => G' (p.ch.symm x)) (fun x => T (p.ch.symm x))
    (fun x => T (p.ch.symm x)) (fun x => T (p.ch.symm x)) p.crd hg' hu hg' hu hTd hTu hTd hTu hTd hTu
    (he.mono fun x hx => ⟨hx, hx⟩) j).2.1
  show pull _ (chernAt _ (A.e c (f p.pt)) j : Alt n) = (chernAt (fun v => G' (p.ch.symm v)) p.crd j : Alt n')
  rw [h2, h1, hv]

theorem pullback_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ x : ι × ℕ, (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) (fld (atlas X σ) (chernF E H x)) = fld (atlas Y σ) (chernF E' (pullGram E H φ f hf) x) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH x
  funext p
  have hol := _root_.GlobalTheory.ChernCalc.ptMap_isHolo F σ X Y f hf
  have hE := _root_.GlobalTheory.ChernCalc.pullGram_eq_of_frame F σ X Y ι m E E' φ f hf hR H hH
  have hA := (E.nonempty (under (ptMap σ f hf p.pt))).choose_spec
  have hB := (E'.nonempty (under p.pt)).choose_spec
  have hP := hR.sub (under p.pt) _ hB _ (by
    have := hA
    exact (congrArg (fun w => (E.nonempty (under (ptMap σ f hf p.pt))).choose ∈ E.S w) (hE p.pt).1).mp this) x.1
  refine pull_chern_of_eventually (atlas X σ) (atlas Y σ) hol (gramAt E H x.1 (ptMap σ f hf p.pt))
    (gramAt E' (pullGram E H φ f hf) x.1 p.pt)
    (fun z => (((E'.nonempty (under p.pt)).choose *
      (Mat.map (E.nonempty (under (ptMap σ f hf p.pt))).choose φ)⁻¹) x.1).map (ratVal · z)) p _ _
    (_root_.GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) _ _ hA x.1).1
    (_root_.GlobalTheory.ChernCalc.holUnitAt_ratVal F σ Y _ _ p.pt (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)) ?_ x.2
  filter_upwards [(hol.1.tendsto p.pt).eventually (_root_.GlobalTheory.ChernCalc.frame_eventually_near F σ X ι m 0 E _ _ hA),
    _root_.GlobalTheory.ChernCalc.frame_eventually_near F σ Y ι m m E' _ _ hB] with z h1 h2
  exact (hE z).2 _ ((congrArg (fun w => (E.nonempty (under (ptMap σ f hf p.pt))).choose ∈ E.S w) (hE z).1).mp h1) _ h2 x.1

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopFormSignedMeasureEqAtlasPart
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

open GlobalTheory.ChartGlue

namespace GlobalTheory.ChernCalc

theorem chartMeas_congr_source {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {n : ℕ}
    (e : OpenPartialHomeomorph Y (V n)) {ρ ρ' : Y → ENNReal} (h : ∀ y ∈ e.source, ρ y = ρ' y) :
    chartMeas e ρ = chartMeas e ρ' := by
  unfold chartMeas
  congr 1
  refine withDensity_congr_ae ?_
  refine (ae_restrict_iff' e.open_target.measurableSet).2 (Eventually.of_forall fun v hv => ?_)
  exact h _ (e.map_target hv)

theorem chernTopPart_eq_part : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), ∀ (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ), chernTopPart E H R ε = (atlas X σ).part (evalF (atlas X σ) (chernF E H) R) ε := by
  intro F _ σ X ι m E H R ε
  unfold chernTopPart HolAtlas.part glueMeas
  refine iSup_congr fun c => chartMeas_congr_source _ fun y hy => ?_
  have hx : (atlas X σ).loc (evalF (atlas X σ) (chernF E H) R) c (c.e y) =
      evalF (atlas X σ) (chernF E H) R ⟨(c, y), hy⟩ :=
    HolAtlas.loc_crd (atlas X σ) (evalF (atlas X σ) (chernF E H) R) ⟨(c, y), hy⟩
  show ENNReal.ofReal (_ * chernTop _ _ _) = ENNReal.ofReal (_ * (dens ((atlas X σ).loc _ c (c.e y))).re)
  rw [hx]
  congr 2
  exact (_root_.GlobalTheory.ChernCalc.dens_chernAt_re X.dim ι m R (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y)).symm

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormHolomorphicPullback
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

noncomputable section
namespace GlobalTheory.ChernCalc

theorem eq_sum_ofLp_smul_complexCoordinateVector {n : ℕ} (w : V n) : w = ∑ a, w a • coordVec a := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem trace_mul_constMatrix_mul_evenForms_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (P Q : Matrix r r (Ev n)) (C : Matrix r r ℂ) :
    (((P * C.map (algebraMap ℂ (Ev n)) * Q).trace : Ev n) : Alt n) = ∑ p, ∑ q, C p q • (((Q * P) q p : Ev n) : Alt n) := by
  rw [Matrix.trace_mul_cycle, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply (M := Q * P), Matrix.map_apply, AddSubmonoidClass.coe_finsetSum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [mul_comm, ← Algebra.smul_def, Subalgebra.coe_smul]

def connectionMatrixDifferenceLinearMap {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n) :
    V n →ₗ[ℂ] Matrix r r ℂ where
  toFun ξ := conn G v ξ - conn G' v ξ
  map_add' ξ ξ' := by rw [conn_add_vec, conn_add_vec]; abel
  map_smul' c ξ := by rw [conn_smul_vec, conn_smul_vec, smul_sub]; rfl

theorem transAt_comp_holo : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ∀ k, transAt (fun x => G (φ x)) (fun x => G' (φ x)) w k = pull (fderiv ℂ φ w) (transAt G G' (φ w) k) := by
  intro n n' r _ _ G G' φ w hφ hG hGu hG' hG'u k
  have hI := (_root_.GlobalTheory.ChernCalc.curv_pow_chern_comp_holo n n' r G' φ w hφ hG' hG'u).1
  have hφ1 : DifferentiableAt ℂ φ w := hφ.differentiableAt two_ne_zero
  have h1 : MContDiffAt 1 G (φ w) := hG.of_le (by exact_mod_cast le_top)
  have h1' : MContDiffAt 1 G' (φ w) := hG'.of_le (by exact_mod_cast le_top)
  have hc : ∀ ξ, conn (fun x => G (φ x)) w ξ - conn (fun x => G' (φ x)) w ξ =
      ∑ b, fderiv ℂ φ w ξ b • connectionMatrixDifferenceLinearMap G G' (φ w) (coordVec b) := by
    intro ξ
    rw [conn_comp_holo h1 hφ1, conn_comp_holo h1' hφ1]
    show connectionMatrixDifferenceLinearMap G G' (φ w) (fderiv ℂ φ w ξ) = _
    conv_lhs => rw [eq_sum_ofLp_smul_complexCoordinateVector (fderiv ℂ φ w ξ)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]
  have hd : ∀ b, conn G (φ w) (coordVec b) - conn G' (φ w) (coordVec b) = connectionMatrixDifferenceLinearMap G G' (φ w) (coordVec b) :=
    fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [transAt, hc, hd, map_sum, map_mul, (pull_dz _ _).1, trace_mul_constMatrix_mul_evenForms_sum, AlgHom.map_smul_of_tower]
  simp only [hI _ _ _ _ G hG hGu, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, Finset.smul_sum]
  conv_lhs => enter [2, a, 2, i, 2, p]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, b]; rw [Finset.sum_comm]

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreThetaSectionGermEqFourierRatioMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mum.FibreGerm.secGerm_eq_secRatio_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (ψ : Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0) ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ _ ψ) → ∀ (k N : ℕ) (α : Fin N → D.toPre.X) (b : ∀ j, D.toPre.SecB k (α j)) (τ : Fin N → SecK D.toPre.P.L Y.q.left k) (F : Fin N → IntFam (maximalIdeal R) D.toPre k) (s : Fin N → H0 U.LG.L k), (∀ j, IsTermOf Y (b j) (τ j)) → (∀ j, (F j).Lead (α j) (b j)) → (∀ j, U.ExpandsAt 0 k (s j) (F j).f) → ∀ (z : (thickObj R (maximalIdeal R) 0 G).left) (j : Fin N) (i : Fin 1 → U.LG.L.ι), ψ.left z ∈ nonzeroLocus (τ j) → (fstG (maximalIdeal R) 0 G).left z ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s l) i = gs (Y := (thickObj R (maximalIdeal R) 0 G).left) ψ.left z (nonzeroLocus (τ j)) (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left z (s j) i := by
  intro R _ _ _ D A G _ _ U Y ψ hP k N α b τ F s hT hL hE z j i hτz hi
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.toPre.P.isLB z
  obtain ⟨c, hc⟩ := GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term R D A G U Y _ (𝟙 _) ψ hP k z J J' hJ hJ'
  have hv : ∀ l, secGerm (fstG (maximalIdeal R) 0 G).left z (s l)
      (fun _ => J ((fstG (maximalIdeal R) 0 G).left ≫ 𝟙 _)) = c.val * sval (τ l) ψ.left z J' := by
    intro l
    have := hc (α l) (b l) (τ l) (F l) (s l) (hT l) (hL l) (hE l)
    rw [Category.id_comp] at this
    exact this
  obtain ⟨a, ha⟩ := exists_unit_secGerm k (fstG (maximalIdeal R) 0 G).left z hi
    (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (fstG (maximalIdeal R) 0 G).left)
  let jt : Fin 1 → D.toPre.P.L.ι := fun _ => J' (ψ.left ≫ Y.q.left)
  have hzt : ψ.left z ∈ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt :=
    hJ'.mem (fun _ : Fin 1 => Y.q.left) ψ.left
  have hzW : ψ.left z ∈ nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt := ⟨hτz, hzt⟩
  have hk : nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt ≤
      (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ))).U jt := inf_le_right
  have ha' : nonzeroLocus (τ j) ⊓ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) jt ≤ nonzeroLocus (τ j) :=
    inf_le_left
  have hu : ∀ l, sval (τ l) ψ.left z J' =
      gs ψ.left z (nonzeroLocus (τ j)) (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) * sval (τ j) ψ.left z J' := by
    intro l
    have e := congrArg (gs ψ.left z _) (GlobalTheory.ProjSpace.secRatio_on (τ j) (τ l) jt ha' hk)
    rw [sval_of (τ l) ψ.left z J' jt (fun _ => rfl), sval_of (τ j) ψ.left z J' jt (fun _ => rfl)]
    exact ((gs_res _ _ hk hzW _).symm.trans e).trans ((gs_mul _ _ _ hzW _ _).trans
      (congrArg₂ (· * ·) (gs_res _ _ ha' hzW _) (gs_res _ _ hk hzW _)))
  have hunit : IsUnit (sval (τ j) ψ.left z J') := by
    obtain ⟨w, hw⟩ := GlobalTheory.ProjSpace.isUnit_resG_sec (τ j) jt ha' hk
    rw [sval_of (τ j) ψ.left z J' jt (fun _ => rfl)]
    have e : gs ψ.left z _ ((τ j).f jt) = (gm ψ.left z _ w).val :=
      (gs_res _ _ hk hzW _).symm.trans ((congrArg (gs ψ.left z _) hw.symm).trans (gs_unit _ _ _ hzW w))
    exact e ▸ Units.isUnit _
  refine ⟨?_, fun l => ?_⟩
  · rw [ha, hv j]
    exact a.isUnit.mul (c.isUnit.mul hunit)
  · rw [ha, ha, hv, hv, hu l]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreTorusCoordinatesIsImmersion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ClosedFibreImm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (ψ : Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0) ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ _ ψ) → IsImmersion ψ.left := by
  intro R _ _ _ D A G _ _ U Y ψ h
  set g := U.gt 0 with hg
  let G₀ := thickObj R (maximalIdeal R) 0 G
  let T : Over (Sp R) := Over.mk (G₀.hom ≫ thick R (maximalIdeal R) 0)
  have hcl : IsClosedImmersion (thick R (maximalIdeal R) 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let T₀ : Over (Sp R) := Over.mk (pullback.fst Y.H.hom (thick R (maximalIdeal R) 0) ≫ Y.H.hom)
  let ξ := Y.Φ T₀ (Over.homMk (pullback.fst Y.H.hom (thick R (maximalIdeal R) 0)) rfl)
  obtain ⟨χ, hχ⟩ := GlobalTheory.TorusCoord.exists_point g (T := T₀) (pullback.snd Y.H.hom (thick R (maximalIdeal R) 0))
    pullback.condition.symm ξ
  let ψ' : G₀.left ⟶ pullback Y.H.hom (thick R (maximalIdeal R) 0) := pullback.lift ψ.left G₀.hom (Over.w ψ)
  have hψ' : ψ' ≫ pullback.fst _ _ = ψ.left := pullback.lift_fst _ _ _

  have hw1 : ψ' ≫ pullback.fst Y.H.hom (thick R (maximalIdeal R) 0) ≫ Y.H.hom = T.hom := by
    rw [← Category.assoc, hψ']; exact Over.w ψ
  let k : T ⟶ T₀ := Over.homMk ψ' hw1
  have hkx : k ≫ (Over.homMk (pullback.fst Y.H.hom (thick R (maximalIdeal R) 0)) rfl : T₀ ⟶ Y.H) = ψ :=
    Over.OverMorphism.ext (by simpa [k] using hψ')
  have hpull := Y.rep.1 T T₀ k (Over.homMk (pullback.fst Y.H.hom (thick R (maximalIdeal R) 0)) rfl)
  rw [hkx] at hpull
  have h1 : GlobalTheory.TorusCoord.IsPointOf g (ψ' ≫ χ) (Y.Φ T ψ) := hχ.pull g hpull
  have e1 : ψ' ≫ χ = 𝟙 _ := h1.unique_left g h
  have hc := hχ.comp_hom g
  have hw2 : χ ≫ T.hom = T₀.hom := hc
  let k' : T₀ ⟶ T := Over.homMk χ hw2
  have hpull' := Y.rep.1 T₀ T k' ψ
  have h2 : GlobalTheory.TorusCoord.IsPointOf g (χ ≫ 𝟙 _) (Y.Φ T₀ (k' ≫ ψ)) := h.pull g hpull'
  rw [Category.comp_id] at h2
  have e2 : Y.Φ T₀ (k' ≫ ψ) = ξ := h2.unique_right g hχ
  have e3 : k' ≫ ψ = Over.homMk (pullback.fst Y.H.hom (thick R (maximalIdeal R) 0)) rfl := (Y.Φ T₀).injective e2
  have e4 : χ ≫ ψ.left = pullback.fst Y.H.hom (thick R (maximalIdeal R) 0) := congrArg (·.left) e3
  have e5 : χ ≫ G₀.hom = pullback.snd Y.H.hom (thick R (maximalIdeal R) 0) := by
    rw [← cancel_mono (thick R (maximalIdeal R) 0), Category.assoc, ← pullback.condition]
    exact hc
  have e6 : χ ≫ ψ' = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hψ', e4, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, e5, Category.id_comp]
  have : IsIso ψ' := ⟨⟨χ, e1, e6⟩⟩
  rw [← hψ']
  infer_instance

end GlobalTheory.Mum.ClosedFibreImm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetFiniteFibresIsAffineFiniteInt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem ringChar_residueField_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    ringChar (X.residueField x) = ringChar (Y.residueField (f x)) := by
  haveI := (RingHom.charP_iff_charP (f.residueFieldMap x).hom (ringChar (Y.residueField (f x)))).1
    (ringChar.charP _)
  exact ringChar.eq _ _

theorem closeds_finite_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (T : Closeds X), (∀ ℓ : ℕ, ((T : Set X) ∩ fib X ℓ).Finite) →
    IsAffine (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧
      Module.Finite ℤ Γ((Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) := by
  intro k _ X _ p D hX T hT
  set I := Scheme.IdealSheafData.vanishingIdeal T with hI
  have hr : Set.range I.subschemeι = (T : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  set q := I.subschemeι ≫ p ≫ spMap (Int.castRingHom k) with hq
  have : IsProper q := by rw [hq]; infer_instance
  have : LocallyQuasiFinite q := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
    have hfin := hT (ringChar ((Sp ℤ).residueField y))
    refine Set.Finite.of_finite_image (f := I.subschemeι) (hfin.subset ?_)
      (I.subschemeι.isClosedEmbedding.injective.injOn)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hr.le ⟨z, rfl⟩, ?_⟩
    show ringChar _ = _
    rw [ringChar_residueField_eq (p ≫ spMap (Int.castRingHom k)) (I.subschemeι z)]
    have e : (p ≫ spMap (Int.castRingHom k)) (I.subschemeι z) = y := by
      rw [← hz, hq]; rfl
    rw [e]
  have : IsFinite q := IsFinite.of_isProper_of_locallyQuasiFinite q
  have hA : IsAffine I.subscheme := isAffine_of_isAffineHom q
  refine ⟨hA, ?_⟩
  have hf : (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).Finite :=
    q.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2)
  rw [RingHom.ext_int (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom)
    (algebraMap ℤ Γ(I.subscheme, ⊤)), RingHom.finite_algebraMap] at hf
  exact hf

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDiagonalMumfordBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagWeil

theorem diag_psum (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (I : Finset (Fin 2)) :
    lift (𝟙 A) (𝟙 A) ≫ psum A (x2 A) I = psum A ![𝟙 A, 𝟙 A] I := by
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl <;>
    simp [psum, padd, pzero, x2, List.finRange_succ]

theorem lbIso_lam_diag (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB) :
    LBIso ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) (cubeLB A ![𝟙 A, 𝟙 A] M) := by
  refine GlobalTheory.PrimNorm.lbIso_nested hM _ _ _ _ _ _ ?_
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [← Over.comp_left, diag_psum]

end GlobalTheory.DiagWeil


open GlobalTheory.TorusRM.DiagFrame in
theorem GlobalTheory.DiagWeil.weilIs_diag_lam : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (N : LB A.left), N.IsLB → LBIso N (cubeLB A ![𝟙 A, 𝟙 A] M) → Out.RelAmple A N → ∀ (k : ℕ) (a b : Fin g → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * (hermForm Hm a b).im : ℝ)) : ℂ) / k) → Out.WeilIs A N k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  intro A _ _ g hA _ M u Hm χ hM hF N hN hNc hamp k a b c hk ha hb hc
  have : IsProper A.hom := hA.proper
  have hL : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB (LB.isLB_linComb hM _ _) _
  have hcube : (cubeLB A ![𝟙 A, 𝟙 A] M).IsLB := LB.isLB_linComb hM _ _
  have hLN : LBIso ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) N :=
    LBIso.trans hL hcube hN (GlobalTheory.DiagWeil.lbIso_lam_diag A hM) hNc.symm
  have hampL : Out.RelAmple A ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.AmpleApprox.relAmple_of_lbIso_self hN hL hLN hamp
  have hF' := isFactorAH_diagUnif u hF
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hampL g (diagUnif u) _ _ hF'.1 hF'.2.1 hF'.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hF' hpos
  have hc' : (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (((a ⬝ᵥ ((2 : ℂ) • Hm).mulVec (star b)).im : ℝ) : ℂ) / k) := by
    rw [hc]
    congr 4
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_im]
    simp [hermForm]
  have hw := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ hL g (diagUnif u) _ _ hAH k a b c hk ha hb hc'
  rw [diagUnif_ex] at hw
  exact GlobalTheory.PELFamily.weilIs_of_lbIso GlobalTheory.globalFns_holds hA hN hL
    (LBIso.trans hN hL (pull_isLB hL _) hLN.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL)) hw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfKillsGeometricTorsionPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_eq_one_of_kills_geometric_torsionPoints : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ), (n : K) ≠ 0 → (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1) → ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ^ n = 1 → x ≫ f.hom = 1 := by
  first | exact @GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts | exact GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts | (intros; apply GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts <;> assumption)
end

