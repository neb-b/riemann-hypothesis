module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0360
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0330
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicSardShiftedFunctionsRegularZerosStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicSard_shifted_functions_regularZeros : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ φ : Fin d → Γ(X, U), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ c ∉ E, ∀ (z : CxPts p (RingHom.id ℂ)) (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
        (∀ j, CxPts.evHom hz (φ j) + c j = 0) →
        RingHom.ker (CxPts.evHom hz) ≤
          Ideal.span (Set.range fun j => φ j + ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (c j)) ⊔ RingHom.ker (CxPts.evHom hz) ^ 2 := by
  first | (exact @GlobalTheory.AlgSard.main) | (exact GlobalTheory.AlgSard.main) | (intros; apply GlobalTheory.AlgSard.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechComparisonDegreeZeroAlternatingPullbackStatement
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechComparison_degreeZero_alternatingPullback : ∀ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V)
    {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
    (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (0 + 1)))
    (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (0 + 1))),
    y.1 = (cechAbPull f τ hτ φ).term (0 + 1) x.1 →
    cechAbHEquivH' hc' hG 0 (cechClass _ 0 y) =
      SheafPull.pull f φ 0 (homOfLE hV) (cechAbHEquivH' hc hF 0 (cechClass _ 0 x)) := by
  first | (exact @GlobalTheory.cechAbPull_degZero) | (exact GlobalTheory.cechAbPull_degZero) | (intros; apply GlobalTheory.cechAbPull_degZero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOrthogonalInvariantProjection
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory.PD.XCover

theorem mem_germ_range_of_mem_rB : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (y : Z.functionField), y ∈ rB ℂ Z.functionField (crd φ) I → ∃ f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i), (Z.presheaf.germ _ (genericPoint Z) h).hom f = y := by
  intro d Z _ p _ inst hinst φ _ _ hgen I hI h y hy
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  have hsc : ∀ r : ℂ, algebraMap ℂ Z.functionField r = (Z.presheaf.germ ⊤ (genericPoint Z) trivial).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) := by
    subst hinst; intro r; rfl
  set U : Z.Opens := I.inf fun i => φ ⁻¹ᵁ chart d i with hU
  have hUa : IsAffineOpen U := (GlobalTheory.T.projective_chart_affine_cover d Z φ).2 I hI
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen Z U hUa
  have halg : ∀ b, algebraMap Γ(Z, U) Z.functionField b = (Z.presheaf.germ U (genericPoint Z) h).hom b := fun _ => rfl
  haveI : IsIntegrallyClosed Γ(Z, U) := by
    have hs := p.smooth_appLE (U := ⊤) (isAffineOpen_top _) hUa (by simp)
    letI := (p.appLE ⊤ U (by simp)).hom.toAlgebra
    haveI : Algebra.Smooth Γ(Sp ℂ, ⊤) Γ(Z, U) := hs
    let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    haveI : IsDomain Γ(Sp ℂ, ⊤) := e.injective.isDomain (e : Γ(Sp ℂ, ⊤) →+* ℂ)
    haveI : IsIntegrallyClosed Γ(Sp ℂ, ⊤) := IsIntegrallyClosed.of_equiv e.symm
    exact isIntegrallyClosed_of_smooth Γ(Sp ℂ, ⊤) Γ(Z, U)
  have hgerm : ∀ a ∈ rA ℂ (crd φ) I, ∃ g : Γ(Z, U),
      (Z.presheaf.germ U (genericPoint Z) h).hom g = ((a : fld φ) : Z.functionField) := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi, j, rfl⟩ := hx
      have hle : U ≤ φ ⁻¹ᵁ chart d i := Finset.inf_le hi
      refine ⟨Z.presheaf.map (homOfLE hle).op (φ.app (chart d i) (ratioSec d i j)), ?_⟩
      rw [Z.presheaf.germ_res_apply]
      have hr := (GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div d Z φ 0 i j (hgen 0) (hgen i)).2
      simp only [IntermediateField.coe_div, crd_val]
      rw [← hr, rat, dite_eq_left (hgen i)]
    | algebraMap r =>
      refine ⟨Z.presheaf.map (homOfLE le_top).op (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), ?_⟩
      rw [Z.presheaf.germ_res_apply]
      exact (hsc r).symm
    | add x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      exact ⟨g + g', by rw [map_add (f := _), hg, hg']; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      exact ⟨g * g', by rw [map_mul, hg, hg']; rfl⟩
  have hy' : IsIntegral (rA ℂ (crd φ) I) y := hy
  have hB : IsIntegral Γ(Z, U) y := by
    obtain ⟨q, hq, hqy⟩ := hy'
    have hl : q.map (algebraMap (rA ℂ (crd φ) I) Z.functionField) ∈
        Polynomial.lifts (algebraMap Γ(Z, U) Z.functionField) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨g, hg⟩ := hgerm _ (q.coeff n).2
      exact ⟨g, by rw [halg, hg]; rfl⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hq.map _)
    refine ⟨Q, hQm, ?_⟩
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map, hqy]
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hB
  exact ⟨b, hb⟩

end GlobalTheory.PD.XCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermChartInterIntegralCoordinateRatiosStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericGerm_chartInter_integral_coordinateRatios : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i)), (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I := by
  first | (exact @GlobalTheory.PD.XCover.germ_mem_rB) | (exact GlobalTheory.PD.XCover.germ_mem_rB) | (intros; apply GlobalTheory.PD.XCover.germ_mem_rB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesAllStepsLtM
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem tieDel_all_steps : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j < D.R.m, S.Del j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos hLaw j hj ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hj1 : j + 1 ≤ D.R.m := hj
  by_cases hne : Nonempty (Lv.comp j) ∧ Nonempty (Lv.comp (j + 1))
  swap
  · refine ⟨1, norm_one, ?_⟩
    intro La _ x c' L' _
    exact absurd ⟨⟨La.1⟩, ⟨c'⟩⟩ hne
  obtain ⟨⟨a⟩, ⟨a'⟩⟩ := hne
  obtain ⟨hn1, -, hsame⟩ := _root_.GlobalTheory.TwV.DelA.cKs_unit_indep S hPos ι hι j hj1 a a'
  set cK := cKs S ι j hj1 a a' with hcK
  refine ⟨cK, hn1, ?_⟩
  obtain ⟨-, -, hrk, hRT⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  have hN := hRT j
  have h1 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := hrk (j + 1)
  obtain ⟨d0⟩ := _root_.GlobalTheory.TwV.DelB.dec_exists S hDict
  intro La hLa x c' L' hL'

  have hQ : K2.SharpQ t ex.tw u μ j x (K2.qOf t ex.tw u μ j x) := by
    have hex := J.sharp j hj x
    unfold K2.qOf
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  set cc := clsAt X H j La.1 La.2 with hcc
  set κ := clsAt X H (j + 1) c' L' with hκ
  set Q := K2.qOf t ex.tw u μ j x with hQdef
  set P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ :=
    ((((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j cc) : ℂˣ) : ℂ) *
          ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) κ) : ℂˣ) : ℂ)) •
          framePol D (t.O u μ).dgen (Q cc) ((t.rd u μ).Th t.seam t.amb j cc κ)) with hP
  have hPw : P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) :=
    Submodule.smul_mem _ _ ((wt_polDY_framePol D (rk_le _ D hN) (t.O u μ).dgen _ (Q cc) (hQ.1 cc)).2 _)
  set φ := K2.entRec t ex.tw u μ j cc x with hφ
  have hφκ : ∀ y, φ κ y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y := by
    intro y
    have e := (_root_.GlobalTheory.TwV.DelA.applyFrame_and_entQFrame).2 D L hT Gi Gl Kc Dx cX ex t u μ j cc (Q cc) κ y
    have e2 : φ κ y = entQ t u μ j cc (Q cc) κ y := rfl
    rw [e2, e, hP, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

  have hR : ∀ d : Dec J std, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj1 h1 (c', L') φ V ∧
      MvPolynomial.map ι V = cK • S.Y.DelF j ((kaAt X H hT).cmp j x La.1 La.2) (srOf S.Y j La (c', L')) := by
    intro d
    obtain ⟨V, hV, hmap⟩ := GlobalTheory.T.transportedFramePolynomial_complex_values_at_point S hPos ι hι d j hj1 h1 (c', L') φ P hPw hφκ
    refine ⟨V, hV, ?_⟩
    rw [hmap]
    obtain ⟨hMove, hOp, hDeg⟩ := GlobalTheory.T.movedForms_operator_degrees_at_kernelSource S hDict hPos ι hι d j hj ⟨a'⟩ hN
    have hEq := GlobalTheory.FrameB.equiv_frame_b S.Y d.fd2 (ltC S.g S.hLT) (GlobalTheory.FrameB.ltC_ne S.hLT)
      ((GlobalTheory.TwV.DelB.frames_invertible S).2 d) j
    have hsc : ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 →
        ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 →
        cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) *
          ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2 := by
      intro La La' _ _
      have e := GlobalTheory.T.unit_mul_sourceScalar_eq_nextLevelScalar S hPos ι hι d j hj1 La La'
      rw [hsame] at e
      exact e
    have hDel := GlobalTheory.T.kernelSite_contractionIdentity_operatorHalf S hDict hPair hPos hLaw d ι hι (fun j => phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j)
      (fun j c' L' => GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j (c', L'))
      (fun j c' L' => scT d S ι j c' L') (sO d ι) (gmS d) j hj cK hN hMove hOp hDeg hEq hsc
    have := hDel La hLa x Q hQ c' L' hL'
    exact this
  obtain ⟨V0, hV0, hm0⟩ := hR d0
  have hall : ∀ d : Dec J std, RealAt d (j + 1) hj1 h1 (c', L') φ V0 := by
    intro d
    obtain ⟨V, hV, hm⟩ := hR d
    have : V = V0 := MvPolynomial.map_injective ι ι.injective (hm.trans hm0.symm)
    exact this ▸ hV
  have hrd := _root_.GlobalTheory.TwV.DelA.rdJ_eq_of_realAt S hDict ι j hj1 h1 (c', L') hL' φ V0 hall
  exact hrd.trans hm0

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModuleCubePullHomTermCommCechDifferentialStatement
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential : ∀ {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
    {σ : R →+* S} {τ : κ → ι} {A : Cube.{0} ι R} {B : Cube.{0} κ S}
    (ψ : Cube.PullHom σ τ A B) (p : ℕ) (x : Cube.Term A p),
    ψ.term (p + 1) (Cube.d A p x) = Cube.d B p (ψ.term p x) := by
  first | (exact @GlobalTheory.Cube.PullHom.term_d) | (exact GlobalTheory.Cube.PullHom.term_d) | (intros; apply GlobalTheory.Cube.PullHom.term_d  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceCechCochainFractionEqSumFibreStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_cechCochain_fraction_eq_sum_fibre : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ (ρ : F →ₗ[k] k), IsRes k x ρ → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), trF k τ ρ (locCoch k K x h Finset.univ) = ∑ᶠ e : fib k K x, e.1 h := by
  first | (exact @GlobalTheory.PD.trF_locCoch_eq_finsum_fib) | (exact GlobalTheory.PD.trF_locCoch_eq_finsum_fib) | (intros; apply GlobalTheory.PD.trF_locCoch_eq_finsum_fib  <;> assumption)
end

