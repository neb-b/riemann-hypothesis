module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2380
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PSpaceDeg

theorem ringKrullDim_eq_one (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ringKrullDim k = 1 := by
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := ℤ) (B := k)
    (algebraMap ℤ k).injective_int]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem isArithVar (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    IsArithVar (PSpace.str k D) D :=
  ProjModel.isArithVar_pspace k (ringKrullDim_eq_one k) D

theorem injective_ringHom {k : Type} [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (ψ : k →+* ℂ) : Function.Injective ψ := by
  refine (RingHom.injective_iff_ker_eq_bot ψ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  change Ideal.comap (algebraMap ℤ k) (RingHom.ker ψ) = ⊥
  rw [RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)

def ringHomEquiv (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] [Field K]
    [Algebra k K] [IsFractionRing k K] : (k →+* ℂ) ≃ (K →+* ℂ) where
  toFun ψ := IsFractionRing.lift (injective_ringHom ψ)
  invFun φ := φ.comp (algebraMap k K)
  left_inv ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom ψ) x
  right_inv φ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors k) (RingHom.ext fun x => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom (φ.comp (algebraMap k K))) x

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem finrank_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    [Field K] [Algebra k K] [IsFractionRing k K] [CharZero K] :
    Module.finrank ℚ K = Module.finrank ℤ k ∧ FiniteDimensional ℚ K := by
  haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  haveI : @IsScalarTower ℤ ℚ K Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid k (nonZeroDivisors ℤ)) K := inferInstance
  let b := Module.Free.chooseBasis ℤ k
  let b' := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  exact ⟨(Module.finrank_eq_card_basis b').trans (Module.finrank_eq_card_basis b).symm,
    Module.Finite.of_basis b'⟩

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem card_ringHom (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    Nat.card (k →+* ℂ) = Module.finrank ℤ k := by
  haveI : CharZero (FractionRing k) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
  obtain ⟨h1, h2⟩ := finrank_fractionRing k (FractionRing k)
  haveI : NumberField (FractionRing k) := ⟨⟩
  rw [Nat.card_congr (ringHomEquiv k (FractionRing k)), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card, h1]

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

open Set
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)

theorem exists_stdChart (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) :
    ∃ (c : AlgChart (PSpace.str k N) σ N) (i : (ProjSpace.hermitianTwistingSheaf k N).B.ι),
      c.e.source = ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) ∧ c.e.target = Set.univ ∧
      c.e.source ⊆ ptsIn (PSpace.str k N) σ ((ProjSpace.hermitianTwistingSheaf k N).B.U i) ∧
      ∀ v, ((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm v) = Real.log (1 + ‖v‖ ^ 2) := by
  obtain ⟨c, h₁, h₂, h₃⟩ := StdProjChart.exists_of_bijective (p := PSpace.str k N) σ
    (ProjSpace.isAffineOpen_chart k N 0) _ (StdProjChart.bijective_ratio k N 0)
  refine ⟨c, (0 : Fin (N + 1)), h₁, h₂, h₁.le, fun v => ?_⟩
  have hv : c.e.symm v ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) :=
    h₁ ▸ c.e.map_target (h₂ ▸ trivial)
  have h := Weight.fsBasis_φ (p := PSpace.str k N) (σ := σ) (ProjSpace.O1_isLB k N)
    (ProjSpace.coord k N) (ProjSpace.iSup_nonzeroLocus_coord k N) 1 (by simp) (0 : Fin (N + 1))
    (c.e.symm v)
  refine h.trans ?_
  have h0 : ev (PSpace.str k N) σ (ProjSpace.chart k N 0) (ProjSpace.ratio k N 0 0)
      (c.e.symm v) = 1 := by
    simp only [ProjSpace.ratio, ProjSpace.ratioOn_self]
    rw [ev_eq hv, map_one]
  have key : ∑ a : Fin (N + 1), ‖ev (PSpace.str k N) σ (ProjSpace.chart k N 0)
      (ProjSpace.ratio k N 0 a) (c.e.symm v)‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
    rw [Fin.sum_univ_succ, h0, EuclideanSpace.norm_sq_eq]
    simp only [Fin.succAbove_zero] at h₃
    simp only [h₃, norm_one, one_pow]
  rw [← key]
  simp [Matrix.one_apply, ev, ProjSpace.O1]

theorem chern_mass_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (N : ℕ) (σ : k →+* ℂ) :
    ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N 1 Set.univ = 1 ∧
      ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N (-1) Set.univ = 0 := by
  have hA := isArithVar k N
  have hproj : IsProjOver (PSpace.str k N) := hA.isProjOver
  haveI : IsIntegral (PSpace k N) := ProjSpace.isIntegral_of_isDomain k N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).IsCInf := (ProjSpace.hermitianTwistingSheaf k N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf k N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := exists_stdChart k σ N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace k N) ∈ ProjSpace.chart k N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace k N)).mem_open_set_iff (ProjSpace.chart k N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := ChernNull.chernPart_over_closed hA ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ
    (ProjSpace.chart k N 0).isOpen.isClosed_compl (by simpa using hgen) σ ((ProjSpace.hermitianTwistingSheaf k N).φ σ) 1
  have hcX : (ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0))ᶜ =
      {y : CxPts (PSpace.str k N) σ | y.1 (IsLocalRing.closedPoint ℂ) ∈
        ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ} := by
    ext y
    simp [mem_ptsIn]
  rw [← hcX, ← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (lintegral_fubiniStudy_density_eq_one N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, FSDet.det_fubiniStudy_hess N v]
  simp

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem degree_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) := by
  have hσ : ∀ σ : k →+* ℂ, ((ProjSpace.hermitianTwistingSheaf k D).φ σ).chernInt D Set.univ (fun _ => 1) = 1 := by
    intro σ
    obtain ⟨h1, h0⟩ := chern_mass_hermitian_O_one_projective k D σ
    rw [GdegPullProof.chernInt_one, h1, h0]
    simp
  haveI : Finite (k →+* ℂ) := by
    haveI : CharZero (FractionRing k) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
    haveI : FiniteDimensional ℚ (FractionRing k) := (finrank_fractionRing k (FractionRing k)).2
    haveI : NumberField (FractionRing k) := ⟨⟩
    exact Finite.of_equiv _ (ringHomEquiv k (FractionRing k)).symm
  haveI := Fintype.ofFinite (k →+* ℂ)
  simp only [gdeg, chInt, hσ]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]

theorem main : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ),
    IsArithVar (PSpace.str k D) D ∧ gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) ∧
      Nat.card (k →+* ℂ) = Module.finrank ℤ k :=
  fun k _ _ _ _ D => ⟨isArithVar k D, degree_hermitian_O_one_projective k D, card_ringHom k⟩

end GlobalTheory.PSpaceDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRigOfOmegaLeRangeRigExtMapVerschiebung
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem range_rigOfOmega_le_range_rigExtMap_verschiebung :
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K),
      LinearMap.range (frobTwist h G).rigOfOmega ≤
        LinearMap.range (rigExtMap (verschiebung h G)) := by
  intro p _ K _ h G
  rintro _ ⟨w, rfl⟩
  obtain ⟨β, w', hβ, hd⟩ :=
    GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung p K h G (-(w.1 1))
  obtain ⟨-, c, B₀, -, hB₀, -, hB₀'⟩ := exists_of_cobOne_eq_zero hβ
  obtain ⟨B, hB⟩ : cocyclesMap (verschiebung h G) c ∈ LinearMap.range (frobTwist h G).cob :=
    (Submodule.Quotient.mk_eq_zero _).1
      (LinearMap.congr_fun (vecExtMap_verschiebung h G) (Submodule.Quotient.mk c))
  have h1 : funsMap (relFrob h G) B - B₀ = 0 := G.eq_zero_of_cob_eq_zero h (by
    rw [map_sub, ← cocyclesMap_cob, hB, hB₀, ← relFrob_comp_verschiebung h G, sub_eq_zero]
    exact Subtype.ext (funext fun _ => (pullTwo_comp _ _ _).symm))
  have h2 : (relFrob h G).app 1 (B.1 1 - β) = 0 := by
    rw [map_sub, ← hB₀']
    exact congrArg (fun z : G.funs => z.1 1) h1
  obtain ⟨w'', hw''⟩ := dUnit_mem_range_of_mem_kerIdeal _
    (_root_.GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero p K _ _ (verschiebung h G) (relFrob h G) (verschiebung_comp_relFrob h G)
      (relFrob_comp_verschiebung h G) _ h2)
  obtain ⟨u, hu⟩ := G.omegaLevel_surjective 1 (w' + w'')
  have h3 : (frobTwist h G).dFun B = omegaMap _ _ (verschiebung h G) u - w :=
    ((frobTwist h G).omegaLevel_one_bijective h).1 (by
      rw [map_sub, omegaLevel_apply, omegaLevel_apply, omegaLevel_apply, omegaMap_val,
        ← omegaLevel_apply, ← omegaLevel_apply _ _ u, hu, map_add, hw'']
      change dUnit (R := K) (B.1 1) = _
      rw [dUnit, dUnit, map_sub, ← dUnit, ← dUnit, hd]
      abel)
  refine ⟨G.rigMk (c, u), ?_⟩
  rw [rigExtMap_mk]
  refine (Submodule.Quotient.eq _).2 ⟨B, Prod.ext ?_ ?_⟩
  · exact hB.trans (sub_zero _).symm
  · exact h3

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedPullbackInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PsiRing GlobalTheory.PrimCocycle

noncomputable section

namespace GlobalTheory.RefPull

open GlobalTheory.HalfBC

theorem refines_pull : ∀ {V V₀ V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₀] [IsDomain V₀] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ₀ : V →+* V₀) (D₀ : DegPre V₀) (e₀ : D₀.X ≃+ Q.X), Function.Injective ρ₀ → Refines Q ρ₀ D₀ e₀ → ∀ (ρ : V₀ →+* V₁) (D₁ : DegPre V₁) (hD : IsPullDeg ρ D₀ D₁), Function.Injective ρ → Refines Q (ρ.comp ρ₀) D₁ (hD.xe.trans e₀) := by
  intro V V₀ V₁ _ _ _ _ _ _ Q ρ₀ D₀ e₀ hρ₀ H ρ D₁ hD hρ
  obtain ⟨β₀, β₂₀, w₀, pb₀, sq₀, gen₀, c₀, tau₀⟩ := H
  have gp := pull_grp hD
  have hΛQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hΛ₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := DVR.linComb_isLB _ D₀.P.isLB _ _
  have hΛ₁ : (abelian₂ D₁.P.A D₁.P.L).IsLB := DVR.linComb_isLB _ D₁.P.isLB _ _
  obtain ⟨w', T⟩ := exists_comp hΛ₀ w₀ (lamIso gp hD.w) ((isGen_iff _).1 gen₀)
    (pgen_lamIso gp hD.w ((isGen_iff _).1 hD.w_gen)) hΛQ hΛ₁
  set β : D₁.P.A.left ⟶ D₀.P.A.left := hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf ρ) with hβ
  let gam : FractionRing V₀ →+* FractionRing V₁ := GlobalTheory.ArcPull.fracMap hρ
  have hgam : ∀ r, gam (algebraMap V₀ _ r) = algebraMap V₁ _ (ρ r) := GlobalTheory.ArcPull.fracMap_algebraMap hρ
  have sgam := gam_comm ρ gam hgam
  obtain ⟨κ₁, hκ₁, hκu⟩ := exists_kappa ρ₀ ρ gam hgam hρ₀
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D₁.P.A).left) (z : Z) J J₁ J', Good Q.M.L z J → Good D₀.P.L z J₁ →
      Good D₁.P.L z J' → lamVal w' p z J J' = lamVal w₀ (p ≫ sqOf gp) z J J₁ *
        ∏ I, gw hD.w (p ≫ lamφ D₁.P.A I) z (J₁ ((p ≫ lamφ D₁.P.A I) ≫ β)) (J' (p ≫ lamφ D₁.P.A I)) ^ lamε I := by
    intro Z p z J J₁ J' hJ hJ₁ hJ'
    have t := T Z p z (fun I => J (p ≫ (sqOf gp ≫ β₂₀) ≫ lamφ Q.B I))
      (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I)) (fun I => J' (p ≫ lamφ D₁.P.A I))
      (Set.mem_iInter.2 fun I => hJ (p ≫ (sqOf gp ≫ β₂₀) ≫ lamφ Q.B I))
      (Set.mem_iInter.2 fun I => hJ₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I))
      (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ D₁.P.A I))
    refine t.trans (congrArg₂ (· * ·) ?_ ?_)
    · show _ = gw w₀ (p ≫ sqOf gp) z (fun I => J ((p ≫ sqOf gp) ≫ β₂₀ ≫ lamφ Q.B I))
        (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I))
      simp only [Category.assoc]
    · rw [gw_lamIso gp hD.w p z _ _ (fun I => by
        have := hJ₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I)
        rw [Category.assoc, sqOf_lamφ, ← Category.assoc] at this ⊢
        exact this) (fun I => hJ' (p ≫ lamφ D₁.P.A I))]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [Category.assoc, sqOf_lamφ, ← Category.assoc]
  refine ⟨β ≫ β₀, sqOf gp ≫ β₂₀, w', ?_, ⟨?_, ?_⟩, (isGen_iff _).2 (T.pgen_comp hΛ₀ ((isGen_iff _).1 gen₀)
    (pgen_lamIso gp hD.w ((isGen_iff _).1 hD.w_gen))), ?_, ?_⟩
  · exact (IsGrpPullback.comp gp pb₀).congr (spMap_comp_spMap' ρ₀ ρ) rfl
  · rw [Category.assoc, sq₀.1, ← Category.assoc, (isSquare_sqOf gp).1, Category.assoc]
  · rw [Category.assoc, sq₀.2, ← Category.assoc, (isSquare_sqOf gp).2, Category.assoc]
  · intro a
    show (D₁.c a).left ≫ β ≫ β₀ = spMap (ρ.comp ρ₀) ≫ (Q.c (e₀ (hD.xe a))).left
    rw [← Category.assoc, hβ, hD.c_pr, Category.assoc, c₀, ← Category.assoc, spMap_comp_spMap']
  · intro κ hκ a b z J J' hJ hJ'
    obtain rfl := hκu κ hκ
    choose J₁ hJ₀ using fun χ : (TK V₁).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (χ z)
    have hJ₁ : Good D₀.P.L z J₁ := hJ₀
    let g₀ : (TK V₁).left ⟶ (TK V₀).left := spMap gam
    have hx : ∀ χ, D₁.xK χ ≫ β = g₀ ≫ D₀.xK (hD.xe χ) := fun χ => by
      show (jK V₁ ≫ (D₁.c χ).left) ≫ β = spMap gam ≫ jK V₀ ≫ (D₀.c (hD.xe χ)).left
      rw [Category.assoc, hβ, hD.c_pr, ← Category.assoc, ← sgam, Category.assoc]
    have hP : (lift (toUnit (TK V₁) ≫ D₁.c a) (toUnit (TK V₁) ≫ D₁.c b)).left ≫ sqOf gp =
        g₀ ≫ (lift (toUnit (TK V₀) ≫ D₀.c (hD.xe a)) (toUnit (TK V₀) ≫ D₀.c (hD.xe b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst D₀.P.A D₀.P.A).left = _ ≫ (fst D₀.P.A D₀.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
          ← Over.comp_left, lift_fst]
        exact hx a
      · show _ ≫ (snd D₀.P.A D₀.P.A).left = _ ≫ (snd D₀.P.A D₀.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
          ← Over.comp_left, lift_snd]
        exact hx b
    have t₁ := tau₀ κ₁ hκ₁ (hD.xe a) (hD.xe b) (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))
      (fun ψ => hJ (g₀ ≫ ψ)) (fun ψ => hJ₁ (g₀ ≫ ψ))
    have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans (map_mul _ _ _)
    have n₁ : val (D₀.tau (hD.xe a) (hD.xe b)) (g₀ ≫ 𝟙 _) z J₁ = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D₀.tau (hD.xe a) (hD.xe b)) (𝟙 _) (g₀ z) (fun ψ => J₁ (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z J₁ hJ₁).2.2.1 _)
    have nQ : val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) (g₀ ≫ κ₁) z J = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) κ₁ (g₀ z) (fun ψ => J (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ κ₁ g₀ z J hJ).2.2.1 _)
    rw [Category.comp_id] at n₁
    have A := n₁.trans (t₂.trans (congrArg₂ (· * ·) (lamVal_comp w₀ g₀ _ z J J₁ hJ hJ₁).symm nQ.symm))
    let h : ((TK V₁).left ⟶ D₁.P.A.left) → ((TK V₁).left.presheaf.stalk z)ˣ :=
      fun q => gw hD.w q z (J₁ (q ≫ β)) (J' q)
    have tv := GlobalTheory.ArcPull.tau_val hD g₀ (𝟙 _) (GlobalTheory.ArcPull.fracMap_sq hρ) hJ₁ hJ' a b
    have K := (key _ (lift (toUnit (TK V₁) ≫ D₁.c a) (toUnit (TK V₁) ≫ D₁.c b)).left z J J₁ J' hJ hJ₁ hJ').trans
      (congrArg₂ (· * ·) (congrArg (fun q => lamVal w₀ q z J J₁) hP)
        (prod_lam (DVR.cP D₁ (TK V₁) a) (DVR.cP D₁ (TK V₁) b) h))
    have o₀ : ∀ x, h (DVR.cP D₁ (TK V₁) x).left = GlobalTheory.ArcPull.om hD.w z J₁ J' (D₁.xK x) := fun _ => rfl
    have o₁ : h (1 : TK V₁ ⟶ D₁.P.A).left = GlobalTheory.ArcPull.om hD.w z J₁ J' (1 : TK V₁ ⟶ D₁.P.A).left := rfl
    rw [← DVR.cPoint_add] at K
    simp only [o₀, o₁] at K
    simp only [Category.id_comp] at tv
    rw [K]
    show _ = _ * val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) (spMap gam ≫ κ₁) z J
    apply Additive.ofMul.injective
    have eA := congrArg Additive.ofMul A
    have eT := congrArg Additive.ofMul tv
    simp only [ofMul_mul, ofMul_inv] at eA eT ⊢
    linear_combination (norm := abel) eA - eT

end GlobalTheory.RefPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReflectionSumJetNumber
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetsCharZero

theorem num_le (dF R N r g0 g1 cst : ℝ) (hR : 0 ≤ R) (hN : 0 ≤ N) (hr : 0 ≤ r) (hg0 : 0 < g0) (hle : g0 ≤ g1)
    (h : R * N ^ 3 * (r * N / 4 + 2 * dF ^ 2) / g0 ≤ cst) : dF ^ 2 * (R * N ^ 3) / g1 ≤ cst := by
  have hX : 0 ≤ R * N ^ 3 := by positivity
  refine le_trans ?_ h
  calc dF ^ 2 * (R * N ^ 3) / g1 ≤ dF ^ 2 * (R * N ^ 3) / g0 := div_le_div_of_nonneg_left (by positivity) hg0 hle
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hg0.le
        have : dF ^ 2 ≤ r * N / 4 + 2 * dF ^ 2 := by nlinarith [sq_nonneg dF, mul_nonneg hr hN]
        nlinarith [mul_le_mul_of_nonneg_left this hX]

theorem exists_thRule_value_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (α : 𝓞 E) (q : ℕ), α * star α = ((q : ℕ) : 𝓞 E) → q ∣ l.M → l.Mb ≤ Ideal.span {star α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → 1 ≤ n → ∀ (N cst : ℝ), ((Module.finrank ℚ E * Dw.q : ℕ) : ℝ) ≤ N → 4 * DF Dw a + 4 ≤ q → (DF Dw a : ℝ) * (2 * Real.sqrt N) < q → (DF Dw a : ℝ) ^ 2 * ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * N ^ 3) / q ≤ cst → ∃ f ∈ thGen Xo c nab a n, evI y f ≠ 0 ∧ (vV T.V (evI y f) : ℝ) ≤ cst * φ := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hch φ hφ α q hα hq hMb a n hanti hs hn N cst hρN h4 hM0 hcst
  obtain ⟨P₁, hP₁, hB⟩ := GlobalTheory.T.exists_harmonicPoly_localInvariant_nonpos_char0 E H Dw l Xo c a n hanti hs
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData E H Dw l Xo c T io y C P ϖ hϖ
  obtain ⟨ρ, hρ, hSB⟩ := GlobalTheory.ShortPhi.exists_shortBasis E H Dw l Xo c T io y φ hφ C P ϖ hϖ Q hQ
  set R : ℝ := |(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E) / (2 * Module.finrank ℚ E) with hR
  have hR0 : 0 ≤ R := by positivity
  have hρN' : (ρ : ℝ) ≤ N := le_trans (by exact_mod_cast hρ) hρN
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := hρ0.trans hρN'
  have hM0' : (DF Dw a : ℝ) * (2 * Real.sqrt ρ) < q := lt_of_le_of_lt (by gcongr) hM0
  have hup := GlobalTheory.T.iInf_thetaRule_le_localValue_charZero E H Dw l Xo c nab hnab T io y C hTr P hP hch ϖ hϖ Q hQ ρ _ _ hSB α q hα hq hMb a n 1 hn one_pos h4
    hM0' P₁ hP₁
  have hloc := hB T io y C hch 1 l.M one_pos
  have hφ0 := hφ.nonneg
  have hq0 : (0 : ℝ) < q := by
    have h : 0 < q := by omega
    exact_mod_cast h
  set B : ℝ := (DF Dw a : ℝ) ^ 2 * (R * (ρ : ℝ) ^ 3 * φ) / q / ((1 : ℕ) : ℝ) with hBdef
  have hBle : B ≤ cst * φ := by
    rw [hBdef, Nat.cast_one, div_one]
    calc (DF Dw a : ℝ) ^ 2 * (R * (ρ : ℝ) ^ 3 * φ) / q ≤ (DF Dw a : ℝ) ^ 2 * (R * N ^ 3 * φ) / q := by gcongr
      _ = (DF Dw a : ℝ) ^ 2 * (R * N ^ 3) / q * φ := by ring
      _ ≤ cst * φ := by gcongr
  have hinf : (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V 1 (evI y f)) ≤
      ((B : ℝ) : EReal) := by
    refine hup.trans ?_
    calc _ ≤ (0 : EReal) + ((B : ℝ) : EReal) := add_le_add hloc le_rfl
      _ = _ := zero_add _
  by_contra hne
  push_neg at hne
  have hlow : (((⌊B⌋ + 1 : ℤ) : ℝ) : EReal) ≤
      ⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V 1 (evI y f) := by
    refine le_iInf₂ fun f ⟨x, hx⟩ => ?_
    have hf : f ∈ thGen Xo c nab a n := ⟨x, P₁, hP₁, hx⟩
    by_cases h0 : evI y f = 0
    · rw [h0, nval_zero]; exact le_top
    have h1 := hne f hf h0
    rw [nval_of_ne h0, Nat.cast_one, div_one, EReal.coe_le_coe_iff]
    have h2 : B < (vV T.V (evI y f) : ℝ) := lt_of_le_of_lt hBle h1
    have h3 : ⌊B⌋ < vV T.V (evI y f) := Int.floor_lt.2 h2
    exact_mod_cast h3
  have h5 := EReal.coe_le_coe_iff.1 (hlow.trans hinf)
  push_cast at h5
  linarith [Int.lt_floor_add_one B]

end GlobalTheory.JetsCharZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLift_galoisTwist_of_conjugatePoint : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  first | exact @GlobalTheory.Mum.Conj.symLift_thTw | exact GlobalTheory.Mum.Conj.symLift_thTw | (intros; apply GlobalTheory.Mum.Conj.symLift_thTw <;> assumption)
end

