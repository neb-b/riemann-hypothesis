module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0039
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0536
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameFormsResidueIndependence
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndepDiscrep

theorem neg_one_lt_formOrd_sub_sum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], topologicalKrullDim Y = n → ∀ (y : Y) (U : Y.Opens) (hy : y ∈ U) (ω : FormsOn q n U), IsFrame ω → ∀ (J : Type) [Fintype J] (a : J → Y.presheaf.stalk y) (ha : ∀ j, a j ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (v : J → Y.functionFieldˣ) (c : J → ℚ), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨a j, ha j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) → (∀ j, (v j : Y.functionField) = algebraMap (Y.presheaf.stalk y) Y.functionField (a j)) → (∀ j, c j < 1) → ∀ E : DivOver q, E.Through y → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) ω) : ℚ) - ∑ j, c j * E.ord (v j) := by
  classical
  intro Y _ _ q n _ hn y U hy ω hω J _ a ha v c hind hv hc E hE
  haveI := SmoothOfRelativeDimension.smooth n q
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.ModifSections.isNormalScheme_of_smooth q
  obtain ⟨U', hy', z, e, he, hze, hz⟩ :=
    GlobalTheory.AdaptedFrame.exists_adapted_frame (p := q) (n := n) y a ha hind
  have h0 : formOf U (gen_mem hy) ω ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hω).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have h0' : formOf U' (gen_mem hy') (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy') hz).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨f, hf⟩ := (isFreeGen_formOf (gen_mem hy') hz).2 (formOf U (gen_mem hy) ω)
  have hf0 : f ≠ 0 := fun h => h0 (by rw [← hf, h]; exact zero_smul _ _)
  set u : Y.functionFieldˣ := Units.mk0 f hf0 with hu
  have hfu : ((u : Y.functionField) • formOf U' (gen_mem hy') (dOn q z)) = formOf U (gen_mem hy) ω :=
    by rw [hu, Units.val_mk0]; exact hf
  have hF (Fd : DivOver q) : Fd.formOrd (formOf U (gen_mem hy) ω) =
      Fd.ord u + Fd.formOrd (formOf U' (gen_mem hy') (dOn q z)) := by
    rw [← Fd.formOrd_smul hn h0' u, hfu]
  have h0z : ∀ w, w ⤳ y → ∀ Fd : DivOver q, Fd.IsAt w → Fd.ord u = 0 := by
    intro w hw Fd hFd
    have h1 := hF Fd
    have a1 := DivOver.formOrd_formOf_eq_zero (hw.mem_open U.isOpen hy) hFd hω
    have a2 := DivOver.formOrd_formOf_eq_zero (hw.mem_open U'.isOpen hy') hFd hz
    rw [a1, a2] at h1
    omega
  have reg : ∀ w : Y.functionFieldˣ,
      (∀ x, x ⤳ y → ∀ Fd : DivOver q, Fd.IsAt x → 0 ≤ Fd.ord w) → 0 ≤ E.ord w := fun w hw =>
    (E.ord_nonneg_iff w).2 (hE _ (regAt_of_forall_coheight_eq_one fun x hx h1 =>
      have ⟨Fd, hFd⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := q) h1
      (hFd _).1 ((Fd.ord_nonneg_iff w).1 (hw x hx Fd hFd))))
  have hu1 := reg u fun x hx Fd hFd => (h0z x hx Fd hFd).ge
  have hu2 := reg u⁻¹ fun x hx Fd hFd => by rw [Fd.ord_inv, h0z x hx Fd hFd, neg_zero]
  rw [E.ord_inv] at hu2
  have hu0 : E.ord u = 0 := by omega
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy' hE z h0' e he v fun j => by
    rw [hv, ← hze j, algebraMap_germ]
  have hN := DivOver.formOrd_formOf_nonneg hn hy' hE (dOn q z) h0'
  have hnn : ∀ j, 0 ≤ E.ord (v j) := fun j => (E.ord_nonneg_iff _).2 (hE _ ⟨a j, (hv j).symm⟩)
  change -1 < (E.formOrd (formOf U (gen_mem hy) ω) : ℚ) - ∑ j, c j * E.ord (v j)
  rw [hF E, hu0, zero_add]
  have hAq : (∑ j, (E.ord (v j) : ℚ)) - 1 ≤ (E.formOrd (formOf U' (gen_mem hy') (dOn q z)) : ℚ) := by
    exact_mod_cast hA
  have hNq : (0 : ℚ) ≤ (E.formOrd (formOf U' (gen_mem hy') (dOn q z)) : ℚ) := by exact_mod_cast hN
  have hle : ∀ j, c j * (E.ord (v j) : ℚ) ≤ E.ord (v j) := fun j => by
    have : (0 : ℚ) ≤ E.ord (v j) := by exact_mod_cast hnn j
    nlinarith [hc j]
  by_cases h : ∃ j, 0 < E.ord (v j)
  · obtain ⟨j, hj⟩ := h
    have hlt : ∑ j, c j * (E.ord (v j) : ℚ) < ∑ j, (E.ord (v j) : ℚ) :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨j, Finset.mem_univ _, by
        have : (0 : ℚ) < E.ord (v j) := by exact_mod_cast hj
        nlinarith [hc j]⟩
    linarith
  · push_neg at h
    have h' : ∀ j, E.ord (v j) = 0 := fun j => le_antisymm (h j) (hnn j)
    simp only [h', Int.cast_zero, mul_zero, Finset.sum_const_zero, sub_zero]
    linarith

end GlobalTheory.IndepDiscrep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffIntegralAlmostAllPrimes
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.CoeffInt

theorem coeff_valuation_le_one_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S,
      ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K (AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.cmPoint_eigenbasis_change_det_integral_almost_all_primes E H Dw l Xo c z f La hz
  have hfin : (⋃ j, {p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K) |
      FractionalIdeal.count z.K p (z.ℓ j).I ≠ 0}).Finite :=
    Set.finite_iUnion fun j => Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (z.ℓ j).I)
  refine ⟨S₁ ∪ hfin.toFinset, fun p hp F hF hv G hG μ => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists,
    not_not] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hgen : ∀ j, Formalism.L2.LamCM.IsLocGen p (1 : z.K) (z.ℓ j).I := fun j =>
    ⟨one_ne_zero, by rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one, hp2 j]⟩
  obtain ⟨T, iK, hT, hiK⟩ := _root_.GlobalTheory.exists_cdvr_completion_integral_iff z.K p
  obtain ⟨M⟩ := (_root_.GlobalTheory.LamT.locMod_exists E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  have hinv : ∀ b j i, (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr) := fun b j i => by
    have := GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j i 1 (hgen _)
    rwa [map_one, _root_.one_mul] at this
  have hR : ∀ x : T.Fr, x ∈ Set.range (algebraMap T.V T.Fr) ↔ x ∈ (algebraMap T.V T.Fr).range :=
    fun x => (RingHom.mem_range).symm
  have hdetinv : ∀ b, ((g b).det)⁻¹ ∈ (algebraMap T.V T.Fr).range := fun b => by
    choose N hN using hinv b
    have e1 : (g b)⁻¹ = (Matrix.of N).map (algebraMap T.V T.Fr) := by
      ext j i; exact (hN j i).symm
    have e2 : ((g b).det)⁻¹ = ((g b)⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [e2, e1]
    exact ⟨(Matrix.of N).det, by rw [RingHom.map_det]; rfl⟩
  have hall := (hR _).1 (hS₁ p hp1 T iK hT hiK M φ yT y' g s rfl hyT hy' hg hL)
  have hdet : ∀ b, (g b).det ∈ (algebraMap T.V T.Fr).range := fun b => by
    have hne : (∏ b' ∈ Finset.univ.erase b, (g b').det) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b' _ => (hg b').ne_zero
    have e3 : (g b).det = (∏ b', (g b').det) * ∏ b' ∈ Finset.univ.erase b, ((g b').det)⁻¹ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), Finset.prod_inv_distrib, _root_.mul_assoc,
        mul_inv_cancel₀ hne, _root_.mul_one]
    rw [e3]
    exact Subring.mul_mem _ hall (Subring.prod_mem _ fun b' _ => hdetinv b')
  have hτ : (∏ b, (g b).det ^ k b) ∈ (algebraMap T.V T.Fr).range :=
    Subring.prod_mem _ fun b _ => Subring.pow_mem _ (hdet b) _
  obtain ⟨w, hw⟩ := GlobalTheory.T.framePolynomial_coeff_bounded_by_determinants E H Dw l Xo c z f La hz e k he p T iK hT hiK M φ yT y' g s rfl hyT hy' s.ne_zero hg hL
    hS (fun _ _ => 1) (fun b j i => by rw [_root_.one_mul]; exact hinv b j i) F hF hv G
    (fun y' Y hY hch => hG y' Y 1 hY (by rw [Units.val_one]; exact hch)) μ
  simp only [one_pow, Finset.prod_const_one, _root_.mul_one] at hw
  refine (hiK _).1 ((hR _).2 ?_)
  rw [hw]
  exact Subring.mul_mem _ hτ (RingHom.mem_range_self _ _)

end GlobalTheory.CoeffInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorIsCombinationEigenbasisFlagSpacePoint
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

theorem frameVector_isCombination_tangentBasis_flagCover_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}
    (X : GlobalTheory.FlagMod.FlagCover Y) (U : Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left))
    (h1 : ∀ i, IsTanAtG Y.t (LogKS.chart U) (v i))
    (h2 : ∀ w', IsTanAtG Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (LogKS.chart U) v cf w')
    (h3 : ∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG Y.t (LogKS.chart U) v
      (Pi.single (e ⟨τ, i⟩) (algX Y.s U.1 (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (Y.t.act.act a).left))
    (k : X.F.J) (S : Type) [CommRing S] (z' : Sp S ⟶ X.YY) (x : Sp S ⟶ Y.X) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ z' ⁻¹ᵁ X.F.U k) (hx : z' ≫ X.π = x) :
    ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
      IsCombAtG Y.t x (fun j => spMap (dualMap (ev x U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i)
        (tv (X.F.vecAt k z' hk hx σ i)).left := by
  classical
  subst hx
  have hxψ : spMap (ev (z' ≫ X.π) U.1 hU) ≫ LogKS.chart U = z' ≫ X.π := GlobalTheory.FlagMod.spMap_ev _ U.2 hU
  obtain ⟨b1, b2⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange Y.t (ev (z' ≫ X.π) U.1 hU) (LogKS.chart U) n v h1 h2
  rw [hxψ] at b1 b2

  set ψ := ev (z' ≫ X.π) U.1 hU with hψ
  let φ : c.F →+* S := (ev ((z' ≫ X.π) ≫ Y.s) ⊤ le_top).comp (toΓ c.F)
  have hφ : z' ≫ X.π ≫ Y.s = spMap φ := by
    rw [GlobalTheory.FlagMod.spMap_ev_top, Category.assoc]
  have hφψ : ∀ r : c.F, ψ (algX Y.s U.1 r) = φ r := fun r =>
    GlobalTheory.FlagMod.ev_appLE (z' ≫ X.π) Y.s (by simp) hU le_top (toΓ c.F r)
  let V : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (z' ≫ X.π) Y.t.G := fun m => GlobalTheory.LieMet.tanOf (b1 m)
  have hb : ∀ W, ∃! a : Fin n → S, ∑ i, a i • V i = W := fun W => by
    obtain ⟨a, ha, hu⟩ := b2 _ (GlobalTheory.LieMet.isTan_tv W)
    exact ⟨a, ((GlobalTheory.LieMet.isComb_iff V a W).1 ha).symm,
      fun a' ha' => hu a' ((GlobalTheory.LieMet.isComb_iff V a' W).2 ha'.symm)⟩
  have hV : ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)) (a : 𝓞 E),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a (V (e ⟨τ, j⟩)) = φ (embK c τ a) • V (e ⟨τ, j⟩) := by
    intro τ j a
    have h := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H Y.X Y.t _ S ψ (LogKS.chart U) _ hxψ).2 n v _ _ (h3 a τ j)
    have e1 : (fun i => ψ ((Pi.single (e ⟨τ, j⟩) (algX Y.s U.1 (embK c τ a)) : Fin n → Γ(Y.X, U.1)) i)) =
        fun i => (Pi.single (e ⟨τ, j⟩) (φ (embK c τ a)) : Fin n → S) i := by
      funext i
      by_cases hi : i = e ⟨τ, j⟩
      · subst hi; simp [hφψ]
      · simp [Pi.single_apply, hi]
    rw [e1] at h
    have e2 : spMap (dualMap ψ) ≫ v (e ⟨τ, j⟩) ≫ (Y.t.act.act a).left =
        (tv (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a (V (e ⟨τ, j⟩)))).left := by
      rw [← Category.assoc]; rfl
    rw [e2] at h
    rw [(GlobalTheory.LieMet.isComb_iff V _ _).1 h]
    simp [Pi.single_apply]
  letI : Algebra c.F S := φ.toAlgebra
  have hs := GlobalTheory.FlagEmb.EigSpread.splits (E := E) c
  have hu : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act) (embK c z.1) (V (e z)) :=
    fun z a => hV z.1 z.2 a
  have hb' : ∀ w, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S, ∑ z, a z • V (e z) = w := fun w => by
    obtain ⟨a, ha, hu⟩ := hb w
    refine ⟨fun z => a (e z), ?_, fun a' ha' => ?_⟩
    · rw [← ha]; exact Equiv.sum_comp e (fun i => a i • V i)
    · have h' : ∑ i, a' (e.symm i) • V i = w := by
        rw [← ha', ← Equiv.sum_comp e.symm (fun z => a' z • V (e z))]; simp
      have := hu _ h'
      funext z
      have := congrFun this (e z)
      simpa using this
  have key : ∀ σ i, ∃ cf : Fin (Dw.mult σ) → S, ∑ j, cf j • V (e ⟨σ, j⟩) = X.F.vecAt k z' hk rfl σ i :=
    fun σ i => (GlobalTheory.FlagEmb.EigSpread.block_basis hs (fun z => V (e z)) hu hb' σ _
      (fun a => GlobalTheory.VarFlag.actR_vecAt X φ z' k hk hφ σ i a)).exists
  choose C hC using key
  refine ⟨fun σ => Matrix.of fun i j => C σ i j, fun σ i => ?_⟩
  exact (GlobalTheory.LieMet.isComb_iff (fun j => V (e ⟨σ, j⟩)) (C σ i) _).2 (hC σ i).symm

theorem isCombAtG_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z), ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv k S _ z hU hk hx
  exact frameVector_isCombination_tangentBasis_flagCover_point TF.X U e v hv.1 hv.2.1 hv.2.2 k S (z ≫ inc₀ TF.X Z) (z ≫ toBase TF Z) hU hk hx

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackDeRhamMapExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.LinFrob

open GlobalTheory.Twist GlobalTheory.ConjSeq

theorem pull_frobDR (p : ℕ) [Fact p.Prime] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hR : (p : R) = 0) (hR' : (p : R') = 0) {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')}
    [GrpObj A'] {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ)
    (c : primDR A) :
    (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (frobDR p R hR A c) =
      frobDR p R' hR' A' ((GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull c) := by
  have k := (frobMor p R hR A (cast_left p R hR A)).comp (GlobalTheory.Published.AbelianDeRham.bcMor hφ)
  refine (GrpMor.pull_pull _ _ k (fun _ ↦ rfl) rfl c).trans
    (GrpMor.pull_pull _ _ k (fun r ↦ ?_) (GlobalTheory.VB.frob_naturality p _ φ _) c).symm
  rw [RingHom.comp_apply, frobR_apply, frobR_apply, map_pow]

theorem frobDR_smul (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A : Over (Sp R)} [GrpObj A] (r : R) (c : primDR A) :
    frobDR p R hR A (r • c) = r ^ p • frobDR p R hR A c := by
  rw [LinearMap.map_smulₛₗ, frobR_apply]

end GlobalTheory.LinFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrict
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem functionFieldMap_bijective_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → Function.Bijective (functionFieldMap s) := by
  intro X Y _ _ s _ U hU hiso
  have hg : s (genericPoint Y) = genericPoint X := by
    have h := (genericPoint_spec Y).image s.continuous
    rw [Set.image_univ, s.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec X)
  have hmem : genericPoint Y ∈ s ⁻¹ᵁ U := by
    change s (genericPoint Y) ∈ U
    rw [hg]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have h1 : IsIso ((s ∣_ U).stalkMap ⟨genericPoint Y, hmem⟩) :=
    ((isIso_iff_isIso_stalkMap (s ∣_ U)).1 hiso).2 _
  have h2 : IsIso (s.stalkMap (genericPoint Y)) :=
    ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap s U ⟨genericPoint Y, hmem⟩)).mp h1
  have h3 : ∀ (x y : X) (_ : x = y) (h : x ⤳ y), IsIso (X.presheaf.stalkSpecializes h) := by
    rintro x y rfl h
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  unfold functionFieldMap
  have h4 := h3 _ _ hg (hg ▸ specializes_rfl)
  exact ConcreteCategory.bijective_of_isIso _

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLab
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

def Deep.GalLab (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam) : Prop :=
  ∃ (P₀ : PolAV (Sp D.X.Ω₁)) (b : P₀.A.left ⟶ D.X.ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left)
    (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)),
    IsGrpPullback P₀.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) b ∧
    IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t ∧
    LBIso P₀.L (D.X.ρ.P.L.pull b) ∧ LBIso P₀.L (P₀.L.pull t) ∧
    (∀ E, (ε₀ E).left ≫ b = b ≫ (D.ε E).left ∧ (ε₀ E).left ≫ t = t ≫ (ε₀ E).left) ∧
    ∀ x (w w' : Sp D.X.Ω₁ ⟶ P₀.A.left), w ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left →
      w' ≫ t = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w →
        w' ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt (a x)).left

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNotInSncBoundary
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem genericPoint_notMem_of_snc (Y : Scheme.{0}) [IsIntegral Y] (B : Closeds Y)
    (h : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) : genericPoint Y ∉ B := by
  obtain ⟨-, U, hy, n, f, J, ⟨-, hn⟩, hI⟩ := h (genericPoint Y)
  have hdim : ringKrullDim (Y.presheaf.stalk (genericPoint Y)) = 0 :=
    ringKrullDim_eq_zero_of_field Y.functionField
  rw [hdim] at hn
  have hn0 : n = 0 := by exact_mod_cast hn
  subst hn0
  have hJ : J = ∅ := Finset.eq_empty_of_isEmpty J
  subst hJ
  intro hB
  have hs : genericPoint Y ∈ (Scheme.IdealSheafData.vanishingIdeal B).support := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hB
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hy, hI, Scheme.mem_zeroLocus_iff] at hs
  refine hs 1 (Ideal.subset_span (by simp)) ?_
  simpa using hy

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyHeightOnePrimesOfFlatStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasHartogsPropertyHeightOnePrimes_of_flat : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (B : Type) [CommRing B] [Algebra A B] [Module.Flat A B], GlobalTheory.GoodEtale.Hart A B B := by
  first | (exact @GlobalTheory.GoodEtale.hart_of_flat) | (exact GlobalTheory.GoodEtale.hart_of_flat) | (intros; apply GlobalTheory.GoodEtale.hart_of_flat  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyQuotientSpanPowRetractionStatement
section
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasHartogsProperty_quotient_span_pow_retraction : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.Hart A R (R ⧸ Ideal.span {t} ^ n) := by
  first | (exact @GlobalTheory.GoodEtaleSection.hart_quot) | (exact GlobalTheory.GoodEtaleSection.hart_quot) | (intros; apply GlobalTheory.GoodEtaleSection.hart_quot  <;> assumption)
end

