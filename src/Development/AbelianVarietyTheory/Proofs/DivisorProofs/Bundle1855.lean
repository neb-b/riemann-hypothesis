module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0775
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceRatioRamified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamifiedOnLargePlaces

theorem chrEq_mul' {D : D7} {c c' : (AE D)ˣ →* Circle} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ)
    (h' : ChrEq c' χ') : ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx]
    rfl

theorem not_unramAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ S1 D →
    ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hIs t v e he hv i j hU
  have hi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  set k := D.R.m - (i : ℕ) with hk
  have hμ : ChrEq (Lc.mu t ((j : ℕ) + 1)) (Lc.C.mu0 j * Lc.xiH t) := chrEq_mul' (hIs.mu0 j) (hIs.xi t)
  have hν : ChrEq (Lc.mu t ((j : ℕ) + 1) / G.ch.chi k) (Lc.C.mu0 j * Lc.xiH t * (G.ch.chiH k)⁻¹) := by
    rw [div_eq_mul_inv]; exact GlobalTheory.ChartQuot.chrEq_div hμ (G.ch.chi_eq k hi1 hi2)
  set P := G.pl.w v
  have hP : P.under (𝓞 D.host.F) = v := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inr hv))
  have hUnr := (GlobalTheory.LFun.unrAt_iff_of_chrEq hν P).1
    (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ v e he hU P hP)
  apply (G.ch.lev1 k hi1 hi2 P (by rw [hP]; exact hv)).2
  intro x hx hxv
  have h1 := hUnr x hx
  have h2 := (Lc.C.isMu0 j).tame P x hx hxv
  have h3 := hIs.xi_tame t P x hx hxv
  have e1 : (Lc.C.mu0 j * Lc.xiH t * (G.ch.chiH k)⁻¹).loc P x =
      (Lc.C.mu0 j).loc P x * (Lc.xiH t).loc P x * ((G.ch.chiH k).loc P x)⁻¹ := rfl
  rw [e1, h2, h3, one_mul, one_mul, inv_eq_one] at h1
  exact h1

end GlobalTheory.RamifiedOnLargePlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TangentConstLB

theorem symIso_of_comm {S₀ S₁ : Scheme.{0}} {X : Over S₀} {A' : Over S₁} [GrpObj X] [GrpObj A']
    {L : LB X.left} (hL : L.IsLB)
    (hS : LBIso L (L.pull (GrpObj.inv : X ⟶ X).left)) (f : A'.left ⟶ X.left)
    (hf : (GrpObj.inv : A' ⟶ A').left ≫ f = f ≫ (GrpObj.inv : X ⟶ X).left) :
    LBIso ((L.pull f).pull (GrpObj.inv : A' ⟶ A').left) (L.pull f) := by
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine ⟨top_le_iff.1 ?_, ?_, ?_⟩
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy,
        gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have h1 := GlobalTheory.FamRep.lbIso_pull_pull hL f (GrpObj.inv : A' ⟶ A').left
  rw [hf] at h1
  have h2 := (GlobalTheory.FamRep.lbIso_pull_pull hL (GrpObj.inv : X ⟶ X).left f).symm
  have h3 := GlobalTheory.FamRep.lbIso_pull hS.symm f
  have hinv := pull_isLB hL (GrpObj.inv : X ⟶ X).left
  exact LBIso.trans (pull_isLB (pull_isLB hL f) _) (pull_isLB hL _) (pull_isLB hL f) h1
    (LBIso.trans (pull_isLB hL _) (pull_isLB hinv f) (pull_isLB hL f) h2 h3)

theorem lbIso_tangent_const :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x₀ : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G x₀ π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) := by
  intro E _ _ _ H Dw l Xo c K _ _ x₀ x' A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine ⟨top_le_iff.1 ?_, ?_, ?_⟩
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy,
        gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hAbG : IsAbelianScheme Xo.univ.t.G := by
    haveI := Xo.univ.proper
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ Xo.univ.t.semi
  have hA : IsAbelianScheme A := by
    refine { comm := ?_, smooth := ?_, proper := ?_, geomConnected := ?_ }
    · have := hAbG.comm
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
        ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm]
    · exact MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hAbG.smooth
    · exact MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hAbG.proper
    · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hAbG.geomConnected
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨-, w, hw, -⟩ := Xo.univ.t.sym
  have hS : LBIso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left) := ⟨w, hw⟩
  have c1 : (GrpObj.inv : A' ⟶ A').left ≫ π' = π' ≫ (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left :=
    GlobalTheory.PolBaseChange.inv_comm hπ'
  have c2 : (GrpObj.inv : A' ⟶ A').left ≫ (q ≫ π) = (q ≫ π) ≫ (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left := by
    rw [← Category.assoc, GlobalTheory.PolBaseChange.inv_comm hq, Category.assoc, GlobalTheory.PolBaseChange.inv_comm hπ,
      Category.assoc]
  have f1 := GlobalTheory.FamRep.lbIso_pull_pull hL π' i
  rw [hiπ] at f1
  have f2 := GlobalTheory.FamRep.lbIso_pull_pull hL (q ≫ π) i
  rw [← Category.assoc, hiq, Category.id_comp] at f2
  exact GlobalTheory.SymFirstOrder.lbIso_of_symmetric K A A' i q hA hi hq hiq _ _ (pull_isLB hL π') (pull_isLB hL (q ≫ π))
    (symIso_of_comm hL hS π' c1) (symIso_of_comm hL hS (q ≫ π) c2)
    (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) f1 f2.symm)

end GlobalTheory.TangentConstLB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanUpperBoundBigFactorsPlaceAboveTwo
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem mean_bound_big_factors_at_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (F : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H F vd → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit ((p : ℕ) : T.V) → y.IsAlg → ∃ len : (E →+* ℂ) → ℝ, (∀ τ, 0 ≤ len τ) ∧ (∀ τ, ¬ InPsi H τ → len τ = 0) ∧ ∑ τ, len τ ≤ F * Dw.q * (1 + vd / 2) ∧ ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → nuFac p y f k ≤ ((k * len f.1 : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p hp F vd hTP T io y h2 hy
  classical
  obtain ⟨Ch, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
  obtain ⟨X⟩ := GlobalTheory.CharDepth.nonempty_valExt T p h2
  obtain ⟨xs, hAF, hprod⟩ := GlobalTheory.CharDepth.colength_bound_at_two p (GlobalTheory.ChF.colength_bound_split_place_chart p)
    E H Dw l Xo c T io y Ch X hy F vd hTP
  set v2 : ℝ := (X.v ((p : ℕ) : X.C) : ℝ) with hv2
  set B : ℝ := (F : ℝ) * Dw.q * (1 + vd / 2) with hB

  have hv2pos : 0 < v2 := by
    rw [hv2, NNReal.coe_pos, pos_iff_ne_zero, Ne, map_eq_zero]
    exact Nat.cast_ne_zero.2 hp.out.ne_zero
  have hv2lt : v2 < 1 := by
    have h2C : algebraMap X.O X.C ((p : ℕ) : X.O) = ((p : ℕ) : X.C) := map_natCast _ _
    have hle := X.ints.map_le_one ((p : ℕ) : X.O)
    have hne : X.v (algebraMap X.O X.C ((p : ℕ) : X.O)) ≠ 1 := fun h =>
      X.nonunit.out ((X.ints.isUnit_iff_valuation_eq_one).2 h)
    rw [h2C] at hle hne
    rw [hv2]
    exact_mod_cast lt_of_le_of_ne hle hne
  have hlogv : Real.log v2 < 0 := Real.log_neg hv2pos hv2lt

  have hpos : ∀ τ, InPsi H τ → 0 < (xs τ : ℝ) := by
    intro τ hτ
    have hP : 0 < ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hv2pos _) hprod
    rcases (NNReal.coe_nonneg (xs τ)).lt_or_eq with h | h
    · exact h
    · exfalso
      have : ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ⟩) h.symm
      linarith
  have hle1 : ∀ τ, InPsi H τ → (xs τ : ℝ) ≤ 1 := by
    intro τ hτ
    have hne : xs τ ≠ 0 := fun h => by have := hpos τ hτ; rw [h] at this; simp at this
    exact_mod_cast (GlobalTheory.CharDepth.exists_flag_characters X.C X.v X.O X.ints _ _ _ _ _ (hAF τ hτ) hne).1
  let len : (E →+* ℂ) → ℝ := fun τ => if InPsi H τ then Real.log (xs τ) / Real.log v2 else 0
  have hlen_pow : ∀ τ, InPsi H τ → v2 ^ len τ = (xs τ : ℝ) := by
    intro τ hτ
    simp only [len, if_pos hτ]
    rw [Real.rpow_def_of_pos hv2pos, mul_div_cancel₀ _ hlogv.ne, Real.exp_log (hpos τ hτ)]
  refine ⟨len, ?_, ?_, ?_, ?_⟩
  · intro τ
    by_cases hτ : InPsi H τ
    · simp only [len, if_pos hτ]
      exact div_nonneg_of_nonpos (Real.log_nonpos (NNReal.coe_nonneg _) (hle1 τ hτ)) hlogv.le
    · simp [len, if_neg hτ]
  · intro τ hτ
    simp [len, if_neg hτ]
  · have hsum : ∑ τ, len τ = (∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ)) / Real.log v2 := by
      rw [Finset.sum_div, Finset.sum_filter]
    have hlogP : Real.log (∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ)) =
        ∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ) :=
      Real.log_prod fun τ hτ => (hpos τ (Finset.mem_filter.1 hτ).2).ne'
    have hlb : B * Real.log v2 ≤ ∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ) := by
      rw [← hlogP, ← Real.log_rpow hv2pos]
      exact Real.log_le_log (Real.rpow_pos_of_pos hv2pos _) hprod
    rw [hsum, div_le_iff_of_neg hlogv]
    exact hlb
  · intro f k hf
    have hr : (X.v ((p : ℕ) : X.C) : ℝ) ^ len f.1 ≤ xs f.1 := (hlen_pow f.1 hf).le
    exact (GlobalTheory.T.flagStep_characters_of_colength E H Dw l Xo c p T io y Ch X f (xs f.1) (len f.1) (hAF f.1 hf) hr).2 k

end GlobalTheory.RefSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

section Data

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev lattice₂ : AddSubgroup (WO (Vc D i) (Wc D i)) := latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True


open Classical in
def IsTypeVec (eg : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (lattice₂ R i) 1 (R.vacP i)
    (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
      omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg


open Classical in
def flatDat (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (eQ : AE D) (x : WO (Vc D i) (Wc D i)) : ℂ :=
  if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaFlat Q (Wc D i).rank ξR (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0

abbrev IsModel (eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ)
    (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) : Prop :=
  IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (lattice₂ R i) 1 fg Tm

abbrev dil (a : D.host.E) (x : WO (Vc D i) (Wc D i)) : WO (Vc D i) (Wc D i) := Matrix.map x fun w => incA D a * w

abbrev IsCoefMap (c0L : ∀ j : Fin D.R.m, VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W) : Prop :=
  ∃ gramR c0R, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L

end Data

def FlatTwoStep : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ) (B : Base (Vc D i) (Wc D i)),
    B.Good → BaseOf R i B → KerDat R i ξ χ ξR B.de.Q ω φ → ChrEq B.de.chi ξ →
    ∃ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg ∧ IsIdemSum eQ B.de.Q ∧ IsTypeVec R i eg fg ∧
      IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (lattice₂ R i) 1 fg (flatDat R i B.de.Q ξR eQ)
        (GlobalTheory.FlatVecSum.princ B).vecBase

def TraceLevel : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ)
    (e : G ≃* G0 B.G.Pg (Wc D i).rank),
    (∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) →
    (∀ g, e g ∈ B.G.P.H ↔ g ∈ U) →
    (∀ (u : U) (hu : e u ∈ B.G.P.H), ((B.G.P.chi ⟨e u, hu⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ u : D.what₂.LLˣ) : D.what₂.LL)) →
    ∀ ω : WeilRep D i, B.IsWeil 1 ω → ∀ (h : GA D (Vc D i)) (P : PolF D (Wc D i).rank (Vc D i).rank),
      levelTrace R i U ψ ((GlobalTheory.FlatVecSum.princ B).theta ω h P) = B.theta ω h P

def CoefIndep : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) c0L, IsCoefMap R c0L → ∀ (h : GA D (Vc D i)) w, InCoefLat R i h w →
      ∃ P ∈ nabAtr (labLL D) (lamV D i) (Bridge.hLat (Vc D i) (fin (Vc D i) h)), w = c0L i P

def NabBaseChange : Prop := ∀ (E K₀ K ι : Type) [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K]
    [Fintype ι] (n : ℕ) (f : K₀ →+* K) (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E M →
    nabAtr (fun τ => f.comp (emb τ)) lam M ≤
      Submodule.span (𝓞 K) {y : VV K lam | ∃ x ∈ nabAtr emb lam M, (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)}

def LevLamRoot : Prop := ∀ (D : D7) (S T : HSp D) (B : Base S T) (t : Twist D Circle) (k : B.levJ t),
    ∃ n : ℕ, n ≠ 0 ∧ ((B.levLam t k : ℂˣ) : ℂ) ^ n = 1

end GlobalTheory.BaseCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NadelApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

theorem topologicalKrullDim_eq_of_smooth (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp ℂ) (D : ℕ)
    [SmoothOfRelativeDimension D q] : topologicalKrullDim X = D := by
  have hc (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
      topologicalKrullDim (U : Set X) = D := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U))).trans
      (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance U hU hne)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (genericPoint X))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

theorem nadel_canonical_add : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → letI := algebraΓOfHom q; ∀ (K : CanonLB q D) (B M₀ : LB X) (hB : B.IsLB) (D₀ : CartierDiv X) (m' r : ℕ), 0 < m' → 0 < r → D₀.Eff → IsNef ℂ M₀ → IsBig ℂ M₀ → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![B] : ℚ) = interNumRed ℂ C ![toLB D₀] / m' + interNumRed ℂ C ![M₀] / r) → ∃ J : X.IdealSheafData, (∀ y : X, y ∈ J.support ↔ ¬ KltAt q D (qWeil D₀ m') y) ∧ ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) (tens K.bundle B)) i) := by
  intro hN X _ _ q D _ hproj K B M₀ hB D₀ m' r hm hr hD₀ hnef hbig hcurve
  letI := algebraΓOfHom q
  haveI := SmoothOfRelativeDimension.smooth D q
  haveI : IsNormalScheme X := isNormalScheme_of_smooth q
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj
  have hdim := topologicalKrullDim_eq_of_smooth X q D
  have hK := K.isLB
  have hKB := isLB_tens hK hB
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB q).1 hproj
  have hcan : toPic (canonical q D) = cls _ hK :=
    (presents_canonical q D).toPic_eq.trans ((cls_eq_iff _ _).2 (CanonLB.lbIso _ K))
  obtain ⟨J, hJ, hv⟩ := hN X q D hproj hdim (tens K.bundle B) (qWeil D₀ m') m'
    (m' • canonical q D + D₀) r M₀ hKB (isEffQDiv_qWeil hD₀ m') hm
    (isLogCanonicalMultiple_canonical hdim D₀ hm) hr hnef hbig (fun C hC => by
      have e1 := hC.interNumRed_of_cls_eq_add hH hKB hK hB (cls_tens hK hB hKB)
      have e2 := hC.interNumRed_of_cls_eq_add hH (isLB_toLB (m' • canonical q D + D₀))
        (isLB_lbPow hK m') (isLB_toLB D₀) (by
          rw [← toPic_apply, ← toPic_apply, map_add (f := _), map_nsmul, hcan, cls_lbPow hK])
      rw [e1, e2, hC.interNumRed_lbPow hH hK m']
      have : (m' : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      rw [hcurve C hC]
      field_simp
      ring)
  exact ⟨J, hJ, hv⟩

end GlobalTheory.NadelApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushInvertibleOfHasTheta
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS.TorFlagEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem isDedFrac_id : GlobalTheory.Models.IsDedFrac (RingHom.id c.F) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩

theorem pushInvertible_of_hasTheta (Y : Model Xo c (RingHom.id c.F)) (hθ : GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L) :
    PushInvertible Y.t.G Y.t.PP.L :=
  GlobalTheory.PushInv.pushInvertible_of_model GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 GlobalTheory.allSixLaws.2.2.1 E H Dw l _ _ _ _ _ _ Y.oF _
    (RingHom.id c.F)
    ⟨Y.X, Y.s, Y.normal, Y.proj, Y.flat, Y.jQ, Y.jQ_over, Y.jQ_open, Y.jQ_dense, Y.t, Y.m, Y.ab_gen⟩ isDedFrac_id hθ

theorem one_le_of_dimFlag (h : 1 ≤ dimFlag Dw) : 1 ≤ Dw.p + Dw.q := by
  by_contra h0
  have : Dw.p + Dw.q = 0 := by omega
  simp [dimFlag, Formalism.DegreeFormula.dimFl, this] at h

end GlobalTheory.CompHS.TorFlagEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStabilizerPreservesVacuumConditionAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryStabilizer_preserves_vacuumCondition_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, k)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ₁)) := by
  first | exact @GlobalTheory.InertSph.acts_vacCond_of_mem_KAt | exact GlobalTheory.InertSph.acts_vacCond_of_mem_KAt | (intros; apply GlobalTheory.InertSph.acts_vacCond_of_mem_KAt <;> assumption)
end

