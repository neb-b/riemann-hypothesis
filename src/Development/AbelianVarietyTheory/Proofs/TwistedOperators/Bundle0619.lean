module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameLatticeFunctional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunctionalEquationLocalLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupFixingVacuumFixesVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.RowTest

theorem IsBottomTri.exists_open_fix_f : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac →
      X.ω t (1, κ) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  have h := hX.is
  have hom := h.weil t
  have hT2 : IsHeckeChar D ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) / (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))) :=
    hom.hecT
  have hx : ∀ x, ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) x =
      (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) / (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))) x)⁻¹ := fun x => by
    rw [MonoidHom.div_apply, MonoidHom.div_apply, inv_div]
  have hνH : IsHeckeChar D ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) :=
    ⟨hT2.1.inv.congr fun x => (hx x).symm, fun x => by rw [hx, hT2.2, inv_one]⟩
  obtain ⟨N₀, hN₀, hN₀'⟩ := _root_.GlobalTheory.HeckeLevel.exists_level D _ hνH
  have hI : X.ideal (locPl G) t ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  set N : ℕ := N₀ * Ideal.absNorm (X.ideal (locPl G) t) * ∏ w ∈ locPl G t, Ideal.absNorm w.asIdeal with hNdef
  have hNpos : 0 < N := by
    refine Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hN₀.ne' ?_) (Finset.prod_ne_zero_iff.2 fun w _ => ?_))
    · exact fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
    · exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hNI : ((N : ℕ) : 𝓞 D.host.E) ∈ X.ideal (locPl G) t := by
    rw [hNdef, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))
  have hNw : ∀ w ∈ locPl G t, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := fun w hw => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => Ideal.absNorm w.asIdeal) hw
    rw [hNdef, hc, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))
  have hNdiv : N₀ ∣ N := ⟨Ideal.absNorm (X.ideal (locPl G) t) * ∏ w ∈ locPl G t, Ideal.absNorm w.asIdeal, by rw [hNdef, mul_assoc]⟩
  obtain ⟨U, hUo, hU⟩ := _root_.GlobalTheory.FrameCongOpen.exists_open_cong D WW X.rW.β N hNpos
  refine ⟨U, hUo, fun κ hκ _ hvac => ?_⟩
  obtain ⟨z, hz, hzc⟩ := hU κ hκ
  have hst : Lev.finE WW κ ∈ Formalism.L2.DIV.St X.rW.β := ⟨z, hz⟩
  have hinv := GlobalTheory.T.standardPairFirst_invariant_congruenceOne D A WW _ (X.e t) (locPl G t) (h.idem t) (X.ideal (locPl G) t) X.rA.β X.rW.β N hNpos hNI hNw
    (hN₀' N hNdiv) κ z hz hzc
  have hsdA := isSelfDualC_neg' h.rigA.1
  have hsdW := h.rigW.1
  have hsg : ∀ f, (X.ω t).toSgn true (1, κ) f = X.ω t (1, κ) f := fun f => by
    simp [GlobalTheory.Grid.WRep.toSgn]
  have key := GlobalTheory.ExportSeries.DualType.om_theta_move hom
    (fun Tm hT Ψ hΨ => GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ h.isVac.1 _ WW _ _ hsdA hsdW _
      (GlobalTheory.PlaceDatum.idemSum_mul_self (h.idem t)) (GlobalTheory.PlaceDatum.infPart_idemSum (h.idem t)) _ h.isVac.2.theta Tm hT Ψ hΨ)
    (h.fst t) (h.fst t) (g := 1) (h := κ)
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D _ WW _ _ _ _ hsdA hsdW h.rigA.2.1 h.rigW.2.1 1 κ (by rw [map_one]; exact one_mem _) hst)
    one_ne_zero (c' := 1) (by rw [one_smul, hsg]; exact hvac) (fun x => by rw [one_mul, hinv x])
  rw [hsg, one_mul, one_smul] at key
  exact key

end GlobalTheory.RowTest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathEdgeFactorProdIntegralVertex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section
namespace GlobalTheory.OppositeEdges

theorem oppositePath_prod_mulSingle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Γ : Grid k) (j : ℕ) :
    j + 1 < Γ.m → ∀ (κ : GL (Fin (Γ.rank (j + 1, Γ.m))) k), κ ∈ GlobalTheory.SplitWeil.KO k _ →
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (j + 1, Γ.m) κ))).prod =
      ((Γ.chi (Γ.m - (j + 1)) (gdet κ) : ℂˣ) : ℂ) * (((Γ.chi (Γ.m - j) (gdet κ))⁻¹ : ℂˣ) : ℂ) := by
  intro hj κ hκ
  set g : Γ.VertexGroup := Pi.mulSingle (j + 1, Γ.m) κ with hg
  have hap : ∀ z, apow (1 : kˣ) z = 1 := fun z => apow_of_valuation_eq_one (by simp) z
  have hK : ∀ Y, g Y ∈ GlobalTheory.SplitWeil.KO k _ := by
    intro Y
    by_cases hY : Y = (j + 1, Γ.m)
    · subst hY; simpa [hg] using hκ
    · rw [hg, Pi.mulSingle_eq_of_ne hY]; exact one_mem _
  have ha : ∀ Y, ∀ z : ℂ, apow (gdet (Assignment.one.read (g Y))) z = 1 := fun Y z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO (hK Y))) z

  have hfar : ∀ b : Edge, b.src ≠ (j + 1, Γ.m) → b.tgt ≠ (j + 1, Γ.m) → Γ.edgeFactor .one g b = 1 := by
    intro b h1 h2
    simp [Grid.edgeFactor, hg, Pi.mulSingle_eq_of_ne h1, Pi.mulSingle_eq_of_ne h2, hap]
  have htheta : (((List.range Γ.m).reverse.map (Edge.theta Γ.m)).map (Γ.edgeFactor .one g)).prod = 1 := by
    refine List.prod_eq_one fun c hc => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    apply hfar <;> simp [Edge.src, Edge.tgt] <;> omega
  have hex : (((List.range Γ.m).map (Edge.ex · Γ.m)).map (Γ.edgeFactor .one g)).prod =
      ∏ i ∈ Finset.range Γ.m, Γ.edgeFactor .one g (.ex i Γ.m) := by
    rw [List.map_map, Finset.prod_eq_multiset_prod]; rfl
  have hne : j ≠ j + 1 := by omega
  have hrest : ∀ i ∈ Finset.range Γ.m, i ≠ j ∧ i ≠ j + 1 → Γ.edgeFactor .one g (.ex i Γ.m) = 1 := by
    intro i _ hi
    apply hfar <;> simp [Edge.src, Edge.tgt] <;> omega
  rw [oppositePath, List.map_append, List.prod_append, htheta, mul_one, hex,
    Finset.prod_eq_mul j (j + 1) hne hrest (by simp; omega) (by simp; omega)]
  have hκa : ∀ z : ℂ, apow (gdet (Assignment.one.read κ)) z = 1 := fun z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO hκ)) z
  have hj1 : (j + 1 + 1, Γ.m) ≠ (j + 1, Γ.m) := by simp
  have hj0 : (j, Γ.m) ≠ (j + 1, Γ.m) := by simp
  simp only [Grid.edgeFactor, Edge.src, Edge.tgt, ha, mul_one, hg, Pi.mulSingle_eq_of_ne hj1,
    Pi.mulSingle_eq_of_ne hj0, Pi.mulSingle_eq_same, hκa, map_one, hap, Units.val_one, inv_one, one_mul]
  simp only [Grid.kappa, Grid.blockChar, MonoidHom.div_apply, Units.val_div_eq_div_val,
    Units.val_inv_eq_inv_val, Nat.add_sub_cancel]
  have h1 := Units.ne_zero (Γ.chi (Γ.m - (j + 1)) (gdet κ))
  have h2 := Units.ne_zero (Γ.chi (Γ.m - j) (gdet κ))
  have h3 := Units.ne_zero ((Γ.eta ^ ((Γ.rank (j + 1, Γ.m) + 1) % 2)) (gdet κ))
  field_simp

end GlobalTheory.OppositeEdges
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicFixedDegree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.BotTransJet

open GlobalTheory.Grid (neg)

theorem conj_isAlgebraic {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (starRingEnd ℂ z) := by
  obtain ⟨p, hp, hz⟩ := h
  refine ⟨p, hp, ?_⟩
  have := Polynomial.aeval_algHom_apply ((starRingEnd ℂ).toRatAlgHom) z p
  rw [hz, map_zero] at this
  simpa using this

theorem applyAt0_isAlgebraic {D : D7} {N N' : ℕ} {P : MvPolynomial (GL3Theta.Idx D N N') ℂ} {G : TaylorLogMetric.VC D N N' → ℂ}
    (hP : ∀ α, IsAlgebraic ℚ (P.coeff α)) (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : IsAlgebraic ℚ (GL3Theta.applyAt0 D P G) := by
  rw [← mem_algebraicClosure_iff]
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ((mem_algebraicClosure_iff).2 (hP α)) ?_) (hG α)
  exact prod_mem fun _ _ => natCast_mem _ _

theorem jet_negSp_heis {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) (u : WO S T) (k : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT (heisO ψ (negSp S) T u f) (MvPolynomial.monomial k 1) 0 =
      starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u (fun w => starRingEnd ℂ (f w)))
        (MvPolynomial.monomial k 1) 0) := by
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T sS sT BS BT _ hψ hθ k 0]
  have h := ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T).2 u (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)).2
  have hcc : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = f := by
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hcc] at h
  have key : (fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w)) = heisO ψ S T u (fun w => starRingEnd ℂ (f w)) := by
    have hcj : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f = fun w => starRingEnd ℂ (f w) := rfl
    rw [h, ← hcj]
    funext w
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [key]

theorem std_eq_colLat_one {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) :
    (L : Set (Fin n → D.host.E)) = (colLat (1 : GL (Fin n) D.host.E) : Set _) := by
  ext y
  simp only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]

theorem even_bot {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

end GlobalTheory.BotTransJet

namespace GlobalTheory.BotTransJet

open GlobalTheory.Grid (neg)

end GlobalTheory.BotTransJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealUnitaryFockColumnActionSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped Matrix

namespace GlobalTheory.RealColAct

theorem compAt_eq_infMat {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V h) = infMat D.sp.cm.sig V.gram (θ τ) h := rfl

theorem realCol_surjective {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    Function.Surjective (GlobalTheory.RealColAct.realCol θ hθ V hV) := by
  classical
  intro u
  have hex : ∀ τ, ∃ h : GA D V, IsAtTau θ V τ ((u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) h := fun τ => by
    refine (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ _ ?_).exists
    have hu := transpose_mem_unitary (u τ).2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    show _ * _ * _ = _
    rw [gramAt_of_gram_one hV, Matrix.mul_one, hu]
  choose hτ hhτ using hex
  have key : ∀ (L : List D.what₂.Tau), L.Nodup → ∀ ρ,
      compAt θ ρ (Formalism.L2.Theta.mt V (L.map hτ).prod) =
        if ρ ∈ L then ((u ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) else 1 := by
    intro L
    induction L with
    | nil => intro _ ρ; simp only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]; exact GlobalTheory.StdUnn.CartanMove.compAt_mt_one θ ρ V
    | cons a L ih =>
      intro hL ρ
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, ih hL.2 ρ, compAt_eq_infMat]
      by_cases c : ρ = a
      · subst c
        rw [(hhτ ρ).2.1, if_neg hL.1, if_pos List.mem_cons_self, Matrix.mul_one]
      · rw [(hhτ a).2.2 ρ c, Matrix.one_mul]
        by_cases d : ρ ∈ L
        · rw [if_pos d, if_pos (List.mem_cons_of_mem a d)]
        · rw [if_neg d, if_neg (by simp [c, d])]
  let L := (Finset.univ : Finset D.what₂.Tau).toList
  have hmem : (L.map hτ).prod ∈ GinfC V := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact (hhτ τ).1
  refine ⟨(⟨(L.map hτ).prod, hmem⟩ : GinfC V)⁻¹, ?_⟩
  funext ρ
  apply Subtype.ext
  rw [realCol_apply]
  simp only [InvMemClass.coe_inv, inv_inv]
  rw [key L (Finset.nodup_toList _) ρ, if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ)), Matrix.transpose_transpose]

end GlobalTheory.RealColAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem GlobalTheory.FrameFB.frame_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b = ι a → a = Fin.last σ ∧ b = Fin.last σ) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xFB F σ h' i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xFB F σ h' i q))) ᵥ*
    ((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcFB W F σ h h').A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' v hv
  obtain ⟨k, _, _, _, _, p, β, j, ϖ, hpv, hid, hlat, hmax, ⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩, hj, hcol, hperp⟩ :=
    GlobalTheory.StairFrameFJ.exists_frame D hq T L μ0 hL sc G W M hM F hF σ h' v hv
  have hϖ : (ϖ : k) ≠ 0 := by
    intro h0
    have h0' : ϖ = 0 := Subtype.ext h0
    have : IsLocalRing.maximalIdeal 𝒪[k] = ⊥ := by rw [hmax, h0', Ideal.span_singleton_eq_bot.2 rfl]
    exact IsDiscreteValuationRing.not_a_field _ this
  obtain ⟨hs, ht⟩ := GlobalTheory.FrameScale.clauses D hq T L μ0 hL sc G W M hM F hF σ h' k p β j (ϖ : k) (G.pl.depth sc v) hϖ hj hcol hperp
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, p, β,
    fun q => j ⟨q.1, by omega⟩, fun q => j ⟨2 * σ - q.1, by omega⟩, _, _, hpv, hid, hlat, ?_, ?_, ?_, hs, ht, ?_⟩
  · intro a b hab
    have := hj hab
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · intro a b hab
    have := congrArg Fin.val (hj hab)
    simp at this
    exact Fin.ext (by omega)
  · intro a b hab
    have := congrArg Fin.val (hj hab)
    simp at this
    constructor <;> exact Fin.ext (by simp; omega)
  · intro a ha
    have hu2 : (p.pr (incA D (star (-D.host.xi0)))) ≠ 0 := right_ne_zero_of_mul_eq_one hu₂
    refine ⟨fun q i => ?_, fun q i => ?_⟩
    · obtain ⟨z, hz, hz'⟩ := _root_.GlobalTheory.DepthColumn.col_mem_depth D hq T L μ0 hL sc G W M hM F hF σ h h' v hv k p β ϖ hpv hid hlat hmax a ha q i
      exact ⟨z, hz, hz'⟩
    · obtain ⟨z, hz, hz'⟩ := GlobalTheory.ConjClause.functional_equation_local_lattice D hq T L μ0 hL sc G W M hM F hF σ h h' v hv k p β ϖ hpv hid hlat hmax a ha q i
      refine ⟨z * (if q.1 = σ then -1 else 1), Ideal.mul_mem_right _ _ hz, ?_⟩
      clear hperp hcol hs ht hlat
      have hϖn : (ϖ : k) ^ (G.pl.depth sc v * (2 * σ + 1 - q.1)) ≠ 0 := pow_ne_zero _ hϖ
      have hx : (p.pr (incA D (star (-D.host.xi0)))) ^ (q.1 + 1) ≠ 0 := pow_ne_zero _ hu2
      rw [← hz']
      generalize (p.pr (incA D (star (-D.host.xi0)))) ^ (q.1 + 1) = X at hx ⊢
      generalize (ϖ : k) ^ (G.pl.depth sc v * (2 * σ + 1 - q.1)) = Y at hϖn ⊢
      by_cases hqσ : q.1 = σ
      · simp only [hqσ, if_true]
        push_cast
        field_simp
      · simp only [hqσ, if_false]
        push_cast
        field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingFilledArgsMoveInnerLastColumnVertex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section
namespace GlobalTheory.TopLevelInv

theorem fill_moveVertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k)
    (x x' : ColArgs Γ) (y : RowArgs Γ) (e e' : Vars Γ),
    (∀ l, l ≠ j → l ≠ j + 1 → downMap hs x' e' l = downMap hs x e l) →
    downMap hs x' e' j = (g⁻¹).val * downMap hs x e j →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val →
    Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) (fill hs x y e) = fill hs x' y e' := by
  intro k _ _ _ _ _ _ Γ hs j hj g x x' y e e' hrest hj0 hj1
  funext b
  cases b with
  | theta i l =>
    by_cases hi : i = Γ.m
    · subst hi
      rw [moveArgs_theta, fill_theta, fill_theta, transpose_transpose]
      by_cases hl : l = j
      · subst hl
        have h1 : (Pi.mulSingle (Γ.m, l + 1) g : Γ.VertexGroup) (Γ.m, l) = 1 :=
          Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
        rw [h1, Pi.mulSingle_eq_same, Units.val_one, Matrix.mul_one, hj0]
      · by_cases hl' : l = j + 1
        · subst hl'
          have h1 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (Γ.m, j + 1 + 1) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
          rw [h1, Pi.mulSingle_eq_same, inv_one, Units.val_one, Matrix.one_mul, hj1]
        · have h1 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (Γ.m, l) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          have h2 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (Γ.m, l + 1) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          simp only [h1, h2, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, hrest l hl hl']
    · simp [fill, Grid.moveArgs, hi]
  | ex i l =>
    by_cases hl : l = Γ.m
    · subst hl
      have h1 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (i, Γ.m) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      have h2 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (i + 1, Γ.m) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, fill_ex, h1, h2, map_one, inv_one, Units.val_one,
        Matrix.one_mul, Matrix.mul_one]
    · simp [fill, Grid.moveArgs, hl]

end GlobalTheory.TopLevelInv

end
end

