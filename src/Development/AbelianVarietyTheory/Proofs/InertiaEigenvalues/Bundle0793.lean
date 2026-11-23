module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayField
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionAdjointFrameConjHalfTwoParts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.TwoStepRed

theorem redM_part_eq {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D))
    (βT : GL (Fin T.rank) (EAf D)) (P R : Finset (Pl D.host.E)) (e f : AE D)
    (hP : IsIdemSum e P) (hR : IsIdemSum f R) (hd : Disjoint P R) (x : WO S T)
    (hx : IsHalf (cA D (e + f)) x) (hN : IsIntM (frMapAdj S T βS βT x)) :
    ∀ PP ∈ P, redM PP (frMapAdj S T βS βT (cA D e • x)) = redM PP (frMapAdj S T βS βT x) := by
  intro PP hPP
  have hsplit : x = cA D e • x + cA D f • x := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← add_mul, ← map_add (f := _), hx i j]
  have h1 : frMapAdj S T βS βT x
      = frMapAdj S T βS βT (cA D e • x) + toEAf D f • frMapAdj S T βS βT x := by
    conv_lhs => rw [hsplit]
    rw [GlobalTheory.PlaceVec.frMapAdj_add, GlobalTheory.RedHalfDrop.frMapAdj_smul_eq βS βT (cA D f) x, cA_cA]
  have hc : toEAf D f ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
    rw [← GlobalTheory.ExportSeries.idem_eq hR]
    unfold GlobalTheory.ExportSeries.idem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show (toEAf D) (∑ Q ∈ R, GlobalTheory.ExportSeries.idemAt Q) = ∑ Q ∈ R, (toEAf D) (GlobalTheory.ExportSeries.idemAt Q) from
      map_sum (toEAf D).toAddMonoidHom _ _]
    exact sum_mem (fun Q hQ => GlobalTheory.RedHalfDrop.int_idemAt ⟨f, hR⟩ hQ)
  rw [eq_sub_of_add_eq h1.symm]
  exact GlobalTheory.RedHalfDrop.redM_sub_smul PP hN hc
    (GlobalTheory.AdjRedOff.resS_idemSum_eq_zero hR hc (fun h => Finset.disjoint_left.mp hd hPP h))

theorem redM_twoStep : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → IsIntM (frMapAdj S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT (cA D eg • x)) = redM PP (frMapAdj S T βS βT x)) ∧ (∀ PP ∈ Q, redM PP (frMapAdj S T βS βT (cA D eQ • x)) = redM PP (frMapAdj S T βS βT x)) := by
  intro D S T βS βT Pg Q eg eQ hg hQ hd _ x hx hN
  exact ⟨redM_part_eq S T βS βT Pg Q eg eQ hg hQ hd x hx hN,
    redM_part_eq S T βS βT Q Pg eQ eg hQ hg hd.symm x (by rwa [add_comm]) hN⟩

end GlobalTheory.TwoStepRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionTrivialOffSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

theorem idemAt_mul_idem_add_conj {D : D7} {P Q' : Finset (Pl D.host.E)} (hP : SplitSet P) (hQ : Q' ⊆ P)
    {PP : Pl D.host.E} (hPP : PP ∈ P) (hPQ : PP ∉ Q') : idemAt PP * (idem Q' + cA D (idem Q')) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mul_add, idem, map_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_eq_zero fun q hq => hP.mul_eq_zero hPP (hQ hq) (fun e => hPQ (e ▸ hq)),
    Finset.sum_eq_zero fun q hq => hP.mul_conj hPP (hQ hq), add_zero]


set_option maxHeartbeats 6000000 in
theorem redFn_eq_one_of_suppAt : ∀ {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {P Q' : Finset (Pl D.host.E)}, SplitSet P → Q' ⊆ P → ∀ {PP : Pl D.host.E}, PP ∈ P → PP ∉ Q' → ∀ {κ : GA D V}, Lev.finE V κ ∈ St β → SuppAt (idem Q') V κ → redFn β PP (Lev.finE V κ) = 1 := by
  intro D V β P Q' hP hQ PP hPP hPQ κ hS hSupp
  obtain ⟨y, hy⟩ := hS
  obtain ⟨hint, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP (hP.isIdemAt hPP)
  have h0 := idemAt_mul_idem_add_conj hP hQ hPP hPQ

  have hk : ∀ i j, idemAt PP * (Formalism.L2.Theta.mt V κ - 1) i j = 0 := fun i j => by
    rw [← hSupp i j, ← mul_assoc, h0, zero_mul]
  have hval : (Lev.finE V κ).val = (Formalism.L2.Theta.mt V κ).map (toEAf D) := rfl

  have hA : toEAf D (idemAt PP) • ((Lev.finE V κ).val - 1) = 0 := by
    ext i j
    have := congrArg (toEAf D) (hk i j)
    rw [RingHom.map_mul, RingHom.map_zero, Matrix.sub_apply, RingHom.map_sub] at this
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, hval, Matrix.map_apply, Matrix.zero_apply]
    convert this using 3
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hY : toEAf D (idemAt PP) • ((intGL D.host.F D.host.E _ y).val - 1) = 0 := by
    have hg : intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V κ * β := by
      rw [← hy]; simp [frGL, MulAut.conj_apply, mul_assoc]
    have e1 : (intGL D.host.F D.host.E _ y).val - 1 = (β⁻¹).val * ((Lev.finE V κ).val - 1) * β.val := by
      rw [hg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul β⁻¹ β, inv_mul_cancel, Units.val_one,
        Units.val_mul, Units.val_mul]
    rw [e1, ← Matrix.smul_mul, ← Matrix.mul_smul, hA, Matrix.mul_zero, Matrix.zero_mul]
  rw [← hy, redFn_frGL]
  ext i j
  have hij := congrFun (congrFun hY i) j
  have hsub : (⟨toEAf D (idemAt PP), hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * y.val i j = (⟨toEAf D (idemAt PP), hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    have hij' : toEAf D (idemAt PP) * ((intGL D.host.F D.host.E _ y).val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j) = 0 := by
      simpa only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.zero_apply] using hij
    have h1ij : ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j : Lev.EAf D) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, h1ij, ← sub_eq_zero, ← mul_sub]
    exact hij'
  have := congrArg (resS D.host.F PP) hsub
  rw [RingHom.map_mul, RingHom.map_mul, h1, one_mul, one_mul] at this
  change (resS D.host.F PP) (y.val i j) = _
  rw [this, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.ExportSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleSecondSplittingCharacter
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem chiData_chrTh_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ChiData (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) (D.host.g 0 * D.host.g 1) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ hLev _ _ _ _ _ i _
  have hxi : R.toLevCh.xi A.μ0 = 1 := MonoidHom.ext fun x => by
    have h := hLev.xi A.μ0
    rw [hLev.xi_base] at h
    exact GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one h x
  have e : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).2 = R.toLevCh.mu0 ((i : ℕ) + 1) * R.eta⁻¹ := by
    simp only [Lift.chrTh, LevCh.mu, Lift.tup, hxi, mul_one]
  rw [e]
  refine ⟨?_, fun Q hQ => ?_, fun Q hQ k => ?_⟩
  · have ha := hLev.mu0 i
    have hc := hLev.eta
    refine ⟨⟨ha.1.1.mul hc.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha.1.2, hc.1.2, inv_one, one_mul]
    · show ((R.toLevCh.mu0 ((i : ℕ) + 1) x * (R.eta x)⁻¹ : Circle) : ℂ) =
        (((R.C.mu0 i).locK P k * (R.C.eta.locK P k)⁻¹ : ℂˣ) : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv, ha.2 P e he k x hx, hc.2 P e he k x hx, Units.val_mul,
        Units.val_inv_eq_inv_val]
  · intro x hx
    have hg : ∀ k, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) Q := fun k hk => hQ (by
      rw [Nat.cast_mul]
      fin_cases k
      · exact Ideal.mul_mem_right _ _ hk
      · exact Ideal.mul_mem_left _ _ hk)
    have loc_mul (a b : Formalism.L2.Host.HChar D.host.E) :
        (a * b).loc Q x = a.loc Q x * b.loc Q x := rfl
    have loc_inv (a : Formalism.L2.Host.HChar D.host.E) :
        (a⁻¹).loc Q x = (a.loc Q x)⁻¹ := rfl
    rw [loc_mul, loc_inv, (R.C.isMu0 i).unr Q hg x hx, R.C.isEta.unr Q x hx,
      inv_one, one_mul]
  · have hcard : (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (Q.under (𝓞 D.host.F))).card ≠ 1 := by
      refine ne_of_gt (Finset.one_lt_card.2 ⟨Q, ?_, GlobalTheory.IdemSupport.cP Q, ?_, hQ.symm⟩)
      · rw [Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset]; rfl
      · rw [Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset]; exact GlobalTheory.IdemSupport.under_cP Q
    rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv, (R.C.isMu0 i).triv.1, R.C.isEta.res.1,
      Formalism.L2.Host.etaFin, ite_eq_right hcard, inv_one, one_mul]

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanConjUnitaryLieAlgebraRealPlaceEqTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.LieSpanConj

theorem exists_decomp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X Y : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 ∧ Yᴴ * H + H * Y = 0 ∧
      Z = X + Complex.I • Y := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.2 hd
  set Zb : Matrix (Fin n) (Fin n) ℂ := -(H⁻¹ * Zᴴ * H) with hZb
  have hA : Zbᴴ * H = -(H * Z) := by
    rw [hZb, conjTranspose_neg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, hH, neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
      Matrix.mul_one]
  have hB : H * Zb = -(Zᴴ * H) := by
    rw [hZb, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Z + Zb), (-(Complex.I / 2)) • (Z - Zb), ?_, ?_, ?_⟩
  · rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      hA, hB]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    rw [show Zᴴ * H + -(H * Z) + (H * Z + -(Zᴴ * H)) = 0 by abel, smul_zero]
  · rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      hA, hB]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by
      simp [Complex.conj_I]
      ring
    rw [this]
    rw [show Zᴴ * H - -(H * Z) = H * Z + Zᴴ * H by abel, show H * Z - -(Zᴴ * H) = H * Z + Zᴴ * H by abel]
    rw [← add_smul]
    simp
  · rw [smul_smul, smul_add, smul_sub]
    have h1 : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      have := Complex.I_sq
      linear_combination (-(1 / 2 : ℂ)) * this
    rw [h1]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem span_conj_lieAt_eq_top : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau) (Fm : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsUnit Fm → Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} = ⊤ := by
  intro D V τ Fm hF
  have hFd : IsUnit Fm.det := (Matrix.isUnit_iff_isUnit_det Fm).1 hF
  have hd : (gramAt D V τ).det ≠ 0 := by
    rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)
  rw [eq_top_iff]
  intro Z' _
  obtain ⟨X, Y, hX, hY, hZ⟩ :=
    GlobalTheory.LieSpanConj.exists_decomp (gramAt D V τ) (SmoothForms.RealPts.gramAt_herm V τ) hd (Fm⁻¹ * Z' * Fm)
  have hmX : Fm * X * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} :=
    Submodule.subset_span ⟨X, hX, rfl⟩
  have hmY : Fm * Y * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} :=
    Submodule.subset_span ⟨Y, hY, rfl⟩
  have hZ' : Z' = Fm * X * Fm⁻¹ + Complex.I • (Fm * Y * Fm⁻¹) := by
    have : Z' = Fm * (Fm⁻¹ * Z' * Fm) * Fm⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hFd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hFd, Matrix.mul_one]
    rw [this, hZ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hZ']
  exact Submodule.add_mem _ hmX (Submodule.smul_mem _ _ hmY)

end GlobalTheory.LieSpanConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanFiniteTranslatesVacuumThetaFockVacua
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem map_infPart_of_nsmul {V W : HSp D} {y : WO V W} {M : ℕ} (hM : M ≠ 0) (h : (M • y).map (infPart D) = 0) :
    y.map (infPart D) = 0 := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul D.host.F] at h1
  exact (smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hM)

theorem map_infPart_of_mem_latO {V W : HSp D} {LV : Set (Fin V.rank → D.host.E)} {LW : Set (Fin W.rank → D.host.E)}
    {u : WO V W} (hu : u ∈ latO V W LV LW fun _ => True) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add (f := _), hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem trSp_theta_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (e : AE D) (M : ℕ) (O₁ : Subring ℂ), M ≠ 0 → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O₁,
      IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hv e M O₁ hM f hf
  have hvac : IsVacO ψ θ V W (fun _ => 1) sW (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f₀ :=
    hv.2.2.2.2.2.2.2.2
  let Sp : Submodule ℂ (WO V W → ℂ) :=
    Submodule.span ℂ (Set.range fun a : {a : WO V W // a.map (infPart D) = 0} => heisO ψ V W a f₀)
  have hle : trSp ψ V W ΛV ΛW f₀ e M O₁ ≤ Sp.restrictScalars O₁ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, -, hy, rfl⟩
    exact Submodule.subset_span ⟨⟨y, map_infPart_of_nsmul hM (map_infPart_of_mem_latO hy)⟩, rfl⟩
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hle hf)
  rw [← hc]
  exact ⟨GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ V W hvac.1.1 f₀ hvac.2.theta _ c.support (fun a => a.1) c
      fun a _ => a.2,
    fun τ => GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ V W hvac.1.1 hvac.2.inf f₀ hvac.2.theta τ _ (hvac.2.fock τ) _
      c.support (fun a => a.1) c fun a _ => a.2⟩

end GlobalTheory.LevelSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDeterminantMulIntegralFormsRayClassCover
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.TwistInt


set_option maxHeartbeats 1000000 in
theorem mul_twist_mem_intForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ C : Cover T j T.σ₀, C.IsUnif → (∃ φ : D.host.K →+* C.d.c₂.F, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ C.d.l₂.M) → ∀ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist C.σ₂ C.d.pd xi → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), ∀ φ ∈ C.intForms wa n S, (fun g => ((xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) : ℂˣ) : ℂ) * φ g) ∈ C.intForms wa n S := by
  intro D T hL j hj C hU hRay xi hxi wa n S φ hφ
  have hP : T.Q.Pins := hL.pins
  have hlev : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hM3 : 3 ≤ C.d.l₂.M := C.d.l₂.three_le
  have hpd : 0 < C.d.pd := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hlev; omega

  have hsq : ∃ a : D.host.K, a ^ 2 = -(T.Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [show T.Q.H.d = D.host.d from hP.1.1]
    apply Subtype.ext
    have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
    simpa using hb
  obtain ⟨φK, hφK⟩ := hRay
  have hW := (_root_.GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField D.host.E T.Q.H D.host.K C.d.c₂.F φK C.d.c₂.F.val.toRingHom (Formalism.L2.Pj.LPb.finrank_K D) hsq
    C.d.l₂.M hM3 hφK).1
  have hWc : GlobalTheory.FinalJoin.WeberIn T.Q.H C.d.c₂.F C.d.l₂.M := fun P hP' => by
    have hsub : ∀ z ∈ C.d.c₂.F.val.toRingHom.toRatAlgHom.fieldRange, z ∈ C.d.c₂.F := fun z hz' => by
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.1 hz'
      exact y.2
    obtain ⟨a1, a2⟩ := hW P hP'
    exact ⟨hsub _ a1, fun s hs => hsub _ (a2 s hs)⟩

  have hno : ∀ g : GA D (T.V j T.σ₀),
      GlobalTheory.FinalJoin.NormOne (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) := fun g => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (T.V j T.σ₀)).1 g
    rw [← GlobalTheory.NormOneTwist.finQuot_of_isDetRoot hx]
    exact GlobalTheory.NormOneTwist.normOne_finQuot x
  obtain ⟨m, hm, hexp⟩ := GlobalTheory.XiCounterexample.fin_of_rat_tame D C.d.pd hpd xi hxi.rat hxi.cond
  choose w hw using fun g => hxi.val _ (hno g)
  have hinj : ∀ g g', xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) =
      xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g')) → w g = w g' :=
    fun g g' h => C.σ₂.injective (by rw [hw, hw, h])
  have hleft : ∀ γ ∈ GQ (T.V j T.σ₀), xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) γ)) = 1 := by
    intro γ hγ
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (T.V j T.σ₀)).2.2.1 γ hγ
    rw [← GlobalTheory.NormOneTwist.finQuot_of_isDetRoot hx]
    exact hxi.rat _ _ (GlobalTheory.NormOneTwist.finQuot_incA x) (GlobalTheory.NormOneTwist.normOne_finQuot _)
  have hright : ∀ u : GA D (T.V j T.σ₀), GlobalTheory.Member.FinCong (T.V j T.σ₀) C.d.l₂.M u →
      xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) u)) = 1 := by
    intro u hu
    obtain ⟨k1, -, k3, k4, -⟩ := _root_.GlobalTheory.Member.latHat_eq_hat_and_gram D (T.V j T.σ₀)
    obtain ⟨w', hw', e⟩ := GlobalTheory.CharRead.det_cong_one D.host.F (GlobalTheory.Member.latC (T.V j T.σ₀)) k3 k4 C.d.l₂.M (by omega)
      (finHom (T.V j T.σ₀) u).1 (by rw [← k1]; exact hu)
    refine hxi.cond _ (hno u) ⟨T.Q.l.M • w', AddSubgroup.nsmul_mem _ (GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers D ▸ hw') _, ?_⟩
    rw [smul_smul, mul_comm, ← hlev]
    exact e
  have key := (GlobalTheory.CoverComp.forms_mul_comp D T hL j hj T.σ₀ rfl C hU C.d.l₂.M (by omega) dvd_rfl (Or.inl hWc) w
    (fun h h' hh => hinj _ _ (by rw [hh]))
    (fun γ hγ h => hinj _ _ (by rw [map_mul, map_mul, map_mul, hleft γ hγ, one_mul]))
    (fun u _ hu2 h => hinj _ _ (by rw [map_mul, map_mul, map_mul, hright u hu2, mul_one])) wa n).2 S ?_ φ hφ
  · simpa only [hw] using key
  · intro la _ h
    have hpow : w h ^ m = 1 := C.σ₂.injective (by
      rw [map_pow, hw, map_one, ← Units.val_pow_eq_pow_val, hexp _ (hno h), Units.val_one])
    have hint : IsIntegral ℤ (w h) := IsIntegral.of_pow hm (by rw [hpow]; exact isIntegral_one)
    have := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := C.d.c₂.F) la (⟨w h, hint⟩ : 𝓞 C.d.c₂.F)
    exact this

end GlobalTheory.TwistInt
end

