module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0424
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddLeLminorSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesDatumMoveToFullRank

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Asm

open Formalism.L2.Indef Formalism.L2.Indef.Tree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jexpU_le_jrec7 (hcut : Formalism.CohomologicalDescent.E.ExCut) {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G]
    [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι) (hN : NumOk P W)
    (hoff : ¬ W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → LIncl B ℓ Z w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w)))
    (hin : W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∃ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam),
      Covers B ℓ Z w X ∧ ∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) :
    B.JexpU ℓ Z w ≤ (W.Jrec7 P (Formalism.EigenvalueLevelCeiling.plc w) : ℚ) := by
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime w
  have hrec := GlobalTheory.exponent_of_record_vs_formulas hcut P hN.1 hN.2.1 ι W hN.2.2.1 _ hp
  by_cases hR : W.WRange P (Formalism.EigenvalueLevelCeiling.plc w)
  · obtain ⟨fr, cj, I, X, hc, hX⟩ := hin hR
    have h1 := _root_.GlobalTheory.ExpTie.lIncl_of_models K G Pl0 B ℓ Z w ι P W hN hp hR fr cj I X hc hX
    have h2 := (_root_.GlobalTheory.ExpTie.jexpU_le_of_lIncl K G Pl0 B ℓ Z w _ h1).2
    rw [hrec.2 hR] at h2
    exact h2
  · have h2 := (_root_.GlobalTheory.ExpTie.jexpU_le_of_lIncl K G Pl0 B ℓ Z w _ (hoff hR)).2
    exact h2.trans (by exact_mod_cast hrec.1 hR)

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem splitPartNumbers_exponent_eq_liftExponent (C CH : ℝ) (t : p.P.T) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) :
    ((R2 p).num (F2 p) C CH).J0 t w j = (((blk p j t).JexpU (lvlL p) (subZ p j t) w : ℚ) : ℝ) := rfl


open Classical in
theorem hasExpBound_at (hcut : Formalism.CohomologicalDescent.E.ExCut) {c : OnConst} (O : Obj p c)
    (hm : O.m = (D.R.m : ℝ)) (hx : O.x = L.sc.x) (heps : O.eps = L.sc.eps) (hT2 : O.T2 = D.host.T2.card)
    (Pj : Fin D.R.m → Par) (Wj : Fin D.R.m → Wts D.what₂.Tau) (hD : ∀ j, Dict L j (Pj j) (Wj j))
    (hN : ∀ j, NumOk (Pj j) (Wj j))
    (hS : ∀ j t w, LIncl (blk p j t) (lvlL p) (subZ p j t) w ((Wj j).JA (Pj j) (Formalism.EigenvalueLevelCeiling.plc w)))
    (hM : ∀ j, ∀ w ∈ p.R.twPl, (Wj j).WRange (Pj j) (Formalism.EigenvalueLevelCeiling.plc w) → ModelAt p j (Pj j) (Wj j) w) (C CH : ℝ) :
    HasExpBound ((R2 p).num (F2 p) C CH) O := by
  constructor
  · intro w _ j
    have h := (_root_.GlobalTheory.ExpTie.jexpU_le_of_lIncl _ _ _ _ _ _ w _ (hS j ((S2 p).μ w) w)).1
    rw [splitPartNumbers_exponent_eq_liftExponent]
    exact_mod_cast h
  refine ⟨fun j l => ((Wj j).Jrec7 (Pj j) l : ℝ), ?_, ?_⟩
  · intro j
    constructor
    · intro l
      exact Nat.cast_nonneg _
    intro Q hQ
    obtain ⟨hHyp, hLarge, hOk, X', A, hRows, hBig⟩ := hN j
    have hcard : Fintype.card D.what₂.Tau = (Pj j).f := by rw [← Nat.card_eq_fintype_card]; exact (hD j).card
    have h := UpperTheory.ExcSet.sum_exponent_log_le hcut D (Pj j) X' A hHyp hLarge hRows hBig D.what₂.Tau (Wj j) hOk hcard (hD j).f
      (hD j).special O.T2
      (by rw [hT2]; exact (hD j).thick) Q hQ
    have hxe : O.xe = (Pj j).L := by rw [(hD j).log]; show O.x ^ O.eps = _; rw [hx, heps]
    have hb : O.b = (Pj j).b := by rw [(hD j).b]; show Real.exp O.xe = _; rw [hxe, (hD j).log]; rfl
    have hm' : O.m = ((Pj j).m : ℝ) := by rw [hm, (hD j).m]
    show _ ≤ 30 * (O.T2 : ℝ) * O.m * O.b * O.xe ^ 2 + 2 * O.m * O.b
    rw [hxe, hb, hm']
    exact h
  · intro w hw j
    have hle := jexpU_le_jrec7 hcut (blk p j (p.R.mu w)) (lvlL p) (subZ p j (p.R.mu w)) w (Pj j) (Wj j) (hN j)
      (fun _ => hS j _ w) (fun hR => hM j w hw hR)
    show (((blk p j (p.R.mu w)).JexpU (lvlL p) (subZ p j (p.R.mu w)) w : ℚ) : ℝ) ≤ ((Wj j).Jrec7 (Pj j) (Formalism.EigenvalueLevelCeiling.plc w) : ℝ)
    exact_mod_cast hle

end Point

end GlobalTheory.ExpTie.Asm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBound
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem facBetween_zero_boundAll : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (f : Lt1 Dw) (k : ℕ), FacBetween Xo la f k 0 (boundAll p (rk f) k) ∧ (k < p → FacBetween Xo la f k 0 0) := by
  intro E _ _ _ H Dw l Xo c p _ la f k
  letI := H.starRing
  have hch : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y) :=
    fun T io y => by
      obtain ⟨C, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
      exact ⟨C⟩
  have hB : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
      0 ≤ nuFacC Ch X f k ∧ nuFacC Ch X f k ≤ ((boundAll p (rk f) k : ℝ) : EReal) ∧ (k < p → nuFacC Ch X f k = 0) := by
    intro T io y Ch X
    have h1 := _root_.GlobalTheory.FGDepth.detDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f)
    refine ⟨h1.1, ?_, fun hk => _root_.GlobalTheory.FGDepth.detDepth_eq_zero_of_lt X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f) hk⟩
    have h2 := h1.2.2
    unfold boundAll
    exact h2
  have hmain : ∀ B : ℝ, (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
      (X : ValExt T p), nuFacC Ch X f k ≤ (B : EReal)) → FacBetween Xo la f k 0 B := by
    intro B hb T io e ho y
    refine ⟨?_, fun _ => ?_⟩
    · rw [EReal.coe_zero]
      exact le_nuFac fun Ch X => (hB T io y Ch X).1
    · obtain ⟨Ch⟩ := hch T io y
      obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
      exact (nuFac_le Ch X f k).trans (hb T io y Ch X)
  refine ⟨hmain _ fun T io y Ch X => (hB T io y Ch X).2.1, fun hk => hmain 0 fun T io y Ch X => ?_⟩
  rw [(hB T io y Ch X).2.2 hk, EReal.coe_zero]

end GlobalTheory.RefSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMemberLieActionFockPlusTrace
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open NumberField MeasureTheory MvPolynomial Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.RealLift GlobalTheory.HoweD

namespace GlobalTheory.HoweD.LieFirstD

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

def swapTD (P Q R S : ι → ℕ) :
    (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) ≃ₗ[ℂ] ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) :=
  PiTensorProduct.congr fun w => GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w)

theorem swapTD_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)))
    (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h : ∀ f, GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) (L' f) =
      L (GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) f))
    (T : ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) :
    swapTD P Q R S (atPl w L' T) = atPl w L (swapTD P Q R S T) := by
  have e : (swapTD P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (swapTD P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, swapTD,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem swapTD_sumPl (L' : ∀ w, Module.End ℂ (Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)))
    (L : ∀ w, Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h : ∀ w f, GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) (L' w f) =
      L w (GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) f))
    (T : ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) :
    swapTD P Q R S (sumPl L' T) = sumPl L (swapTD P Q R S T) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => swapTD_atPl w (L' w) (L w) (h w) T

end Tensor

theorem lieFirstD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUSplitting (adeleClass F) ψ d' (actB (cA σ)) om →
    ∃ c, ActsByD τ A om Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om hCM hψ hfr hΦ hdd hW
  have hfr' : FramedD τ JB JA b a C A := ⟨by rw [mul_comm]; exact hfr.1, hfr.2.2, hfr.2.1⟩
  have hΦ' : IsFockMapD ψ τ d' C A (Φ ∘ₗ (swapTD P Q R S).toLinearMap) := by
    refine ⟨hΦ.1.comp (swapTD P Q R S).injective, fun u hu c hc T => ?_⟩
    have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
    have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
      rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapTD P Q R S T)
    have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
      show schr ψ (d'.e _) = schr ψ (d.e _)
      rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rwa [swapTD_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ)
      (fun w f => GlobalTheory.RealLift.LieFirstPf.swapE_heisOp (c w) f)]
  obtain ⟨c, hA⟩ := GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om hCM hψ hfr' hΦ' hW
  refine ⟨c, fun γ hγ Y hY T => ?_⟩
  have key := hA γ hγ Y hY ((swapTD P Q R S).symm T)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at key
  rwa [swapTD_sumPl (fun w => fockAct2 (R w) (S w) (P w) (Q w) (Y w) + (c w * (Y w).trace) • 1)
    (fun w => fockAct1 (P w) (Q w) (R w) (S w) (Y w) + (c w * (Y w).trace) • 1) (fun w f => by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul,
        GlobalTheory.RealLift.LieFirstPf.swapE_apply, (GlobalTheory.FockSwap.swap_symmetry (R w) (S w) (P w) (Q w)).2.1]),
    LinearEquiv.apply_symm_apply] at key

end GlobalTheory.HoweD.LieFirstD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Degree

variable {k : Type} [Field k] [NumberField k]

end Degree

section Lie

variable {k : Type} [Field k] [NumberField k] {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)}

theorem isEigBasis_iff (τ : E →+* k) : EigenvectorLieDegree.IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) x ↔
    AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ (a : E)) x := Iff.rfl


end Lie

section Point

variable {k : Type} [Field k] [NumberField k]

variable {t : SAB H (Sp k)} {τ τ' : E →+* k} {p q : ℕ}

end Point

section Extension

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] {i : k →+* k'}

variable {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)} {ε : HeightOneSpectrum (𝓞 k') → ℕ}

variable {t : SAB H (Sp k)} {t' : SAB H (Sp k')}

end Extension

end GlobalTheory.FlatDegreeCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitary
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial

namespace GlobalTheory.HoweR

theorem adjZ_Eab_of_isLeft {p q : ℕ} {a b : Ix p q} (h : a.isLeft = b.isLeft) :
    adjZ (Eab a b) = Eab b a := by
  have hs : sameBlock a b := by
    rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
  ext i j
  rw [GlobalTheory.FockAdj.adjZ_apply]
  simp only [Eab, Matrix.single_apply]
  by_cases e : a = j ∧ b = i
  · obtain ⟨rfl, rfl⟩ := e
    simp [hs]
  · have e' : ¬ (b = i ∧ a = j) := fun ⟨h1, h2⟩ => e ⟨h2, h1⟩
    simp [e, e']

theorem isKC_Eab_of_isLeft {p q : ℕ} {a b : Ix p q} (h : a.isLeft = b.isLeft) : IsKC (Eab a b) := by
  intro i j hij
  simp only [Eab, Matrix.single_apply]
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  apply hij
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem fock_locU : ∀ P Q R S : ℕ, LocU (fun a : Ix R S => a.isLeft) (units (fockAct2 P Q R S)) := by
  intro P Q R S t
  classical
  obtain ⟨ι, hι, hinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln P Q R S)
  refine ⟨restrictTotalDegree (Ln P Q R S) ℂ (t.sup totalDegree), fun x hx => ?_, ?_⟩
  · rw [mem_restrictTotalDegree]
    exact Finset.le_sup hx
  refine ⟨inferInstance, fun a b hab u hu => ?_, ((innerₛₗ ℂ).comp ι).compl₂ ι, fun x _ y _ => ?_,
    fun x _ hx => ?_, fun a b hab x _ y _ => ?_⟩
  · exact GlobalTheory.DegKeep.stable_restrict _ (Eab a b) (isKC_Eab_of_isLeft hab) u hu
  · simp [inner_conj_symm]
  · have hx' : ι x ≠ 0 := fun h0 => hx (hinj (h0.trans (map_zero ι).symm))
    have := (re_inner_self_pos (𝕜 := ℂ)).2 hx'
    simpa using this
  · have := (GlobalTheory.FockAdj.fock_adjoints P Q R S _ ι hι).2.2 (Eab a b) x y
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, innerₛₗ_apply_apply, units]
    rw [this, adjZ_Eab_of_isLeft hab]

end GlobalTheory.HoweR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallNoContractionUnitaryUpperLevel
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.FreeBallAt

open GlobalTheory.Up GlobalTheory.Up.BallExPf
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem noContraction_of_rmul (X : DataX E r) {x1 b : Frame X.Ψ r} (hx1 : x1 ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) (h : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X (rmul x1 b)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x1 := by
  intro N hN hop
  refine h N hN fun τ => ?_
  obtain ⟨c, hc0, hc1, hc⟩ := hop τ
  refine ⟨c, hc0, hc1, fun u => ?_⟩
  rw [GlobalTheory.MajInv.maj_rmul X.toData hx1 hb, GlobalTheory.MajInv.maj_rmul X.toData hx1 hb]
  exact hc u

theorem opNormLe_of_ball (hr : 0 < r) (X : Data E r) {x0 z1 : Frame X.Ψ r} {γ : GL (Fin r) E}
    (h0 : IsOrth X x0) (h1 : IsOrth X z1) (h2 : IsOrth X (lact γ z1))
    (hlt : rhX X x0 z1 < 1 / (49 * (r : ℝ) ^ 2))
    (hlt2 : rhX X x0 (lact γ z1) < 1 / (49 * (r : ℝ) ^ 2)) (τ : X.Ψ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.OpNormLe X x0 τ (γ : Matrix (Fin r) (Fin r) E) (Real.exp (1 / (3 * (r : ℝ)))) := by
  intro u
  rw [ModeHalfA.maj_orth X h0, ModeHalfA.maj_orth X h0]
  change ReciprocityTheory.MultiplicativeHeights.normSq _ ≤ _ * ReciprocityTheory.MultiplicativeHeights.normSq _
  have hk := ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_nonneg hr
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  have hu1 : IsUnit (mat z1 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X z1 h1 τ)
  have b1 := (frame_bound hr X h0 h1 hlt τ ((mat x0 τ)⁻¹ *ᵥ u)).1
  have b2 := (frame_bound hr X h0 h2 hlt2 τ ((mat z1 τ)⁻¹ *ᵥ u)).2
  have e : mat (lact γ z1) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat z1 τ := rfl
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv_cancel_right _ _ hu] at b1
  rw [e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu1,
    ← Matrix.mulVec_mulVec] at b2
  have hn : 0 ≤ ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ u) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : ReciprocityTheory.MultiplicativeHeights.ballRatio r ^ 2 ≤ Real.exp (1 / (3 * (r : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hk (ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_le hr) 2
  calc _ ≤ _ := b2
    _ ≤ _ := mul_le_mul_of_nonneg_left b1 hk
    _ = ReciprocityTheory.MultiplicativeHeights.ballRatio r ^ 2 * ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ u) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hE hn

theorem freeBall_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g → X.Γ ≤ G → (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, IsUStab X.Gm X.Λ γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∃ x0 : Frame X.Ψ r, IsOrth X.toData x0 ∧ (∃ b ∈ Bor X.Ψ r, x = rmul x0 b) ∧ GlobalTheory.Up.FreeBall X.toData G x0 (1 / (49 * (r : ℝ) ^ 2)) := by
  intro E _ _ _ r X G g hsp hg hΓ hL' hΛ hU x hx hNC
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X.toData x hx
  have hx1 : x1 ∈ X.dom := IW.orth_mem_dom X.toData x1 h1
  have hNC1 := noContraction_of_rmul X hx1 hb hNC
  refine ⟨x1, h1, ⟨b, hb, rfl⟩, hΓ, hΛ, fun γ hγ hne z hz hlt => ?_⟩
  by_contra hlt2
  rw [not_le] at hlt2
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have := rhX_nonneg h1 hz
    simp at hlt
    linarith
  obtain ⟨z1, hz1, b', hb', rfl⟩ := ortho_holds r X.toData z hz
  rw [FundSetPf.lact_rmul, rhX_rmul _ _ hb'] at hlt2
  rw [rhX_rmul _ _ hb'] at hlt
  have h2 := isOrth_lact_of_isUStab (hΛ γ hγ) hz1
  exact hne (_root_.GlobalTheory.SmallElement.smallElement E r X g hsp hg G hL' hU x1 hx1 hNC1 γ hγ
    (opNormLe_of_ball hr X.toData h1 hz1 h2 hlt hlt2))

end GlobalTheory.FreeBallAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorEqTranslateKernelDatum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.FreeBlockMove

theorem vecFree_translate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∃ φ', VecOf R i Q (omegaFree R i Q ξR y₀) φ' ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ' = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i ξ χ ξR Q ω φ hK p hp hξ hV y₀ hy₀
  obtain ⟨φ₁, hφ₁, k₁, hk₁, c₁, m, e₁, i₁, i₁', c₁0, L₁⟩ := _root_.GlobalTheory.FreeBlockTwist.vecFree_base_translate D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK p hp hξ hV
  obtain ⟨φ', hφ', k₂, hk₂, c₂, e₂, i₂, i₂', c₂0, L₂⟩ := _root_.GlobalTheory.TypeMove.vecFree_typeMove D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK y₀ hy₀ φ₁ hφ₁
  refine ⟨φ', hφ', k₂ * k₁, mul_mem hk₂ hk₁, c₂ * c₁, m, ?_, ?_, ?_, mul_ne_zero c₂0 c₁0, ?_⟩
  · have hm : ((k₂ * k₁, (1 : GA D (Wc D i))) : GA D (Vc D i) × GA D (Wc D i)) = (k₂, 1) * (k₁, 1) := by
      simp
    rw [e₂, e₁, hm, map_mul ω, Module.End.mul_apply, map_smul, smul_smul, map_mul D.what₂.embLL]
  · have := i₂.mul i₁
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  · have := i₂'.mul i₁'
    simpa [mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  · intro h hh w hw
    have := L₁ (h * k₂) (mul_mem hh hk₂) w (L₂ h hh w hw)
    simpa [mul_assoc] using this

end GlobalTheory.FreeBlockMove
end

