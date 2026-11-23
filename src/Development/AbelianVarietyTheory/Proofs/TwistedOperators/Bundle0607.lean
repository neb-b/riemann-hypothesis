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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMatrixOfIsLattice
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.MovedAlg

variable {D : D7}

def IsAlgComb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f₀ F : WO S T → ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO S T), (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, (w p).map (infPart D) = 0) ∧
    F = ∑ p, c p • heisO ψ S T (w p) f₀

theorem isAlg_mul {a b : ℂ} (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) : IsAlgebraic ℚ (a * b) := by
  rw [← mem_algebraicClosure_iff] at ha hb ⊢
  exact mul_mem ha hb

section Comb

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem IsAlgComb.zero : IsAlgComb ψ S T f₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, by simp⟩

theorem IsAlgComb.smul {a : ℂ} (ha : IsAlgebraic ℚ a) {F : WO S T → ℂ} (h : IsAlgComb ψ S T f₀ F) :
    IsAlgComb ψ S T f₀ (a • F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := h
  refine ⟨n, fun p => a * c p, w, fun p => isAlg_mul ha (hc p), hw, ?_⟩
  rw [Finset.smul_sum]
  simp only [smul_smul]

theorem IsAlgComb.add {F F' : WO S T → ℂ} (hF : IsAlgComb ψ S T f₀ F) (hF' : IsAlgComb ψ S T f₀ F') :
    IsAlgComb ψ S T f₀ (F + F') := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨m, c', w', hc', hw', rfl⟩ := hF'
  refine ⟨n + m, Fin.append c c', Fin.append w w', fun p => ?_, fun p => ?_, ?_⟩
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simpa using hc q
    · simpa using hc' q
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simpa using hw q
    · simpa using hw' q
  · rw [Fin.sum_univ_add]
    simp

theorem IsAlgComb.finsum : ∀ {n : ℕ} (c : Fin n → ℂ) (F : Fin n → WO S T → ℂ), (∀ p, IsAlgebraic ℚ (c p)) →
    (∀ p, IsAlgComb ψ S T f₀ (F p)) → IsAlgComb ψ S T f₀ (∑ p, c p • F p)
  | 0, _, _, _, _ => by simpa using (IsAlgComb.zero : IsAlgComb ψ S T f₀ 0)
  | n + 1, c, F, hc, hF => by
    rw [Fin.sum_univ_succ]
    exact (IsAlgComb.smul (hc 0) (hF 0)).add (IsAlgComb.finsum _ _ (fun p => hc _) fun p => hF _)

theorem heisO_sum_smul (u : WO S T) {n : ℕ} (c : Fin n → ℂ) (F : Fin n → WO S T → ℂ) :
    heisO ψ S T u (∑ p, c p • F p) = ∑ p, c p • heisO ψ S T u (F p) := by
  funext z
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem IsAlgComb.Heisenberg₂
    (hψ : ∀ u v : WO S T, u.map (infPart D) = 0 → v.map (infPart D) = 0 → IsAlgebraic ℚ (ψ (symplOH S T u v)))
    {u : WO S T} (hu : u.map (infPart D) = 0) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T f₀ F) :
    IsAlgComb ψ S T f₀ (heisO ψ S T u F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  refine ⟨n, fun p => c p * ψ (symplOH S T u (w p)), fun p => u + w p,
    fun p => isAlg_mul (hc p) (hψ _ _ hu (hw p)), fun p => ?_, ?_⟩
  · rw [Matrix.map_add _ (map_add (infPart D)), hu, hw p, add_zero]
  · rw [heisO_sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [GlobalTheory.LinkCompare.heisO_heisO, smul_smul]

end Comb

theorem om_algComb {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X)
    (hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)))
    (t : T) (x : GA D A) (h : GA D WW)
    (h0 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) X.vac)) {F : WO (GlobalTheory.Grid.neg A) WW → ℂ}
    (hF : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F) : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  have e : ∀ p, X.ω t (x, h) (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) =
      heisO W.ψ (GlobalTheory.Grid.neg A) WW (actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm x) h (w p))
        (X.ω t (x, h) X.vac) := fun p =>
    (hX.is.weil t).om_heis ((GlobalTheory.Grid.ofSgn true A).symm x) h (w p) X.vac hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, e]
  exact IsAlgComb.finsum _ _ hc fun p => IsAlgComb.Heisenberg₂ hψ (GlobalTheory.FinApprox.actO_fin _ _ (hw p)) h0

end GlobalTheory.MovedAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExAtAssembly

theorem exAt_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → HostHyp D → R.IsChainW → R.IsThPW → R.ExAt := by
  intro h1 h2 h3 h4 D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hr hH hc hp
  have eP : R.ex_ioP := _root_.GlobalTheory.IndefLinks.exists_ioP_of_realDat D G Pl0 T A Ks R h0 hf hm hp.ωP hp.vP
  have eF : R.ex_thF := _root_.GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak h3 D G Pl0 T A Ks R h0 hf hm hp eP
  exact ⟨_root_.GlobalTheory.Chain.ExItY.ex_ItY_holds h1 h2 D G Pl0 T A Ks R h0 hf hm hH hc, _root_.GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner D G Pl0 T A Ks R h0 hf hm hc,
    _root_.GlobalTheory.Chain.ExIoY.ex_ioY_holds h1 h2 h3 h4 D G Pl0 T A Ks R h0 hf hm hH hc, _root_.GlobalTheory.Twist.LastStepLift.exists_lastStep_lift D G Pl0 T A Ks R h0 hf hm hc,
    GlobalTheory.ProjectedLift.ex_Th_of_chain D G Pl0 T A Ks R h0 hf hm hr, eP, eF,
    _root_.GlobalTheory.Twist.exists_thG_models D G Pl0 T A Ks R h0 hf hm hp.thF eF⟩

end GlobalTheory.ExAtAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.GramOneCompact

theorem isCompact_GinfC_of_gram_eq_one : ∀ (D : D7) (V : HSp D), V.gram = 1 → IsCompact (GinfC V : Set (GA D V)) := by
  intro D V hg
  have hL : (GlobalTheory.SW.stdL D.host.E V.rank).FG ∧ Submodule.span D.host.E
      (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    exact ⟨a, by simp⟩
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.Ker.CongTop.exists_compact V _ hL.1 hL.2
  refine hC.of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) fun k hk => hCm k ?_ (Or.inr hg)
  have hk1 : finHom V k = 1 := hk
  have h1 : GlobalTheory.Ker.fmt V k = GlobalTheory.Ker.fmt V 1 := by
    rw [GlobalTheory.Ker.CongTop.fmt_eq, GlobalTheory.Ker.CongTop.fmt_eq, hk1, map_one]
  rw [h1]
  exact (GlobalTheory.Ker.CongTop.congSub V (GlobalTheory.SW.stdL D.host.E V.rank) 1).one_mem.1

end GlobalTheory.GramOneCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralInvNegXi0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.StairFrameFJ

private theorem isIntegral_sqrtMinusD' (D : D7) : IsIntegral ℤ D.host.sqrtMinusD := by
  refine IsIntegral.of_pow (n := 2) two_pos ?_
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
    unfold Host.sqrtMinusD
    exact D.host.sqd_sq
  rw [hsq]
  refine IsIntegral.neg ?_
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (D.host.d : ℤ)))

theorem isIntegral_inv_neg_xi0 (D : D7) : IsIntegral ℤ (-D.host.xi0)⁻¹ := by

  unfold Host.xi0
  rw [neg_div, neg_neg, one_div, inv_inv]
  refine IsIntegral.mul ?_ (isIntegral_sqrtMinusD' D)
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := ((Ideal.absNorm D.host.ccK : ℕ) : ℤ)))

private theorem mem_integer_of_isIntegral_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {y : k} (hy : IsIntegral ℤ y) : y ∈ 𝒪[k] := by
  have h2 : IsIntegral 𝒪[k] y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact hz ▸ z.2

theorem exists_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {x : D.host.E} (hx : x ≠ 0) (h : IsIntegral ℤ x⁻¹) :
    ∃ u : 𝒪[k], (u : k) * p.pr (incA D x) = 1 := by
  have hy : IsIntegral ℤ (p.pr (incA D x⁻¹)) := h.map ((p.pr.comp (incA D)).toIntAlgHom)
  refine ⟨⟨_, mem_integer_of_isIntegral_int hy⟩, ?_⟩
  show p.pr (incA D x⁻¹) * p.pr (incA D x) = 1
  rw [← map_mul, ← map_mul, inv_mul_cancel₀ hx, map_one, map_one]

theorem exists_frame : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
    (j : Fin (2 * σ + 2 - 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (ϖ : 𝒪[k]),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} ∧
  (∃ u : 𝒪[k], (u : k) * p.pr (incA D (-D.host.xi0)) = 1) ∧
  (∃ u : 𝒪[k], (u : k) * p.pr (incA D (star (-D.host.xi0))) = 1) ∧
  Function.Injective j ∧
  (∀ r i, β.b i (j r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * σ + 2) (by omega) h').a i r))) ∧
  (∀ m, m ∉ Set.range j → ∀ r, ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i r)))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) m = 0) := by
  unfold OnStd All
  intro D hq T L μ₀ hL sc G W M _ F _ σ h' v hv
  obtain ⟨k, _, _, _, _, p, hpv, hpe⟩ := GlobalTheory.LatticeMembershipValuation.exists_splitPoint_at_S0 G.pl hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨β, j, hβ, hj, hcol, horth⟩ := GlobalTheory.LatticeMembershipValuation.exists_stairFrame (p := p) hq hL G hv (2 * σ + 2) (by omega) h'
    hpv hpe hϖ
  have hx0 : D.host.xi0 ≠ 0 := by
    exact GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hs : IsIntegral ℤ (star (-D.host.xi0))⁻¹ := by
    have h1 : IsIntegral ℤ (star (-D.host.xi0)⁻¹) :=
      (isIntegral_inv_neg_xi0 D).map ((starRingEnd D.host.E).toIntAlgHom)
    rwa [star_inv₀] at h1
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, p, β, j, ϖ, hpv, hpe, hβ,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    exists_inv p (neg_ne_zero.2 hx0) (isIntegral_inv_neg_xi0 D),
    exists_inv p (star_ne_zero.2 (neg_ne_zero.2 hx0)) hs, hj, hcol, ?_⟩
  intro m hm r
  have hmr := horth m hm r
  have hf : (fun x => p.pr (incA D x)) = ⇑(p.pr.comp (incA D)) := rfl
  rw [hf, Matrix.map_mul, Matrix.mul_assoc] at hmr
  simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply] using hmr

end GlobalTheory.StairFrameFJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFlipStageIsTensorPlaceDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

theorem canFlip_of_append {γ : List GlobalTheory.SplitFlip.Edge} {l l' : List (ℕ × ℕ)} (h : GlobalTheory.SplitFlip.CanFlip γ (l ++ l')) :
    GlobalTheory.SplitFlip.CanFlip γ l := by
  induction l generalizing γ with
  | nil => exact .nil _
  | cons x l ih =>
    cases h with
    | cons hp h' => exact .cons hp (ih h')

theorem isTensor_flips_take : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (Φ : ch.G.Datum), ∀ w ∈ locPl ch.G t, ∀ k, k ≤ D.R.m ^ 2 → (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w) ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).path ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).tensor := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t Φ w hw k _
  have hL := s.core.lev
  have hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
    obtain ⟨⟨P, -, -⟩, -⟩ := s.size
    have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
      UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
    exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde (hch.guard t)).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, GlobalTheory.SplitFlip.CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    rw [← GlobalTheory.SplitFlip.Grid.alpha_div_beta]
    exact (hg.square i hi j hj).condν
  have hcan : GlobalTheory.SplitFlip.CanFlip (GlobalTheory.SplitFlip.givenPath D.R.m) ((flipOrder D.R.m).take k) := by
    have h := (canFlip_flipOrder D.R.m).1
    rw [← List.take_append_drop k (flipOrder D.R.m)] at h
    exact canFlip_of_append h
  exact isTensor_flips h00.unif h00.cond h00.one_le ((flipOrder D.R.m).take k) (givenStage t w ch.S.B Φ)
    (fun x hx => hν x (List.mem_of_mem_take hx)) hcan (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor

end GlobalTheory.FlipRun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsDoublingFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
open scoped Classical
namespace GlobalTheory.PlacePureFin
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

theorem side {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    (om : Rep σ Y Wd) (h : UA σ Wd.J)
    (hloc : ∀ v, ∀ hh ∈ UAt σ Wd (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, hh)) φ φ₁)
    (S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)))
    (hfix : ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (e : AF F) (he : e * e = e), S₀ ⊆ S →
      (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u * e = 0) →
      (∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * e = 0 ∨ u * e = u) →
      ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
        (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
        om (1, loc e he h) (pure f φ) = pure f φ)
    (f : SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = M.vac v) ∧
      (∀ v, Acts (evFin F v) (om (1, loc (idem F v) (idem_mul_self v) h)) (φ v) (φ₁ v)) ∧
      om (1, h) (pure f φ) = pure f φ₁ := by
  have hvAt : ∀ v, loc (idem F v) (idem_mul_self v) h ∈ UAt σ Wd (evFin F v) := by
    intro v u hu
    show u • (mat (loc (idem F v) (idem_mul_self v) h) - 1) = 0
    rw [mat_loc, phi_sub_one, smul_smul, mul_idem_of_evFin hu, zero_smul]
  choose φ₁ hφ₁SB hφ₁Act using fun v => hloc v _ (hvAt v) (φ v) (hSB v)
  have hN : {v | ¬ φ v = M.vac v}.Finite := hvac
  have hN2 : {v | ¬ M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite := hM.std
  set S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) := S₀ ∪ hN.toFinset ∪ hN2.toFinset with hSdef
  have hS₀ : S₀ ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hφS : ∀ w ∉ S, φ w = M.vac w := fun w hw => by
    by_contra hc; exact hw (Finset.mem_union_left _ (Finset.mem_union_right _ (hN.mem_toFinset.2 hc)))
  have hvacS : ∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := fun w hw => by
    by_contra hc; exact hw (Finset.mem_union_right _ (hN2.mem_toFinset.2 hc))
  have hidem_at : ∀ w v (u : AF F), At (evFin F w) u → w ≠ v → u * idem F v = 0 := by
    intro w v u hu hwv
    apply mul_idem_of_evFin
    rw [← idem_mul_of_at hu, map_mul, evFin_idem, if_neg (Ne.symm hwv), zero_mul]
  have key : ∀ v ∉ S, φ₁ v = φ v := by
    intro v hv
    have hA := hφ₁Act v
    rw [hφS v hv] at hA ⊢
    refine GlobalTheory.T.vacuum_fixed_of_fixes_pureTensors_vacuaOutside F E σ M om v _ S (hM.vac v).1 hvacS (fun f' φ' hSB' hout => ?_) (φ₁ v) hA
    refine hfix S (idem F v) (idem_mul_self v) hS₀ (fun w hw u hu => hidem_at w v u hu (fun e => hv (e ▸ hw)))
      (fun w _ u hu => ?_) f' φ' hSB' hout
    by_cases hwv : w = v
    · subst hwv; right; rw [mul_comm]; exact idem_mul_of_at hu
    · left; exact hidem_at w v u hu hwv
  refine ⟨φ₁, hφ₁SB, ?_, hφ₁Act, ?_⟩
  · filter_upwards [hvac, S.eventually_cofinite_notMem] with v hv hvS
    rw [key v hvS, hv]
  · have heS : idemS F S * idemS F S = idemS F S := idemS_mul_self S
    have heS' : (1 - idemS F S) * (1 - idemS F S) = 1 - idemS F S := by
      rw [sub_mul, one_mul, mul_sub, mul_one, heS, sub_self, sub_zero]
    have horth : idemS F S * (1 - idemS F S) = 0 := by rw [mul_sub, mul_one, heS, sub_self]
    have hdec : h = (S.toList.map fun v => loc (idem F v) (idem_mul_self v) h).prod * loc (1 - idemS F S) heS' h := by
      apply ua_ext
      rw [mat_mul, mat_prod_loc h _ S.nodup_toList, Finset.toList_toFinset, mat_loc, phi_mul_orth horth,
        add_sub_cancel, phi_one]
    have hnot : ∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * idemS F S = 0 := by
      intro w hw u hu
      rw [← idem_mul_of_at hu, mul_comm (idem F w), mul_assoc, idem_mul_idemS_of_notMem hw, mul_zero]
    have hk : om (1, loc (1 - idemS F S) heS' h) (pure f φ) = pure f φ := by
      refine hfix S _ heS' hS₀ (fun w hw u hu => ?_) (fun w hw u hu => Or.inr ?_) f φ hSB hφS
      · calc u * (1 - idemS F S) = (idem F w * u) * (1 - idemS F S) := by rw [idem_mul_of_at hu]
          _ = u * (idem F w - idem F w * idemS F S) := by ring
          _ = 0 := by rw [idem_mul_idemS_of_mem hw, sub_self, mul_zero]
      · rw [mul_sub, mul_one, hnot w hw u hu, sub_zero]
    have hmul : ∀ (a b : UA σ Wd.J) (x : (Fin n × Fin d → AF F) → ℂ), om (1, a * b) x = om (1, a) (om (1, b) x) := by
      intro a b x
      have : ((1 : UA σ Y.J), a * b) = (1, a) * (1, b) := by simp
      rw [this, map_mul]; rfl
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hvac.and hM.std).mono fun v hv => hv.1.trans hv.2
    conv_lhs => rw [hdec]
    rw [hmul, hk, GlobalTheory.T.weilRep_list_prod_distinctPlaces_pureTensor F E σ om (fun v => loc (idem F v) (idem_mul_self v) h) φ φ₁ hSB hφ₁SB hφ₁Act hstd S.toList
      S.nodup_toList f]
    congr 1
    funext v
    by_cases hv : v ∈ S
    · rw [if_pos (Finset.mem_toList.2 hv)]
    · rw [if_neg (mt Finset.mem_toList.1 hv), key v hv]

end GlobalTheory.PlacePureFin
end
end

