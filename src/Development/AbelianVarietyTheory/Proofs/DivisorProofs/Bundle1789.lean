module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import GroundTheory.AutomorphicForms.MeasuresModulus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineMultipleLeFamilyThreshold
section
namespace GlobalTheory.HodgeMultNum

theorem nat_bound (r f T : ℕ) (hr : 100 ≤ r) (hf : 5 ≤ f) (hT : 11 * (f * r.choose 2) ^ 2 ≤ T) :
    2 * r + 50 * r ^ 2 * (f * (r * r / 4)) + 2 ≤ T := by
  have hq : 4 * (r * r / 4) ≤ r * r := Nat.mul_div_le (r * r) 4
  have hc : 2 * r.choose 2 = r * (r - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 100 := ⟨r - 100, by omega⟩
  have h1 : s + 100 - 1 = s + 99 := by omega
  rw [h1] at hc
  set q := (s + 100) * (s + 100) / 4
  set c := (s + 100).choose 2
  have key : 4 * (2 * (s + 100) + 50 * (s + 100) ^ 2 * (f * q) + 2) ≤ 4 * (11 * (f * c) ^ 2) := by
    have e1 : 4 * (11 * (f * c) ^ 2) = 11 * f ^ 2 * ((s + 100) * (s + 99)) ^ 2 := by rw [← hc]; ring
    rw [e1]
    have e2 : 4 * (2 * (s + 100) + 50 * (s + 100) ^ 2 * (f * q) + 2) = 8 * (s + 100) + 8 + 50 * (s+100)^2 * f * (4 * q) := by ring
    rw [e2]
    have h3 : 50 * (s+100)^2 * f * (4 * q) ≤ 50 * (s+100)^2 * f * ((s+100)*(s+100)) := Nat.mul_le_mul_left _ hq
    have h4 : 8 * (s + 100) + 8 + 50 * (s+100)^2 * f * ((s+100)*(s+100)) ≤ 11 * f ^ 2 * ((s + 100) * (s + 99)) ^ 2 := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
      ring_nf
      nlinarith [Nat.zero_le (s * g), Nat.zero_le (s * g ^ 2), Nat.zero_le (s ^ 2 * g), Nat.zero_le (s ^ 2 * g ^ 2),
        Nat.zero_le (s ^ 3 * g), Nat.zero_le (s ^ 3 * g ^ 2), Nat.zero_le (s ^ 4 * g), Nat.zero_le (s ^ 4 * g ^ 2),
        Nat.zero_le (s ^ 2), Nat.zero_le (s ^ 3), Nat.zero_le (s ^ 4), Nat.zero_le (g ^ 2)]
    omega
  omega

theorem five_le_of_pow (r f : ℕ) (hr : 100 ≤ r) (h : (r : ℝ) / 2 * (7 / 8 : ℝ) ^ f ≤ 1 / 16) : 5 ≤ f := by
  by_contra hf
  push_neg at hf
  have h1 : (7 / 8 : ℝ) ^ 4 ≤ (7 / 8 : ℝ) ^ f := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (100 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith [pow_pos (show (0:ℝ) < 7/8 by norm_num) f]

end GlobalTheory.HodgeMultNum

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn

theorem GlobalTheory.HodgeMultNum.hodgeMult_le_TO : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x →
    ∀ ι : Fm.Ix x, 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * ((Fm.D x ι).R.r * (Fm.D x ι).R.r / 4)) + 2 ≤
      (Fm.parT x hx ι).TO := by
  refine Closed.imp _root_.GlobalTheory.BadNumOnto.badShare_numbers_onto fun Fm _ _ H => ?_
  obtain ⟨x0, H⟩ := H
  refine ⟨x0, fun x hx h0 ι => ?_⟩
  obtain ⟨hr, -, hE, hk⟩ := H x hx h0 ι
  obtain ⟨hg, hsum⟩ := hk 0
  set D := Fm.D x ι
  set g : ℝ := (D.host.g 0 : ℝ)
  have hg1 : (4096 : ℝ) ≤ g := by simp only [g]; exact_mod_cast hg
  have hlogg : 0 ≤ Real.log g := Real.log_nonneg (by linarith)
  have hr' : (100 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast hr
  have hlogr : 0 ≤ Real.log (D.R.r : ℝ) := Real.log_nonneg (by linarith)
  have hfpos : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hmpos : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ 3 * (D.R.f : ℝ) / g := by positivity
  have hB : 0 ≤ 23 * (D.R.f : ℝ) * Real.log g / Real.sqrt g := by positivity
  have hC : 0 ≤ 2 * (D.R.f : ℝ) * (D.R.m : ℝ) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) +
      (1 + Real.log (D.R.r : ℝ)) / (g - 1)) := by
    have : 0 ≤ g - 1 := by linarith
    positivity
  have hE' : 0 ≤ Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := (Real.exp_pos _).le
  have hP : (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f ≤ 1 / 16 := by linarith
  have hf := GlobalTheory.HodgeMultNum.five_le_of_pow _ _ hr hP
  have hT := (Fm.parT x hx ι).TO_11D2
  rw [(Fm.parT x hx ι).Dp_eq] at hT
  exact GlobalTheory.HodgeMultNum.nat_bound _ _ _ hr hf hT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigenStatement
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_action_unit_character_eigen : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ ν : (AE D)ˣ →* Circle, HasFinPart ν⁻¹ P.W.chV' P.W.ep' → KillsCong ν 𝔪 →
  ∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a, k ∈ intG D P.a → P.W.Om k 1 P.e0 = unitChar ν e (matE k) • P.e0 := by
  first | exact @GlobalTheory.StdRead.CharVal.om_vac_eq | exact GlobalTheory.StdRead.CharVal.om_vac_eq | (intros; apply GlobalTheory.StdRead.CharVal.om_vac_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompSymm
section
noncomputable section

open MeasureTheory
open scoped Matrix Pointwise NNReal

namespace GlobalTheory.ChangeVarPi

theorem map_symm_eq_smul (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι]
    (μ : Measure (ι → k)) [μ.IsAddHaarMeasure] (M : (ι → k) ≃ₗ[k] (ι → k)) :
    μ.map M.symm = (distribHaarChar k (LinearEquiv.det M)) • μ := by
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : Continuous M.symm := (M.symm : (ι → k) →ₗ[k] (ι → k)).continuous_on_pi
  ext s hs
  rw [Measure.map_apply hc.measurable hs, Measure.smul_apply, ← GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq,
    ENNReal.smul_def, smul_eq_mul, distribHaarChar_mul μ M s]
  have : (M.symm : (ι → k) → (ι → k)) ⁻¹' s = M • s := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      exact ⟨M.symm x, h, by simp [LinearEquiv.smul_def]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [LinearEquiv.smul_def] using hy
  rw [this]

end GlobalTheory.ChangeVarPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactFiniteAdeleAnnihilatorStdChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.AnnCompactStdChar

theorem isCompact_annihilator_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F | ∀ y ∈ L, ψ (pairA D.host.F 0 (x ⬝ᵥ y)) = 1} := by
  intro D ψ hψ κ _ L hL
  exact GlobalTheory.AnnCompactStd.isCompact_annihilator D.host.F ψ (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) κ L hL

end GlobalTheory.AnnCompactStdChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantOfModular
section
noncomputable section

open GlobalTheory.WeilM MeasureTheory MeasureTheory.Measure
open scoped Matrix NNReal

namespace GlobalTheory.ParAvg

theorem isMulRightInvariant_of_modular {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (h : ∀ g : G, modularCharacterFun g = 1) : μ.IsMulRightInvariant :=
  ⟨fun g => by rw [map_right_mul_eq_modularCharacterFun_smul μ g, h g, one_smul]⟩

theorem modularCharacterFun_GL {r : ℕ} {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    [LocallyCompactSpace (GL (Fin r) E)] (a : GL (Fin r) E) : modularCharacterFun a = 1 := by
  borelize (GL (Fin r) E)
  refine GlobalTheory.SplitFlip.hom_eq_one_of_center (modularCharacter : GL (Fin r) E →* ℝ≥0) (fun z hz => ?_) a
  change modularCharacterFun z = 1
  have e : map (fun x : GL (Fin r) E => x * z) (haar : Measure (GL (Fin r) E)) = haar := by
    rw [show (fun x : GL (Fin r) E => x * z) = fun x => z * x from funext fun x => (hz x).symm,
      map_mul_left_eq_self]
  rw [modularCharacterFun_eq_haarScalarFactor (haar : Measure (GL (Fin r) E)) z]
  simp only [e, haarScalarFactor_self]

end GlobalTheory.ParAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameAut

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame

section Op

variable (K : Type) [CommRing K] (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)

def wtOp (g : ι → GL (Fin n) K) : Module.End K (NablaT K n mu) :=
  ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : Kˣ) : K) • grp K n mu g

theorem wtOp_apply (g : ι → GL (Fin n) K) (u : NablaT K n mu) :
    wtOp K n mu sh g u = ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : Kˣ) : K) • grp K n mu g u := rfl

theorem wtOp_one : wtOp K n mu sh 1 = 1 := by
  simp [wtOp, grp]

theorem wtOp_mul (g h : ι → GL (Fin n) K) : wtOp K n mu sh (g * h) = wtOp K n mu sh g * wtOp K n mu sh h := by
  simp only [wtOp, grp, map_mul, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, smul_mul_smul_comm]

def wtHom : (ι → GL (Fin n) K) →* Module.End K (NablaT K n mu) where
  toFun := wtOp K n mu sh
  map_one' := wtOp_one K n mu sh
  map_mul' := wtOp_mul K n mu sh

end Op

end GlobalTheory.FrameAut

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL

namespace GlobalTheory.FrameAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def labOf (j : Fin D.R.m) (t : p.P.T) (Q : (blk p j t).Pl) : HeightOneSpectrum (𝓞 D.host.E) := Formalism.DivisionValues.conjPl (plOf p j t Q)

def IsSystemOf (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} {F : Frame l D.what₂.Tau N} {e0 : D.what₂.LL →+* PadicAlgCl l}
    {ix : F.I → (blk p j t).Pl × ℕ} {inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)} (T : Tied p j t F e0 ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (π : Submodule ℂ (UA D.host.E N → ℂ)) : Prop :=
  IsAutRepU π ∧
  (∀ τ, ∃ lam : DomWeight N, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
    HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
  (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
  ∀ Q : (blk p j t).Pl, IsUnramU π (labOf p j t Q) ∧
    ∃ (σ : SmIrr (GL (Fin N) ((labOf p j t Q).adicCompletion D.host.E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU N (labOf p j t Q)) ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype) σ.ρ ∧
      GlobalTheory.LFun.HasSatGL (labOf p j t Q) σ.ρ S ∧
      ∀ i, (ix i).1 = Q → T.io (θ i) = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E (labOf p j t Q)) N S (ix i).2

def PlacesOk (j : Fin D.R.m) (t : p.P.T) (l : ℕ) : Prop :=
  (∀ Q : (blk p j t).Pl, IsSplitAt (labOf p j t Q) ∧
    (labOf p j t Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j t Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
    Ideal.absNorm (labOf p j t Q).asIdeal = (blk p j t).q Q ∧
    (((l : ℕ) : 𝓞 D.host.E) ∈ (labOf p j t Q).asIdeal ↔ ((l : ℕ) : 𝓞 D.host.E) ∈ (plOf p j t Q).asIdeal)) ∧
  {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
    ¬ ∃ Q : (blk p j t).Pl, ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t Q).asIdeal ∧ labOf p j t Q = v}.Finite ∧
  ∀ ν ∈ (blk p j t).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j t).q Q : ℝ) ^ ((blk p j t).n - (blk p j t).t)


open Classical in
def AutAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  PlacesOk p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) ∧
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π, IsSystemOf p j (p.R.mu w) T mu θ π

end GlobalTheory.FrameAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBump
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.KirSemi

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem gl_af_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w => ?_))
  exact congrArg (fun x : GL (Fin a) (w.adicCompletion E) => x.1 i j) (H w)

theorem map_loc_fin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comm_of_supp (S : Finset (HeightOneSpectrum (𝓞 E))) {s t : GA E a} (hs : s ∈ supS (E := E) (a := a) S)
    (h1 : GeneralLinearGroup.map (pInf E) t = 1)
    (h2 : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) : s * t = t * s := by
  apply ga_ext
  · simp [map_mul, h1]
  · apply gl_af_ext
    intro w
    simp only [map_mul, map_loc_fin]
    by_cases hw : w ∈ S
    · rw [h2 w hw]; simp
    · rw [hs w hw]; simp

theorem supS_mul (S : Finset (HeightOneSpectrum (𝓞 E))) {x y : GA E a} (hx : x ∈ supS (E := E) (a := a) S)
    (hy : y ∈ supS (E := E) (a := a) S) : x * y ∈ supS (E := E) (a := a) S := by
  intro w hw
  rw [map_mul, hx w hw, hy w hw, one_mul]

theorem whit_rt (F : GA E a → ℂ) (h g : GA E a) : whit (fun y => F (y * h)) g = whit F (g * h) := by
  simp only [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker, mul_assoc]

theorem ratGL_scalar_val (α : Eˣ) :
    ((ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) : GA E a) :
      Matrix (Fin a) (Fin a) (Ad E)) = Matrix.scalar (Fin a) (algebraMap E (Ad E) (α : E)) := by
  ext i j
  by_cases h : i = j <;> simp [ratGL, Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem aut_central {φ : Sm E a} (hφ : IsAutForm φ) (α : Eˣ) (g : GA E a) :
    φ.1 (g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α)) = φ.1 g := by
  have hc : g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) =
      ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) * g := by
    apply Units.ext
    simp only [Units.val_mul, ratGL_scalar_val]
    exact ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _)).symm
  rw [hc, hφ.left]

theorem exists_mirabolic_nonzero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ ψ ∈ π.V, (∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit ψ.1 p ≠ 0) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, ψ.1 (g * k) = ψ.1 g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit ψ.1 (x * t) = c * GlobalTheory.JSW.whit ψ.1 x := by
  intro E _ _ _ m S π φ hφ ⟨x, hxS, hx⟩
  have haut : IsAutForm φ := (π.cusp φ hφ).1
  set xf := GeneralLinearGroup.map (pFin E) x with hxf
  obtain ⟨p0, ρ, k, hp0, hy⟩ := _root_.GlobalTheory.IwasawaLast.iwasawa_lastRow E m (GeneralLinearGroup.map (pInf E) x)
  let sc : (Cinf E)ˣ →* GL (Fin (m + 1)) (Cinf E) :=
    Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom
  have hsc : Continuous sc := by
    apply Continuous.units_map
    show Continuous (fun c : Cinf E => Matrix.scalar (Fin (m + 1)) c)
    simp only [Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  let ζ : (Cinf E)ˣ → ℂ := fun c =>
    whit φ.1 (infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf)
  have hζc : Continuous ζ :=
    (_root_.GlobalTheory.JSW.continuous_whit_infGL E (m + 1) φ haut _ _).comp (hsc.mul continuous_const)
  have hζρ : ζ ρ ≠ 0 := by
    have hx' : infGL E (m + 1) p0 * infGL E (m + 1) (sc ρ * Unitary.toUnits k) * finGL E (m + 1) xf = x := by
      rw [← map_mul, ← mul_assoc]
      rw [show p0 * sc ρ * Unitary.toUnits k = GeneralLinearGroup.map (pInf E) x from hy.symm]
      exact infGL_mul_finGL x
    show whit φ.1 _ ≠ 0
    rw [hx']
    exact hx
  obtain ⟨β, hβ⟩ := _root_.GlobalTheory.UnitsDense.exists_unit_mem_open E {c | ζ c ≠ 0} (isOpen_ne_fun hζc continuous_const) ⟨ρ, hζρ⟩
  set c := Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β with hc
  let zE : GL (Fin (m + 1)) E := Units.map (Matrix.scalar (Fin (m + 1)) : E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) E).toMonoidHom β⁻¹
  set s := infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf with hs
  have hcen : ∀ g : GL (Fin (m + 1)) (Cinf E), sc c * g = g * sc c := by
    intro g
    apply Units.ext
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _
  have hzinf : GeneralLinearGroup.map (pInf E) (ratGL E (m + 1) zE) = (sc c)⁻¹ := by
    have hci : (sc c)⁻¹ = sc (Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹) := by
      simp only [hc, map_inv]
    rw [hci]
    apply Units.ext
    show ((ratGL E (m + 1) zE : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map (pInf E) =
      Matrix.scalar (Fin (m + 1)) (((Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹ : (Cinf E)ˣ)) : Cinf E)
    rw [ratGL_scalar_val]
    simp [Matrix.scalar_apply, Matrix.diagonal_map]
    funext v
    simp [pInf_algebraMap, map_inv₀]
  set z := GeneralLinearGroup.map (pFin E) (ratGL E (m + 1) zE) with hz
  have hsz : s * ratGL E (m + 1) zE = infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z) := by
    apply ga_ext
    · simp only [hs, map_mul, pInf_infGL, hzinf]
      simp
      rw [hcen]; group
    · simp [hs, hz, mul_assoc]
  let ψ : Sm E (m + 1) := act (Op.cpt k) (act (Op.fin (xf * z)) φ)
  have hψV : ψ ∈ π.V := π.stable _ _ (π.stable _ _ hφ)
  have hψ : ∀ g, ψ.1 g = φ.1 (g * s) := by
    intro g
    have h0 : ψ.1 g = φ.1 (g * infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z)) := rfl
    rw [h0, mul_assoc, ← hsz, ← mul_assoc, aut_central haut β⁻¹]
  have hψf : ψ.1 = fun g => φ.1 (g * s) := funext hψ
  have hsS : s ∈ supS (E := E) (a := (m + 1)) S := by
    intro w hw
    rw [← map_loc_fin, hs, map_mul, pFin_infGL, pFin_finGL, one_mul, hxf, map_loc_fin]
    exact hxS w hw
  refine ⟨ψ, hψV, ⟨infGL E (m + 1) p0, ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro w hw
    rw [← map_loc_fin]
    simp
  · intro j
    have h1 : pInf E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        (p0 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Cinf E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j)
        (pInf_infGL (E := E) p0)
    have h2 : pFin E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        ((1 : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Af E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j)
        (pFin_infGL (E := E) p0)
    rw [hp0 j] at h1
    apply ad_ext
    · rw [h1]; split_ifs <;> simp
    · rw [h2]; split_ifs with h <;> simp [Matrix.one_apply, h, eq_comm]
  · rw [hψf, whit_rt]
    have : infGL E (m + 1) p0 * s = infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf := by
      rw [hs, mul_assoc]
    rw [this]
    exact hβ
  · intro k' h1 h2 hk g
    rw [hψ, hψ, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc, hk]
  · intro t c' h1 h2 hrel y hy
    rw [hψf, whit_rt, whit_rt, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc]
    exact hrel (y * s) (supS_mul S hy hsS)

theorem kirillov_semilocal_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ t : GA E (m + 1), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ g, φ.1 (g * t) = φ.1 g) → ∀ g, F (g * t) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ m S b hb hC hU hsm π φ hφ hx
  obtain ⟨ψ, hψ, hp, hk, hrel⟩ := exists_mirabolic_nonzero E m S π φ hφ hx
  obtain ⟨F, hF, hFb, hFU, hFk, hFrel⟩ := GlobalTheory.T.kirillov_semilocal_mirabolic_whittaker E m S b hb hC hU hsm π ψ hψ hp
  exact ⟨F, hF, hFb, hFU, fun k h1 h2 h3 => hFk k h1 h2 (hk k h1 h2 h3),
    fun t c h1 h2 h3 => hFrel t c h1 h2 (hrel t c h1 h2 h3)⟩

end GlobalTheory.JSW.KirSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroupStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityW'.locality | exact GlobalTheory.WeilLocalityW'.locality | (intros; apply GlobalTheory.WeilLocalityW'.locality <;> assumption)
end

