module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitCharEqOfNatCong
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingMellin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareAgree.LineDerFun

theorem conjugateUnitaryAdelicIso_map_one {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem algebraicDatum_eq_sum_pureTensors_vacua {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Φ = ∑ i, pure (f i) (φ i) := by
  rw [algD, Submodule.mem_span_set'] at hΦ
  obtain ⟨m, c, g, rfl⟩ := hΦ
  choose f φ hf hφ hv hg using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hg i]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

end GlobalTheory.SquareAgree.LineDerFun


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardPairFirstInvariantCongruenceOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdFstInv

theorem mul_sub_mem {R : Type} [CommRing R] (O : Subring R) (c : R) {b a : ℕ} (Z : Matrix (Fin b) (Fin b) R)
    (hZ : ∀ i j, ∃ w ∈ O, Z i j - (1 : Matrix (Fin b) (Fin b) R) i j = c * w)
    (Y : Matrix (Fin b) (Fin a) R) (hY : ∀ i j, Y i j ∈ O) (i : Fin b) (j : Fin a) :
    ∃ w ∈ O, (Z * Y) i j - Y i j = c * w := by
  choose w hwO hw using hZ
  refine ⟨∑ k, w i k * Y k j, O.sum_mem fun k _ => O.mul_mem (hwO i k) (hY k j), ?_⟩
  have hsplit : (Z * Y) i j - Y i j = ∑ k, (Z i k - (1 : Matrix (Fin b) (Fin b) R) i k) * Y k j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.one_mul]
  rw [hsplit, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hw i k, mul_assoc]

theorem mem_iff {R : Type} [CommRing R] (O : Subring R) (J : Ideal O) (N : ℕ) (hN : (N : O) ∈ J) {p q w : R}
    (hp : p ∈ O) (hw : w ∈ O) (h : q - p = (N : R) * w) :
    (∃ h : q ∈ O, (⟨q, h⟩ : O) ∈ J) ↔ ∃ h : p ∈ O, (⟨p, h⟩ : O) ∈ J := by
  have hq : q ∈ O := by
    have e : q = p + (N : R) * w := by linear_combination h
    rw [e]
    exact O.add_mem hp (O.mul_mem (natCast_mem O N) hw)
  have key : (⟨q, hq⟩ : O) = ⟨p, hp⟩ + (N : O) * ⟨w, hw⟩ := by
    apply Subtype.ext
    show q = p + ((N : O) : R) * w
    rw [show ((N : O) : R) = (N : R) from map_natCast O.subtype N]
    linear_combination h
  have hNw : (N : O) * ⟨w, hw⟩ ∈ J := J.mul_mem_right _ hN
  constructor
  · rintro ⟨_, hJ⟩
    refine ⟨hp, ?_⟩
    rw [key] at hJ
    exact (J.add_mem_iff_left hNw).1 hJ
  · rintro ⟨_, hJ⟩
    refine ⟨hq, ?_⟩
    rw [key]
    exact J.add_mem hJ hNw

theorem fixed_mul {R : Type} [CommRing R] {b a : ℕ} (e : R) (M : Matrix (Fin b) (Fin b) R) (x : Matrix (Fin b) (Fin a) R)
    (H : ∀ i j, e * x i j = x i j) (i : Fin b) (j : Fin a) : e * (M * x) i j = (M * x) i j := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, H k j]

theorem fixed_iff {R : Type} [CommRing R] {b a : ℕ} (e : R) (M : GL (Fin b) R) (P : Matrix (Fin a) (Fin a) R) (hP : P = 1)
    (x : Matrix (Fin b) (Fin a) R) :
    (∀ i j, e * (M.val * x * P) i j = (M.val * x * P) i j) ↔ ∀ i j, e * x i j = x i j := by
  subst hP
  simp only [Matrix.mul_one]
  constructor
  · intro h i j
    have hx : x = (M⁻¹).val * (M.val * x) := by
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [hx]
    exact fixed_mul e _ _ h i j
  · intro h i j
    exact fixed_mul e _ _ h i j

variable {D : D7}

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V)⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [inv_one, map_one, Units.val_one]

theorem actO_neg_one (A WW : HSp D) (κ : GA D WW) (x : WO A WW) :
    actO (GlobalTheory.Grid.neg A) WW 1 κ x = actO A WW 1 κ x := by
  unfold actO
  rw [mt_one, mt_one]

theorem isHalf_iff (A WW : HSp D) (κ : GA D WW) (e : AE D) (x : WO A WW) :
    IsHalf e (actO A WW 1 κ x) ↔ IsHalf e x := by
  unfold IsHalf actO
  exact fixed_iff e (matHom WW κ) _ (mt_one A) x

theorem frMapO_eq {A WW : HSp D} (βA : GL (Fin A.rank) (Lev.EAf D)) {βW : GL (Fin WW.rank) (Lev.EAf D)}
    {κ : GA D WW} {z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hz : Formalism.L2.DIV.frGL βW z = Lev.finE WW κ) (x : WO A WW) :
    frMapO A WW βA βW (actO A WW 1 κ x) =
      ((intGL D.host.F D.host.E _ z⁻¹)⁻¹).val * frMapO A WW βA βW x *
        (intGL D.host.F D.host.E _ (1 : GL (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))).val := by
  have h1 := GlobalTheory.FrameRed.frMapO_actO (βS := βA) (βT := βW) (g := (1 : GA D A)) (h := κ⁻¹)
    (y := 1) (z := z⁻¹) (by rw [map_one, map_one]) (by rw [map_inv, map_inv, hz]) x
  rw [inv_one, inv_inv] at h1
  exact h1

set_option maxHeartbeats 1600000 in
theorem frMapO_eq' {A WW : HSp D} (βA : GL (Fin A.rank) (Lev.EAf D)) {βW : GL (Fin WW.rank) (Lev.EAf D)}
    {κ : GA D WW} {z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hz : Formalism.L2.DIV.frGL βW z = Lev.finE WW κ) (x : WO A WW) :
    frMapO A WW βA βW (actO A WW 1 κ x) = (intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x := by
  rw [frMapO_eq βA hz x, map_inv (intGL D.host.F D.host.E WW.rank), inv_inv,
    map_one (intGL D.host.F D.host.E A.rank), Units.val_one, Matrix.mul_one]

theorem topL_int {b a : ℕ} (k : ℕ) {Y : Matrix (Fin b) (Fin a) (Lev.EAf D)} (hY : IsIntM (D := D) Y) :
    IsIntM (D := D) (topL k Y) := by
  intro i j
  unfold topL
  split_ifs with hij
  · exact hY _ _
  · exact zero_mem _

theorem topL_sub {R : Type} [CommRing R] (O : Subring R) (c : R) {b a : ℕ} (k : ℕ) {Y Y' : Matrix (Fin b) (Fin a) R}
    (h : ∀ i j, ∃ w ∈ O, Y' i j - Y i j = c * w) (i j : Fin k) :
    ∃ w ∈ O, topL k Y' i j - topL k Y i j = c * w := by
  unfold topL
  split_ifs with hij
  · exact h _ _
  · exact ⟨0, O.zero_mem, by rw [sub_self, mul_zero]⟩

set_option maxHeartbeats 1600000 in
theorem stdFst_actO : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  intro D A WW ν e Sf hSf I βA βW N hN hNI hNS hν κ z hz hz1 x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [actO_neg_one, isHalf_iff, frMapO_eq' βA hz x]
  have hInt : IsIntM (D := D) ((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) ↔
      IsIntM (D := D) (frMapO A WW βA βW x) := by
    have h2 := GlobalTheory.FrameRed.isIntM_iff (D := D) z⁻¹
      (1 : GL (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (frMapO A WW βA βW x)
    rwa [map_inv (intGL D.host.F D.host.E WW.rank), inv_inv, map_one (intGL D.host.F D.host.E A.rank),
      Units.val_one, Matrix.mul_one] at h2
  by_cases hM : IsIntM (D := D) (frMapO A WW βA βW x)
  · have hc : ∀ i j, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
        ((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) i j - frMapO A WW βA βW x i j =
          (N : Lev.EAf D) * w :=
      mul_sub_mem (Formalism.L2.Herm.intAf D.host.F D.host.E) (N : Lev.EAf D) (intGL D.host.F D.host.E _ z).val hz1 _ hM
    have hNJ : ((N : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ Formalism.L2.DIV.idS D.host.F I := by
      rw [← map_natCast (Formalism.L2.DIV.oToS D.host.F D.host.E) N]
      exact Ideal.mem_map_of_mem _ hNI
    have hId : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) i j) ↔
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA βW x i j) := fun i j => by
      obtain ⟨w, hw, hq⟩ := hc i j
      exact GlobalTheory.StdFstInv.mem_iff _ _ N hNJ (hM i j) hw hq
    have hU := GlobalTheory.UnitCharCong.unitChar_eq_of_natCong D ν e Sf hSf N hN hNS hν _ _ (topL_int A.rank hM)
      (topL_sub _ _ A.rank hc)
    rw [hU]
    have hcond := and_congr (Iff.rfl (a := IsHalf e x)) (and_congr hInt
      (forall_congr' fun (i : Fin WW.rank) => forall_congr' fun (j : Fin A.rank) =>
        imp_congr (Iff.rfl (a := A.rank ≤ (i : ℕ))) (hId i j)))
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hcond.1 h1) h2
    · exact absurd (hcond.2 h2) h1
    · rfl
  · rw [if_neg (fun h => hM (hInt.1 h.2.1)), if_neg (fun h => hM h.2.1)]

end GlobalTheory.StdFstInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestChoicesExistLargeCoeffFieldAdelicData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

noncomputable section

theorem GlobalTheory.RowEx.dat_choice_exists : GlobalTheory.RowEx.ExField → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLg fun K B f T => ∀ (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (L : SizeData₂ (w.st Z).toD7), L.sc = K.s → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 → ∃ ch : GlobalTheory.RowTest.Choice z.R.toRealDat, ch.Is ∧ ch.AtScale CF L.sc.b ∧ ch.FieldOK := by
  classical
  intro hE
  obtain ⟨CF0, hE⟩ := hE
  refine ⟨CF0, fun CF hCF => ⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ?_⟩⟩⟩⟩⟩
  obtain ⟨x₀, hx⟩ := hE eps CF hCF
  refine ⟨x₀, fun K _ _ _ hK hxK => ?_⟩
  have hF := hx K.s hK hxK
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f _ _ Ξ => if h : Ξ.Finite then Classical.choose (hF P f Ξ h) else ∅, by simp, ?_, ?_⟩
  · intro P f _ _ Ξ z hz
    by_cases h : Ξ.Finite
    · dsimp only at hz
      rw [dite_eq_left h] at hz
      exact (Classical.choose_spec (hF P f Ξ h)).1 z hz
    · dsimp only at hz
      rw [dite_eq_right h] at hz
      simp at hz
  · intro B f T _ hH _ _ w Z hX Wt z L hL hS
    obtain ⟨hq, hC, hfin, hmem⟩ := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z hX Wt z
    have hS2 := hH.2
    dsimp only at hS2
    rw [dite_eq_left hfin] at hS2
    rw [hL]
    exact (Classical.choose_spec (hF B.toPre f (T.set f) hfin)).2 (w.st Z) f rfl HEq.rfl L hL _ _ _ _ _ _ _ hS hC hq
      (fun t => ⟨_, hmem t, HEq.rfl⟩) (fun y hy => hS2 y hy)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridStageLatticesPropertiesProof
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct nonZeroDivisors ComplexConjugate

namespace GlobalTheory.CoreOnto.StageProof

theorem under_mem_of_modul_le {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) (h : P.modul sc ≤ Q.asIdeal) : Q.under (𝓞 D.host.F) ∈ P.S0 := by
  unfold GlobalTheory.ChiGrid.Places.modul at h
  obtain ⟨v, hv, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have hd : 0 < P.depth sc v ∨ P.depth sc v = 0 := by omega
  rcases hd with hd | hd
  · have h1 : (P.w v).asIdeal ≤ Q.asIdeal := Q.isPrime.le_of_pow_le hle
    have h2 : (P.w v).asIdeal = Q.asIdeal := (P.w v).isMaximal.eq_of_le Q.isPrime.ne_top h1
    have h3 : P.w v = Q := HeightOneSpectrum.ext h2
    rw [← h3, P.w_over v hv]
    exact hv
  · rw [hd, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact absurd hle Q.isPrime.ne_top

theorem stageOK : StageOK := by
  intro D hQ T L μ0 hL sc G W Mv hM i hi
  have hV := node_isV G hL (X := .core i) hi
  have hsd : IsSelfDualC (G.V (.core i)) (G.Λ (.core i)) := hV.sd
  obtain ⟨hsd', hstab, hcong⟩ := _root_.GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual D (G.V (.core i)) (G.Λ (.core i)) hsd i
  have hRL := _root_.GlobalTheory.ReLatPf.reLatLaw_holds D
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := hRL.1 _ _ hsd'
    exact ⟨r, hr⟩
  · intro r hr v Mo
    have hsdS : IsSelfDualC (gridStage G v i r Mo).V (gridStage G v i r Mo).Λ := by
      show IsSelfDualC r.sp (GlobalTheory.AdelicU.frameLat r.sp)
      rw [hr]; exact hsd'
    have hJ : (gridStage G v i r Mo).J = Lev.levA (gridStage G v i r Mo).V
        (congLev D.sp.cm (gridStage G v i r Mo).V.gram (gridStage G v i r Mo).Λ G.modul) := by
      show lev G (.core i) = Lev.levA r.sp (congLev D.sp.cm r.sp.gram (GlobalTheory.AdelicU.frameLat r.sp) G.modul)
      rw [hr]
      exact (congrArg (Lev.levA (G.V (.core i))) (hcong G.modul)).symm
    obtain ⟨hfin, hopen, hst, hoff, hsph, hsplit⟩ := _root_.GlobalTheory.CongMember.congLev_clauses D (gridCom W) (gridStage G v i r Mo) G.modul
      (GlobalTheory.ChiGrid.Places.modul_ne_bot _ _) (fun Q hQ' => under_mem_of_modul_le G.pl sc Q hQ') hsdS hJ
    have hw : GlobalTheory.Cusp.wittIndex r.sp = GlobalTheory.Cusp.wittIndex (G.V (.core i)) :=
      ((hRL.2.1 (G.V (.core i)) r W.θ _ Mo Set.univ).2.2.2).1
    have hwle : GlobalTheory.Cusp.wittIndex (G.V (.core i)) ≤ Node.neg D.R.m (.core i) := by
      haveI : IsCMField D.host.E := D.host.isCMField_hostE
      have hpar := GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel.parallelSig_of_sigOK hV.sigOK (fun τ => hV.sig τ)
      obtain ⟨U, hU, e⟩ := (GlobalTheory.Cusp.isGreatest_wittIndex ((G.V (.core i)) : HSpace D.host.E)).1
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      have h1 := GlobalTheory.ParallelWitt.finrank_le (E := D.host.E) (G.V (.core i)) τ (hpar τ) U (fun x hx y hy => by
        have := hU hy
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
        exact this x hx)
      omega
    exact {
      rank := hV.rank
      sigOK := hV.sigOK
      witt := by
        rw [show (gridStage G v i r Mo).V = r.sp from rfl, hw]
        refine lt_of_le_of_lt hwle ?_
        have h3 := D.R.three_m_lt_t
        have h4 := D.R.rank_add_five_le
        have h5 := D.R.m_add_three_le_k
        simp only [Node.neg, gridCom, sLen]
        unfold Ranks.r
        omega
      selfDual := hsdS
      fin := hfin
      isOpen := hopen
      stab := hst
      off := hoff
      sph := hsph
      split := hsplit
      haar := (v i).haar
      fund := (v i).fund }

end GlobalTheory.CoreOnto.StageProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelSiegelSetLeTorusPowerHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SiegelThetaBound

theorem theta_le_torus_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (M X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω → ∀ (Φ : WO M X → ℂ), IsThetaFunO ψ (sgn ε M) X Φ → ∀ (r : ℕ) (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf → ∀ (Ω C₀ : Set (GA D M)) (K : Subgroup (GA D M)) (c : ℝ), IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GA D M)) → 0 < c → (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a → a⁻¹ * p * a ∈ C₀) → ∃ (N : ℕ) (C : ℝ), ∀ (h : GA D X), ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a → ∀ k ∈ K, ‖thetaKO ω (p * a * k) h Φ‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hsub
  have hC₁ : IsCompact (C₀ * (K : Set (GA D M))) := hC₀.mul hK
  obtain ⟨K₀, hK₀n, hK₀c, m, e, hlev⟩ := _root_.GlobalTheory.LevelGrowth.level_poly ψ θ hθ ε M X χ χ' ω hω Φ hΦ _ hC₁
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (sgn ε M) X
  obtain ⟨k, A, C, hC, hT⟩ := GlobalTheory.T.thetaValue_siegelTorusElement_le_sobolevSeminorm ψ θ hθ ε M X χ χ' ω hω r Xf Yf hW c hc K₀ hK₀n hK₀c μ 𝓕 hμ
  obtain ⟨N₂, C₂, hC₂, hU⟩ := GlobalTheory.T.sobolevSeminorm_weilTheta_polynomial_in_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ _ hC₁ μ 𝓕 hμ k
  refine ⟨e * A + N₂, C * |m| ^ A * C₂, fun h p hp t ht a ha k' hk' => ?_⟩
  have hy : a⁻¹ * p * a * k' ∈ C₀ * (K : Set (GA D M)) := Set.mul_mem_mul (hsub p hp t ht a ha) hk'
  have hΨ : IsThetaFunO ψ (sgn ε M) X (ω (a⁻¹ * p * a * k', h) Φ) := by
    have := hω.om_pres ((GlobalTheory.Grid.ofSgn ε M).symm (a⁻¹ * p * a * k'), h) Φ hΦ
    simpa [GlobalTheory.Grid.WRep.toSgn] using this
  obtain ⟨n, hn, hnle, hnlev⟩ := hlev _ hy h
  have key := hT n hn _ hΨ hnlev t ht a ha
  have hs := hU _ hy h
  have hsplit : thetaKO ω (p * a * k') h Φ = ω (a, 1) (ω (a⁻¹ * p * a * k', h) Φ) 0 := by
    have e1 : ((p * a * k', h) : GA D M × GA D X) = (a, 1) * (a⁻¹ * p * a * k', h) := by
      ext <;> simp [mul_assoc]
    unfold thetaKO
    rw [e1, map_mul]
    rfl
  rw [hsplit]
  refine key.trans ?_
  have hH : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := by
    exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ X h
  have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have hs0 : 0 ≤ (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k (ω (a⁻¹ * p * a * k', h) Φ)).toReal :=
    ENNReal.toReal_nonneg
  set H : ℝ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) with hHdef
  have hnA : (n : ℝ) ^ A ≤ |m| ^ A * H ^ (e * A) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (hnle.trans (mul_le_mul_of_nonneg_right (le_abs_self m)
      (pow_nonneg (zero_le_one.trans hH) e))) A
  calc C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k (ω (a⁻¹ * p * a * k', h) Φ)).toReal *
        ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)
      ≤ C * (|m| ^ A * H ^ (e * A)) * (C₂ * H ^ N₂) * ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
        gcongr
    _ = C * |m| ^ A * C₂ * H ^ (e * A + N₂) * ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
        rw [pow_add]; ring

end GlobalTheory.SiegelThetaBound

end
end

