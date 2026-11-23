module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSplitHalfLatticeCoordinatesIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.RdBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_mul_mem (x : k) : ∃ N : ℕ, 0 < N ∧ (N : k) * x ∈ 𝒪[k] := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  set Q := Fintype.card (IsLocalRing.ResidueField 𝒪[k])
  have hQ : (Q : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hQ
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[k]) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have h2 : b ∣ ((Q ^ m : ℕ) : 𝒪[k]) := by
    rw [hu, Units.mul_left_dvd, Nat.cast_pow]
    exact pow_dvd_pow_of_dvd hQ m
  obtain ⟨d, hd⟩ := h2
  refine ⟨Q ^ m, pow_pos Fintype.card_pos m, ?_⟩
  have hb1 : (algebraMap 𝒪[k] k b) ≠ 0 := fun h => hb0 (Subtype.ext h)
  have h3 : ((Q ^ m : ℕ) : k) = algebraMap 𝒪[k] k b * algebraMap 𝒪[k] k d := by
    rw [← map_mul, ← hd, map_natCast]
  have h4 : ((Q ^ m : ℕ) : k) * (algebraMap 𝒪[k] k a / algebraMap 𝒪[k] k b) = ((d * a : 𝒪[k]) : k) := by
    rw [h3]
    change _ = algebraMap 𝒪[k] k (d * a)
    rw [map_mul]
    field_simp
  rw [h4]
  exact (d * a).2

theorem exists_nat_mul_mem_family {ι : Type} [Fintype ι] (f : ι → k) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : k) * f i ∈ 𝒪[k] := by
  classical
  choose n hn hf using fun i => exists_nat_mul_mem (f i)
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (n i : k), mul_assoc]
  exact mul_mem (natCast_mem _ c) (hf i)

end GlobalTheory.FinPl.RdBound


open GlobalTheory.FinPl.RdBound in
theorem GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), IsHalf p.e u → ∀ i j, (N : k) * rd α β u i j ∈ 𝒪[k] := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨K₁, hK₁, h₁⟩ := exists_nat_mul_mem_family (fun x : n × Fin T.rank => β.b' x.1 x.2)
  obtain ⟨K₂, hK₂, h₂⟩ := exists_nat_mul_mem_family (fun x : Fin S.rank × n' => α.b x.1 x.2)
  refine ⟨K₁ * M * K₂, Nat.mul_pos (Nat.mul_pos hK₁ hM) hK₂, fun u hu hh i j => ?_⟩
  have hu' := GlobalTheory.PlaceModel.latO_le_top _ hu
  have hint : ∀ a b, (M : k) * p.pr (u a b) ∈ 𝒪[k] := fun a b => by
    rw [p.int_iff]
    have h1 : p.sec ((M : k) * p.pr (u a b)) = (M : AE D) * u a b := by
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, p.sec_pr, hh a b]
    rw [h1]
    refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
    rw [RingHom.map_mul, map_natCast]
    exact hden _ hu' a b
  change (_ : k) * (β.b' * Matrix.map u p.pr * α.b) i j ∈ 𝒪[k]
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine sum_mem fun a _ => ?_
  have e : ((K₁ * M * K₂ : ℕ) : k) * (β.b' i a * Matrix.map u p.pr a b * α.b b j) =
      ((K₁ : k) * β.b' i a) * ((M : k) * p.pr (u a b)) * ((K₂ : k) * α.b b j) := by
    rw [Matrix.map_apply]; push_cast; ring
  rw [e]
  exact mul_mem (mul_mem (h₁ (i, a)) (hint a b)) (h₂ (b, j))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardLocalisationWeilDatumInertPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertFrameLoc


set_option maxHeartbeats 800000 in
theorem exists_isStd_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ (∀ m : M, IsThetaFunO ψ S T m) ∧ ∀ x, ∃ u : WO S T, ∀ m : M, ((ρ x m : M) : WO S T → ℂ) = heisO ψ S T u m := by
  intro D ψ S T χS χT om hW v w h hw uS uT c ϖ eS eT hU hcS hcT f hf hf0
  obtain ⟨hconj, ⟨aS, haS, gS, eSa⟩, kSc⟩ := hcS
  obtain ⟨-, ⟨aT, haT, gT, eTa⟩, kTc⟩ := hcT
  obtain ⟨k, hk⟩ := GlobalTheory.InertLoc.exists_isGen D w
  have h2 := _root_.GlobalTheory.InertTwo.valued_two_eq_one D v w hw
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := GlobalTheory.InertLoc.exists_delta_psi hU h2 (thW ψ hw h (k * c k))
    (_root_.GlobalTheory.InertFrameLoc.thW_conj D ψ v w hw h c k hconj hU.1) (_root_.GlobalTheory.InertFrameLoc.thW_cond D ψ v w hw h c ϖ k hW.std hconj hU hk)
  have hadd : ∀ x y, uPt hw h k aS aT (x + y) = uPt hw h k aS aT x + uPt hw h k aS aT y := uPt_add
  have hMθ : spanT ψ (uPt hw h k aS aT) f ≤ GlobalTheory.FinWeilO.thetaSub ψ S T := Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    exact GlobalTheory.FinTranslate.isTheta_heisO_fin hW.std.1 (map_infPart_uPt (hw := hw) (h := h) (k := k) (aS := aS) (aT := aT) x) hf.1)
  let π : GU c S.rank × GU c T.rank →* Module.End ℂ (WO S T → ℂ) :=
    om.comp (((embV S v).comp eS.symm.toMonoidHom).prodMap ((embV T v).comp eT.symm.toMonoidHom))
  have hπ : ∀ p m, π p m = om (embV S v (eS.symm p.1), embV T v (eT.symm p.2)) m := fun _ _ => rfl
  have hstab : ∀ p, ∀ m ∈ spanT ψ (uPt hw h k aS aT) f, π p m ∈ spanT ψ (uPt hw h k aS aT) f := fun p m hm =>
    mem_spanT_of (fun y => by
      rw [hπ, hW.om_heis _ _ _ _ hf.1, _root_.GlobalTheory.InertFrameAct.actO_uPt]
      exact heis_mem_spanT hadd _
        (GlobalTheory.T.weilRep_latticeVacuum_mem_span_inertTranslates D ψ S T χS χT om hW v w hw h uS uT c ϖ k aS aT hU hconj hk haS haT gS gT f hf _ _)) hm
  have hint2 : (2⁻¹ : w.adicCompletion D.host.E) ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := (GlobalTheory.SphTheta.half h2).2
  have hvac : ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E),
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → heisO ψ S T (uPt hw h k aS aT x) f = f := fun x hx => by
    have h1 := hf.2.1 _ (_root_.GlobalTheory.InertFrameLoc.uPt_mem_latO D v w hw h S T k aS aT hk haS haT ((2⁻¹ : w.adicCompletion D.host.E) • x)
      fun i j => mul_mem hint2 (hx i j))
    rwa [two_nsmul, ← uPt_add, GlobalTheory.InertLoc.half_add_half] at h1
  have hfM : f ∈ spanT ψ (uPt hw h k aS aT) f := self_mem_spanT uPt_zero
  have dict := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have unr : ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → GlobalTheory.Hk3.UnrPl w χ := fun χ hχ =>
    dict.2.1 χ fun w' hw' => by rw [(GlobalTheory.LFun.InertChart.under_eq_iff hw w').1 hw']; exact hχ
  have hfix := GlobalTheory.ConjVacFix.vacFix_of_unrPl ψ S T χS χT om w hW (unr χS uS) (unr χT uT)
  refine ⟨δ, ψ', spanT ψ (uPt hw h k aS aT) f, rhoT ψ (uPt hw h k aS aT) f hadd, omT ψ (uPt hw h k aS aT) f π hstab,
    ⟨f, hfM⟩, ⟨⟨hU, GlobalTheory.InertLoc.odd_of_v_two hU h2, antiG_mem _, antiG_mem _, antiJ_herm c _, antiJ_herm c _, hδ, p1, p2,
      ?_, fun x y => ?_, ?_, fun g g' x => ?_, fun g g' hg hg' s hs => ?_⟩,
      fun e => hf0 (congrArg Subtype.val e), fun x hx => Subtype.ext (hvac x hx), span_rhoT_eq_top hadd hfM⟩,
    rfl, fun _ _ _ => rfl, fun m => hMθ m.2, fun x => ⟨uPt hw h k aS aT x, fun _ => rfl⟩⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [coe_rhoT, uPt_zero, GlobalTheory.SplitScalar.heisO_zero]
    rfl
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [Module.End.mul_apply, coe_rhoT, coe_rhoT, GlobalTheory.SplitScalar.heisO_heisO, LinearMap.smul_apply, Submodule.coe_smul,
      coe_rhoT, ← uPt_add, _root_.GlobalTheory.InertFrameSympl.symplOH_uPt D ψ v w hw h S T c k aS aT hconj gS gT, ← p3]
    simp only [GlobalTheory.Hk3.locH, one_mul]
  · refine eq_top_iff.2 ((span_rhoT_eq_top hadd hfM).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨x, rfl⟩
    exact ⟨x, ⟨f, hfM⟩, fun y hy => Subtype.ext (hvac y hy), rfl⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    have hinv : (eS.symm g)⁻¹ = eS.symm g⁻¹ := (map_inv eS.symm g).symm
    show π (g, g') (heisO ψ S T (uPt hw h k aS aT x) m) = heisO ψ S T (uPt hw h k aS aT _) (π (g, g') m)
    rw [hπ, hπ, hW.om_heis _ _ _ _ (hMθ m.2), _root_.GlobalTheory.InertFrameAct.actO_uPt]
    refine congrArg (fun z => heisO ψ S T (uPt hw h k aS aT z) (om (embV S v (eS.symm g), embV T v (eT.symm g')) m)) ?_
    rw [← eTa, hinv, ← eSa]
    erw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  · refine Subtype.ext (hfix _ ⟨hMθ s.2, fun e e' he uu huu hh => ?_⟩ _
      ((dict.2.2.1 S _).2 ⟨eS.symm g, (kSc _).2 ((eS.apply_symm_apply g).symm ▸ GlobalTheory.SphTheta.mem_KU_iff.2 hg), rfl⟩) _
      ((dict.2.2.1 T _).2 ⟨eT.symm g', (kTc _).2 ((eT.apply_symm_apply g').symm ▸ GlobalTheory.SphTheta.mem_KU_iff.2 hg'), rfl⟩))
    obtain ⟨x, hx, rfl⟩ := _root_.GlobalTheory.InertFrameLoc.exists_uPt_of_half D v w hw h S T k aS aT hk haS haT e e' he uu huu hh
    exact congrArg Subtype.val (hs x hx)

end GlobalTheory.InertFrameLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureDisintegrationBesselGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Disint

theorem disint : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), ∃ c : ℝ, 0 < c ∧ ∀ G : X.B.I.GA → ENNReal, Measurable G → (∀ x, G x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
  intro D X h u ψ A B
  obtain ⟨μSf, hHaar, hσ, c₁, hc₁, hfin⟩ := _root_.GlobalTheory.SfinHaar.disint_finPart D X u
  obtain ⟨c₃, hc₃, hR⟩ := _root_.GlobalTheory.Core.Mi.BesHaar.lintegral_besGrp_eq D X h u ψ A B μSf hHaar hσ (_root_.GlobalTheory.MuSHaar.muS_isHaarOnSet D X u)
  refine ⟨c₁ / c₃, div_pos hc₁ hc₃, ?_⟩
  intro G hGm hsupp
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI := hσ
  set μS := ((X.muN u).prod (X.muH u)).map (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) with hμS

  set g : X.B.I.Ginf → ENNReal := fun x => ∫⁻ t, ∫⁻ k in X.K2, G (x, t.1 * X.xu u * k) ∂X.B.μf ∂μSf with hgdef
  have hg : Measurable g := by
    have hΨ : Measurable (fun p : (X.B.I.Ginf × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) × X.B.I.Gf =>
        G (p.1.1, p.1.2.1 * X.xu u * p.2)) :=
      hGm.comp (measurable_fst.fst.prodMk
        (((measurable_subtype_coe.comp measurable_fst.snd).mul_const _).mul measurable_snd))
    exact (hΨ.lintegral_prod_right' (ν := X.B.μf.restrict X.K2)).lintegral_prod_right' (ν := μSf)
  have hL : ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u) := by
    have e0 : X.B.I.muA X.B.μf = (Formalism.L2.SG.ProjRows.muInf X.B.I).prod X.B.μf := rfl
    rw [e0, lintegral_prod _ hGm.aemeasurable]
    have e1 : ∀ x, ∫⁻ z, G (x, z) ∂X.B.μf = ENNReal.ofReal c₁ * g x := fun x =>
      hfin (fun z => G (x, z)) (hGm.comp measurable_prodMk_left) (fun z hz => hsupp (x, z) hz)
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, X.nuQ_weil u g hg]
  have hRy : ∀ y : X.B.I.Ginf, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR =
      ENNReal.ofReal c₃ * ∫⁻ a, g (a * y) ∂μS := by
    intro y
    set Φ : X.B.I.GA → ENNReal := fun p => ∫⁻ k in X.K2, G (p.1 * y, p.2 * X.xu u * k) ∂X.B.μf with hΦ
    have hΦm : Measurable Φ := by
      have : Measurable (fun q : X.B.I.GA × X.B.I.Gf => G (q.1.1 * y, q.1.2 * X.xu u * q.2)) :=
        hGm.comp ((measurable_fst.fst.mul_const y).prodMk ((measurable_fst.snd.mul_const _).mul measurable_snd))
      exact this.lintegral_prod_right' (ν := X.B.μf.restrict X.K2)
    have e : ∀ s : besGrp B.d B.o, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf = Φ (iotaX X h s.1) := by
      intro s
      refine lintegral_congr fun k => ?_
      congr 1
      ext <;> simp
    simp_rw [e]
    rw [hR Φ hΦm]
  calc ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u) := hL
    _ = ENNReal.ofReal (c₁ / c₃) * (ENNReal.ofReal c₃ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (div_pos hc₁ hc₃).le, div_mul_cancel₀ _ hc₃.ne']
    _ = _ := by
        congr 1
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact (lintegral_congr fun y => hRy y).symm

end GlobalTheory.Core.Mi.Disint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorHomSelfDualComponentsSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem isLattice_of_isLat_selfDual {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p S n) (L : Lat S) (hL : IsSelfDualC S L) (Λ : Submodule 𝒪[k] (n → k)) (h : β.IsLat L Λ) :
    Λ.IsFullLattice k := by
  obtain ⟨Λ₀, h₀, hI, -⟩ := (_root_.GlobalTheory.FrameAt.frame_facts D k p S n β).2.2.2.1 L hL
  have e : Λ = Λ₀ := Submodule.ext fun x => (h x).trans (hI x).symm
  have hlat : Λ.IsLattice k := e ▸ h₀
  refine { toIsLattice := hlat, span_eq_top := eq_top_iff.mpr fun x _ => ?_ }
  obtain ⟨m, s, c, hs, hc, -⟩ := GlobalTheory.FinPl.FrameLat.exists_gen (p := p) hL
  have hx := congrArg (β.b' *ᵥ ·) (hc (β.b *ᵥ x))
  simp only [Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec, Matrix.mulVec_sum,
    Matrix.mulVec_smul] at hx
  rw [hx]
  refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  apply (h _).2
  rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
  exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (p := p) (hs l)

theorem latInd_mem_SB_of_selfDual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → latInd ΛS ΛT ∈ SB (Matrix n n' k) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT ΛS ΛT hα hβ
  have := isLattice_of_isLat_selfDual α LS hS ΛS hα
  have := isLattice_of_isLat_selfDual β LT hT ΛT hβ
  exact GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT

end GlobalTheory.FinPl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCFrameLat
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.AbsConv

open Filter Set GlobalTheory.Eis

theorem isSelfDualC_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem enorm_dblIntegrand {D : D7} {V : HSp D} (μ : (AE D)ˣ →* Circle) (E : GA D (dblSp V) → ℂ)
    (f₁ f₂ : GA D V → ℂ) (x : GA D V × GA D V) :
    ‖dblIntegrand V μ E f₁ f₂ x‖ₑ = ‖E (io V x)‖ₑ * (‖f₁ x.1‖ₑ * ‖f₂ x.2‖ₑ) := by
  simp only [dblIntegrand]
  simp_rw [← ofReal_norm_eq_enorm]
  rw [norm_mul, norm_mul, norm_mul, norm_inv, Circle.norm_coe, inv_one, mul_one, Complex.norm_conj,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem dblConv_of_growth {D : D7} {V : HSp D} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ)
    {m : Measure (GA D V)} (hm : m.IsHaarMeasure) {f₁ f₂ : GA D V → ℂ} (h₁ : GlobalTheory.Grow.RapidDec V f₁)
    (h₂ : GlobalTheory.Grow.RapidDec V f₂) {E : GA D (dblSp V) → ℂ} (hE : LeftInv (GQ (dblSp V)) E) (hc : Continuous E)
    {C : ℝ} {N : ℕ} (hb : ∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) :
    DblConv V μ m E f₁ f₂ := by
  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_dblIntegrand hμ hE h₁.1 h₂.1
  have hmeas : AEStronglyMeasurable (dblIntegrandQ V μ E f₁ f₂) ((autMeasure V m).prod (autMeasure V m)) := by
    have e' : dblIntegrandQ V μ E f₁ f₂ = dblIntegrand V μ E f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
      funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk hli _ _)
    rw [e']
    exact ((continuous_dblIntegrand hμ hc h₁.continuous h₂.continuous).measurable.comp
      (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
  have i₁ := _root_.GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec D V m hm f₁ h₁ N
  have i₂ := _root_.GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec D V m hm f₂ h₂ N
  set K : ℝ := max C 0 * 4 ^ N with hK
  have hK0 : 0 ≤ K := mul_nonneg (le_max_right _ _) (by positivity)
  refine ⟨hli, ((i₁.mul_prod i₂).const_mul K).mono' hmeas (Eventually.of_forall fun q => ?_)⟩
  obtain ⟨γ₁, hγ₁, e₁⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.1.out
  obtain ⟨γ₂, hγ₂, e₂⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.2.out
  have hinv : E (io V (q.1.out, q.2.out)) = E (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := by
    have e : io V (γ₁ * q.1.out, γ₂ * q.2.out) = io V (γ₁, γ₂) * io V (q.1.out, q.2.out) := by
      rw [← map_mul]; rfl
    rw [e, hE _ (io_mem_GQ V hγ₁ hγ₂)]
  have hq₁ := GlobalTheory.Grow.one_le_quotHeight V q.1.out
  have hq₂ := GlobalTheory.Grow.one_le_quotHeight V q.2.out
  have hx₁ := GlobalTheory.Grow.one_le_height V (γ₁ * q.1.out)
  have hx₂ := GlobalTheory.Grow.one_le_height V (γ₂ * q.2.out)
  have h3 : GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ≤
      4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) := by
    refine (GlobalTheory.Cont.HeightIo.height_io_le_mul V _ _).trans ?_
    nlinarith
  have h0 : 1 ≤ GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := GlobalTheory.Grow.one_le_height _ _
  have hEq : ‖E (io V (q.1.out, q.2.out))‖ ≤
      K * (GlobalTheory.Grow.quotHeight V q.1.out ^ N * GlobalTheory.Grow.quotHeight V q.2.out ^ N) := by
    rw [hinv]
    calc _ ≤ C * GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ^ N := hb _
      _ ≤ max C 0 * (4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out)) ^ N :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by linarith) h3 N) (pow_nonneg (by linarith) N)
            (le_max_right _ _)
      _ = _ := by rw [hK, mul_pow, mul_pow]; ring
  have hμ1 : ‖((μ (detA V q.2.out) : ℂ))⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  simp only [dblIntegrandQ, dblIntegrand, norm_mul, hμ1, mul_one, Complex.norm_conj]
  calc ‖E (io V (q.1.out, q.2.out))‖ * ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖
      ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ N * GlobalTheory.Grow.quotHeight V q.2.out ^ N) *
          ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖ := by gcongr
    _ = _ := by ring

theorem absConv_unfolded : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle),
    IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s,
    GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V),
    m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ →
    (∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 m → ∑' q : GlobalTheory.Eis.SiegelCosets V, ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖GlobalTheory.Eis.dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m ≠ ⊤) ∧
    GlobalTheory.Eis.DblConv V μ m (GlobalTheory.Eis.eis V φ) f₁ f₂ := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  have hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) :=
    _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D V (frameLat V) a (isSelfDualC_frameLat V) ha
  have hS : SphConv V a := GlobalTheory.Eis.sphConv D V a hI
  have hσ : (V.rank : ℝ) / 2 < ((s.re : ℂ)).re := by simpa using hs
  have hconvS : ∀ g, EisConv V (sph V a (s.re : ℂ)) g := fun g => (((sphConv_iff hI).1 hS).1 _ hσ).2 g
  have h2 : ∀ g, sph V a (s.re : ℂ) g = (((hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) : ℝ) : ℂ) := fun g => by
    rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]; push_cast; rfl
  have hr0 : ∀ g, 0 ≤ (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g =>
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hn : ∀ g, ‖sph V a (s.re : ℂ) g‖ = (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g => by
    rw [h2, Complex.norm_real, Real.norm_of_nonneg (hr0 g)]
  have hsS : ∀ g, Summable fun q : SiegelCosets V =>
      ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ := fun g => hconvS g
  have heS : ∀ g, ‖eis V (sph V a (s.re : ℂ)) g‖ =
      ∑' q : SiegelCosets V, ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ := by
    intro g
    have e : eis V (sph V a (s.re : ℂ)) g = ((∑' q : SiegelCosets V,
        ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun q => by rw [hn]; exact h2 _
    rw [e, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := by
    haveI := t2Space_adeleRing' (F := D.host.F)
    exact hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  have hφS : ∀ g, ‖φ g‖ ≤ max C 0 * ‖sph V a (s.re : ℂ) g‖ := fun g =>
    (hC g).trans (by rw [hn]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hr0 g))
  have hsφ : ∀ y, Summable fun q : SiegelCosets V => ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y)‖ :=
    fun y => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hφS _) ((hsS y).mul_left _)
  have hle : ∀ y, ∑' q : SiegelCosets V, ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y)‖ ≤
      max C 0 * ‖eis V (sph V a (s.re : ℂ)) y‖ := fun y => by
    rw [heS, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun q => hφS _) (hsφ y) ((hsS y).mul_left _)
  obtain ⟨B, A, hB⟩ := hgrow
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have hSi : LeftInv (GQ (dblSp V)) (eis V (sph V a (s.re : ℂ))) := leftInv_eis (leftInv_of_mem h1 (sph_mem hI _))
  have hSc : Continuous (eis V (sph V a (s.re : ℂ))) := SphConv.continuous_eis hI (sph_mem hI _) hS hσ
  have hconv0 : DblConv V μ m (fun y => (((max C 0 * ‖eis V (sph V a (s.re : ℂ)) y‖ : ℝ)) : ℂ)) f₁ f₂ := by
    refine dblConv_of_growth hμ hm h₁ h₂ (C := max C 0 * B) (N := A) (fun γ hγ g => ?_)
      (Complex.continuous_ofReal.comp (continuous_const.mul hSc.norm)) (fun g => ?_)
    · beta_reduce
      rw [hSi γ hγ g]
    · rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _)), mul_assoc]
      exact mul_le_mul_of_nonneg_left (hB g) (le_max_right _ _)
  refine ⟨fun 𝓕 h𝓕 => ?_, ?_⟩
  · have hint := (hconv0.dblInt_eq h𝓕).1
    have hφc : Continuous φ := hφ.2.1
    have hmeas : ∀ q : SiegelCosets V, AEMeasurable (fun x =>
        ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ)
        ((m.prod m).restrict (𝓕 ×ˢ 𝓕)) := fun q =>
      (continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous
        h₂.continuous).measurable.enorm.aemeasurable
    rw [← lintegral_tsum hmeas]
    refine ne_top_of_le_ne_top hint.2.ne (lintegral_mono fun x => ?_)
    simp only [enorm_dblIntegrand]
    rw [ENNReal.tsum_mul_right]
    gcongr ?_ * _
    simp_rw [← ofReal_norm_eq_enorm]
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _)),
      ← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsφ _)]
    exact ENNReal.ofReal_le_ofReal (hle _)
  · refine dblConv_of_growth hμ hm h₁ h₂ (leftInv_eis (leftInv_of_mem hμ hφ)) (SphConv.continuous_eis hI hφ hS hs)
      (C := max C 0 * B) (N := A) fun g => ?_
    refine (norm_tsum_le_tsum_norm (hsφ g)).trans ((hle g).trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB g) (le_max_right _ _)

end GlobalTheory.Core.Rk.AbsConv

end
end

