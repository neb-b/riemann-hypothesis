module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0289
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTiedRowLoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0023
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0022
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.BaseRowsEqRecordRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0293
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Formalism.LocalToGlobal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0073

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerMore
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.IsoComp
open GlobalTheory.CompRed
section Gen
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {W : Type} [AddCommGroup W] [Module ℂ W]
end Gen
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (x : D.nd.X i) (f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)), f' ∈ eigC D.nd D.naut i x → f' ≠ 0 → ∀ sp : SplitPlace D.host.E, ∀ c : ℕ → ℂ, (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real f') = c k • (P.M.loc i).real f') → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ ∃ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ F ≠ 0 ∧ ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = c k • F := by
  intro hL D P i x f' hf' hf0 sp c hc
  classical
  have hfin : ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k, ((fun y : GAf D.host.E D.R.nV =>
      (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J)) '' Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k).Finite := by
    intro ϖ hϖ k
    obtain ⟨N, hN, hNJ⟩ := (P.M.loc i).J_open
    exact _root_.GlobalTheory.TSetFinCong.finite_image_tSet_cong D.host.E D.R.nV (P.M.loc i).J ⟨N, hN, fun κ hκ => (hNJ κ hκ).1⟩ sp ϖ k hϖ
  unfold eigC at hf'
  rw [Submodule.mem_iSup_iff_exists_finsupp] at hf'
  obtain ⟨g, hgmem, hgsum⟩ := hf'
  have hg' : ∀ Q, g Q ≠ 0 → D.naut.ptV i Q = some x ∧ g Q ∈ D.naut.typeV i Q := by
    intro Q hQ
    by_cases h : D.naut.ptV i Q = some x
    · refine ⟨h, ?_⟩
      have := hgmem Q
      rwa [iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from h)] at this
    · exfalso
      have := hgmem Q
      rw [iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from h), Submodule.mem_bot] at this
      exact hQ this
  obtain ⟨Q0, hQ0⟩ : ∃ Q, g Q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf0
    rw [← hgsum, show g = 0 from Finsupp.ext h, Finsupp.sum_zero_index]
  set G : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) := fun Q => (P.M.loc i).real (g Q) with hGdef
  have hsum : (P.M.loc i).real f' = ∑ Q ∈ g.support, G Q := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hgsum, Finsupp.sum, map_sum]
  have hGiso : ∀ Q ∈ g.support, G Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    intro Q hQ
    have hy := (hg' Q (Finsupp.mem_support_iff.1 hQ)).2
    rw [P.H.av.typeV] at hy
    exact hy
  have hind := isoTyp_indep (P.M.loc i).wt (P.H.av.S i) (P.H.av.irr i) (P.H.av.inj i)
  have hQ0s : Q0 ∈ g.support := Finsupp.mem_support_iff.2 hQ0
  refine ⟨Q0, (hg' Q0 hQ0).1, G Q0, hGiso Q0 hQ0s, ?_, ?_, ?_⟩
  · rw [← (P.M.loc i).real_range]
    exact ⟨g Q0, rfl⟩
  · intro h
    exact hQ0 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))
  · intro ϖ hϖ k hk
    set Dk := Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k
    set t : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) :=
      fun Q => NG.heckeD (P.M.loc i).J Dk (G Q) - c k • G Q with htdef
    have htmem : ∀ Q ∈ g.support, t Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := fun Q hQ =>
      Submodule.sub_mem _ (heckeD_mem_isoTyp _ _ _ (hfin ϖ hϖ k) _ (hGiso Q hQ))
        (Submodule.smul_mem _ _ (hGiso Q hQ))
    have htsum : ∑ Q ∈ g.support, t Q = 0 := by
      simp only [t]
      rw [Finset.sum_sub_distrib, ← heckeD_finset_sum _ _ (hfin ϖ hϖ k), ← Finset.smul_sum, ← hsum, hc ϖ hϖ k hk,
        sub_self]
    have hrest : t Q0 = -∑ Q ∈ g.support.erase Q0, t Q := by
      rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ hQ0s, htsum]
    have hmem2 : t Q0 ∈ ⨆ (j : D.naut.AV i) (_ : j ≠ Q0), NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j) := by
      rw [hrest]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun Q hQ => ?_)
      obtain ⟨hne, hQs⟩ := Finset.mem_erase.1 hQ
      exact (le_iSup₂ (f := fun (j : D.naut.AV i) (_ : j ≠ Q0) => NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j)) Q hne)
        (htmem Q hQs)
    have h0 : t Q0 = 0 := Submodule.disjoint_def.1 (iSupIndep_def.1 hind Q0) _ (htmem Q0 hQ0s) hmem2
    exact sub_eq_zero.1 h0
end GlobalTheory.IsoComp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGw
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu := by
  intro hL D P S hS i k v hw
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hc := hS.mu i _ hw j hjj
  have hc' : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) ((P.tp.tup (D.nd.mu i) j).loc (D.naut.plGw k v)) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ _, fun _ => rfl⟩
  rw [GlobalTheory.HeckeComp.eq_of_isComp hc' hc]
  exact GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j).tame _) (P.tp.xi_tame _ _))
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NAllCWithLoc
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.HeightCounting.FitAll
theorem nAllC_withLoc_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.HeightCounting.LpCmpAlt hL → _root_.GlobalTheory.HeightCounting.CgCmpAlt hL → ∀ (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (fr : OmFrame b.D), fr.jE = b.jE → (PhtOn b.A.wd fr fun _ _ _ _ => True) → Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → lowPr b.D ⊆ b.low → ∃ a : _root_.GlobalTheory.HeightCounting.NAllCAlt (withLoc b.L) (chL b.L b.C), (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc b.L), TupTied (withLoc b.L) c (chL b.L b.C)) = ⟨cfL b.L b.cf, tpL b.L b.tp⟩ ∧ a.gal.fr.jE = b.jE ∧ a.gal.mt = mtL b.L b.M ∧ ExpRel b.L b.Bs.exp a.exp ∧ Nonempty (NCharTied (withLoc b.L) (cfL b.L b.cf) (chL b.L b.C) (tpL b.L b.tp)) ∧ NGalChrTied (withLoc b.L) (cfL b.L b.cf) (chL b.L b.C) (tpL b.L b.tp) ∧ ∀ F : RowFrame (withLoc b.L), F.rep = b.rep → _root_.Formalism.L2.RowLocTiedAlt (withLoc b.L) a.gal.lp F := by
  intro hL hLp hCg D' b fr hfr hpht hE hCh hlow
  obtain ⟨g, hgj, hgm, hgt, ⟨dat⟩, ⟨cov⟩, hrow⟩ :=
    _root_.GlobalTheory.FitGal.galTied_withLoc_alt hL hLp D' b fr hfr hpht hE.star hE.int hE.split hCh
  obtain ⟨⟨nt⟩, ⟨lt⟩⟩ := _root_.GlobalTheory.HeightCounting.nTied_locTied_of_built_alt hL hCg D' b
  obtain ⟨TO⟩ := _root_.GlobalTheory.HeightCounting.typesOpen_withLoc_alt b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch b.mt
    hE.star hE.int hE.split hCh b.big b.L b.Sp b.Au b.ss
  have rho : NR.NRhoTied (withLoc b.L) := _root_.GlobalTheory.HeightCounting.nRhoTied_withLoc_alt hL D' b hE.star hE.int hE.split hCh TO
  obtain ⟨Tw, hX⟩ := _root_.GlobalTheory.T.exists_twOpen_expRel_of_chebSplit hL D' b hE hCh
  have ty : NormalizedTypesCompatibility (withLoc b.L) b.jE :=
    { eM := TO.par.eM, eM_K := TO.par.eM_K, tA := TO.grp.tA, tκ := TO.grp.tκ, teichC_def := TO.grp.teichC_def,
      iota_loc := fun i => ⟨TO.plB _, TO.plκ _, TO.plB_loc i, TO.plB_iota i⟩,
      ζ := TO.grp.ζ, ζ_gen := TO.grp.ζ_gen, O := TO.grp.O, eSer_def := TO.grp.eSer_def, kv := TO.grp.kv,
      tg_tame := TO.grp.tg_tame, O_equiv := TO.grp.O_equiv, O_tw := TO.grp.O_tw, eP := TO.par.eP,
      locPar_def := TO.par.locPar_def }
  let F0 : TwFrame (withLoc b.L) := ⟨Tw.twF.K0, Tw.twF.eO0, Tw.twF.j0, Tw.twF.Lw, Tw.twF.eO, Tw.twF.eOk, Tw.twF.iCq, Tw.twF.S0x⟩
  have hlow' : lowPr (withLoc b.L) ⊆ b.low := hlow
  have tw : NTwTied (withLoc b.L) F0 := by
    have T := Tw.tw
    have hN : Ideal.absNorm (withLoc b.L).host.ccK ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (withLoc b.L).host.ccK_ne_bot
    have hd : (NumberField.discr (withLoc b.L).host.E).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero (withLoc b.L).host.E)
    exact ⟨T.pl_emb, T.ringSpec_baseIntegersEquiv_algebraMap, T.ringSpec_baseEmbedding_compatible, T.eO_alg, T.eOk_alg, T.mu_g, T.hk_split, T.ringSpec_excludedPlaces_eq, T.concreteTwistFrame_extraExcludedPlaces_conj, T.B_range,
      T.sig_inj, T.qs_pos,
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hlow' (by simp [lowPr, Nat.mem_primeFactors, hp, h, hN])),
      fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (hlow' (by simp [lowPr])), fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (hlow' (by simp [lowPr])),
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hlow' (by simp [lowPr, Nat.mem_primeFactors, hp, h, hd]))⟩
  refine ⟨
    { gal := g, n := (b.eq ▸ nt), loc := (b.eq ▸ lt), data := dat, cover := (hgm ▸ cov), chiD := Tw.chiD, chi := Tw.chi,
      rho := rho, types := (hgj.symm ▸ ty), twF := F0, tw := tw, nct := Tw.ch.nct, exp := Tw.exp, choice := Tw.ch.choice,
      eMt_level := by rw [hgm]; exact Tw.ch.eMt_level,
      cf := cfL b.L b.cf, tp := tpL b.L b.tp, tupLink := hgt,
      eta_eq := Tw.eta_eq, ringSpec_normalisedCharacter_eq := Tw.ringSpec_normalisedCharacter_eq, del_eq := Tw.del_eq, psi_eq := Tw.psi_eq,
      plB := TO.plB, plκ := TO.plκ, plB_loc := TO.plB_loc, plB_iota := TO.plB_iota,
      etaT_link := Tw.etaT_link, muC_link := Tw.muC_link, iCq_embO := Tw.iCq_embO, embO_star := Tw.embO_star },
    rfl, hgj, hgm, hX, ⟨Tw.chrN⟩, Tw.chrGal, hrow⟩
end GlobalTheory.HeightCounting.FitAll
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy
structure RowsAAlt (D : D7) : Prop where
  tieLab : SumRepresentations.tieLab D
  hecke : HeckeSplitOne D
  tie0 : SumRepresentations.tie0 D
  a2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D
  an1 : T2.SumRepresentations.StrongMultiplicityOneCuspidalSums D.nd D.naut
  an2 : T2.SumRepresentations.IsobaricMultiplicityOne D.nd D.naut
  a5 : SumRepresentations.adm5 D
  temp : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D
  g4p : _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)
def SummandsSuffice (D : D7) : Prop :=
  _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D → SumRepresentations.tieLab D → RowSize D → HeckeSplitOne D → (∀ i : D.nd.Loc, LamPos D (D.nd.mu i) (D.nd.j i)) →
    ThetaOne D → _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D → _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D
structure LinkedData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Type 1 where
  P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D
  X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp
  agree : GlobalTheory.NJoin.Agree X P.M P.rep
  e0read : GoodIdempotentReadsAsGoodTypeProjector X
structure LinkedDataNamed {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (T : _root_.GlobalTheory.NRows.LinkedData hL D) : Prop where
  hypO : SumRepresentations.hypO D
  c1 : GlobalDatumCompatibility D
  bc : SphericalInertData.Conclusion1 D
  lam : LamUsed D
  isot : SumRepresentations.adm8 D
  ser : GlobalTheory.TypeLeaf.SerLoc D
  typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ T.X.R j t
structure LinkedInputs (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Type 1 extends toRowSideFamily : _root_.GlobalTheory.NRows.LinkedData hL D where
  named : _root_.GlobalTheory.NRows.LinkedDataNamed toRowSideFamily
structure PointConditions' (D : D7) : Prop where
  a : _root_.GlobalTheory.NRows.RowsAAlt D
  b : RowsB D
  c : RowsC D
  typeNZ : ∀ i, TypeNZRec D.nd D.naut i
  rank : ∀ L : SizeData₂ D, TwistedPlaces.adm3 L
namespace Inputs
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (I : _root_.GlobalTheory.NRows.LinkedInputs hL D)
include I
theorem _root_.GlobalTheory.NRows.LinkedInputs.hypO : SumRepresentations.hypO D := I.named.hypO
theorem _root_.GlobalTheory.NRows.LinkedInputs.c1 : GlobalDatumCompatibility D := I.named.c1
theorem _root_.GlobalTheory.NRows.LinkedInputs.bc : SphericalInertData.Conclusion1 D := I.named.bc
theorem _root_.GlobalTheory.NRows.LinkedInputs.lam : LamUsed D := I.named.lam
theorem _root_.GlobalTheory.NRows.LinkedInputs.isot : SumRepresentations.adm8 D := I.named.isot
theorem _root_.GlobalTheory.NRows.LinkedInputs.ser : GlobalTheory.TypeLeaf.SerLoc D := I.named.ser
theorem _root_.GlobalTheory.NRows.LinkedInputs.typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ I.X.R j t := I.named.typeNZ
theorem _root_.GlobalTheory.NRows.LinkedInputs.e0loc : GoodIdempotentFixesLocalisationForms D := goodIdempotentFixes_of_onlySeriesOfLabelActs I.ser
set_option linter.unusedSectionVars false in
theorem _root_.GlobalTheory.NRows.LinkedInputs.mtPar : MtParTie D.nd D.naut D.ntypes := D.mtpar_tie
theorem _root_.GlobalTheory.NRows.LinkedInputs.adm1 : SumRepresentations.adm1 D := base_change_automorphic_of D I.bc I.c1
theorem _root_.GlobalTheory.NRows.LinkedInputs.admAt (a : _root_.GlobalTheory.NRows.RowsAAlt D) (b : RowsB D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D :=
  ⟨⟨a.tie0, I.hypO, I.adm1, a.a2, b.a3, b.a4, a.a5⟩, a.temp⟩
theorem _root_.GlobalTheory.NRows.LinkedInputs.Conclusion1 (h : _root_.GlobalTheory.NRows.SummandsSuffice D) (a : _root_.GlobalTheory.NRows.RowsAAlt D) (b : RowsB D) : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D :=
  h (I.admAt a b) a.tieLab b.rowSize a.hecke I.lam.loc b.thetaOne a.g4p
end Inputs
end GlobalTheory.NRows
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankZeroOfRowConditions
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.L2.N.RankZeroOfLevelThree
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
open Formalism.L2.N.ExtNRows3 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
theorem rank_zero_of_row_conditions_alt {eps : ℝ} (Fm : FamP eps) (x0 : ℝ)
    (T : ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.TiedDataSKAlt (Fm.ex x hx i))
    (P : ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, RowSideFamily (Fm.ex x hx i))
    (hp : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), _root_.Formalism.L2.Rows.RowSideDeterminedAlt (T x hx h0 i) (P x hx h0 i))
    (hL : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), RowsHoldLam3 (P x hx h0 i))
    (hR : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), Formalism.L2.DIV.DivRows3 (Fm.D x i) (P x hx h0 i).A3 (P x hx h0 i).P0
      (P x hx h0 i).ψ0 (P x hx h0 i).Ps (P x hx h0 i).ψs (P x hx h0 i).Zs (P x hx h0 i).S0 (P x hx h0 i).S1 (Fm.ex x hx i).p0
      (P x hx h0 i).C (P x hx h0 i).NuC (P x hx h0 i).I)
    (h : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), RowsHold0_3 (P x hx h0 i))
    (ht : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), ∃ t : (P x hx h0 i).T,
      (P x hx h0 i).I.tup t = (Fm.D x i).what₂.mu0 ∧
      ∀ k : Fin (Fm.D x i).R.m, Function.Surjective (lPrj (Fm.D x i) (P x hx h0 i).A3.A (P x hx h0 i).P0
        (P x hx h0 i).ψ0 ((P x hx h0 i).A3.fam3.toSub2 (P x hx h0 i).Zs) k t).mulVec) :
    SmallLevelRankEq Fm := by
  refine ⟨max x0 (Fm.x1 + 1), fun x hxx i j hj => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hxx)
  have h0 : x0 ≤ x := le_trans (le_max_left _ _) hxx
  obtain ⟨t, htup, hsurj⟩ := ht x hx1 h0 i
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨k, rfl⟩ : ∃ k : Fin (Fm.D x i).R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have key := (_root_.Formalism.L2.N.ExtNRows3.thetaT_injective_and_finrank_Zj_eq_D0_of_surjective (T x hx1 h0 i) (P x hx1 h0 i) (hp x hx1 h0 i) (hL x hx1 h0 i) (h x hx1 h0 i) (hR x hx1 h0 i) k t (hsurj k)).2
  rw [htup] at key
  exact key
end Formalism.L2.N.RankZeroOfLevelThree
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RaysOfRayRecStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_rays_of_ray_rec' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), RayRec (p.w.D p.Z) p.O.ex.nch → (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Rays := by
  first | exact @_root_.GlobalTheory.Plug.RaysW.rays_of_rayRec_alt | exact _root_.GlobalTheory.Plug.RaysW.rays_of_rayRec_alt | (intros; apply _root_.GlobalTheory.Plug.RaysW.rays_of_rayRec_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRtEqOfGoodInert
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.InertFormFix.real_rt_eq_of_good_inert_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl Pp v → ∀ g : D.what₂.Mt (D.nd.mu i) (D.nd.j i), ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ → NG.rt D.host.E D.R.nV κ ((P.M.loc i).real g) = (P.M.loc i).real g := by
  intro hA hL D P X hX h41 h7 htie i hμ j hj h hh Pp hG hI v hv g κ hκ hT
  have hstd := hX.stdV j
  have hprime := GlobalTheory.InertFrameLoc.isPrimeIdem_tensAt hI rfl
  have hsupp := GlobalTheory.InertFormFix.suppF_of_trivOutside D hX.hF (Formalism.IndefR.Links.Vc D j) D.R.nV (hX.PV j) hstd Pp _ _ hprime v hv κ hT
  obtain ⟨c, hc⟩ := X.given.core.lev.βV j
  rw [one_pow] at hc
  have ls := (GlobalTheory.LevSplit.lev_split (Formalism.IndefR.Links.Vc D j) (X.R.βV j) (X.R.ΛV j) 1
    (Formalism.IndefR.RecTie.datVP X.R j (X.tupT (D.nd.mu i)) (X.R.levR X.F false)) hc).2 Pp _ _ hprime
    (by
      intro h1
      have : ((1 : ℕ) : 𝓞 D.host.E) = 1 := Nat.cast_one
      rw [this] at h1
      exact Pp.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1))
    (fun PP hPP => hG PP hPP)
  have hK : (hX.PV j).ψ κ ∈ Formalism.L2.Theta.KsphC (Formalism.IndefR.Links.Vc D j) ∅ := (hstd.2 κ).1 hκ
  have hlev := (ls.1 _ hsupp).2 hK
  have hchi := ls.2.1 _ hlev hsupp
  have hfix : ∀ (x : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) y,
      X.fn hμ j x (y * (hX.PV j).ψ κ) = X.fn hμ j x y := by
    intro x y
    have hm := ((X.IL.jMt (D.nd.mu i) hμ j) x).2
    obtain ⟨-, hm2⟩ := hm
    have e1 := hm2 ((hX.PV j).ψ κ) hlev y
    unfold GlobalTheory.NJoin.RealAt.fn
    rw [e1]
    rw [hchi]
    exact one_smul ℂ _
  have key : ∀ (j' : ℕ) (e : j.1 + 1 = j') (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m) (x : D.what₂.Mt (D.nd.mu i) j'),
      NG.rt D.host.E D.R.nV κ ((P.M (D.nd.mu i) j' h1 h2).real x) = (P.M (D.nd.mu i) j' h1 h2).real x := by
    intro j' e h1 h2 x
    subst e
    funext y
    show (P.M _ _ h1 h2).real x (y * κ) = _
    rw [hX.real (D.nd.mu i) hμ j x (y * κ), hX.real (D.nd.mu i) hμ j x y, ← mul_assoc, map_mul, hfix]
  exact key _ hj _ _ g
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting
namespace Formalism.L2.SG.SpectralTiesReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
structure STiesRAlt (R : _root_.Formalism.L2.RecTAlt ex) extends STies D where
  tr : ∀ u, Formalism.L2.SG.ColDict.Transport X u ((R.T.cols.forms u).to0)
  into : ∀ u, Formalism.L2.SG.ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, Formalism.L2.SG.ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, Formalism.L2.SG.ColDict.LevelMatch X (tr u) Y.hK
  colPin : ∀ (hF : FinX Y) (u : D.what₂.Word) (x : D.s.Cu u),
    Formalism.L2.SG.ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x
  inst : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D
  G : Formalism.L2.SG.RowDict.GoodOp X
  rowTie : ∀ hF : FinX Y, Formalism.L2.SG.RowDict.RowDictTie X G (hI hF).eHH
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D
end Formalism.L2.SG.SpectralTiesReal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSidePq
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.L2
namespace SelJ
variable {D : D7} {X : Col.Fields}
end SelJ
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
def SelInAlt (R : _root_.Formalism.L2.RecTAlt ex) (Side : Set (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  ∀ μ, ∀ P ∈ Col.QE R.T.ker.sel (R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K),
    ∀ P', SelJ.Carried R.T.ker.seam P P' → P' ∈ Side
def SelectedSideOfPrimeAbove (R : _root_.Formalism.L2.RecTAlt ex)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  (∀ v, NG.OverPl (Pq v) v) ∧ _root_.Formalism.L2.SelInAlt R (Set.range Pq)
end
end Formalism.L2
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWChrStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_psi_choice_tame_tie : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Formalism.L2.Host.PsiChoiceCompatible (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf p.O.ex.nch (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp ∧ (∀ v, (p.w.D p.Z).what₂.muAt v ≠ (p.w.D p.Z).what₂.mu0 → ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp.psi v).ValuesIn 0 (p.w.D p.Z).what₂.embLL) ∧ GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf.W.om := by
  first | exact @_root_.GlobalTheory.PlugPt.side_weight_psi_values_tame_tie | exact _root_.GlobalTheory.PlugPt.side_weight_psi_values_tame_tie | (intros; apply _root_.GlobalTheory.PlugPt.side_weight_psi_values_tame_tie <;> assumption)
end
end

