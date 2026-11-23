module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedMatchOfHeckeGalois
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefRingTakenOfLocalisationCoefficientExte
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0290
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0289

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Conclusion42OfParts
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.NRows.Parts
theorem conclusion42_of_parts (D : D7) (a : _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D) (s : GlobalTheory.RowCopy.RowSize D) (hk : GlobalTheory.RowCopy.HeckeSplitOne D)
    (l : ∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) (th : GlobalTheory.RowCopy.ThetaOne D) : SumRepresentations.ReducedParameterProposition D := by
  obtain ⟨⟨t0, hO, a1, a2, a3, a4, a5⟩, a7⟩ := a
  intro i σ hσ
  obtain ⟨P, hP⟩ := th i σ hσ
  obtain ⟨Pa, hPa⟩ := a1 i P
  obtain ⟨Sig, h1, h2⟩ := GlobalTheory.T.row_param_of_thetaLift_baseChange D t0 a3 a4 a5 i σ P Pa hP hPa (_root_.GlobalTheory.T.twisted_mu_piece_mem_base_change D t0 a3 a5 a7 s hk i σ P Pa hσ hP hPa)
  refine ⟨⟨⟨_, (l i σ).2 hσ, (l i σ).1⟩, P, hP⟩, Sig, h1, fun P' hP' => ?_⟩
  obtain rfl : P = P' := by
    by_contra hne
    exact hP.1 (le_bot_iff.1 ((le_inf hP.2 hP'.2).trans ((D.naut.typeV_indep i).pairwiseDisjoint hne).le_bot))
  exact h2
end GlobalTheory.NRows.Parts
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvIpAtLeNormAtSqStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_tilde_gamma_values_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → K.c.mu P.A3.fam3.base3.μ0 = 1 → ∀ X0, IsFrames (P.A3.side3 P.Ps P.ψs P.Zs) X0 → ∀ v F, ((Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu P.A3.fam3.base3.μ0) K.c.Lv).ipAt (K.c.hP P.A3.fam3.base3.μ0) v ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1 ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV P.A3.fam3.base3.μ0))) X0 v F ^ 2 := by
  first | exact @_root_.GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq_alt | exact _root_.GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq_alt | (intros; apply _root_.GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOTakenAll
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.CoefDuty.TakenLarge
set_option maxHeartbeats 4000000 in
theorem evO_takenAll_alt : GlobalTheory.TwSys.Cheb → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ GlobalTheory.SplitCoef.OSplit D' ∧ ∀ i, ZDecomp D'.nd i) → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup TakenAll := by
  intro hCh hHS D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hE hsplit hCS2 hB hQ
  classical
  obtain ⟨bigA, hA⟩ := hQ
  obtain ⟨L₀, hL₀⟩ := hB bigA
  have hQ₀ := hA L₀ hL₀
  obtain ⟨big₁, h₁⟩ :=
    _root_.GlobalTheory.T.side_eigen_integrality_alt hHS D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hE hsplit hCS2 bigA L₀ hL₀
  have hc₀ := _root_.GlobalTheory.T.contains_after_localization_alt D cf jE A M C tp.tup bigA L₀ hL₀
  let S0 : L₀.X.nd.Loc → Finset ℂ := fun i =>
    if h : ∃ S : Finset ℂ, Chosen (withLoc L₀).nd (withLoc L₀).naut i ↑S then h.choose else ∅
  let big : D.what₂.places.Pl → Finset ℂ := fun w =>
    big₁ w ∪ (Finset.range (D.R.m + 1)).biUnion (fun j => (L₀.X.nd.locs j w).biUnion S0)
  refine ⟨big, fun L₁ hL₁ => ?_⟩
  have hL₁' : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ :=
    (_root_.GlobalTheory.T.eventually_conjunction_mono_alt D cf jE A M C tp.tup (fun _ => True) (fun _ => True)).2.2.2 big₁ big L₁
      (fun w => Finset.subset_union_left) hL₁
  have hc₁ := _root_.GlobalTheory.T.contains_after_localization_alt D cf jE A M C tp.tup big L₁ hL₁
  intro i₁ hlive₁
  obtain ⟨i₀, hw, ⟨e⟩⟩ := h₁ L₁ hL₁' i₁
  have hc₀i := hc₀ i₀
  have hc₁i := hc₁ i₁
  have hgood₀ : ∃ r, GoodR L₀.lay.fixZ.nd i₀ r := hc₀i.2.2.2.2.2.1.1 (hQ₀.1 i₀).1.2
  have hZ₀ : ZDecomp L₀.lay.fixZ.nd i₀ := hc₀i.2.2.2.1.1 (hQ₀.2.2 i₀)
  have hlive₀ : Live L₀.lay.fixZ.nd i₀ :=
    _root_.GlobalTheory.LiveDescent.live_of_locExt hCh _ _ _ _ i₀ i₁ e hgood₀ hZ₀ (hc₁i.2.2.1.1 hlive₁)
  have hex : ∃ S : Finset ℂ, Chosen (withLoc L₀).nd (withLoc L₀).naut i₀ ↑S :=
    _root_.GlobalTheory.T.exists_finset_chosen_of_cheb_oSplit hCh (withLoc L₀) hQ₀.1 hQ₀.2.1 i₀ (hQ₀.2.2 i₀) (hc₀i.2.2.1.2 hlive₀)
  have hch : Chosen (withLoc L₀).nd (withLoc L₀).naut i₀ ↑(S0 i₀) := by
    simp only [S0, dif_pos hex]
    exact hex.choose_spec
  have hch' := (hc₀i.2.2.2.2.1 _).1 hch
  have hsub : S0 i₀ ⊆ big (L₁.X.nd.w i₁) := by
    intro z hz
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨L₀.X.nd.j i₀, ?_, Finset.mem_biUnion.2 ⟨i₀, ?_, hz⟩⟩)
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (L₀.X.nd.j_range i₀).2)
    · exact (L₀.X.nd.locs_mem _ _ _).2 ⟨rfl, hw⟩
  have hcont : Contains L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ↑(S0 i₀) := fun z hz => hc₁i.2.1 z (hsub hz)
  exact (hc₁i.2.2.2.2.2.2).2 (_root_.GlobalTheory.CoefDuty.Take.takenWild_of_locExt _ _ _ _ i₀ i₁ e _ hch' hcont)
end GlobalTheory.CoefDuty.TakenLarge
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobEigTwEqInvValV
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TieFrob
theorem frobEig_tw_eq_inv_valV_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {((GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂˣ) : ℂ)⁻¹} := by
  intro _ hL D P X _ _ i hμ j hj w hG _
  have hIs := X.recR.base.lev
  set t := X.tupT (D.nd.mu i) with ht
  have hV : GlobalTheory.DownLift.valV X.R j t w = (X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹).val w := by
    have e1 : GlobalTheory.DownLift.valV X.R j t w =
        GlobalTheory.LFun.val (X.R.toLevCh.mu0 (j.1 + 1)) w * GlobalTheory.LFun.val (X.R.toLevCh.xi t) w *
          (GlobalTheory.LFun.val X.R.toLevCh.eta w)⁻¹ := by
      show GlobalTheory.LFun.val (X.R.toLevCh.mu0 (j.1 + 1) * X.R.toLevCh.xi t * X.R.toLevCh.eta⁻¹) w = _
      rw [GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv]
    rw [e1, GlobalTheory.LFun.val_eq_of_chrEq (hIs.mu0 j), GlobalTheory.LFun.val_eq_of_chrEq (hIs.xi t),
      GlobalTheory.LFun.val_eq_of_chrEq hIs.eta, HChar.val_mul, HChar.val_mul, HChar.val_inv]
  have hxi : X.R.xiH t = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ]
    exact congrFun (xi_eq_of_heq X.cfEq X.Tp P.tp X.tpEq) _
  have hE : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹ := by
    rw [P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv, hxi, X.cfEq]
    rfl
  have hU : (X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹).UnrAt w := by
    refine HChar.UnrAt.mul (HChar.UnrAt.mul ?_ ?_) (HChar.UnrAt.inv (X.R.C.isEta.unr w))
    · refine (X.R.C.isMu0 j).unr w fun k hk => ?_
      rcases GlobalTheory.StepLaw.div_or_isConjPl_div D X.R.C.P k w hk with hd | ⟨PP, hd, hc⟩
      · exact (hG w (Or.inl ((hIs.Pg w).2 ⟨k, hd⟩))).1 rfl
      · exact (hG PP (Or.inl ((hIs.Pg PP).2 ⟨k, hd⟩))).2 hc
    · by_contra hn
      rcases (hIs.Q_ram t w).1 hn with hq | ⟨PP, hq, hc⟩
      · exact (hG w (Or.inr hq)).1 rfl
      · exact (hG PP (Or.inr hq)).2 hc
  rw [P.chr.frob _ w (by rw [hE]; exact hU), hE, hV, Units.val_inv_eq_inv_val]
end GlobalTheory.TieFrob
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodNotMemBadPl
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GoodOffBad
theorem good_not_mem_badPl_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), Formalism.L2.NG.OverPl Pp v → v ∉ Formalism.L2.badPl D i := by
  intro hL D P X i _ w hG v hov
  have hlev := X.recR.base.lev
  have hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i) := by
    rcases D.what₂.muAt_or (D.nd.w i) with h | h
    · exact absurd h (D.nd.w_tw i)
    · rw [h, D.nd.mu_w i]
  have hxi := X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)
  have hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra hn
    rcases (hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr hPP)).2 hc
  rw [hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i] at hunr
  have hψ := X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i] at hψ
  set δ := X.R.C.delAt (D.nd.l i) with hδdef
  set ψ := X.Tp.psi (D.nd.w i) with hψdef
  set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef
  have hd : IsDelta (H := D.host) p δ := by
    rw [hδdef, hpdef, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x := fun _ => rfl
  have hnp : ¬ OverP D.host p w := by
    intro hw
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 : 15 ∣ D.nd.l i ^ a := by
      refine (hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_
      have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
      have h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1 := by
        have := congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha
        simpa [HChar.loc] using this
      have h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1 := by rw [h1, one_pow]
      rwa [mul_pow, h2, mul_one] at h3
    have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
    have h3 : 3 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
      (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    have h5 : 5 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq (by norm_num) hl).1
      ((show (5 : ℕ).Prime by norm_num).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    omega
  have hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hw
    have hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k) := D.nd.g_split k
    rcases (GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩
    · exact (hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl
    · exact (hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc
  have hnQ : w ∉ D.nd.Q i := by
    intro hQ
    rw [P.Q_eq i] at hQ
    refine (hψ.ram w).1 ?_ hQ
    intro x hx
    have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
    rw [hd.unr w hnp x hx, one_mul] at h1
    exact h1
  have hnp' : w ∉ placesOver D.host.E p := hnp
  rintro ⟨w', hover, hw'⟩
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE w w' (hover.trans hov.symm) with e | e
  · subst e
    rcases hw' with hQ | ⟨k, hg⟩ | hpd
    · exact hnQ hQ
    · exact hng k hg
    · exact hnp' hpd
  · subst e
    rcases hw' with hQ | ⟨k, hg⟩ | hpd
    · exact hnQ (P.H.hecke.Q_conj i _ w (isConjPl_conjPlE_left w) hQ)
    · exact hng k ((conjPlE_mem_placesOver w _).1 hg)
    · exact hnp' ((conjPlE_mem_placesOver w _).1 hpd)
end GlobalTheory.GoodOffBad
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodNotMemSQStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_place_not_mem_S_and_Q_of_used0 : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Pp ∉ D.nd.S i ∧ Pp ∉ D.nd.Q i := by
  first | exact @_root_.GlobalTheory.GoodOffLoc.good_not_mem_S_Q_alt | exact _root_.GlobalTheory.GoodOffLoc.good_not_mem_S_Q_alt | (intros; apply _root_.GlobalTheory.GoodOffLoc.good_not_mem_S_Q_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffSQ
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.OffSQ
theorem good_off_SQ_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → w ∉ D.nd.S i ∧ w ∉ D.nd.Q i := by
  intro hL D P X hA _ _ i w hG
  have hlev := X.recR.base.lev
  have hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i) := by
    rcases D.what₂.muAt_or (D.nd.w i) with h | h
    · exact absurd h (D.nd.w_tw i)
    · rw [h, D.nd.mu_w i]
  have hxi := X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)
  have hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra hn
    rcases (hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr hPP)).2 hc
  rw [hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i] at hunr
  have hψ := X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i] at hψ
  set δ := X.R.C.delAt (D.nd.l i) with hδdef
  set ψ := X.Tp.psi (D.nd.w i) with hψdef
  set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef
  have hd : IsDelta (H := D.host) p δ := by
    rw [hδdef, hpdef, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x := fun _ => rfl
  have hnp : ¬ OverP D.host p w := by
    intro hw
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 : 15 ∣ D.nd.l i ^ a := by
      refine (hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_
      have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
      have h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1 := by
        have := congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha
        simpa [HChar.loc] using this
      have h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1 := by rw [h1, one_pow]
      rwa [mul_pow, h2, mul_one] at h3
    have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
    have h3 : 3 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
      (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    have h5 : 5 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq (by norm_num) hl).1
      ((show (5 : ℕ).Prime by norm_num).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    omega
  have hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hw
    have hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k) := D.nd.g_split k
    rcases (GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩
    · exact (hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl
    · exact (hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc
  refine ⟨fun hS => ?_, fun hQ => ?_⟩
  · rcases ((D.nd.S_def i w).1 hS).1 with h | h | h
    · exact hng 0 h
    · exact hng 1 h
    · exact hnp h
  · rw [P.Q_eq i] at hQ
    refine (hψ.ram w).1 ?_ hQ
    intro x hx
    have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
    rw [hd.unr w hnp x hx, one_mul] at h1
    exact h1
end GlobalTheory.OffSQ
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSide
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RowModCanon
open MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace
open scoped InnerProductSpace
end GlobalTheory.RowModCanon
namespace GlobalTheory.RowModCanon
open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (j : Fin D.R.m) (j' : ℕ)
    (hj : j.1 + 1 = j'), ∃ Y : RowMod D P.rep j', GlobalTheory.NJoin.IsCanon X j hj Y := by
  intro hH hC hL D P X hA j j' hj
  subst hj
  have hmod := X.given.core.models
  have hθ := hmod.inf
  have hν := hmod.νW j
  have hHaar : (X.R.νW j).IsHaarMeasure := hν.1.1
  have hFD := hν.2
  have hSig : (Wc D j).SigOK := D.sp.W_sig _
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  have hStd : GlobalTheory.Mem.R3.StdFrame hA.hF (X.PW j) := hA.stdW j
  have hcc := _root_.GlobalTheory.CongConjugate.congConj D.host.E D.R.r
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := X.R.MW j (sg0 D X.A)) (θ := X.R.θ) (X.R.νW j) (X.R.fdW j)
    (X.PW j) hSA hSig hθ hHaar hFD
  have hT := X.recR.tied.lift
  have hLev := GlobalTheory.FinTypesRows.levOK_levS (X.PW j) hStd (X.R.βW j) (X.R.datWp j (X.R.levL X.F false (sg0 D X.A)))
  set c : ℝ := (∏ ρ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D X.A) ρ) : ℚ) : ℝ)) * (RealDat.nP X.F false)⁻¹ with hcdef
  have hc : 0 < c := mul_pos (Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.EasyInputs.dimOK D j (sg0 D X.A) ρ)
    (inv_pos.2 (RealDat.nP_pos false))
  have hSm := GlobalTheory.Mem.EasyInputs.smAll D (Wc D j) _ (X.R.MW j (sg0 D X.A))
  have hex : ∀ x ∈ principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)), ∀ y ∈ principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)),
      ∃ b, Mult.IsMultIP (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) x y b := by
    intro x hx y hy
    obtain ⟨N, -, hx', hy'⟩ := GlobalTheory.FinTypesRows.exists_common (X.PW j) hx hy
    exact hSA _ hSig _ X.R.θ _ _ _ _ _ hθ hHaar hFD x hx' y hy'
  let φ : D.what₂.Mj (j.1 + 1) →ₗ[ℂ] Mult.MMap (X.R.MW j (sg0 D X.A)) :=
    (PiTensorProduct.lift : Mult.MMap (X.R.MW j (sg0 D X.A)) ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ
      (Submodule.subtype ((toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).Wc j)) ∘ₗ (X.IL.jMj j).toLinearMap
  have hφ : ∀ y, PiTensorProduct.lift (φ y) = (X.IL.jMj j y).1 := by
    intro y
    exact LinearEquiv.apply_symm_apply _ _
  have hgood : ∀ y, φ y ∈ Mult.goodPart X.R.θ (X.R.MW j (sg0 D X.A)) (levS _ (X.R.βW j) (X.R.datWp j (X.R.levL X.F false (sg0 D X.A))))
      (levChi _ (X.R.βW j) (X.R.datWp j (X.R.levL X.F false (sg0 D X.A)))) (X.R.eWf j (sg0 D X.A)) := by
    intro y
    obtain ⟨a, ha, hay⟩ := (X.IL.jMj j y).2
    have : φ y = a := by
      show PiTensorProduct.lift.symm (X.IL.jMj j y).1 = a
      rw [← hay]
      exact LinearEquiv.symm_apply_apply _ _
    rw [this]
    exact ha
  have hmem : ∀ y, φ y ∈ principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) := fun y =>
    principalLevelFrame.mult_le_Minf hLev (Mult.goodPart_le _ _ _ _ _ (hgood y))
  refine ⟨{ A := Mult.MMap (X.R.MW j (sg0 D X.A))
            ρ := principalLevelFrame.actM (X.PW j) (X.R.MW j (sg0 D X.A))
            C := principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A))
            B := fun x y => (c : ℂ) * Mult.ipM (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) x y
            lin := fun x hx y hy z hz c' => by
              rw [hlin x hx y hy z hz c']
              ring
            herm := fun x hx y hy => by
              rw [map_mul, Complex.conj_ofReal, ← hherm x hx y hy]
            pos := fun x hx hx0 => by
              rw [Complex.re_ofReal_mul]
              exact mul_pos hc (hpos x hx hx0)
            stab := fun h x hx => GlobalTheory.FinTypesRows.minf_stable (X.PW j) hcc h hx
            inv := fun h x hx y hy => by
              rw [_root_.GlobalTheory.SchurPairingInvariant.ipM_actM D (Wc D j) _ X.R.θ (X.R.MW j (sg0 D X.A)) D.R.r (X.PW j) (X.R.νW j) (X.R.fdW j) hSA hSig hθ
                hHaar hFD h x hx y hy]
            smooth := fun x hx => GlobalTheory.FinTypesRows.minf_smooth (X.PW j) hx
            adm := fun N hN => GlobalTheory.FinTypesRows.minf_adm (X.PW j) hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open (X.PW j) hStd) N hN
            φ := φ
            φ_mem := hmem
            φ_inner := fun x y => by
              beta_reduce
              rw [hT.mj j x y]
              change (∏ τ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D X.A) τ) : ℚ) : ℂ)) *
                Mult.ipM (X.R.MW j (sg0 D X.A)) (ENNReal.ofReal (RealDat.nP X.F false)⁻¹ • X.R.νW j) (X.R.fdW j) (φ x) (φ y) = _
              rw [ipM_smul_measure _ hSm _ _ (inv_nonneg.2 (RealDat.nP_pos false).le) _ _ (hex _ (hmem x) _ (hmem y)), hcdef]
              push_cast
              ring
            isot := fun σ y => by
              rw [hT.isot j σ y, X.recR.prtWE j σ, principalLevelFrame.isotIn_iso _ _ (hA.rep_iso σ)]
              constructor
              · rintro ⟨a, ha, hay⟩
                have e : φ y = a := by
                  show PiTensorProduct.lift.symm (X.IL.jMj j y).1 = a
                  rw [← hay]
                  exact LinearEquiv.symm_apply_apply _ _
                rw [e]
                exact (Submodule.mem_inf.1 ha).2
              · intro h
                exact ⟨φ y, Submodule.mem_inf.2 ⟨hgood y, h⟩, hφ y⟩ }, LinearMap.id, c, Function.injective_id, hc, Submodule.map_id _, fun h x => rfl, fun x _ y _ => rfl,
            fun y => hφ y⟩
end GlobalTheory.RowModCanon
end
end
end

