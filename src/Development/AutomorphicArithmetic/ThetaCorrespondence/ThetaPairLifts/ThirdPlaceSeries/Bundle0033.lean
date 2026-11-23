module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
public import Formalism.LocalToGlobal.ClassS
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0742
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Formalism.LocalToGlobal.UnitaryNorms.DatumS
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0229
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0028

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMuUnrFrobStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_hecke_compatible_alt : ∀ (hArt : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (hψ : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (μ : D.naut.CG 1), D.naut.csd μ → (∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j) → ∀ w, SplitOut X.nd i w → D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) ∧ ∀ (B : ValuationSubring X.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om), IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ → D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)) = {(qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i)))} := by
  first | exact @_root_.GlobalTheory.AutPart.chiMu_unr_frob_alt | exact _root_.GlobalTheory.AutPart.chiMu_unr_frob_alt | (intros; apply _root_.GlobalTheory.AutPart.chiMu_unr_frob_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClosedRankTiesFC2S
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.Ext.Lw
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.Forms Formalism.BasicNotions
open scoped TensorProduct
theorem rankTiesF_of_C2S_alt {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondChernLinkedClass Fm) : RankTiesF Fm := by
  obtain ⟨x0, h⟩ := h
  refine rank_conditions_of_lowest_space Fm ⟨max x0 (Fm.x1 + 1), fun x hx i u => ?_⟩
  have e1 : Fm.x1 < x := by
    have := (le_max_right x0 (Fm.x1 + 1)).trans hx
    linarith
  obtain ⟨T⟩ := h x e1 ((le_max_left _ _).trans hx) i
  exact mu0Tie_of_sym T.cols u
theorem second_chern_linked_closed_rank_ties : Closed _root_.Formalism.L2.SecondChernLinkedClass fun Fm _ => RankTiesF Fm :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hC _ => _root_.Formalism.MainNotions.Ext.Lw.rankTiesF_of_C2S_alt Fm hC⟩⟩
end Formalism.MainNotions.Ext.Lw
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOHypO
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.LargeO
theorem evO_hypO_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup SumRepresentations.hypO := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
  classical
  have hbig : ∀ lam (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
      (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.places.resChar lam) (C.Q lam)).Finite →
      ∃ Sf, @BigOk D (D.what₂.places.resChar lam) ⟨D.what₂.places.resChar_prime lam⟩ (C.Q lam)
        (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.places.resChar lam) (C.Q lam)) (A.pl.ι lam) Sf :=
    fun lam j h1 h2 hf => @exists_bigOk D _ ⟨D.what₂.places.resChar_prime lam⟩ _ _ _ hf hcheb
  let big : D.what₂.places.Pl → Finset ℂ := fun lam => (Finset.range (D.R.m + 1)).biUnion fun j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then
      if hf : (EigSet (M (D.what₂.muTw lam) j h.1 h.2) (D.what₂.places.resChar lam) (C.Q lam)).Finite then
        Classical.choose (hbig lam j h.1 h.2 hf) else ∅
    else ∅
  refine ⟨big, fun L hB => ?_⟩
  obtain ⟨Sp, ⟨Au⟩, hss⟩ := hB
  intro i x ρ hρ
  haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i
  have hB' : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L := ⟨Sp, ⟨Au⟩, hss⟩
  obtain ⟨hfin, hpt⟩ := _root_.GlobalTheory.T.side_eigen_unitary_alt hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB' i x
  have hj := L.X.nd.j_range i
  have hOk : @BigOk D (D.what₂.places.resChar (L.X.nd.w i)) ⟨D.what₂.places.resChar_prime (L.X.nd.w i)⟩
      (C.Q (L.X.nd.w i)) (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) hj.1 hj.2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))) (A.pl.ι (L.X.nd.w i)) (big (L.X.nd.w i)) := by
    have hc := Classical.choose_spec (hbig (L.X.nd.w i) (L.X.nd.j i) hj.1 hj.2 hfin)
    refine bigOk_mono hc ?_
    intro z hz
    refine Finset.mem_biUnion.2 ⟨L.X.nd.j i, Finset.mem_range.2 (by omega), ?_⟩
    rw [dite_eq_left hj, dite_eq_left hfin]
    exact hz
  have hOk' := bigOk_cast (L.X.nd.w_l i) hOk
  obtain ⟨K, hK, -, -⟩ := _root_.GlobalTheory.Proof.CoefField.coefField_range (withLoc L).nd (withLoc L).naut i
  have hcont := (_root_.GlobalTheory.T.contains_after_localization_alt D cf jE A M C tp.tup big L hB' i).1
  have hKbig : ∀ z ∈ big (L.X.nd.w i), (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).symm z ∈ K := by
    intro z hz
    obtain ⟨y, hy⟩ := hcont z hz
    have hy' : L.Y.naut.iotaQC i (L.Y.naut.iotaQ i y) = z := hy
    rw [Au.iotaQC i] at hy'
    rw [← hy', RingEquiv.symm_apply_apply]
    exact (hK _).2 ⟨y, rfl⟩
  have hQ : L.X.nd.Q i = C.Q (L.X.nd.w i) :=
    (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  have hchar := charpoly_pt (withLoc L) i x ρ hρ
  have hchar' : ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (L.X.nd.l i) ∧ v ∉ placesS D (L.X.nd.l i) ∧
      v ∉ C.Q (L.X.nd.w i)) → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ →
      (show Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (L.X.nd.l i)) from (ρ σ).val).charpoly.map
        (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).toRingHom = sysPol D.R.nV (ptSys (withLoc L) i x) v := by
    intro v hv B σ hB hF
    rw [← Au.iotaQC i]
    exact hchar v ⟨hv.1, hv.2.1, hv.2.2.1, hQ ▸ hv.2.2.2⟩ B σ hB hF
  obtain ⟨P, hP⟩ := hOk' _ hpt K hKbig ρ hρ.1 hρ.2.1 hchar'
  exact model_of_conj (withLoc L).nd (withLoc L).naut i _ ρ P hρ.1 (fun g s t => (hK _).1 (hP g s t))
end GlobalTheory.LargeO
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsBigOSplit
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.OSplitBig
theorem exists_big_oSplit_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∃ big : D.what₂.places.Pl → Finset ℂ, ∀ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C → GlobalTheory.SplitCoef.OSplit (withLoc L) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb
  classical
  have hsys := fun w => _root_.GlobalTheory.T.galois_family_local_global_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb w
  choose FA Sy hSy using hsys
  have hexc := fun w : D.what₂.places.Pl => _root_.GlobalTheory.PlacesExc.finite_exceptional D (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)
  choose FB hFB using hexc
  let Fw : D.what₂.places.Pl → Finset (PlE D.host) := fun w => FA w ∪ FB w ∪ C.Q w
  let Pv : D.what₂.places.Pl → Formalism.ConjugateSelfDual.G D.host.E D.nd.Om → PlE D.host → Prop := fun w σ v =>
    v ∉ Fw w ∧ IsSplitPl D.host v ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ
  let pw : D.what₂.places.Pl → (PlE D.host → ℕ → ℂ) → Formalism.ConjugateSelfDual.G D.host.E D.nd.Om → ℂ[X] := fun w c σ =>
    if h : ∃ v, Pv w σ v then sysPol D c h.choose else 0
  have hcore := fun (w : D.what₂.places.Pl) (c : PlE D.host → ℕ → ℂ) =>
    _root_.GlobalTheory.OSplitCore.exists_splitting_set (D.what₂.places.resChar w) (A.pl.ι w) D.host.E D.nd.Om D.R.nV (frobSet D (Fw w)) (pw w c)
      (dense_frobSet D hCheb (Fw w))
  choose SC hSC using hcore
  refine ⟨fun w => (Sy w).biUnion (SC w), ?_⟩
  intro L Sp hAut i x r hr
  obtain ⟨c, hcS, hc⟩ := hSy ((withLoc L).nd.w i) _ L Sp hAut i x rfl
  haveI : Fact ((withLoc L).nd.l i).Prime := (withLoc L).nd.lPrime i
  letI := (withLoc L).nd.dvrO i
  letI := (withLoc L).nd.algO i
  letI := (withLoc L).nd.finO i
  letI := (withLoc L).nd.topO i
  letI := (withLoc L).nd.trO i
  refine hSC ((withLoc L).nd.w i) c ((withLoc L).nd.l i) ((withLoc L).nd.w_l i) ((withLoc L).nd.O i) ((withLoc L).nd.O_adic i) (Sp.iq i) ?_ ?_ r
    hr.1 hr.2.1 ?_
  · exact fun z => Sp.iq_alg i z
  · intro z hz
    exact Sp.iq_big i z (Finset.mem_biUnion.2 ⟨c, hcS, hz⟩)
  · intro σ hσ
    have hex : ∃ v, Pv ((withLoc L).nd.w i) σ v := hσ
    have hspec := hex.choose_spec
    obtain ⟨hvF, hvs, B, hB, hFr⟩ := hspec
    have hvF' := hvF
    simp only [Fw, Finset.mem_union, not_or] at hvF'
    obtain ⟨⟨hvA, hvB⟩, hvQ⟩ := hvF'
    have hSO : SplitOut (withLoc L).nd i hex.choose := by
      have hQi : (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i) :=
        (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
      obtain ⟨h1, h2⟩ := hFB ((withLoc L).nd.w i) _ hvB
      refine ⟨hvs, ?_, ?_, ?_⟩
      · rw [← (withLoc L).nd.w_l i]; exact h1
      · intro hmem
        apply h2
        have := ((withLoc L).nd.S_def i _).1 hmem
        rw [← (withLoc L).nd.w_l i] at this
        exact this
      · show _ ∉ (withLoc L).nd.Q i
        rw [hQi]; exact hvQ
    refine (congrArg (Polynomial.map _) (hr.2.2 _ hSO B σ hB hFr)).trans ?_
    have hio : (qCast ((withLoc L).nd.w_l i) (A.pl.ι ((withLoc L).nd.w i))).toRingHom.comp
        ((Sp.iq i).comp (algebraMap ((withLoc L).nd.O i) (FractionRing ((withLoc L).nd.O i)))) = iotaOC (withLoc L) i := by
      ext z
      simp only [iotaOC, RingHom.comp_apply]
      rw [show (withLoc L).naut.iotaQC i = L.Y.naut.iotaQC i from rfl, hAut.iotaQC i,
        show (withLoc L).naut.iotaQ i = L.Y.naut.iotaQ i from rfl, hAut.iotaQ i]
      rfl
    refine (congrArg (fun f => (heckePol (withLoc L).nd i x hex.choose).map f) hio).trans ?_
    rw [heckePol_map D L i x _ hSO]
    simp only [pw, dif_pos hex, sysPol]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc _ hvA k]
end GlobalTheory.OSplitBig
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GTiedFOfC2S
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
theorem gTiedF_of_C2S_alt {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondChernLinkedClass Fm) : G.GroupCompatibilityFamily Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i hx1 => ?_⟩
  obtain ⟨T⟩ := hx0 x hx1 ((le_max_left _ _).trans hx) i
  exact ⟨T.g⟩
end Formalism.L2
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckePolMapEqFrobPolStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_trace_frobenius_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → ∀ P x, ptV P = some x → ∀ w, SplitOut X.nd i w → (heckePol X.nd i x w).map (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) = ((D.naut.frobEig (D.naut.lpTw (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) ((1 - (D.R.nV : ℝ)) / 2))).map fun α => Polynomial.X - Polynomial.C α).prod := by
  first | exact @_root_.GlobalTheory.AutPart.heckePol_map_eq_frobPol_alt | exact _root_.GlobalTheory.AutPart.heckePol_map_eq_frobPol_alt | (intros; apply _root_.GlobalTheory.AutPart.heckePol_map_eq_frobPol_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkBCharpolySplitsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_basis_free_module_place_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (hst : HkStab D T S In) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host)
      [hfr : Module.Free (T.O i) ↥(BI D T S In i j b)] [hfi : Module.Finite (T.O i) ↥(BI D T S In i j b)], P ∉ T.S0 i →
      ∃ s : Multiset (FractionRing (T.O i)),
        (LinearMap.charpoly (hkB D T S In hst i j b k P)).map
          (algebraMap (T.O i) (FractionRing (T.O i))) = (s.map fun a => X - C a).prod := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.hkB_charpoly_splits_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.hkB_charpoly_splits_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.hkB_charpoly_splits_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
namespace Host
end Host
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure HostDatumWithTies {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSAlt ex) where
  d3b : Host.PlacesOverCommonPrime D.host
  Tu_g : ∀ u i, (D.mem u).A.T ≠ D.host.g i
  Qw_Tu : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ ex.nch.Q w, ∀ u, ¬ Host.OverP D.host (D.mem u).A.T v
  clsK : Host.ClsRepK D.host
  clsK_Tu : ∀ c u, IsCoprime (clsK.rep c : Ideal (𝓞 D.host.K)) (Host.idK (H := D.host) (D.mem u).A.T)
  clsK_Qw : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ ex.nch.Q w, ∀ c,
    Host.PrimeToPl (H := D.host) (clsK.rep c : Ideal (𝓞 D.host.K)) v
  LLgal : IsGalois ℚ T.host.LLQ
  HE : Fld
  HE_fd : FiniteDimensional ℚ HE
  HE_hilb : Host.IsHilbertCFE (hL := HE_fd) D.host HE
  HE_le : HE ≤ Rows.KsQ D T.host T.n.cf T.what₂.O.pieces
def HostDatumSelfDual {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSAlt ex) : Prop := Nonempty (_root_.Formalism.L2.HostDatumWithTies T)
end
end Formalism.L2
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisFurther
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypeBlockPf
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → TypeBlock S i w hw := by
  intro hL D P S hT i w hw ⟨k, hk⟩ htame
  refine ⟨htame, fun Q => ?_⟩
  obtain ⟨s, rfl⟩ := splitAt D w hw
  obtain ⟨c, T, hc, hcs, -, -, -⟩ := hT.rep i s hw Q
  have hf : ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧
      ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x →
        Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t →
        NG.rt D.host.E D.R.nV x f =
          blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
    obtain ⟨v, e | e⟩ := GlobalTheory.DimPartsCompare.cover k s.w hk
    · exact _root_.GlobalTheory.T.split_place_completion_iso_tame_alt hL D P S hT i k v s hw e htame c hc hcs Q
    · exact _root_.GlobalTheory.T.conjugate_place_completion_iso_tame_alt hL D P S hT i k v s hw e htame c hc hcs Q
  obtain ⟨f, hfS, hf0, hfe⟩ := hf
  obtain ⟨y, hy0, hy⟩ := _root_.GlobalTheory.EigLocal.exists_eigen_local D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _
    (hT.rep i s hw Q) c hc hcs (blockGrp _ D.R.r D.R.t) (blockChar (S i s.w hw).mu) (fun h hh => hh.1)
    (fun h hh => ⟨kOne_le_blockGrp _ _ hh, blockChar_kOne _ htame hh⟩) f hfS hf0 hfe
  exact ⟨y, hy0, isBlockVec_of _ _ _ hy⟩
end GlobalTheory.TypeBlockPf
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisRest
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowPointLoc
theorem main_alt_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D)
    (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) :
    GlobalTheory.SplitRead.RowPoint D.nd D.naut := by
  intro i σ hne
  obtain ⟨Q, hQ⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ :=
    _root_.GlobalTheory.LiftPoint.main D P.M P.H.hecke P.H.av P.H.cover (_root_.GlobalTheory.T.heckeStdTw_cover' hL D P) i σ Q hQ
  obtain ⟨hj, hw⟩ := (D.nd.locs_mem _ _ i').1 hi'
  have hl : D.nd.l i' = D.nd.l i := by rw [← D.nd.w_l i', ← D.nd.w_l i, hw]
  obtain ⟨φ, hφ⟩ := P.H.hecke.sameO i' i hj hw
  refine ⟨i', hj, hl, fun w _ => P.locW_eq i' i σ w, ⟨φ, ?_, fun z => (hφ z).symm⟩, P', x', hth, hx⟩
  exact continuous_of_adic (D.nd.O_adic i') (D.nd.O_adic i) φ
end GlobalTheory.RowPointLoc
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreRest
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.PtExt
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ i₁ : L₁.lay.fixZ.nd.Loc, ∃ i₀ : L₀.lay.fixZ.nd.Loc, L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧ L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ ∧ ∃ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, ∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x)) := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big₀ big₁ L₀ L₁ hB₀ hB₁ i₁
  have onto : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 →
      ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w),
        ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, sys L i x = c := by
    intro big L hB j w h1 h2 htw c hc
    obtain ⟨i, hi, x, hx⟩ := _root_.GlobalTheory.T.side_eigen_frobenius_alt hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big L hB j w h1 h2 htw c hc
    refine ⟨i, hi, x, funext fun v => funext fun k => ?_⟩
    by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
    · rw [_root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi x hg, hx v k hg]
    · rw [_root_.GlobalTheory.PtExt.sys_eq_zero_of_not_gen_at hB hi x hg, hc.1 v k hg]
  have cong : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w →
      ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'),
        (i = i' ↔ ∀ v k, sys L i x v k - sys L i' x' v k ∈ (A.pl.plB w).nonunits) := by
    intro big L hB j w i i' hi hi' x x'
    rw [_root_.GlobalTheory.T.locations_distinguished_by_generics_alt D cf jE A M C tp.tup big L hB j w i i' hi hi' x x']
    constructor
    · intro h v k
      by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
      · rw [_root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi x hg, _root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi' x' hg]; exact h v k hg
      · rw [_root_.GlobalTheory.PtExt.sys_eq_zero_of_not_gen_at hB hi x hg, _root_.GlobalTheory.PtExt.sys_eq_zero_of_not_gen_at hB hi' x' hg, sub_zero]; exact zero_mem _
    · intro h v k hg
      rw [← _root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi x hg, ← _root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi' x' hg]; exact h v k
  have h1 := (L₁.X.nd.j_range i₁).1
  have h2 := (L₁.X.nd.j_range i₁).2
  have hi₁ : i₁ ∈ L₁.X.nd.locs (L₁.X.nd.j i₁) (L₁.X.nd.w i₁) := (L₁.X.nd.locs_mem _ _ i₁).2 ⟨rfl, rfl⟩
  have htw : D.what₂.muAt (L₁.X.nd.w i₁) ≠ D.what₂.mu0 := L₁.X.nd.w_tw i₁
  obtain ⟨x₁⟩ := L₁.X.nd.neX i₁
  obtain ⟨i₀, hi₀, y₀, hy₀⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (_root_.GlobalTheory.PtExt.sys_mem_eig_set_of_built hB₁ h1 h2 hi₁ x₁)
  have fwd : ∀ x : L₁.X.nd.X i₁, ∃ y : L₀.X.nd.X i₀, sys L₀ i₀ y = sys L₁ i₁ x := by
    intro x
    obtain ⟨i', hi', y', hy'⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (_root_.GlobalTheory.PtExt.sys_mem_eig_set_of_built hB₁ h1 h2 hi₁ x)
    have hc : i' = i₀ := by
      rw [cong big₀ L₀ hB₀ _ _ i' i₀ hi' hi₀ y' y₀, hy', hy₀]
      exact (cong big₁ L₁ hB₁ _ _ i₁ i₁ hi₁ hi₁ x x₁).1 rfl
    subst hc
    exact ⟨y', hy'⟩
  choose f hf using fwd
  have finj : Function.Injective f := fun x x' h => sys_inj L₁ i₁ (by rw [← hf x, ← hf x', h])
  have fsurj : Function.Surjective f := by
    intro y
    obtain ⟨i', hi', x', hx'⟩ := onto big₁ L₁ hB₁ _ _ h1 h2 htw _ (_root_.GlobalTheory.PtExt.sys_mem_eig_set_of_built hB₀ h1 h2 hi₀ y)
    have hc : i' = i₁ := by
      rw [cong big₁ L₁ hB₁ _ _ i' i₁ hi' hi₁ x' x₁, hx', ← hy₀]
      exact (cong big₀ L₀ hB₀ _ _ i₀ i₀ hi₀ hi₀ y y₀).1 rfl
    subst hc
    exact ⟨x', sys_inj L₀ i₀ (by rw [hf x', hx'])⟩
  have hw₀ : L₀.X.nd.w i₀ = L₁.X.nd.w i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).2
  have hj₀ : L₀.X.nd.j i₀ = L₁.X.nd.j i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).1
  refine ⟨i₀, hw₀, hj₀, Equiv.ofBijective f ⟨finj, fsurj⟩, fun v k x hv k1 k2 => ?_⟩
  have hg := (_root_.GlobalTheory.PtExt.splitOut_iff_genAt_alt hB₁ hi₁ v k).1 ⟨hv, k1, k2⟩
  have e := congrFun (congrFun (hf x) v) k
  rw [_root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB₀ hi₀ _ hg] at e
  exact (_root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB₁ hi₁ x hg).symm.trans e.symm
end GlobalTheory.PtExt
end
end
end

