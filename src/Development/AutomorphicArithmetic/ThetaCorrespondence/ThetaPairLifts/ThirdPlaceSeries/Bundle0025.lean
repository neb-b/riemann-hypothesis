module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigAtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PtLocalPin

theorem eig_at_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i)
    (w : PlE D.host) (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hcw : IsConjPl D.host w s.w)
    (hu : IsUnif D.host.E s.v ϖ) :
    ∃ c : ℕ → ℂ, X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (D.naut.locV i Q w) ((1 - (D.R.nV : ℝ)) / 2)) ∧
      ∀ k, 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i Q,
        NG.tN (P.M.loc i).J s ϖ k ((P.M.loc i).real y) = c k • (P.M.loc i).real y := by
  classical
  have HT := P.H.hecke
  have hsB : s.v ∉ badPl D i := GlobalTheory.HeckeScalarAll.not_bad HT i hw s hcw
  have hex : ∀ k, ∃ c : ℂ, ∀ f ∈ P.H.av.S i Q,
      (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) →
      NG.tN (Umax D.host.E D.R.nV) s ϖ k f = c • f := fun k =>
    _root_.GlobalTheory.HeckeScalarSph.tN_scalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s ϖ k hu
  choose c hc using hex
  have hfT : ∀ y, (P.M.loc i).real y ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    intro y
    rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
  have hfI : ∀ y ∈ D.naut.typeV i Q, (P.M.loc i).real y ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    intro y hy
    rw [P.H.av.typeV] at hy; exact hy
  have hfix : ∀ y, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      NG.rt D.host.E D.R.nV κ ((P.M.loc i).real y) = (P.M.loc i).real y := by
    intro y κ hκ ht
    have ht' : TrivOutside (badPl D i)ᶜ κ :=
      GlobalTheory.HeckeScalarAll.trivOutside_mono (Set.singleton_subset_iff.2 hsB) ht
    obtain ⟨h1, h2⟩ := HT.J_hyp i κ ht'
    have hJ : κ ∈ (P.M.loc i).J := h1.2 hκ
    have e := (hfT y).2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨y0, hy0, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
    have hf0 : (P.M.loc i).real y0 ≠ 0 := fun h =>
      hy00 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))
    obtain ⟨g, hg, hg0, hgfix⟩ := exists_fixed_of_isoTyp (P.H.av.irr i Q) s.v _ (hfI y0 hy0) hf0 (hfix y0)
    have hpol := P.H.au.locPol (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) s w ϖ hcw hu
      (Umax D.host.E D.R.nV) (fun κ _ => Iff.rfl) g hg hg0 hgfix c (fun k _ _ => hc k g hg hgfix)
    rw [hpol, D.nbc.embAV_loc, P.H.emb]
  · intro k _ _ y hy
    have hfinU := _root_.GlobalTheory.TSetFin.finite_image_tSet D.host.E D.R.nV (Umax D.host.E D.R.nV) 1 ∅
      (fun κ _ => ⟨Iff.rfl, fun _ => rfl⟩) s ϖ k (by simp) hu
    have e1 : NG.tN (P.M.loc i).J s ϖ k ((P.M.loc i).real y) =
        NG.tN (Umax D.host.E D.R.nV) s ϖ k ((P.M.loc i).real y) := by
      simp only [NG.tN]
      rw [GlobalTheory.HeckeScalarAll.heckeD_eq_of_fixed (P.M.loc i).J (P.M.loc i).χ (badPl D i) (HT.J_hyp i) s hsB ϖ k _
        (hfix y)]
    rw [e1]
    exact GlobalTheory.HeckeScalarAll.tN_isoTyp (P.H.av.irr i Q) s ϖ k hfinU (c k) (hc k) _ (hfI y hy) (hfix y)
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i,
    GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  intro hL D P i
  refine _root_.GlobalTheory.PtLocalEig.main D P.M P.H.hecke P.H.rational P.H.av P.H.cover i ?_
  intro Q w hw
  obtain ⟨s0, ϖ0, hc0, hu0⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw.1
  obtain ⟨c0, hp0, -⟩ := _root_.GlobalTheory.PtLocalPin.eig_at_alt P i Q w hw s0 ϖ0 hc0 hu0
  have hN : normV w ≠ 0 := (lt_trans zero_lt_one (GlobalTheory.WeilDeligne.one_lt_normV w)).ne'
  refine ⟨c0, hp0.symm, fun k s ϖ hc hu h1 h2 y hy => ?_⟩
  obtain ⟨c, hp, hy'⟩ := _root_.GlobalTheory.PtLocalPin.eig_at_alt P i Q w hw s ϖ hc hu
  rw [hy' k h1 h2 y hy, coeff_eq hN (hp.trans hp0.symm) h1 h2]

end GlobalTheory.PtLocalPin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptLocal_theta_exhaustion : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  exact _root_.GlobalTheory.PtLocalPin.main_alt_alt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsCompIrrSmParam
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace GlobalTheory.TypeRec
theorem exists_comp_irrSm_param_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (I : Ident D) (rc : GlobalTheory.SerSys.Corr D) (hrc : _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc) (Rw : GlobalTheory.HeightCounting.RowSide D)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (h1 : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR) (h2 : GlobalTheory.HeightCounting.RowDepth D rep) :
    ∃ cp : GlobalTheory.GoodTypes.Comp D, IsComp I rep cp ∧
      ∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v) := by
  obtain ⟨cp, hc⟩ := exists_isComp_of_rowDepth I rep h2
  refine ⟨cp, hc, fun σ k v => ⟨?_, _root_.GlobalTheory.TypeRec.Model.locR_eq_rc_of_isRc_and_true_reading hrc hc h1 σ k v⟩⟩
  obtain ⟨s, hs, τ, -, e⟩ := hc σ k v
  rw [e]
  exact Model.irrSm_pull I k v τ
end GlobalTheory.TypeRec
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsMuCStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_crystalline_weights_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ μ : D.naut.CG 1, D.naut.csd μ ∧ ∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j := by
  first | exact @_root_.GlobalTheory.MuCLoc.exists_muC_alt | exact _root_.GlobalTheory.MuCLoc.exists_muC_alt | (intros; apply _root_.GlobalTheory.MuCLoc.exists_muC_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsResidueFieldMapStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_determinant_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ κ : IsLocalRing.ResidueField (X.nd.O i) →+* Formalism.CyclotomicNorms.Fbar (X.nd.l i), ∀ y : X.nd.O i, ∃ h : (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) y ∈ A.pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) = κ (IsLocalRing.residue (X.nd.O i) y) := by
  first | exact @_root_.GlobalTheory.ResidueLocPlace.exists_residueField_map_alt | exact _root_.GlobalTheory.ResidueLocPlace.exists_residueField_map_alt | (intros; apply _root_.GlobalTheory.ResidueLocPlace.exists_residueField_map_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtRing
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.CoefDuty.ExtRing
end GlobalTheory.CoefDuty.ExtRing
end
open GlobalTheory.CoefDuty.ExtRing in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.CoefDuty.ExtRing.ext_ring_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ) (L₀ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → ∃ big₁ : D.what₂.places.Pl → Finset ℂ, ∀ L₁ : LocAll (lay0 D), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → ∃ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) ∧ ∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z' := by
  classical
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big₀ L₀ hB₀
  obtain ⟨Sp₀, ⟨Au₀⟩, -⟩ := hB₀
  have hg := fun i => exists_gens (Sp₀.iq i) (Sp₀.iq_alg i)
  let gens : ∀ i : L₀.X.nd.Loc, Finset (Qbar (L₀.X.nd.l i)) := fun i => Classical.choose (hg i)
  have hgens : ∀ i x, Sp₀.iq i x ∈ Submodule.span ℚ_[L₀.X.nd.l i] (gens i : Set (Qbar (L₀.X.nd.l i))) :=
    fun i => Classical.choose_spec (hg i)
  let big₁ : D.what₂.places.Pl → Finset ℂ := fun w => (Finset.Icc 1 D.R.m).biUnion fun j =>
    (L₀.X.nd.locs j w).biUnion fun i => (gens i).image fun y => qCast (L₀.X.nd.w_l i) (A.pl.ι (L₀.X.nd.w i)) y
  have hbig : ∀ i y, y ∈ gens i → qCast (L₀.X.nd.w_l i) (A.pl.ι (L₀.X.nd.w i)) y ∈ big₁ (L₀.X.nd.w i) := by
    intro i y hy
    refine Finset.mem_biUnion.2 ⟨L₀.X.nd.j i, Finset.mem_Icc.2 (L₀.X.nd.j_range i), ?_⟩
    exact Finset.mem_biUnion.2 ⟨i, (L₀.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩, Finset.mem_image_of_mem _ hy⟩
  refine ⟨big₁, fun L₁ hB₁ i₀ i₁ hw => ?_⟩
  obtain ⟨Sp₁, ⟨Au₁⟩, -⟩ := hB₁
  change L₀.X.nd.w i₀ = L₁.X.nd.w i₁ at hw
  have hl : L₀.X.nd.l i₀ = L₁.X.nd.l i₁ := by
    exact (L₀.X.nd.w_l i₀).symm.trans ((congrArg _ hw).trans (L₁.X.nd.w_l i₁))
  haveI := L₀.X.nd.lPrime i₀
  haveI := L₁.X.nd.lPrime i₁
  have key : ∀ w (_ : L₀.X.nd.w i₀ = w) (h₁ : D.what₂.places.resChar w = L₁.X.nd.l i₁),
      qCast h₁ (A.pl.ι w) = qCast hl (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) := by
    intro w hw' h₁
    subst hw'
    exact qCast_trans _ _ _ _
  obtain ⟨φ, h1, h2⟩ := exists_ringHom (O₀ := L₀.X.nd.O i₀) (O₁ := L₁.X.nd.O i₁)
    (cr₀ := L₀.X.nd.instO i₀) (dm₀ := L₀.X.nd.domO i₀) (dv₀ := L₀.X.nd.dvrO i₀) (al₀ := L₀.X.nd.algO i₀) (fi₀ := L₀.X.nd.finO i₀)
    (cr₁ := L₁.X.nd.instO i₁) (dm₁ := L₁.X.nd.domO i₁) (dv₁ := L₁.X.nd.dvrO i₁) (al₁ := L₁.X.nd.algO i₁) (fi₁ := L₁.X.nd.finO i₁) hl (Sp₀.iq i₀) (Sp₀.iq_alg i₀) (Sp₁.iq i₁) (Sp₁.iq_alg i₁)
    (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) (qCast (L₁.X.nd.w_l i₁) (A.pl.ι (L₁.X.nd.w i₁)))
    (key _ hw _) _ (hgens i₀) (fun y hy => Sp₁.iq_big i₁ _ (hw ▸ hbig i₀ y hy))
  refine ⟨φ, fun z => ?_, h2⟩
  have e₀ := fun x => (congrArg (fun g : Qbar (L₀.X.nd.l i₀) ≃+* ℂ => g (L₀.Y.naut.iotaQ i₀ x)) (Au₀.iotaQC i₀)).trans
    (congrArg (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) (DFunLike.congr_fun (Au₀.iotaQ i₀) x))
  have e₁ := fun x => (congrArg (fun g : Qbar (L₁.X.nd.l i₁) ≃+* ℂ => g (L₁.Y.naut.iotaQ i₁ x)) (Au₁.iotaQC i₁)).trans
    (congrArg (qCast (L₁.X.nd.w_l i₁) (A.pl.ι (L₁.X.nd.w i₁))) (DFunLike.congr_fun (Au₁.iotaQ i₁) x))
  exact (e₁ _).trans ((h1 z).trans (e₀ _).symm)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisFamilyIrreducible
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_irreducible_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), IsSplitPl D.host w → w ∉ X.nd.Q i → (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) → D.naut.unr (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) := by
  first | exact @_root_.GlobalTheory.AutUnr.locV_unr_m_alt | exact _root_.GlobalTheory.AutUnr.locV_unr_m_alt | (intros; apply _root_.GlobalTheory.AutUnr.locV_unr_m_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisTwist
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwistGal
theorem galois_twist_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w)) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w)) ∧ (∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c))) := by
  intro hB hL D P i a ρ χ hρ hχ
  have htc : Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) :=
    GlobalTheory.TwistGal.cont_twGL ρ χ hρ hχ
  have hdR : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) {b : ℕ} (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))),
      Continuous (fun g => ((r g : GL (Fin b) (Qbar (D.nd.l i))) : Matrix (Fin b) (Fin b) (Qbar (D.nd.l i)))) →
      (D.naut.IsdRW i r w ↔ GlobalTheory.Pst.IsdRAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
    intro w hw b r hr
    rw [(P.wdOf i b r w).2.2.2.1]
    exact GlobalTheory.T.deRham_galoisSide_iff_deRham_at_localEmbedding D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) w hw (D.nd.O i) (D.nbr i w hw) (D.nbr_ind i w hw) b r hr
  have p1 : ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w) := by
    intro w hw h
    rw [hdR w hw χ hχ] at h
    rw [hdR w hw _ htc, hdR w hw ρ hρ]
    rw [GlobalTheory.Pst.resDec, GlobalTheory.TwistGal.comp_twGL]
    exact _root_.GlobalTheory.TwistBridgeDR.isdRAt_twist_iff (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ D.host.E D.nd.Om _ (D.nd.O i) (D.nbr i w hw) a (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w) (GlobalTheory.Pst.resDec D.nd.plOm.1 χ w) (hρ.comp continuous_subtype_val) (hχ.comp continuous_subtype_val) h
  have p3 : ∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c) := by
    intro τ c h hc
    have w0 : HeightOneSpectrum (𝓞 D.host.E) := PI.CompDegEF.plOf τ
    rw [(P.wdOf i 1 χ w0).2.2.2.2 τ] at hc
    rw [(P.wdOf i a _ w0).2.2.2.2 τ, (P.wdOf i a ρ w0).2.2.2.2 τ]
    refine _root_.GlobalTheory.TwistJumpsW.jumpsW_twist D P.T P.wd i (D.naut.iotaQC i) a ρ χ hρ hχ τ c (fun w hw => ?_) hc
    obtain ⟨h1, h2⟩ := h w hw
    exact ⟨(P.wdOf i a ρ w).2.2.2.1.1 h1, (P.wdOf i 1 χ w).2.2.2.1.1 h2⟩
  have pst : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) {b : ℕ} (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))),
      Continuous (fun g => ((r g : GL (Fin b) (Qbar (D.nd.l i))) : Matrix (Fin b) (Fin b) (Qbar (D.nd.l i)))) →
      D.naut.IsdRW i r w → ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
      (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw →
      GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w) := by
    intro w hw b r hr hd O _ _ _ Bw hj
    exact hB.isPstAt (D.locT (D.nd.l i)) Bw _ (hr.comp continuous_subtype_val)
      ((GlobalTheory.T.deRham_galoisSide_iff_deRham_at_localEmbedding D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) w hw O Bw hj b r hr).1 ((P.wdOf i b r w).2.2.2.1.1 hd))
  have p2 : ∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w) := by
    intro w h1 h2
    rw [(P.wdOf i a _ w).1, (P.wdOf i a ρ w).1, (P.wdOf i 1 χ w).1]
    have hd : D.naut.lpDim (P.wd.wdOf (D.nd.l i) (D.naut.iotaQC i) χ w) = 1 := P.wd.wdOf_dim _ _ χ w
    apply (P.T.e w).injective
    rw [P.T.char w _ _ hd]
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · have d1 : D.naut.IsdRW i ρ w := h1.resolve_left (not_not.2 hw)
      have d2 : D.naut.IsdRW i χ w := h2.resolve_left (not_not.2 hw)
      have d3 := (p1 w hw d2).2 d1
      obtain ⟨L1, B1, j1, e1⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w hw
      obtain ⟨L2, B2, j2, e2⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) ρ w hw
      obtain ⟨L3, B3, j3, e3⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) χ w hw
      rw [e1, e2, e3]
      have T0 : Nonempty (LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i))) := ⟨D.locT (D.nd.l i)⟩
      have hN := D.nbr_ind i w hw
      rw [GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
          _ (D.nd.O i) B1 (D.nbr i w hw) j1 hN a _ (htc.comp continuous_subtype_val)
          (pst w hw _ htc d3 _ B1 j1) (pst w hw _ htc d3 _ (D.nbr i w hw) hN),
        GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
          _ (D.nd.O i) B2 (D.nbr i w hw) j2 hN a _ (hρ.comp continuous_subtype_val)
          (pst w hw _ hρ d1 _ B2 j2) (pst w hw _ hρ d1 _ (D.nbr i w hw) hN),
        GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
          _ (D.nd.O i) B3 (D.nbr i w hw) j3 hN 1 _ (hχ.comp continuous_subtype_val)
          (pst w hw _ hχ d2 _ B3 j3) (pst w hw _ hχ d2 _ (D.nbr i w hw) hN)]
      have q3 := pst w hw _ htc d3 _ (D.nbr i w hw) hN
      rw [GlobalTheory.Pst.resDec, GlobalTheory.TwistGal.comp_twGL] at q3 ⊢
      exact GlobalTheory.T.fontaineParameter_twist_potentiallySemistable (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
        (D.nd.O i) (D.nbr i w hw) hN a _ _ (hρ.comp continuous_subtype_val) (hχ.comp continuous_subtype_val)
        (pst w hw _ hρ d1 _ (D.nbr i w hw) hN) (pst w hw _ hχ d2 _ (D.nbr i w hw) hN) q3
    · rw [P.wd.away _ _ _ w hw, P.wd.away _ _ _ w hw, P.wd.away _ _ _ w hw]
      exact GlobalTheory.T.weilDeligneParamOfLadicRep_twist_det_awayFrom_l D.host.E D.nd.Om _ w (D.nd.plOm.2 w) (D.nd.l i) hw (D.naut.iotaQC i) a ρ χ hρ hχ
  exact ⟨p1, p2, p3⟩
end GlobalTheory.TwistGal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodPartLeISupEigenStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_in_isotypic_sup_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          V0T D T S In.rho In.chi In.θ i j b ⊓
            ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i),
              Module.End.eigenspace (hkT D T S In i j b k P)
                (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.goodPart_le_iSup_eigen_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.goodPart_le_iSup_eigen_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.goodPart_le_iSup_eigen_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeStdTwCover
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.NPin
theorem heckeStdTw_cover_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), HeckeStdTw P.H.cover.B :=
  fun _ D P =>
    Formalism.L2.heckeStd_of_plain P.H.cover GlobalTheory.HeckeStdFacts.heckeStdPlain P.H.hecke (GlobalTheory.SplitConjPlace.splitEx_all D)
      (Formalism.L2.genOutBad_of P.H.cover)
end GlobalTheory.NPin
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkStabAllStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hkStab_of_subset_of_star_closed : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → HkStab D T S In := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.hkStab_of_ringSpec_of_subset | exact _root_.GlobalTheory.HeightCounting.FormsStep.hkStab_of_ringSpec_of_subset | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.hkStab_of_ringSpec_of_subset <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisMore
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.MuTameQS
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu ∧ ((∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu) := by
  intro hL D P S hS i w hw hSQ
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hc := hS.mu i w hw j hjj
  have hc' : IsComp (P.tp.tup (D.nd.mu i) j) w ((P.tp.tup (D.nd.mu i) j).loc w) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ w, fun _ => rfl⟩
  have hmu : (S i w hw).mu = (P.tp.tup (D.nd.mu i) j).loc w := GlobalTheory.HeckeComp.eq_of_isComp hc' hc
  rw [hmu]
  refine ⟨isTame_loc (tameAt_mul ((P.cf.isMu0 j).tame w) (P.tp.xi_tame _ w)), fun hg => ?_⟩
  refine not_isUnram_loc fun hU => ?_
  have hm0 : (P.cf.mu0 j).UnrAt w := (P.cf.isMu0 j).unr w fun k hk => hg k hk
  have hX : (P.tp.xi (D.nd.mu i)).UnrAt w := unrAt_of_mul_left hm0 hU
  rw [D.nd.mu_w i, P.tp.xi_tw, CharFrame.delAt, D.nd.w_l i] at hX
  have hpsi := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i, ← P.Q_eq i] at hpsi
  have hnl : w ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i w hSQ
  rcases hSQ with hwS | hwQ
  ·
    have hwQ : w ∉ D.nd.Q i := Finset.disjoint_left.1 (D.nd.SQ_disj i) hwS
    have hp : (P.tp.psi (D.nd.w i)).UnrAt w := (hpsi.ram w).2 hwQ
    have hd := (D.nd.S_def i w).1 hwS
    rcases hd.1 with h0 | h1 | hq
    · exact hg 0 h0
    · exact hg 1 h1
    · split_ifs at hX hq with hl
      · have hdu := unrAt_of_mul_left hp ((mul_comm _ _ : P.cf.del' * _ = _) ▸ hX)
        have := (P.cf.isDel'.ine w hq 1).1 fun x hx => by rw [pow_one]; exact hdu x hx
        norm_num at this
      · have hdu := unrAt_of_mul_left hp ((mul_comm _ _ : P.cf.del * _ = _) ▸ hX)
        have := (P.cf.isDel.ine w hq 1).1 fun x hx => by rw [pow_one]; exact hdu x hx
        norm_num at this
  ·
    have hwS : w ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hwQ
    have hd : (CharFrame.delAt P.cf (D.nd.l i)).UnrAt w := by
      unfold CharFrame.delAt
      split_ifs with hl
      · refine P.cf.isDel'.unr w fun ho => hwS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr ?_), hnl⟩)
        rw [if_pos hl]; exact ho
      · refine P.cf.isDel.unr w fun ho => hwS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr ?_), hnl⟩)
        rw [if_neg hl]; exact ho
    have hX' : (CharFrame.delAt P.cf (D.nd.l i) * P.tp.psi (D.nd.w i)).UnrAt w := by
      unfold CharFrame.delAt; exact hX
    exact (hpsi.ram w).1 (unrAt_of_mul_left hd hX') hwQ
end GlobalTheory.MuTameQS
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisTer
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PartOrthPin
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i)) → GlobalTheory.ThetaExh.PartOrth D.nd i := by
  intro hL D P i ⟨X⟩ σ σ' hne
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  have hni : ¬ (P.rep σ).Iso (P.rep σ') := fun h => hne (P.rep_inj σ σ' h)
  rw [X.φ_inner]
  exact GlobalTheory.IsotOrth.isotIn_orthogonal D D.R.r X.A X.ρ X.C X.B X.lin X.herm X.pos X.stab X.inv X.adm
    (P.rep σ) (P.rep σ') hni _ ((X.isot σ u).1 hu) _ ((X.isot σ' v).1 hv)
end GlobalTheory.PartOrthPin
end
end

