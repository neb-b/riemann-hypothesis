module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTiedRowLoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0026
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BuiltFiniteAndMemStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_unitary_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd →
    ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L →
    ∀ (i : L.X.nd.Loc) (x : L.X.nd.X i),
      (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))).Finite ∧
      ptSys (withLoc L) i x ∈ EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) := by
  first | exact @_root_.GlobalTheory.EigPlace.built_finite_and_mem_alt | exact _root_.GlobalTheory.EigPlace.built_finite_and_mem_alt | (intros; apply _root_.GlobalTheory.EigPlace.built_finite_and_mem_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiEqOfExtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_character_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) → (∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') → ∀ c, 1 ≤ c → c ≤ D.R.t → ∀ σ : GE L₁.lay.fixZ.nd, ((L₁.lay.fixZ.nd.chi i₁ c σ : (L₁.lay.fixZ.nd.O i₁)ˣ) : L₁.lay.fixZ.nd.O i₁) = φ ((L₀.lay.fixZ.nd.chi i₀ c σ : (L₀.lay.fixZ.nd.O i₀)ˣ) : L₀.lay.fixZ.nd.O i₀) := by
  first | exact @_root_.GlobalTheory.ChiExtend.chi_eq_of_ext_alt | exact _root_.GlobalTheory.ChiExtend.chi_eq_of_ext_alt | (intros; apply _root_.GlobalTheory.ChiExtend.chi_eq_of_ext_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMuUnrFrob
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.AutPart.chiMu_unr_frob_alt : ∀ (hArt : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (hψ : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (μ : D.naut.CG 1), D.naut.csd μ → (∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j) → ∀ w, SplitOut X.nd i w → D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) ∧ ∀ (B : ValuationSubring X.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om), IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ → D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)) = {(qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i)))} := by
  intro hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i μ _hcsd hμ w hw
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = X.nd.j i :=
    ⟨⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩, by have := X.nd.j_range i; simp; omega⟩
  have e : (A.chr.e1 (D.naut.tw μ D.naut.etaTinv)).1 = tp.tup (X.nd.mu i) j * cf.eta⁻¹ := by
    rw [A.chr.tw, hμ j hj, A.chr.etaTinv]
  have hU : (A.chr.e1 (D.naut.tw μ D.naut.etaTinv)).1.UnrAt w := by
    rw [e]; exact _root_.GlobalTheory.T.galois_family_conductor_bound_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i j hj w hw
  have hu : D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) := (A.chr.unr_iff _ w).2 hU
  refine ⟨hu, fun B σ hB hσ => ?_⟩
  rw [D.naut.frobEig_tw _ _ hu, A.chr.frob _ w hU, e, Multiset.map_singleton, Multiset.singleton_inj]
  exact (_root_.GlobalTheory.T.galois_family_places_over_real_alt hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i j hj (_root_.GlobalTheory.T.galois_family_residual_image_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i j hj) w hw B σ hB hσ).symm
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiOneTameGenStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_rational_character_data_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb → ∀ (i : X.nd.Loc) k v, X.nd.l i ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))) := by
  first | exact @_root_.GlobalTheory.ChiTame.chi_one_tameGen_alt | exact _root_.GlobalTheory.ChiTame.chi_one_tameGen_alt | (intros; apply _root_.GlobalTheory.ChiTame.chi_one_tameGen_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ContainsWithLocStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contains_after_localization_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → ∀ i : L.X.nd.Loc, Contains (withLoc L).nd (withLoc L).naut i ↑(big (L.X.nd.w i)) ∧ Contains L.lay.fixZ.nd L.lay.fixZ.naut i ↑(big (L.X.nd.w i)) ∧ (Live (withLoc L).nd i ↔ Live L.lay.fixZ.nd i) ∧ (ZDecomp (withLoc L).nd i ↔ ZDecomp L.lay.fixZ.nd i) ∧ (∀ S, Chosen (withLoc L).nd (withLoc L).naut i S ↔ Chosen L.lay.fixZ.nd L.lay.fixZ.naut i S) ∧ ((∃ r, GoodR (withLoc L).nd i r) ↔ ∃ r, GoodR L.lay.fixZ.nd i r) ∧ ((∃ r ρ, GoodR (withLoc L).nd i r ∧ TakenWild (withLoc L).nd i r ρ) ↔ ∃ r ρ, GoodR L.lay.fixZ.nd i r ∧ TakenWild L.lay.fixZ.nd i r ρ) := by
  first | exact @_root_.GlobalTheory.CoefDuty.MemberO.member_duties_alt | exact _root_.GlobalTheory.CoefDuty.MemberO.member_duties_alt | (intros; apply _root_.GlobalTheory.CoefDuty.MemberO.member_duties_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOLawsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_conjunction_mono_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (P₁ P₂ : D7 → Prop), (_root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₂ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup fun D' => P₁ D' ∧ P₂ D') ∧ ((∀ D', P₁ D' → P₂ D') → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₂) ∧ (_root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L ∧ P₁ (withLoc L)) ∧ ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big' L → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L := by
  first | exact @_root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt | exact _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt | (intros; apply _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsCompIrrSmParamStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comp_irrSm_locR_eq_rc : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → ∃ cp : GlobalTheory.GoodTypes.Comp D, IsComp I rep cp ∧ ∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v) := by
  first | exact @_root_.GlobalTheory.TypeRec.exists_comp_irrSm_param_alt | exact _root_.GlobalTheory.TypeRec.exists_comp_irrSm_param_alt | (intros; apply _root_.GlobalTheory.TypeRec.exists_comp_irrSm_param_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtRingStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_level_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ) (L₀ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → ∃ big₁ : D.what₂.places.Pl → Finset ℂ, ∀ L₁ : LocAll (lay0 D), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → ∃ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) ∧ ∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z' := by
  first | exact @_root_.GlobalTheory.CoefDuty.ExtRing.ext_ring_alt | exact _root_.GlobalTheory.CoefDuty.ExtRing.ext_ring_alt | (intros; apply _root_.GlobalTheory.CoefDuty.ExtRing.ext_ring_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalTiedWithLoc
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.FitGal
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem galTied_withLoc_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.HeightCounting.LpCmpAlt hL → ∀ (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (fr : OmFrame b.D), fr.jE = b.jE → (PhtOn b.A.wd fr fun _ _ _ _ => True) → (∀ x : b.D.LL0, star (x : b.D.what₂.LL) ∈ b.D.LL0) → (∀ j g, ∃ z : ℤ, eExp b.D j g = z) → (∀ v, v ∈ placesOver b.D.host.E b.D.host.pde ∨ v ∈ placesOver b.D.host.E b.D.host.pde' → IsSplitPl b.D.host v) → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ g : _root_.Formalism.L2.NGalTiedAlt (withLoc b.L), g.fr.jE = b.jE ∧ g.mt = mtL b.L b.M ∧ g.tup = b.tp.tup ∧ Nonempty (NormalizedDataCompatibility (withLoc b.L)) ∧ Nonempty (NormalizedLocalCompatibility (withLoc b.L) (mtL b.L b.M)) ∧ ∀ F : RowFrame (withLoc b.L), F.rep = b.rep → _root_.Formalism.L2.RowLocTiedAlt (withLoc b.L) g.lp F := by
  intro hL hLp D' b fr hfr hpht hstar hexp hsplit hcheb
  obtain ⟨Hk, hHk⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch
    b.mt hstar hexp hsplit hcheb b.big b.L b.Sp b.Au
  let lp : LPTiedPlaceholder (withLoc b.L) := ⟨⟩
  let fr' : OmFrame (withLoc b.L) := { fr with }
  have au : _root_.Formalism.L2.AUTiedAlt (withLoc b.L) lp (mtL b.L b.M) Hk.av :=
    { Hk.au with
      emb := Hk.emb }
  let g : _root_.Formalism.L2.NGalTiedAlt (withLoc b.L) :=
    { fr := fr', lp := lp, mt := mtL b.L b.M, hecke := Hk.hecke, av := Hk.av, au := au
      rational := Hk.rational, tup := b.tp.tup, level := Hk.level }
  refine ⟨g, hfr, rfl, rfl, ⟨Hk.data⟩, ⟨Hk.cover⟩, ?_⟩
  intro F hF
  refine ⟨fun i σ v w hov Dv hα => ?_⟩
  · rw [hF] at hα ⊢
    obtain ⟨α, hS, he⟩ := b.row.2 σ v w hov Dv hα
    refine ⟨α, hS, ?_⟩
    show b.L.Y.satW i σ w = _
    rw [b.Au.satW i σ w]
    exact he
end GlobalTheory.FitGal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisTwistStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_weight_twist_character_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w)) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w)) ∧ (∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c))) := by
  first | exact @_root_.GlobalTheory.TwistGal.galois_twist_alt | exact _root_.GlobalTheory.TwistGal.galois_twist_alt | (intros; apply _root_.GlobalTheory.TwistGal.galois_twist_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckePolMapEqFrobPol
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.AutPart
theorem heckePol_map_eq_frobPol_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → ∀ P x, ptV P = some x → ∀ w, SplitOut X.nd i w → (heckePol X.nd i x w).map (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) = ((D.naut.frobEig (D.naut.lpTw (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) ((1 - (D.R.nV : ℝ)) / 2))).map fun α => Polynomial.X - Polynomial.C α).prod := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop ptV hpt P x hx w hw
  obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw.1
  have heig := (hpt P x).1 hx
  have hlev := _root_.GlobalTheory.T.mem_j_iff_umax_and_chi_eq_one_of_split_out D cf jE A M C tp hMI big X T Sp i w s hw hc
  have hne' : Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P) ⊓ Formalism.L2.NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne P)
    rw [Submodule.ne_bot_iff]
    refine ⟨(mlX M X i).real y, ⟨hy, ?_⟩, fun h0 => hy0 ((mlX M X i).real_inj (h0.trans (map_zero _).symm))⟩
    rw [← (mlX M X i).real_range]; exact LinearMap.mem_range_self _ _
  obtain ⟨f, ⟨hfF, hfT⟩, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (_root_.GlobalTheory.MoveTyped.typed_of_isoTyp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ (F P) (irr P).1 hne')
  have hfR : f ∈ LinearMap.range (mlX M X i).real := by rw [(mlX M X i).real_range]; exact hfT
  obtain ⟨y, rfl⟩ := hfR
  have hyV : y ∈ (Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real := by
    show (mlX M X i).real y ∈ Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P)
    exact (le_sSup (show F P ∈ {S' | Formalism.L2.NG.IsIrrRep (mlX M X i).wt.ρ S' ∧ Formalism.L2.NG.IsoRep (F P) S'} from
      ⟨irr P, LinearEquiv.refl ℂ _, fun h f f' e => e⟩)) hfF
  have hsph : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      Formalism.L2.NG.rt D.host.E D.R.nV κ ((mlX M X i).real y) = (mlX M X i).real y := by
    intro κ hκ ht
    have hJ : κ ∈ (mlX M X i).J := ((hlev κ ht).1).2 hκ
    have := hfT.2 ⟨κ, hJ⟩
    rw [this, (hlev κ ht).2 hJ]; simp
  have hpol := A.au.locPol (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
    { (mlX M X i).wt with S := F P, irrS := irr P } s w ϖ hc hu (mlX M X i).J (fun κ ht => (hlev κ ht).1)
    ((mlX M X i).real y) hfF hf0 hsph
    (fun k => (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x))
    (fun k hk1 hk2 => heig w k s ϖ hw hc hu hk1 hk2 y hyV)
  refine Eq.trans ?_ hpol
  set_option synthInstance.maxHeartbeats 100000 in
    simp [heckePol, Polynomial.map_sum]
end GlobalTheory.AutPart
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeStdTwCoverStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStdTw_cover' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), HeckeStdTw P.H.cover.B := by
  first | exact @_root_.GlobalTheory.NPin.heckeStdTw_cover_alt | exact _root_.GlobalTheory.NPin.heckeStdTw_cover_alt | (intros; apply _root_.GlobalTheory.NPin.heckeStdTw_cover_alt <;> assumption)
end
end

