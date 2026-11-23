module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0007
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeStdStatement
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0002
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0003
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0005
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.LocalToGlobal.GaloisLevelStructure.NGalTied
public import Formalism.LocalToGlobal.LocalInduction.BridgeInd
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdL
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.BasicNotions

namespace Formalism.L2

section Rfl

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

end Rfl

theorem heckeStdPlain_of_statement (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement) : HeckeStdPlain := by
  intro L _ _ _ n a J χ B hJo hB s ϖ k hs hu hk1 hk2
  exact h L n a.W a.ρ a.alg J χ B hJo hB s ϖ k hs hu hk1 hk2

theorem linkEtaTw_of_statement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    LocsCoverTwF Fm :=
  linkEtaTw_of_plain Fm (heckeStdPlain_of_statement h) hfam

end Formalism.L2
end
end

-- bundled from Formalism.LocalToGlobal.NormalizedHeckeFactors.EMtLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain
open Formalism.L2.NT

namespace Formalism.L2


set_option synthInstance.maxHeartbeats 400000 in
structure NormalizedTwistCompatibility (D : D7) (C : NChoice D) (I : TwIn D) where

  gal : NGalTied D

  n : NormalizedHeckeDataPlaceholder D

  loc : LocTied D

  data : NormalizedDataCompatibility D

  cover : NormalizedLocalCompatibility D gal.mt

  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD

  rho : NR.NRhoTied D

  types : NormalizedTypesCompatibility D gal.fr.jE

  twF : TwFrame D
  tw : NTwTied D twF

  nct : NChTie D C

  exp : NExpTied D

  choice : NChoiceTied D C I (avDesign D)

  eMt_level : ∀ (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : TwistedAt D w) (hA : NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))),
    ∃ ι : FractionRing (C.Oe w) →+* ℂ, (∀ x : D.what₂.LL, ι (C.embW w x) = D.what₂.embLL x) ∧
      (gal.mt (D.what₂.muTw w) j h1 h2).J =
        (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J ∧
      ∀ (κ : Formalism.AUTREP.GAf D.host.E D.R.nV) (h : κ ∈ (gal.mt (D.what₂.muTw w) j h1 h2).J)
        (h' : κ ∈ (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
          ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J),
        (((gal.mt (D.what₂.muTw w) j h1 h2).χ ⟨κ, h⟩ : ℂˣ) : ℂ) =
          ι (C.kMapE w (((exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
            ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).χ ⟨κ, h'⟩ : (NX.Kk D (C.twI w) (C.k' w))ˣ) :
              NX.Kk D (C.twI w) (C.k' w)))

  cf : Host.CharFrame D
  tp : Host.TupTied D cf C

  tupLink : gal.TupLink tp

  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  psi_eq : ∀ a x, (chiD.psi a).χ x = (tp.psi (D.nd.w a)).1 x

  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plκ : ∀ w, haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IsLocalRing.ResidueField (plB w) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w)

  plB_loc : ∀ (i : D.nd.Loc) (y : D.nd.O i),
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ h : iotaOC D i y ∈ plB (D.nd.w i),
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (plκ (D.nd.w i) (IsLocalRing.residue (plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)

  plB_iota : ∀ (i : D.nd.Loc) k v x,
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    D.ntypes.iota k v (D.nd.w i) x = redThrough (plB (D.nd.w i)) (plκ (D.nd.w i)) (D.ntypes.teichC k x)

  etaT_link : ∀ (w : PlE D.host) (α : ℂ), chiD.etaT.At w α →
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹}

  muC_link : ∀ i : D.nd.Loc, ∀ᶠ w in Filter.cofinite, ∀ α : ℂ,
    (chiD.mu0 (D.nd.j i) * chiD.del (D.ntw.twOf i) * chiD.psi i).At w α →
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹}

  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)

  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y

end Formalism.L2
end
end

