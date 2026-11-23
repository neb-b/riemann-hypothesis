module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.DataForms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IndexAtLevel
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

open Formalism.BasicNotions Formalism.MainNotions

variable (D : D7) (u : D.what₂.Word)

def IsScaledU (w : D.what₂.places.Pl) (v : (D.mem u).A.vT)
    (g : (D.fm u).ramSub →ₗ[D.what₂.LL] (D.fm u).ramSub) : Prop :=
  ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (g x : LT.Vl D u 0) =
    (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) •
      LT.Uop D u 0 v ((D.fm u).emb 0 (x : LT.Vl D u 0))

end GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

section Param

variable {R : Ranks}

def run (P : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Multiset.range R.t).map fun k : ℕ => -P.e j + ((R.t : ℚ) + 1) / 2 - ((k : ℚ) + 1)

def param (P : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map P.v +
    (Finset.univ : Finset (Fin R.m)).val.map (fun i => -P.b i) + run P j

def sgnOf (ep b : Bool) : ℚ := if ep = b then 1 else -1

end Param

variable (D : D7)

def liftIdx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def embOver (ρ : D.what₂.Tau) (b : Bool) : D.host.E →+* ℂ :=
  if b then
    (D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)).comp (D.host.conj : D.host.E →+* D.host.E)
  else D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)

def PP (i : D.nd.Loc) (ρ : D.what₂.Tau) : Multiset ℚ := param (D.hc ρ) (liftIdx D i)

section Local

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Local

def chiGL (i : D.nd.Loc) (c : ℕ) : GE D.nd →* GL (Fin 1) (D.nd.O i) :=
  (Units.map (Matrix.scalar (Fin 1) : D.nd.O i →+* Matrix (Fin 1) (Fin 1) (D.nd.O i)).toMonoidHom).comp
    (D.nd.chi i c)

def WeightParam : Prop :=
  ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
    D.naut.infWt i (embOver D ρ false) = (PP D i ρ).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) ∧
    D.naut.infWt i (embOver D ρ true) = (PP D i ρ).map (fun p => ((-(p - 1 / 2) : ℚ) : ℂ))

def BlockCharParam : Prop :=
  ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
    D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ false) =
      {((-(D.hc ρ).e (liftIdx D i) - 1 / 2 : ℚ) : ℂ)} ∧
    D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ true) =
      {(((D.hc ρ).e (liftIdx D i) + 1 / 2 : ℚ) : ℂ)}

end GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

def nlen {O : Type} [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : WithTop ℚ :=
  if Module.length O M = ⊤ then ⊤ else ((lenUnit (O := O) l M : ℚ) : WithTop ℚ)

section Ext

variable {O₀ O' : Type} [CommRing O₀] [IsDomain O₀] [CommRing O'] [IsDomain O']
  (f : O₀ →+* O') (hf : Function.Injective f)

def fracMap : FractionRing O₀ →+* FractionRing O' :=
  IsFractionRing.map (A := O₀) (B := O') (K := FractionRing O₀) (L := FractionRing O') hf

theorem fracMap_alg (c : O₀) :
    fracMap f hf (algebraMap O₀ (FractionRing O₀) c) = algebraMap O' (FractionRing O') (f c) := by
  simp [fracMap, IsFractionRing.map]

def vecMap (k : ℕ) : (Fin k → FractionRing O₀) →ₛₗ[f] (Fin k → FractionRing O') where
  toFun v j := fracMap f hf (v j)
  map_add' u v := by
    funext j
    simp
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, fracMap_alg]

def pushKO (k : ℕ) : KOG O₀ k →ₛₗ[f] KOG O' k :=
  Submodule.mapQ _ _ (vecMap f hf k) (by
    rintro _ ⟨u, rfl⟩
    refine ⟨fun j => f (u j), ?_⟩
    funext j
    exact (fracMap_alg f hf (u j)).symm)

def extCond {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : ℕ}
    (ρ₀ : Representation O₀ Γ (KOG O₀ k)) (L₀ : Submodule O₀ (H1 ρ₀))
    (ρ' : Representation O' Γ (KOG O' k)) : Submodule O' (H1 ρ') :=
  ((Submodule.span O' {c : Γ → KOG O' k | ∃ c₀ : Z1 ρ₀, Submodule.Quotient.mk c₀ ∈ L₀ ∧
      c = fun g => pushKO f hf k ((c₀ : Γ → KOG O₀ k) g)}).comap (Z1 ρ').subtype).map
    (Submodule.mkQ _)

end Ext

def SameChar {O₀ O₁ O₂ Γ : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ]
    (f₁ : O₀ →+* O₁) (f₂ : O₀ →+* O₂) (ψ₁ : Γ →* O₁ˣ) (ψ₂ : Γ →* O₂ˣ) : Prop :=
  ∀ F : Γ →₀ O₀, (F.sum fun g c => f₁ c * ((ψ₁ g : O₁ˣ) : O₁)) = 0 ↔
    (F.sum fun g c => f₂ c * ((ψ₂ g : O₂ˣ) : O₂)) = 0

section Tw

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (tw : NTw R H what₂ LL0 N)

def latT (i : tw.Tw) (s : tw.Sig i) : GE N →* Matrix (Fin R.r) (Fin R.r) (tw.O0 i) :=
  twistM ((Units.coeHom _).comp (tw.rhoS i s)) (tw.chi1 i (tw.jS i s) (tw.side i s))⁻¹

def setS (i : tw.Tw) : Set (PlE H) :=
  {v | ((∃ k, v ∈ placesOver H.E (H.g k)) ∨ v ∈ tw.pD i) ∧ v ∉ placesOver H.E (tw.l i)}

def latTpsi (i : tw.Tw) (s : tw.Sig i) {O' : Type} [CommRing O'] (f : tw.O0 i →+* O')
    (ψ : GE N →* O'ˣ) : GE N →* Matrix (Fin R.r) (Fin R.r) O' :=
  twistM (mapM f (latT tw i s)) ψ⁻¹

variable {tw} (L : LocTheory) (nbt : Br.NBrTw tw) (i : tw.Tw) (s : tw.Sig i)
  (Q : Finset (PlE H)) {O' : Type} [CommRing O'] [IsDomain O'] (f : tw.O0 i →+* O')
  (hf : Function.Injective f) (ψ : GE N →* O'ˣ)


open Classical in
def condL : ∀ v, Submodule O'
    (H1 ((WKG (latTpsi tw i s f ψ)).comp (Dec (F := H.E) (N.plOm.1 v)).subtype)) :=
  fun v => if h : v ∈ placesOver H.E (tw.l i) then
    extCond f hf ((WKG (latT tw i s)).comp (decS N v)) (Br.bkTw L nbt i v h (latT tw i s))
      ((WKG (latTpsi tw i s f ψ)).comp (Dec (F := H.E) (N.plOm.1 v)).subtype)
  else ⊤

def selT : Submodule O' (H1 (WKG (latTpsi tw i s f ψ))) :=
  Formalism.GaloisCohomology.SelAll (WKG (latTpsi tw i s f ψ)) N.plOm
    (Formalism.GaloisCohomology.bkCond (WKG (latTpsi tw i s f ψ)) N.plOm (tw.l i) (setS tw i ∪ ↑Q)
      (condL L nbt i s f hf ψ))

def sT : WithTop ℚ := nlen (O := O') (tw.l i) ↥(selT L nbt i s Q f hf ψ)

variable (tw)

def toOk (i : tw.Tw) (k : ℕ) : tw.O0 i →+* tw.Ok i k :=
  (algebraMap (tw.O i) (tw.Ok i k)).comp (algebraMap (tw.O0 i) (tw.O i))

theorem toOk_inj (i : tw.Tw) (k : ℕ) : Function.Injective (toOk tw i k) :=
  (tw.Ok_inj i k).comp (tw.O_inj i)

theorem twO_inj (a : N.Loc) : Function.Injective (tw.twist₂ a) := by
  haveI : CharZero (FractionRing (N.O a)) := (N.embK a).charZero_iff (N.embK a).injective |>.1 inferInstance
  haveI : CharZero (N.O a) := (algebraMap (N.O a) (FractionRing (N.O a))).charZero
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (tw.twist₂ a)).IsPrime := RingHom.ker_isPrime _
  have hm : (RingHom.ker (tw.twist₂ a)).IsMaximal := hp.isMaximal hne
  have he := IsLocalRing.eq_maximalIdeal hm
  haveI := tw.twistBaseCoefficientRing_residueField_finite (tw.twOf a)
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField (tw.O0 (tw.twOf a)))
  have h0 : ((Fintype.card (IsLocalRing.ResidueField (tw.O0 (tw.twOf a))) : ℕ) :
      IsLocalRing.ResidueField (tw.O0 (tw.twOf a))) = 0 := FiniteField.cast_card_eq_zero _
  have h1 : ((Fintype.card (IsLocalRing.ResidueField (tw.O0 (tw.twOf a))) : ℕ) :
      tw.O0 (tw.twOf a)) ∈ RingHom.ker (tw.twist₂ a) := by
    rw [he, ← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact h0
  rw [RingHom.mem_ker, map_natCast, Nat.cast_eq_zero] at h1
  exact Fintype.card_ne_zero h1

end Tw

section Rec

variable (D : D7)

def sPiTop (a : D.nd.Loc) (ρ : D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (π : D.nd.X a) :
    WithTop ℚ :=
  nlen (O := D.nd.O a) (D.nd.l a) ↥(Br.selPi D.loc D.nbr a ρ π)

def sTLoc (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) : WithTop ℚ :=
  sT D.loc D.ntwbr (D.ntw.twOf a) s (D.nd.Q a) (D.ntw.twist₂ a) (twO_inj D.ntw a) (D.ntw.psiL a)

def IsRhoPt (a : D.nd.Loc) (π : D.nd.X a) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a))) ∧
  ∃ r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O a), IsHeckeGalois D.nd a π r ∧
    ∃ e : (Fin D.R.nV → KK D.nd a) ≃ₗ[KK D.nd a] ((Fin D.R.r → KK D.nd a) × (Fin D.R.t → KK D.nd a)),
      ∀ g u, e ((mapM (toK D.nd a) ((Units.coeHom _).comp r) g).mulVec u) =
        ((mapM (toK D.nd a) ((Units.coeHom _).comp ρ) g).mulVec (e u).1,
          fun c : Fin D.R.t =>
            toK D.nd a ((D.nd.chi a ((c : ℕ) + 1) g : (D.nd.O a)ˣ) : D.nd.O a) * (e u).2 c)

def GoodRowOf (j : ℕ) (σ : D.what₂.FT) : Prop := D.nd.goodRow σ ∧ D.what₂.isot j σ ≠ ⊥

def IsTriple (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)) : Prop :=
  D.ntw.jS _ s = D.nd.j a ∧ D.ntw.side _ s = D.ntw.twSide a ∧
  IsSSRep (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))
    (D.ntw.rhoS _ s)) ∧
  ∀ᶠ w in Filter.cofinite, SplitOut D.nd a w →
    ∀ (B : ValuationSubring D.nd.Om) (γ : GE D.nd), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) γ →
      ((D.ntw.rhoS _ s γ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly.map
          ((iotaO D.nd D.naut a).comp (D.ntw.twist₂ a)) =
        galPol D.naut (D.naut.lpTw (isoLoc D.nd D.naut (twistIso D.nd D.naut Sg D.naut.etaTinv) w)
          ((1 - (D.R.nV : ℝ)) / 2))

def AllTriples : Prop :=
  ∀ (a : D.nd.Loc) (σ : D.what₂.FT) (Sg : List (Part D.naut.CG)), GoodRowOf D (D.nd.j a) σ →
    HasParamW D.nd D.naut a σ Sg → ∃ s, IsTriple D a s Sg

def Attached (a : D.nd.Loc) (π : D.nd.X a) (s : D.ntw.Sig (D.ntw.twOf a)) : Prop :=
  ∃ (σ : D.what₂.FT) (Sg : List (Part D.naut.CG)), GoodRowOf D (D.nd.j a) σ ∧
    HasParamW D.nd D.naut a σ Sg ∧ HasParamX D.nd D.naut a π Sg ∧ IsTriple D a s Sg

end Rec

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ThetaLift
section
noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions
open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

section Theta
variable {P : Type} [Fintype P]

end Theta

section Schur
variable {T : Type} [Fintype T] {n₀ : ℕ}

end Schur

def hookProd (n : ℕ) (ν : ℕ → ℕ) : ℕ :=
  ∏ r ∈ Finset.range n, ∏ c ∈ Finset.range (ν r),
    ((ν r - c - 1) + ((Finset.Ioo r n).filter (fun r' => c < ν r')).card + 1)

variable (D : D7)

end GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistedTriples
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable (D : D7)

abbrev Trip (a : D.nd.Loc) : Type := D.ntw.Sig (D.ntw.twOf a)

def rhoTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* GL (Fin D.R.r) (D.nd.O a) :=
  mapRep (D.ntw.twist₂ a) (D.ntw.rhoS (D.ntw.twOf a) s)

def chiTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* (D.nd.O a)ˣ :=
  (Units.map (D.ntw.twist₂ a).toMonoidHom).comp
    (D.ntw.chi1 (D.ntw.twOf a) (D.ntw.jS (D.ntw.twOf a) s) (D.ntw.side (D.ntw.twOf a) s))

def tTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a) :=
  twistM ((Units.coeHom _).comp (rhoTrip D a s)) (chiTrip D a s)⁻¹

def badS (a : D.nd.Loc) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  {v | ((∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨ v ∈ D.ntw.pD (D.ntw.twOf a)) ∧
    v ∉ placesOver D.host.E (D.nd.l a)}

def selT (a : D.nd.Loc) (s : Trip D a) (ψ : GE D.nd →* (D.nd.O a)ˣ) :
    Submodule (D.nd.O a) (H1 (WKG (twistM (tTrip D a s) ψ⁻¹))) :=
  Br.selG D.nd.plOm (D.nd.l a) (D.loc (D.nd.l a)) (D.nbr a) (badS D a ∪ ↑(D.nd.Q a))
    (twistM (tTrip D a s) ψ⁻¹)

def IsGoodRow (a : D.nd.Loc) (σ : D.what₂.FT) : Prop :=
  D.what₂.isot (D.nd.j a) σ ≠ ⊥ ∧ D.nd.goodRow σ

def IsRhoOfRow (a : D.nd.Loc) (σ : D.what₂.FT) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) : Prop :=
  IsSSRep (mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) ρ) ∧
  ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w →
    ∀ (B : ValuationSubring D.nd.Om) (g : GE D.nd), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) g →
      ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).charpoly.map
          (iotaO D.nd D.naut a) =
        galPol D.naut (D.naut.lpTw (D.naut.lpChar (D.naut.locW a σ w) (D.naut.locG D.naut.etaTinv w))
          ((1 - (D.R.nV : ℝ)) / 2))

def IsTripleOf (a : D.nd.Loc) (σ : D.what₂.FT) (s : Trip D a) : Prop :=
  D.ntw.jS (D.ntw.twOf a) s = D.nd.j a ∧ D.ntw.side (D.ntw.twOf a) s = D.ntw.twSide a ∧
    IsRhoOfRow D a σ (rhoTrip D a s)

def TripAll : Prop :=
  ∀ (a : D.nd.Loc) (σ : D.what₂.FT), IsGoodRow D a σ → ∃ s : Trip D a, IsTripleOf D a σ s

def ind2 (l : ℕ) : ℚ := if l = 2 then 1 else 0

def epsL (l : ℕ) : ℚ := ((l : ℚ) ^ 2)⁻¹

theorem badS_eq (a : D.nd.Loc) : badS D a = ↑(D.nd.S a) := by
  ext v
  have h := D.ntw.pD_eq (D.ntw.twOf a)
  rw [D.ntw.twOf_l a] at h
  have h' : v ∈ D.ntw.pD (D.ntw.twOf a) ↔
      v ∈ placesOver D.host.E (if D.nd.l a = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← h]; rfl
  simp only [badS, Set.mem_setOf_eq, Finset.mem_coe, D.nd.S_def, h', Fin.exists_fin_two, or_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples

end
end

