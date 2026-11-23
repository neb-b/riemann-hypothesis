module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPtSSubset
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SmallDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}


variable (G i j) in
abbrev PtS : Type := Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)


variable (G i j) in
abbrev IxS : Type := Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)


variable (G) in
abbrev HomA (t : T) (i j : ℕ) : Type := WO (G.pS (.mu t i j)) (G.pT (.mu t i j))


variable (G i j) in
abbrev HomB : Type := WO (G.pS (.chi i j)) (G.pT (.chi i j))

abbrev mapA (t : T) (e : Num G i j) (u : PtS G i j) : HomA G t i j := mulG (spW₁ G i j) (colV e u)ᵀ

abbrev mapB (e : Num G i j) (u : PtS G i j) : HomB G i j := adjV₁ e u

def ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : PtS G i j :=
  (fromCols (GlobalTheory.BigDat.divG (spW₁ G i j) x.1)ᵀ ((GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2)).map (cA D))).submatrix id e.symm

theorem mapA_ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : mapA t e (ofMaps t e x) = x.1 := by
  have h1 : (colV e (ofMaps t e x))ᵀ = GlobalTheory.BigDat.divG (spW₁ G i j) x.1 := Matrix.ext fun a b => by
    simp only [colV, ofMaps, transpose_apply, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl]
  exact (congrArg (mulG (spW₁ G i j)) h1).trans (GlobalTheory.BigDat.mulG_divG _ _)

theorem mapB_ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : mapB e (ofMaps t e x) = x.2 := by
  have h2 : ((ofMaps t e x).submatrix id fun k => e (.inr k)).map (cA D) = GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2) :=
    Matrix.ext fun a b => by
      simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply,
        GlobalTheory.DualPairCheck.cA_cA]
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h2).trans ((congrArg Neg.neg (GlobalTheory.BigDat.mulG_divG _ _)).trans (neg_neg _))

theorem ofMaps_maps (t : T) (e : Num G i j) (u : PtS G i j) : ofMaps t e (mapA t e u, mapB e u) = u := by
  have h1 : GlobalTheory.BigDat.divG (spW₁ G i j) (mapA t e u) = (colV e u)ᵀ := GlobalTheory.BigDat.divG_mulG _ _
  have h2 : GlobalTheory.BigDat.divG (spV₁ G i j) (-mapB e u) = (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    (congrArg (GlobalTheory.BigDat.divG (spV₁ G i j)) (neg_neg _)).trans (GlobalTheory.BigDat.divG_mulG _ _)
  ext a b
  obtain ⟨k | k, rfl⟩ := e.surjective b
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]
    exact congrFun (congrFun h1 k) a
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]
    exact (congrArg (cA D) (congrFun (congrFun h2 a) k)).trans (GlobalTheory.DualPairCheck.cA_cA _)

theorem mapA_add (t : T) (e : Num G i j) (u u' : PtS G i j) : mapA t e (u + u') = mapA t e u + mapA t e u' :=
  GlobalTheory.RouteCoords.mulG_colV_add e u u'

theorem mapB_add (e : Num G i j) (u u' : PtS G i j) : mapB e (u + u') = mapB e u + mapB e u' :=
  GlobalTheory.RouteCoords.adjV₁_add e u u'

theorem mapA_smul (t : T) (e : Num G i j) (c : AF D.host.F) (u : PtS G i j) : mapA t e (c • u) = c • mapA t e u :=
  GlobalTheory.BigDat.mulG_smul (spW₁ G i j) c (colV e u)ᵀ

theorem mapB_smul (e : Num G i j) (c : AF D.host.F) (u : PtS G i j) : mapB e (c • u) = c • mapB e u := by
  have h : ((c • u).submatrix id fun k => e (.inr k)).map (cA D) = c • (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans
    ((congrArg Neg.neg (GlobalTheory.BigDat.mulG_smul _ _ _)).trans (smul_neg _ _).symm)

def maps (t : T) (e : Num G i j) : PtS G i j ≃ₗ[AF D.host.F] HomA G t i j × HomB G i j where
  toFun u := (mapA t e u, mapB e u)
  invFun := ofMaps t e
  map_add' u u' := Prod.ext (mapA_add t e u u') (mapB_add e u u')
  map_smul' c u := Prod.ext (mapA_smul t e c u) (mapB_smul e c u)
  left_inv := ofMaps_maps t e
  right_inv x := Prod.ext (mapA_ofMaps t e x) (mapB_ofMaps t e x)

theorem maps_apply (t : T) (e : Num G i j) (u : PtS G i j) : maps t e u = (mapA t e u, mapB e u) := rfl

abbrev sympS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (u u' : PtS G i j) : AF D.host.F :=
  symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u'

theorem sympS_eq (t : T) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e)
    (x x' : PtS G i j) :
    sympS Γ x x' = symplO _ _ (mapA t e x) (mapA t e x') + symplO _ _ (mapB e x) (mapB e x') :=
  GlobalTheory.RouteCoords.symp_eq t e Γ hW₁ hWW x x'

def boxS (t : T) (e : Num G i j) (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) (u : PtS G i j) : ℂ :=
  f₁ (mapA t e u) * f₂ (mapB e u)

def heisS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : PtS G i j) (f : PtS G i j → ℂ)
    (u : PtS G i j) : ℂ :=
  ψ (⅟(2 : AF D.host.F) * sympS Γ u u₀) * f (u + u₀)

theorem heisS_box (t : T) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e)
    (ψ : AddChar (AF D.host.F) ℂ) (u₀ : PtS G i j) (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) :
    heisS Γ ψ u₀ (boxS t e f₁ f₂) = boxS t e (heisO ψ _ _ (mapA t e u₀) f₁) (heisO ψ _ _ (mapB e u₀) f₂) := by
  funext u
  unfold heisS boxS heisO symplOH
  rw [sympS_eq t e Γ hW₁ hWW, mul_add, AddChar.map_add_eq_mul, mapA_add, mapB_add, GlobalTheory.BigDat.invOf_two]
  ring

abbrev thetaS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (IxS G i j → AF D.host.F) → ℂ)
    (u : PtS G i j) : ℂ := thetaSum D.host.F (Γ.M'.co.rho ψ u Φ)

theorem thetaS_rho (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (IxS G i j → AF D.host.F) → ℂ)
    (u₀ : PtS G i j) : thetaS Γ ψ (Γ.M'.co.rho ψ u₀ Φ) = heisS Γ ψ u₀ (thetaS Γ ψ Φ) :=
  funext fun u => (congrArg (thetaSum D.host.F) (GlobalTheory.BigDat.rho_rho Γ.M'.co ψ u u₀ Φ)).trans tsum_mul_left

theorem thetaS_smul (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ)
    (Φ : (IxS G i j → AF D.host.F) → ℂ) (u : PtS G i j) : thetaS Γ ψ (c • Φ) u = c * thetaS Γ ψ Φ u :=
  (tsum_congr fun _ => mul_left_comm _ _ _).trans tsum_mul_left


variable (G) in
abbrev latA (t : T) (i j : ℕ) : AddSubgroup (HomA G t i j) :=
  latO (G.pS (.mu t i j)) (G.pT (.mu t i j)) (G.latS (.mu t i j) : Set _) (G.latT (.mu t i j) : Set _) fun _ => True


variable (G i j) in
abbrev latB : AddSubgroup (HomB G i j) :=
  latO (G.pS (.chi i j)) (G.pT (.chi i j)) (G.latS (.chi i j) : Set _) (G.latT (.chi i j) : Set _) fun _ => True

def latPtS (t : T) (e : Num G i j) (v : Pl D.host.F) : AddSubgroup (PtS G i j) where
  carrier := {u | At (evFin D.host.F v) u ∧ mapA t e u ∈ latA G t i j ∧ mapB e u ∈ latB G i j}
  zero_mem' := ⟨fun u _ => smul_zero u, by
    rw [show mapA t e 0 = 0 from congrArg Prod.fst (map_zero (maps t e))]; exact zero_mem _, by
    rw [show mapB e 0 = 0 from congrArg Prod.snd (map_zero (maps t e))]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero],
    by rw [mapA_add]; exact add_mem ha.2.1 hb.2.1, by rw [mapB_add]; exact add_mem ha.2.2 hb.2.2⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by
    rw [show mapA t e (-a) = -mapA t e a from congrArg Prod.fst (map_neg (maps t e) a)]; exact neg_mem ha.2.1, by
    rw [show mapB e (-a) = -mapB e a from congrArg Prod.snd (map_neg (maps t e) a)]; exact neg_mem ha.2.2⟩

def genPtS (t : T) (e : Num G i j) (v : Pl D.host.F) : Set (PtS G i j) :=
  {γ | (∃ γ' ∈ latPtS t e v, γ = 2 • γ') ∨ γ ∈ latPtS t e v ∧ ∃ ε, IsSplitIdem D ε ∧ γ ∈ GlobalTheory.FlipMatch.mixHalfS e ε}

theorem genPtS_subset (t : T) (e : Num G i j) (v : Pl D.host.F) : genPtS t e v ⊆ latPtS t e v := by
  rintro _ (⟨γ, h, rfl⟩ | h)
  exacts [nsmul_mem h 2, h.1]

end GlobalTheory.SmallDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjComponentIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IdemPairCpt

open GlobalTheory.StdFrames

theorem cpt_sg_eq_one_of_cP_mem {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (w : Pl D.host.E) (hw : GlobalTheory.IdemSupport.cP w ∈ P) : cpt (D := D) w (sg D (toEAf D e)) = 1 := by
  have h1 : cpt (D := D) (GlobalTheory.IdemSupport.cP w) (1 - toEAf D e) = 0 := by
    rw [map_sub, map_one, GlobalTheory.OffPartLattice.cpt_idemSum he, if_pos hw, sub_self]
  have h2 := cpt_sg_eq_zero h1
  rw [map_sub, map_one, map_sub, map_one] at h2
  exact (sub_eq_zero.mp h2).symm

theorem cpt_sg_eq_zero_of_cP_notMem {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (w : Pl D.host.E) (hw : GlobalTheory.IdemSupport.cP w ∉ P) : cpt (D := D) w (sg D (toEAf D e)) = 0 := by
  have h1 : cpt (D := D) (GlobalTheory.IdemSupport.cP w) (toEAf D e) = 0 := by
    rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg hw]
  exact cpt_sg_eq_zero h1

theorem cpt_add_cA_idemSum : ∀ {D : D7} {e : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum e P → ∀ w : Pl D.host.E,
    ((w ∈ P ∨ GlobalTheory.IdemSupport.cP w ∈ P) → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 1) ∧
    (w ∉ P → GlobalTheory.IdemSupport.cP w ∉ P → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 0) := by
  intro D e P he w
  have hsplit : GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) =
      cpt (D := D) w (toEAf D e) + cpt (D := D) w (sg D (toEAf D e)) := by
    rw [map_add (f := _), toEAf_cA, map_add (f := _)]
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
  · rw [hsplit]
    by_cases hw : w ∈ P
    · have hc : GlobalTheory.IdemSupport.cP w ∉ P := fun hc => GlobalTheory.IdemSumBranch.conjPrime_ne he hc hw rfl
      rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_pos hw, cpt_sg_eq_zero_of_cP_notMem he w hc, add_zero]
    · have hc : GlobalTheory.IdemSupport.cP w ∈ P := h.resolve_left hw
      rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg hw, cpt_sg_eq_one_of_cP_mem he w hc, zero_add]
  · rw [hsplit, GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg h1, cpt_sg_eq_zero_of_cP_notMem he w h2, add_zero]

end GlobalTheory.IdemPairCpt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemSumUniq

theorem idemSum_unique : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e e' : AE D), IsIdemSum e P → IsIdemSum e' P → e = e' := by
  intro D P e e' h h'
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hP =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ PP PP (hes PP hP) (hes' PP hP)).1 rfl

end GlobalTheory.IdemSumUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitriangularOfRationalMulMemCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem det_eq_one_of_upperUni {A : Type} [CommRing A] {ρ : ℕ} {M : Matrix (Fin ρ) (Fin ρ) A}
    (h : ∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) : M.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]
  simp [fun i => (h i i).2]

theorem mem_UX_iff_entries {D : D7} {ρ : ℕ} (v : GL (Fin ρ) (AE D)) :
    v ∈ UX D ρ ↔ ∀ i j : Fin ρ, (j < i → v.val i j = 0) ∧ v.val i i = 1 := Iff.rfl

theorem exists_unit_of_upperUni {A : Type} [CommRing A] {ρ : ℕ} {M : Matrix (Fin ρ) (Fin ρ) A}
    (h : ∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) :
    ∃ v : GL (Fin ρ) A, v.val = M ∧ (v⁻¹).val = M.adjugate := by
  have hdet := det_eq_one_of_upperUni h
  refine ⟨⟨M, M.adjugate, ?_, ?_⟩, rfl, rfl⟩
  · rw [Matrix.mul_adjugate, hdet, one_smul]
  · rw [Matrix.adjugate_mul, hdet, one_smul]

theorem isCompact_setOf_rat_mul_mem : ∀ (D : D7) (n ρ : ℕ) (x₀ : Matrix (Fin n) (Fin ρ) D.host.E), LinearIndependent D.host.E x₀.transpose → ∀ K : Set (Mx D n ρ), IsCompact K → IsCompact {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} := by
  intro D n ρ x₀ hx K hK
  obtain ⟨-, hT2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hinj : Function.Injective x₀.mulVec := Matrix.mulVec_injective_iff.2 hx
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin x₀) (LinearMap.ker_eq_bot.2 hinj)
  have hL : LinearMap.toMatrix' g * x₀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hLr : rat (LinearMap.toMatrix' g) ⬝ rat x₀ = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) := by
    simp only [rat]
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  set S' : Set (Matrix (Fin ρ) (Fin ρ) (AE D)) :=
    {M | (∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) ∧ rat x₀ ⬝ M ∈ K} with hS'def
  have hC : IsCompact ((fun N : Mx D n ρ => rat (LinearMap.toMatrix' g) ⬝ N) '' K) :=
    hK.image (continuous_const.matrix_mul continuous_id)
  have hsub : S' ⊆ (fun N : Mx D n ρ => rat (LinearMap.toMatrix' g) ⬝ N) '' K := by
    rintro M ⟨-, hM⟩
    exact ⟨_, hM, by simp only [← Matrix.mul_assoc, hLr, Matrix.one_mul]⟩
  have hcl : IsClosed S' := by
    rw [hS'def, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) (hK.isClosed.preimage ((continuous_const (y := (rat x₀ : Mx D n ρ))).matrix_mul (continuous_id (X := Matrix (Fin ρ) (Fin ρ) (AE D)))))
    rw [Set.setOf_forall]
    refine isClosed_iInter fun j => ?_
    rw [Set.setOf_and]
    exact (isClosed_imp isOpen_const (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hS' : IsCompact S' := hC.of_isClosed_subset hcl hsub
  let ι : UX D ρ → Matrix (Fin ρ) (Fin ρ) (AE D) × (Matrix (Fin ρ) (Fin ρ) (AE D))ᵐᵒᵖ := fun u => Units.embedProduct _ u.1
  have hι : Topology.IsEmbedding ι := Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
  have hF : Continuous (fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => (M, MulOpposite.op M.adjugate)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate)
  have heq : ι '' {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} = (fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => (M, MulOpposite.op M.adjugate)) '' S' := by
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hU : ∀ i j : Fin ρ, (j < i → u.1.1 i j = 0) ∧ u.1.1 i i = 1 := u.2
      refine ⟨u.1.1, ⟨hU, hu⟩, ?_⟩
      have hdet := det_eq_one_of_upperUni hU
      refine Prod.ext rfl ?_
      show MulOpposite.op u.1.1.adjugate = MulOpposite.op (Units.val (u.1)⁻¹)
      congr 1
      rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
    · rintro ⟨M, ⟨hU, hM⟩, rfl⟩
      have hdet := det_eq_one_of_upperUni hU
      obtain ⟨v, hv1, hv2⟩ := exists_unit_of_upperUni hU
      subst hv1
      have hmem : v ∈ UX D ρ := (mem_UX_iff_entries v).2 hU
      refine ⟨⟨v, hmem⟩, hM, ?_⟩
      exact Prod.ext rfl (congrArg MulOpposite.op hv2)
  rw [hι.isInducing.isCompact_iff, heq]
  exact hS'.image hF

end GlobalTheory.AscFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOfStabiliserMulInvEqStandardLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section
namespace GlobalTheory.LatStdStab
open Matrix
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem latAt_mul_inv_eq_stdL : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ k : FinPt G X,
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X)) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V X) k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X))) →
    GlobalTheory.SumSize.latAt S X (k * (S.N.u X)⁻¹) = stdL D _ := by
  intro D T L sc G W S X hX k hk
  have hC := GlobalTheory.MovedHomLat.colLat_fin (S.N.fr X)
  have hsp := GlobalTheory.MovedHomLat.colLat_span (S.N.fr X)

  have key : ∀ y, y ∈ Formalism.UG.CS.globLat (finG (G.V X) (k * (S.N.u X)⁻¹)) (G.Λ X) ↔ y ∈ colLat (S.N.fr X) := by
    intro y
    have e : finG (G.V X) (k * (S.N.u X)⁻¹) * Formalism.IndefR.Lev.finE (G.V X) (S.N.u X).1 =
        Formalism.IndefR.Lev.finE (G.V X) k.1 := by
      show Formalism.IndefR.Lev.finE (G.V X) ((k * (S.N.u X)⁻¹ : FinPt G X) : GA D (G.V X)) * _ = _
      rw [← map_mul]
      congr 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [GlobalTheory.MovedHomLat.globLat_mul_iff _ _ _ _ (S.N.u_lat X hX), e, GlobalTheory.MovedHomLat.mem_globLat_iff]
    rw [hk, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact GlobalTheory.CongStdLoc.incl_mem_hatL_iff (F := D.host.F) (Module.Finite.iff_fg.1 hC) hsp y
  ext z
  simp only [GlobalTheory.SumSize.latAt, Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  rw [key]
  have := congrArg (z ∈ ·) (GlobalTheory.ColStd.colLat_comap_eq_stdLat (S.N.fr X))
  simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at this
  exact Iff.of_eq this

end GlobalTheory.LatStdStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesSubsetChosenPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

namespace GlobalTheory.LevelPlacesChosen

theorem levelPlaces_subset_chosenPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → L.Pg ⊆ G.pl.W0 := by
  intro D T L sc G μ₀ hμ P hP
  obtain ⟨k, hk⟩ := (hμ.Pg P).1 hP
  have hK : P.under (𝓞 D.host.K) = L.C.P.pb k := hk
  have hgE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (P.under (𝓞 D.host.K)).asIdeal := by
      rw [hK]; exact L.C.P.pb_over k
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal := h1
    rwa [map_natCast] at h2
  have hgF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal
    rw [map_natCast]; exact hgE
  have hS1 : P.under (𝓞 D.host.F) ∈ S1 D := by
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hgF
    · exact Or.inr (Or.inl hgF)
  have hS0 : P.under (𝓞 D.host.F) ∈ insert G.pl.v0 (S1 D) := Finset.mem_insert_of_mem hS1
  have hwPg : G.pl.w (P.under (𝓞 D.host.F)) ∈ L.Pg := G.pl.w_g _ k hgF
  have hover : (G.pl.w (P.under (𝓞 D.host.F))).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := G.pl.w_over _ hS0
  have heq : G.pl.w (P.under (𝓞 D.host.F)) = P := by
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hover with h | h
    · exact h
    · exact absurd ((GlobalTheory.GoodPrimes.isConjPl_iff).2 h)
        (GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg hμ.Pg P hP _ hwPg)
  unfold Places.W0
  exact Finset.mem_image.2 ⟨_, hS0, heq⟩

end GlobalTheory.LevelPlacesChosen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    K * K' = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.tMat c K * GlobalTheory.SplitDblGen.tMat c K' = 1 := by
  first | exact @GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one | exact GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one | (intros; apply GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one <;> assumption)
end

