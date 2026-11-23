module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFockVectorHeisenbergAverageIsotropicEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistence
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.BigOn.Exp.Adapt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ext_frac {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) [Module.Finite A B] (f : FractionRing A →+* ℂ) :
    ∃ g : FractionRing B →+* ℂ, ∀ a : A, g (algebraMap B _ (algebraMap A B a)) = f (algebraMap A _ a) := by
  letI : Algebra A ℂ := (f.comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsAlgebraic A B := inferInstance
  haveI : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A (FractionRing B) := Algebra.IsAlgebraic.trans A B (FractionRing B)
  have hA : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj
  have hC : Function.Injective (algebraMap A ℂ) :=
    f.injective.comp (IsFractionRing.injective A (FractionRing A))
  haveI : Module.IsTorsionFree A (FractionRing B) := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => hA (h.trans (map_zero _).symm)) id
  haveI : Module.IsTorsionFree A ℂ := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => hC (h.trans (map_zero _).symm)) id
  let g := IsAlgClosed.lift (M := ℂ) (R := A) (S := FractionRing B)
  refine ⟨g.toRingHom, fun a => ?_⟩
  have h := g.commutes a
  rw [IsScalarTower.algebraMap_apply A B (FractionRing B)] at h
  exact h

variable {D : D7}

theorem charOf_congr {Ω : Type} [Field Ω] [Algebra D.host.E Ω] (a : Recip D Ω) {R : Type} [CommRing R]
    (f f' : R →+* ℂ) (ψ : G D.host.E Ω →* Rˣ) (h : ∀ σ, f (ψ σ : Rˣ) = f' (ψ σ : Rˣ)) :
    GlobalTheory.SeriesTie.charOf a f ψ = GlobalTheory.SeriesTie.charOf a f' ψ := by
  have hv : ∀ x, ∃ σ, a.pull ψ x = ψ σ := by
    intro x
    unfold Recip.pull GlobalTheory.SeriesTie.descend
    split_ifs with hc
    · obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective _ (a.sym x)
      refine ⟨σ, ?_⟩
      rw [MonoidHom.comp_apply, ← hσ]
      rfl
    · exact ⟨1, by simp⟩
  refine MonoidHom.ext fun x => ?_
  obtain ⟨σ, hσ⟩ := hv x
  simp only [GlobalTheory.SeriesTie.charOf, MonoidHom.comp_apply, hσ]
  rw [show Units.map f.toMonoidHom (ψ σ) = Units.map f'.toMonoidHom (ψ σ) from Units.ext (h σ)]


open Classical in
def withTau (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) : Setup D.ntw :=
  { ρ with
    e := fun i b => if i = t ∧ b = s then τ.toRingHom.comp (ρ.e i b) else ρ.e i b
    ek := fun i b k => if i = t ∧ b = s then τ.toRingHom.comp (ρ.ek i b k) else ρ.ek i b k }


open Classical in
theorem withTau_e (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) (i : D.ntw.Tw) (b : Bool) :
    (withTau ρ t s τ).e i b = if i = t ∧ b = s then τ.toRingHom.comp (ρ.e i b) else ρ.e i b := rfl


open Classical in
theorem withTau_ek (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) (i : D.ntw.Tw) (b : Bool) (k : ℕ) :
    (withTau ρ t s τ).ek i b k = if i = t ∧ b = s then τ.toRingHom.comp (ρ.ek i b k) else ρ.ek i b k := rfl

theorem withTau_good {ρ : Setup D.ntw} (hρ : ρ.Good) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ)
    (hfix : ∀ y, τ (embLL0 D y) = embLL0 D y)
    (hδ : ∀ σ, τ (ρ.eO t s (algebraMap (D.ntw.O0 t) (D.ntw.O t)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt s (D.ntw.delta t) σ : (D.ntw.O0 t)ˣ) : D.ntw.O0 t))) =
      ρ.eO t s (algebraMap (D.ntw.O0 t) (D.ntw.O t) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt s (D.ntw.delta t) σ : (D.ntw.O0 t)ˣ) : D.ntw.O0 t))) :
    (withTau ρ t s τ).Good := by
  refine ⟨hρ.rc, hρ.ch, hρ.bad_ne, hρ.goodSetup_bad_mem_badPlaces, hρ.goodSetup_badPlaces_conj, hρ.goodSetup_placesOverTwo_subset, hρ.goodSetup_count_eq_zero_off_badPlaces, ?_, ?_, hρ.base, hρ.latS, hρ.latT, hρ.Pg,
    ?_, hρ.weil, hρ.classes⟩
  · intro i b x
    rw [withTau_e]
    split_ifs with h
    · show τ (ρ.e i b _) = _
      rw [hρ.e_LL0]
      exact hfix x
    · exact hρ.e_LL0 i b x
  · intro i b k x
    show (withTau ρ t s τ).ek i b k _ = (withTau ρ t s τ).e i b _
    rw [withTau_e, withTau_ek]
    split_ifs with h
    · exact congrArg τ (hρ.ek_e i b k x)
    · exact hρ.ek_e i b k x
  · intro i j b
    show (ρ.B i j b).de = twistOf ρ.rc (((withTau ρ t s τ).eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (ρ.ch i)
      (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
    rw [hρ.delta i j b]
    unfold twistOf
    have : GlobalTheory.SeriesTie.charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) =
        GlobalTheory.SeriesTie.charOf ρ.rc (((withTau ρ t s τ).eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
          (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) := by
      refine charOf_congr _ _ _ _ fun σ => ?_
      show ρ.e i b _ = (withTau ρ t s τ).e i b _
      rw [withTau_e]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact (hδ σ).symm
      · rfl
    rw [this]

theorem ext_onSmallField {c : NChoice D} (hc : NChTie D c) (w : D.what₂.places.Pl) {ρ : Setup D.ntw} (hρ : ρ.Good)
    (g : FractionRing (c.Oe w) →+* ℂ)
    (hg : ∀ a : D.ntw.Ok (c.twI w) (c.k' w), g (algebraMap (c.Oe w) _ (algebraMap _ (c.Oe w) a)) =
      ρ.ek (c.twI w) (c.sd w) (c.k' w) (algebraMap _ _ a))
    (y : D.LL0) : g (c.embW w (y : D.what₂.LL)) = embLL0 D y := by
  obtain ⟨⟨y', z⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors (D.ntw.O0 (c.twI w)))
    ((if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) y)
  have hz0 : (z : D.ntw.O0 (c.twI w)) ≠ 0 := nonZeroDivisors.coe_ne_zero z
  have e1 : ∀ x : D.ntw.O (c.twI w), ρ.ek (c.twI w) (c.sd w) (c.k' w)
      (algebraMap _ (FractionRing _) (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) x)) =
      ρ.e (c.twI w) (c.sd w) (algebraMap _ _ x) := hρ.ek_e (c.twI w) (c.sd w) (c.k' w)
  have h1 := congrArg g (hc.embedding_baseField_condition w y y' z hz0 hz)
  rw [map_mul, hg, hg, e1, e1] at h1
  have h2 : sideEmb D.ntw (c.twI w) (c.sd w) y * algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w)))
      (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z) =
      algebraMap _ _ (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y') := by
    have := congrArg (IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w))
      (K := FractionRing (D.ntw.O0 (c.twI w))) (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w))) hz
    simp only [map_mul, IsFractionRing.map, IsLocalization.map_eq] at this
    exact this
  have h3 := congrArg (ρ.e (c.twI w) (c.sd w)) h2
  rw [map_mul, hρ.e_LL0] at h3
  have hne : ρ.e (c.twI w) (c.sd w) (algebraMap _ (FractionRing (D.ntw.O (c.twI w)))
      (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z)) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      ((map_ne_zero_iff _ (D.ntw.O_inj (c.twI w))).2 hz0))
  exact mul_right_cancel₀ hne (h1.trans h3.symm)

section Point

theorem realPin_withTau {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (h : RealPin Rl cG ρ)
    (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) : RealPin Rl cG (withTau ρ t s τ) :=
  { psi := h.psi, inf := h.inf, cartT := h.cartT, onbS := h.onbS, onbT := h.onbT, latS := h.latS, latT := h.latT,
    frS := h.frS, frT := h.frT, vac := h.vac, Pg := h.Pg, grp := h.grp, mu0 := h.mu0, eta := h.eta, delta := h.delta,
    deltaPl := h.deltaPl, ap := h.ap, am := h.am }

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem adapt_at (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m) (hm : More p) (ρ : Setup D.ntw) (hρ : ρ.Good)
    (hpin : RealPin p.R p.cG ρ) : ∃ ρ' : Setup D.ntw, ρ'.Good ∧ SameBut ρ ρ' ∧ Adapted p w ρ' := by
  haveI : Module.Finite (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w) := ex.nch.Oe_fin w
  obtain ⟨g, hg⟩ := exists_ext_frac (ex.nch.Oe_inj w) (ρ.ek (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w))
  haveI : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.symm.toEquiv
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL (g.comp (ex.nch.embW w)) D.what₂.embLL
  have hfix : ∀ y : D.LL0, τ (embLL0 D y) = embLL0 D y := fun y => by
    have h := ext_onSmallField ex.nch_tie w hρ g hg y
    have h2 : τ (g (ex.nch.embW w (y : D.what₂.LL))) = D.what₂.embLL y := hτ _
    rw [h] at h2
    exact h2
  have hχ : (p.R.C.delAt (D.ntw.l (ex.nch.twI w))).ValuesIn 0 (embLL0 D) := by
    have hv := hm.2.2.small.val
    unfold CharFrame.delAt
    split_ifs
    exacts [hv.del', hv.del]
  have hδ := _root_.GlobalTheory.DeltaFixed.aut_fixes_delta_values ρ hρ (ex.nch.twI w) j (ex.nch.sd w) _ (hpin.delta _ j _) hχ τ hfix
  refine ⟨withTau ρ (ex.nch.twI w) (ex.nch.sd w) τ, withTau_good hρ _ _ τ hfix hδ, ⟨rfl, rfl, rfl, rfl, rfl⟩, realPin_withTau hpin _ _ τ,
    τ.toRingHom.comp g, fun x => hτ x, fun a => ?_⟩
  show τ (g _) = (withTau ρ (ex.nch.twI w) (ex.nch.sd w) τ).ek (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) _
  rw [withTau_ek, if_pos ⟨rfl, rfl⟩]
  exact congrArg τ (hg a)

end Point

end GlobalTheory.BigOn.Exp.Adapt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftMemCuspFormMultiplicitySpace
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.CuspLift

theorem liftIsCuspC : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), LiftIsCuspC R F := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F
  intro i t σ s P cμ cη m ω BW f₀ f c io hd ν 𝓕 hν φ hφ
  obtain ⟨hcore, -, hemb, -, -, hom, -, -, hpt, hc, hio⟩ := id hd
  have h5 := GlobalTheory.Core5.of_core hcore
  have hm := h5.models
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨hM, w, hw⟩ := _root_.GlobalTheory.LowRow.holShape_overK R F h5 i σ s hemb
  have : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hF := GlobalTheory.ThetaIntegrand.form_continuous (finHom (Vc D i)).rangeRestrict (GQ (Vc D i)) c.ρ hc.2.2.1
    (eventually_grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) hφ
  have key := GlobalTheory.DefLift.ThetaMap.exists_member hP hom hm.inf hpos hM hw hc
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW f) hpt hio
    (_root_.GlobalTheory.LowKillDelta.rderC_ptAt_delta_eq_zero R F i t σ s P cμ cη m ω BW f₀ f c io hd)
    (J := levS _ (R.βW i) (R.datWp i R.triv)) (fun _ hk => hk.1) (GlobalTheory.DefLift.ThetaMap.level_open _ _ _)
    (fun k hk Q => GlobalTheory.PrincipalLevelFock.levW_fix_ptAt R F i t σ s P cμ cη m ω BW f₀ f c io hd Q k hk)
    (GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters.principalLevelCharacter_eq_one R i)
    (fun Q h g ξ hξ => _root_.GlobalTheory.LevelSupport.sum_heisO_along_eq_zero_level R F i t σ s P cμ cη m ω BW f₀ f c io hd Q h g ξ hξ)
    hF (GlobalTheory.ThetaIntegrand.ext_invariant c hφ) hν.1.1 hν.2
  obtain ⟨Θ, hΘ, hΘv⟩ := key
  refine ⟨Θ, Submodule.subset_span hΘ, fun v g => ?_⟩
  rw [hΘv v]
  rfl

end GlobalTheory.LowRow.CuspLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGapsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anchoredWeight_indefiniteLift_gaps : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
    (p : PtAt ex Csz) (P : ParameterChoice' D L) (i : Fin D.R.m), (i : ℕ) + 1 < D.R.m →
    (dat p i).p + (dat p i).q = D.R.r ∧ GlobalTheory.FlagTan.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 ∧
    ∀ (τ : Psi p.T.Q.H) (k : ℕ), k + 1 < (dat p i).p + (dat p i).q →
      (k + 1 ≠ (dat p i).p → min (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L) - 2 ≤ (gap (uW p i τ) k : ℝ)) ∧
      (k + 1 = (dat p i).p → LevelStarExponents.h0 L + D.R.r - 3 ≤ (gap (uW p i τ) k : ℝ)) := by
  first | exact @GlobalTheory.RecGaps.gaps | exact GlobalTheory.RecGaps.gaps | (intros; apply GlobalTheory.RecGaps.gaps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzDatumStableHeisenbergDerivati
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigNZ.DatRealStable

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem schr_schr_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (f : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' f) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') f x := by
  simp only [GlobalTheory.WeilM.schr, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm w'.1 w.2]
  first
    | linear_combination (w.1 ⬝ᵥ w'.2) * invOf_mul_self (2 : R)
    | linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

theorem sum_tensT (W : G.Weil) {X Y : Node} {p : Path T X Y} (a : PolT G p →₀ ℂ) (τ : TotT G p) (g : PureT G p → ℂ) :
    (tensT W a τ).sum (fun d c => c * g d) =
      a.sum fun P c => τ.sum fun d c' => c * c' * g (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) := by
  unfold tensT
  rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun P _ => ?_
  beta_reduce
  rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun d _ => ?_
  beta_reduce
  rw [Finsupp.sum_single_index (zero_mul _)]

theorem datum_stable : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ (f : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank))) a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ f₁ : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Γ.M.heisLine Bs.ψ u) f f₁ →
    ∃ a', IsDatumA W e Γ (tensT W a' τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f a ha u hu f₁ h1
  change TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) at τ
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hFr : IsTotallyReal D.host.F := hT.base.cm.1
  have hψc : IsCharAF D.host.F W.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hψ
  have hstd := (hT.geo.hM.std.and (Finset.finite_toSet X.T).compl_mem_cofinite).mono
    fun v hv => (hφ.2 v hv.2).trans hv.1
  have hrest := GlobalTheory.ThK.EvUniqInf.rest_pure f φ hφ.1 hstd
  have hmem1 := GlobalTheory.TensUniq.pure_mem_schA f₁ φ hφ.1 hstd
  have hd : ∀ x, HasDerivAt (fun s : ℝ => Γ.M.co.rho W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ x) 0 := by
    intro x
    rw [← h.ψ]
    exact h1 _ hrest x
  choose b hb using fun P => _root_.GlobalTheory.RouteBoxDeriv.hasDerivAt_box hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF u hu P
  refine ⟨a.sum fun P c => c • b P, hmem1, fun v => ?_⟩
  have H1 := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho Γ.M.co W.ψ hFr hψc u _ ha.1 _ hmem1 hd v
  set g : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) → PureT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) → _ → ℂ :=
    fun P d => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) with hg
  set ph : ℝ → ℂ := fun s => W.ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).2 -
        (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).1 ⬝ᵥ (Γ.M.co.e v).2)) with hph
  have e1 : ∀ s : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho W.ψ v (Γ.M.co.rho W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) = ∑ P ∈ a.support, ∑ d ∈ τ.support,
        a P * τ d * (ph s * g P d (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)) := by
    intro s
    have e2 : GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho W.ψ v (Γ.M.co.rho W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) = ph s * GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho W.ψ
          (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) := by
      unfold GlobalTheory.WeilM.thetaSum
      rw [← tsum_mul_left]
      refine tsum_congr fun ξ => ?_
      simp only [GlobalTheory.WeilM.Darboux.rho, map_add (f := _)]
      exact schr_schr_apply W.ψ _ _ _ _
    rw [e2, ha.2, sum_tensT, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hg]
    ring
  have H2 : HasDerivAt (fun s : ℝ => ∑ P ∈ a.support, ∑ d ∈ τ.support,
        a P * τ d * (ph s * g P d (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)))
      (∑ P ∈ a.support, ∑ d ∈ τ.support, a P * τ d * (b P).sum fun P' c => c * g P' d v) 0 :=
    HasDerivAt.fun_sum fun P _ => HasDerivAt.fun_sum fun d hd => (hb P d hd v).const_mul (a P * τ d)
  rw [← funext e1] at H2
  rw [H1.unique H2, sum_tensT, Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp only [add_mul, Finsupp.sum_add])]
  refine Finset.sum_congr rfl fun P _ => ?_
  beta_reduce
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P' _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [hg, smul_eq_mul]
  ring

end GlobalTheory.BigNZ.DatRealStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.ExpTie

def parOf {D : D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) : Par where
  k := D.R.k
  m := D.R.m
  t := D.R.t
  f := D.R.f
  n := D.R.n
  Nr := (Vc D j).rank
  L := L.sc.L
  x := L.sc.x
  b' := L.sc.b'
  η := L.etaSz
  S := L.Sc

end GlobalTheory.ExpTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealIndicatorUnitBlockTranslateReadsWeilOpeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjIdealIndicator_unitBlockTranslate_reads_weilOperator : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∀ (G : VC D a d → ℂ) (o : ℕ), Reads ψ θ hS hT ⊤ δ 1 G (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1 (ζ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) G)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o))) := by
  first | exact @GlobalTheory.BotSmallTransl.reads_transl | exact GlobalTheory.BotSmallTransl.reads_transl | (intros; apply GlobalTheory.BotSmallTransl.reads_transl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCharactersEmbeddingsOfCharacterisationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ η', IsEtaConj σ R.eta η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), Function.Bijective (lab (D := D) σ) → (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) → logHookSum i (lab σ) = logHookSum i id ∧ ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ResEta D η' 1 → (∀ ρ, HasInfExp D η' ρ (1 / 2)) → HypConj R i σ μ' η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → HypConj R i σ μ' η' → ∃ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → JUnif T R κw v₀ → Function.Injective ((R.FW i).j (sg0 D A))) := by
  first | exact @GlobalTheory.GalLift.conjChars_five | exact GlobalTheory.GalLift.conjChars_five | (intros; apply GlobalTheory.GalLift.conjChars_five <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalMirabolicWhittakerStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_semilocal_mirabolic_whittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ.1 p ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, F (g * k) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | (exact @GlobalTheory.JSW.MirSemi.kirillov_semilocal) | (exact GlobalTheory.JSW.MirSemi.kirillov_semilocal) | (intros; apply GlobalTheory.JSW.MirSemi.kirillov_semilocal  <;> assumption)
end

