module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0229
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.FrobeniusPowerCompatibility
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsHeckeModulesIsoAllPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicModularForms_heckeModules_iso_all_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep a.ρ S₂ → (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ (∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ (∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), (∀ f ∈ S₁, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f) ∧ (∀ f ∈ S₂, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f)) → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  first | exact @GlobalTheory.HeckeIso.main | exact GlobalTheory.HeckeIso.main | (intros; apply GlobalTheory.HeckeIso.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistableStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineParameter_twist_potentiallySemistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw c → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) → GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) = (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpChar (GlobalTheory.Pst.wdAt P ι Bw h hj c) := by
  first | exact @GlobalTheory.TwistParamAbove.wdAt_twist | exact GlobalTheory.TwistParamAbove.wdAt_twist | (intros; apply GlobalTheory.TwistParamAbove.wdAt_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL

namespace GlobalTheory.TheRecTransport

theorem exists_contra_equiv {H H' V V' : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (f : H →* H') (f' : H' →* H) (hf : Continuous f) (hf' : Continuous f') (hff : ∀ g, f (f' g) = g)
    (ρ : Representation ℂ H V) (ρ' : Representation ℂ H' V') (e : V ≃ₗ[ℂ] V')
    (he : ∀ g v, e (ρ g v) = ρ' (f g) (e v)) :
    ∃ d : smoothPart ρ.dual ≃ₗ[ℂ] smoothPart ρ'.dual, ∀ g l, d (contra ρ g l) = contra ρ' (f g) (d l) := by
  have key : ∀ g (l : Module.Dual ℂ V), e.symm.dualMap (ρ.dual g l) = ρ'.dual (f g) (e.symm.dualMap l) := by
    intro g l
    ext v
    obtain ⟨v, rfl⟩ := e.surjective v
    show l (ρ g⁻¹ (e.symm (e v))) = l (e.symm (ρ' (f g)⁻¹ (e v)))
    rw [← map_inv f, ← he, e.symm_apply_apply, e.symm_apply_apply]
  have hmap : (smoothPart ρ.dual).map (e.symm.dualMap : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V') = smoothPart ρ'.dual := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (((show IsOpen {g | ρ.dual g l = l} from hl).preimage hf').mem_nhds (by
          show ρ.dual (f' 1) l = l
          rw [map_one, map_one]; rfl)) fun g hg => ?_)
      have h1 : ρ.dual (f' g) l = l := hg
      show ρ'.dual g (e.symm.dualMap l) = e.symm.dualMap l
      rw [← hff g, ← key, h1]
    · intro l' hl'
      obtain ⟨l, rfl⟩ := e.symm.dualMap.surjective l'
      refine ⟨l, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (((show IsOpen {g | ρ'.dual g (e.symm.dualMap l) = e.symm.dualMap l} from hl').preimage hf).mem_nhds
          (by
            show ρ'.dual (f 1) _ = _
            rw [map_one, map_one]; rfl)) fun g hg => ?_), rfl⟩
      have h1 : ρ'.dual (f g) (e.symm.dualMap l) = e.symm.dualMap l := hg
      show ρ.dual g l = l
      apply e.symm.dualMap.injective
      rw [key, h1]
  exact ⟨e.symm.dualMap.ofSubmodules _ _ hmap, fun g l => Subtype.ext (key g l)⟩

section Rep

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem exists_of_repRel {i : k ≃+* k'} {n : ℕ} (π : IrrRep (GL (Fin n) k)) {x' : IrrGL (k := k')} (H : RepRel i (cls π) x') :
    ∃ (π' : IrrRep (GL (Fin n) k')) (e : π.V ≃ₗ[ℂ] π'.V), x' = cls π' ∧
      ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v) := by
  obtain ⟨m, π₀, π', e, h1, rfl, he⟩ := H
  obtain rfl : n = m := congrArg Sigma.fst h1
  obtain ⟨φ⟩ := (IrrGL.of_eq_of (π := π.ρ) (σ := π₀.ρ) (hs := π.smooth) (hi := π.irr) (hs' := π₀.smooth)
    (hi' := π₀.irr)).1 h1
  refine ⟨π', φ.toLinearEquiv.trans e, rfl, fun g v => ?_⟩
  have h2 : φ.toLinearEquiv (π.ρ g v) = π₀.ρ g (φ.toLinearEquiv v) := φ.toIntertwiningMap.isIntertwining _ _ g v
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h2, he]

theorem continuous_glMap (i : k ≃+* k') (hi : Continuous i) (n : ℕ) :
    Continuous (GeneralLinearGroup.map (n := Fin n) i.toRingHom) :=
  Continuous.units_map _ (continuous_matrix fun a b => hi.comp (continuous_id.matrix_elem a b))

theorem contra_transport (i : k ≃+* k') (hi : Continuous i) (hs : Continuous i.symm) {n : ℕ}
    (π τ : IrrRep (GL (Fin n) k)) (π' τ' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v))
    (u : τ.V ≃ₗ[ℂ] τ'.V) (hu : ∀ g v, u (τ.ρ g v) = τ'.ρ (GeneralLinearGroup.map i.toRingHom g) (u v))
    (φ : τ.ρ.Equiv (contra π.ρ)) : Nonempty (τ'.ρ.Equiv (contra π'.ρ)) := by
  obtain ⟨d, hd⟩ := exists_contra_equiv (GeneralLinearGroup.map (n := Fin n) i.toRingHom)
    (GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom) (continuous_glMap i hi n) (continuous_glMap i.symm hs n)
    (map_map_symm i) π.ρ π'.ρ e he
  refine ⟨.mk (u.symm.trans (φ.toLinearEquiv.trans d)) fun g => LinearMap.ext fun v => ?_⟩
  have h2 : ∀ g v, φ.toLinearEquiv (τ.ρ g v) = contra π.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  show d (φ.toLinearEquiv (u.symm (τ'.ρ g v))) = contra π'.ρ g (d (φ.toLinearEquiv (u.symm v)))
  rw [symm_rel i τ τ' u hu, h2, hd, map_map_symm]

theorem central_transport (i : k ≃+* k') {x : IrrGL (k := k)} {x' : IrrGL (k := k')} (H : RepRel i x x') {ω : kˣ →* ℂˣ}
    (hω : HasCentralChar x.rep ω) :
    HasCentralChar x'.rep (ω.comp (Units.map i.symm.toRingHom.toMonoidHom)) := by
  rw [← cls_rep x] at H
  obtain ⟨π', e, rfl, he⟩ := exists_of_repRel _ H
  intro z v
  let φ := equivRep π'
  have h2 : ∀ g v, φ.toLinearEquiv (π'.ρ g v) = π'.cl.rep.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective v
  obtain ⟨v, rfl⟩ := e.surjective v
  have hz : GeneralLinearGroup.scalar (Fin x.1) z = GeneralLinearGroup.map i.toRingHom
      (GeneralLinearGroup.scalar (Fin x.1) (Units.map i.symm.toRingHom.toMonoidHom z)) := by
    ext a b
    by_cases hab : a = b <;> simp [GeneralLinearGroup.scalar, Matrix.diagonal_apply, hab]
  show π'.cl.rep.ρ (GeneralLinearGroup.scalar (Fin x.1) z) (φ.toLinearEquiv (e v)) = _
  rw [← h2, hz, ← he, hω, map_smul, map_smul]
  rfl

end Rep

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem equiv_lpDual (P : PlaceIso A w A' w' φ j i) (S : WD h ≃ WD h') (hS : ∀ y y', WDRel φ y y' ↔ S y = y')
    (y : WD h) : S y.lpDual = (S y).lpDual := by
  obtain ⟨c, hc, hdegc, hq, hsm⟩ := _root_.GlobalTheory.WeilTransport.weil_equiv E Ω A w h E' Ω' A' w' h' φ j i P
  have hd1 : ∀ σ, deg (c.symm.toMonoidHom σ) = deg σ := fun σ => by
    have := hdegc (c.symm σ); simp only [MulEquiv.apply_symm_apply] at this
    simpa using this.symm
  have hs1 : ∀ (M : Type) [Monoid M] (g : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth g →
      GlobalTheory.WeilDeligne.IsSmooth (g.comp c.symm.toMonoidHom) := fun M _ g hg => by
    have e : (g.comp c.symm.toMonoidHom).comp c.toMonoidHom = g := by ext σ; simp
    have hg' : GlobalTheory.WeilDeligne.IsSmooth ((g.comp c.symm.toMonoidHom).comp c.toMonoidHom) := by rwa [e]
    exact (hsm M _).mpr hg'
  have hF : ∀ y, S y = GlobalTheory.WDTransport.pullWD c.symm.toMonoidHom hd1 hq.symm hs1 y := fun y => by
    obtain ⟨n, b, rfl⟩ := WD.exists_rep y
    refine (hS _ _).1 ⟨n, b, GlobalTheory.WDTransport.pull c.symm.toMonoidHom hd1 hq.symm hs1 b, rfl,
      (GlobalTheory.WDTransport.pullWD_mk _ _ _ _ b).symm, rfl, fun σ σ' hσ => ?_⟩
    rw [← (hc σ σ').mp hσ]
    simp [GlobalTheory.WDTransport.pull]
  obtain ⟨n, b, rfl⟩ := WD.exists_rep y
  rw [hF, hF, WD.lpDual_mk, GlobalTheory.WDTransport.pullWD_mk, GlobalTheory.WDTransport.pullWD_mk, WD.lpDual_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  show b.ρ.dual (c.symm.toMonoidHom σ) v = Representation.dual (b.ρ.comp c.symm.toMonoidHom) σ v
  simp only [Representation.dual_apply, MonoidHom.comp_apply, map_inv]

end GlobalTheory.TheRecTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Published UpperTheory.V.Af.Bc

namespace GlobalTheory.QuadNormRam

theorem not_unrAt_of_ramified : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M],
    Module.finrank K M = 2 → ∀ η : HChar K, IsNormChar M η → ∀ w : HeightOneSpectrum (𝓞 M),
    ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal → ¬ η.UnrAt (w.under (𝓞 K)) := by
  intro F E _ _ _ _ _ h2 η hη w hram hu
  have hGAR : GlobalTheory.Published.GlobalArtinReciprocity := GlobalTheory.globalArtinReciprocity_holds
  obtain ⟨hne, hpow, hsplit⟩ := hη
  rw [h2] at hpow
  let Ω := AlgebraicClosure E
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨artF, haF⟩ := hGAR F Ω
  obtain ⟨artE, haE⟩ := hGAR E Ω
  obtain ⟨δ, hδc, hL⟩ := haF.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η) (m := 2) (by norm_num) hpow)
  have hEig : ∀ v : HeightOneSpectrum (𝓞 F), η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := by
    intro v hu A hA
    refine ⟨fun s hs => (hL.unr_iff haF (Or.inr rfl) hA).2 hu s hs, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr haF (Or.inr rfl) hu hA hσ, inv_inv, ι.apply_symm_apply]
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, η.UnrAt (w.under (𝓞 F)) ∧
      ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f → η.val (w.under (𝓞 F)) ^ f = 1 :=
    ((GlobalTheory.QuadNormChar.tendsto_under (K := F) (K' := E)).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))).and hsplit
  have hres : δ.comp (UpperTheory.V.Af.Bc.res F Ω E) = 1 := by
    have hS := Filter.eventually_cofinite.1 hev
    refine GlobalTheory.FrobDense.eq_one_of_frob E Ω artE haE (Qbar 2)ˣ _
      (hδc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom F E Ω)) hS.toFinset fun w hw A hA σ hσ => ?_
    have hw' : η.UnrAt (w.under (𝓞 F)) ∧
        ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f → η.val (w.under (𝓞 F)) ^ f = 1 := by
      simpa using hw
    have hf := GlobalTheory.QuadNormChar.normV_under (K := F) w
    have h1 := ((UpperTheory.frobenius_power_compatibility F E Ω 2 ι w _ hf).2 δ _ (hEig _ hw'.1)) A hA
    have h3 := h1.2 σ hσ
    rw [← Units.val_pow_eq_pow_val, hw'.2 _ hf, Units.val_one, map_eq_one_iff _ ι.injective,
      Units.val_eq_one, map_inv, inv_eq_one] at h3
    exact h3

  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
  have hAv : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)

  have hmove : ∃ s ∈ Ine (F := F) A, ∃ e : E, s (algebraMap E Ω e) ≠ algebraMap E Ω e := by
    by_contra hfix
    push_neg at hfix
    have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
      let K := F
      let L := E
      let v := w.under (𝓞 F)
      have hv := hAv
      have hw := hA
      have hI := hfix
      have exists_mem_Ine_lift_int {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
          (A : ValuationSubring Ω) (M : Type) [Field M] [Algebra F M]
          [Algebra M Ω] [IsScalarTower F M Ω] [FiniteDimensional F M] [IsGalois F M] (τ : M ≃ₐ[F] M)
          (h : ∀ x : 𝓞 M, A.valuation (algebraMap M Ω (τ (x : M)) - algebraMap M Ω (x : M)) < 1) :
          ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω (τ x) := by
        open Pointwise in
          haveI : NumberField M := NumberField.of_module_finite F M
          haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
          haveI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩
          let σ₁ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
          have h₁ : ∀ x : M, σ₁ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => τ.liftNormal_commutes Ω x
          obtain ⟨g, hg⟩ := GlobalTheory.InertiaLift.exists_smul_eq (F := M) (A := A) (A' := σ₁⁻¹ • A) (by
            intro x
            rw [smul_valuation_lt_one_iff, inv_inv]
            change A.valuation (algebraMap M Ω (x : M)) < 1 ↔ A.valuation (σ₁ (algebraMap M Ω (x : M))) < 1
            rw [h₁]
            have hx := h x
            constructor
            · intro hl
              simpa using Valuation.map_add_lt _ hx hl
            · intro hl
              simpa using Valuation.map_sub_lt _ hl hx)
          let σ₂ : Ω ≃ₐ[F] Ω := σ₁ * g.restrictScalars F
          have h₂ : ∀ x : M, σ₂ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => by
            rw [← h₁]
            exact congrArg σ₁ (g.commutes x)
          have h₂' : ∀ y, A.valuation (σ₂ y) < 1 ↔ A.valuation y < 1 := fun y => by
            rw [← hg y, smul_valuation_lt_one_iff, inv_inv]
            rfl
          obtain ⟨k, hk, hk'⟩ := GlobalTheory.InertiaLift.exists_congr (F := M) (A := A) σ₂.toRingEquiv h₂' (by
            intro x
            change A.valuation (σ₂ (algebraMap M Ω (x : M)) - algebraMap M Ω (x : M)) < 1
            rw [h₂]
            exact h x)
          have hkinv : ∀ y, A.valuation (k.symm y) < 1 ↔ A.valuation y < 1 := fun y => by
            rw [← valuation_apply_lt_one_iff hk, k.apply_symm_apply]
          refine ⟨k.symm.restrictScalars F * σ₂, GlobalTheory.InertiaLift.mem_Ine_of_integral
            (GlobalTheory.InertiaLift.mem_Dec_of_lt fun y => ?_) fun b hb => ?_, fun x => ?_⟩
          · change A.valuation (k.symm (σ₂ y)) < 1 ↔ _
            rw [hkinv, h₂']
          · change A.valuation (k.symm (σ₂ b) - b) < 1
            rw [← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]
            exact hk' b hb
          · change k.symm (σ₂ (algebraMap M Ω x)) = _
            rw [h₂]
            exact k.symm.commutes (τ x)
      let primeUnder {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (M : Type) [Field M] [NumberField M] [Algebra M Ω] :
          Ideal (𝓞 M) :=
        Ideal.comap (((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A.toSubring fun x =>
          mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap M Ω).toIntAlgHom)) (IsLocalRing.maximalIdeal A)

      have mem_primeUnder {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (M : Type) [Field M] [NumberField M]
          [Algebra M Ω] (x : 𝓞 M) : x ∈ primeUnder A M ↔ A.valuation (algebraMap M Ω (x : M)) < 1 := by
        dsimp only [primeUnder]
        rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
        rfl
      let N : IntermediateField F Ω := IntermediateField.normalClosure F E Ω
      let M : Type := N
      haveI : FiniteDimensional F M := inferInstance
      haveI : NumberField M := NumberField.of_module_finite F M
      haveI : IsGalois F M := IsGalois.normalClosure F E Ω
      haveI : IsGalois E M := IsGalois.tower_top_of_isGalois F E M
      let P : Ideal (𝓞 M) := primeUnder A M
      haveI : P.IsPrime := Ideal.comap_isPrime _ _
      have hPv : P.under (𝓞 F) = v.asIdeal := by
        ext x
        rw [Ideal.mem_comap, mem_primeUnder, ← hv x]
        congr! 2
      have hPw : P.under (𝓞 E) = w.asIdeal := by
        ext x
        rw [Ideal.mem_comap, mem_primeUnder, ← hw x]
        congr! 2
      haveI hPv' : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
      haveI hPw' : P.LiesOver w.asIdeal := ⟨hPw.symm⟩
      haveI hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hPw, Ideal.under_under, hPv]⟩
      have hv0 := v.ne_bot
      have hw0 := w.ne_bot
      have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P
      have := v.isMaximal
      have := w.isMaximal
      have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hv0
      have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hw0
      have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[F] M) v.asIdeal P
      have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[E] M) w.asIdeal P
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[F] M)] at h1
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[E] M)] at h2
      have h3 := Ideal.ramificationIdx_tower (R := 𝓞 F) w.asIdeal P
    
      have hfix : ∀ τ ∈ P.toAddSubgroup.inertia (M ≃ₐ[F] M), ∀ x : E, τ (algebraMap E M x) = algebraMap E M x := by
        intro τ hτ x
        obtain ⟨σ, hσ, hστ⟩ := exists_mem_Ine_lift_int A M τ fun y => by
          have := (mem_primeUnder A M _).1 (hτ y)
          have e : ((τ • y - y : 𝓞 M) : M) = τ (y : M) - (y : M) := rfl
          rw [← map_sub, ← e]
          exact this
        apply (algebraMap M Ω).injective
        rw [← hστ, ← IsScalarTower.algebraMap_apply, hI σ hσ x]
      let f : P.toAddSubgroup.inertia (M ≃ₐ[F] M) → P.toAddSubgroup.inertia (M ≃ₐ[E] M) := fun τ =>
        ⟨{ (τ : M ≃ₐ[F] M).toRingEquiv with commutes' := hfix τ τ.2 }, fun y => τ.2 y⟩
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        apply AlgEquiv.ext
        intro y
        exact DFunLike.congr_fun (congrArg Subtype.val hab) y
      have h4 := Nat.card_le_card_of_injective f hf
      rw [h1, h2, h3] at h4
      have hpos : 0 < P.ramificationIdx (𝓞 F) := h1 ▸ Nat.card_pos
      rw [h3] at hpos
      have ha : w.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := by
        intro h0
        rw [h0] at hpos
        simp at hpos
      have hb : P.ramificationIdx (𝓞 E) ≠ 0 := by
        intro h0
        rw [h0] at hpos
        simp at hpos
      have hle : w.asIdeal.ramificationIdx (𝓞 F) ≤ 1 := by
        by_contra hc
        push_neg at hc
        have : 2 * P.ramificationIdx (𝓞 E) ≤ w.asIdeal.ramificationIdx (𝓞 F) * P.ramificationIdx (𝓞 E) :=
          Nat.mul_le_mul_right _ hc
        omega
      omega
    exact hram (Ideal.ramificationIdx_eq_one_iff.1 he)
  obtain ⟨s, hs, hsm⟩ := hmove
  have hδs : δ s = 1 := (hL.unr_iff haF (Or.inr rfl) hAv).2 hu s hs
  have fixes_or (σ : G F Ω) (hσ : ∃ e : E, σ (algebraMap E Ω e) ≠ algebraMap E Ω e) (τ : G F Ω) :
      τ ∈ (UpperTheory.V.Af.Bc.res F Ω E).range ∨ σ⁻¹ * τ ∈ (UpperTheory.V.Af.Bc.res F Ω E).range := by
    haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
    have hfix : ∀ ρ : G F Ω, (∀ e : E, ρ (algebraMap E Ω e) = algebraMap E Ω e) → ρ ∈ (UpperTheory.V.Af.Bc.res F Ω E).range :=
      fun ρ hρ => ⟨AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) hρ, AlgEquiv.ext fun _ => rfl⟩
    let f : G F Ω → (E →ₐ[F] Ω) := fun ρ => (ρ : Ω →ₐ[F] Ω).comp (IsScalarTower.toAlgHom F E Ω)
    have hf : ∀ ρ e, f ρ e = ρ (algebraMap E Ω e) := fun _ _ => rfl
    have hcard : Fintype.card (E →ₐ[F] Ω) = 2 := by rw [AlgHom.card, h2]
    obtain ⟨e₀, he₀⟩ := hσ
    have h01 : f 1 ≠ f σ := fun h => he₀ (by have := DFunLike.congr_fun h e₀; rw [hf, hf] at this; exact this.symm)
    by_cases h1 : f τ = f 1
    · left
      exact hfix τ fun e => by have := DFunLike.congr_fun h1 e; rw [hf, hf] at this; exact this
    · by_cases h2' : f τ = f σ
      · right
        refine hfix _ fun e => ?_
        have := DFunLike.congr_fun h2' e
        rw [hf, hf] at this
        rw [AlgEquiv.mul_apply, this]
        exact σ.symm_apply_apply _
      · exfalso
        have : 2 < Fintype.card (E →ₐ[F] Ω) :=
          Fintype.two_lt_card_iff.2 ⟨f 1, f σ, f τ, h01, Ne.symm h1, Ne.symm h2'⟩
        omega
  have hδ1 : δ = 1 := MonoidHom.ext fun τ => by
    rcases fixes_or s hsm τ with ⟨τ', rfl⟩ | ⟨τ', hτ'⟩
    · exact DFunLike.congr_fun hres τ'
    · have := DFunLike.congr_fun hres τ'
      rw [MonoidHom.comp_apply, hτ', map_mul, map_inv, hδs, inv_one, one_mul] at this
      exact this
  apply hne
  apply Subtype.ext
  refine MonoidHom.ext fun x => Units.ext ?_
  obtain ⟨τ, hτ⟩ := toAb_surjective (artF x)
  have := hL x τ hτ.symm
  rw [hδ1, infPow_zero, lPow_zero, inv_one, mul_one, mul_one, MonoidHom.one_apply, Units.val_one, eq_comm,
    map_eq_one_iff _ ι.symm.injective] at this
  exact this

end GlobalTheory.QuadNormRam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrOfConjRes
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open Polynomial

namespace GlobalTheory.RealGal.ConjUnr

theorem unr_of_conj_res : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Q : GlobalTheory.RealGal.QCM E Ω) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)), UpperTheory.V.Af.RepIso r (ρ.comp (UpperTheory.V.Af.Bc.res E Ω ↥Q.K)) → (∀ᶠ w : HeightOneSpectrum (𝓞 ↥Q.K) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := ↥Q.K) A, r s = 1) → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, ρ s = 1 := by
  intro E Ω _ _ _ _ _ Q l _ a ρ r hiso hr
  haveI : FiniteDimensional E Q.K := Module.finite_of_finrank_eq_succ Q.two
  have hS1 := GlobalTheory.InertiaAlmostAll.finite_ramified E Ω Q.K
  have hbad := Filter.eventually_cofinite.mp hr
  have hS2 := hbad.image (fun u : HeightOneSpectrum (𝓞 ↥Q.K) => u.under (𝓞 E))
  refine Filter.eventually_cofinite.mpr ((hS1.union hS2).subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨A, hA, s, hs, hρ⟩ := hw
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_image, not_or, not_exists, not_and] at hn
  obtain ⟨h1, h2⟩ := hn
  have hfix : s ∈ Q.K.fixingSubgroup := by
    by_contra hns
    exact h1 A hA (fun hle => hns (hle hs))
  obtain ⟨u, hu⟩ := GlobalTheory.LocLanglands.EpsUnique.exists_place hA ↥Q.K
  have hwu : u.under (𝓞 E) = w := ReciprocityTheory.Gal.eq_of_isPlaceOver (GlobalTheory.DelGlob.placeUnder_isPlaceOver ↥Q.K hu) hA
  have hgood : ∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ t ∈ Ine (F := ↥Q.K) A, r t = 1 := by
    by_contra hb
    exact h2 u hb hwu
  let t : G ↥Q.K Ω := IntermediateField.fixingSubgroupEquiv Q.K ⟨s, hfix⟩
  have hts : UpperTheory.V.Af.Bc.res E Ω ↥Q.K t = s := AlgEquiv.ext fun _ => rfl
  have ht : t ∈ Ine (F := ↥Q.K) A := ⟨hs.1, hs.2⟩
  obtain ⟨g, hg⟩ := hiso
  apply hρ
  have := hg t
  rw [MonoidHom.comp_apply, hts, hgood A hu t ht] at this
  rw [this]; simp

end GlobalTheory.RealGal.ConjUnr
end

