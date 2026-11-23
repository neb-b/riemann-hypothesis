module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GraphOfFixedGraph
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfEqualAnnihilators
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0219
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0196
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0130
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsHeckeModulesIsoAllPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeIso

section Abstract

variable {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : G →* Module.End ℂ V} {Gv Gc : ι → Subgroup G}
  {J : Subgroup G}

theorem graph_of_local' (H : PlaceSys Gv Gc J) (horb : ∀ x, ((fun k => ρ k x) '' (J : Set G)).Finite)
    {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂) (n₁ : fixIn ρ J S₁ ≠ ⊥) (n₂ : fixIn ρ J S₂ ≠ ⊥)
    (hfd : FiniteDimensional ℂ (fixIn ρ J S₁)) (hloc : ∀ v, ∃ X, IsGraph ρ (Gv v) S₁ S₂ X) :
    ∃ W, IsGraph ρ ⊤ S₁ S₂ W := by
  obtain ⟨X, hX0, hXm, hX, i₁, i₂⟩ := _root_.GlobalTheory.CommDet.stable_graph V ι (fun v => locAlg ρ (Gv v) (Gc v) ⊓ fixAlg ρ J)
    (fixIn ρ J S₁) (fixIn ρ J S₂) hfd n₁ n₂
    (fun v c hc x hx => ⟨locAlg_mem hc.1 h₁.stab hx.1, hc.2 x hx.2⟩)
    (fun v c hc x hx => ⟨locAlg_mem hc.1 h₂.stab hx.1, hc.2 x hx.2⟩)
    (fun v w hvw c hc d hd => ⟨fun x _ => locAlg_comm (H.le v w hvw) hc.1 hd.1 x,
      fun x _ => locAlg_comm (H.le v w hvw) hc.1 hd.1 x⟩)
    (fun v c hc => by
      obtain ⟨P, hP⟩ := exists_avg ρ (Gv v ⊓ J) fun x => (horb x).subset (Set.image_mono fun k hk => hk.2)
      obtain ⟨Q, hQ⟩ := exists_avg ρ (Gc v ⊓ J) fun x => (horb x).subset (Set.image_mono fun k hk => hk.2)
      obtain ⟨X, hX⟩ := hloc v
      exact ⟨ann_transfer (H.comm v) (H.dec v) (H.decJ v) hP hQ h₁ h₂ n₁ hX hc.1,
        ann_transfer (H.comm v) (H.dec v) (H.decJ v) hP hQ h₂ h₁ n₂ hX.swap hc.1⟩)
    (fun Y hY hst => fixIn_simple H horb h₁ Y hY hst) (fun Y hY hst => fixIn_simple H horb h₂ Y hY hst)
  exact graph_of_fixed_graph H horb h₁ h₂ n₁ n₂ X hX0 hXm hX i₁ i₂

theorem graph_of_local (H : PlaceSys Gv Gc J) {S₁ S₂ : Submodule ℂ V} (h₁ : Irr ρ S₁) (h₂ : Irr ρ S₂)
    (horb : ∀ x ∈ S₁ ⊔ S₂, ((fun k => ρ k x) '' (J : Set G)).Finite)
    (n₁ : fixIn ρ J S₁ ≠ ⊥) (n₂ : fixIn ρ J S₂ ≠ ⊥)
    (hfd : FiniteDimensional ℂ (fixIn ρ J S₁)) (hloc : ∀ v, ∃ X, IsGraph ρ (Gv v) S₁ S₂ X) :
    ∃ W, IsGraph ρ ⊤ S₁ S₂ W := by
  have hne : ∀ S ≤ S₁ ⊔ S₂, fixIn ρ J S ≠ ⊥ →
      fixIn (res ρ _ (sup_stab h₁ h₂)) J (S.comap (S₁ ⊔ S₂).subtype) ≠ ⊥ := by
    intro S hS h
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact (Submodule.ne_bot_iff _).2 ⟨⟨f, hS hf.1⟩, ⟨hf.1, fun k hk => Subtype.ext (hf.2 k hk)⟩,
      fun e => hf0 (congrArg Subtype.val e)⟩
  obtain ⟨W, hW⟩ := graph_of_local' (ρ := res ρ _ (sup_stab h₁ h₂)) H (orbit_res horb) (h₁.res le_sup_left)
    (h₂.res le_sup_right) (hne _ le_sup_left n₁) (hne _ le_sup_right n₂)
    (FiniteDimensional.of_injective
      (((S₁ ⊔ S₂).subtype.comp (fixIn (res ρ _ (sup_stab h₁ h₂)) J (S₁.comap (S₁ ⊔ S₂).subtype)).subtype).codRestrict
        (fixIn ρ J S₁) (fun f => ⟨f.2.1, fun k hk => congrArg Subtype.val (f.2.2 k hk)⟩))
      (fun a b e => by
        have e' := congrArg Subtype.val e
        exact Subtype.ext (Subtype.ext e')))
    (fun v => by
      obtain ⟨X, hX⟩ := hloc v
      exact ⟨_, hX.res le_sup_left le_sup_right⟩)
  exact ⟨_, hW.of_res⟩

end Abstract

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

def rtRep (W : Type) [AddCommGroup W] [Module ℂ W] : GAf L n →* Module.End ℂ (GAf L n → W) where
  toFun g := NG.rt L n g
  map_one' := LinearMap.ext fun φ => funext fun x => by
    show φ (x * 1) = φ x
    rw [mul_one]
  map_mul' g g' := LinearMap.ext fun φ => funext fun x => by
    show φ (x * (g * g')) = φ (x * g * g')
    rw [mul_assoc]

def Gaway (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v}ᶜ x}
  mul_mem' := fun hx hy => GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
  one_mem' := GlobalTheory.InertSph.trivOutside_one _
  inv_mem' := fun hx => GlobalTheory.SatInd.CosetFin.trivOutside_inv hx

theorem placeSys {N : ℕ} (hN : 0 < N) :
    PlaceSys (GlobalTheory.InertSph.Gv L n) (Gaway L n) (GlobalTheory.IsotOrth.congSub L n N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun v x hx y hy => (GlobalTheory.InertSph.commute_of_trivOutside v x y hx hy).eq
  · intro v w hvw x hx u hu
    apply hx u
    have : u = v := by simpa using hu
    subst this
    simpa using hvw
  · intro v g
    obtain ⟨x, y, hx, hy, e⟩ := _root_.GlobalTheory.PlaceDecomp.decomp L n v g
    exact ⟨x, hx, y, hy, e⟩
  · intro v k hk
    obtain ⟨x, y, hx, hy, cx, cy, e⟩ := _root_.GlobalTheory.CongSplitBoth.split_cong_at_place L n N v k hk
    exact ⟨x, ⟨hx, cx⟩, y, ⟨hy, cy⟩, e⟩
  · exact fun p h1 h2 => _root_.GlobalTheory.PlaceInd.induction_places L n N hN p h1 (fun v x y hx hy => h2 v x hx y hy)

variable {L n}

theorem irr_of {a : NG.AlgWt L n} {S : Submodule ℂ (GAf L n → a.W)} (h : NG.IsIrrRep a.ρ S) :
    Irr (rtRep L n a.W) S :=
  ⟨h.1.stable, fun T hT hst => h.2.2 T ⟨hT.trans h.1.le, hst⟩ hT⟩

theorem orbit_fin {a : NG.AlgWt L n} {S₁ S₂ : Submodule ℂ (GAf L n → a.W)} (h₁ : NG.IsIrrRep a.ρ S₁)
    (h₂ : NG.IsIrrRep a.ρ S₂) {K : Subgroup (GAf L n)} (hK : K ≤ Umax L n) :
    ∀ x ∈ S₁ ⊔ S₂, ((fun k => rtRep L n a.W k x) '' (K : Set (GAf L n))).Finite := by
  intro x hx
  obtain ⟨N, hN, hx⟩ := (sup_le h₁.1.le h₂.1.le hx).2
  exact (GlobalTheory.IsotOrth.orbit_finite (rtRep L n a.W) hN x fun κ hκ => funext fun g => hx κ hκ g).subset
    (Set.image_mono hK)

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep a.ρ S₂ → (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ (∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ (∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), (∀ f ∈ S₁, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f) ∧ (∀ f ∈ S₂, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f)) → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  intro L _ _ _ n a S₁ S₂ h₁ h₂ hsplit hinert N hN hf
  refine _root_.GlobalTheory.HeckeIsoMap.isoMap L n a S₁ S₂ h₁ ?_ N hN hf
  obtain ⟨g₁, hg₁, hg₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁.2.1
  obtain ⟨g₂, hg₂, hg₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂.2.1
  obtain ⟨M₁, hM₁, e₁⟩ := (h₁.1.le hg₁).2
  obtain ⟨M₂, hM₂, e₂⟩ := (h₂.1.le hg₂).2
  have hM : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have H := placeSys L n hM
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  obtain ⟨W, hW⟩ := graph_of_local H (irr_of h₁) (irr_of h₂) (orbit_fin h₁ h₂ fun k hk => hk.1)
    ((Submodule.ne_bot_iff _).2 ⟨g₁, ⟨hg₁, fun k hk => funext fun g => e₁ k (NG.Cong.of_mul_left L n hk) g⟩, hg₁0⟩)
    ((Submodule.ne_bot_iff _).2 ⟨g₂, ⟨hg₂, fun k hk => funext fun g => e₂ k (NG.Cong.of_mul_right L n hk) g⟩, hg₂0⟩)
    (by
      have := GlobalTheory.AlgFormsFin.fixedForms_finite L n a.ρ (_root_.GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n) hM
      refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n a.ρ (M₁ * M₂)) ?_
      rintro f ⟨hfS, hfU⟩
      exact ⟨(h₁.1.le hfS).1, fun κ hκ g => congrFun (hfU κ hκ) g⟩)
    (fun v => by
      by_cases hv : ∃ s : SplitPlace L, s.v = v
      · obtain ⟨s, rfl⟩ := hv
        obtain ⟨σ₁, σ₂, l₁, l₂, he⟩ := hsplit s
        obtain ⟨X, x1, x2, x3, x4, x5⟩ := _root_.GlobalTheory.LocSplitGraph.main L n a S₁ S₂ s σ₁ σ₂ l₁ l₂ he
        exact ⟨X, x1, x2, x3, x4, x5⟩
      · obtain ⟨w, Dv, α, -, ⟨f₁, hf₁, n₁, k₁⟩, ⟨f₂, hf₂, n₂, k₂⟩, hH⟩ := hinert v fun s hs => hv ⟨s, hs⟩
        refine graph_of_hecke (K := GlobalTheory.InertSph.Kv L n v) (H.comm v) (H.dec v) inf_le_right (irr_of h₁) (irr_of h₂)
          (orbit_fin h₁ h₂ inf_le_left) hf₁ hf₂ n₁ n₂ (fun k hk => k₁ k hk.1 hk.2) (fun k hk => k₂ k hk.1 hk.2)
          fun x hx => ?_
        obtain ⟨R, h, hR, hh, hA⟩ := _root_.GlobalTheory.InertDCOp.dcOp_eq_heckeFunI L n v w Dv (_root_.GlobalTheory.inertLoc_mem_GU L n v w Dv) (_root_.GlobalTheory.InertStdLat.loc_mem_KU L n v w Dv)
          (_root_.GlobalTheory.InertLift.exists_trivOutside_loc_eq L n v w Dv) (_root_.GlobalTheory.InertLocInj.loc_injective L n v w Dv) x hx
        have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
            (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
          fun κ hκ _ => ⟨_root_.GlobalTheory.inertLoc_mem_GU L n v w Dv κ, _root_.GlobalTheory.InertStdLat.loc_mem_KU L n v w Dv κ hκ _⟩
        have hKv : ∀ κ : GAf L n, TrivOutside {v} κ → (κ ∈ GlobalTheory.InertSph.Kv L n v ↔ κ ∈ Umax L n) :=
          fun κ hκ => ⟨fun h => h.1, fun h => ⟨h, hκ⟩⟩
        obtain ⟨γ, ⟨hγ, -⟩, -⟩ := hR.2 x ⟨1, one_mem _, 1, one_mem _, by simp⟩
        refine ⟨R, Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α, ⟨γ, hγ⟩, hR.1, ?_, ?_⟩
        · refine (hA a.W f₁ k₁).trans ?_
          rw [_root_.GlobalTheory.InertLevel.heckeFunI_level_indep L n v w Dv hK (Umax L n) _ (fun _ _ => Iff.rfl) hKv a.W h hh.1 f₁ k₁]
          exact (hH _ hKv h hh).1 f₁ hf₁ fun k hk => k₁ k hk.1 hk.2
        · refine (hA a.W f₂ k₂).trans ?_
          rw [_root_.GlobalTheory.InertLevel.heckeFunI_level_indep L n v w Dv hK (Umax L n) _ (fun _ _ => Iff.rfl) hKv a.W h hh.1 f₂ k₂]
          exact (hH _ hKv h hh).2 f₂ hf₂ fun k hk => k₂ k hk.1 hk.2)
  exact _root_.GlobalTheory.isoRep_of_stable_graph L n a.ρ a.ρ S₁ S₂ W h₁ h₂ hW.mem (fun h w hw => hW.stab h trivial w hw) hW.inj₁ hW.inj₂ hW.ne

end GlobalTheory.HeckeIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockTypeVectorIrreducibleSplitsAsProduct
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.BlockSplitProof

private theorem is_smooth_char_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : IsSmoothChar χ⁻¹ := by
  have hk : (χ⁻¹).ker = χ.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  unfold IsSmoothChar
  rw [hk]
  exact h

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], BlockSplit k := by
  intro hBZ hGL hUP hDZ k _ _ _ _ r t χ π v hχ hT hv hvec

  obtain ⟨s, d, σ, hsupp, hle⟩ := _root_.GlobalTheory.BlockSupp.main hBZ hGL hUP hDZ k r t χ π v hχ hT hv hvec
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inr ⟨s, d, σ, hsupp, hlt⟩
  ·
    obtain ⟨π₁, π₂, hE, hns⟩ := _root_.GlobalTheory.BlockSplitProd.main hBZ hGL hUP k r t χ π s d σ hχ hsupp heq.symm
    have hsph := _root_.GlobalTheory.BlockSph.sph_of_isBlockVec hBZ hGL hDZ k r t χ π π₁ π₂ v hχ hT hns hE hv hvec
    have hχi : IsSmoothChar χ⁻¹ := is_smooth_char_inv hχ
    refine Or.inl ⟨π₁, GlobalTheory.SplitPairLift.twistIrr π₂ hχi, hsph, ?_⟩
    have h2 := GlobalTheory.SplitPairLift.twist_twist_inv π₂ χ⁻¹
    rw [inv_inv] at h2
    show Nonempty (π.π.Equiv (prod₂ π₁.π (twist (twist π₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
    rw [h2]
    exact hE

end GlobalTheory.BlockSplitProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistable
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwistParamAbove

theorem wdPst_twist_one_field : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (m : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1), IsPst P (Bw.repE L s) → IsPst P (Bw.repE L m) → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) → wdPst P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) = (wdPst P ι Bw h hj (Bw.repE L s)).lpChar (wdPst P ι Bw h hj (Bw.repE L m)) := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj L a s m hs hm ht
  haveI := hs.finite
  haveI := hm.finite
  haveI := ht.finite
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.dpstLetter_twist_tensor_equiv P AI hT ι Bw h hj s m hs hm ht
  have f1 := isFrobSS_wdRep P ι Bw h hj (Bw.repE L s)
  have f2 := isFrobSS_wdRep P ι Bw h hj (Bw.repE L m)
  have f3 := isFrobSS_wdRep P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))
  have f12 := _root_.GlobalTheory.WeilDeligne.IsFrobSS.tensor f1 f2
  have hI := IsFrobSS.iso f12 f3 e (fun g v => he1 g v) (fun v => he2 v)
  rw [wdPst_of_isPst ι Bw h hj hs, wdPst_of_isPst ι Bw h hj hm, wdPst_of_isPst ι Bw h hj ht, WD.lpChar_mk]
  exact (WD.sound hI).symm

theorem wdAt_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw c → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) → GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) = (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpChar (GlobalTheory.Pst.wdAt P ι Bw h hj c) := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r c _ _ hr hc ht
  obtain ⟨L₁, r₁, hm₁, hp₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hr
  obtain ⟨L₂, c₂, hm₂, hp₂, e₂⟩ := wdAt_of_isPstAt ι Bw h hj hc
  obtain ⟨L₃, t₃, hm₃, hp₃, e₃⟩ := wdAt_of_isPstAt ι Bw h hj ht
  have l₁ : L₁.1 ≤ (supExt (supExt L₁ L₂) L₃).1 := le_sup_left.trans le_sup_left
  have l₂ : L₂.1 ≤ (supExt (supExt L₁ L₂) L₃).1 := le_sup_right.trans le_sup_left
  have l₃ : L₃.1 ≤ (supExt (supExt L₁ L₂) L₃).1 := le_sup_right
  have hmt := isModel_twist (hm₁.enlarge l₁) (hm₂.enlarge l₂)
  have hu := IsModel.unique Bw (r := Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) (hm₃.enlarge l₃) hmt
  have q₃ := GlobalTheory.PstExt.isPst_enlarge P Bw l₃ t₃ hp₃
  rw [hu] at q₃
  rw [e₁, e₂, e₃, ← GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι Bw h hj l₃ t₃ hp₃, hu, ← GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι Bw h hj l₁ r₁ hp₁, ← GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι Bw h hj l₂ c₂ hp₂]
  exact wdPst_twist_one_field P AI hT ι Bw h hj _ _ (GlobalTheory.PstExt.isPst_enlarge P Bw l₁ r₁ hp₁)
    (GlobalTheory.PstExt.isPst_enlarge P Bw l₂ c₂ hp₂) q₃

end GlobalTheory.TwistParamAbove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearIndependentSimulEigen
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong

theorem linearIndependent_simulEigen {J V : Type} [AddCommGroup V] [Module ℂ V] (T : J → V →ₗ[ℂ] V)
    (S : Set (J → ℂ)) (v : S → V) (hv : ∀ χ, v χ ≠ 0)
    (hT : ∀ (χ : S) j, T j (v χ) = (χ : J → ℂ) j • v χ) : LinearIndependent ℂ v := by
  first
  | exact @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | (apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors ..)

def opLin {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) :
    V →ₗ[ℂ] V :=
  f.sum fun g c => c • ρ g

theorem opLin_apply {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ)
    (v : V) : opLin ρ f v = opOf ρ f v := by
  simp [opLin, opOf, Finsupp.sum, LinearMap.sum_apply]

theorem eq_zero_of_finU {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : UA E n → ℂ}
    (hφ : IsAutFormU φ) (h0 : ∀ g ∈ finU (E := E) (n := n), φ g = 0) : φ = 0 := by
  refine Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hφ.cont continuous_const ?_
  rintro x ⟨γ, hγ, g, hg, rfl⟩
  simp only [Pi.zero_apply]
  rw [hφ.left γ hγ g]
  exact h0 g hg

theorem finU_holds : FinU := by
  intro E _ _ _ l _ ι a _ w₀ K _ lam J t η ht hact U hU
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  have hφ : IsAutFormU φ := hU.aut.aut φ hφU
  have heig : ∀ j, opOf (RU E a) (t j) φ = η U j • φ := fun j => hact U hU.aut φ hφU hφK j
  obtain ⟨g₀, hg₀, hφg₀⟩ : ∃ g ∈ finU (E := E) (n := a), φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (eq_zero_of_finU hφ h)
  choose φ' hφ' hφ'eq using fun σ : ℂ ≃+* ℂ => exists_conj_isAutFormU E a σ φ hφ
  obtain ⟨M, hMfin, hM⟩ := GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional E a φ hφ
  have heig' : ∀ σ j, opOf (RU E a) (t j) (φ' σ) = σ (η U j) • φ' σ := fun σ j =>
    GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism E a σ (t j) (ht j) φ (φ' σ) (η U j) hφ (hφ' σ) (hφ'eq σ) (heig j)
  have hne : ∀ σ, φ' σ ≠ 0 := by
    intro σ h
    have e := hφ'eq σ g₀ hg₀
    rw [h, Pi.zero_apply, eq_comm, map_eq_zero_iff σ σ.injective] at e
    exact hφg₀ e
  have hfin : (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j)).Finite := by
    set S := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j) with hS
    have hch : ∀ χ : S, ∃ σ : ℂ ≃+* ℂ, (fun j => σ (η U j)) = (χ : J → ℂ) := fun χ => χ.2
    choose sel hsel using hch
    let v : S → (UA E a → ℂ) := fun χ => φ' (sel χ)
    have hli : LinearIndependent ℂ v := by
      refine linearIndependent_simulEigen (fun j => opLin (RU E a) (t j)) S v (fun χ => hne _) ?_
      intro χ j
      rw [opLin_apply, heig', ← hsel χ]
    let v' : S → M := fun χ => ⟨v χ, hM (sel χ) (φ' (sel χ)) (hφ' _) (hφ'eq _)⟩
    have hli' : LinearIndependent ℂ v' := LinearIndependent.of_comp M.subtype hli
    have : Finite S := hli'.finite
    exact Set.toFinite S
  obtain ⟨L, hL, hLmem⟩ := _root_.GlobalTheory.orbit_finite_mem_finite_ext l ι J (η U) hfin
  exact ⟨⟨L, hL⟩, hLmem⟩

end GlobalTheory.Cong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointOfConditions
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowPointLoc

theorem continuous_of_adic {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A ≃+* B) :
    Continuous f := by
  have hm : Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have := hu.map (f.symm : B →+* A)
    simpa using this
  refine continuous_of_continuousAt_zero (f : A →+ B) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := ((isAdic_iff.1 hB).2 s hs)
  have hopen := (isAdic_iff.1 hA).1 n
  refine Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds (Ideal.zero_mem _)) ?_)
  intro x hx
  apply hn
  have h1 : f x ∈ Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

end GlobalTheory.RowPointLoc
end

