module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0472

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarOnIsotypicPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RtSumScalar

section Main

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rtSum_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f)
    (f' : GAf L n → W) (hf' : f' ∈ S') (hfix : ∀ κ ∈ K, NG.rt L n κ f' = f') :
    ∑ γ ∈ R, NG.rt L n γ f' = c • f' := by
  classical
  obtain ⟨T, hT⟩ := hiso
  set f : S := T.symm ⟨f', hf'⟩ with hfdef
  have hTf : T f = ⟨f', hf'⟩ := T.apply_symm_apply _
  have hrt : ∀ h : GAf L n, ((T ⟨NG.rt L n h f, hS.stable h _ f.2⟩ : S') : GAf L n → W) = NG.rt L n h f' := by
    intro h
    have := hT h f ⟨_, hS.stable h _ f.2⟩ rfl
    rw [this, hTf]
  have hffix : ∀ κ ∈ K, NG.rt L n κ (f : GAf L n → W) = f := by
    intro κ hκ
    have h1 := hrt κ
    rw [hfix κ hκ] at h1
    have h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f := Subtype.ext (by rw [h1, hTf])
    exact congrArg Subtype.val (T.injective h2)
  have hcf := hc f f.2 hffix
  let σ : S := ∑ γ ∈ R, (⟨NG.rt L n γ f, hS.stable _ _ f.2⟩ : S)
  have hσ : (σ : GAf L n → W) = ∑ γ ∈ R, NG.rt L n γ f := by
    rw [Submodule.coe_sum]
  have hTσ : ((T σ : S') : GAf L n → W) = ∑ γ ∈ R, NG.rt L n γ f' := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun γ _ => hrt γ
  have key : σ = c • f := Subtype.ext (by rw [hσ, Submodule.coe_smul]; exact hcf)
  have h3 := congrArg (fun y => ((T y : S') : GAf L n → W)) key
  simp only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3
  exact h3

theorem rtSum_finset_sum {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S)
    (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f)
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    subst hf
    simp
  | insert a t ha ih =>
    intro hsub f hf hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      GlobalTheory.HeckeScalarAll.iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ K, NG.rt L n κ y = y := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _)] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ K, NG.rt L n κ z = z := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _), hyfix κ hκ] at e
        exact add_left_cancel e
      have e1 := rtSum_iso hS.1 haF.2 K R c hc y hy hyfix
      have e2 := ih htF z hz hzfix
      simp only [map_add (f := _), Finset.sum_add_distrib, e1, e2, smul_add]
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      exact ih htF f ((sup_le hle le_rfl) hf) hfix

end Main

theorem rtSum_isoTyp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f) → ∀ f ∈ NG.isoTyp ρ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  intro L _ _ _ n W _ _ ρ S hS K R c hc f hf hfix
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact rtSum_finset_sum hS K R c hc t ht f hft hfix

end GlobalTheory.RtSumScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMultisetAtInertPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.UbcString

theorem not_isSplitPl_of_inert {R : Ranks} (H : Host R) (w : HeightOneSpectrum (𝓞 H.E))
    (hw : Formalism.UG.IsInertAt H.F H.E (w.under (𝓞 H.F)) w) : ¬ IsSplitPl H w := by
  rintro ⟨x, hx, hy⟩
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv (H.conj : H.E ≃+* H.E)
  have hc : ∀ z : 𝓞 H.E, ((c z : 𝓞 H.E) : H.E) = H.conj (z : H.E) := fun z => rfl
  have hfix : ∀ a : 𝓞 H.F, c (algebraMap (𝓞 H.F) (𝓞 H.E) a) = algebraMap (𝓞 H.F) (𝓞 H.E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hc]
    have e : ((algebraMap (𝓞 H.F) (𝓞 H.E) a : 𝓞 H.E) : H.E) = ((a : H.F) : H.E) := rfl
    rw [e]
    exact (H.conjE_mem_hostF_iff _).1 (a : H.F).2
  have hle : w.asIdeal ≤ w.asIdeal.comap (c : 𝓞 H.E →+* 𝓞 H.E) := by
    unfold Formalism.UG.IsInertAt at hw
    rw [← hw, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c (algebraMap (𝓞 H.F) (𝓞 H.E) a) ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  exact hy (c x) (hc x) (hle hx)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)

theorem unr_of_foldr {w : PlE H} (a : A.LP w) (f : ℝ → ℝ) (L : List ℝ) (k : ℝ) (hk : k ∈ L)
    (h : A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w))) : A.unr a := by
  induction L with
  | nil => simp at hk
  | cons j L ih =>
    rw [List.foldr_cons, A.unr_sum] at h
    rcases List.mem_cons.1 hk with rfl | hk
    · exact (A.unr_tw a _).1 h.1
    · exact ih hk h.2

theorem frobEig_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (f : ℝ → ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) ∧
    A.frobEig (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) =
      (L.map fun k => (A.frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((f k : ℝ) : ℂ))).sum := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons k L ih =>
    have hk := (A.unr_tw a (f k)).2 ha
    refine ⟨(A.unr_sum _ _).2 ⟨hk, ih.1⟩, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [A.frobEig_sum _ _ hk ih.1, A.frobEig_tw a _ ha, ih.2]

theorem sum_singletons {ι : Type} (g : ι → ℂ) (L : List ι) :
    (L.map fun k => ({g k} : Multiset ℂ)).sum = ((L.map g : List ℂ) : Multiset ℂ) := by
  induction L with
  | nil => simp
  | cons k L ih => simp [ih]

end GlobalTheory.UbcString
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLocalComponentHasFixedVectorOfIsotypic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsoTypFixLoc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rt_rt (h h' : GAf L n) (f : GAf L n → W) : NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext g; simp [NG.rt, mul_assoc]

def LocEq (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → W)) : Prop :=
  ∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)

theorem le_iSup_range (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (hS : NG.IsIrrRep ρ S)
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  obtain ⟨hdec, hcomm, -⟩ := _root_.GlobalTheory.SplitAdelic.main L n s
  have hnt : Nontrivial τ.V := by
    haveI := τ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation τ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  let Good : (τ.V →ₗ[ℂ] (GAf L n → W)) → Prop := fun T => LocEq s τ i T ∧ ∀ u, T u ∈ S
  let Wd : Submodule ℂ (GAf L n → W) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS : Wd ≤ S := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 :=
    iSup_le fun T => le_iSup_of_le (⟨T.1, T.2.1⟩ : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}) le_rfl
  have htr : ∀ (T : τ.V →ₗ[ℂ] (GAf L n → W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => hS.1.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, rt_rt, rt_rt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, rt_rt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂
  have hT0 : Good T0 := ⟨hT0eq, hT0S⟩
  rcases hS.2.2 Wd ⟨hWdS.trans hS.1.le, hstab⟩ hWdS with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : τ.V)
    have hmem : T0 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T0, hT0⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hu (hT0inj (hmem.trans (map_zero T0).symm))
  · rw [← h0]
    exact hWdle

theorem isoTyp_le (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W))
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    NG.isoTyp ρ S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  refine sSup_le ?_
  rintro S' ⟨hS', E, hE⟩
  let T1 : τ.V →ₗ[ℂ] (GAf L n → W) := S'.subtype ∘ₗ (E : S →ₗ[ℂ] S') ∘ₗ LinearMap.codRestrict S T0 hT0S
  refine le_iSup_range ρ S' hS' s τ i T1 ?_ (fun a => (E _).2) ?_
  · intro a b hab
    apply hT0inj
    have := E.injective (Subtype.ext hab)
    exact congrArg Subtype.val this
  · intro x hx a
    exact hE x ⟨T0 a, hT0S a⟩ ⟨_, hT0S _⟩ (hT0eq x hx a)

end GlobalTheory.IsoTypFixLoc


open GlobalTheory.IsoTypFixLoc in
theorem GlobalTheory.IsoTypFixLoc.main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s τ → ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∃ a : τ.V, a ≠ 0 ∧ ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ)) a = a := by
  intro L _ _ _ n W _ _ ρ S hS s τ hloc i hi hiL f hf hf0 hfix
  classical
  obtain ⟨i', T0, hi', hi'L, hT0inj, hT0S, hT0eq⟩ := hloc
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i' i hi' hi hi'L hiL
  have hspan := isoTyp_le ρ S s τ i' T0 hT0inj hT0S hT0eq hf
  have hI := _root_.GlobalTheory.SplitAdelic.main L n s
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun hx hy => GlobalTheory.HeckeScalarSph.triv_mul hx hy
      one_mem' := GlobalTheory.HeckeScalarSph.triv_one
      inv_mem' := fun hx => GlobalTheory.HeckeScalarSph.triv_inv hx }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map i'.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, ⟨hx, e⟩, -⟩ := hI.2.2 (Matrix.GeneralLinearGroup.map i'.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map i'.toRingHom (s.loc n x) = h
    rw [e]
    exact Units.ext (Matrix.ext fun a b => i'.apply_symm_apply _)
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective τ.ρ φ hφ τ.irr
  let ρ' : Representation ℂ H (GAf L n → W) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [Submodule.mem_iSup_iff_exists_finset] at hspan
  obtain ⟨t, ht⟩ := hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => j.1.2 g.1 g.2 a⟩
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.HeckeScalarSph.locK n s.v).comap H.subtype
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk => hfix k.1 hk
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, hy0, fun κ hκ => ?_⟩
  exact (GlobalTheory.Parabolic.mem_fixed.1 hy) ⟨κ, hκ.2⟩ hκ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentMulEqSelfOfSupported
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.PlaceSupp

theorem tensCast_tmul_one {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (v : HeightOneSpectrum (𝓞 F1)) (α : FiniteAdeleRing (𝓞 F1) F1) (h1 : α v = 1) (h0 : ∀ v', v' ≠ v → α v' = 0) :
    ∃ (w : HeightOneSpectrum (𝓞 F2)) (α' : FiniteAdeleRing (𝓞 F2) F2),
      GlobalTheory.NJoin.tensCast h (α ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] α' ∧ α' w = 1 ∧ ∀ v', v' ≠ w → α' v' = 0 := by
  subst h
  exact ⟨v, α, rfl, h1, h0⟩


open Classical in
theorem equivFinsuppOfBasisRight_rTensor {K M N N' ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']
    (b : Module.Basis ι K M) (f : N →ₗ[K] N') (x : N ⊗[K] M) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b (LinearMap.rTensor M f x) i =
      f (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem rTensor_eq_zero {K M N P Q ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    (b : Module.Basis ι K M) (f : N →ₗ[K] P) (g : N →ₗ[K] Q) (hfg : ∀ n, f n = 0 → g n = 0 → n = 0)
    (x : N ⊗[K] M) (h1 : LinearMap.rTensor M f x = 0) (h2 : LinearMap.rTensor M g x = 0) : x = 0 := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisRight (M := N) b
  have hc : ∀ i, e x i = 0 := by
    intro i
    apply hfg
    · have := equivFinsuppOfBasisRight_rTensor b f x i
      rw [h1, map_zero, Finsupp.zero_apply] at this
      exact this.symm
    · have := equivFinsuppOfBasisRight_rTensor b g x i
      rw [h2, map_zero, Finsupp.zero_apply] at this
      exact this.symm
  have : e x = 0 := Finsupp.ext hc
  simpa using congrArg e.symm this

theorem AE_eq_zero (D : D7) (x : Formalism.L2.Theta.AE D) (h1 : Formalism.L2.Theta.infPart D x = 0)
    (h2 : Formalism.L2.Theta.finPart D x = 0) : x = 0 := by
  classical
  let b := Module.finBasis D.host.F D.host.E
  refine rTensor_eq_zero b (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F).toLinearMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F).toLinearMap
    (fun n hf hs => Prod.ext hf hs) x ?_ ?_
  · rw [← h1]; clear h1 h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  · rw [← h2]; clear h1 h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]


set_option maxHeartbeats 2000000 in
theorem idem_mul_eq_self : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) → ∀ a : Formalism.L2.Theta.AE D, Formalism.L2.Theta.infPart D a = 0 → (∀ v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), v' ≠ s.v → ReciprocityTheory.Aut.compAt D.host.E v' (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)) = 0) → (p.e + Formalism.L2.Theta.cA D p.e) * a = a := by
  intro D s hF p c hπ a ha0 haf
  obtain ⟨he2, hec, v, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := p.split
  rw [hsum]
  have hι1 : p.ι 1 = p.e := by
    have := p.ι_π 1
    rwa [map_one, mul_one] at this
  have hπe : p.π p.e = 1 := by rw [← hι1, p.π_ι]
  have hee : p.e * algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) = p.e := by
    rw [← hsum, mul_add, he2, hec, add_zero]
  have hfin : Formalism.L2.Theta.finPart D (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  obtain ⟨w, α', hT, hw1, hw0⟩ := tensCast_tmul_one hF v α hα1 hα0
  have hws : w = s.v := by
    by_contra hne
    have h0 : α' s.v = 0 := hw0 s.v (Ne.symm hne)
    have hz : p.π (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = 0 := by
      rw [hπ, hfin, hT]
      have : s.proj ((1 : D.host.E) ⊗ₜ α') = 0 := by
        rw [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        exact h0
      rw [this, map_zero]
    have := congrArg p.π hee
    rw [map_mul, hz, mul_zero, hπe] at this
    exact zero_ne_one this
  subst hws
  set x := algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) with hx
  suffices hb : x * a - a = 0 from sub_eq_zero.mp hb
  apply AE_eq_zero D
  · rw [RingHom.map_sub, RingHom.map_mul, ha0, mul_zero, sub_zero]
  · have key : GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (x * a - a)) = 0 := by
      apply GlobalTheory.AL_eq_zero_of_compAt
      intro v''
      rw [(Formalism.L2.Theta.finPart D).map_sub, (Formalism.L2.Theta.finPart D).map_mul, (GlobalTheory.NJoin.tensCast hF).map_sub,
        (GlobalTheory.NJoin.tensCast hF).map_mul, (compAt D.host.E v'').map_sub, (compAt D.host.E v'').map_mul, hfin, hT]
      by_cases hv : v'' = s.v
      · subst hv
        have : compAt D.host.E s.v ((1 : D.host.E) ⊗ₜ α') = 1 := by
          rw [compAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
          change (1 : D.host.E) ⊗ₜ (α' s.v) = 1
          rw [hw1]
          rfl
        rw [this, one_mul, sub_self]
      · rw [haf v'' hv, mul_zero, sub_zero]
    exact (GlobalTheory.NJoin.tensCast hF).map_eq_zero_iff.mp key

end GlobalTheory.PlaceSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnsGoodChartsMiddleSteps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue


set_option maxHeartbeats 4000000 in
theorem goodCharts_mid : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → i < B.R.m → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (Kc : Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hF i hi h1 h2
  have h2' : i + 1 ≤ B.R.m := h2
  obtain ⟨Ch, hCh, chOf, K, g, hK, hKb⟩ :=
    GlobalTheory.T.tupleChain_middleStage_charts_joined_member I hI hP l Z u a Q i hi (Ch0 i) (chOf0 i) (F.ch i h1 h2') h1 h2 hQ (hF.mid i h1 h2')
  obtain ⟨Kc, hR, hKc⟩ := _root_.GlobalTheory.TwU.AtTrue.charts_funKilled_one I hI hP l Z u a i hi (badQ (I.rec7 l Z) Q) Ch chOf K hK
    (fun β => (hKb β).2.1)
  exact ⟨Ch, hCh, chOf, Kc, hR, hKc⟩

end GlobalTheory.TwU.AtTrue
end

