module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalRingCardinality.HostCls
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfReps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.ClassPet

noncomputable section

namespace GlobalTheory.FormInner

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_reps (J : Subgroup (GAf L n)) (S : Finset (GAf L n))
    (hS : ∀ g : GAf L n, ∃ s ∈ S, ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * s * κ) :
    ∃ T, IsClassReps J T := by
  classical
  let q : GAf L n → DoubleCoset.Quotient (GQ L n : Set (GAf L n)) (J : Set (GAf L n)) := DoubleCoset.mk (GQ L n) J
  have hq : ∀ a b, q a = q b ↔ ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ b = (γ : GAf L n) * a * κ := fun a b => by
    rw [DoubleCoset.eq]
    exact ⟨fun ⟨h, hh, k, hk, e⟩ => ⟨⟨h, hh⟩, k, hk, e⟩, fun ⟨h, k, hk, e⟩ => ⟨h, h.2, k, hk, e⟩⟩
  refine ⟨S.image fun s => (q s).out, fun g => ?_⟩
  obtain ⟨s, hs, e⟩ := hS g
  have e1 : q s = q g := (hq _ _).2 e
  have ho : ∀ c : DoubleCoset.Quotient (GQ L n : Set (GAf L n)) (J : Set (GAf L n)), q c.out = c := fun c => Quotient.out_eq c
  refine ⟨(q s).out, ⟨Finset.mem_image_of_mem _ hs, (hq _ _).1 ((ho _).trans e1)⟩, ?_⟩
  rintro t ⟨ht, h⟩
  obtain ⟨s', -, rfl⟩ := Finset.mem_image.1 ht
  have := (hq _ _).2 h
  rw [ho] at this
  rw [this, e1]

theorem relIndex_ne_zero_of_reps {J K : Subgroup (GAf L n)} (hJ : IsBounded J) (hle : K ≤ J) {T : Finset (GAf L n)}
    (hT : IsClassReps K T) : K.relIndex J ≠ 0 := by
  classical
  have hfin : ∀ t : GAf L n, {γ : GQ L n | (γ : GAf L n) * t ∈ J}.Finite := by
    intro t
    rcases Set.eq_empty_or_nonempty {γ : GQ L n | (γ : GAf L n) * t ∈ J} with h | ⟨γ₀, h₀⟩
    · rw [h]; exact Set.finite_empty
    · haveI := GlobalTheory.StabFin.finite_conj_mem L n J hJ 1
      refine Set.Finite.subset (Set.finite_range fun δ : {γ : GQ L n // (1 : GAf L n)⁻¹ * (γ : GAf L n) * 1 ∈ J} => δ.1 * γ₀) ?_
      intro γ hγ
      refine ⟨⟨γ * γ₀⁻¹, ?_⟩, by simp⟩
      have := J.mul_mem hγ (J.inv_mem h₀)
      simpa [mul_assoc] using this
  refine relIndex_ne_zero_of_cover (T.biUnion fun t => (hfin t).toFinset.image fun γ : GQ L n => (γ : GAf L n) * t) (fun κ hκ => ?_) hle
  obtain ⟨t, ⟨ht, γ, k, hk, e⟩, -⟩ := hT κ
  refine ⟨γ * t, Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).2 ?_)⟩, by rw [e, inv_mul_cancel_left]; exact hk⟩
  have := J.mul_mem hκ (J.inv_mem (hle hk))
  rw [e] at this
  simpa using this

theorem form_inv {a : NG.AlgWt L n} (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) {J : Subgroup (GAf L n)} (hJ : IsBounded J) {χ : J →* ℂˣ}
    {f f' : GAf L n → a.W} (hf : f ∈ NG.TypeSp a.ρ J χ) (hf' : f' ∈ NG.TypeSp a.ρ J χ) :
    ∀ κ ∈ J, ∀ g, β (f (g * κ)) (f' (g * κ)) = β (f g) (f' g) := by
  intro κ hκ g
  have e : ∀ k : J, f (g * k) = ((χ k : ℂˣ) : ℂ) • f g := fun k => congrFun (hf.2 k) g
  have e' : f' (g * κ) = ((χ ⟨κ, hκ⟩ : ℂˣ) : ℂ) • f' g := congrFun (hf'.2 ⟨κ, hκ⟩) g
  rw [e ⟨κ, hκ⟩, e']
  by_cases h0 : f g = 0
  · simp [h0]
  obtain ⟨N, hN, hinv⟩ := hf.1.2
  obtain ⟨F, hF⟩ := (GlobalTheory.CongIndex.finite_index_conj L n J hJ 1 N hN).2.1
  have hle : J ⊓ congSub L n N ≤ J := inf_le_left
  have hne : (J ⊓ congSub L n N).relIndex J ≠ 0 := by
    classical
    have : ∀ f₀ ∈ F, ∃ u, (∃ κ ∈ J, f₀⁻¹ * κ ∈ congSub L n N) → u ∈ J ∧ f₀⁻¹ * u ∈ congSub L n N := fun f₀ _ => by
      by_cases h : ∃ κ ∈ J, f₀⁻¹ * κ ∈ congSub L n N
      · obtain ⟨u, hu⟩ := h
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' h⟩
    choose! u hu using this
    refine relIndex_ne_zero_of_cover (F.image u) (fun κ hκ => ?_) hle
    obtain ⟨f₀, h₀, h₁⟩ := hF κ hκ
    obtain ⟨h2, h3⟩ := hu f₀ h₀ ⟨κ, hκ, h₁⟩
    refine ⟨u f₀, Finset.mem_image_of_mem _ h₀, J.mul_mem (J.inv_mem h2) hκ, ?_⟩
    have := (congSub L n N).mul_mem ((congSub L n N).inv_mem h3) h₁
    simpa [mul_assoc] using this
  have hn := norm_eq_one_of_relIndex hle hne χ (fun k hk => by
    have h1 := e ⟨k, hle hk⟩
    rw [hinv k hk.2 g] at h1
    have h2 : (((χ ⟨k, hle hk⟩ : ℂˣ) : ℂ) - 1) • f g = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact Units.ext (sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right h0))) ⟨κ, hκ⟩
  rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, Complex.conj_mul', hn]
  simp

theorem classSum_index {a : NG.AlgWt L n} {β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ} (hβ : IsInvForm a β) {J K : Subgroup (GAf L n)}
    {T T' : Finset (GAf L n)} (hJ : IsBounded J) (hle : K ≤ J) (hne : K.relIndex J ≠ 0) (hT : IsClassReps J T)
    (hT' : IsClassReps K T') {χ : J →* ℂˣ} {f f' : GAf L n → a.W} (hf : f ∈ NG.TypeSp a.ρ J χ) (hf' : f' ∈ NG.TypeSp a.ρ J χ) :
    classSum a β K T' f f' = (K.relIndex J : ℂ) * classSum a β J T f f' := by
  obtain ⟨F, h1, h2, h3⟩ := exists_cosetReps hle hne
  have hi := form_inv β hJ hf hf'
  rw [GlobalTheory.ClassRefine.classSum_smaller_level L n a β hβ J K T T' hJ hle hne hT hT' f hf.1 f' hf'.1
    (fun κ hκ => hi κ (hle hκ)) F h1 h2, classSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_congr rfl fun u hu => hi u (h1 u hu) t, Finset.sum_const, h3, nsmul_eq_mul]
  ring

theorem classSum_compare {a : NG.AlgWt L n} {β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ} (hβ : IsInvForm a β) {J J' : Subgroup (GAf L n)}
    (hJ : IsBounded J) {N : ℕ} (hN : 0 < N) (hNJ : ∀ κ, NG.Cong L n N κ → κ ∈ J) (hJ' : IsBounded J') {T' : Finset (GAf L n)}
    (hT' : IsClassReps J' T') : ∃ (T : Finset (GAf L n)) (c : ℝ), IsClassReps J T ∧ 0 < c ∧
      ∀ (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (f f' : GAf L n → a.W), f ∈ NG.TypeSp a.ρ J χ → f' ∈ NG.TypeSp a.ρ J χ →
        f ∈ NG.TypeSp a.ρ J' χ' → f' ∈ NG.TypeSp a.ρ J' χ' → classSum a β J' T' f f' = (c : ℂ) * classSum a β J T f f' := by
  classical
  obtain ⟨F, hF⟩ := (GlobalTheory.CongIndex.finite_index_conj L n J' hJ' 1 N hN).2.1
  have hne' : (J ⊓ J').relIndex J' ≠ 0 := by
    have : ∀ f₀ ∈ F, ∃ u, (∃ κ ∈ J', f₀⁻¹ * κ ∈ J) → u ∈ J' ∧ f₀⁻¹ * u ∈ J := fun f₀ _ => by
      by_cases h : ∃ κ ∈ J', f₀⁻¹ * κ ∈ J
      · obtain ⟨u, hu⟩ := h
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' h⟩
    choose! u hu using this
    refine relIndex_ne_zero_of_cover (F.image u) (fun κ hκ => ?_) inf_le_right
    obtain ⟨f₀, h₀, h₁⟩ := hF κ hκ
    obtain ⟨h2, h3⟩ := hu f₀ h₀ ⟨κ, hκ, hNJ _ h₁⟩
    refine ⟨u f₀, Finset.mem_image_of_mem _ h₀, ?_, J'.mul_mem (J'.inv_mem h2) hκ⟩
    have := J.mul_mem (J.inv_mem h3) (hNJ _ h₁)
    simpa [mul_assoc] using this
  obtain ⟨U, hU1, hU2, -⟩ := exists_cosetReps (inf_le_right : J ⊓ J' ≤ J') hne'
  obtain ⟨T₀, hT₀⟩ := exists_reps (J ⊓ J') ((T' ×ˢ U).image fun p => p.1 * p.2) fun g => by
    obtain ⟨t, ⟨ht, γ, κ, hκ, e⟩, -⟩ := hT' g
    obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hU2 κ hκ
    exact ⟨t * u, Finset.mem_image.2 ⟨(t, u), Finset.mem_product.2 ⟨ht, hu⟩, rfl⟩, γ, u⁻¹ * κ, hu', by rw [e]; group⟩
  have hne : (J ⊓ J').relIndex J ≠ 0 := relIndex_ne_zero_of_reps hJ inf_le_left hT₀
  obtain ⟨T, hT⟩ := exists_reps J T₀ fun g => by
    obtain ⟨t, ⟨ht, γ, κ, hκ, e⟩, -⟩ := hT₀ g
    exact ⟨t, ht, γ, κ, hκ.1, e⟩
  refine ⟨T, ((J ⊓ J').relIndex J : ℝ) / ((J ⊓ J').relIndex J' : ℝ), hT,
    div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hne)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hne')), ?_⟩
  intro χ χ' f f' h1 h2 h3 h4
  have e1 := classSum_index hβ hJ inf_le_left hne hT hT₀ h1 h2
  have e2 := classSum_index hβ hJ' inf_le_right hne' hT' hT₀ h3 h4
  have hc : (((J ⊓ J').relIndex J' : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne'
  push_cast
  rw [div_mul_eq_mul_div, ← e1, e2, mul_div_cancel_left₀ _ hc]

theorem classSum_transport {G Γ W I : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I]
    (ι : Γ →* G) (hι : Function.Injective ι) (φ : GAf L n ≃* G) (hrat : ∀ h, h ∈ GQ L n ↔ ∃ γ, ι γ = φ h)
    (J : Subgroup G) (y : I → G) (hy : Formalism.IndefR.Bridge.IsReps ι J y) :
    ∃ T, IsClassReps (J.comap φ.toMonoidHom) T ∧ ∀ (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (f f' : GAf L n → a.W)
      (F F' : G → W), (∀ g, β (f g) (f' g) = inner ℂ (F (φ g)) (F' (φ g))) →
      classSum a β (J.comap φ.toMonoidHom) T f f' = Formalism.IndefR.Bridge.adInner ι J y F F' := by
  classical
  have hinj : Function.Injective fun i => φ.symm (y i) := fun i j e => by
    have e' : y i = y j := φ.symm.injective e
    exact (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨1, 1, by simp [e']⟩
  have key : ∀ g i, (∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J.comap φ.toMonoidHom ∧ g = (γ : GAf L n) * φ.symm (y i) * κ) ↔
      ∃ (γ : Γ) (k : J), φ g = ι γ * y i * k := fun g i => by
    constructor
    · rintro ⟨γ, κ, hκ, rfl⟩
      obtain ⟨δ, hδ⟩ := (hrat _).1 γ.2
      exact ⟨δ, ⟨φ κ, hκ⟩, by simp [hδ]⟩
    · rintro ⟨γ, k, e⟩
      refine ⟨⟨φ.symm (ι γ), (hrat _).2 ⟨γ, by simp⟩⟩, φ.symm k, by simp, φ.injective (by simp [e])⟩
  refine ⟨Finset.univ.image fun i => φ.symm (y i), fun g => ?_, fun a β f f' F F' h => ?_⟩
  · obtain ⟨i, hi, hu⟩ := hy (φ g)
    refine ⟨φ.symm (y i), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key g i).2 hi⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
    rw [hu j ((key g j).1 h)]
  · rw [classSum, Finset.sum_image fun i _ j _ e => hinj e, Formalism.IndefR.Bridge.adInner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h, MulEquiv.apply_symm_apply]
    congr 3
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun δ : Formalism.IndefR.Bridge.stab ι J (y i) =>
      (⟨⟨φ.symm (ι δ), (hrat _).2 ⟨δ, by simp⟩⟩, by simpa using (Formalism.IndefR.Bridge.mem_stab ι).1 δ.2⟩ :
        {γ : GQ L n // (φ.symm (y i))⁻¹ * (γ : GAf L n) * φ.symm (y i) ∈ J.comap φ.toMonoidHom})) ⟨fun δ δ' e => ?_, fun γ => ?_⟩)
    · exact Subtype.ext (hι (φ.symm.injective (congrArg (fun z => (z.1 : GAf L n)) e)))
    · obtain ⟨δ, hδ⟩ := (hrat _).1 γ.1.2
      refine ⟨⟨δ, (Formalism.IndefR.Bridge.mem_stab ι).2 ?_⟩, Subtype.ext (Subtype.ext (by simp [hδ]))⟩
      simpa [hδ] using γ.2

end GlobalTheory.FormInner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowAt
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitRowAll

theorem splitRow_at : ∀ D : D7, SplitRow_at D := by
  intro D
  refine ⟨fun l hl => _root_.GlobalTheory.SplitPlaces.placesSplit D.host l hl, fun i hi => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro w hw
    have h2 : D.nd.l i ∉ D.host.small := ((primeClass_eq_splitK_iff _).1 hi.2.2.2.2.2).1
    exact (_root_.GlobalTheory.HubLoc.localField_unramified D i h2 hi.2.2.1 hi.2.2.2.1 w hw).1
  · rintro w hw τ ⟨h1, h2⟩
    rcases GlobalTheory.SplitRowProbe.embIn_xor D i w hw τ with h | h
    · exact h.2 h2
    · exact h.2 h1
  · exact GlobalTheory.T.splitPrime_place_cmType_conjugate D i hi
  · exact GlobalTheory.T.cmHalfTypePlaces_meet_conjugatePairs_and_count D i hi

end GlobalTheory.SplitRowAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLevelDecomposition
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LevelTypeProj

theorem span_eval_eq_top {X M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (ev : X → Module.Dual ℂ M) (hev : ∀ v, (∀ x, ev x v = 0) → v = 0) :
    Submodule.span ℂ (Set.range ev) = ⊤ := by
  have hbot : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact (Submodule.mem_bot ℂ).2 (hev v fun x => hv (ev x) (Submodule.subset_span ⟨x, rfl⟩))
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), hbot,
    Submodule.dualAnnihilator_bot]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem finRep_cptRep (l : GL (Fin N) (Af E)) (k : Kinf E N) (φ : Sm E N) :
    finRep E N l (cptRep E N k φ) = cptRep E N k (finRep E N l φ) := by
  simp only [finRep, cptRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul, ← infGL_comm, map_mul, Module.End.mul_apply]

def orbitSpan (L : Subgroup (GL (Fin N) (Af E))) (ψ : Sm E N) : Submodule ℂ (Sm E N) :=
  Submodule.span ℂ {v | ∃ l ∈ L, ∃ k, v = finRep E N l (cptRep E N k ψ)}

theorem mem_orbitSpan_self (L : Subgroup (GL (Fin N) (Af E))) (ψ : Sm E N) : ψ ∈ orbitSpan L ψ :=
  Submodule.subset_span ⟨1, L.one_mem, 1, by rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply]⟩

theorem orbitSpan_le {J : Submodule ℂ (Sm E N)} (hJ : _root_.GlobalTheory.CuspRep.IsStable J) (L : Subgroup (GL (Fin N) (Af E)))
    {ψ : Sm E N} (hψ : ψ ∈ J) : orbitSpan L ψ ≤ J :=
  Submodule.span_le.2 (by rintro _ ⟨l, -, k, rfl⟩; exact hJ (.fin l) _ (hJ (.cpt k) _ hψ))

theorem finRep_mem_orbitSpan {L : Subgroup (GL (Fin N) (Af E))} {ψ : Sm E N} {l' : GL (Fin N) (Af E)}
    (hl' : l' ∈ L) {v : Sm E N} (hv : v ∈ orbitSpan L ψ) : finRep E N l' v ∈ orbitSpan L ψ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, k, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l' * l, L.mul_mem hl' hl, k, ?_⟩
    rw [map_mul (finRep E N), Module.End.mul_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem cptRep_mem_orbitSpan {L : Subgroup (GL (Fin N) (Af E))} {ψ : Sm E N} (k' : Kinf E N)
    {v : Sm E N} (hv : v ∈ orbitSpan L ψ) : cptRep E N k' v ∈ orbitSpan L ψ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, k, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l, hl, k' * k, ?_⟩
    rw [map_mul (cptRep E N), Module.End.mul_apply, finRep_cptRep l k' (cptRep E N k ψ)]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem orbitSpan_finiteDimensional (L : Subgroup (GL (Fin N) (Af E))) (hL : IsCompact (L : Set (GL (Fin N) (Af E))))
    (ψ : Sm E N) (hψ : IsAutForm ψ) : FiniteDimensional ℂ (orbitSpan L ψ) := by
  classical
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover (fun l : GL (Fin N) (Af E) => {m | finRep E N (l⁻¹ * m) ψ = ψ})
    (fun l => hψ.level.preimage (continuous_const_mul l⁻¹))
    (fun m _ => Set.mem_iUnion.2 ⟨m, by simp only [Set.mem_setOf_eq, inv_mul_cancel, map_one]; rfl⟩)
  have := hψ.kfin
  refine Submodule.finiteDimensional_of_le
    (S₂ := t.sup fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨m, hm, k, rfl⟩
  obtain ⟨l, hl, hlm⟩ := Set.mem_iUnion₂.1 (ht hm)
  have e : finRep E N m ψ = finRep E N l ψ := by
    calc finRep E N m ψ = finRep E N l (finRep E N (l⁻¹ * m) ψ) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = finRep E N l ψ := by rw [show finRep E N (l⁻¹ * m) ψ = ψ from hlm]
  refine Finset.le_sup (f := fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l)) hl ?_
  refine ⟨cptRep E N k ψ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  change finRep E N l (cptRep E N k ψ) = finRep E N m (cptRep E N k ψ)
  rw [finRep_cptRep, finRep_cptRep, e]

def typePart (L : Subgroup (GL (Fin N) (Af E))) {U : Type} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Kinf E N) U) : Submodule ℂ (Sm E N) where
  carrier := {φ | (∀ k ∈ L, finRep E N k φ = φ) ∧
    ∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k hk => by rw [map_add (f := _), hx.1 k hk, hy.1 k hk],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ => map_zero _, fun _ => by
    simp only [map_zero, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k hk => by rw [map_smul, hx.1 k hk],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

theorem exists_proj {μ : Measure (GA E N)} [μ.IsHaarMeasure] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    (S : Submodule ℂ (Sm E N)) (hSW : S ≤ W) [FiniteDimensional ℂ S] :
    ∃ p : W →ₗ[ℂ] W, (∀ x, (p x).1 ∈ S) ∧
      ∀ x y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h (p x)) (toL2ₗ μ W h y) = 0 := by
  haveI : FiniteDimensional ℂ (S.comap W.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hSW).symm.finiteDimensional
  let e := Submodule.equivMapOfInjective (toL2ₗ μ W h) hF (S.comap W.subtype)
  haveI : FiniteDimensional ℂ ((S.comap W.subtype).map (toL2ₗ μ W h)) := e.finiteDimensional
  have e1 : ∀ z, toL2ₗ μ W h ((e.symm z : S.comap W.subtype) : W) = (z : L2 (latticeGL E N) μ) := fun z => by
    have := Submodule.coe_equivMapOfInjective_apply (toL2ₗ μ W h) hF (S.comap W.subtype) (e.symm z)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨(S.comap W.subtype).subtype ∘ₗ e.symm.toLinearMap ∘ₗ
    ((S.comap W.subtype).map (toL2ₗ μ W h)).orthogonalProjectionOnto.toLinearMap ∘ₗ toL2ₗ μ W h,
    fun x => (e.symm _).2, fun x y hy => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
  rw [e1]
  exact Submodule.starProjection_inner_eq_zero _ _ ⟨y, hy, rfl⟩

theorem proj_unique {μ : Measure (GA E N)} [μ.IsHaarMeasure] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    {S : Submodule ℂ (Sm E N)} {x a b : W} (ha : a.1 ∈ S) (hb : b.1 ∈ S)
    (hxa : ∀ y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h a) (toL2ₗ μ W h y) = 0)
    (hxb : ∀ y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h b) (toL2ₗ μ W h y) = 0) : a = b := by
  have hm : (b - a).1 ∈ S := S.sub_mem hb ha
  have key : toL2ₗ μ W h (b - a) = (toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b) := by
    rw [map_sub]; abel
  have h0 : inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a)) = 0 := by
    calc inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a))
        = inner ℂ ((toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b)) (toL2ₗ μ W h (b - a)) := by
          rw [← key]
      _ = 0 := by rw [inner_sub_left, hxa _ hm, hxb _ hm, sub_zero]
  exact (sub_eq_zero.1 (hF ((inner_self_eq_zero.1 h0).trans (map_zero _).symm))).symm

theorem proj_rt {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    {S : Submodule ℂ (Sm E N)} (hSW : S ≤ W) (p : W →ₗ[ℂ] W) (hpS : ∀ x, (p x).1 ∈ S)
    (hp : ∀ x y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h (p x)) (toL2ₗ μ W h y) = 0)
    (g : GA E N) (hgW : ∀ x ∈ W, rt E N g x ∈ W) (hgS : ∀ x ∈ S, rt E N g x ∈ S)
    (hgS' : ∀ x ∈ S, rt E N g⁻¹ x ∈ S) (x : W) :
    p ⟨rt E N g x.1, hgW _ x.2⟩ = ⟨rt E N g (p x).1, hgW _ (p x).2⟩ := by
  refine proj_unique h hF (hpS _) (hgS _ (hpS x)) (hp _) fun y hy => ?_
  have hy' : rt E N g⁻¹ y.1 ∈ W := hSW (hgS' _ hy)
  have ey : y = ⟨rt E N g (rt E N g⁻¹ y.1), hgW _ hy'⟩ := Subtype.ext (by
    show y.1 = rt E N g (rt E N g⁻¹ y.1)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
  rw [ey, ← R_toL2ₗ h x (hgW _ x.2), ← R_toL2ₗ h (p x) (hgW _ (p x).2), ← R_toL2ₗ h ⟨_, hy'⟩ (hgW _ hy'),
    ← map_sub]
  let Ui : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ := ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  change inner ℂ (Ui _) (Ui _) = 0
  rw [Ui.inner_map_map]
  exact hp x ⟨_, hy'⟩ (hgS' _ hy)

theorem exists_levelType_part : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W J : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ) → _root_.GlobalTheory.CuspRep.IsStable J → J ≤ W → ∀ (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) → IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (ρ : Representation ℂ (Kinf E N) U), AutFin.IsContRep ρ → ∀ ψ : W, ψ.1 ∈ J → ∃ ψ' : W, ψ'.1 ∈ J ∧ (∀ k ∈ L, finRep E N k ψ'.1 = ψ'.1) ∧ (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k ψ'.1).1 g) ∈ AutFin.coeffSpan ρ) ∧ ∀ φ : W, (∀ k ∈ L, finRep E N k φ.1 = φ.1) → (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ.1).1 g) ∈ AutFin.coeffSpan ρ) → inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ψ) = inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ψ') := by
  intro E _ _ _ N μ _ _ W J h hW hA hJ hJW L _ hLc U _ _ _ ρ _ ψ hψ
  have hF := toL2ₗ_injective h fun φ hφ => ContAut.continuous_of_isOpen_stab E N φ (hA φ hφ).level
  have hSJ : orbitSpan L ψ.1 ≤ J := orbitSpan_le hJ L hψ
  have hSW := hSJ.trans hJW
  haveI := orbitSpan_finiteDimensional L hLc ψ.1 (hA _ ψ.2)
  haveI : FiniteDimensional ℂ (orbitSpan L ψ.1 ⊓ typePart L ρ : Submodule ℂ (Sm E N)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨p, hpS, hp⟩ := exists_proj h hF (orbitSpan L ψ.1) hSW
  obtain ⟨q, hqQ, hq⟩ := exists_proj h hF (orbitSpan L ψ.1 ⊓ typePart L ρ) (inf_le_left.trans hSW)
  refine ⟨q ψ, hSJ (hqQ ψ).1, (hqQ ψ).2.1, (hqQ ψ).2.2, fun φ hφL hφK => ?_⟩
  have hpT : (p φ).1 ∈ typePart L ρ := by
    refine ⟨fun k hk => ?_, fun g => ?_⟩
    · have hc := proj_rt h hF hSW p hpS hp (finGL E N k) (fun x hx => hW (.fin k) x hx)
        (fun x hx => finRep_mem_orbitSpan hk hx)
        (fun x hx => by rw [← map_inv]; exact finRep_mem_orbitSpan (L.inv_mem hk) hx) φ
      exact (congrArg Subtype.val hc).symm.trans (congrArg (fun x => (p x).1) (Subtype.ext (hφL k hk)))
    · have hcomm : ∀ k : Kinf E N, cptRep E N k (p φ).1 = (p ⟨cptRep E N k φ.1, hW (.cpt k) _ φ.2⟩).1 := fun k =>
        (congrArg Subtype.val (proj_rt h hF hSW p hpS hp (infGL E N (Unitary.toUnits k))
          (fun x hx => hW (.cpt k) x hx) (fun x hx => cptRep_mem_orbitSpan k hx)
          (fun x hx => by rw [← map_inv, ← map_inv]; exact cptRep_mem_orbitSpan k⁻¹ hx) φ)).symm
      have := (hA φ φ.2).kfin
      have hVW : Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1) ≤ W :=
        Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hW (.cpt k) _ φ.2)
      let V := Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1)
      let Λ : Module.Dual ℂ V →ₗ[ℂ] (Kinf E N → ℂ) :=
        { toFun := fun ℓ k => ℓ ⟨cptRep E N k φ.1, Submodule.subset_span ⟨k, rfl⟩⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let ev : GA E N → Module.Dual ℂ V := fun x => (LinearMap.proj x).comp ((Sm E N).subtype.comp V.subtype)
      have htop := span_eval_eq_top ev fun v hv => Subtype.ext (Subtype.ext (funext hv))
      have hle : Submodule.span ℂ (Set.range ev) ≤ (AutFin.coeffSpan ρ).comap Λ :=
        Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hφK x)
      let ℓ : Module.Dual ℂ V :=
        (LinearMap.proj g).comp ((Sm E N).subtype.comp (W.subtype.comp (p.comp (Submodule.inclusion hVW))))
      have hℓ : Λ ℓ ∈ AutFin.coeffSpan ρ := hle (htop ▸ Submodule.mem_top)
      convert hℓ using 1
      funext k
      rw [hcomm k]
      rfl
  have hψS : ψ.1 ∈ orbitSpan L ψ.1 := mem_orbitSpan_self L ψ.1
  have hr : (ψ - q ψ).1 ∈ orbitSpan L ψ.1 := (orbitSpan L ψ.1).sub_mem hψS (hqQ ψ).1
  have h1 : inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h (ψ - q ψ)) =
      inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) := by
    have := hp φ (ψ - q ψ) hr
    rwa [inner_sub_left, sub_eq_zero] at this
  have h2 : inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) = 0 := by
    have := hq ψ (p φ) ⟨hpS φ, hpT⟩
    rw [map_sub, ← inner_conj_symm, this, map_zero]
  rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, h1, h2]

end GlobalTheory.LevelTypeProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StmtOfReal
section
namespace GlobalTheory.TopSteps.CharVanish
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem cls_eq_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (hC : S.CrysCalc) (hR : S.Real)
    (c : ℕ) (h2 : 2 ≤ c) (ht : c ≤ S.D.t) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X] :
    S.cls (S.Γ.Wchi c) X = {0} := by
  have hcl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hL : S.Lem0 (S.Γ.Wchi c) :=
    (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hcl (GlobalTheory.TopSteps.StdAdm.stdAdm S hC hcl)).2 c (by omega) ht
  exact GlobalTheory.TopSteps.CharAllCoef.main S c hL
    ((GlobalTheory.TopSteps.CharBound.resBound_chars S hR).1 c h2 ht hL) X

theorem stmt_of_real : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    Nonempty (LocTied l P AI) → (∀ S : TopSit P, S.Real) → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P := by
  intro l _ P AI hT hR K LL n r emb D Γ hyp c h2 ht X _ _ _
  have : NeZero n := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hyp.1⟩
  let S : TopSit P := ⟨K, LL, n, r, emb, D, Γ, hyp⟩
  exact cls_eq_zero S (GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps AI hT S) (hR S) c h2 ht X

end GlobalTheory.TopSteps.CharVanish
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedActionEqTwistedCoefficientsCocycleIffStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff : ∀ {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]
    (χ : G →* Oˣ),
    (∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m) ∧
    ∀ z : G → ↥L.T ⊗[O] X, tableLineDegreeTwo.IsCoc L X χ z ↔ z ∈ Z1 (twCoef (latRep L) χ X) ⊤ := by
  first | exact @GlobalTheory.actTw_eq_twCoef_and_isCoc_iff | exact GlobalTheory.actTw_eq_twCoef_and_isCoc_iff | (intros; apply GlobalTheory.actTw_eq_twCoef_and_isCoc_iff <;> assumption)
end

