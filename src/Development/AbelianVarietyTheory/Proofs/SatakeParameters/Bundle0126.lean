module

public import Mathlib
public import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
public import GroundTheory.AutomorphicForms.GKModules.RightRegular
public import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Product
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.T2SpaceAfP
section
open NumberField GlobalTheory.LKTrip IsDedekindDomain
open scoped TensorProduct Matrix.Norms.L2Operator RestrictedProduct

noncomputable section

open Topology

namespace GlobalTheory.GfTop

theorem td_of_inj {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (hi : Function.Injective f) : TotallyDisconnectedSpace X :=
  ⟨fun s _ hs => Set.subsingleton_of_image hi s
    (isTotallyDisconnected_of_totallyDisconnectedSpace (f '' s) (f '' s) subset_rfl (hs.image f hf.continuousOn))⟩

theorem props_of_closedEmb {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LocallyCompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [SecondCountableTopology Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    LocallyCompactSpace X ∧ T2Space X ∧ TotallyDisconnectedSpace X ∧ SecondCountableTopology X :=
  ⟨hf.locallyCompactSpace, hf.isEmbedding.t2Space, td_of_inj hf.continuous hf.injective,
    hf.isEmbedding.secondCountableTopology⟩

theorem isClosedEmbedding_embedProduct' (A : Type*) [TopologicalSpace A] [Monoid A] [ContinuousMul A] [T2Space A] :
    IsClosedEmbedding (Units.embedProduct A) := by
  refine ⟨Units.isEmbedding_embedProduct, ?_⟩
  have h : Set.range (Units.embedProduct A) =
      {x : A × Aᵐᵒᵖ | x.1 * x.2.unop = 1 ∧ x.2.unop * x.1 = 1} := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨u, hu⟩
      rw [← hu]
      simp
    · rintro ⟨h1, h2⟩
      exact ⟨⟨a, b.unop, h1, h2⟩, rfl⟩
  rw [h]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
    (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

theorem units_props (A : Type*) [TopologicalSpace A] [Monoid A] [ContinuousMul A] [LocallyCompactSpace A]
    [T2Space A] [TotallyDisconnectedSpace A] [SecondCountableTopology A] :
    LocallyCompactSpace Aˣ ∧ T2Space Aˣ ∧ TotallyDisconnectedSpace Aˣ ∧ SecondCountableTopology Aˣ := by
  obtain ⟨o1, o2, o3, o4⟩ := props_of_closedEmb (MulOpposite.opHomeomorph (M := A)).symm.isClosedEmbedding
  exact props_of_closedEmb (isClosedEmbedding_embedProduct' A)

theorem module_props (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [T2Space R] [TotallyDisconnectedSpace R] [SecondCountableTopology R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [TopologicalSpace M]
    [IsModuleTopology R M] :
    LocallyCompactSpace M ∧ T2Space M ∧ TotallyDisconnectedSpace M ∧ SecondCountableTopology M := by
  haveI : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  let b := Module.Free.chooseBasis R M
  let e : M ≃ₜ (Module.Free.ChooseBasisIndex R M → R) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  exact props_of_closedEmb e.isClosedEmbedding

section UPts

open GlobalTheory.LKTrip

variable {C : Type} [Ring C] [Algebra ℚ C] [Module.Finite ℚ C] (star : C →+* Cᵐᵒᵖ)

theorem upts_props (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [SecondCountableTopology R] :
    LocallyCompactSpace (UPts star R) ∧ T2Space (UPts star R) ∧ TotallyDisconnectedSpace (UPts star R) ∧
      SecondCountableTopology (UPts star R) := by
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[ℚ] C) := IsModuleTopology.isTopologicalRing R (R ⊗[ℚ] C)
  obtain ⟨m1, m2, m3, m4⟩ := module_props R (R ⊗[ℚ] C)
  obtain ⟨u1, u2, u3, u4⟩ := units_props (R ⊗[ℚ] C)
  obtain ⟨v1, v2, v3, v4⟩ := units_props R
  let f : C →ₗ[ℚ] C := (MulOpposite.opLinearEquiv ℚ).symm.toLinearMap ∘ₗ star.toRatAlgHom.toLinearMap
  have hσeq : (fun y : R ⊗[ℚ] C => (starT star R y).unop) = LinearMap.baseChange R f := by
    funext y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [starT_tmul, LinearMap.baseChange_tmul]
      rfl
    | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add] at hx hy ⊢; rw [hx, hy]
  have hσ : Continuous (fun y : R ⊗[ℚ] C => (starT star R y).unop) := by
    rw [hσeq]
    exact IsModuleTopology.continuous_of_linearMap _
  have hcl : IsClosed ((UPts star R : Subgroup ((R ⊗[ℚ] C)ˣ × Rˣ)) : Set ((R ⊗[ℚ] C)ˣ × Rˣ)) := by
    have hs : ((UPts star R : Subgroup ((R ⊗[ℚ] C)ˣ × Rˣ)) : Set ((R ⊗[ℚ] C)ˣ × Rˣ)) =
        {x | ((x.1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C) * (starT star R ((x.1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C)).unop =
          algebraMap R (R ⊗[ℚ] C) ((x.2 : Rˣ) : R)} := rfl
    rw [hs]
    exact isClosed_eq ((Units.continuous_val.comp continuous_fst).mul (hσ.comp (Units.continuous_val.comp continuous_fst)))
      ((continuous_algebraMap R (R ⊗[ℚ] C)).comp (Units.continuous_val.comp continuous_snd))
  exact props_of_closedEmb hcl.isClosedEmbedding_subtypeVal

end UPts

end GlobalTheory.GfTop

namespace GlobalTheory.GfTop

open GlobalTheory.LKTrip IsDedekindDomain

section AfP

variable (p : ℕ)

theorem t2Space_afP : T2Space (AfP p) :=
  inferInstanceAs (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))

theorem finiteAdeleRingAway_locallyCompactSpace : LocallyCompactSpace (AfP p) :=
  (LevelExists.isCompact_intAfP p).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((LevelExists.isOpen_intAfP p).mem_nhds (LevelExists.intAfP p).zero_mem)

theorem finiteAdeleRingAway_totallyDisconnectedSpace : TotallyDisconnectedSpace (AfP p) :=
  td_of_inj (X := Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ])
    (f := fun x => (x : ∀ v : AwayP p, v.1.adicCompletion ℚ)) RestrictedProduct.continuous_coe
    (fun x y h => RestrictedProduct.ext _ _ fun i => congrFun h i)

theorem countable_awayP : Countable (AwayP p) := by
  have hI : Countable (Ideal ℤ) := by
    have hs : Function.Surjective (fun n : ℤ => Ideal.span {n}) := fun I =>
      ⟨Submodule.IsPrincipal.generator I, Ideal.span_singleton_generator I⟩
    exact hs.countable
  have hi : Function.Injective (fun v : AwayP p => v.1.asIdeal) := fun v w h =>
    Subtype.ext (HeightOneSpectrum.ext h)
  exact hi.countable

theorem compl_sc (v : HeightOneSpectrum ℤ) : SecondCountableTopology (v.adicCompletion ℚ) := by
  haveI : Fact ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding.secondCountableTopology

theorem finiteAdeleRingAway_secondCountableTopology : SecondCountableTopology (AfP p) := by
  haveI := countable_awayP p
  haveI : ∀ v : AwayP p, SecondCountableTopology (v.1.adicCompletion ℚ) := fun v => compl_sc v.1
  have hAopen : ∀ v : AwayP p, IsOpen ((v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) :=
    fun v => Valued.isOpen_valuationSubring _
  have hS : ∀ S : Finset (AwayP p), Filter.cofinite ≤ Filter.principal ((S : Set (AwayP p))ᶜ) := fun S =>
    Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite
  let U : Finset (AwayP p) → Set (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]) :=
    fun S => Set.range (RestrictedProduct.inclusion (fun v : AwayP p => v.1.adicCompletion ℚ)
      (fun v : AwayP p => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) (hS S))
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hAopen (hS S)).isOpen_range
  have hsc : ∀ S, SecondCountableTopology (U S) := fun S => by
    haveI : SecondCountableTopology (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]_[
        Filter.principal ((S : Set (AwayP p))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (RestrictedProduct.isOpenEmbedding_inclusion_principal hAopen
      (hS S)).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hcov : ⋃ S, U S = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨(Filter.eventually_cofinite.1 x.2).toFinset, ?_⟩
    show x ∈ Set.range _
    rw [RestrictedProduct.range_inclusion]
    refine Filter.eventually_principal.2 fun i hi => ?_
    by_contra h
    exact hi (by rw [Finset.mem_coe, Set.Finite.mem_toFinset]; exact h)
  exact @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ U hsc hUo hcov

end AfP

end GlobalTheory.GfTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VEqKZeroOfNormOne
section
noncomputable section

namespace GlobalTheory.UnitK

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem vEqK_zero_of_norm_one : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (x : X.G.Kf), ‖E.iK x‖ = 1 → X.vEqK x 0 := by
  intro p _ X hfr E x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨N, hN⟩ := Formalism.MainNotions.FormalGroupSystem.Pf.exists_rep X hfr hx0

  have hint : ∀ y : X.G.Kf, ‖E.iK y‖ = 1 → y ∈ X.intK := fun y hy =>
    (E.mem_iff y).1 (by rw [mem_OcC]; exact hy.le)
  have h1 : X.vGeK x 0 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_zero_iff X).2 (hint x hx)
  have h2 : X.vGeK x⁻¹ 0 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_zero_iff X).2 (hint x⁻¹ (by rw [map_inv₀, norm_inv, hx, inv_one]))
  have hN1 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_iff_of_rep X hfr hN 0).1 h1
  have hN2 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_iff_of_rep X hfr (Formalism.MainNotions.FormalGroupSystem.Pf.Rep.inv X hN) 0).1 h2
  simp only [zero_mul] at hN1 hN2
  have hN0 : N = 0 := by
    have a : (0 : ℤ) ≤ N := by exact_mod_cast hN1
    have b : (0 : ℤ) ≤ -N := by exact_mod_cast hN2
    omega

  have he : 0 < X.eO := by
    rcases Nat.eq_zero_or_pos X.eO with h0 | h0
    · exfalso
      obtain ⟨u, hu⟩ := X.eO_spec
      rw [h0, pow_zero] at hu

      have hpu : IsUnit (p : X.G.O) := by
        exact IsUnit.of_mul_eq_one _ hu
      obtain ⟨w, hw⟩ := hpu.exists_right_inv
      have hb := E.int w
      have hmul : E.iK (algebraMap X.G.O X.G.Kf (p : X.G.O)) * E.iK (algebraMap X.G.O X.G.Kf w) = 1 := by
        rw [← map_mul, ← map_mul, hw, map_one, map_one]
      have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
        have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
        rw [this, norm_algebraMap', Padic.norm_p]
      rw [map_natCast, map_natCast] at hmul
      have hn2 := congrArg norm hmul
      rw [norm_mul, norm_one, hn] at hn2
      have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      have hp0 : (0 : ℝ) < p := by linarith
      have : ‖E.iK (algebraMap X.G.O X.G.Kf w)‖ = p := by
        field_simp at hn2
        linarith
      linarith
    · exact h0
  exact (Formalism.MainNotions.FormalGroupSystem.Pf.vEqK_iff_of_rep X hfr hN 0).2 ⟨he, by simp [hN0]⟩

end GlobalTheory.UnitK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumTranslateRelationMapPreservingVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem locVac_rel_map : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ φ : M →ₗ[ℂ] M, (∀ s, LocVac ρ s → LocVac ρ (φ s)) → ∀ f : Matrix (Fin n') (Fin n) L →₀ M, (∀ x, LocVac ρ (f x)) → (f.sum fun x m => ρ x m) = 0 → (f.sum fun x m => ρ x (φ m)) = 0 := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP φ hφ f hf hsum
  classical
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by
    intro t ht x u hu
    have h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t := by
      have := congrArg (fun f => f t) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [ht u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by
    intro t ht x u hu
    have := congrArg (fun f => f t) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  have hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L := L) n n',
      ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) →
      x - y ∈ intMatSub (L := L) n n' := by
    intro x y hxy
    refine intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)
    have e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) =
        (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y)) := by
      rw [locH_sub_right, map_sub]; ring
    rw [e, AddChar.map_add_eq_mul, hxy u hu, hψinv]

  have hinj : ∀ x t, ρ x t = 0 → t = 0 := by
    intro x t h0
    have := congrArg (fun f => f t) (hρ (-x) x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0,
      Module.End.one_apply] at this
    have hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0 := by
      intro h; have := hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2); rw [h, zero_mul] at this
      exact zero_ne_one this
    exact (smul_eq_zero.mp this.symm).resolve_left hne

  set Λ := intMatSub (L := L) n n' with hΛ
  have hmem : ∀ x : Matrix (Fin n') (Fin n) L, -(QuotientAddGroup.mk x : _ ⧸ Λ).out + x ∈ Λ := by
    intro x
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  set κ : Matrix (Fin n') (Fin n) L → ℂ := fun x =>
    ψ (-((locH σ δ JS JT (QuotientAddGroup.mk x : _ ⧸ Λ).out (-(QuotientAddGroup.mk x : _ ⧸ Λ).out + x) +
      σ (locH σ δ JS JT (QuotientAddGroup.mk x : _ ⧸ Λ).out (-(QuotientAddGroup.mk x : _ ⧸ Λ).out + x))) / 2)) with hκ
  have hdec1 : ∀ t, LocVac ρ t → ∀ x, ρ x t = κ x • ρ (QuotientAddGroup.mk x : _ ⧸ Λ).out t := by
    intro t ht x
    have := hshift t ht (QuotientAddGroup.mk x : _ ⧸ Λ).out _ (hmem x)
    rwa [add_neg_cancel_left] at this
  set I : Finset (Matrix (Fin n') (Fin n) L ⧸ Λ) := f.support.image (fun x => (QuotientAddGroup.mk x : _ ⧸ Λ)) with hI

  let cl : (Matrix (Fin n') (Fin n) L → M) → (Matrix (Fin n') (Fin n) L ⧸ Λ) → M := fun g y =>
    ∑ x ∈ f.support with (QuotientAddGroup.mk x : _ ⧸ Λ) = y, κ x • g x
  have hdec : ∀ g : Matrix (Fin n') (Fin n) L → M, (∀ x, LocVac ρ (g x)) →
      ∑ x ∈ f.support, ρ x (g x) = ∑ y ∈ I, ρ y.out (cl g y) := by
    intro g hg
    have e1 : ∑ x ∈ f.support, ρ x (g x) =
        ∑ x ∈ f.support, κ x • ρ (QuotientAddGroup.mk x : _ ⧸ Λ).out (g x) :=
      Finset.sum_congr rfl fun x _ => hdec1 _ (hg x) x
    rw [e1, ← Finset.sum_fiberwise_of_maps_to (s := f.support) (t := I) (g := fun x => (QuotientAddGroup.mk x : _ ⧸ Λ))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl fun y _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cl, map_sum, map_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]
  have hclvac : ∀ y, LocVac ρ (cl f y) := by
    intro y u hu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cl, map_sum, map_smul]
    exact Finset.sum_congr rfl fun x _ => by rw [hf x u hu]

  have hcl0 : ∀ y ∈ I, cl f y = 0 := by
    intro y hy
    have hsum' : ∑ y ∈ I, ρ y.out (cl f y) = 0 := by
      rw [← hdec f hf]; exact hsum
    have hind := GlobalTheory.joint_eigenvectors_eq_zero_of_sum_eq_zero Λ (Matrix (Fin n') (Fin n) L ⧸ Λ) M
      (fun u : Λ => ρ (u : Matrix (Fin n') (Fin n) L))
      (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : Λ) =>
        ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out)))
      (fun y => ρ y.out (cl f y)) I (fun y _ u => heig _ (hclvac y) y.out u u.2)
      (by
        intro y _ y' _ hyy
        have hm := hdist y.out y'.out (fun u hu => congrFun hyy ⟨u, hu⟩)
        rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
        exact hm)
      hsum' y hy
    exact hinj _ _ hind
  have hφcl : ∀ y, cl (fun x => φ (f x)) y = φ (cl f y) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cl, map_sum, map_smul]
  show ∑ x ∈ f.support, ρ x (φ (f x)) = 0
  rw [hdec (fun x => φ (f x)) (fun x => hφ _ (hf x))]
  exact Finset.sum_eq_zero fun y hy => by rw [hφcl, hcl0 y hy, map_zero, map_zero]

end GlobalTheory.Hk3
end

