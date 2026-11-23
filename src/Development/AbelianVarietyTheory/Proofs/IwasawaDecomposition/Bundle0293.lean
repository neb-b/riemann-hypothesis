module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxUnramifiedSubfieldConjIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicSumInfGroupAlgebraKilledEqBot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

noncomputable section

namespace GlobalTheory.RepCount

theorem iSup_range_homInto_inf_killed_eq_bot : ∀ (H S0 X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (C : Submodule ℂ X) (I : Set (MonoidAlgebra ℂ H)), σ0.IsIrreducible → killed σ0 I = ⊥ → ((⨆ f ∈ homInto σ0 ρ C, LinearMap.range f) ⊓ killed ρ I : Submodule ℂ X) = ⊥ := by
  intro H S0 X _ _ _ _ _ σ0 ρ C I hirr hk
  haveI hS : IsSimpleModule (MonoidAlgebra ℂ H) σ0.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ0).1 hirr
  let N : Submodule (MonoidAlgebra ℂ H) ρ.asModule :=
    ⨆ (f : S0 →ₗ[ℂ] X) (hf : f ∈ homInto σ0 ρ C), LinearMap.range (modMap f hf.2)
  have hN : N ≤ isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule σ0.asModule := by
    refine iSup₂_le fun f hf => ?_
    rcases LinearMap.injective_or_eq_zero (modMap f hf.2) with hi | h0
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · rw [h0, LinearMap.range_zero]; exact bot_le
  haveI : IsSemisimpleModule (MonoidAlgebra ℂ H) N :=
    IsSemisimpleModule.of_injective _ (Submodule.inclusion_injective hN)
  have hiso : IsIsotypicOfType (MonoidAlgebra ℂ H) N σ0.asModule :=
    (IsIsotypicOfType.isotypicComponent _ _ _).of_injective _ (Submodule.inclusion_injective hN)
  obtain ⟨ι, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
  rw [eq_bot_iff]
  rintro v ⟨hv1, hv2⟩
  rw [Submodule.mem_bot]
  by_contra hv0
  have hvN : ρ.asModuleEquiv.symm v ∈ N := by
    have hle : (⨆ f ∈ homInto σ0 ρ C, LinearMap.range f : Submodule ℂ X) ≤
        (N.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
      refine iSup₂_le fun f hf => ?_
      rintro _ ⟨s, rfl⟩
      have hfs : ρ.asModuleEquiv.symm (f s) = modMap f hf.2 (σ0.asModuleEquiv.symm s) := by
        rw [LinearEquiv.symm_apply_eq, modMap_apply, LinearEquiv.apply_symm_apply]
      show ρ.asModuleEquiv.symm (f s) ∈ N
      rw [hfs]
      exact (le_iSup₂ (f := fun (f : S0 →ₗ[ℂ] X) (hf : f ∈ homInto σ0 ρ C) =>
        LinearMap.range (modMap f hf.2)) f hf) ⟨_, rfl⟩
    exact hle hv1
  let w : N := ⟨_, hvN⟩
  have hw : w ≠ 0 := fun h => hv0 (by
    have := congrArg (fun x : N => ρ.asModuleEquiv x.1) h
    simpa [w] using this)
  have hew : e w ≠ 0 := fun h => hw (e.map_eq_zero_iff.1 h)
  obtain ⟨i, hi⟩ : ∃ i, e w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hew (Finsupp.ext h)
  refine killed_ne_bot (LinearEquiv.refl _ σ0.asModule) hi (fun x hx => ?_) hk
  have hxw : x • w = 0 := by
    apply Subtype.ext
    show x • ρ.asModuleEquiv.symm v = 0
    apply ρ.asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, mem_killed.1 hv2 x hx,
      map_zero]
  have := congrArg (fun u => e u i) hxw
  simpa [map_smul, Finsupp.smul_apply] using this

end GlobalTheory.RepCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepPuVolAR
section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe.KeepD

variable {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X)


set_option maxHeartbeats 4000000 in
theorem toTerm_eTT (u u' : D.what₂.Word) (s : TT Y u u') : (eTT Z Y u u' s).toTerm = eRT Z Y u u' s.toTerm := (by with_unfolding_all exact (Eq.refl (eRT Z Y u u' s.toTerm) :))


set_option maxHeartbeats 4000000 in
def eFib (u u' : D.what₂.Word) (t : RT Y u u') : fib Y t ≃ fib (reY Z Y) (eRT Z Y u u' t) :=
  Equiv.subtypeEquiv (eTT Z Y u u') fun s => by
    rw [toTerm_eTT]
    exact (eRT Z Y u u').injective.eq_iff.symm


set_option maxHeartbeats 4000000 in
theorem aT_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u u' : D.what₂.Word) (s : TT Y u u') (x : ColT (h.shInj u')) :
    eCure Z h h' u (aT h u u' s x) = aT h' (wd Z u) (wd Z u') (eTT Z Y u u' s) (eCure Z h h' u' x) := (by with_unfolding_all exact (
  Eq.refl (aT h u u' s x) :))


set_option maxHeartbeats 4000000 in
theorem aR_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u u' : D.what₂.Word) (t : RT Y u u') (x : ColT (h.shInj u')) :
    eCure Z h h' u (aR h u u' t x) = aR h' (wd Z u) (wd Z u') (eRT Z Y u u' t) (eCure Z h h' u' x) := by
  letI := h.fibFT t
  letI := h'.fibFT (eRT Z Y u u' t)
  unfold aR
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, map_sum]
  exact Fintype.sum_equiv (eFib Z Y u u' t) _ _ fun s => aT_keep Z Y u u' s.1 x


set_option maxHeartbeats 4000000 in
theorem pu_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u : D.what₂.Word) (x : ColT (h.shInj u)) :
    eHHre Z X (puC h u x) = puC h' (wd Z u) (eCure Z h h' u x) := (by with_unfolding_all exact (Eq.refl (puC h u x) :))


set_option maxHeartbeats 4000000 in
theorem vol_keep (u : D.what₂.Word) : Y.volN u = (reY Z Y).volN u ∧ Y.volH u = (reY Z Y).volH u := by
  constructor
  · exact (by with_unfolding_all exact (Eq.refl (Y.volN u) :))
  · exact (by with_unfolding_all exact (Eq.refl (Y.volH u) :))

end GlobalTheory.Mem.SRe.KeepD

namespace GlobalTheory.Mem.SRe


set_option maxHeartbeats 4000000 in
theorem keep_pu_vol_aR : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y)), (∀ u x, eHHre Z X (puC h u x) = puC h' (wd Z u) (eCure Z h h' u x)) ∧ (∀ u, Y.volN u = (reY Z Y).volN u ∧ Y.volH u = (reY Z Y).volH u) ∧ ∀ u u' (t : RT Y u u') x, eCure Z h h' u (aR h u u' t x) = aR h' (wd Z u) (wd Z u') (eRT Z Y u u' t) (eCure Z h h' u' x) :=
  fun _ Z _ Y _ _ => ⟨fun u x => KeepD.pu_keep Z Y u x, fun u => KeepD.vol_keep Z Y u,
    fun u u' t x => KeepD.aR_keep Z Y u u' t x⟩

end GlobalTheory.Mem.SRe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatible
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

theorem GlobalTheory.LocalExtCompletion.exists_completion_ext : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (_ : IsPlaceOver A v'), IsLocalExt L h → ∀ (ι : Ω →ₐ[K] Kbar v) (ι' : Ω →ₐ[L] Kbar v'), IsLocEmb A v ι → IsLocEmb A v' ι' → ∃ (f : v.adicCompletion K →+* v'.adicCompletion L) (b : Kbar v ≃+* Kbar v'), Continuous f ∧ (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) ∧ (∀ z, b (ι z) = ι' z) ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ (letI := f.toAlgebra; Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L ∧ Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ (∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) ∧ ∀ z : L, Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' hloc ι ι' hι hι'
  obtain ⟨e, he, hv⟩ := _root_.GlobalTheory.LyingOver.valuation_pow_of_isPlaceOver K L Ω A v v' h h'
  obtain ⟨f, hfc, hfK, hfv⟩ := GlobalTheory.T.exists_extension_pow_alt K L v v' e he hv
  have hirr := GlobalTheory.T.minpoly_irreducible_local_embedding K L Ω A v h (fun σ => by
    obtain ⟨τ, hτ⟩ := hloc σ
    exact ⟨τ, Weil_le_Dec h τ.2, hτ⟩) ι hι
  letI : Algebra (v.adicCompletion K) (v'.adicCompletion L) := f.toAlgebra
  have hind := GlobalTheory.T.linearIndependent_completion_of_irreducible_minpoly_alt K L v v' f hfK hirr _ (Module.finBasis K L)
  have hspan := GlobalTheory.T.span_basis_image_adicCompletion_eq_top_alt K L v v' f hfc hfK _ (Module.finBasis K L)
  let b' : Module.Basis (Fin (Module.finrank K L)) (v.adicCompletion K) (v'.adicCompletion L) :=
    Module.Basis.mk hind hspan.ge
  have hb' : ∀ i, b' i = algebraMap L _ (Module.finBasis K L i) := fun i => Module.Basis.mk_apply _ _ _
  haveI hfd : FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) := Module.Finite.of_basis b'
  have hrank : Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L := by
    rw [Module.finrank_eq_card_basis b', Fintype.card_fin]
  have htn := GlobalTheory.T.adicCompletion_trace_norm_of_basis_image_alt K L v v' f hfK _ (Module.finBasis K L) b' hb'
  have hcont := GlobalTheory.T.adicCompletion_trace_norm_continuous_alt K L v v' f hfc hfd

  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (v'.adicCompletion L) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (Kbar v') :=
    Algebra.IsAlgebraic.trans (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : IsAlgClosure (v.adicCompletion K) (Kbar v') := ⟨inferInstance, inferInstance⟩
  let b₀ : Kbar v ≃ₐ[v.adicCompletion K] Kbar v' := IsAlgClosure.equiv (v.adicCompletion K) (Kbar v) (Kbar v')
  have hb₀ : ∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) = algebraMap (v'.adicCompletion L) (Kbar v') (f x) :=
    fun x => (b₀.commutes x).trans rfl
  have hint := GlobalTheory.T.residue_closure_iso_ramified_ext K L v v' e f he hfv hfd b₀.toRingEquiv hb₀
  let ι₂ : Ω →ₐ[K] Kbar v :=
    { (b₀.symm.toRingEquiv.toRingHom.comp ι'.toRingHom) with
      commutes' := fun x => by
        change b₀.symm (ι' (algebraMap K Ω x)) = algebraMap K (Kbar v) x
        rw [IsScalarTower.algebraMap_apply K L Ω, ι'.commutes,
          IsScalarTower.algebraMap_apply L (v'.adicCompletion L) (Kbar v'), ← hfK, ← hb₀,
          AlgEquiv.symm_apply_apply, ← IsScalarTower.algebraMap_apply] }
  have hι₂ : IsLocEmb A v ι₂ := fun z => by
    rw [hι' z, hint]
    change IsIntegral _ (ι' z) ↔ IsIntegral _ (b₀ (b₀.symm (ι' z)))
    rw [AlgEquiv.apply_symm_apply]
  obtain ⟨σ, hσ, hσι⟩ := GlobalTheory.T.local_embeddings_differ_by_decomposition K Ω A v ι ι₂ hι hι₂
  obtain ⟨θ, -, -, hθ⟩ := GlobalTheory.T.decomposition_group_local_galois_iso K Ω A v h ι hι
  let g := θ ⟨σ, hσ⟩
  have hg : ∀ z, g (ι z) = b₀.symm (ι' z) := fun z => (hθ ⟨σ, hσ⟩ z).trans (hσι z).symm
  refine ⟨f, g.toRingEquiv.trans b₀.toRingEquiv, hfc, fun x => ?_, fun z => ?_, hfK, hrank, hcont.1,
    fun z => (htn z).1, hcont.2, fun z => (htn z).2⟩
  · change b₀ (g (algebraMap _ _ x)) = _
    rw [g.commutes, hb₀]
  · change b₀ (g (ι z)) = _
    rw [hg, AlgEquiv.apply_symm_apply]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyIsoOfEquivariantHomIntoIsotypicSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.IsoRankMult

open GlobalTheory.RepCount in
theorem iso_of_hom_into_sum : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X), σ0.IsIrreducible → σ.IsIrreducible → ∀ f ∈ homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g), f ≠ 0 → Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) := by
  intro H S0 S X _ _ _ _ _ _ _ σ0 σ ρ C h0 h1 f hf hne
  let R := MonoidAlgebra ℂ H
  haveI : IsSimpleModule R σ0.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ0).mp h0
  haveI : IsSimpleModule R σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp h1

  let N' : Submodule R ρ.asModule :=
    ⨆ (g : S0 →ₗ[ℂ] X) (hg : g ∈ homInto σ0 ρ C), LinearMap.range (modMap g hg.2)
  have hN'iso : N' ≤ isotypicComponent R ρ.asModule σ0.asModule := by
    refine iSup₂_le fun g hg => ?_
    rcases LinearMap.injective_or_eq_zero (modMap (σ := σ0) (ρ := ρ) g hg.2) with hi | hz
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · rw [hz, LinearMap.range_zero]; exact bot_le
  have hsub : (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ≤
      (N'.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨s, rfl⟩
    have hmem : modMap (σ := σ0) (ρ := ρ) g hg.2 (σ0.asModuleEquiv.symm s) ∈ N' :=
      (le_iSup₂_of_le (f := fun (g : S0 →ₗ[ℂ] X) (hg : g ∈ homInto σ0 ρ C) =>
        LinearMap.range (modMap (σ := σ0) (ρ := ρ) g hg.2)) g hg le_rfl) ⟨_, rfl⟩
    show ρ.asModuleEquiv.symm (g s) ∈ N'
    convert hmem using 1
    apply ρ.asModuleEquiv.injective
    rw [modMap_apply]; simp
  let F := modMap (σ := σ) (ρ := ρ) f hf.2
  have hFi : Function.Injective F := by
    rcases LinearMap.injective_or_eq_zero F with hi | hz
    · exact hi
    · exfalso; apply hne
      ext s
      have := congrArg (fun φ => ρ.asModuleEquiv (φ (σ.asModuleEquiv.symm s))) hz
      simp only [F, modMap_apply, LinearMap.zero_apply, map_zero] at this
      simpa using this
  have hle : LinearMap.range F ≤ isotypicComponent R ρ.asModule σ0.asModule := by
    refine le_trans ?_ hN'iso
    rintro _ ⟨x, rfl⟩
    have hx := hsub (hf.1 (σ.asModuleEquiv x))
    have : ρ.asModuleEquiv.symm (f (σ.asModuleEquiv x)) = F x := by
      apply ρ.asModuleEquiv.injective; simp [F, modMap_apply]
    rw [← this]; exact hx
  let e := LinearEquiv.ofInjective F hFi
  haveI : IsSimpleModule R (LinearMap.range F) := IsSimpleModule.congr e.symm
  obtain ⟨e'⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R ρ.asModule σ0.asModule) (LinearMap.range F) hle
  exact ⟨e.trans e'⟩

end GlobalTheory.IsoRankMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyWdSideOfTie
section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.Pst

theorem exists_bridges (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (hpl : ∀ w, IsPlaceOver (pl w) w) :
    ∃ (LL : FinExt l) (br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) ↥(OL LL)),
      ∀ w hw, Induces (br w hw) := by
  have hfin : (placesOver E l).Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
      simpa using (Fact.out : l.Prime).ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.mpr hv
  have := hfin.to_subtype
  choose j L0 hj hL using fun w : placesOver E l => GlobalTheory.PlaceBridge.exists_locBridge l E Ω w.1 (pl w.1) w.2 (hpl w.1)
  have := fun w => (L0 w).2
  let LL : FinExt l := ⟨⨆ w, (L0 w).1, inferInstance⟩
  choose br hb using fun w => hL w LL (le_iSup (fun w => (L0 w).1) w)
  exact ⟨LL, fun w hw => br ⟨w, hw⟩, fun w hw x => by rw [(hb _).1]; exact hj ⟨w, hw⟩ x⟩

theorem localPreds_of_isModel {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
    {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
    (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw))
    {m : ℕ} {r : G E Ω →* GL (Fin m) (Om l)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ placesOver E l) (B : LocBridge l E Ω (Dec (F := E) (pl w)) O') (hB : Induces B)
    {L : FinExt l} {r' : ↥(Dec (F := E) (pl w)) →* GL (Fin m) ↥L.1}
    (h : IsModel B (resDec pl r w) L r') :
    (IsCrysW P pl br r w ↔ B.IsCrysE P L r') ∧
    (IsdRW P pl br r w ↔ B.IsdRE P L r') ∧
    (IsPotCrysW P pl br r w ↔ B.IsPotCrysE P L r') ∧
    ∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced B τ τ' →
      (B.IsdRE P L r' → ∀ a : ℤ, a ∈ jumpsW P pl br r τ ↔ B.IsJumpE P L r' τ' a) ∧
      (B.IsdRE P L r' → ∀ a : ℤ, ((jumpsW P pl br r τ).count a : ℤ) = B.multE P L r' τ' a) := by
  have := L.2
  have := (br w hw).LL.2
  let L' : FinExt l := ⟨L.1 ⊔ (br w hw).LL.1, inferInstance⟩
  have l₁ : L.1 ≤ L'.1 := le_sup_left
  have l₂ : (br w hw).LL.1 ≤ L'.1 := le_sup_right
  have h' : IsModel (br w hw) (resDec pl r w) L' (mapRep (IntermediateField.inclusion l₁).toRingHom r') :=
    ⟨l₂, (h.enlarge l₁).2⟩
  obtain ⟨a₁, b₁, c₁, d₁⟩ := local_of_isModel P hpl hbr h'
  obtain ⟨a₂, b₂, c₂, d₂⟩ := bridge_indep l P E Ω (pl w) O O' (br w hw) B (hbr w hw) hB L' l₂ m (mapRep (IntermediateField.inclusion l₁).toRingHom r')
  obtain ⟨a₃, b₃, c₃, d₃⟩ := local_ext P B l₁ r'
  have key : ∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced B τ τ' → B.IsdRE P L r' →
      ∀ a : ℤ, ((jumpsW P pl br r τ).count a : ℤ) = B.multE P L r' τ' a := fun τ τ' hτ hd a => by
    obtain ⟨τ₁, t₁, e⟩ := d₂ τ ((IntermediateField.inclusion l₁).comp τ') hτ
    rw [(d₁ τ τ₁ t₁).2 (b₂.2 (b₃.2 hd)), e, d₃]
  refine ⟨a₁.trans (a₂.trans a₃), b₁.trans (b₂.trans b₃), c₁.trans (c₂.trans c₃), fun τ τ' hτ => ⟨fun hd a => ?_, key τ τ' hτ⟩⟩
  rw [isJumpE_iff P hd, ← key τ τ' hτ hd a, ← Multiset.count_ne_zero]
  exact Nat.cast_ne_zero.symm

theorem localPreds_of_bridge {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
    {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
    (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ placesOver E l) (B : LocBridge l E Ω (Dec (F := E) (pl w)) O') (hB : Induces B)
    (φ : O' →+* Om l) (hφ : ∀ x, φ x = ((B.toLL x : ↥B.LL.1) : Om l)) :
    (∀ (m : ℕ) (ρ : G E Ω →* GL (Fin m) O'),
      (IsCrysW P pl br (mapRep φ ρ) w ↔ B.IsCrysW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsdRW P pl br (mapRep φ ρ) w ↔ B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsPotCrysW P pl br (mapRep φ ρ) w ↔ B.IsPotCrysW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥B.LL.1), IsInduced B τ τ' →
        (B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          a ∈ jumpsW P pl br (mapRep φ ρ) τ ↔ B.IsJumpW P (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a) ∧
        (B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          ((jumpsW P pl br (mapRep φ ρ) τ).count a : ℤ) = B.multW P (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a))) ∧
    ∀ (LL' : FinExt l), B.LL.1 ≤ LL'.1 → ∀ (m : ℕ) (ρ : G E Ω →* GL (Fin m) ↥LL'.1),
      (IsCrysW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsCrysE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsdRW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsPotCrysW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsPotCrysE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced B τ τ' →
        (B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          a ∈ jumpsW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) τ ↔ B.IsJumpE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a) ∧
        (B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          ((jumpsW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) τ).count a : ℤ) =
            B.multE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a)) := by
  refine ⟨fun m ρ => ?_, fun LL' hL m ρ => ?_⟩
  · have h : IsModel B (resDec pl (mapRep φ ρ) w) B.LL (mapRep B.toLL (ρ.comp (Dec (F := E) (pl w)).subtype)) :=
      ⟨le_rfl, by ext g i j; exact (hφ _).symm⟩
    obtain ⟨a, b, c, d⟩ := localPreds_of_isModel P hpl hbr hw B hB h
    exact ⟨a, b, c, d⟩
  · have h : IsModel B (resDec pl (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w) LL' (ρ.comp (Dec (F := E) (pl w)).subtype) := ⟨hL, rfl⟩
    exact localPreds_of_isModel P hpl hbr hw B hB h


set_option maxHeartbeats 1000000 in
theorem nonempty_wdSide_of_tie (hB : GlobalTheory.Published.DeRhamPotSemistable) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Nonempty (WDSide D T) := by
  classical
  choose LL br hbr using fun (l : ℕ) (hl : Fact l.Prime) => exists_bridges l D.host.E D.nd.Om D.nd.plOm.1 D.nd.plOm.2
  let wd : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → ∀ w, D.naut.LP w :=
    fun l hl ι a r w => (T.e w).symm (if hw : w ∈ placesOver D.host.E l then
      wdL (D.loc l) ι D.nd.plOm.1 (br l hl) r D.nd.plOm.2 (hbr l hl) w hw else GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r)
  have h1 : ∀ (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
      (hw : w ∈ placesOver D.host.E l), T.e w (wd l ι r w) = wdL (D.loc l) ι D.nd.plOm.1 (br l hl) r D.nd.plOm.2 (hbr l hl) w hw :=
    fun l hl ι a r w hw => by simp only [wd, Equiv.apply_symm_apply, dif_pos hw]
  have h2 : ∀ (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
      (hw : w ∉ placesOver D.host.E l), T.e w (wd l ι r w) = GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r :=
    fun l hl ι a r w hw => by simp only [wd, Equiv.apply_symm_apply, dif_neg hw]
  have hL := fun (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w hw =>
    GlobalTheory.PstLaws.wdL_laws hB l (D.loc l) (D.locA l) (D.locT l) ι D.host.E D.nd.Om _ D.nd.plOm.1 (br l hl) D.nd.plOm.2 (hbr l hl) r w hw
  have hA := fun (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
    (hw : w ∉ placesOver D.host.E l) => GlobalTheory.WeilDeligne.wdOf_laws (D.nd.plOm.2 w) hw ι r
  refine ⟨{
    wdOf := wd
    wdOf_dim := fun l hl ι a r w => ?_
    wdOf_unr := fun l hl ι a r w hw hc => by rw [T.unr, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.1
    wdOf_frob := fun l hl ι a r w hw hc hu B σ hp hσ => ?_
    wdOf_ine := fun l hl ι a r w hw hc σ hσ => by rw [T.inePol _ _ σ hσ, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.2.2.1 σ hσ
    wdOf_mono0 := fun l hl ι a r w hw hc => by rw [T.mono0, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.2.2.2
    IsCrysW := fun l hl _ _ r w => IsCrysW (D.loc l) D.nd.plOm.1 (br l hl) r w
    IsPotCrysW := fun l hl _ _ r w => IsPotCrysW (D.loc l) D.nd.plOm.1 (br l hl) r w
    IsdRW := fun l hl _ _ r w => IsdRW (D.loc l) D.nd.plOm.1 (br l hl) r w
    jumpsW := fun l hl _ _ r τ => jumpsW (D.loc l) D.nd.plOm.1 (br l hl) r τ
    wdOf_unrL := fun l hl ι a r w hw hc hd => by rw [T.unr, h1 l ι r w hw]; exact ((hL l ι r w hw).2 hc hd).1
    wdOf_mono0L := fun l hl ι a r w hw hc hd => by rw [T.mono0, h1 l ι r w hw]; exact ((hL l ι r w hw).2 hc hd).2
    away := fun l hl ι a r w hw => h2 l ι r w hw
    above := fun l hl ι a r w hw => ⟨LL l hl, br l hl w hw, hbr l hl w hw, h1 l ι r w hw⟩
    loc := fun l hl ι w hw O _ _ _ Bw hj φ hφ => ⟨fun m ρ _ => ?_, fun LL' hL' m ρ _ => ?_⟩ }⟩
  · rw [← T.dim]
    by_cases hw : w ∈ placesOver D.host.E l
    · rw [h1 l ι r w hw]; exact (hL l ι r w hw).1
    · rw [h2 l ι r w hw]; exact (hA l ι r w hw).1
  · rw [T.frobEig _ _ hu, h2 l ι r w hw]
    rw [T.unr, h2 l ι r w hw] at hu
    exact ((hA l ι r w hw).2 hc).2.2.2.1 hu B σ hp hσ
  · exact (localPreds_of_bridge (D.loc l) D.nd.plOm.2 (hbr l hl) hw Bw hj φ hφ).1 m ρ
  · exact (localPreds_of_bridge (D.loc l) D.nd.plOm.2 (hbr l hl) hw Bw hj φ hφ).2 LL' hL' m ρ

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieDirectSum
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PolyRep

theorem lie_sum {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R]
    (A : Mat m R) :
    (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  ext i j
  simp only [lie, Matrix.of_apply]
  change Fin (ρ.M + σ.M) at i j
  change ∑ v : EntIx m, aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2)
      (pderiv v (blockSum ρ.ent σ.ent i j)) * A v.1 v.2.1 v.2.2 = _
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rcases x with x | x <;> rcases y with y | y <;> simp [lie, sum, blockSum]

end GlobalTheory.GoodMetric.PolyRep
end
end

