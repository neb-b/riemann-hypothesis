module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterAdelicGLEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0705
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0707
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0703
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfCharOfCharOfHasInfQ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import GroundTheory.PAdicHodge.AInfGalois

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightInvariantHaarLevi
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def levPair : GA D W × GL (Fin t) (AE D) →* levM d where
  toFun p := ⟨⟨d.emb0 p.1 * d.levi p.2, mul_mem (GlobalTheory.GodementSectionReduction.wittCoreEmbedding_mem_isotropicStabilizer d _) (GlobalTheory.RegSW.levi_mem d _)⟩, p.1, p.2, rfl⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' p q := Subtype.ext (Subtype.ext (by
    show d.emb0 (p.1 * q.1) * d.levi (p.2 * q.2) = d.emb0 p.1 * d.levi p.2 * (d.emb0 q.1 * d.levi q.2)
    rw [map_mul, map_mul]
    calc d.emb0 p.1 * d.emb0 q.1 * (d.levi p.2 * d.levi q.2)
        = d.emb0 p.1 * (d.emb0 q.1 * d.levi p.2) * d.levi q.2 := by group
      _ = d.emb0 p.1 * (d.levi p.2 * d.emb0 q.1) * d.levi q.2 := by rw [d.wittHyperbolic_anisotropic_commute_levi]
      _ = _ := by group))

theorem coe_levPair (p : GA D W × GL (Fin t) (AE D)) :
    (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) = d.emb0 p.1 * d.levi p.2 := rfl

theorem mt_eq_of_levPair (p : GA D W × GL (Fin t) (AE D)) :
    d.p0 ⬝ (mt B (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.j0) = mt W p.1 := by
  rw [coe_levPair, mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul]

theorem onX_levPair (p : GA D W × GL (Fin t) (AE D)) :
    GlobalTheory.RegSW.onX d ((levPair d p : levM d) : GlobalTheory.RegSW.stab d) = p.2 := by
  have h : mt B (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.jX = d.jX ⬝ p.2.1 := by
    rw [coe_levPair, mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
  exact Units.ext ((GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d _)).trans (GlobalTheory.RegSW.eq_of_mul_jX d h).symm)

theorem levPair_bijective : Function.Bijective (levPair d) := by
  constructor
  · intro p q h
    refine Prod.ext (mt_injective W ?_) ?_
    · rw [← mt_eq_of_levPair d p, ← mt_eq_of_levPair d q, h]
    · rw [← onX_levPair d p, ← onX_levPair d q, h]
  · rintro ⟨⟨q, hq⟩, g, a, e⟩
    exact ⟨(g, a), Subtype.ext (Subtype.ext e.symm)⟩

def levEquiv : (GA D W × GL (Fin t) (AE D)) ≃* levM d := MulEquiv.ofBijective (levPair d) (levPair_bijective d)

theorem continuous_levEquiv : Continuous (levEquiv d) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have h : Continuous fun p : GA D W × GL (Fin t) (AE D) => d.emb0 p.1 * d.levi p.2 :=
    (d.continuous_embed.comp continuous_fst).mul (d.continuous_levi.comp continuous_snd)
  exact (h.subtype_mk _).subtype_mk _

theorem continuous_levEquiv_symm : Continuous (levEquiv d).symm := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hv : Continuous fun m : levM d => ((m : GlobalTheory.RegSW.stab d) : GA D B) :=
    continuous_subtype_val.comp continuous_subtype_val
  refine Continuous.prodMk (continuous_of_mt W ?_) ?_
  · have hc : Continuous fun m : levM d => d.p0 ⬝ (mt B ((m : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.j0) :=
      continuous_const.matrix_mul (((continuous_mt B).comp hv).matrix_mul continuous_const)
    refine hc.congr fun m => ?_
    have := mt_eq_of_levPair d ((levEquiv d).symm m)
    rwa [show levPair d ((levEquiv d).symm m) = m from (levEquiv d).apply_symm_apply m] at this
  · refine ((GlobalTheory.RegSW.continuous_onX d).comp continuous_subtype_val).congr fun m => ?_
    have := onX_levPair d ((levEquiv d).symm m)
    rwa [show levPair d ((levEquiv d).symm m) = m from (levEquiv d).apply_symm_apply m] at this

end GlobalTheory.CompanionTheory.QKAvg

theorem GlobalTheory.CompanionTheory.QKAvg.exists_haar_of_prod {G₁ G₂ M : Type} [Group G₁] [Group G₂] [Group M] [TopologicalSpace G₁]
    [TopologicalSpace G₂] [TopologicalSpace M] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [IsTopologicalGroup M]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂] [SecondCountableTopology G₁] [SecondCountableTopology G₂]
    [T2Space G₂] [MeasurableSpace G₁] [BorelSpace G₁] [MeasurableSpace M] [BorelSpace M]
    (e : (G₁ × G₂) ≃* M) (he : Continuous e) (he' : Continuous e.symm)
    (h₁ : ∀ μ : Measure G₁, μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (h₂ : ∀ a : G₂, Measure.modularCharacterFun a = 1) :
    ∃ νM : Measure M, νM.IsHaarMeasure ∧ νM.IsMulRightInvariant := by
  borelize G₂
  haveI hr1 : (Measure.haar : Measure G₁).IsMulRightInvariant := h₁ _ inferInstance
  haveI hr2 : (Measure.haar : Measure G₂).IsMulRightInvariant := GlobalTheory.ParAvg.isMulRightInvariant_of_modular _ h₂
  obtain ⟨ν, hνH, hνR⟩ : ∃ ν : Measure (G₁ × G₂), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant :=
    ⟨(Measure.haar : Measure G₁).prod Measure.haar, inferInstance, inferInstance⟩
  refine ⟨Measure.map e ν, MulEquiv.isHaarMeasure_map ν e he he', ⟨fun m => ?_⟩⟩
  obtain ⟨p, rfl⟩ := e.surjective m
  rw [Measure.map_map (measurable_mul_const _) he.measurable]
  have h : (fun x => x * e p) ∘ e = e ∘ fun x => x * p := by
    funext x; simp [map_mul]
  rw [h, ← Measure.map_map he.measurable (measurable_mul_const _), map_mul_right_eq_self]


set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.CompanionTheory.QKAvg.top_GL (D : D7) (t : ℕ) : LocallyCompactSpace (GL (Fin t) (AE D)) ∧
    SecondCountableTopology (GL (Fin t) (AE D)) ∧ T2Space (GL (Fin t) (AE D)) := by
  obtain ⟨-, m2, m3, m4, -⟩ := lattice_Mx D t t
  haveI : LocallyCompactSpace (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : T2Space (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.t2Space
  haveI : T1Space (Mx D t t) := @T2Space.t1Space _ _ m4
  exact ⟨(Units.isClosedEmbedding_embedProduct (α := Mx D t t)).locallyCompactSpace,
    (Units.isEmbedding_embedProduct (M := Mx D t t)).secondCountableTopology,
    (Units.isEmbedding_embedProduct (M := Mx D t t)).t2Space⟩

theorem GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (levM d)],
    ∃ νM : Measure (levM d), νM.IsHaarMeasure ∧ νM.IsMulRightInvariant := by
  intro D B W t d _
  obtain ⟨g1, g2, g3, g4, g5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨l1, l2, l3⟩ := GlobalTheory.CompanionTheory.QKAvg.top_GL D t
  exact GlobalTheory.CompanionTheory.QKAvg.exists_haar_of_prod (levEquiv d) (continuous_levEquiv d) (continuous_levEquiv_symm d)
    (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W) (_root_.GlobalTheory.CompanionTheory.GLUnimod.modularCharacterFun_GL_adele D t)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalPairTyped
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.FdPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_eq_prodSpan (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ = prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro F ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩
  · refine Submodule.span_mono ?_
    rintro F ⟨_, ⟨φ₁, h₁, rfl⟩, _, ⟨φ₂, h₂, rfl⟩, rfl⟩
    exact ⟨φ₁, h₁, φ₂, h₂, rfl⟩

theorem map_typed {N : ℕ} (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E)))
    (W : Submodule ℂ (Kinf E N → ℂ)) :
    U.map (Sm E N).subtype ⊓ typeF K W = (typed U K W).map (Sm E N).subtype := by
  ext f
  constructor
  · rintro ⟨⟨φ, hφ, rfl⟩, hS⟩
    exact ⟨φ, ⟨hφ, hS⟩, rfl⟩
  · rintro ⟨φ, ⟨hφ, hS⟩, rfl⟩
    exact ⟨⟨φ, hφ, rfl⟩, hS⟩

theorem slice_left {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (y : GA E b) : (fun x => F (x, y)) ∈ typeF K₁ W₁ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have := hF.1 u hu 1 K₂.one_mem (g, y)
    simpa using this
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
      { toFun := fun f k => f (k, 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hL : Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}
        ≤ W₁.comap L := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨w₁, h₁, w₂, h₂, rfl⟩
      have : L (fun k => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁ := by
        funext k
        simp [L, mul_comm]
      show L _ ∈ W₁
      rw [this]
      exact W₁.smul_mem _ h₁
    have := hL (hF.2 (g, y))
    simpa [L] using this

theorem slice_right {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (x : GA E a) : (fun y => F (x, y)) ∈ typeF K₂ W₂ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have := hF.1 1 K₁.one_mem u hu (x, g)
    simpa using this
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ) :=
      { toFun := fun f k => f (1, k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hL : Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}
        ≤ W₂.comap L := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨w₁, h₁, w₂, h₂, rfl⟩
      have : L (fun k => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂ := by
        funext k
        simp [L]
      show L _ ∈ W₂
      rw [this]
      exact W₂.smul_mem _ h₂
    have := hL (hF.2 (x, g))
    simpa [L] using this

theorem finiteDimensional_pairSpace_inf_typeHF : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E)))
    (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)),
    FiniteDimensional ℂ (typed U₁ K₁ W₁) → FiniteDimensional ℂ (typed U₂ K₂ W₂) →
    FiniteDimensional ℂ ((pairSpace U₁ U₂ ⊓ typeHF K₁ K₂ W₁ W₂ : Submodule ℂ (H E a b → ℂ))) := by
  intro E _ _ _ a b U₁ U₂ K₁ K₂ W₁ W₂ h₁ h₂
  have f₁ : FiniteDimensional ℂ (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁ : Submodule ℂ (GA E a → ℂ)) := by
    rw [map_typed]; infer_instance
  have f₂ : FiniteDimensional ℂ (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂ : Submodule ℂ (GA E b → ℂ)) := by
    rw [map_typed]; infer_instance
  haveI hfd := _root_.GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁) (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂) f₁ f₂
  refine Submodule.finiteDimensional_of_le (S₂ := prodSpan (U₁.map (Sm E a).subtype ⊓ typeF K₁ W₁)
    (U₂.map (Sm E b).subtype ⊓ typeF K₂ W₂)) ?_
  rintro F ⟨hU, hT⟩
  rw [SetLike.mem_coe, pairSpace_eq_prodSpan] at hU
  exact _root_.GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices _ _ _ _ F hU (fun y => slice_left hT y) (fun x => slice_right hT x)

end GlobalTheory.CompanionTheory.LimV.FdPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedNode
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.FdNode

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N r s : ℕ}

theorem memInd2_of_mem_indSpan {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indSpan U₁ U₂) : MemInd2 U₁ U₂ φ := by
  unfold indSpan at h
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => (tens2 U₁ U₂).zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => (tens2 U₁ U₂).add_mem (hx.2 k g) (hy.2 k g)⟩
    change x.1 _ + y.1 _ = x.1 _ + y.1 _
    rw [hx.1, hy.1]
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => (tens2 U₁ U₂).smul_mem c (hx.2 k g)⟩
    change c • x.1 _ = c • x.1 _
    rw [hx.1]

def sliceMap (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) :
    Sm E (r + s) →ₗ[ℂ] (GA E r × GA E s → ℂ) where
  toFun φ m := φ.1 (lev (Ad E) r s m * cf (r + s) k t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tensor_le_prodSpan (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) :
    tens2 U₁ U₂ ≤ prodSpan (U₁.map (Sm E r).subtype) (U₂.map (Sm E s).subtype) := by
  refine Submodule.span_le.2 ?_
  rintro F ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact Submodule.subset_span ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩

theorem fd_inf (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (h : FiniteDimensional ℂ (typed U K W)) :
    FiniteDimensional ℂ ↥(U.map (Sm E N).subtype ⊓ typeF K W) := by
  have hle : U.map (Sm E N).subtype ⊓ typeF K W ≤ (typed U K W).map (Sm E N).subtype := by
    rintro f ⟨⟨φ, hφ, rfl⟩, hf⟩
    exact ⟨φ, ⟨hφ, hf⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end SlopeTestRemainingChoices

theorem finiteDimensional_typed_indSpan : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), (∀ (K : Subgroup (GL (Fin r) (Af E))) (W : Submodule ℂ (Kinf E r → ℂ)), IsOpen (K : Set (GL (Fin r) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₁ K W)) → (∀ (K : Subgroup (GL (Fin s) (Af E))) (W : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K : Set (GL (Fin s) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₂ K W)) → ∀ (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed (indSpan U₁ U₂) K W) := by
  intro E _ _ _ r s U₁ U₂ h₁ h₂ K W hK hW
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s K hK
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points W hW
  choose K₁ W₁ oK₁ fW₁ sl₁ using
    fun i : Kinf E (r + s) × GL (Fin (r + s)) (Af E) => _root_.GlobalTheory.CompanionTheory.LimV.SliceL.slice_typeF i.1 i.2 K W hK hW
  choose K₂ W₂ oK₂ fW₂ sl₂ using
    fun i : Kinf E (r + s) × GL (Fin (r + s)) (Af E) => _root_.GlobalTheory.CompanionTheory.LimV.SliceR.slice_right i.1 i.2 K W hK hW
  let P : ↥S × ↥T → Submodule ℂ (GA E r × GA E s → ℂ) := fun i =>
    prodSpan (U₁.map (Sm E r).subtype ⊓ typeF (K₁ (i.1.1, i.2.1)) (W₁ (i.1.1, i.2.1)))
      (U₂.map (Sm E s).subtype ⊓ typeF (K₂ (i.1.1, i.2.1)) (W₂ (i.1.1, i.2.1)))
  haveI : ∀ i, FiniteDimensional ℂ (P i) := fun i =>
    _root_.GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd _ _ (fd_inf _ _ _ (h₁ _ _ (oK₁ _) (fW₁ _))) (fd_inf _ _ _ (h₂ _ _ (oK₂ _) (fW₂ _)))
  have hmem : ∀ (i : ↥S × ↥T) (φ : typed (indSpan U₁ U₂) K W), sliceMap i.1.1 i.2.1 φ.1 ∈ P i := by
    intro i φ
    have hmi := memInd2_of_mem_indSpan φ.2.1
    exact _root_.GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices _ _ _ _ _ (tensor_le_prodSpan U₁ U₂ (hmi.2 i.1.1 i.2.1))
      (fun y => sl₁ (i.1.1, i.2.1) _ φ.2.2 y) (fun x => sl₂ (i.1.1, i.2.1) _ φ.2.2 x)
  let Φ : typed (indSpan U₁ U₂) K W →ₗ[ℂ] ∀ i, P i := LinearMap.pi fun i =>
    ((sliceMap i.1.1 i.2.1).comp (Submodule.subtype _)).codRestrict (P i) (hmem i)
  refine FiniteDimensional.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun φ hφ => ?_)
  have hz : ∀ a ∈ S, ∀ t ∈ T, ∀ m, φ.1.1 (lev (Ad E) r s m * cf (r + s) a t) = 0 := by
    intro a ha t ht m
    have e := congrArg Subtype.val (congrFun hφ (⟨a, ha⟩, ⟨t, ht⟩))
    exact congrFun e m
  have hmi := memInd2_of_mem_indSpan φ.2.1
  have hty : φ.1.1 ∈ typeF K W := φ.2.2
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  obtain ⟨x, m, t, k, l, ht, hl, rfl⟩ := hT g
  have e : unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l =
      unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) * finGL E (r + s) l := by
    simp only [mul_assoc]
  rw [e, hty.1 l hl, hmi.1]
  have hw := hS _ (hty.2 (lev (Ad E) r s m * finGL E (r + s) t)) (fun a ha => by
    have h0 := hz a ha t ht m
    rw [cf, infGL_comm, ← mul_assoc] at h0
    exact h0)
  exact congrFun hw k

end GlobalTheory.CompanionTheory.LimV.FdNode

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneEuler
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero

open GlobalTheory.CompanionTheory.SW.Growth

section Abstract
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M : ℕ}

theorem growth_of_scale (b : Module.Basis (Fin d) F E)
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hscale : ∀ (v : HeightOneSpectrum (𝓞 F)) (a e : ℕ), 0 < a → Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e →
      ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1) →
      μ v (dilSet b v a) = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) * μ v (latV b v))
    (hfin : ∀ v, μ v (latV b v) < ⊤)
    (hsum : Summable fun v => |(μ v (latV b v)).toReal - 1|)
    (hne : ∀ v, μ v ≠ 0) :
    (∀ a : ℕ, 0 < a → ∀ v, μ v (dilSet b v a) < ⊤) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧
        κ * (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) ≤ ∏' v, (μ v (dilSet b v a)).toReal := by
  have hdil : ∀ (a : ℕ), 0 < a → ∀ v, μ v (dilSet b v a) < ⊤ := by
    intro a ha v
    obtain ⟨e, he, -, -⟩ := exists_exponents (F := F) a ha
    rw [hscale v a (e v) ha (he v).1 (he v).2]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin v)
  have hpos : ∀ v, 0 < (μ v (latV b v)).toReal := by
    intro v
    obtain ⟨n, hn, hnz⟩ := exists_pos_mass b v (μ v) (hne v)
    obtain ⟨e, he, -, -⟩ := exists_exponents (F := F) n hn
    have hz : μ v (latV b v) ≠ 0 := by
      intro h0
      rw [hscale v n (e v) hn (he v).1 (he v).2, h0, mul_zero] at hnz
      exact hnz rfl
    exact ENNReal.toReal_pos hz (hfin v).ne
  obtain ⟨hmulL, -, hprodpos, -⟩ := GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ (fun v => (μ v (latV b v)).toReal) hsum
  refine ⟨hdil, ∏' v, (μ v (latV b v)).toReal, hprodpos hpos, fun k => ⟨k + 1, Nat.lt_succ_self k, ?_⟩⟩
  set a := k + 1 with hadef
  have ha : 0 < a := Nat.succ_pos k
  obtain ⟨e, he, hfs, hprod⟩ := exists_exponents (F := F) a ha
  have hid : ∀ v, (μ v (dilSet b v a)).toReal =
      (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2) * (μ v (latV b v)).toReal := by
    intro v
    rw [hscale v a (e v) ha (he v).1 (he v).2, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), pow_mul]
  have hf2 : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2)) :=
    hfs.fun_comp (g := fun y : ℝ => y ^ (2 * M - 2)) (one_pow _)
  have hmul : Multipliable
      (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2)) :=
    (hasProd_prod_of_ne_finset_one (s := Set.Finite.toFinset hf2) (fun v hv =>
      by_contra fun h => hv ((Set.Finite.mem_toFinset hf2).2 h))).multipliable
  rw [tprod_congr hid, hmul.tprod_mul hmulL, tprod_eq_finprod hf2, ← finprod_pow hfs, hprod, ← pow_mul,
    mul_comm]

end Abstract

theorem growth_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) → (∀ a : ℕ, 0 < a → ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} < ⊤) ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧ κ * (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) ≤ ∏' v, (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b lam hlam m hm hne
  obtain ⟨hfin, hsum⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.mass_free_summable F E σ hσ M J hJ hM h₀ d b lam hlam m hm
  have hscale := fun (v : HeightOneSpectrum (𝓞 F)) (a e : ℕ) (ha : 0 < a) h1 h2 =>
    _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero.mass_dilated_lattice F E σ hσ M J hJ hM h₀ d b v (lam v) (hlam v) (m v) (hm v) a e ha h1 h2
  exact growth_of_scale b (fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))
    hscale hfin hsum hne

end GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisRepresentationAdmitted
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.HeckeAlg

open GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem dchi_atEmb (χ : HChar E) (τ : E →+* ℂ) (z : ℂ) :
    dchi χ (atEmb τ z) = expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [atEmb_eq, map_add (f := _), map_smul, map_smul]
  simp only [expo, atEmb_conj, map_one, Complex.conj_I, e, map_neg, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (z.im * dchi χ (atEmb τ Complex.I)) * Complex.I_mul_I

theorem dchi_eq_sum (χ : HChar E) (z : Cinf E) : dchi χ z = ∑ φ : E →+* ℂ, expo χ φ * coord φ z := by
  classical
  have hz : z = ∑ w : InfinitePlace E, atEmb w.embedding (z w) := by
    funext v
    rw [Finset.sum_apply, Finset.sum_eq_single v]
    · simp [atEmb, InfinitePlace.mk_embedding]
    · intro b _ hb
      simp [atEmb, InfinitePlace.mk_embedding, Pi.single_eq_of_ne hb.symm]
    · simp
  conv_lhs => rw [hz]
  conv_rhs => rw [hz]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dchi_atEmb]
  simp only [coord_atEmb', mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.CompanionTheory.HeckeAlg

namespace GlobalTheory.CompanionTheory.RankOneGal

open GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.Pst GlobalTheory.GalOfCusp
open Formalism.BasicNotions.Loc Neutral.B1

section Char

variable {E Ω : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]

end Char

end GlobalTheory.CompanionTheory.RankOneGal

namespace GlobalTheory.CompanionTheory.RankOneGal

open GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.Pst GlobalTheory.GalOfCusp
open Formalism.BasicNotions.Loc

end GlobalTheory.CompanionTheory.RankOneGal

end
end

