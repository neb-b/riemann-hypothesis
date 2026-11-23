module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0252

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarFiniteAdeleDisintegrationStabilizerCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.SfinHaar

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH Topology

theorem exists_idem_of_subspace {E : Type} [Field E] {n : ℕ} (W : Submodule E (Fin n → E)) :
    ∃ e : Matrix (Fin n) (Fin n) E, e * e = e ∧ ∀ x, x ∈ W ↔ e *ᵥ x = x := by
  obtain ⟨W', hc⟩ := W.exists_isCompl
  obtain ⟨p, hp⟩ : ∃ p : Matrix (Fin n) (Fin n) E, ∀ x, p *ᵥ x = Submodule.projection W W' hc x :=
    ⟨LinearMap.toMatrix' _, fun x => LinearMap.toMatrix'_mulVec _ x⟩
  have h1 : ∀ x, p *ᵥ x ∈ W := fun x => hp x ▸ Submodule.projection_apply_mem hc x
  have h2 : ∀ x ∈ W, p *ᵥ x = x := fun x hx => (hp x).trans (Submodule.projection_apply_of_mem_left hc hx)
  refine ⟨p, Matrix.ext_iff_mulVec.2 fun y => by rw [← Matrix.mulVec_mulVec, h2 _ (h1 y)], fun x =>
    ⟨fun hx => h2 x hx, fun hx => hx ▸ h1 x⟩⟩

theorem span_incl_eq (I : AutInst) (T : Set (Fin I.n → I.E)) :
    Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T) =
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
        ((fun w i => GlobalTheory.UnipApprox.inc I (w i)) '' (Submodule.span I.E T : Set (Fin I.n → I.E))) := by
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((0 : Fin I.n → I.E) i)) = 0 := by ext; simp
      beta_reduce; rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((x + y) i)) =
          (fun i => GlobalTheory.UnipApprox.inc I (x i)) + fun i => GlobalTheory.UnipApprox.inc I (y i) := by ext; simp
      rw [SetLike.mem_coe] at hx hy; beta_reduce at hx hy ⊢; rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((a • x) i)) =
          GlobalTheory.UnipApprox.inc I a • fun i => GlobalTheory.UnipApprox.inc I (x i) := by ext; simp
      rw [SetLike.mem_coe] at hx; beta_reduce at hx ⊢; rw [this]; exact Submodule.smul_mem _ _ hx

theorem isClosed_cond (I : AutInst) (v : Fin I.n → I.E) (T : Set (Fin I.n → I.E)) :
    IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I v ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T)} := by
  obtain ⟨t, hr, h2, -, -, -, hind⟩ := GlobalTheory.UnipApprox.exists_top I
  obtain ⟨e, he, hW⟩ := exists_idem_of_subspace (Submodule.span I.E T)
  have hset : {x : I.Gf | (I.fmat x - 1) *ᵥ incl I v ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T)} =
      {x | e.map (GlobalTheory.UnipApprox.inc I) *ᵥ ((I.fmat x - 1) *ᵥ incl I v) = (I.fmat x - 1) *ᵥ incl I v} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [span_incl_eq]
    exact GlobalTheory.UnipApprox.mem_span_iff (GlobalTheory.UnipApprox.inc I) he _ hW _
  rw [hset]
  have hc : Continuous fun x : I.Gf => I.fmat x := Units.continuous_val.comp hind.continuous
  have hc2 : Continuous fun x : I.Gf => (I.fmat x - 1) *ᵥ incl I v :=
    (hc.sub continuous_const).matrix_mulVec continuous_const
  exact isClosed_eq (continuous_const.matrix_mulVec hc2) hc2

theorem isClosed_sfin (I : AutInst) {r : ℕ} (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) :
    IsClosed (Sfin I e z) := by
  have h1 : ∀ a : Fin r, IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I (e a) ∈
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => incl I (e b)) '' {b | b.1 < a.1})} := by
    intro a
    have := isClosed_cond I (e a) (e '' {b : Fin r | b.1 < a.1})
    rwa [Set.image_image] at this
  have h2 : IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I z ∈
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => incl I (e b))} := by
    have := isClosed_cond I z (Set.range e)
    rwa [← Set.range_comp] at this
  unfold Sfin
  rw [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_iInter h1).inter h2

end GlobalTheory.SfinHaar

namespace GlobalTheory.SfinHaar

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH Topology MeasureTheory

theorem disint_finPart : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    ∃ μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), μSf.IsHaarMeasure ∧ SigmaFinite μSf ∧
      ∃ c : ℝ, 0 < c ∧ ∀ φ : X.B.I.Gf → ENNReal, Measurable φ →
        (∀ x, φ x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x = s * X.xu u * k) →
        ∫⁻ x, φ x ∂X.B.μf = ENNReal.ofReal c * ∫⁻ t, ∫⁻ k in X.K2, φ (t.1 * X.xu u * k) ∂X.B.μf ∂μSf := by
  intro D X u
  set G := X.B.I.Gf
  set S := Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u) with hSdef
  set K := X.K2 with hKdef
  set x := X.xu u with hxdef
  haveI : SecondCountableTopology G := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : X.B.μf.IsHaarMeasure := X.B.haar
  have hKg := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hKt := Formalism.L2.SG.Pf.level_subgroup_compact_open X
  have hK1 : (1 : G) ∈ K := hKg.1
  have hKmul : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K := hKg.2.1
  have hKinv : ∀ a ∈ K, a⁻¹ ∈ K := hKg.2.2.1
  have hKo : IsOpen K := hKt.1
  have hKc : IsCompact K := hKt.2
  haveI : LocallyCompactSpace G := hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds hK1)
  have hSc : IsClosed (S : Set G) := isClosed_sfin X.B.I X.eR (X.zR u)

  set C : Set G := {g | x⁻¹ * g * x ∈ K} with hCdef
  have hCeq : C = (fun k => x * k * x⁻¹) '' K := by
    ext g
    constructor
    · intro hg; exact ⟨x⁻¹ * g * x, hg, by group⟩
    · rintro ⟨k, hk, rfl⟩
      show x⁻¹ * (x * k * x⁻¹) * x ∈ K
      simpa [mul_assoc] using hk
  have hCc : IsCompact C := hCeq ▸ hKc.image ((continuous_const_mul _).mul continuous_const)
  have hCo : IsOpen C := hKo.preimage ((continuous_const_mul _).mul continuous_const)
  set H : Set S := Subtype.val ⁻¹' C with hHdef
  have hHc : IsCompact H := hSc.isClosedEmbedding_subtypeVal.isCompact_preimage hCc
  have hHo : IsOpen H := hCo.preimage continuous_subtype_val
  have hH1 : (1 : S) ∈ H := by
    show x⁻¹ * ((1 : S) : G) * x ∈ K
    simpa using hK1
  haveI : LocallyCompactSpace S := hHc.locallyCompactSpace_of_mem_nhds_of_group (hHo.mem_nhds hH1)
  let K₀ : TopologicalSpace.PositiveCompacts S := ⟨⟨H, hHc⟩, ⟨1, hHo.subset_interior_iff.2 le_rfl hH1⟩⟩
  set ν : Measure S := Measure.haarMeasure K₀ with hνdef
  haveI : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀
  have hνH : ν H = 1 := Measure.haarMeasure_self
  refine ⟨ν, inferInstance, inferInstance, 1, one_pos, fun φ hφ hsupp => ?_⟩
  rw [ENNReal.ofReal_one, one_mul]

  set Z : Set (S × G) := {p | x⁻¹ * ((p.1 : G)⁻¹ * p.2) ∈ K} with hZdef
  have hZo : IsOpen Z := hKo.preimage
    (continuous_const.mul ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd))
  have hZm : MeasurableSet Z := hZo.measurableSet
  have hKm : MeasurableSet K := hKo.measurableSet
  let F : S → G → ENNReal := fun t g => φ g * Z.indicator 1 (t, g)
  have hF : Measurable (Function.uncurry F) :=
    (hφ.comp measurable_snd).mul (measurable_one.indicator hZm)

  have hA : ∀ t : S, ∫⁻ g, F t g ∂X.B.μf = ∫⁻ k in K, φ ((t : G) * x * k) ∂X.B.μf := by
    intro t
    rw [← lintegral_mul_left_eq_self _ ((t : G) * x), ← lintegral_indicator hKm]
    refine lintegral_congr fun k => ?_
    have e : x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) = k := by group
    by_cases hk : k ∈ K
    · have : ((t, (t : G) * x * k) : S × G) ∈ Z := by show x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) ∈ K; rw [e]; exact hk
      simp only [F]
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hk, Pi.one_apply, mul_one]
    · have : ((t, (t : G) * x * k) : S × G) ∉ Z := by show ¬ x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) ∈ K; rw [e]; exact hk
      simp only [F]
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hk, mul_zero]

  have hC' : ∀ g, ∫⁻ t, F t g ∂ν = φ g := by
    intro g
    by_cases h0 : φ g = 0
    · simp [F, h0]
    obtain ⟨s, hs, k, hk, rfl⟩ := hsupp g h0
    have hset : {t : S | (t, s * x * k) ∈ Z} = (fun t => (⟨s, hs⟩ : S)⁻¹ * t) ⁻¹' H := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      show x⁻¹ * ((t : G)⁻¹ * (s * x * k)) ∈ K ↔ x⁻¹ * (s⁻¹ * (t : G)) * x ∈ K
      have e : x⁻¹ * ((t : G)⁻¹ * (s * x * k)) = (x⁻¹ * (s⁻¹ * (t : G)) * x)⁻¹ * k := by group
      rw [e]
      constructor
      · intro h
        have := hKinv _ (hKmul _ h _ (hKinv _ hk))
        simpa using this
      · intro h
        exact hKmul _ (hKinv _ h) _ hk
    have hmeas : MeasurableSet {t : S | (t, s * x * k) ∈ Z} :=
      hZm.preimage (measurable_id.prodMk measurable_const)
    calc ∫⁻ t, F t (s * x * k) ∂ν = ∫⁻ t, φ (s * x * k) * {t : S | (t, s * x * k) ∈ Z}.indicator 1 t ∂ν := by
          refine lintegral_congr fun t => ?_
          simp only [F]
          congr 1
      _ = φ (s * x * k) * ν {t : S | (t, s * x * k) ∈ Z} := by
          rw [lintegral_const_mul _ (measurable_one.indicator hmeas), lintegral_indicator_one hmeas]
      _ = φ (s * x * k) := by
          rw [hset, measure_preimage_mul, hνH, mul_one]
  calc ∫⁻ g, φ g ∂X.B.μf = ∫⁻ g, ∫⁻ t, F t g ∂ν ∂X.B.μf := lintegral_congr fun g => (hC' g).symm
    _ = ∫⁻ t, ∫⁻ g, F t g ∂X.B.μf ∂ν := (lintegral_lintegral_swap hF.aemeasurable).symm
    _ = ∫⁻ t, ∫⁻ k in K, φ ((t : G) * x * k) ∂X.B.μf ∂ν := lintegral_congr fun t => hA t

end GlobalTheory.SfinHaar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittTarget
section
namespace I195MixedCoordinates_4160728ecfd2b76db64d5897

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_4160728ecfd2b76db64d5897

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.MixTargetProof

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {D : D7}

theorem cj_smul {X Y : Type} (e : Y → X) (c : ℂ) (φ : X → ℂ) : cj e (c • φ) = starRingEnd ℂ c • cj e φ := by
  funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem cj_dagger_inj (S T : HSp D) {a b : WO S T → ℂ} (h : cj (dagger T S) a = cj (dagger T S) b) : a = b := by
  have h' := congrArg (cj (dagger S T)) h
  rwa [cj_cj (dagger T S) (dagger S T) (dagger_dagger S T), cj_cj (dagger T S) (dagger S T) (dagger_dagger S T)] at h'

theorem conjAdjoint_cj {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem conj_psi_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : AF D.host.F) :
    starRingEnd ℂ (ψ (-q)) = ψ q := by
  rw [← Complex.inv_eq_conj (hψ.1.2.1 _), AddChar.map_neg_eq_inv, inv_inv]

theorem conj_levi_coeff' (z : Circle) (r : ℝ) :
    starRingEnd ℂ ((z : ℂ) * (r : ℂ)) = ((z⁻¹ : Circle) : ℂ) * (r : ℂ) := by
  rw [map_mul, Circle.coe_inv_eq_conj, Complex.conj_ofReal]

theorem incA_conj_neg_inv : cA D (incA D (-D.host.xi0⁻¹)) = incA D D.host.xi0⁻¹ := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg]

theorem dagger_ofAdj (S T : HSp D) (z : Mx D S.rank T.rank) :
    dagger S T (ofAdj S T z) = incA D D.host.xi0⁻¹ • z := by
  rw [dagger, ofAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, incA_conj_neg_inv, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

theorem symplOH_dagger {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (x y : WO S T) :
    symplOH T S (dagger S T x) (dagger S T y) = -symplOH S T x y := by
  rw [symplOH, symplOH, (_root_.GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ S T).1 x y, mul_neg]

end GlobalTheory.MixTargetProof

namespace GlobalTheory.MixTargetProof

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {D : D7}

theorem nC_inv_incAdj_sub {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ) :
    mt T (d.nC c)⁻¹ ⬝ d.incAdj S y - d.incAdj S y =
      d.incX S (-(c.1 ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)))) := by
  rw [d.nC_inv, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, ← Matrix.mul_assoc, d.nC_jY,
    Matrix.add_mul, add_sub_cancel_left, AddSubgroup.coe_neg, Matrix.mul_assoc, Matrix.neg_mul]

theorem giA_adj_central {S : HSp D} {ρ : ℕ} (c : skewA D ρ) (y : Mx D S.rank ρ) :
    giA S ⬝ adj (-(c.1 ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)))) = (incA D D.host.xi0⁻¹ • y) ⬝ c.1 := by
  have hc : adj c.1 = -c.1 := c.2
  rw [adj_neg, adj_mul, hc, adj_smul, adj_mul, adj_adj, adj_gA, incA_conj_neg_inv]
  simp only [Matrix.mul_neg, neg_neg]
  rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, giA_gA_cancel, Matrix.smul_mul]

theorem quadratic_form_xi_inverse {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ}
    (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank))
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) (c : skewA D ρ) (y : Mx D S.rank ρ) :
    d.qS S c (incA D D.host.xi0⁻¹ • y) = -d.qT S c y := by
  obtain ⟨μ', 𝓕', -, hX, hY, -, -⟩ := _root_.GlobalTheory.MixSwap.mixS_cj_dagger D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  rw [HypDec.qS, HypDec.qT, ← hX, ← giA_adj_central c y, ← hY, nC_inv_incAdj_sub, symplOH_dagger hψ]

end GlobalTheory.MixTargetProof

namespace GlobalTheory.MixTargetProof

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

section Read

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} {d : HypDec T T₀ ρ} {χS : (AE D)ˣ →* Circle}
  {om : Rep S T} {om₀ : Rep S T₀} {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
  {μ' : Measure (Mx D S.rank ρ)} {𝓕' : Set (Mx D S.rank ρ)} {f : WO S T → ℂ}
  (hsw : ∀ (f : WO S T → ℂ) y, (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕' (cj (dagger T S) f) (incA D D.host.xi0⁻¹ • y) =
    cj (dagger T₀ S) ((_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 f y))
  (FS : FormulasS d ψ χS (conjAdjoint om) (conjAdjoint om₀) μ' 𝓕' (cj (dagger T S) f))
include hsw FS

theorem read_source (g : GA D S) (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 (om (g, 1) f) y = om₀ (g, 1) ((_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 f (mt S g⁻¹ ⬝ y)) := by
  apply cj_dagger_inj S T₀
  have h1 : (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕'
      (conjAdjoint om (1, g) (cj (dagger T S) f)) (incA D D.host.xi0⁻¹ • y) =
      conjAdjoint om₀ (1, g) ((_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕'
        (cj (dagger T S) f) (mt S g⁻¹ ⬝ (incA D D.host.xi0⁻¹ • y))) := FS.target g _
  rw [conjAdjoint_cj, hsw, Matrix.mul_smul, hsw, conjAdjoint_cj] at h1
  exact h1

theorem read_core (h₀ : GA D T₀) (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 (om (1, d.emb0 h₀) f) y = om₀ (1, h₀) ((_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 f y) := by
  apply cj_dagger_inj S T₀
  have h1 : (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕'
      (conjAdjoint om (d.emb0 h₀, 1) (cj (dagger T S) f)) (incA D D.host.xi0⁻¹ • y) =
      conjAdjoint om₀ (h₀, 1) ((_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕'
        (cj (dagger T S) f) (incA D D.host.xi0⁻¹ • y)) := FS.core h₀ _
  rw [conjAdjoint_cj, hsw, hsw, conjAdjoint_cj] at h1
  exact h1

theorem read_levi (a : GL (Fin ρ) (AE D)) (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 (om (1, d.levi a) f) y =
      (((χS (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) * (halfMod S.rank a : ℂ)) •
        (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 f (y ⬝ a.1) := by
  apply cj_dagger_inj S T₀
  have h1 : (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕'
      (conjAdjoint om (d.levi a, 1) (cj (dagger T S) f)) (incA D D.host.xi0⁻¹ • y) =
      ((((χS (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (halfMod S.rank a : ℂ)) •
        (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕'
          (cj (dagger T S) f) ((incA D D.host.xi0⁻¹ • y) ⬝ a.1) := FS.levi a _
  rw [conjAdjoint_cj, hsw, Matrix.smul_mul, hsw] at h1
  rw [cj_smul, conj_levi_coeff']
  exact h1

theorem read_unip (hψ : IsStdChar D ψ (-1)) (b : Mx D ρ T₀.rank) (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 (om (1, d.nB b) f) y = heisO ψ S T₀ (ofAdj S T₀ (y ⬝ b)) ((_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 f y) := by
  apply cj_dagger_inj S T₀
  have h1 : (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕'
      (conjAdjoint om (d.nB b, 1) (cj (dagger T S) f)) (incA D D.host.xi0⁻¹ • y) =
      heisO ψ T₀ S ((incA D D.host.xi0⁻¹ • y) ⬝ b)
        ((_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕'
          (cj (dagger T S) f) (incA D D.host.xi0⁻¹ • y)) := FS.unip b _
  rw [conjAdjoint_cj, hsw, Matrix.smul_mul, hsw, ← dagger_ofAdj, (_root_.GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ S T₀).2.2.2] at h1
  exact h1

theorem read_centre (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) (c : skewA D ρ)
    (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 (om (1, d.nC c) f) y = ψ (d.qT S c y) • (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.target d) S ψ μ 𝓕 f y := by
  apply cj_dagger_inj S T₀
  have h1 : (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕' (conjAdjoint om (d.nC c, 1) (cj (dagger T S) f)) (incA D D.host.xi0⁻¹ • y) =
      ψ (d.qS S c (incA D D.host.xi0⁻¹ • y)) • (_root_.I195MixedCoordinates_4160728ecfd2b76db64d5897.source d) S ψ μ' 𝓕' (cj (dagger T S) f) (incA D D.host.xi0⁻¹ • y) :=
    FS.centre c _
  rw [conjAdjoint_cj, hsw, hsw, quadratic_form_xi_inverse hψ d μ 𝓕 hμ] at h1
  rw [cj_smul, ← conj_psi_neg hψ, Complex.conj_conj]
  exact h1

end Read

theorem mixedTarget : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedTarget D := by
  intro D ψ S T T₀ ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ f hf
  have hψ := hom.std
  obtain ⟨μ', 𝓕', hμ', -, -, -, hsw⟩ := _root_.GlobalTheory.MixSwap.mixS_cj_dagger D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  have hF : IsThetaFunO ψ T S (cj (dagger T S) f) := ((_root_.GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ S T).2.2.1 f).2 hf
  have FS := _root_.GlobalTheory.MixSourceFormulas.mixed_source D ψ T T₀ S ρ d χT χS (conjAdjoint om) (conjAdjoint om₀)
    (_root_.GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S T χS χT om hom) (_root_.GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S T₀ χS χT om₀ hom₀) μ' 𝓕' hμ' _ hF
  exact ⟨read_source hsw FS, read_core hsw FS, read_levi hsw FS, read_unip hsw FS hψ, read_centre hsw FS hψ hμ⟩

end GlobalTheory.MixTargetProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowGen1POfSteps
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
open Formalism.L2.SG.Pf

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scT_sc_genSet {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) :
    (scT X).sc (scT X).genSet = X.one X.genSet := by
  ext p
  simp only [PB.Terms.one, PB.Terms.sc, PB.Terms.allPairs, Set.mem_setOf_eq]
  exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, trivial⟩⟩

theorem rowGen1P_of_steps (hCh : PN.NGChain) (hC : StepClass1) (hN : StepNormals1) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLoc1) (hTB : GlobalTheory.SnPos.StepThmBGP) : RowGen1P := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨CB, hCB, a₁, b₁, hTB2⟩ := hTB Cg cb Cw cT CT C0 hcb hcT (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, a₂, b₂, hS2⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  obtain ⟨a₃, b₃, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨a₄, b₄, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨a₅, b₅, hH2⟩ := stepHeightG_of_normOne hO Cg cb Cw cT CT C0
  obtain ⟨a₆, b₆, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨a₇, b₇, hT2⟩ := hTi Cg cb Cw cT CT C0
  obtain ⟨a₈, b₈, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨a₉, b₉, hV2⟩ := hV Cg cb Cw cT CT C0
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh meanAmplitudeGeneric_holds C1 C0n (C1 + C0n + 38) CB CSt Cgs CTs
    hCB hCSt hCg hCT le_rfl
  refine ⟨Cn, hCn, max a₀ (max a₁ (max a₂ (max a₃ (max a₄ (max a₅ (max a₆ (max a₇ (max a₈ a₉)))))))),
    max b₀ (max b₁ (max b₂ (max b₃ (max b₄ (max b₅ (max b₆ (max b₇ (max b₈ b₉)))))))),
    fun C' Cl e1 e2 D large₂ X Y u hTies hH0 hSt hT ha => ?_⟩
  simp only [max_le_iff] at e1 e2
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := e1
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := e2
  have hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hH0, hSt, hT⟩
  obtain ⟨hb, X0, ψ, hTie⟩ := hT2 C' Cl p7 q7 D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl p6 q6 D large₂ X Y u u hc hb X0 ψ hTie
  have hBk' : MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) (Irat * kapU D) (Ire * kapU D) :=
    massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨ν, hν⟩ := hE2 C' Cl p8 q8 D large₂ X Y u u hc
  obtain ⟨s, hs1, hs0, hsb, hLe⟩ :=
    hL2 C' Cl p0 q0 D large₂ X Y u hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  have hSum := hTB2 C' Cl p1 q1 D large₂ X Y u hTies hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  generalize bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq = B at hBk' hLe
  have hSz := hS2 C' Cl p2 q2 D large₂ X Y u u hc
  have hrd : 0 < D.host.rdE := by
    obtain ⟨-, -, hrd, -⟩ := hSz
    have hv : 2 * D.host.v = D.host.rdE := by simp only [Formalism.BasicNotions.Host.v]; ring
    rwa [hv] at hrd
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk'
  set ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA * 2 *
      HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ PN.eN D.R.rS *
      nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u : ℕ)) γ with hng
  obtain ⟨hPt, -, -, hAmp⟩ := GlobalTheory.Core.One.genericTerms_points_agree_groupSums_corankOne D X Y u (sc s ν) ν ng
  have hVan : ∀ t ∈ (Y.tO u u).genSet, J2of Y u u (sc s ν) (ptPN t) = 0 → (Y.tO u u).vec t = 0 := by
    intro t ht h0
    obtain ⟨g, hg⟩ := J2of_sc Y u u s ν (ptPN t)
    rw [hg] at h0
    have hp : (0 : ℝ) < (s g : ℝ) ^ 2 := by have := hs0 g; positivity
    exact hV2 C' Cl p9 q9 D large₂ X Y u hc ν hν t ht ((mul_eq_zero.1 h0).resolve_left hp.ne')
  have hIn : GenInputs (scT (Y.tO u u)) (NOf1 Y u (sc s ν) ν ng) D.R.f C1 C0n (C1 + C0n + 38) CB large₂.sc.b
      (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
      (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f))
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) 2 (Ire * kapU D) := by
    refine ⟨hC D X Y u hT _ _ _, hAmp hVan, hN2 C' Cl p3 q3 D large₂ X Y u hc _ _ _, ?_,
      localInputG_of_le _ _ _ _ _ hLe (fun γ => rfl), ?_, ?_, ?_, ?_⟩
    · exact fun γ hγ => hP2 C' Cl p4 q4 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun γ hγ => measureInputG_sc Y u s ν _ hsb ng γ ((hPt γ).1 hγ)
    · exact fun γ _ => ⟨nPt_nonneg _ hrd _ _ γ, le_rfl⟩
    · exact fun γ hγ => hH2 C' Cl p5 q5 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun S hS => hSum (sc s ν) ng S (fun γ hγ => (hPt γ).1 (hS γ hγ))
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (scT (Y.tO u u)) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOf1 Y u (sc s ν) ν ng) _ B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) 2 (Irat * kapU D) (Ire * kapU D)
  rw [hcard] at key
  have r := key ha hG hNI hFI (ngSizes_of hSz hb0 le_rfl zero_le_two le_rfl) hIn
  rw [hdd] at r
  unfold PB.Terms.RowMain at r
  rw [scT_sc_genSet] at r
  exact r

end GlobalTheory.Core.One
end
end

