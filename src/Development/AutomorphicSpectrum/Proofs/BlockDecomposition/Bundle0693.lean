module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneVolumeBound
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.DilPush

theorem push_dil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (c : ℝ≥0), MeasurableSet P → (∀ S : Set (Fv F v), MeasurableSet S → coordW (Fv F v) b lam 1 M (P ∩ (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S) → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fv F v)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ∩ (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ⁻¹' S) ≤ ((c * ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ (M - 1) : ℝ≥0) : ℝ≥0∞) * lam S := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b v lam hlam P c hP hbound u S hS
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI := hlam.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  set Q : (Fin 1 → Fin M → Fv F v ⊗[F] E) → Fv F v := fun X => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) with hQ
  set D : (Fin 1 → Fin M → Fv F v ⊗[F] E) → (Fin 1 → Fin M → Fv F v ⊗[F] E) := fun X p k => (u : Fv F v ⊗[F] E) * X p k with hD
  set n : Fv F v := Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) with hn
  have hn0 : n ≠ 0 := (u.isUnit.map (Algebra.norm (Fv F v))).ne_zero
  have hdil : ∀ X, Q (D X) = n * Q X := fun X => _root_.GlobalTheory.CompanionTheory.AvgFree.Dilate.half_trace_dilate F E σ hσ M J hJ v u X
  set S' : Set (Fv F v) := (fun t => n * t) ⁻¹' S with hS'def
  have hmul : Measurable (fun t : Fv F v => n * t) := (continuous_const_mul n).measurable
  have hS' : MeasurableSet S' := hmul hS
  have hset : D '' P ∩ Q ⁻¹' S = D '' (P ∩ Q ⁻¹' S') := by
    ext Y
    constructor
    · rintro ⟨⟨X, hX, rfl⟩, hY⟩
      refine ⟨X, ⟨hX, ?_⟩, rfl⟩
      show n * Q X ∈ S
      rw [← hdil]
      exact hY
    · rintro ⟨X, ⟨hX, hXS⟩, rfl⟩
      refine ⟨⟨X, hX, rfl⟩, ?_⟩
      show Q (D X) ∈ S
      rw [hdil]
      exact hXS
  have hQc : Continuous Q := by
    have h1 : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
      PI.VolStabSW.SdUniqW.continuous_trace_tens (F := F) (E := E) (Fv F v)
    have h2 : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => gramR (Fv F v) σ J X 0 0 :=
      (continuous_apply_apply 0 0).comp (PI.VolStabS.continuous_gramR (Fv F v) σ J)
    exact continuous_const.mul (h1.comp h2)
  have hQm : Measurable Q := hQc.measurable
  have hlamS : lam S' = (‖n‖₊ : ℝ≥0∞)⁻¹ * lam S := by
    have h := GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_finite v n hn0 lam hlam.1
    have h2 := congrArg (fun μ : Measure (Fv F v) => μ S) h
    simp only [Measure.smul_apply] at h2
    rw [Measure.map_apply hmul hS] at h2
    rw [hS'def, h2, ENNReal.smul_def, smul_eq_mul]
    simp [ENNReal.coe_inv (nnnorm_ne_zero_iff.2 hn0)]
  rw [hset, _root_.GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul F E σ hσ M d b v lam hlam u _ (hP.inter (hQm hS'))]
  set a : ℝ≥0∞ := (‖n‖₊ : ℝ≥0∞) with ha
  have ha0 : a ≠ 0 := by simpa [ha] using hn0
  have hat : a ≠ ⊤ := ENNReal.coe_ne_top
  have hpow : a ^ M = a ^ (M - 1) * a := by rw [← pow_succ, Nat.sub_add_cancel hM]
  have haa : a * a⁻¹ = 1 := ENNReal.mul_inv_cancel ha0 hat
  calc a ^ M * coordW (Fv F v) b lam 1 M (P ∩ Q ⁻¹' S')
      ≤ a ^ M * ((c : ℝ≥0∞) * lam S') := by gcongr; exact hbound S' hS'
    _ = (c : ℝ≥0∞) * a ^ (M - 1) * (a * a⁻¹) * lam S := by rw [hlamS, hpow]; ring
    _ = ((c * ‖n‖₊ ^ (M - 1) : ℝ≥0) : ℝ≥0∞) * lam S := by rw [haa, ha]; push_cast; ring

end GlobalTheory.CompanionTheory.WeilSiegel.DilPush
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleRayEqPowDegree
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem md_ray : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  intro F _ _ hF θ r hr δ hδ
  obtain ⟨h1, h2⟩ := hr δ hδ
  have hw : ∀ w : InfinitePlace F, ‖(θ δ) w‖ = δ := by
    intro w
    have hreal : w.IsReal := hF.isReal w
    have hu := congrArg (fun f : ℝ →+* ℝ => f δ)
      (Subsingleton.elim ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal).comp
        ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ)) (RingHom.id ℝ))
    have hu' : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal ((θ δ) w) = δ := hu
    have hn := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hreal).norm_map_of_map_zero
      (map_zero _) ((θ δ) w)
    rw [hu', Real.norm_eq_abs, abs_of_pos hδ] at hn
    exact hn.symm
  change (∏ w, ‖((r δ : AF F)).1 w‖ ^ w.mult) * (∏ᶠ v, ‖((r δ : AF F)).2 v‖) = δ ^ Module.finrank ℚ F
  rw [h1, h2]
  simp only [hw]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  simp

end GlobalTheory.CompanionTheory.BasePsi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzero
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem eventually_cv_mem_intLoc {D : D7} (a : AE D) :
    ∀ᶠ v : Pl D in cofinite, cv D v a ∈ intLoc D.host.F D.host.E v :=
  GlobalTheory.ThK.ConeEuler.eventually_compFin_mem_intLoc_adele a

theorem isOpen_intAll (D : D7) : IsOpen {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} :=
  GlobalTheory.ThK.ConeEuler.UnitsOpen.isOpen_integral_everywhere

theorem exists_intOff {D : D7} {a b : ℕ} (x : Mx D a b) :
    ∀ᶠ v : Pl D in cofinite, ∀ i j, cv D v (x i j) ∈ intLoc D.host.F D.host.E v :=
  eventually_all.2 fun i => eventually_all.2 fun j => eventually_cv_mem_intLoc (x i j)

theorem isOpen_nearInt {D : D7} {a b : ℕ} (x : Mx D a b) :
    IsOpen {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have h : {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} =
      ⋂ i, ⋂ j, (fun y : Mx D a b => y i j - x i j) ⁻¹' {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  have hT := (top_mx (D := D) a b).1
  haveI hS : ContinuousSub (Mx D a b) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hT
  have hc : Continuous fun y : Mx D a b => y - x := continuous_id.sub continuous_const
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_intAll D).preimage (hc.matrix_elem i j)

theorem nuT_intOff_ne_zero : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S →
      nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} ≠ 0 := by
  intro D n t B W d hn I μ hμ x₀
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let π : I.l.K × Par D n t W → Mx D B.rank W.rank × Mx D B.rank t :=
    fun p => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)
  let p₀ : I.l.K × Par D n t W := (1, (1, (0, 0)))
  have hbad : {v : Pl D | ¬ ((∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v)}.Finite :=
    ((exists_intOff (π p₀).1).and (exists_intOff (π p₀).2))
  refine ⟨hbad.toFinset, fun S hS => ?_⟩
  have hπ : Continuous π := by
    obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
    exact (continuous_ac B).comp (((continuous_subtype_val.comp continuous_fst).inv).prodMk
      ((continuous_zp d hn x₀).comp continuous_snd))
  let N : Set (Mx D B.rank W.rank × Mx D B.rank t) :=
    {z | (∀ i j, ∀ v : Pl D, cv D v (z.1 i j - (π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, ∀ v : Pl D, cv D v (z.2 i j - (π p₀).2 i j) ∈ intLoc D.host.F D.host.E v}
  have hNo : IsOpen N := ((isOpen_nearInt (π p₀).1).preimage continuous_fst).inter
    ((isOpen_nearInt (π p₀).2).preimage continuous_snd)
  have hN0 : π p₀ ∈ N := by
    constructor <;> intro i j v <;> simp only [sub_self, map_zero, zero_mem]
  have hNO : N ⊆ {z | IntOff S z.1 ∧ IntOff S z.2} := by
    intro z hz
    have key : ∀ v, v ∉ S → (∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
        ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v := fun v hv => by
      by_contra hc
      exact hv (hS (hbad.mem_toFinset.2 hc))
    refine ⟨fun v hv i j => ?_, fun v hv i j => ?_⟩
    · have := add_mem (hz.1 i j v) ((key v hv).1 i j)
      rwa [← RingHom.map_add, sub_add_cancel] at this
    · have := add_mem (hz.2 i j v) ((key v hv).2 i j)
      rwa [← RingHom.map_add, sub_add_cancel] at this
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hGB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.haarK
  have hs1 : SigmaFinite (I.μ₁.prod μ) := inferInstance
  have hs2 : SigmaFinite (Q0 I μ) := sigmaFinite_parameter_product_measure I μ hμ
  have p1 : (I.μ₁.prod μ).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have p2 : (Q0 I μ).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have hpos : (I.νK.prod (Q0 I μ)).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have hopen : IsOpen (π ⁻¹' N) := hNo.preimage hπ
  have hne : (I.νK.prod (Q0 I μ)) (π ⁻¹' N) ≠ 0 := hopen.measure_ne_zero _ ⟨p₀, hN0⟩
  intro h0
  apply hne
  have hle : (I.νK.prod (Q0 I μ)) (π ⁻¹' {z | IntOff S z.1 ∧ IntOff S z.2}) ≤ nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} :=
    Measure.le_map_apply (measurable_pi hn I x₀).aemeasurable _
  exact le_antisymm (((measure_mono (Set.preimage_mono hNO)).trans hle).trans h0.le) bot_le

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormula
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

theorem rv_zero_apply (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    rv v 0 s = if s ≠ 0 ∧ s ∈ v.adicCompletionIntegers F then 1 else 0 := by
  unfold rv
  rw [tsum_eq_single 0]
  · have h : (s ∈ v.adicCompletionIntegers F) ↔ Valued.v s ≤ 1 :=
      HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v
    simp [h]
  · intro i hi
    simp [hi]

theorem rv_zero_of_mem (v : HeightOneSpectrum (𝓞 F)) {s : Fv F v} (h0 : s ≠ 0)
    (hs : s ∈ v.adicCompletionIntegers F) : rv v 0 s = 1 := by
  rw [rv_zero_apply, if_pos ⟨h0, hs⟩]

theorem rv_zero_of_not_mem (v : HeightOneSpectrum (𝓞 F)) {s : Fv F v}
    (hs : s ∉ v.adicCompletionIntegers F) : rv v 0 s = 0 := by
  rw [rv_zero_apply, if_neg fun h => hs h.2]

theorem pure_rv_zero_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ) :
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a =
      if ∀ v, v ∉ S → (a : AF F).2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G (a : AF F).1 * ∏ v ∈ S, g v ((a : AF F).2 v)) else 0 := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), (a : AF F).2 v ≠ 0 := fun v =>
    IdeleGroup.finite_ne_zero a v
  unfold PositivityTheory.Rg.Base1.pure
  split_ifs with h
  · rw [finprod_eq_one_of_forall_eq_one (fun v : {v // v ∉ S} => rv_zero_of_mem v.1 (hne v.1) (h v.1 v.2)),
      mul_one]
  · push_neg at h
    obtain ⟨v, hvS, hv⟩ := h
    have hfin : (Function.mulSupport fun v : {v // v ∉ S} => rv v.1 0 ((a : AF F).2 v.1)).Finite := by
      have hco : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
          (a : AF F).2 v ∈ v.adicCompletionIntegers F := (a : AF F).2.2
      refine Set.Finite.subset (Set.Finite.preimage Subtype.val_injective.injOn hco) ?_
      intro w hw
      by_contra hmem
      exact hw (rv_zero_of_mem w.1 (hne w.1) (not_not.1 hmem))
    rw [finprod_eq_zero _ (⟨v, hvS⟩ : {v // v ∉ S}) (rv_zero_of_not_mem v hv) hfin, mul_zero,
      ENNReal.ofReal_zero]

end GlobalTheory.CompanionTheory.BasePsi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionEnlargeFiniteSet
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi.Integrals

variable {F : Type} [Field F] [NumberField F]

theorem integral_pi_unit {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (h : X → ℝ) :
    ∫ y : Unit → X, h (y ()) ∂(Measure.pi fun _ : Unit => μ) = ∫ x, h x ∂μ :=
  (measurePreserving_piUnique (fun _ : Unit => μ)).integral_comp' (f := MeasurableEquiv.piUnique _) h

theorem integral_comp_unit_mul {R : Type} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [MeasurableSpace R] [BorelSpace R] (b : Rˣ) (μ : Measure R) (f : R → ℝ) :
    ∫ y, f ((b : R) * y) ∂μ = ∫ y, f y ∂(μ.map fun y => (b : R) * y) := by
  let e : R ≃ₜ R :=
    { toEquiv := Units.mulLeft b
      continuous_toFun := show Continuous fun x => (b : R) * x from continuous_const.mul continuous_id
      continuous_invFun :=
        show Continuous fun x => ((b⁻¹ : Rˣ) : R) * x from continuous_const.mul continuous_id }
  exact (e.measurableEmbedding.integral_map (μ := μ) f).symm

def unitInf (a : (AF F)ˣ) : (Ainf F)ˣ where
  val := (a : AF F).1
  inv := ((a⁻¹ : (AF F)ˣ) : AF F).1
  val_inv := by
    have h : ((a : AF F) * ((a⁻¹ : (AF F)ˣ) : AF F)).1 = 1 := by simp
    exact h
  inv_val := by
    have h : (((a⁻¹ : (AF F)ˣ) : AF F) * (a : AF F)).1 = 1 := by simp
    exact h

theorem sigmaFinite_inf (li : Measure (Ainf F)) (h : li.IsAddHaarMeasure) : SigmaFinite li := by
  infer_instance

theorem sigmaFinite_fin (v : HeightOneSpectrum (𝓞 F)) (l : Measure (Fv F v)) (h : l.IsAddHaarMeasure) :
    SigmaFinite l := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  infer_instance

theorem integral_mul_inf (li : Measure (Ainf F)) (h : li.IsAddHaarMeasure) (b : (Ainf F)ˣ)
    (G : Ainf F → ℝ) :
    ∫ y, G ((b : Ainf F) * y) ∂li = ‖((b⁻¹ : (Ainf F)ˣ) : Ainf F)‖ * ∫ y, G y ∂li := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hn : 0 ≤ ‖((b⁻¹ : (Ainf F)ˣ) : Ainf F)‖ := by
    rw [InfiniteAdeleRing.norm_def]
    exact Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _
  rw [integral_comp_unit_mul b li G, GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_infinite ⟨rfl⟩ b li h,
    integral_smul_measure, ENNReal.toReal_ofReal hn, smul_eq_mul]

theorem integral_mul_fin (v : HeightOneSpectrum (𝓞 F)) (l : Measure (Fv F v))
    (h : l.IsAddHaarMeasure) (c : Fv F v) (hc : c ≠ 0) (f : Fv F v → ℝ) :
    ∫ y, f (c * y) ∂l = ‖c‖⁻¹ * ∫ y, f y ∂l := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have h1 := integral_comp_unit_mul (Units.mk0 c hc) l f
  simp only [Units.val_mk0] at h1
  rw [h1, GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_finite v c hc l h, integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul]
  simp

theorem integral_ind (v : HeightOneSpectrum (𝓞 F)) (l : Measure (Fv F v)) (h : IsStdV v l)
    (c : Fv F v) (hc : c ≠ 0) :
    ∫ y, (if c * y ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0) ∂l = ‖c‖⁻¹ := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (Fv F v)) :=
    (Valued.isOpen_valuationSubring _).measurableSet
  have h0 := integral_mul_fin v l h.1 c hc
    (fun s => if s ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0)
  have h1 : (fun s : Fv F v => if s ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0) =
      (v.adicCompletionIntegers F : Set (Fv F v)).indicator 1 := by
    ext s
    simp [Set.indicator]
  have h2 : ∫ s, (if s ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0) ∂l = 1 := by
    rw [h1, integral_indicator_one hO, Measure.real, h.2]
    simp
  rw [h0, h2, mul_one]

theorem norm_unitInf_inv (a : (AF F)ˣ) :
    ‖(((unitInf a)⁻¹ : (Ainf F)ˣ) : Ainf F)‖ =
      (∏ w : InfinitePlace F, ‖(a : AF F).1 w‖ ^ w.mult)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [InfiniteAdeleRing.norm_def, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [← mul_pow, ← norm_mul]
  have h := IdeleGroup.infinite_mul_inv a w
  have h' : ((a⁻¹ : (AF F)ˣ) : AF F).1 w * (a : AF F).1 w = 1 := by rw [mul_comm]; exact h
  have : (((unitInf a)⁻¹ : (Ainf F)ˣ) : Ainf F) w = ((a⁻¹ : (AF F)ˣ) : AF F).1 w := rfl
  rw [this, h', norm_one, one_pow]

theorem md_eq_of_off (a : (AF F)ˣ) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hoff : ∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) :
    md a = (∏ w : InfinitePlace F, ‖(a : AF F).1 w‖ ^ w.mult) * ∏ v ∈ T, ‖(a : AF F).2 v‖ := by
  rw [md, IdeleGroup.ideleModule_eq]
  congr 1
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hT
  exact hv (IdeleGroup.norm_eq_one_of_mul_eq_one (IdeleGroup.finite_mul_inv a v)
    (hoff v hT).1 (hoff v hT).2)

theorem integrals_translates : ∀ (F : Type) [Field F] [NumberField F] (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)),
    IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    (∫ y, phiA G a y ∂(Measure.pi fun _ : Unit => li)) * ∏ v ∈ T, ∫ y, psiA S g a v y ∂(Measure.pi fun _ : Unit => lam v) =
      (md a)⁻¹ * ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v)) := by
  intro F _ _ li lam hli hlam S T G g a hST hoff
  haveI := sigmaFinite_inf li hli.1
  have hI : ∫ y, phiA G a y ∂(Measure.pi fun _ : Unit => li) =
      ‖(((unitInf a)⁻¹ : (Ainf F)ˣ) : Ainf F)‖ * ∫ y, G y ∂li :=
    (integral_pi_unit li (fun x => G ((a : AF F).1 * x))).trans
      (integral_mul_inf li hli.1 (unitInf a) G)
  have hv : ∀ v, (a : AF F).2 v ≠ 0 := IdeleGroup.finite_ne_zero a
  have hP : ∀ v ∈ T, ∫ y, psiA S g a v y ∂(Measure.pi fun _ : Unit => lam v) =
      ‖(a : AF F).2 v‖⁻¹ * (if v ∈ S then ∫ s, g v s ∂(lam v) else 1) := by
    intro v _
    haveI := sigmaFinite_fin v (lam v) (hlam v).1
    by_cases hS : v ∈ S
    · have h1 := integral_pi_unit (lam v) (fun x => g v ((a : AF F).2 v * x))
      have h2 := integral_mul_fin v (lam v) (hlam v).1 _ (hv v) (g v)
      simp only [psiA, hS, if_true]
      rw [h1, h2]
    · have h1 := integral_pi_unit (lam v) (fun x =>
        if (a : AF F).2 v * x ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0)
      have h2 := integral_ind v (lam v) (hlam v) _ (hv v)
      simp only [psiA, hS, if_false]
      rw [h1, h2, mul_one]
  have hS' : ∏ v ∈ T, (if v ∈ S then ∫ s, g v s ∂(lam v) else 1) = ∏ v ∈ S, ∫ s, g v s ∂(lam v) := by
    symm
    calc ∏ v ∈ S, ∫ s, g v s ∂(lam v)
        = ∏ v ∈ S, (if v ∈ S then ∫ s, g v s ∂(lam v) else 1) :=
          Finset.prod_congr rfl fun v h => by simp [h]
      _ = _ := Finset.prod_subset hST fun v _ h => by simp [h]
  rw [hI, Finset.prod_congr rfl hP, Finset.prod_mul_distrib, hS', md_eq_of_off a T hoff,
    norm_unitInf_inv, mul_inv, Finset.prod_inv_distrib]
  ring

end GlobalTheory.CompanionTheory.BasePsi.Integrals
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayNormAndModuleFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay

theorem norm_theta {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F)
    (ε : ℝ) (w : InfinitePlace F) : ‖θ ε w‖ = |ε| := by
  have hw : w.IsReal := hF.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ρ : ℝ →+* ℝ := (e : w.Completion →+* ℝ).comp ((Pi.evalRingHom _ w).comp θ)
  have hρ : ρ ε = ε := by
    have : ρ = RingHom.id ℝ := Subsingleton.elim _ _
    rw [this]; rfl
  have hnorm : ‖θ ε w‖ = ‖e (θ ε w)‖ := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) _).symm
  rw [hnorm]
  change ‖ρ ε‖ = |ε|
  rw [hρ, Real.norm_eq_abs]

theorem norm_md_ray : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F,
    Continuous θ → ∀ r, IsRay θ r → (∀ (ε : ℝ) (w : InfinitePlace F), ‖θ ε w‖ = |ε|) ∧
      ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  intro F _ _ hF θ _ r hr
  refine ⟨norm_theta hF θ, fun δ hδ => ?_⟩
  obtain ⟨h1, h2⟩ := hr δ hδ
  have hmd : md (r δ) = (∏ w : InfinitePlace F, ‖(r δ : AF F).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ := IdeleGroup.ideleModule_eq _
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [h2]
    exact norm_one
  rw [hmd, hfin, mul_one, h1]
  simp only [norm_theta hF θ δ, abs_of_pos hδ]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilRankOneBaseCaseStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_rank_one_base_case : Prop1 → Simil → Hasse → Cnt → PositivityTheory.SiegelWeilFormula.Densx.BaseOne := by
  first | exact @GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | exact GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | (intros; apply GlobalTheory.CompanionTheory.Base1.baseOne_of_parts <;> assumption)
end

