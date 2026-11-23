module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0209

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureConcentratedOnQuadric
section
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

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7}

theorem continuous_adjM {a b : ℕ} : Continuous (adj : Mx D a b → Mx D b a) := by
  have hc : Continuous (cA D) := GlobalTheory.FockCompare.ThetaCont.continuous_conj
  exact (continuous_id.matrix_map hc).matrix_transpose

theorem continuous_ipM {X : Type} [TopologicalSpace X] (V : HSp D) {a b : ℕ} {f : X → Mx D V.rank a}
    {g : X → Mx D V.rank b} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => ip V (f x) (g x) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (continuous_adjM.comp hf).matrix_mul (continuous_const.matrix_mul hg)

theorem continuous_qvM (V : HSp D) {r t : ℕ} (b₀ : HermE D r) :
    Continuous (qv (t := t) V b₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hT := (top_mx (D := D) t t).1
  have hy : Continuous (yv (t := t) V b₀) :=
    continuous_const.matrix_mul (continuous_ipM V continuous_fst continuous_snd)
  have h2 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2 :=
    continuous_ipM V continuous_snd continuous_snd
  have h3 : Continuous fun z : Mx D V.rank r × Mx D V.rank t =>
      pr b₀ (yv V b₀ z) (yv V b₀ z) :=
    (continuous_adjM.comp hy).matrix_mul (continuous_const.matrix_mul hy)
  have hs : ContinuousSub (Mx D t t) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hT
  exact h2.sub h3

theorem nuT_supp : ZpEq → AcEq → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → nuT hn I μ x₀ {z | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧ ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} = 0 := by
  intro hZ hA D n t B W d hn I μ _ b₀ hb x₀ hx
  obtain ⟨g1, -⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := g1.opensMeasurable
  have t1 := (top_mx (D := D) W.rank W.rank).2.2.2.1
  have t2 := (top_mx (D := D) t t).2.2.2.1
  have hcl : IsClosed {z : Mx D B.rank W.rank × Mx D B.rank t |
      ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0} :=
    (isClosed_eq (continuous_ipM B continuous_fst continuous_fst)
      continuous_const).inter (isClosed_eq (continuous_qvM B b₀) continuous_const)
  have hS : {z : Mx D B.rank W.rank × Mx D B.rank t | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧
      ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} =
      {z | ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, one_smul, true_and]
  rw [hS]
  unfold nuT
  rw [Measure.map_apply (measurable_pi hn I x₀) hcl.measurableSet.compl]
  have hE : (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ⁻¹'
      {z | ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0}ᶜ = ∅ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    obtain ⟨a1, -, a3⟩ := hA D W.rank t B b₀ ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)
    obtain ⟨z1, -, z3⟩ := hZ D n t B W d hn b₀ hb x₀ hx p.2
    exact ⟨a1.trans z1, a3.trans z3⟩
  rw [hE, measure_empty]

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariant
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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.InvU

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem ac_mul (V : HSp D) {a b : ℕ} (g h : GA D V) (z : Mx D V.rank a × Mx D V.rank b) :
    ac V (g * h) z = ac V g (ac V h z) := by
  simp only [ac, mm, mt_mul, Matrix.mul_assoc]

theorem measurable_ac (V : HSp D) {a b : ℕ} (g : GA D V) :
    Measurable (ac V g : Mx D V.rank a × Mx D V.rank b → Mx D V.rank a × Mx D V.rank b) := by
  obtain ⟨g1, g2⟩ := top_pair (D := D) V.rank a b
  have o1 : OpensMeasurableSpace (Mx D V.rank a × Mx D V.rank b) := g1.opensMeasurable
  have hc : Continuous (ac V g : Mx D V.rank a × Mx D V.rank b → Mx D V.rank a × Mx D V.rank b) :=
    (continuous_ac V).comp (continuous_const.prodMk continuous_id)
  exact hc.measurable

theorem rho_apply {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) :
    rho hn I μ x₀ A = Q0 I μ (zp d hn x₀ ⁻¹' A) :=
  Measure.map_apply (measurable_zp d hn x₀) hA

def sA {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (A : Set (Mx D B.rank W.rank × Mx D B.rank t)) (x : GA D B) : ℝ≥0∞ :=
  rho hn I μ x₀ {z | ac B x⁻¹ z ∈ A}

theorem measurable_sA {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) : Measurable (sA hn I μ x₀ A) := by
  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oB : OpensMeasurableSpace (GA D B) := hB.opensMeasurable
  have e1 : SecondCountableTopologyEither (GA D B) (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (GA D B × Par D n t W) := Prod.opensMeasurableSpace
  have := sigmaFinite_parameter_product_measure I μ hμ
  have hc : Continuous fun p : GA D B × Par D n t W => ac B p.1⁻¹ (zp d hn x₀ p.2) :=
    (continuous_ac B).comp ((continuous_fst.inv).prodMk ((continuous_zp d hn x₀).comp continuous_snd))
  have hS : MeasurableSet {p : GA D B × Par D n t W | ac B p.1⁻¹ (zp d hn x₀ p.2) ∈ A} := hc.measurable hA
  have key := measurable_measure_prodMk_left (ν := Q0 I μ) hS
  have e : sA hn I μ x₀ A = fun x => Q0 I μ (Prod.mk x ⁻¹' {p : GA D B × Par D n t W | ac B p.1⁻¹ (zp d hn x₀ p.2) ∈ A}) := by
    funext x
    exact rho_apply hn I μ x₀ (measurable_ac B x⁻¹ hA)
  rw [e]
  exact key

theorem sA_stab (hL : Law) {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) (q : GlobalTheory.RegSW.stab d) (x : GA D B) :
    sA hn I μ x₀ A (q * x) = ((GlobalTheory.RegSW.absDet d q ^ (W.rank + t) : ℝ≥0) : ℝ≥0∞) * sA hn I μ x₀ A x := by
  have hA' : MeasurableSet {z | ac B x⁻¹ z ∈ A} := measurable_ac B x⁻¹ hA
  have h1 := congrArg (fun ν : Measure _ => ν {z | ac B x⁻¹ z ∈ A}) (hL D n t B W d hn I μ hμ x₀ q⁻¹)
  beta_reduce at h1
  rw [Measure.map_apply (measurable_ac B _) hA'] at h1
  have e : sA hn I μ x₀ A (q * x) = rho hn I μ x₀ (ac B ((q⁻¹ : GlobalTheory.RegSW.stab d) : GA D B) ⁻¹' {z | ac B x⁻¹ z ∈ A}) := by
    unfold sA
    congr 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ← ac_mul, mul_inv_rev, Subgroup.coe_inv]
  rw [e, h1, map_inv, inv_inv]
  rfl

theorem nuT_apply {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) :
    nuT hn I μ x₀ A = ∫⁻ k : I.l.K, sA hn I μ x₀ A (k : GA D B) ∂I.νK := by
  have := sigmaFinite_parameter_product_measure I μ hμ
  unfold nuT
  rw [Measure.map_apply (measurable_pi hn I x₀) hA, Measure.prod_apply (measurable_pi hn I x₀ hA)]
  refine lintegral_congr fun k => ?_
  exact (rho_apply hn I μ x₀ (measurable_ac B (k : GA D B)⁻¹ hA)).symm

theorem nuT_map_ac (hQ : QK) (hL : Law) (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n)
    (I : IkD d n) (μ : Measure (Mx D W.rank t)) (hμ : μ.IsAddHaarMeasure) (x₀) (h : GA D B) :
    (nuT hn I μ x₀).map (fun z => (mm (mt B h) z.1, mm (mt B h) z.2)) = nuT hn I μ x₀ := by
  change (nuT hn I μ x₀).map (ac B h) = nuT hn I μ x₀
  refine Measure.ext fun A hA => ?_
  have hA' : MeasurableSet (ac B h ⁻¹' A) := measurable_ac B h hA
  rw [Measure.map_apply (measurable_ac B h) hA, nuT_apply hn I μ hμ x₀ hA', nuT_apply hn I μ hμ x₀ hA]
  have key := hQ D t B W d I.l I.good I.νK I.haarK (sA hn I μ x₀ A) (measurable_sA hn I μ hμ x₀ hA)
    (fun q x => sA_stab hL hn I μ hμ x₀ hA q x) h⁻¹
  rw [← key]
  refine lintegral_congr fun k => ?_
  unfold sA
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, ← ac_mul, mul_inv_rev, inv_inv]

end GlobalTheory.CompanionTheory.ColumnSplitting.InvU

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFiniteDimensional
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_fd_slices (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) :
    ∃ (A : Submodule ℂ (Sm E a)) (B : Submodule ℂ (Sm E b)), FiniteDimensional ℂ A ∧ FiniteDimensional ℂ B ∧
      (∀ m₂ : GA E b, ∃ φ ∈ A, φ.1 = fun x => F (x, m₂)) ∧ (∀ m₁ : GA E a, ∃ φ ∈ B, φ.1 = fun x => F (m₁, x)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, -, rfl⟩ := h
    refine ⟨Submodule.span ℂ {φ₁}, Submodule.span ℂ {φ₂}, inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · refine ⟨φ₂.1 m₂ • φ₁, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp [mul_comm]
    · refine ⟨φ₁.1 m₁ • φ₂, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp
  | zero =>
    refine ⟨⊥, ⊥, inferInstance, inferInstance, fun m₂ => ⟨0, Submodule.zero_mem _, ?_⟩,
      fun m₁ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · funext x
      simp
    · funext x
      simp
  | add F G _ _ hF hG =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    obtain ⟨A', B', hA', hB', h₁', h₂'⟩ := hG
    refine ⟨A ⊔ A', B ⊔ B', inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      obtain ⟨φ', hφ', e'⟩ := h₁' m₂
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      obtain ⟨φ', hφ', e'⟩ := h₂' m₁
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
  | smul c F _ hF =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    refine ⟨A, B, hA, hB, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      refine ⟨c • φ, A.smul_mem c hφ, ?_⟩
      funext x
      simp [e]
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      refine ⟨c • φ, B.smul_mem c hφ, ?_⟩
      funext x
      simp [e]

theorem pairFD_holds : PairFD := by
  intro E _ _ _ a b ι _ U₁ U₂ f hf
  choose A B hA hB h₁ h₂ using fun i => exists_fd_slices U₁ U₂ (f i) (hf i)
  have hA' : FiniteDimensional ℂ (⨆ i, A i : Submodule ℂ (Sm E a)) := Submodule.finiteDimensional_iSup A
  have hB' : FiniteDimensional ℂ (⨆ i, B i : Submodule ℂ (Sm E b)) := Submodule.finiteDimensional_iSup B
  constructor
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, A i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₂, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₁ i m₂
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, B i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₁, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₂ i m₁
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalHypotheses

theorem thetaGL_id_mem {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E) {g : GLw n w}
    (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : thetaGL n (RingHom.id _) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) g = g :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) g) * (PhiU n _)⁻¹ ∈ _
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n)
    (GlobalTheory.BCT.LocGlue.intst E n w w (RingHom.id _) (fun _ => rfl) g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))

theorem sgP_facts : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
    Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧
      ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := by
  intro E _ _ a b w
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.LocTwist.continuous_thetaGL a (RingHom.id _) continuous_id).prodMap
      (GlobalTheory.LocTwist.continuous_thetaGL b (RingHom.id _) continuous_id)
  · rintro ⟨g₁, g₂⟩
    exact Prod.ext (GlobalTheory.LocTwist.thetaGL_thetaGL a (RingHom.id _) (fun _ => rfl) g₁)
      (GlobalTheory.LocTwist.thetaGL_thetaGL b (RingHom.id _) (fun _ => rfl) g₂)
  · rintro ⟨k₁, k₂⟩ hk
    exact ⟨thetaGL_id_mem a w hk.1, thetaGL_id_mem b w hk.2⟩

end GlobalTheory.CompanionTheory.LocalHypotheses

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSlices
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.PairSl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_slices (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) :
    (∀ m₂, ∃ φ ∈ U₁, φ.1 = fun x => F (x, m₂)) ∧ (∀ m₁, ∃ φ ∈ U₂, φ.1 = fun x => F (m₁, x)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    refine ⟨fun m₂ => ⟨φ₂.1 m₂ • φ₁, U₁.smul_mem _ h₁, ?_⟩, fun m₁ => ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, ?_⟩⟩
    · funext x
      simp [mul_comm]
    · funext x
      simp
  | zero =>
    refine ⟨fun m₂ => ⟨0, U₁.zero_mem, ?_⟩, fun m₁ => ⟨0, U₂.zero_mem, ?_⟩⟩
    · funext x
      simp
    · funext x
      simp
  | add F G _ _ h₁ h₂ =>
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁.1 m₂
      obtain ⟨ψ, hψ, e'⟩ := h₂.1 m₂
      refine ⟨φ + ψ, U₁.add_mem hφ hψ, ?_⟩
      funext x
      have i := congrFun e x
      have i' := congrFun e' x
      simp_all
    · obtain ⟨φ, hφ, e⟩ := h₁.2 m₁
      obtain ⟨ψ, hψ, e'⟩ := h₂.2 m₁
      refine ⟨φ + ψ, U₂.add_mem hφ hψ, ?_⟩
      funext x
      have i := congrFun e x
      have i' := congrFun e' x
      simp_all
  | smul r F _ h =>
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h.1 m₂
      refine ⟨r • φ, U₁.smul_mem r hφ, ?_⟩
      funext x
      have i := congrFun e x
      simp_all
    · obtain ⟨φ, hφ, e⟩ := h.2 m₁
      refine ⟨r • φ, U₂.smul_mem r hφ, ?_⟩
      funext x
      have i := congrFun e x
      simp_all

end GlobalTheory.CompanionTheory.EGlue.PairSl

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairSlices : PairSlices := by
  intro E _ _ _ a b U₁ U₂ F hF
  obtain ⟨h₁, h₂⟩ := PairSl.exists_slices U₁ U₂ F hF
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨φ, hφ, e⟩ := h₁ m₂
    have hex : ∃ φ : Sm E a, φ.1 = fun x => F (x, m₂) := ⟨φ, e⟩
    have hs : sl₁ F m₂ = hex.choose := by simp only [sl₁, dif_pos hex]
    have hc : hex.choose = φ := Subtype.ext (hex.choose_spec.trans e.symm)
    rw [hs, hc]
    exact ⟨hφ, e⟩
  · obtain ⟨φ, hφ, e⟩ := h₂ m₁
    have hex : ∃ φ : Sm E b, φ.1 = fun x => F (m₁, x) := ⟨φ, e⟩
    have hs : sl₂ F m₁ = hex.choose := by simp only [sl₂, dif_pos hex]
    have hc : hex.choose = φ := Subtype.ext (hex.choose_spec.trans e.symm)
    rw [hs, hc]
    exact ⟨hφ, e⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdStage

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open GlobalTheory.ProdFlatten in
unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two in
theorem equiv_of_iso_two {p q c r t N : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) (H : Iso (two e (pr x hx) (pr y hy)) (pr w hz)) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := H


open GlobalTheory.ProdFlatten in
unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one in
theorem equiv_of_iso {q c N : ℕ} (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (w a).1 = N) (H : Iso (pr y hy) (pr w hz)) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr w hz)) := H

theorem ind₂_prodIrr_empty {c q N : ℕ} (x : Fin 0 → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hw : List.ofFn w = List.ofFn y) (hx : ∑ a, (x a).1 = 0) (hy : ∑ a, (y a).1 = N)
    (hz : ∑ a, (w a).1 = N) (e : 0 + N = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  have A : Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr y hy)) :=
    GlobalTheory.ProdReorder.ind₂_unit_left k N 0 e _ (prodIrr y hy) (isSmooth_prodIrr y hy)
      (fun a => (x a).1) (fun a => (x a).2.rep.V) (fun a => (x a).rep) (stdBlocks (fun a => (x a).1) hx)
  have B : Nonempty ((prodIrr y hy).Equiv (prodIrr w hz)) :=
    equiv_of_iso y w hy hz (GlobalTheory.ProdFlatten.pr_congr hw.symm hy hz)
  exact A.elim fun a => B.elim fun b => ⟨a.trans b⟩

theorem ind₂_prodIrr_equiv_zero {q c r t N : ℕ} (x : Fin 0 → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hw : List.ofFn w = List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  have hr : r = 0 := by simpa using hx.symm
  subst hr
  have ht : t = N := by omega
  subst ht
  exact ind₂_prodIrr_empty x y w hw hx hy hz e

theorem ind₂_prodIrr_equiv_pos {p q c r t N : ℕ} (hp : p ≠ 0) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k))
    (w : Fin c → IrrGL (k := k)) (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r)
    (hy : ∑ a, (y a).1 = t) (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) :=
  equiv_of_iso_two x y w hx hy hz e
    (GlobalTheory.ProdFlatten.iso_symm (GlobalTheory.ProdFlatten.pr_append x y w hw (Or.inl hp) hx hy hz e))

theorem ind₂_prodIrr_equiv {p q c r t N : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  cases p with
  | zero => exact ind₂_prodIrr_equiv_zero x y w (by simpa using hw) hx hy hz e
  | succ n => exact ind₂_prodIrr_equiv_pos (Nat.succ_ne_zero n) x y w hw hx hy hz e

theorem prod₂_prodIrr_append : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t),
    Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)) :=
  fun _ _ _ _ _ _ _ _ _ x y hx hy h =>
    ind₂_prodIrr_equiv x y (Fin.append x y) (List.ofFn_fin_append x y) hx hy h rfl

end GlobalTheory.CompanionTheory.ProdStage
end
end

