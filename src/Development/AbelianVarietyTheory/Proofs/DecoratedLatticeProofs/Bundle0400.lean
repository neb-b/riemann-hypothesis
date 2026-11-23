module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylElementActsOnSchrodingerByFourier
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.WeylFourier

variable {D : D7}

theorem extX_mul_weyl {A B : HSp D} {w : GA D (dblSp A)} {b c : AE D}
    (hX : mt (dblSp A) w ⬝ (dblDec A).jX = -(b • (dblDec A).jY))
    (hY : mt (dblSp A) w ⬝ (dblDec A).jY = c • (dblDec A).jX) (x : Mx D B.rank A.rank) :
    (dblDec A).extX B x ⬝ mt (dblSp A) w = (dblDec A).extY B (c • x) := by
  refine (dblDec A).mat_ext ?_ (Matrix.ext fun _ j => Fin.elim0 j) ?_
  · simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, hX, Matrix.mul_neg, Matrix.mul_smul]
    rw [(dblDec A).pX_jY, (dblDec A).pY_jX, Matrix.mul_zero, Matrix.mul_zero, smul_zero, neg_zero]
  · simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, hY, Matrix.mul_smul]
    rw [(dblDec A).pX_jX, (dblDec A).pY_jY, Matrix.mul_one, Matrix.mul_one]

theorem symplO_extX_extY_smul {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : AE D) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T y) (d.extY T (c • x)) =
      trA (incA D D.host.xi0 * cA D c * Matrix.trace (GlobalTheory.StdUnn.inner T x y)) := by
  have h := d.hO_ext T y 0 0 (c • x) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, Matrix.trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS, adj_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc]
  rfl

theorem sch_weyl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ w : GA D (dblSp A), IsWeyl A w → mt (dblSp A) w ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) → mt (dblSp A) w ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x, sch ψ A B ν 𝓨 (omh (w, 1) f) x = ∫ y, sch ψ A B ν 𝓨 f y * ψ (trA (incA D (-D.host.xi0 / μ) * Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  intro D ψ A B χB omh hW ν 𝓨 hν μ hμ w hw hX hY f hf x
  set u : WO (dblSp A) B := (dblDec A).extY B (incA D μ⁻¹ • x) with hu
  have hact : actO (dblSp A) B w 1 u = (dblDec A).extX B x := by
    rw [actO_eq, mt_one, Matrix.one_mul, hu, ← extX_mul_weyl hX hY x, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
  have hf₁ : IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B u f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hW.std (dblSp A) B).1 u f hf
  have h1 : sch ψ A B ν 𝓨 (omh (w, 1) f) x = swSec A B omh ν 𝓨 (heisO ψ (dblSp A) B u f) w := by
    have h := congrFun (GlobalTheory.MixModel.Check.mixS_heis_extX (ψ := ψ) (dblDec A) ν 𝓨 (omh (w, 1) f) x 0) 0
    rw [zero_add, ← hact, ← hW.om_heis w 1 u f hf, mixS_dblDec_zero] at h
    exact h.symm
  rw [h1, _root_.GlobalTheory.Core.Rk.WeylValue.swSec_weyl D ψ A B χB omh hW ν 𝓨 hν _ hf₁ w hw]
  refine congrArg _ (funext fun y => ?_)
  have hc : incA D D.host.xi0 * cA D (incA D μ⁻¹) = incA D (-D.host.xi0 / μ) := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_inv₀, hμ.2, inv_neg, mul_neg, neg_div, div_eq_mul_inv]
  have h2 := GlobalTheory.MixModel.Check.mixS_heis_extY (dblDec A) hν hf (incA D μ⁻¹ • x) y 0
  rw [symplO_extX_extY_smul, hc, mul_comm] at h2
  exact h2

end GlobalTheory.StdUnn.WeylFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemFiniteAdelicUnitaryGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Corev.EmbAGfC

variable {D : D7}

abbrev finfR (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GfC_iff' (V : HSp D) (g : GA D V) : g ∈ GfC V ↔ (Formalism.L2.Theta.mt V g).map (finfR D) = 1 := by
  show infHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand' {k n : ℕ} (x : Mx D k n) (m : Mx D n n) (y : Mx D n k) (hm : m.map (finfR D) = 1) :
    (x ⬝ m ⬝ y).map (finfR D) = (x ⬝ y).map (finfR D) := by
  have e1 : (x ⬝ m ⬝ y).map (finfR D) = x.map (finfR D) ⬝ m.map (finfR D) ⬝ y.map (finfR D) := by
    rw [Matrix.map_mul (f := finfR D), Matrix.map_mul (f := finfR D)]
  have e2 : (x ⬝ y).map (finfR D) = x.map (finfR D) ⬝ y.map (finfR D) := Matrix.map_mul (f := finfR D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GfC' {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GfC A) :
    o.emb (a, 1) ∈ GfC S := by
  rw [mem_GfC_iff'] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finfR D)), map_sand' _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one,
    ← Matrix.map_add _ (map_add (finfR D)), o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem wittCoreEmbedding_mem_finiteAdelicUnitaryGroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {g : GA D S₀} (hg : g ∈ GfC S₀) :
    d.emb0 g ∈ GfC S := by
  rw [mem_GfC_iff'] at hg ⊢
  rw [HypDec.unitaryMatrix_wittCoreEmbedding, Matrix.map_add _ (map_add (finfR D)), Matrix.map_add _ (map_add (finfR D)), map_sand' _ _ _ hg,
    ← Matrix.map_add _ (map_add (finfR D)), ← Matrix.map_add _ (map_add (finfR D)), d.sum_eq_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem embA_mem_GfC_fin : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (κ : GA D A), κ ∈ GfC A → embA d o κ ∈ GfC S := by
  intro D S S₀ A L ρ d o κ hκ
  rw [embA_apply]
  exact wittCoreEmbedding_mem_finiteAdelicUnitaryGroup d (orth_emb_mem_GfC' o hκ)

end GlobalTheory.Corev.EmbAGfC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def dualC (𝔟 : FI D) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {c | ∀ b ∈ 𝔟, star b * c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range}
  add_mem' := fun {x y} hx hy b hb => by
    rw [mul_add]; exact add_mem (hx b hb) (hy b hb)
  zero_mem' := fun b _ => by rw [mul_zero]; exact zero_mem _
  smul_mem' := fun r x hx b hb => by
    obtain ⟨o, ho⟩ := hx b hb
    refine ⟨r * o, ?_⟩
    rw [map_mul, ho, Algebra.smul_def]; ring

theorem mem_dualC {𝔟 : FI D} {c : D.host.E} :
    c ∈ dualC 𝔟 ↔ ∀ b ∈ 𝔟, star b * c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := Iff.rfl

def crd {m : ℕ} (q : Matrix (Fin m) (Fin S.rank) D.host.E) : (Fin S.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin m → D.host.E) :=
  (Matrix.mulVecLin q).restrictScalars (𝓞 D.host.E)

def splitL (d : HypDec S S₀ ρ) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) : Lat S :=
  (⨅ i : Fin ρ, (𝔟 i : Submodule (𝓞 D.host.E) D.host.E).comap ((LinearMap.proj i).comp (crd d.qX))) ⊓
    L₀.comap (crd d.q0) ⊓ ⨅ i : Fin ρ, (dualC (𝔟 i)).comap ((LinearMap.proj i).comp (crd d.qY))

theorem mem_splitL (d : HypDec S S₀ ρ) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (y : Fin S.rank → D.host.E) :
    y ∈ splitL d L₀ 𝔟 ↔ (∀ i : Fin ρ, (d.qX *ᵥ y) i ∈ 𝔟 i) ∧ d.q0 *ᵥ y ∈ L₀ ∧ ∀ i : Fin ρ, (d.qY *ᵥ y) i ∈ dualC (𝔟 i) := by
  simp only [splitL, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply, LinearMap.proj_apply]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

variable (d : HypDec S S₀ ρ)

theorem qX_e : d.qX * d.e = 1 := d.e'e
theorem qX_i₀ : d.qX * d.i₀ = 0 := by
  have h := congrArg Matrix.conjTranspose d.i₀e'
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
    Matrix.conjTranspose_zero, HypDec.qX, HypDec.qY, Matrix.mul_assoc] using h
theorem qX_e' : d.qX * d.e' = 0 := d.e'e'
theorem qY_e : d.qY * d.e = 0 := d.ee
theorem qY_i₀ : d.qY * d.i₀ = 0 := by
  have h := congrArg Matrix.conjTranspose d.i₀e
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
    Matrix.conjTranspose_zero, HypDec.qX, HypDec.qY, Matrix.mul_assoc] using h
theorem qY_e' : d.qY * d.e' = 1 := by
  have h := congrArg Matrix.conjTranspose d.e'e
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
    Matrix.conjTranspose_one, HypDec.qY, Matrix.mul_assoc] using h
theorem wittDecomposition_coreProj_mul_e_eq_zero : d.q0 * d.e = 0 := by
  simp only [HypDec.q0, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.i₀e, Matrix.mul_zero]
theorem wittDecomposition_coreProj_mul_core_eq_one : d.q0 * d.i₀ = 1 := by
  rw [HypDec.q0, Matrix.mul_assoc, d.iso,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (gram_det_ne S₀))]
theorem wittZeroProjection_mul_dualBasis_eq_zero : d.q0 * d.e' = 0 := by
  simp only [HypDec.q0, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.i₀e', Matrix.mul_zero]

theorem gram_eq : S.gram = d.qYᴴ * d.qX + d.q0ᴴ * (S₀.gram * d.q0) + d.qXᴴ * d.qY := by
  have h0 : d.q0ᴴ * S₀.gram = S.gram * d.i₀ := by
    simp only [HypDec.q0, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (gram_det_ne S₀)), Matrix.mul_one]
  have hx : d.qXᴴ = S.gram * d.e' := by simp [HypDec.qX, gram_conjTranspose]
  have hy : d.qYᴴ = S.gram * d.e := by simp [HypDec.qY, gram_conjTranspose]
  rw [hy, hx, ← Matrix.mul_assoc d.q0ᴴ, h0]
  simp only [Matrix.mul_assoc, ← Matrix.mul_add, d.sum_eq_one_rat, Matrix.mul_one]

theorem rat_mulVec_gen {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (t : AF D.host.F) (x : Fin n → D.host.E) :
    rat M *ᵥ (fun l => t ⊗ₜ[D.host.F] (1 * x l)) = fun k => t ⊗ₜ[D.host.F] (1 * (M *ᵥ x) k) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, one_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k l) * (t ⊗ₜ[D.host.F] x l) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem rat_mulVec_mem_latV {S' : HSp D} (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat S'}
    (hM : ∀ x ∈ L, M *ᵥ x ∈ L') (P : Pl D → Prop) {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    rat M *ᵥ y ∈ latV S' L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [rat_mulVec_gen]
    exact AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, _, hM x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

variable {d} {L₀ : Lat S₀} {𝔟 : ℕ → FI D}

theorem e_mem {w : Fin ρ → D.host.E} (hw : ∀ i : Fin ρ, w i ∈ 𝔟 i) : d.e *ᵥ w ∈ splitL d L₀ 𝔟 := by
  refine (mem_splitL d L₀ 𝔟 _).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mulVec_mulVec, qX_e, Matrix.one_mulVec]; exact hw i
  · rw [Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_e_eq_zero, Matrix.zero_mulVec]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, qY_e, Matrix.zero_mulVec]; exact zero_mem _

theorem i₀_mem {x : Fin S₀.rank → D.host.E} (hx : x ∈ L₀) : d.i₀ *ᵥ x ∈ splitL d L₀ 𝔟 := by
  refine (mem_splitL d L₀ 𝔟 _).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mulVec_mulVec, qX_i₀, Matrix.zero_mulVec]
    show (0 : D.host.E) ∈ (𝔟 i : Submodule (𝓞 D.host.E) D.host.E); exact zero_mem _
  · rw [Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec]; exact hx
  · rw [Matrix.mulVec_mulVec, qY_i₀, Matrix.zero_mulVec]; exact zero_mem _

theorem e'_mem {w : Fin ρ → D.host.E} (hw : ∀ i : Fin ρ, w i ∈ dualC (𝔟 i)) : d.e' *ᵥ w ∈ splitL d L₀ 𝔟 := by
  refine (mem_splitL d L₀ 𝔟 _).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mulVec_mulVec, qX_e', Matrix.zero_mulVec]
    show (0 : D.host.E) ∈ (𝔟 i : Submodule (𝓞 D.host.E) D.host.E); exact zero_mem _
  · rw [Matrix.mulVec_mulVec, wittZeroProjection_mul_dualBasis_eq_zero, Matrix.zero_mulVec]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, qY_e', Matrix.one_mulVec]; exact hw i

theorem single_mem_of_mem {I : ℕ → Submodule (𝓞 D.host.E) D.host.E} (i : Fin ρ) {a : D.host.E} (ha : a ∈ I i) (j : Fin ρ) :
    (Pi.single i a : Fin ρ → D.host.E) j ∈ I j := by
  by_cases h : j = i
  · subst h; rw [Pi.single_eq_same]; exact ha
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

def colProj {m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) :
    Matrix (Fin S.rank) (Fin m) D.host.E := Matrix.of fun k l => f k i * q i l

theorem colProj_mulVec {m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ)
    (x : Fin m → D.host.E) : colProj q f i *ᵥ x = f *ᵥ Pi.single i ((q *ᵥ x) i) := by
  funext k
  simp only [colProj, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.single_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]

theorem colMul_rat {m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ)
    (y : Fin m → AE D) : colMul (rat f) i ((rat q *ᵥ y) i) = rat (colProj q f i) *ᵥ y := by
  funext k
  simp only [colMul, colProj, rat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem colMul_eq_mulVec {m n : ℕ} (x : Mx D m n) (i : Fin n) (a : AE D) : colMul x i a = x *ᵥ Pi.single i a := by
  funext k
  simp only [colMul, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, mul_comm]

theorem mulVec_eq_sum_colMul {m n : ℕ} (x : Mx D m n) (w : Fin n → AE D) : x *ᵥ w = ∑ i, colMul x i (w i) := by
  funext k
  simp only [colMul, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

variable (d L₀ 𝔟)

theorem monoAt_splitL (v : Pl D) : MonoAt d (splitL d L₀ 𝔟) L₀ v := by
  have hX : ∀ i : Fin ρ, ∀ x ∈ splitL d L₀ 𝔟, colProj d.qX d.e i *ᵥ x ∈ splitL d L₀ 𝔟 := fun i x hx => by
    rw [colProj_mulVec]
    exact e_mem (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i
      (((mem_splitL d L₀ 𝔟 x).1 hx).1 i))
  have hY : ∀ i : Fin ρ, ∀ x ∈ splitL d L₀ 𝔟, colProj d.qY d.e' i *ᵥ x ∈ splitL d L₀ 𝔟 := fun i x hx => by
    rw [colProj_mulVec]
    exact e'_mem (single_mem_of_mem (I := fun j => dualC (𝔟 j)) i (((mem_splitL d L₀ 𝔟 x).1 hx).2.2 i))
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hX i) _ hy
    · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hY i) _ hy
    · exact rat_mulVec_mem_latV d.q0 (fun x hx => ((mem_splitL d L₀ 𝔟 x).1 hx).2.1) _ hy
  · rintro ⟨h1, h3, h2⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        (show d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY = 1 from by
          have h := congrArg rat d.sum_eq_one_rat
          simpa only [rat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), HypDec.jX, HypDec.j0,
            HypDec.jY, HypDec.pX, HypDec.p0, HypDec.pY] using h), Matrix.one_mulVec]
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
    exact rat_mulVec_mem_latV d.i₀ (fun x hx => i₀_mem hx) _ h2

theorem line_splitL (v : Pl D) (i : Fin ρ) (a : AE D) :
    colMul d.jX i a ∈ latV S (splitL d L₀ 𝔟) (· = v) ↔ a ∈ idV (𝔟 i) v := by
  constructor
  · intro ha
    have key : ∀ y ∈ latV S (splitL d L₀ 𝔟) (· = v), (d.pX *ᵥ y) i ∈ idV (𝔟 i) v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
        rw [Set.mem_singleton_iff] at hc
        subst hc
        change (rat d.qX *ᵥ _) i ∈ _
        rw [rat_mulVec_gen]
        refine AddSubgroup.subset_closure ⟨β, hβi, hβ, _, ?_, rfl⟩
        rw [one_mul]
        exact ((mem_splitL d L₀ 𝔟 x).1 hx).1 i
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
      | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz
    have h := key _ ha
    rwa [colMul_eq_mulVec, Matrix.mulVec_mulVec, (show d.pX * d.jX = 1 from by
      have h := congrArg rat (qX_e d)
      simpa only [rat, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), HypDec.pX, HypDec.jX] using h), Matrix.one_mulVec, Pi.single_eq_same] at h
  · intro ha
    rw [idV] at ha
    induction ha using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, b, hb, rfl⟩ := hz
      have e : colMul d.jX i (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
          rat d.e *ᵥ fun l => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (Pi.single i b : Fin ρ → D.host.E) l) := by
        rw [colMul_eq_mulVec]
        change rat d.e *ᵥ _ = _
        congr 1
        funext l
        by_cases h : l = i
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      rw [e, rat_mulVec_gen]
      exact AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, _,
        e_mem (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i hb), rfl⟩
    | zero =>
      have : colMul d.jX i 0 = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    | add z z' _ _ hz hz' =>
      have : colMul d.jX i (z + z') = colMul d.jX i z + colMul d.jX i z' := by funext k; simp [colMul, add_mul]
      rw [this]; exact add_mem hz hz'
    | neg z _ hz =>
      have : colMul d.jX i (-z) = -colMul d.jX i z := by funext k; simp [colMul]
      rw [this]; exact neg_mem hz

end GlobalTheory.SeeSaw.SplitLat

end
end

