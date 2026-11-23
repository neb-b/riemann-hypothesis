module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSumLeibniz
section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem coefwise_dbar_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) v)
    (hF : ∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) (w : V n) :
    coefwise (fun f => GlobalTheory.dbar f v w) (fun x => ∑ i, c i x • F i x) =
      ∑ i, (GlobalTheory.dbar (c i) v w • F i v + c i v • coefwise (fun f => GlobalTheory.dbar f v w) (F i)) := by
  have h (S : Finset (Fin (n + n))) :
      GlobalTheory.dbar (fun x => (bas n).repr (∑ i, c i x • F i x) S) v w =
        ∑ i, (c i v * GlobalTheory.dbar (fun x => (bas n).repr (F i x) S) v w +
          GlobalTheory.dbar (c i) v w * (bas n).repr (F i v) S) := by
    have e : (fun x => (bas n).repr (∑ i, c i x • F i x) S) =
        fun x => ∑ i, c i x * (bas n).repr (F i x) S := by
      funext x
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finsupp.finsetSum_apply]
    rw [e, GlobalTheory.dbar_sum (A := fun i x => c i x * (bas n).repr (F i x) S) (fun i _ => (hc i).mul (hF i S)),
      ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.dbar_mul (hc i) (hF i S) w
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (bas n).sum_repr (F i v)]
  simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  rw [add_comm]

theorem dbarAt_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) v)
    (hF : ∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) :
    dbarAt (fun x => ∑ i, c i x • F i x) v =
      ∑ i, ((∑ a, GlobalTheory.dbar (c i) v (coordVec a) • dzb a) * F i v + c i v • dbarAt (F i) v) := by
  simp only [dbarAt, coefwise_dbar_sum_smul hc hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_add, mul_smul_comm, smul_mul_assoc, Finset.sum_mul, Finset.sum_add_distrib, Finset.smul_sum]

end GlobalTheory.CxForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryRationalPointSplitFiniteInfinite
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RatSplit

theorem ratU_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n,
    ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧
      ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := by
  intro E _ _ _ n γ hγ
  obtain ⟨g0, hg0⟩ := (Subgroup.mem_subgroupOf.1 hγ : γ.1 ∈ (ratGL E n).range)
  have hval : γ.1.val = g0.val.map (algebraMap E (Ad E)) := by rw [← hg0]; rfl

  have hU : g0 ∈ UE E n := by
    have h2 : cT (conjAd E) γ.1.val * 1 * γ.1.val = 1 := γ.2
    show cT (IsCMField.complexConj E).toRingEquiv.toRingHom g0.val * 1 * g0.val = 1
    have hinj : Function.Injective (algebraMap E (Ad E)) := by
      intro x y hxy
      have τ := (Classical.arbitrary (InfinitePlace E)).embedding
      exact τ.injective (by rw [← coord_algebraMap τ x, ← coord_algebraMap τ y, hxy])
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul,
      FinPtLoc.map_cT (algebraMap E (Ad E)) _ (conjAd E) (fun x => (conjAd_algebraMap x).symm),
      Matrix.map_one _ (map_zero _) (map_one _), ← hval, h2]
  refine ⟨⟨g0, hU⟩, ?_, ?_⟩
  · set a : finU (E := E) (n := n) := finPt ⟨g0, hU⟩ with ha
    have haval : ((a : UA E n) : GA E n) = finGL E n (ratF E n g0) := by
      rw [ha, FinPtLoc.finPt_eq]
    have hb : (a : UA E n)⁻¹ * γ ∈ infU E n := by
      show GeneralLinearGroup.map (pFin E) (((a : UA E n)⁻¹ * γ : UA E n) : GA E n) = 1
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, haval, pFin_finGL, ← hg0]
      have : GeneralLinearGroup.map (pFin E) (ratGL E n g0) = ratF E n g0 := by
        apply Units.ext; ext i j; rfl
      rw [this, inv_mul_cancel]
    have hγs : γ = (a : UA E n) * ((⟨_, hb⟩ : infU E n) : UA E n) := by
      simp
    rw [hγs, splitFin_mul]
  · intro v
    apply Units.ext
    ext i j
    change coord v.embedding (pInf E (γ.1.val i j)) = v.embedding (g0.val i j)
    rw [hval, Matrix.map_apply, coord_algebraMap]

end GlobalTheory.BCT.RatSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMRealLineFiniteInvariant
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisDerivCM

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symplOHF_add_left (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (x + x') y = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x' y := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem map_symplOHF_eq_zero {B : Type} [CommRing B] [Algebra F B] (p : AF F →ₐ[F] B)
    (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y : WOF F E nS nT)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0) :
    p (symplOHF σ JS JT ξ₀ x y) = 0 := by
  have h1 : p (symplOF σ JS JT ξ₀ x y) = 0 := by
    unfold symplOF hOF
    rw [GlobalTheory.WeilVacMove.sum_reorder (cAF σ) (fun k i => incAF F E (JS⁻¹ k i)) (fun j l => incAF F E (JT j l)) x y]
    refine GlobalTheory.FockCompare.map_trace_sesq_eq_zero p σ _ (fun k i => incAF F E (JS⁻¹ k i))
      (fun j l => incAF F E (JT j l)) xᵀ yᵀ (h.imp (fun h => ?_) fun h => ?_) <;>
    · ext i j
      exact congrFun (congrFun h j) i
  unfold symplOHF
  rw [map_mul, h1, mul_zero]

theorem symplOHF_fin_real (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u v : WOF F E nS nT)
    (hu : u.map (infPartF F E) = 0) (hv : v.map (finPartF F E) = 0) :
    symplOHF σ JS JT ξ₀ u v = 0 ∧ symplOHF σ JS JT ξ₀ v u = 0 :=
  ⟨Prod.ext (map_symplOHF_eq_zero (fstA F) σ JS JT ξ₀ u v (Or.inl hu))
      (map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ u v (Or.inr hv)),
    Prod.ext (map_symplOHF_eq_zero (fstA F) σ JS JT ξ₀ v u (Or.inr hu))
      (map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ v u (Or.inl hv))⟩

theorem heisOF_deriv_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ u : Formalism.IndefR.DatumF.WOF F E nS nT, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) f = f →
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) (fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0) = fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f L _ hL u hu hf
  funext w
  have key : ∀ t : ℝ, B.ψ (symplOHF σ JS JT ξ₀ w u) * heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u) =
      heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    obtain ⟨h1, h2⟩ := symplOHF_fin_real σ JS JT ξ₀ u (L t) hu (hL t)
    have hfx := congrFun hf (w + L t)
    simp only [heisOF] at hfx ⊢
    conv_rhs => rw [← hfx]
    rw [symplOHF_add_left, symplOHF_add_left, h1, h2, add_zero, add_zero,
      show w + u + L t = w + L t + u by abel]
    ring
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u)) 0 = _
  rw [← deriv_const_mul_field]
  exact congrArg (fun g : ℝ → ℂ => deriv g 0) (funext key)

end GlobalTheory.HeisDerivCM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMThetaQuasiInvariantRational
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaDerivQuasi

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symplOHF_add_left' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (x + x') y = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x' y := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_add_right' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (y + y') = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x y' := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

end GlobalTheory.ThetaDerivQuasi

theorem GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
      deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w)) 0 = B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) * deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f hf L _ _ γ w
  have key : ∀ t : ℝ, Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w) =
      B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
        Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    simp only [Formalism.IndefR.DatumF.heisOF]
    rw [add_assoc, hf.quasi γ (w + L t), GlobalTheory.ThetaDerivQuasi.symplOHF_add_left',
      GlobalTheory.ThetaDerivQuasi.symplOHF_add_right', neg_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    have h1 : B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) *
        B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L t)) *
      B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w) * f (w + L t)) * h1
  simp_rw [key]
  exact congrFun (deriv_const_mul_field' _) 0

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivedActionIntertwinesOfGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Complex SchwartzMap
open scoped Real RealInnerProductSpace Topology

namespace GlobalTheory.RealWeil.DRhoTransfer

variable {l : Type} [Fintype l]

theorem exists_decay (h : Sch l) (N : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, (1 + ‖y‖) ^ N * ‖h y‖ ≤ M := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h, by positivity, fun y => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (le_refl N) (le_refl 0) h y
  simpa [norm_iteratedFDeriv_zero] using this

theorem translate_bound (h : Sch l) (N : ℕ) (p : EuclideanSpace ℝ l) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, |s| ≤ 1 → ∀ x, ‖h (x + s • p)‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ := by
  obtain ⟨M, hM, hb⟩ := exists_decay h N
  refine ⟨M * (1 + ‖p‖) ^ N, by positivity, fun s hs x => ?_⟩
  have h1 : 1 + ‖x‖ ≤ (1 + ‖x + s • p‖) * (1 + ‖p‖) := by
    have h0 : ‖x‖ ≤ ‖x + s • p‖ + ‖s • p‖ := by
      have := norm_sub_le (x + s • p) (s • p)
      simpa using this
    have h2 : ‖s • p‖ ≤ ‖p‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hs
    nlinarith [norm_nonneg (x + s • p), norm_nonneg p]
  have h3 : (1 + ‖x‖) ^ N ≤ (1 + ‖x + s • p‖) ^ N * (1 + ‖p‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 N
  have hpos : 0 < (1 + ‖x‖) ^ N := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖h (x + s • p)‖ * (1 + ‖x‖) ^ N ≤ ‖h (x + s • p)‖ * ((1 + ‖x + s • p‖) ^ N * (1 + ‖p‖) ^ N) := by
        gcongr
    _ = ((1 + ‖x + s • p‖) ^ N * ‖h (x + s • p)‖) * (1 + ‖p‖) ^ N := by ring
    _ ≤ M * (1 + ‖p‖) ^ N := by gcongr; exact hb _

theorem lintegral_inv_pow_lt_top (K : ℝ) :
    ∫⁻ x : EuclideanSpace ℝ l, ‖K * ((1 + ‖x‖) ^ (Module.finrank ℝ (EuclideanSpace ℝ l) + 1))⁻¹‖ₑ ^ 2 < ⊤ := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  have hi := integrable_one_add_norm (E := EuclideanSpace ℝ l) (μ := volume) (r := 2 * N)
    (by rw [hN]; push_cast; have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EuclideanSpace ℝ l)); linarith)
  have hi2 := hi.const_mul (K ^ 2)
  have e : ∀ x : EuclideanSpace ℝ l, ‖K * ((1 + ‖x‖) ^ N)⁻¹‖ₑ ^ 2 = ‖K ^ 2 * (1 + ‖x‖) ^ (-(2 * N : ℝ))‖ₑ := by
    intro x
    rw [← enorm_pow, mul_pow, inv_pow, ← pow_mul, Real.rpow_neg (by positivity),
      show (2 * (N : ℝ)) = ((N * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  simp_rw [e]
  exact hi2.hasFiniteIntegral

theorem taylor_bound (w : l ⊕ l → ℝ) (f : Sch l) :
    ∃ B : EuclideanSpace ℝ l → ℝ, (∀ x, 0 ≤ B x) ∧ (∫⁻ x, ‖B x‖ₑ ^ 2 < ⊤) ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x, ‖rhoFun (t • w) f x - f x - t * dRho w f x‖ ≤ t ^ 2 * B x := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1
  obtain ⟨M, hM, hb⟩ := translate_bound (dRho w (dRho w f)) N (pPart w)
  refine ⟨fun x => M * ((1 + ‖x‖) ^ N)⁻¹, fun x => by positivity, lintegral_inv_pow_lt_top M, fun t ht x => ?_⟩
  set h := dRho w f with hh
  have hB : ∀ s : ℝ, |s| ≤ 1 → ‖rhoFun (s • w) (dRho w h) x‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ := fun s hs => by
    rw [rhoFun, norm_mul, norm_phase, one_mul, pPart_smul]
    exact hb s hs x
  have habs : ∀ s σ : ℝ, σ ∈ Set.uIcc 0 s → |σ| ≤ |s| := fun s σ hσ => by
    simpa using Set.abs_sub_left_of_mem_uIcc hσ
  have step1 : ∀ s : ℝ, |s| ≤ 1 → ‖rhoFun (s • w) h x - h x‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ * |s| := by
    intro s hs
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun σ : ℝ => rhoFun (σ • w) h x)
      (f' := fun σ => rhoFun (σ • w) (dRho w h) x) (s := Set.uIcc 0 s) (C := M * ((1 + ‖x‖) ^ N)⁻¹)
      (fun σ _ => (hasDerivAt_rhoFun_at w h x σ).hasDerivWithinAt)
      (fun σ hσ => hB σ ((habs s σ hσ).trans hs)) (convex_uIcc 0 s) Set.left_mem_uIcc Set.right_mem_uIcc
    simpa [rhoFun_zero, Real.norm_eq_abs] using this
  have hd : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => rhoFun (σ • w) f x - f x - σ * h x)
      (rhoFun (σ • w) h x - h x) σ := fun σ => by
    have e1 : HasDerivAt (fun σ : ℝ => (σ : ℂ) * h x) (h x) σ := by
      simpa using (hasDerivAt_id σ).ofReal_comp.mul_const (h x)
    exact ((hasDerivAt_rhoFun_at w f x σ).sub_const (f x)).sub e1
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun σ : ℝ => rhoFun (σ • w) f x - f x - σ * h x)
    (f' := fun σ => rhoFun (σ • w) h x - h x) (s := Set.uIcc 0 t) (C := M * ((1 + ‖x‖) ^ N)⁻¹ * |t|)
    (fun σ _ => (hd σ).hasDerivWithinAt)
    (fun σ hσ => (step1 σ ((habs t σ hσ).trans ht)).trans (mul_le_mul_of_nonneg_left (habs t σ hσ) (by positivity)))
    (convex_uIcc 0 t) Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [zero_smul, rhoFun_zero, sub_self, ofReal_zero, zero_mul, sub_zero, Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [← sq_abs t]
  ring

theorem enorm_sub_sq_le (a b : ℂ) : ‖a - b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  simp only [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_sub_le a b, norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]

theorem lintegral_le_of_bound (φ : EuclideanSpace ℝ l → ℂ) (B : EuclideanSpace ℝ l → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ x, 0 ≤ B x) (h : ∀ x, ‖φ x‖ ≤ c * B x) :
    ∫⁻ x, ‖φ x‖ₑ ^ 2 ≤ ENNReal.ofReal c ^ 2 * ∫⁻ x, ‖B x‖ₑ ^ 2 := by
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x => ?_
  rw [← mul_pow]
  gcongr
  calc ‖φ x‖ₑ = ENNReal.ofReal ‖φ x‖ := (ofReal_norm_eq_enorm _).symm
    _ ≤ ENNReal.ofReal (c * B x) := ENNReal.ofReal_le_ofReal (h x)
    _ = ENNReal.ofReal c * ‖B x‖ₑ := by rw [ENNReal.ofReal_mul hc, Real.enorm_eq_ofReal (hB x)]

theorem dRho_intertwine : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w (f f' : GlobalTheory.RealWeil.Sch l), ⇑f' = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(A' f') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' f)) →
    ∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f) := by
  intro l _ L' A' C hC hA hI w f
  obtain ⟨B₁, hB₁0, hB₁i, hB₁⟩ := taylor_bound w f
  obtain ⟨B₂, hB₂0, hB₂i, hB₂⟩ := taylor_bound (L' w) (A' f)
  set u := A' (dRho w f) - dRho (L' w) (A' f) with hu
  have t1 : ∫⁻ x, ‖B₁ x‖ₑ ^ 2 ≠ ⊤ := hB₁i.ne
  have t2 : (2 : ℝ≥0∞) * C ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hC
  have t4 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = 2 * C * (∫⁻ x, ‖B₁ x‖ₑ ^ 2) + 2 * ∫⁻ x, ‖B₂ x‖ₑ ^ 2 := ⟨_, rfl⟩
  have hKt : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top t2 t1, ENNReal.mul_ne_top t4 hB₂i.ne⟩
  have hmeas : ∀ g : Sch l, AEMeasurable (fun x => ‖g x‖ₑ ^ 2) volume := fun g =>
    ((ENNReal.continuous_pow 2).comp g.continuous.enorm).aemeasurable
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ ENNReal.ofReal (t ^ 2) * K := by
    intro t ht0 ht1
    have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
    obtain ⟨g, hg⟩ := exists_schwartz_rhoFun l (t • w) f
    have hAg : ⇑(A' g) = rhoFun (t • L' w) ⇑(A' f) := by rw [hI (t • w) f g hg, map_smul]
    set k := g - f - (t : ℂ) • dRho w f with hk
    set m := A' g - A' f - (t : ℂ) • dRho (L' w) (A' f) with hm
    have hkb : ∀ x, ‖k x‖ ≤ t ^ 2 * B₁ x := fun x => by
      have e : k x = rhoFun (t • w) f x - f x - t * dRho w f x := by
        simp only [hk, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hg]
      rw [e]; exact hB₁ t hta x
    have hmb : ∀ x, ‖m x‖ ≤ t ^ 2 * B₂ x := fun x => by
      have e : m x = rhoFun (t • L' w) (A' f) x - A' f x - t * dRho (L' w) (A' f) x := by
        simp only [hm, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hAg]
      rw [e]; exact hB₂ t hta x
    have hum : (t : ℂ) • u = m - A' k := by
      simp only [hu, hk, hm, map_sub, map_smul, smul_sub]
      abel
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0∞, a = ENNReal.ofReal (t ^ 2) := ⟨_, rfl⟩
    have ha0 : a ≠ 0 := ha ▸ (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hat : a ≠ ⊤ := ha ▸ ENNReal.ofReal_ne_top
    have hIk := lintegral_le_of_bound k B₁ (by positivity) hB₁0 hkb
    have hIm := lintegral_le_of_bound m B₂ (by positivity) hB₂0 hmb
    have hsc : ∀ x, ‖((t : ℂ) • u) x‖ₑ ^ 2 = a * ‖u x‖ₑ ^ 2 := fun x => by
      rw [SchwartzMap.smul_apply, enorm_smul, mul_pow, ha, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have main : a * ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ a * (a * K) := by
      calc a * ∫⁻ x, ‖u x‖ₑ ^ 2 = ∫⁻ x, ‖((t : ℂ) • u) x‖ₑ ^ 2 := by
            rw [← lintegral_const_mul' _ _ hat]; simp only [hsc]
        _ = ∫⁻ x, ‖m x - A' k x‖ₑ ^ 2 := by rw [hum]; simp only [SchwartzMap.sub_apply]
        _ ≤ ∫⁻ x, (2 * ‖m x‖ₑ ^ 2 + 2 * ‖A' k x‖ₑ ^ 2) := lintegral_mono fun x => enorm_sub_sq_le _ _
        _ = 2 * (∫⁻ x, ‖m x‖ₑ ^ 2) + 2 * ∫⁻ x, ‖A' k x‖ₑ ^ 2 := by
            rw [lintegral_add_left' ((hmeas m).const_mul 2), lintegral_const_mul' _ _ t4, lintegral_const_mul' _ _ t4]
        _ ≤ 2 * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₂ x‖ₑ ^ 2) +
              2 * (C * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₁ x‖ₑ ^ 2)) := by
            have hAk : ∫⁻ x, ‖A' k x‖ₑ ^ 2 ≤ C * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₁ x‖ₑ ^ 2) :=
              (hA k).trans (by gcongr)
            gcongr
        _ = a * (a * K) := by rw [hK, ha]; ring
    rw [← ha]
    exact (ENNReal.mul_le_mul_iff_right ha0 hat).mp main
  have hz : ∫⁻ x, ‖u x‖ₑ ^ 2 = 0 := by
    refine le_antisymm ?_ bot_le
    have ht : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ 2) * K) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal ((continuous_pow 2).tendsto (0 : ℝ)))
        (Or.inr hKt)
      simpa using this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact key t ht.1 ht.2.le
  have hae := (lintegral_eq_zero_iff' (hmeas u)).1 hz
  have hu0 : ⇑u = fun _ => (0 : ℂ) := by
    refine (Continuous.ae_eq_iff_eq volume u.continuous (continuous_const (y := (0 : ℂ)))).1 ?_
    filter_upwards [hae] with x hx
    have hx' : ‖u x‖ₑ ^ 2 = 0 := hx
    simpa using hx'
  have : u = 0 := by ext x; simpa using congrFun hu0 x
  exact sub_eq_zero.1 this

end GlobalTheory.RealWeil.DRhoTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsRationalOfRational
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.DblSchr.ddr_rat : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ x : Matrix (Fin T.rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E, ∃ y z : κ ⊕ κ → D.host.F,
      (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  intro D S T JA JB ξ κ _ co h x
  obtain ⟨y₁, z₁, h₁⟩ := h (x.submatrix id finSumFinEquiv).toCols₁
  obtain ⟨y₂, z₂, h₂⟩ := h (x.submatrix id finSumFinEquiv).toCols₂
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  rw [GlobalTheory.DblSchr.ddr, GlobalTheory.DblSchr.reD_e, Equiv.symm_symm]
  have e1 : ((incM D.host.F x).submatrix id finSumFinEquiv).toCols₁ = incM D.host.F (x.submatrix id finSumFinEquiv).toCols₁ := rfl
  have e2 : ((incM D.host.F x).submatrix id finSumFinEquiv).toCols₂ = incM D.host.F (x.submatrix id finSumFinEquiv).toCols₂ := rfl
  simp only [GlobalTheory.DblSchr.dblD, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, e1, e2, h₁, h₂]
  refine Prod.ext ?_ ?_
  · funext i; rcases i with i | i <;> rfl
  · funext i; rcases i with i | i <;> simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPoint
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory.GenericCoords

theorem exists_affine_etale_coords : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧
      ∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale := by
  intro k _ X _ p D h
  obtain ⟨U, t, hU, hη, he⟩ := GlobalTheory.GenericEtale.exists_etale_coords h
  exact ⟨U, hU, hη, t, he⟩

end GlobalTheory.GenericCoords
end

