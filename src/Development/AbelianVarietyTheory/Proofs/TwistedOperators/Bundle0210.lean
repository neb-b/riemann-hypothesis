module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairSplitTorus
section
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd

noncomputable section

namespace GlobalTheory.SplitTorus

variable {n : ℕ} (ε : Fin n → Bool)

def bJ (u y : Fin n → ℂ) : ℂ := star u ⬝ᵥ (Jm ε *ᵥ y)

variable {ε}

theorem coord {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (b : Fin n) (y : Fin n → ℂ) :
    bJ ε (P *ᵥ Pi.single b 1) y = ((Pᴴ * Jm ε * P) *ᵥ (P⁻¹ *ᵥ y)) b := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  conv_lhs => rw [show y = P *ᵥ (P⁻¹ *ᵥ y) by rw [mulVec_mulVec, hPP, one_mulVec]]
  rw [bJ, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  simp [Pi.star_def, Pi.single_apply, dotProduct]

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
include hP hpq hG

end

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
include hP hpq hG

end

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IncASmulMemAdelicCompletionMatrixGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section

namespace GlobalTheory.HatScalar

theorem smul_mem_tens_of {E : Type} [Field E] [NumberField E] {n r : ℕ} {Λ : Lt E n} {L L' : Lt E r} (c : E)
    (h : ∀ u ∈ L, c • u ∈ L') {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) :
    c • y ∈ tens Λ L' := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨v, hv, c • u, h u hu, ?_⟩
    rw [Matrix.vecMulVec_smul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem incA_smul_mem_hatA (D : D7) (S T : HSp D) (Λ : Lt D.host.E S.rank) (L1 L2 : Lt D.host.E T.rank)
    (c : D.host.E) (h : ∀ v ∈ L1, c • v ∈ L2) :
    ∀ u ∈ hatA S T (tens Λ L1), incA D c • u ∈ hatA S T (tens Λ L2) := by
  intro u hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, c • y, smul_mem_tens_of c h hy, ?_⟩
    ext a k
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    show (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] AF D.host.F ⊗[D.host.F] D.host.E) c *
      _ = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.HatScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSize
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLimit

theorem integral_eq_zero_of_approx {X : Type} [MeasurableSpace X] {μ : Measure X} {u : ℕ → X → ℂ} {v : X → ℂ}
    {w : X → ℝ} (hu : ∀ n, Integrable (u n) μ) (hv : Integrable v μ) (hw : Integrable w μ)
    (h0 : ∀ n, ∫ x, u n x ∂μ = 0) (h : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x, ‖u n x - v x‖ ≤ ε * w x) :
    ∫ x, v x ∂μ = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ := fun ε hε => by
    obtain ⟨n, hn⟩ := h ε hε
    have e : ∫ x, (u n x - v x) ∂μ = -∫ x, v x ∂μ := by rw [integral_sub (hu n) hv, h0, zero_sub]
    rw [← norm_neg, ← e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)
  have t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ)) :=
    ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul] at t
  exact norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))

theorem isCuspFun_of_tendsto : ∀ (D : D7) (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ) (f : GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ (∀ γ ∈ GQ V, ∀ g, ψ n (γ * g) = ψ n g) ∧ IsCuspFun V (ψ n)) → Continuous f → (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → Filter.Tendsto (fun n => GlobalTheory.Size.growthSize V N (ψ n - f)) Filter.atTop (nhds 0) → IsCuspFun V f := by
  intro D V N ψ f hψ hf hl ht
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
      ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRat D.sp.cm V W) 𝓕 μ → ∀ g : GA D V,
        IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl W hW μ hμ 𝓕 h𝓕 g
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.Size.quotHeight_laws V
  have hw := (hint (fun x => ((GlobalTheory.Grow.quotHeight V x ^ N : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (h4.pow N)) (fun γ hγ x => by rw [h2 γ hγ]) W hW μ hμ 𝓕 h𝓕 g).re
  refine integral_eq_zero_of_approx (μ := μ.restrict 𝓕) (u := fun k n => ψ k (n.1 * g)) (v := fun n => f (n.1 * g))
    (fun k => hint _ (hψ k).1 (hψ k).2.1 W hW μ hμ 𝓕 h𝓕 g) (hint _ hf hl W hW μ hμ 𝓕 h𝓕 g) hw
    (fun k => (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ k).2.2 W hW μ hμ 𝓕 h𝓕 g) fun ε hε => ?_
  obtain ⟨k, hk⟩ := (ht.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  refine ⟨k, fun n => ?_⟩
  rw [GlobalTheory.Size.growthSize_eq_quot (fun γ hγ x => by
    rw [Pi.sub_apply, Pi.sub_apply, (hψ k).2.1 γ hγ, hl γ hγ])] at hk
  have := (ENNReal.ofReal_le_ofReal_iff hε.le).1 ((le_iSup _ (n.1 * g)).trans hk)
  exact (div_le_iff₀ (pow_pos (lt_of_lt_of_le one_pos (h1 _).1) N)).1 this

end GlobalTheory.CuspLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRadicalSpanGMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesRadical

theorem isRadical_span_g_mul : ∀ (D : D7),
    (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}).IsRadical := by
  intro D
  have hrad : ∀ i : Fin 2, (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)}).IsRadical := fun i =>
    GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver D.host.E (D.host.g i) (D.host.g_prime i)
      ((Formalism.MainNotions.Inhab.primesOver_ncard D.host.E (D.host.g i) (D.host.g_prime i)).trans (D.nd.g_split i))
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  have hsup : Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.E)} ⊔ Ideal.span {((D.host.g 1 : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    have h1 : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
      have h2 := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 D.host.E))
      simpa using h2
    exact Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_span_singleton_iff _ _).2 h1)
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, Ideal.mul_eq_inf_of_coprime hsup]
  exact (hrad 0).inf (hrad 1)

end GlobalTheory.TypePrimesRadical
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicStabilizerSplitPlaceInConjParabolics
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitStab

open scoped Matrix

theorem exists_basis_adapted {k : Type} [Field k] {r : ℕ} (U : Submodule k (Fin r → k)) :
    ∃ b : Module.Basis (Fin r) k (Fin r → k),
      (∀ j : Fin r, j.val < Module.finrank k U → b j ∈ U) ∧
      ∀ x ∈ U, ∀ i : Fin r, Module.finrank k U ≤ i.val → b.repr x i = 0 := by
  obtain ⟨C, hC⟩ := U.exists_isCompl
  set a := Module.finrank k U with ha
  have hsum : a + Module.finrank k C = r := by
    rw [ha, Submodule.finrank_add_eq_of_isCompl hC, Module.finrank_fin_fun]
  have hCr : Module.finrank k C = r - a := by omega
  let bU : Module.Basis (Fin a) k U := Module.finBasisOfFinrankEq k U rfl
  let bC : Module.Basis (Fin (r - a)) k C := Module.finBasisOfFinrankEq k C hCr
  let B : Module.Basis (Fin a ⊕ Fin (r - a)) k (Fin r → k) := (bU.prod bC).map (U.prodEquivOfIsCompl C hC)
  let e : Fin a ⊕ Fin (r - a) ≃ Fin r := finSumFinEquiv.trans (finCongr (by omega))
  refine ⟨B.reindex e, fun j hj => ?_, fun x hx i hi => ?_⟩
  · have hj' : e.symm j = Sum.inl ⟨j.val, hj⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp [e]
    rw [Module.Basis.reindex_apply, hj']
    simp [B]
  · have hi' : e.symm i = Sum.inr ⟨i.val - a, by omega⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp [e]; omega
    rw [Module.Basis.repr_reindex_apply, hi']
    simp only [B, Module.Basis.map_repr, LinearEquiv.trans_apply]
    rw [show x = ((⟨x, hx⟩ : U) : Fin r → k) from rfl, Submodule.prodEquivOfIsCompl_symm_apply_left,
      Module.Basis.prod_repr_inr]
    simp

theorem inConjParabolic_of_maps {k : Type} [Field k] {r : ℕ} (H : Subgroup (GL (Fin r) k))
    (U : Submodule k (Fin r → k)) (hH : ∀ p ∈ H, ∀ u ∈ U, (p : Matrix (Fin r) (Fin r) k) *ᵥ u ∈ U) :
    InConjParabolic H (Module.finrank k U) := by
  obtain ⟨b, hb1, hb2⟩ := exists_basis_adapted U
  let φ : (Fin r → k) ≃ₗ[k] (Fin r → k) := b.equivFun.symm
  let g : GL (Fin r) k :=
    ⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨g, fun p hp i j hj hi => ?_⟩
  have key : ((g⁻¹ * p * g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) i j =
      b.repr ((p : Matrix (Fin r) (Fin r) k) *ᵥ b j) i := by
    have := congrFun (Matrix.mulVec_single_one ((g⁻¹ * p * g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) j) i
    rw [Matrix.col_apply] at this
    rw [← this, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (LinearMap.toMatrix' φ.symm.toLinearMap *ᵥ ((p : Matrix (Fin r) (Fin r) k) *ᵥ
      (LinearMap.toMatrix' φ.toLinearMap *ᵥ Pi.single j 1))) i = _
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    simp [φ]
  rw [key]
  exact hb2 _ (hH p hp _ (hb1 j hj)) i hi

end GlobalTheory.SplitStab

namespace GlobalTheory.SplitStab

open scoped Matrix TensorProduct
open GlobalTheory.AutFunCompare (colSpan exists_colSpan mem_extSub_colSpan)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : HeightOneSpectrum (𝓞 F)}


omit [NumberField E] in
theorem splitVec_map_inclR_mulVec (τ : E →ₐ[F] Fv F v) {n r : ℕ} (C : Matrix (Fin n) (Fin r) E)
    (a : Fin r → Fv F v ⊗[F] E) :
    splitVec τ ((C.map (inclR (Fv F v))) *ᵥ a) = (C.map τ) *ᵥ fun k => splitProj τ (a k) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [splitVec, Matrix.mulVec, dotProduct, map_sum, map_mul, splitProj_inclR]

end GlobalTheory.SplitStab

namespace GlobalTheory.SplitStab

open scoped Matrix TensorProduct
open GlobalTheory.AutFunCompare (colSpan exists_colSpan mem_extSub_colSpan)

theorem inConjParabolic_parab (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (W : Submodule D.host.E V.V) :
    InConjParabolic ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) W).map
        (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) (Module.finrank D.host.E W) := by
  obtain ⟨r', C, hC, rfl⟩ := exists_colSpan V W
  have hfin : Module.finrank D.host.E (colSpan V C) = r' := by
    have hli : LinearIndependent D.host.E fun k => GlobalTheory.AutFunCompare.vecOf V (Cᵀ k) :=
      hC.map' (V.frame.equivFun.symm.toLinearMap) (LinearEquiv.ker _)
    rw [colSpan, finrank_span_eq_card hli]
    simp
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective C.mulVecLin
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 hC))
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r') (Fin V.rank) D.host.E, L * C = 1 :=
    ⟨LinearMap.toMatrix' l, by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]; exact hl⟩
  set τ := s.emb
  let U : Submodule (Fv D.host.F v) (Fin V.rank → Fv D.host.F v) := LinearMap.range (C.map τ).mulVecLin
  have hinj : Function.Injective (C.map τ).mulVecLin := fun c d e => by
    have h1 : (L.map τ * C.map τ) *ᵥ c = (L.map τ * C.map τ) *ᵥ d := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; exact congrArg _ e
    have hm : (L * C).map τ = L.map τ * C.map τ := Matrix.map_mul (f := (τ : D.host.E →+* Fv D.host.F v))
    rwa [← hm, hL, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.one_mulVec, Matrix.one_mulVec] at h1
  have hU : Module.finrank (Fv D.host.F v) U = r' := by
    rw [LinearMap.finrank_range_of_inj hinj]; simp
  have hmaps : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) (colSpan V C), ∀ u ∈ U,
      ((splitHom D.sp.cm.sig V.gram τ x : GL (Fin V.rank) (Fv D.host.F v)) : Matrix _ _ _) *ᵥ u ∈ U := by
    rintro x hx _ ⟨c, rfl⟩
    let y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E :=
      (C.map (inclR (Fv D.host.F v))) *ᵥ fun k => algebraMap (Fv D.host.F v) _ (c k)
    have hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub V (Fv D.host.F v) (colSpan V C) :=
      (mem_extSub_colSpan V _ C y).2 ⟨_, rfl⟩
    obtain ⟨a', ha'⟩ := (mem_extSub_colSpan V _ C _).1 (GlobalTheory.Cusp.mem_parab_iff_maps.1 hx y hy)
    have e1 : splitVec τ y = (C.map τ) *ᵥ c := by
      rw [splitVec_map_inclR_mulVec]
      congr 1
      funext k
      exact (splitProj τ).commutes (c k)
    have e2 := splitVec_matHom_mulVec τ x y
    change splitVec τ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act D.sp.cm V x y) = _ at e2
    rw [ha', splitVec_map_inclR_mulVec, e1] at e2
    exact ⟨fun k => splitProj τ (a' k), e2⟩
  obtain ⟨g, hg⟩ := inConjParabolic_of_maps
    ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) (colSpan V C)).map (splitHom D.sp.cm.sig V.gram τ)) U
    (by
      rintro _ ⟨x, hx, rfl⟩ u hu
      exact hmaps x hx u hu)
  have hdim : Module.finrank D.host.E (colSpan V C) = Module.finrank (Fv D.host.F v) U := hfin.trans hU.symm
  rw [hdim]
  refine ⟨s.basis⁻¹ * g, fun p hp => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
  have := hg _ ⟨x, hx, rfl⟩
  convert this using 1
  change (s.basis⁻¹ * g)⁻¹ * splitEquivIn s.cm s.herm s.emb s.basis x * (s.basis⁻¹ * g) = _
  rw [splitEquivIn_apply]
  change _ = g⁻¹ * splitHom D.sp.cm.sig V.gram s.emb x * g
  group

end GlobalTheory.SplitStab

namespace GlobalTheory.SplitStab

theorem splitStab : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (W : Submodule D.host.E V.V), GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W →
    InConjParabolic ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) W).map
        (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) (Module.finrank D.host.E W) ∧
      InConjParabolic ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) W).map
        (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) (V.rank - Module.finrank D.host.E W) := by
  intro D V v s W _
  refine ⟨inConjParabolic_parab D V v s W, ?_⟩
  have h := inConjParabolic_parab D V v s (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W)
  have hr : Module.finrank D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) = V.rank - Module.finrank D.host.E W := by
    have := GlobalTheory.Cusp.WittIdx.finrank_add_finrank_perp W
    omega
  rw [hr] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun p hp => hg p (Subgroup.map_mono GlobalTheory.Cusp.parab_le_perp hp)⟩

end GlobalTheory.SplitStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftDat

open GlobalTheory.LiftLevel

variable {D : D7}

def rowAdj (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (v : Fin T.rank → D.host.E) :
    Matrix (Fin 1) (Fin T.rank) (EAf D) :=
  toEAf D a • HMul.hMul ((Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] v k) * incA D (T.gram k l)).map (toEAf D)) βT.val

def rowRed (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E)
    (v : Fin T.rank → D.host.E) : Fin T.rank → Formalism.L2.DIV.kP PP :=
  fun j => redM PP (rowAdj T βT a e v) 0 j

theorem liftI_le {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ Pg ∪ Q) :
    liftI Pg Q ≤ conjI PP.asIdeal :=
  Ideal.prod_le_inf.trans (Finset.inf_le h)

def toConj (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (h : PP ∈ Pg ∪ Q) :
    𝓞 D.host.E ⧸ liftI Pg Q →+* 𝓞 D.host.E ⧸ conjI PP.asIdeal :=
  Ideal.quotientMap (conjI PP.asIdeal) (RingHom.id _) (fun _ hx => liftI_le h hx)

def conjRes (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (h : PP ∈ Pg ∪ Q) :
    𝓞 D.host.E ⧸ liftI Pg Q →+* Formalism.L2.DIV.kP PP :=
  Ideal.quotientMap PP.asIdeal GlobalTheory.SW.Lev.bar (fun _ hx => GlobalTheory.SW.Lev.mem_conjI.1 (liftI_le h hx))

def Jgrp (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ) : Subgroup (GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q)) :=
  ⨅ PP : Pg, (Matrix.GeneralLinearGroup.map (toConj Pg Q PP.1 (Finset.mem_union_left _ PP.2))).ker

def lamHom (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) : Jgrp Pg Q r →* ℂˣ :=
  (∏ PP ∈ Q.attach, (ξ PP.1).comp ((Units.map (conjRes Pg Q PP.1 (Finset.mem_union_right _ PP.2)).toMonoidHom).comp
    (Matrix.GeneralLinearGroup.det.comp (Jgrp Pg Q r).subtype)))⁻¹

theorem mem_Jgrp {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ} {κ : GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q)} :
    κ ∈ Jgrp Pg Q r ↔ ∀ PP (h : PP ∈ Pg),
      Matrix.GeneralLinearGroup.map (toConj Pg Q PP (Finset.mem_union_left _ h)) κ = 1 := by
  simp [Jgrp, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem lamHom_apply {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ}
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (κ : Jgrp Pg Q r) :
    lamHom Pg Q r ξ κ = (∏ PP ∈ Q.attach, ξ PP.1 (Units.map (conjRes Pg Q PP.1
      (Finset.mem_union_right _ PP.2)).toMonoidHom (Matrix.GeneralLinearGroup.det (κ : GL (Fin r) _))))⁻¹ := by
  simp [lamHom]

def mkLevel {S T : HSp D} (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : liftI Pg Q ≠ ⊤) (h2 : liftI Pg Q ≠ ⊥)
    (h3 : IsCoprime (liftI Pg Q) (conjI (liftI Pg Q))) (h4 : IsCoprime (liftI Pg Q) (Ideal.span {2}))
    (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ)
    (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ liftI Pg Q • C.X.Λ)
    (Lv0 : GlobalTheory.SW.Level C.X) : GlobalTheory.SW.Level C.X where
  𝔪 := liftI Pg Q
  proper := h1
  ne_bot := h2
  cop := h3
  odd := h4
  β := β
  β_mem := hβ
  β_span := hsp
  J := Jgrp Pg Q T.rank
  lam := lamHom Pg Q T.rank ξ
  w := Lv0.w
  w_int := Lv0.w_int
  w_tr := Lv0.w_tr

end GlobalTheory.LiftDat

end
end

