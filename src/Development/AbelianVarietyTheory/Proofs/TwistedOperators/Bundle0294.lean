module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzUnitaryIntertwinerScalar
section
open scoped Matrix

noncomputable section

open MeasureTheory Complex
open scoped Real RealInnerProductSpace ComplexConjugate FourierTransform SchwartzMap

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

def modPt (q : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim 0 fun i => q i

def trPt (p : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim (fun i => p i) 0

theorem pPart_modPt (q : EuclideanSpace ℝ l) : pPart (modPt q) = 0 := by
  ext i; simp [pPart, modPt]

theorem qPart_modPt (q : EuclideanSpace ℝ l) : qPart (modPt q) = q := by
  ext i; simp [qPart, modPt]

theorem pPart_trPt (p : EuclideanSpace ℝ l) : pPart (trPt p) = p := by
  ext i; simp [pPart, trPt]

theorem qPart_trPt (p : EuclideanSpace ℝ l) : qPart (trPt p) = 0 := by
  ext i; simp [qPart, trPt]

theorem rhoFun_modPt (q : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (modPt q) f x = cexp (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * I) * f x := by
  simp [rhoFun, phase, pPart_modPt, qPart_modPt]

theorem rhoFun_trPt (p : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (trPt p) f x = f (x + p) := by
  simp [rhoFun, phase, pPart_trPt, qPart_trPt]

def modS (q : EuclideanSpace ℝ l) (g : Sch l) : Sch l :=
  SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫) g

theorem coe_modS (q : EuclideanSpace ℝ l) (g : Sch l) : ⇑(modS q g) = rhoFun (modPt q) ⇑g := by
  have ht : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫ :=
    GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (innerSL ℝ q).hasTemperateGrowth
  funext x
  rw [modS, SchwartzMap.smulLeftCLM_apply_apply ht, GlobalTheory.Published.Metaplectic.eChar_apply, rhoFun_modPt, smul_eq_mul]
  congr 2
  push_cast
  ring

def trS (p : EuclideanSpace ℝ l) (g : Sch l) : Sch l := SchwartzMap.compSubConstCLM ℂ (-p) g

theorem coe_trS (p : EuclideanSpace ℝ l) (g : Sch l) : ⇑(trS p g) = rhoFun (trPt p) ⇑g := by
  funext x
  rw [trS, SchwartzMap.compSubConstCLM_apply, rhoFun_trPt, sub_neg_eq_add]

theorem integrable_conj_mul (a b : Sch l) : Integrable (fun x => conj (a x) * b x) := by
  refine b.integrable.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 a)
    (Complex.continuous_conj.comp a.continuous).aestronglyMeasurable (.of_forall fun x => ?_)
  rw [Complex.norm_conj]
  exact SchwartzMap.norm_le_seminorm ℝ a x

theorem integral_conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) :
    ∫ x, conj (U f x) * U g x = ∫ x, conj (f x) * g x := by
  have hn : ∀ h : Sch l, ‖(U h).toLp 2‖ = ‖h.toLp 2‖ := fun h => by
    rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) (U h).continuous.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) h.continuous.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hU]
  have hlin : ∀ (b : ℂ) (u v : Sch l), u.toLp 2 volume + b • v.toLp 2 volume = (u + b • v).toLp 2 volume := fun b u v => by
    have := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_add u (b • v)
    rw [(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_smul] at this
    exact this.symm
  have key : ∀ b : ℂ, ‖(U f).toLp 2 volume + b • (U g).toLp 2 volume‖ = ‖f.toLp 2 volume + b • g.toLp 2 volume‖ := fun b => by
    rw [hlin, hlin, ← map_smul, ← map_add (f := _), hn]
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key (-(RCLike.I : ℂ))
  have k4 := key (RCLike.I : ℂ)
  simp only [one_smul, neg_one_smul, neg_smul, ← sub_eq_add_neg] at k1 k2 k3 k4
  have e1 := SchwartzMap.inner_toL2_toL2_eq (U f) (U g) volume
  have e2 := SchwartzMap.inner_toL2_toL2_eq f g volume
  simp only [RCLike.inner_apply] at e1 e2
  simp only [mul_comm (starRingEnd ℂ _)]
  rw [← e1, ← e2, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, k1, k2, k3, k4]

end GlobalTheory.RealWeil.SchurSchwartz

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

theorem conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hc : ∀ (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h → ⇑(U h₁) = rhoFun w ⇑(U h))
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) (x : EuclideanSpace ℝ l) :
    conj (U f x) * U g x = conj (f x) * g x := by
  set D : EuclideanSpace ℝ l → ℂ := fun y => conj (U f y) * U g y - conj (f y) * g y with hD
  have hDi : Integrable D := (integrable_conj_mul (U f) (U g)).sub (integrable_conj_mul f g)
  have hDc : Continuous D :=
    ((Complex.continuous_conj.comp (U f).continuous).mul (U g).continuous).sub
      ((Complex.continuous_conj.comp f.continuous).mul g.continuous)
  have hF : 𝓕 D = 0 := by
    funext w
    rw [Real.fourier_eq', Pi.zero_apply]
    have h1 := hc (modPt (-w)) g (modS (-w) g) (coe_modS _ _)
    have h2 := integral_conj_mul_eq U hU f (modS (-w) g)
    rw [← sub_eq_zero, ← integral_sub (integrable_conj_mul _ _) (integrable_conj_mul _ _)] at h2
    rw [← h2]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [h1, coe_modS, rhoFun_modPt, hD, smul_eq_mul]
    rw [inner_neg_left, real_inner_comm]
    push_cast
    ring_nf
  have hinv := hDc.fourierInv_fourier_eq hDi (by rw [hF]; exact integrable_zero _ _ _)
  have hz : 𝓕⁻ (0 : EuclideanSpace ℝ l → ℂ) = 0 := by
    first
      | exact FourierTransform.fourierInv_zero
      | (funext w; simp [Real.fourierInv_eq])
  rw [hF, hz] at hinv
  have hx := congrFun hinv x
  simp only [hD, Pi.zero_apply] at hx
  exact sub_eq_zero.1 hx.symm

end GlobalTheory.RealWeil.SchurSchwartz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleSplitLabMemSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanPoly

open Polynomial

theorem coeff_heckePolyOf_le (n q : ℕ) (a : ℕ → ℂ) {i : ℕ} (hi : i ≤ n) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff i = (-1) ^ i * (q : ℂ) ^ (i * (i - 1) / 2) * a i := by
  unfold Formalism.L2.Col.heckePolyOf
  rw [finsetSum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b _ hb
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem heckePolyOf_eq_zero (n q : ℕ) (a : ℕ → ℂ) (h : ∀ k ≤ n, a k = 0) :
    Formalism.L2.Col.heckePolyOf n q a = 0 := by
  unfold Formalism.L2.Col.heckePolyOf
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [h k (by simpa [Nat.lt_succ_iff] using hk)]
  simp

theorem single_mem_span (nX nY q : ℕ) (hq : q ≠ 0) (c : ℂ) (hc : c ≠ 0) (B : Polynomial ℂ) (hB : B ≠ 0)
    (z : ℕ → ℕ → ℂ)
    (h : ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nX q (fun k => ∑ j ∈ Finset.range (nY + 1), z k j * a j) =
      (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) * B)
    (j : Fin (nY + 1)) :
    Pi.single j (1 : ℂ) ∈ Submodule.span ℂ (Set.range fun k : Fin (nX + 1) => fun i : Fin (nY + 1) => z k i) := by
  by_contra hj
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hj inferInstance
  set a : ℕ → ℂ := fun i => if hi : i < nY + 1 then f (Pi.single ⟨i, hi⟩ 1) else 0 with ha
  have hfv : ∀ k : ℕ, f (fun i : Fin (nY + 1) => z k i) = ∑ i ∈ Finset.range (nY + 1), z k i * a i := by
    intro k
    rw [← Fin.sum_univ_eq_sum_range (fun i => z k i * a i)]
    conv_lhs => rw [show (fun i : Fin (nY + 1) => z k i) = ∑ i : Fin (nY + 1), z k i • Pi.single i (1 : ℂ) by
      ext m; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := Fin.is_le i
    simp [ha, hi]
  have hzero : ∀ k ≤ nX, ∑ i ∈ Finset.range (nY + 1), z k i * a i = 0 := by
    intro k hk
    rw [← hfv k]
    have hm : f (fun i : Fin (nY + 1) => z k i) ∈ Submodule.map f (Submodule.span ℂ (Set.range fun k : Fin (nX + 1) => fun i : Fin (nY + 1) => z k i)) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩)
    rw [hmap] at hm
    simpa using hm
  have h0 := h a
  rw [heckePolyOf_eq_zero _ _ _ hzero] at h0
  have hcomp : (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) = 0 := by
    rcases mul_eq_zero.1 h0.symm with h1 | h1
    · exact h1
    · exact absurd h1 hB
  have hco := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p j) hcomp
  simp only [comp_C_mul_X_coeff, coeff_zero] at hco
  rw [coeff_heckePolyOf_le _ _ _ (Nat.lt_succ_iff.1 j.isLt)] at hco
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have haj : a j = 0 := by
    simpa [hc, hqc] using hco
  apply hf
  have hjle := Fin.is_le j
  simpa [ha, hjle] using haj

end GlobalTheory.SpanPoly

namespace GlobalTheory.SpanPoly

theorem single_splitLab_mem_span : ∀ (nX nY q : ℕ), q ≠ 0 → ∀ (c : ℂ), c ≠ 0 → ∀ (B : Polynomial ℂ), B ≠ 0 → ∀ (z : ℕ → ℕ → ℂ), (∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nX q (fun k => ∑ j ∈ Finset.range (nY + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) * B) → ∀ j ≤ nY, Finsupp.single (splitLab nY j) (1 : ℂ) ∈ Submodule.span ℂ ((fun k => GlobalTheory.Hk3.splitC nY (z k)) '' Set.Iic nX) := by
  intro nX nY q hq c hc B hB z h j hj
  let φ : (Fin (nY + 1) → ℂ) →ₗ[ℂ] (List ℤ →₀ ℂ) :=
    ∑ i : Fin (nY + 1), (Finsupp.lsingle (splitLab nY i)).comp (LinearMap.proj i)
  have hφz : ∀ k, φ (fun i : Fin (nY + 1) => z k i) = GlobalTheory.Hk3.splitC nY (z k) := by
    intro k
    unfold GlobalTheory.Hk3.splitC
    rw [← Fin.sum_univ_eq_sum_range (fun i => Finsupp.single (splitLab nY i) (z k i))]
    simp [φ]
  have hφe : φ (Pi.single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nY + 1)) 1) = Finsupp.single (splitLab nY j) (1 : ℂ) := by
    simp only [φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Finsupp.lsingle_apply]
    rw [Finset.sum_eq_single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nY + 1))]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  rw [← hφe]
  have hm := Submodule.mem_map_of_mem (f := φ) (single_mem_span nX nY q hq c hc B hB z h ⟨j, Nat.lt_succ_of_le hj⟩)
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact ⟨k, Set.mem_Iic.2 (Nat.lt_succ_iff.1 k.isLt), (hφz k).symm⟩

end GlobalTheory.SpanPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevSeminormWeilThetaPolynomialInHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
noncomputable section

open GlobalTheory.KernelSeminorm GlobalTheory.Size GlobalTheory.FockCompare GlobalTheory.ThetaGrowth
open scoped NNReal

namespace GlobalTheory.WeilSobolev

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem sobO_om_le (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (g : GA D S) (h : GA D T) {ρ : ℝ≥0}
    (hρ : ∀ a, ‖mov θ g⁻¹ h⁻¹ (letter a)‖ ≤ ρ) (d : ℕ) :
    ∀ f, IsThetaFunO ψ S T f → sobO ψ θ μ 𝓕 d (om (g, h) f) ≤
      ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d * sobO ψ θ μ 𝓕 d f := by
  induction d with
  | zero =>
    intro f hf
    rw [sobO_zero, sobO_zero, l2O_om_apply_eq_of_isThetaFunO hom hμ h𝓕 hf, pow_zero, one_mul]
  | succ d ih =>
    intro f hf
    have e1 : sobO ψ θ μ 𝓕 (d + 1) (om (g, h) f) =
        l2O μ 𝓕 (om (g, h) f) + ∑ a, sobO ψ θ μ 𝓕 d (heisDer ψ θ a (om (g, h) f)) :=
      Translate.wordSum_succ _ _ d _
    have e2 : ∀ a, sobO ψ θ μ 𝓕 d (heisDer ψ θ a (om (g, h) f)) ≤
        ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
          (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d *
        (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (d + 1) f) := by
      intro a
      rw [← dv_letter hc hom.std a, dv_om hom hc g h (letter a) hf]
      refine (ih _ (theta_dv hc hom.std _ hf)).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      exact sobO_dvL_le hc hom.std d (hρ a) ⟨f, hf⟩
    have e3 : l2O μ 𝓕 (om (g, h) f) ≤ sobO ψ θ μ 𝓕 (d + 1) f := by
      rw [l2O_om_apply_eq_of_isThetaFunO hom hμ h𝓕 hf]
      exact (sobO_zero (ψ := ψ) (θ := θ)).ge.trans (sobO_mono (Nat.zero_le _))
    rw [e1]
    refine (add_le_add e3 (Finset.sum_le_sum fun a _ => e2 a)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h1 : (1 : ℝ≥0∞) ≤ ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d :=
      one_le_pow₀ (ENNReal.one_le_coe_iff.2 le_self_add)
    rw [pow_succ]
    generalize sobO ψ θ μ 𝓕 (d + 1) f = s at *
    generalize ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d = q at *
    calc s + (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) : ℝ≥0∞) *
          (q * (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * s))
        ≤ q * s + (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) : ℝ≥0∞) *
          (q * (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * s)) :=
          add_le_add (le_mul_of_one_le_left' h1) le_rfl
      _ = _ := by push_cast; ring

theorem sobO_weil_le_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕) (k : ℕ),
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ y ∈ C₁, ∀ h : GA D X,
      (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k (ω (y, h) Φ)).toReal ≤
        C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ C₁ hC₁ μ 𝓕 hμ k
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ : IsStdChar D ψ (-1) := hω.std
  obtain ⟨B, hB⟩ := (hC₁.image (continuous_ofSgn_symm ε M)).exists_bound_of_continuousOn
    (GlobalTheory.RatCount.continuous_normInf hθ (sgn ε M)).continuousOn
  obtain ⟨CT, hCT⟩ := (GlobalTheory.SmoothForms.normInf_mul_le_and_le_height D θ X).2
  obtain ⟨L, hL, hL0⟩ : ∃ L : ℝ, (∀ a, ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖ ≤ L) ∧ 0 ≤ L :=
    ⟨∑ a, ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖,
      fun a => Finset.single_le_sum (f := fun a => ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a), by positivity⟩
  obtain ⟨c0, hc0, hc0'⟩ : ∃ c0 : ℝ, c0 = |CT| * L * |B| ∧ 0 ≤ c0 := ⟨_, rfl, by positivity⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, K = (Fintype.card (D.what₂.Tau × Fin X.rank × Fin (sgn ε M).rank × Bool) : ℝ≥0) :=
    ⟨_, rfl⟩
  refine ⟨k, (1 + (K : ℝ) * K * c0) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal,
    by positivity, fun y hy h => ?_⟩
  have hy' : (ofSgn ε M).symm y ∈ (ofSgn ε M).symm '' C₁ := ⟨y, hy, rfl⟩
  have eω : ω (y, h) Φ = (ω.toSgn ε) ((ofSgn ε M).symm y, h) Φ := by
    simp [WRep.toSgn]
  have hH : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ X h
  obtain ⟨H, hH'⟩ : ∃ H : ℝ, H = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := ⟨_, rfl⟩
  rw [← hH'] at hH ⊢
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = c0 * H := ⟨⟨c0 * H, by positivity⟩, rfl⟩
  have hρ : ∀ a, ‖mov θ ((ofSgn ε M).symm y)⁻¹ h⁻¹ (letter a)‖ ≤ ρ := by
    intro a
    refine (norm_mov_le_normInf _ _ _).trans ?_
    rw [inv_inv, GlobalTheory.RatCount.normInf_inv]
    have h1 : normInf θ X h ≤ |CT| * H := (hCT h).trans (by rw [← hH']; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have h2 : normInf θ (sgn ε M) ((ofSgn ε M).symm y) ≤ |B| :=
      (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB _ hy').trans (le_abs_self _))
    have h3 := GlobalTheory.RatCount.normInf_nonneg θ X h
    have h4 := GlobalTheory.RatCount.normInf_nonneg θ (sgn ε M) ((ofSgn ε M).symm y)
    rw [hρdef]
    calc normInf θ X h * ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖ * normInf θ (sgn ε M) ((ofSgn ε M).symm y)
        ≤ (|CT| * H) * L * |B| := by gcongr; exact hL a
      _ = c0 * H := by rw [hc0]; ring
  have key := GlobalTheory.WeilSobolev.sobO_om_le hω hc hμ.1 hμ.2.1 ((ofSgn ε M).symm y) h hρ k Φ hΦ
  rw [eω]
  have hs := sobO_ne_top hψ hθ hμ.1 hμ.2.1 hΦ k
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hs) key).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ← hK]
  have hQ : ((1 + K * (K * ρ) : ℝ≥0) : ℝ) ≤ (1 + (K : ℝ) * K * c0) * H := by
    push_cast
    rw [hρdef]
    have : (0 : ℝ) ≤ K := K.2
    nlinarith [mul_nonneg (mul_nonneg this this) hc0']
  calc _ ≤ ((1 + (K : ℝ) * K * c0) * H) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (NNReal.coe_nonneg _) hQ k) ENNReal.toReal_nonneg
    _ = (1 + (K : ℝ) * K * c0) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal * H ^ k := by
        rw [mul_pow]; ring

end GlobalTheory.WeilSobolev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoSlopeMetaplecticLiftSchwartz
section
open scoped Matrix

namespace GlobalTheory.RealWeil

theorem tendsto_slope_omS_schwartz :
    ∀ (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] (pr : G →* Matrix.symplecticGroup l ℝ)
    (om : G →* (GlobalTheory.RealWeil.L2 l ≃ₗᵢ[ℂ] GlobalTheory.RealWeil.L2 l)) (omS : G →* (GlobalTheory.RealWeil.Sch l →L[ℂ] GlobalTheory.RealWeil.Sch l)),
    (∀ (g : G) (w : l ⊕ l → ℝ) (f : GlobalTheory.RealWeil.L2 l),
      om g (GlobalTheory.RealWeil.rho w f) = GlobalTheory.RealWeil.rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) →
    (∀ (g : G) (f : GlobalTheory.RealWeil.Sch l), om g (f.toLp 2) = (omS g f).toLp 2) →
    ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ γ : ℝ → G, γ 0 = 1 →
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) →
    (∀ f : GlobalTheory.RealWeil.Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((GlobalTheory.RealWeil.quad X f).toLp 2) 0) →
    ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (omS (γ t) f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (GlobalTheory.RealWeil.quad X f)) := by
  intro l _ _ G _ pr om omS h3 h4 X hX γ h0 hγ h6 f
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨A, hA, hb⟩ := exists_seminorm_le (l := l) k n
  have key : ∀ r, Filter.Tendsto
      (fun t : ℝ => ‖schwartzToL2 l (A r (t⁻¹ • (omS (γ t) f - f) - quad X f))‖) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    intro r
    have h := hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_toLp_omS h3 h4 hX h0 hγ h6 (hA r) f)
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    refine h.congr fun t => ?_
    have e : ∀ (B : Sch l →L[ℂ] L2 l) (u v w : Sch l) (s : ℝ), B (s • (u - v) - w) = s • (B u - B v) - B w := by
      intro B u v w s
      rw [B.map_sub, B.map_smul_of_tower, B.map_sub]
    have e1 : omS (γ 0) f = f := by rw [h0, omS.map_one]; rfl
    rw [zero_add, e1]
    exact congrArg norm (e ((schwartzToL2 l).comp (A r)) _ _ _ _).symm
  have hs := tendsto_finsetSum Finset.univ fun r _ => key r
  rw [Finset.sum_const_zero] at hs
  filter_upwards [hs.eventually (gt_mem_nhds hε)] with t ht
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  exact (hb _).trans_lt ht

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointPreservesHeckeEigenvectorsMatche
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Hk3


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Hk3.SysE.matched_keeps_eigen : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (cX c0 : List ℤ →₀ ℂ), GlobalTheory.Hk3.MatchE R t P cX c0 → ∀ (x : R.HE.H) (l : ℂ), h P c0 x = l • x → h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh hhn P hg cX c0 hM x l hx
  have injE : Function.Injective R.HE.e := hC.models.HE.1
  have hX01 := (GlobalTheory.DefiniteOps.definite_ops R F hC.lev hC.fam hC.models).1 t
  rcases hX01 with ⟨hX, hXo, hXn⟩
  have comm : ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y) := by
    intro y
    apply injE
    exact (hM y (hX P cX y) (hXo P hg cX y)).trans (hh P hg c0 (R.Th t y)).symm
  have eX : LinearMap.adjoint (hX P cX) = hX P (dualC (Finsupp.mapRange star (star_zero ℂ) cX)) := hXn.2 P hg cX
  have cX' : Commute (hX P cX) (hX P (dualC (Finsupp.mapRange star (star_zero ℂ) cX))) := hXn.1 P P hg hg _ _
  have nX : Commute (hX P cX) (LinearMap.adjoint (hX P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute (hX P cX) B) _ _ eX.symm cX'
  have eE : LinearMap.adjoint (h P c0) = h P (dualC (Finsupp.mapRange star (star_zero ℂ) c0)) := hhn.2 P hg c0
  have cE : Commute (h P c0) (h P (dualC (Finsupp.mapRange star (star_zero ℂ) c0))) := hhn.1 P P hg hg _ _
  have nE : Commute (h P c0) (LinearMap.adjoint (h P c0)) :=
    @Eq.subst (Module.End ℂ R.HE.H) (fun B => Commute (h P c0) B) _ _ eE.symm cE
  have up : hX P cX (LinearMap.adjoint (R.Th t) x) = l • LinearMap.adjoint (R.Th t) x :=
    _root_.GlobalTheory.HkUp.eigen_up_along_adjoint (R.Th t) (fun _ : Unit => hX P cX) (fun _ : Unit => h P c0)
      (fun _ u => comm u) (fun _ => nX) (fun _ => nE) () l x hx
  have c1 := comm (LinearMap.adjoint (R.Th t) x)
  have c2 : R.Th t (hX P cX (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
    exact (congrArg (R.Th t) up).trans ((R.Th t).map_smul l _)
  exact c1.symm.trans c2
end

