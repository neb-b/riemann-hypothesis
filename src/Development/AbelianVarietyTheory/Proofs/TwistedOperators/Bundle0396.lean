module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCuspSectionsOfDominatedRationalIsometries
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.HeckeEx.Dom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem nfac_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a) {la : Wt X.Ψ r}
    {la' : Wt X'.Ψ r} (hl : ∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) (x : Frame X.Ψ r) :
    X'.nfac la' (lact a (castFr h.psi x)) = X.nfac la x := by
  unfold Data.nfac
  simp only [h.dmin_eq]
  exact (GlobalTheory.Dict.Pull.cast_wt h.psi rfl hl (castFr h.psi x)).symm

open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs in
theorem lact_flow_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a)
    (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    lact a (castFr h.psi (X.flow ξ s x)) =
      X'.flow ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => s ⟨τ.1, h.mem τ⟩) (lact a (castFr h.psi x)) := by
  funext τ
  have hm : (a : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) =
      X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
        (a : Matrix (Fin r) (Fin r) E).map τ.1 := by
    have he : Data.emb τ.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) =
        (a : Matrix (Fin r) (Fin r) E).map τ.1 *ᵥ Data.emb τ.1 ξ := by
      funext i
      simp [Data.emb, Matrix.mulVec, dotProduct]
    have hc : X'.c τ = X.c ⟨τ.1, h.mem τ⟩ := by simp only [Data.c, h.xi]
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flowMat_mulVec, flowMat_mulVec, he, h.hermC_eq, hc,
      Matrix.mulVec_add, Matrix.mulVec_smul]
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) *
      mat x ⟨τ.1, h.mem τ⟩) = X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hm]

theorem flowMat_nsmul (X : Data E r) (n : ℕ) (v : Fin r → E) (τ : X.Ψ) (z : ℂ) :
    X.flowMat ((n : E) • v) τ z = X.flowMat v τ ((n : ℂ) ^ 2 * z) := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast,
    Complex.conj_natCast, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem flow_nsmul (X : Data E r) {n : ℕ} (hn : 0 < n) (v : Fin r → E) (t : ℝ) (x : Frame X.Ψ r) :
    X.flow ((n : E) • v) (fun _ => Complex.I * ((t / (n : ℝ) ^ 2 : ℝ) : ℂ)) x =
      X.flow v (fun _ => Complex.I * (t : ℂ)) x := by
  funext τ
  simp only [Data.flow, flowMat_nsmul]
  congr 2
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  push_cast
  field_simp

theorem lact_mul_q {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact (a * b) x = lact a (lact b x) := by
  funext τ
  simp only [lact, mat, Units.val_mul, Matrix.map_mul, Matrix.of_apply]
  rw [Matrix.mul_assoc]
  rfl

theorem norm_chi (X : Data E r) (la : Wt X.Ψ r) {g : GL (Fin r) E} (hg : g ∈ X.Γ) : ‖X.χ la g‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have := congrArg norm (h g hg)
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

end GlobalTheory.HeckeEx.Dom


open GlobalTheory.HeckeEx.Dom in
theorem GlobalTheory.HeckeEx.mem_SS_of_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (I₀ : Type) [Finite I₀] (X' : I₀ → Data E r) (la : Wt X.Ψ r) (la' : ∀ j, Wt (X' j).Ψ r) (P : Frame X.Ψ r → ℂ) (Q : ∀ j, Frame (X' j).Ψ r → ℂ) (N : ℕ) (M : ℝ), 0 < N → 0 ≤ M → X.IsSec la P → (∀ j, Q j ∈ (X' j).SS (la' j)) → (∀ j a (h : QMatch X (X' j) N a) τ m, la' j τ m = la ⟨τ.1, h.mem τ⟩ m) → (∀ x ∈ X.dom, ∀ B : ℝ, 0 ≤ B → (∀ j a (h : QMatch X (X' j) N a), ‖Q j (lact a (castFr h.psi x))‖ ≤ B) → ‖P x‖ ≤ M * B) → P ∈ X.SS la := by
  intro E _ _ _ r X I₀ _ X' la la' P Q N M hN hM hP hQ hl hdom
  classical
  haveI : Fintype I₀ := Fintype.ofFinite I₀

  choose C hC using fun j => (hQ j).1.2
  have hbd : ∀ x ∈ X.dom, X.pnorm la P x ≤ M * ∑ j, |C j| := fun x hx => by
    have hn := BoundedSectionAlgebra.nfac_pos X hx la
    have h1 := hdom x hx ((∑ j, |C j|) / X.nfac la x)
      (div_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) hn.le) fun j a h => by
        rw [le_div_iff₀ hn]
        have := hC j _ (h.mem_dom hx)
        rw [BoundedSectionAlgebra.pnorm_eq, nfac_q h (hl j a h)] at this
        exact this.trans ((le_abs_self _).trans
          (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))
    rw [BoundedSectionAlgebra.pnorm_eq]
    calc ‖P x‖ * X.nfac la x ≤ M * ((∑ j, |C j|) / X.nfac la x) * X.nfac la x :=
          mul_le_mul_of_nonneg_right h1 hn.le
      _ = M * ∑ j, |C j| := by field_simp
  have hB : X.IsBddSec la P := ⟨hP, _, hbd⟩
  refine ⟨hB, fun ξ hξ x hx => ?_⟩

  choose S hS hS' using fun j => GlobalTheory.T.finite_classes_rational_isometries_bounded_denominator E r X (X' j) N hN
  obtain ⟨hmem, hlim⟩ := _root_.GlobalTheory.HeckeEx.bddSec_tendsto_constTerm E r X la P hB ξ hξ x hx
  let xt : ℝ → Frame X.Ψ r := fun t => X.flow ξ (fun _ => Complex.I * (t : ℂ)) x
  let Bt : ℝ → ℝ := fun t => ∑ j, ∑ s ∈ (S j).attach,
    ‖Q j (lact s.1 (castFr (hS j s.1 s.2).psi (xt t)))‖
  have hdomt : ∀ t : ℝ, 0 ≤ t → ‖P (xt t)‖ ≤ M * Bt t := fun t ht => by
    refine hdom _ (hmem t ht) _ (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ => norm_nonneg _)
      fun j a h => ?_
    obtain ⟨s, hs, b, hb, rfl⟩ := hS' j a h
    have hy := (hS j s hs).mem_dom (hmem t ht)
    have e1 : ‖Q j (lact (b * s) (castFr h.psi (xt t)))‖ = ‖Q j (lact s (castFr (hS j s hs).psi (xt t)))‖ := by
      rw [lact_mul_q, (hQ j).1.1.2.2 b hb _ hy, norm_mul, norm_chi _ _ hb, _root_.one_mul]
    rw [e1]
    have e2 : ‖Q j (lact s (castFr (hS j s hs).psi (xt t)))‖ ≤
        ∑ s' ∈ (S j).attach, ‖Q j (lact s'.1 (castFr (hS j s'.1 s'.2).psi (xt t)))‖ :=
      Finset.single_le_sum (f := fun s' : (S j) => ‖Q j (lact s'.1 (castFr (hS j s'.1 s'.2).psi (xt t)))‖)
        (a := ⟨s, hs⟩) (fun _ _ => norm_nonneg _) (Finset.mem_attach _ _)
    exact e2.trans (Finset.single_le_sum (f := fun j => ∑ s' ∈ (S j).attach,
      ‖Q j (lact s'.1 (castFr (hS j s'.1 s'.2).psi (xt t)))‖)
      (a := j) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j))
  have hBt : Filter.Tendsto Bt Filter.atTop (nhds 0) := by
    have : (0 : ℝ) = ∑ j : I₀, ∑ s ∈ (S j).attach, (0 : ℝ) := by simp
    rw [this]
    refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun s _ => ?_
    have h := hS j s.1 s.2
    let v : Fin r → E := (N : E) • ((s.1 : Matrix (Fin r) (Fin r) E) *ᵥ ξ)
    have hv : (X' j).IsIso v := by
      refine ⟨h.lat ξ hξ.1, ?_, ?_⟩
      · have e : herm (X' j).Gm v v = ((N : E) * cc (N : E)) *
            herm (X' j).Gm ((s.1 : Matrix (Fin r) (Fin r) E) *ᵥ ξ) ((s.1 : Matrix (Fin r) (Fin r) E) *ᵥ ξ) := by
          simp only [v, herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          simp only [cc, map_mul]
          ring
        rw [e, h.iso, hξ.2.1, MulZeroClass.mul_zero]
      · intro e
        have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
        have hv0 := (smul_eq_zero.1 e).resolve_left hN0
        apply hξ.2.2
        rw [← GlobalTheory.Dict.Pull.inv_mulVec s.1 ξ, hv0, Matrix.mulVec_zero]
    have hy := h.mem_dom hx
    obtain ⟨-, hl'⟩ := _root_.GlobalTheory.HeckeEx.bddSec_tendsto_constTerm E r (X' j) (la' j) (Q j) (hQ j).1 v hv _ hy
    rw [(hQ j).2 v hv _ hy] at hl'
    have hdiv : Filter.Tendsto (fun t : ℝ => t / (N : ℝ) ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_div_const (by positivity)
    have key := (hl'.comp hdiv).norm
    rw [norm_zero] at key
    refine key.congr fun t => ?_
    simp only [Function.comp_apply, xt, v]
    rw [lact_flow_q h, flow_nsmul _ hN]
  have hP0 : Filter.Tendsto (fun t : ℝ => P (xt t)) Filter.atTop (nhds 0) := by
    have hMB : Filter.Tendsto (fun t => M * Bt t) Filter.atTop (nhds 0) := by
      simpa using hBt.const_mul M
    exact squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨0, fun t ht => hdomt t ht⟩) hMB
  exact tendsto_nhds_unique hlim hP0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open scoped ENNReal
open GlobalTheory.WeilAdm.HaarSplit

private theorem opensMeasurableSpace_pi_mixedSpace (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := by
  haveI : SecondCountableTopology (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  infer_instance

theorem exists_haar (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hg0 : g 0 ≠ 0) :
    ∃ μA : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μA ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μA = c * ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ := by
  classical
  haveI := opensMeasurableSpace_pi_mixedSpace F κ
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (κ → FiniteAdeleRing (𝓞 F) F), ν = Measure.addHaar := ⟨_, rfl⟩
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : SFinite ν := by rw [hν]; infer_instance
  haveI : SFinite μ := inferInstance
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := inferInstance
  let h : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ₜ (κ → AdeleRing (𝓞 F) F) :=
    { toEquiv := (splitE F κ).toEquiv
      continuous_toFun := continuous_splitE F κ
      continuous_invFun := continuous_splitE_symm F κ }
  let m := h.toMeasurableEquiv
  have hm : (m : _ → _) = splitE F κ := rfl
  have hgc : Continuous g := hg.1.continuous
  refine ⟨(μ.prod ν).map m, ?_, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν, ?_, ?_, ?_⟩
  · rw [hm]
    exact AddEquiv.isAddHaarMeasure_map (μ.prod ν) (splitE F κ) (continuous_splitE F κ) (continuous_splitE_symm F κ)
  · apply ne_of_gt
    have hU : IsOpen {y | g y = g 0} := hg.1.isOpen_fiber _
    have hpos : 0 < ν {y | g y = g 0} := hU.measure_pos ν ⟨0, rfl⟩
    calc (0 : ℝ≥0∞) < ‖g 0‖ₑ ^ 2 * ν {y | g y = g 0} :=
          ENNReal.mul_pos (pow_ne_zero _ (enorm_ne_zero.2 hg0)) hpos.ne'
      _ = ∫⁻ y, {y | g y = g 0}.indicator (fun _ => ‖g 0‖ₑ ^ 2) y ∂ν :=
          (lintegral_indicator_const hU.measurableSet _).symm
      _ ≤ ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := by
          refine lintegral_mono fun y => ?_
          by_cases hy : g y = g 0
          · simp [Set.indicator, hy]
          · simp [Set.indicator, hy]
  · have hs : HasCompactSupport fun y => ‖g y‖ ^ 2 := hg.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have hint : Integrable (fun y => ‖g y‖ ^ 2) ν := (hgc.norm.pow 2).integrable_of_hasCompactSupport hs
    have h2 := hint.2
    unfold HasFiniteIntegral at h2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h2)
    refine lintegral_congr fun y => ?_
    rw [enorm_pow, enorm_norm]
  · intro f
    rw [lintegral_map_equiv, hm]
    have hpt : ∀ p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F),
        ‖GlobalTheory.WeilM.pureA F f g (splitE F κ p)‖ₑ ^ 2 = ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, enorm_mul, mul_pow]
    simp_rw [hpt]
    rw [mul_comm]
    exact lintegral_prod_mul (μ := μ) (ν := ν) (f := fun z => ‖f z‖ₑ ^ 2) (g := fun y => ‖g y‖ₑ ^ 2)
      (f.continuous.measurable.enorm.pow_const 2).aemeasurable (hgc.measurable.enorm.pow_const 2).aemeasurable

theorem integral_sq_eq {V : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V] (μ : Measure V)
    {f : V → ℂ} (hf : Continuous f) : ∫ x, ‖f x‖ ^ 2 ∂μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  have hc : Continuous fun x => ‖f x‖ ^ 2 := hf.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x‖ ^ 2)
    (Filter.Eventually.of_forall fun x => by positivity) hc.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem opensMeasurable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := opensMeasurableSpace_pi_mixedSpace F κ

theorem snd_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have h := hz (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _)
  have h2 : (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) * ((z i).1, (z i).2)).2 =
      (0 : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 := congrArg Prod.snd (congrFun h i)
  simpa using h2

theorem integral_norm_sq_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∀ (μ : Measure (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ _ T hAct μ hμ t f
  classical
  haveI := hμ
  haveI := opensMeasurable F (Fin a × Fin (a + a'))
  set g : (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (GlobalTheory.SchANonzero.intPts F (Fin a × Fin (a + a'))).indicator 1 with hgdef
  have hgSB : g ∈ GlobalTheory.WeilM.SB _ := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _
  have h0mem : (0 : Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F _ := by
    intro i _ v
    exact zero_mem (v.adicCompletionIntegers F)
  have hg0 : g 0 ≠ 0 := by
    rw [hgdef, Set.indicator_of_mem h0mem]
    simp
  obtain ⟨μA, hμA, c, hc0, hctop, hc⟩ := exists_haar F (Fin a × Fin (a + a')) μ g hgSB hg0
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).unit
  let r : (Fin a × Fin (a + a') → AF F) → ℂ := fun x => g (fun i => (x i).2)
  have htens : ∀ φ : SInf F (Fin a × Fin (a + a')), tens (evI F) (φ : _ → ℂ) r = GlobalTheory.WeilM.pureA F φ g :=
    fun φ => rfl
  have hRest : Rest (evI F) (f : _ → ℂ) r := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · show g _ = g _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero hz i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hA := hAct t f r hRest
  rw [htens, htens] at hA
  have hmem : GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) :=
    Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hu := hU μA hμA (1, γ (Multiplicative.ofAdd t)) _ hmem
  rw [hA, hc, hc] at hu
  have hl := (ENNReal.mul_right_inj hc0 hctop).1 hu
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, hl]

end GlobalTheory.ArchimedeanUnitaryL2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SkewSpaceLineOneParamFockDerivative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LieLines

theorem line_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X)
    (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ), IsInfFam θ →
    IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
    ∀ (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
      (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
      ∃ (h : ℝ → GA D X) (Y : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ τ, Y τ ∈ lieAt X τ) ∧
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (h t)) ∧
        ∀ f₀ : WO (sgn ε M) X → ℂ, IsVacF ψ θ (frSgn ε A) B f₀ → ∀ (P : PolF D X.rank M.rank) (z : WO (sgn ε M) X),
          HasDerivAt (fun t : ℝ => ω (1, h t) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z)
            (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (∑ τ, GlobalTheory.RealQuot.actT ε A B eS τ (Y τ) P) z) 0 := by
  classical
  intro D ψ θ ε M X A B χS χT ω eS eT hθ hω hexp Ws hJ γ hγ
  obtain ⟨L, hL⟩ : ∃ L : GlobalTheory.SmoothForms.LieN X, ∀ t : ℝ, γ (Multiplicative.ofAdd t) =
      GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (GlobalTheory.SmoothForms.expInf θ X (t • L)) :=
    _root_.GlobalTheory.LineDecomp.line_eq_expInf D θ hθ X Ws hJ γ hγ
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ X
  refine ⟨fun t => GlobalTheory.SmoothForms.expInf θ X (t • L), fun τ => (L τ).1, fun τ => (L τ).2, hL, ?_⟩
  intro f₀ hf P z
  have hω' : IsWeilDatumO ψ (sgn ε M) X χS χT (WRep.toSgn ε ω) := hω
  have hψ := hω'.std
  have h1g : ∀ (g : GA D X), WRep.toSgn ε ω (1, g) = ω (1, g) := fun g => by
    simp [WRep.toSgn]
  have hlin : ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (∑ τ, GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) =
      ∑ τ, ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) := map_sum _ _ _
  rcases isEmpty_or_nonempty D.what₂.Tau with hT | ⟨⟨τ₀⟩⟩
  · have e : ∀ t : ℝ, t • L = L := fun t => funext fun τ => (IsEmpty.false τ).elim
    simp only [e, hlin, Finset.univ_eq_empty, Finset.sum_empty, Pi.zero_apply]
    exact hasDerivAt_const _ _
  have hth : ∀ Q, IsThetaFunO ψ (sgn ε M) X (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ Q) :=
    (GlobalTheory.LieScalar.ptF_laws hθ hψ (frSgn ε A) B hf).1 τ₀
  let 𝒮 : Set (GA D X → ℂ) :=
    {φ | ∃ f z, IsThetaFunO ψ (sgn ε M) X f ∧ φ = fun g => WRep.toSgn ε ω (1, g) f z}
  have hc : ∀ φ ∈ 𝒮, Continuous φ := by
    rintro _ ⟨f, z, hf, rfl⟩
    exact (hω'.om_cont f hf z).comp (continuous_const.prodMk continuous_id)
  have hd : ∀ φ ∈ 𝒮, ∀ τ', ∀ Z ∈ lieAt X τ', ∃ φ' ∈ 𝒮, ∀ g,
      HasDerivAt (fun t : ℝ => φ (g * oneP θ X τ' Z t)) (φ' g) 0 := by
    rintro _ ⟨f, z, hf, rfl⟩ τ' Z hZ
    obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genT hθ hω' τ' Z hZ f hf
    refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
    have := h (MonoidHom.inr (GA D (sgn ε M)) (GA D X) g) z
    simpa only [MonoidHom.inr_apply, Prod.mk_mul_mk, mul_one] using this
  let φ : GA D X → ℂ := fun g => WRep.toSgn ε ω (1, g) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z
  have hφ : φ ∈ 𝒮 := ⟨_, z, hth P, rfl⟩
  have h1 := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ X 𝒮 hc hd φ hφ
  have h2 : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ X) φ :=
    (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 h1)
  have h3 := ((h2 1).differentiable (by simp) 0).hasFDerivAt
  have hline : ∀ V : GlobalTheory.SmoothForms.LieN X, HasDerivAt (fun t : ℝ => φ (GlobalTheory.SmoothForms.expInf θ X (t • V)))
      (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 V) 0 := by
    intro V
    have h4 : HasDerivAt (fun t : ℝ => t • V) V 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).smul_const V
      rwa [one_smul] at h
    have h3' : HasFDerivAt (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y))
        (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0) ((0 : ℝ) • V) := by
      rw [zero_smul]
      exact h3
    have h5 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h3' h4
    simpa only [Function.comp_def, one_mul] using h5
  have hτ : ∀ τ, fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
      (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) =
      ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) z := by
    intro τ
    have hl := (GlobalTheory.LieScalar.lieFockAll D (sgn ε M) X (frSgn ε A) B θ ψ χS χT (WRep.toSgn ε ω) f₀ τ (eS τ) (eT τ)
      hθ hω' (hexp τ).1 (hexp τ).2 hf).2 (L τ).1 (L τ).2 P z
    have e := (hline (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)).unique
      (hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        show φ _ = _
        simp only [φ]
        rw [GlobalTheory.SmoothForms.oneP_eq R τ (L τ) t]
        rfl))
    rw [e]
    rfl
  have hsum : ∑ τ, (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) = L := Finset.univ_sum_single L
  have e1 : (fun t : ℝ => ω (1, GlobalTheory.SmoothForms.expInf θ X (t • L)) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) =
      fun t => φ (GlobalTheory.SmoothForms.expInf θ X (t • L)) := funext fun t => by simp only [φ, h1g]
  rw [e1, hlin, Finset.sum_apply]
  have e2 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
      ∑ τ, ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) z := by
    have h7 := map_sum (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0)
      (fun τ => (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)) Finset.univ
    have h8 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
        fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
          (∑ τ, (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)) := by
      congr 1
      exact hsum.symm
    have h9 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
        ∑ τ, fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
          (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) := by
      exact h8.trans h7
    rw [h9]
    exact Finset.sum_congr rfl fun τ _ => hτ τ
  have h6 := hline L
  rwa [e2] at h6

end GlobalTheory.LieLines

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionLinearMul
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine

theorem archAct_linear_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W),
    (∀ (h : UA σ W.J) (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (v + v') = archAct M h v + archAct M h v') ∧
    (∀ (h : UA σ W.J) (c : ℝ) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (c • v) = c • archAct M h v) ∧
    (∀ (h h' : UA σ W.J) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M (h * h') v = archAct M h (archAct M h' v)) := by
  intro F E _ _ _ _ _ σ n d X W M
  refine ⟨fun h v v' => ?_, fun h c v => ?_, fun h h' v => ?_⟩
  · unfold archAct
    rw [Prod.fst_add, Prod.snd_add, lift_add, lift_add, ← Prod.mk_add_mk, map_add (f := _)]
    simp only [actAB, Matrix.mul_add, Matrix.add_mul]
    rw [coordI_add]
  · unfold archAct
    rw [Prod.smul_fst, Prod.smul_snd, lift_smul, lift_smul, ← Prod.smul_mk, map_smul]
    simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]
    rw [coordI_smul]
  · unfold archAct
    rw [lift_coordI]
    simp only [actAB, Matrix.mul_smul, Matrix.smul_mul, coordI_one]
    congr 1
    simp only [one_mul, Units.val_one, Subgroup.coe_one, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    simp only [Matrix.one_mul]

end GlobalTheory.ArchLine
end
end

