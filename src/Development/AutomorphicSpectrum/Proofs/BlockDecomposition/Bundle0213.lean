module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitaryRootEmbedding

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowLeftInvariant
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def unitaryUnit {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) : G n :=
  ⟨k.1, (k⁻¹).1,
    by have h : (k * k⁻¹).1 = 1 := by rw [mul_inv_cancel]; rfl
       exact h,
    by have h : (k⁻¹ * k).1 = 1 := by rw [inv_mul_cancel]; rfl
       exact h⟩

theorem unitaryUnit_inv_val {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ((unitaryUnit k)⁻¹ : G n).val = (k⁻¹).1 := rfl

theorem inner_cls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (f g : Mat n → V) (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hg : MemLp (fun y : G n => g y.val) 2 μ) :
    ⟪cls μ f, cls μ g⟫_ℂ = ∫ y : G n, ⟪f y.val, g y.val⟫_ℂ ∂μ := by
  unfold cls
  rw [dite_eq_left hf, dite_eq_left hg, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem inner_cls_lTr {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) (f g : Mat n → V)
    (hf : MemLp (fun y : G n => f y.val) 2 μ) (hf' : MemLp (fun y : G n => lTr x f y.val) 2 μ)
    (hg : MemLp (fun y : G n => g y.val) 2 μ) (hg' : MemLp (fun y : G n => lTr x⁻¹ g y.val) 2 μ) :
    ⟪cls μ (lTr x f), cls μ g⟫_ℂ = ⟪cls μ f, cls μ (lTr x⁻¹ g)⟫_ℂ := by
  rw [inner_cls μ _ _ hf' hg, inner_cls μ _ _ hf hg',
    ← integral_mul_left_eq_self (μ := μ) (fun y : G n => ⟪f y.val, lTr x⁻¹ g y.val⟫_ℂ) x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h : (x⁻¹ : G n).val * (x.val * y.val) = y.val := by
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_left]
  simp only [lTr, Units.val_mul, h]

theorem isSec_lTr {n : ℕ} {E : KMod n} (x : G n) {f : Mat n → E.V} (hf : IsSec E f) : IsSec E (lTr x f) := by
  intro g hg k
  have hxg : x.val * g ∈ GLs n := by
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hg ⊢
    exact mul_ne_zero (Matrix.isUnits_det_units x).ne_zero hg
  have := hf _ hxg k
  simpa only [lTr, mul_assoc] using this

theorem inner_rho {n : ℕ} (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) (v w : E.V) :
    ⟪v, E.ρ k w⟫_ℂ = ⟪E.ρ k⁻¹ v, w⟫_ℂ := by
  have hI : ∀ a b : E.V, ⟪E.ρ k a, E.ρ k b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b =>
    LinearIsometry.inner_map_map (⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩ : E.V →ₗᵢ[ℂ] E.V) a b
  have h1 : E.ρ k (E.ρ k⁻¹ v) = v := by
    have h := map_mul E.ρ k k⁻¹
    rw [mul_inv_cancel, map_one] at h
    have h2 := congrArg (fun S : E.V →L[ℂ] E.V => S v) h
    simpa using h2.symm
  rw [← hI (E.ρ k⁻¹ v) w, h1]

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem rowLeft (hLS : LtSob) (hLC : LtComm) : RowLeft := by
  intro n _ _ μ _ E _ Ω T F c hStd h A hR hRow k y hy v
  have hStd' := hStd
  obtain ⟨hLg, hUn, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, hS1, hS2, hS3, hS4, hOm, hc⟩ := hStd'
  have hCF := hCS.2.2.2.2.1 n μ E.V hUn
  have hSB := hCS.2.2.2.2.2.1 n μ E.V hLg hUn hRC
  obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm h hR
  have hLt := hLS n μ E.V hLg hUn hRC
  have hL2 : ∀ {f : Mat n → E.V}, Sob μ f → MemLp (fun y : G n => f y.val) 2 μ := fun hf => hf.2 []
  set x : G n := unitaryUnit k with hx
  set r : Mat n → E.V := fun y => A y v with hr
  set b : Mat n → E.V := fun y => A y (E.ρ k⁻¹ v) with hb
  set a : Mat n → E.V := lTr x r with ha
  have hrow := hRow v
  have hrowb := hRow (E.ρ k⁻¹ v)
  have hrS : Sob μ r := hrow.1
  have hbS : Sob μ b := hrowb.1
  have haS : Sob μ a := (hLt x r hrS).1
  have haSec : IsSec E a := isSec_lTr x hrow.2.1
  have hkey : ∀ ψ : Mat n → E.V, Sob μ ψ → IsSec E ψ → ⟪cls μ a, cls μ ψ⟫_ℂ = ⟪cls μ b, cls μ ψ⟫_ℂ := by
    intro ψ hψ hψs
    obtain ⟨ψ', hψ'S, hψ's, hψ'c, -⟩ := hC (cls μ ψ) (subset_closure ⟨ψ, hψ, hψs, rfl⟩)
    have hlψ := (hLt x⁻¹ ψ hψ).1
    have hlψ' := (hLt x⁻¹ ψ' hψ'S).1
    have hcomm := hLC n μ E Ω T F c hStd h x⁻¹ ψ ψ' hψ hψ'S hψ'c
    have e1 : ⟪cls μ a, cls μ ψ⟫_ℂ = ⟪cls μ r, cls μ (lTr x⁻¹ ψ)⟫_ℂ :=
      inner_cls_lTr μ x r ψ (hL2 hrS) (hL2 haS) (hL2 hψ) (hL2 hlψ)
    have e2 := hrow.2.2 (lTr x⁻¹ ψ) (lTr x⁻¹ ψ') hlψ (isSec_lTr _ hψs) hlψ' (isSec_lTr _ hψ's) hcomm
    have e3 : lTr x⁻¹ ψ' 1 = E.ρ k (ψ' 1) := by
      have h1 := hψ's 1 (one_mem_GLs n) k⁻¹
      rw [inv_inv, one_mul] at h1
      simpa only [lTr, mul_one, hx, unitaryUnit_inv_val] using h1
    have e4 := hrowb.2.2 ψ ψ' hψ hψs hψ'S hψ's hψ'c
    rw [e1, e2, e3, inner_rho, ← e4]
  set ψ : Mat n → E.V := (-1 : ℂ) • b + a with hψd
  have hψS : Sob μ ψ := ((hSB b hbS).2.2.2.1 (-1) a haS).1
  have hbSec : IsSec E b := hrowb.2.1
  have hψs : IsSec E ψ := by
    intro g hg k'
    simp only [hψd, Pi.add_apply, Pi.smul_apply, map_add (f := _), map_smul]
    rw [hbSec g hg k', haSec g hg k']
  have hcψ : cls μ ψ = cls μ a - cls μ b := by
    rw [hψd, hCF.2.1 (-1) b a (hL2 hbS) (hL2 haS)]
    simp [sub_eq_add_neg, add_comm]
  have hz := hkey ψ hψS hψs
  have hzero : cls μ a - cls μ b = 0 := by
    rw [hcψ] at hz
    have : ⟪cls μ a - cls μ b, cls μ a - cls μ b⟫_ℂ = 0 := by
      rw [inner_sub_left, hz, sub_self]
    exact inner_self_eq_zero.mp this
  have hfin := hCF.1 a b haS.1.continuousOn hbS.1.continuousOn (hL2 haS) (hL2 hbS) (sub_eq_zero.mp hzero) y hy
  exact hfin

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowMatrix
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc.RowLin

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem sum_sec {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hCl : ClsFacts) (hOps : SobOps)
    {ι : Type} (f₀ : Mat n → E.V) (h₀ : Sob μ f₀) (f : ι → Mat n → E.V) (hS : ∀ i, Sob μ (f i))
    (hI : ∀ i, IsSec E (f i)) (a : ι → ℂ) (s : Finset ι) :
    Sob μ (fun y => ∑ i ∈ s, a i • f i y) ∧ IsSec E (fun y => ∑ i ∈ s, a i • f i y) ∧
      cls μ (fun y => ∑ i ∈ s, a i • f i y) = ∑ i ∈ s, a i • cls μ (f i) := by
  classical
  have hlin := (hCl n μ E.V hU).2.1
  have hadd : ∀ (b : ℂ) (g g' : Mat n → E.V), Sob μ g → Sob μ g' → Sob μ (b • g + g') := fun b g g' hg hg' =>
    ((hOps n μ E.V hLg hU hR g hg).2.2.2.1 b g' hg').1
  have hmem : ∀ g : Mat n → E.V, Sob μ g → MemLp (fun y : G n => g y.val) 2 μ := fun g hg => hg.2 []
  induction s using Finset.induction_on with
  | empty =>
    have hz : (fun _ : Mat n => (0 : E.V)) = (-1 : ℂ) • f₀ + f₀ := by
      funext y; simp
    simp only [Finset.sum_empty]
    refine ⟨hz ▸ hadd _ _ _ h₀ h₀, fun g _ k => by simp, ?_⟩
    rw [hz, hlin _ _ _ (hmem _ h₀) (hmem _ h₀)]
    simp
  | insert i s hi ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hz : (fun y => ∑ j ∈ insert i s, a j • f j y) = a i • f i + fun y => ∑ j ∈ s, a j • f j y := by
      funext y; simp [Finset.sum_insert hi]
    rw [hz, Finset.sum_insert hi]
    refine ⟨hadd _ _ _ (hS i) ih1, fun g hg k => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), map_smul]
      rw [hI i g hg k]
      exact congrArg (a i • (E.ρ k⁻¹) (f i g) + ·) (ih2 g hg k)
    · rw [hlin _ _ _ (hmem _ (hS i)) (hmem _ ih1), ih3]

end GlobalTheory.CompanionTheory.KerFc.RowLin

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rowMatrix_holds : RowMatrix := by
  intro n _ _ μ _ E _ Ω T F c hstd h hrow
  obtain ⟨hLg, hU, hR, -, -, -, -, hCS, -⟩ := hstd
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  let e := stdOrthonormalBasis ℂ E.V
  choose f hf using fun i => hrow (e i)
  obtain ⟨f₀, hf₀⟩ := hrow 0
  refine ⟨fun y => ∑ i, (innerSL ℂ (e i)).smulRight (f i y), fun v => ?_⟩
  have hA : (fun y => (∑ i, (innerSL ℂ (e i)).smulRight (f i y)) v) =
      fun y => ∑ i ∈ Finset.univ, (⟪e i, v⟫_ℂ) • f i y := by
    funext y
    simp [ContinuousLinearMap.sum_apply]
  obtain ⟨h1, h2, h3⟩ := RowLin.sum_sec μ E hLg hU hR hCl hOps f₀ hf₀.1 f (fun i => (hf i).1)
    (fun i => (hf i).2.1) (fun i => ⟪e i, v⟫_ℂ) Finset.univ
  show Row μ E F h v (fun y => (∑ i, (innerSL ℂ (e i)).smulRight (f i y)) v)
  rw [hA]
  refine ⟨h1, h2, fun φ f' hφ hφs hf' hf's hcl => ?_⟩
  rw [h3, sum_inner, ← (e.sum_inner_mul_inner v (f' 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_conj_symm, (hf i).2.2 φ f' hφ hφs hf' hf's hcl]

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowSupport
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma sr_window {R a : ℝ} (h : R < a) : ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ (∀ s, 0 ≤ β s) ∧ 0 < β a ∧
    (∀ s, s ≤ R → β s = 0) ∧ ∀ s, a + 1 ≤ s → β s = 0 := by
  refine ⟨fun s => Real.smoothTransition (s - R) * Real.smoothTransition (a + 1 - s), ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))
  · intro s
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
      (Real.smoothTransition.pos_of_pos (by linarith))
  · intro s hs
    simp only [Real.smoothTransition.zero_of_nonpos (show s - R ≤ 0 by linarith), zero_mul]
  · intro s hs
    simp only [Real.smoothTransition.zero_of_nonpos (show a + 1 - s ≤ 0 by linarith), mul_zero]

lemma sr_inner_cls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {f g : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hg : MemLp (fun y : G n => g y.val) 2 μ) :
    Integrable (fun y : G n => ⟪f y.val, g y.val⟫_ℂ) μ ∧
      ⟪cls μ f, cls μ g⟫_ℂ = ∫ y : G n, ⟪f y.val, g y.val⟫_ℂ ∂μ := by
  have e1 : cls μ f = hf.toLp _ := dif_pos hf
  have e2 : cls μ g = hg.toLp _ := dif_pos hg
  have hae : (fun y : G n => ⟪(hf.toLp _ : Lp V 2 μ) y, (hg.toLp _ : Lp V 2 μ) y⟫_ℂ) =ᵐ[μ]
      fun y : G n => ⟪f y.val, g y.val⟫_ℂ := by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y a b
    rw [a, b]
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) (hf.toLp _) (hg.toLp _)).congr hae, ?_⟩
  rw [e1, e2, L2.inner_def]
  exact integral_congr_ae hae

lemma sr_val_mem {n : ℕ} (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

lemma sr_eq_zero {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {ψ : G n → ℝ} (hc : Continuous ψ) (h0 : ∀ y, 0 ≤ ψ y) (hi : Integrable ψ μ) (hz : ∫ y, ψ y ∂μ = 0) :
    ∀ y, ψ y = 0 := by
  have hae : ψ =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg h0 hi).1 hz
  have := (Continuous.ae_eq_iff_eq μ hc continuous_zero).1 hae
  intro y
  rw [this]
  rfl

theorem supportRow : SupportRow := by
  intro n _ _ μ _ E _ Ω T F c hStd g T₀ h hg hh H
  obtain ⟨hLg, hUn, hRC, hSobG, hAlg, hWS, hWC, hCS, hSO, hPW, -, -, -, -, hOm, -⟩ := hStd
  have hCptSob : CptSob := hCS.2.2.2.2.2.2.1
  obtain ⟨c₀, hc₀⟩ := hWS n
  refine ⟨|c₀| * (1 + |T₀|), ?_⟩
  intro v f hRow y₀ hy₀ hR
  obtain ⟨hfSob, hfSec, hfRow⟩ := hRow
  obtain ⟨β, hβs, hβ0, hβpos, hβlo, hβhi⟩ := sr_window hR
  obtain ⟨-, -, hLk, hLs, -, -, -⟩ := hLg n
  set φ : Mat n → E.V := fun y => ((β (lg y) : ℝ) : ℂ) • f y with hφ

  have hφs : ContDiffOn ℝ ∞ φ (GLs n) := by
    have h1 : ContDiffOn ℝ ∞ (fun y : Mat n => ((β (lg y) : ℝ) : ℂ)) (GLs n) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hβs.comp_contDiffOn hLs)
    exact h1.smul hfSob.1
  have hφsec : IsSec E φ := by
    intro y hy k
    have hl : lg (y * k.1) = lg y := by
      have := hLk y hy 1 k
      simpa using this
    simp only [hφ, hl, hfSec y hy k, map_smul]
  have hφc : Cpt φ := by
    refine ⟨lg y₀ + 1, fun y _ hy => ?_⟩
    simp only [hφ, hβhi _ hy.le, Complex.ofReal_zero, zero_smul]
  have hφCE : φ ∈ CE E := ⟨hφs, hφsec⟩
  have hφSob : Sob μ φ := (hCptSob n μ E.V hLg hRC φ hφs hφc).1
  obtain ⟨u, huW, hu0⟩ := hWC n E φ hφCE hφc
  obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSobG hAlg hCS hOm h hh
  obtain ⟨f', hf'Sob, hf'Sec, hf'cls, -⟩ := hC (cls μ φ) (subset_closure ⟨φ, hφSob, hφsec, rfl⟩)
  have h1G : (1 : Mat n) ∈ GLs n := by
    show (1 : Mat n).det ≠ 0
    simp

  have hf'1 : f' 1 = 0 := by
    rw [← H φ hφCE hφc u huW hu0 f' hf'Sob hf'Sec hf'cls 1 h1G]
    have : ∀ t, (g t : ℂ) • u t 1 = 0 := by
      intro t
      by_cases hgt : g t = 0
      · simp [hgt]
      · have ht : |t| ≤ T₀ := by
          by_contra hcon
          exact hgt (hg.2.2 t (not_le.1 hcon))
        have hut : u t 1 = 0 := by
          refine hc₀ E u huW t 1 h1G fun y hy hly => ?_
          rw [one_mul, hu0 y hy]
          have hb : lg y ≤ |c₀| * (1 + |T₀|) := by
            refine hly.trans ?_
            have h1 : c₀ ≤ |c₀| := le_abs_self _
            have h2 : |t| ≤ |T₀| := ht.trans (le_abs_self _)
            have h3 : 0 ≤ |c₀| := abs_nonneg _
            have h4 : 0 ≤ |t| := abs_nonneg _
            nlinarith
          simp only [hφ, hβlo _ hb, Complex.ofReal_zero, zero_smul]
        simp [hut]
    simp [this]
  have hzero : ⟪cls μ f, cls μ φ⟫_ℂ = 0 := by
    rw [hfRow φ f' hφSob hφsec hf'Sob hf'Sec hf'cls, hf'1, inner_zero_right]

  have hfL : MemLp (fun y : G n => f y.val) 2 μ := hfSob.2 []
  have hφL : MemLp (fun y : G n => φ y.val) 2 μ := hφSob.2 []
  obtain ⟨hI, hE⟩ := sr_inner_cls μ hfL hφL
  set ψ : G n → ℝ := fun y => β (lg y.val) * ‖f y.val‖ ^ 2 with hψ
  have hpt : ∀ y : G n, ⟪f y.val, φ y.val⟫_ℂ = (ψ y : ℂ) := by
    intro y
    simp only [hφ, hψ, inner_smul_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hψi : Integrable ψ μ := by
    have := hI.re
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [hpt y]
  have hψz : ∫ y, ψ y ∂μ = 0 := by
    have h2 : ((∫ y, ψ y ∂μ : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal, ← hzero, hE]
      exact integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)
    exact_mod_cast h2
  have hlc : Continuous (fun y : G n => lg y.val) :=
    hLs.continuousOn.comp_continuous Units.continuous_val sr_val_mem
  have hfc : Continuous (fun y : G n => f y.val) :=
    hfSob.1.continuousOn.comp_continuous Units.continuous_val sr_val_mem
  have hψc : Continuous ψ := (hβs.continuous.comp hlc).mul (hfc.norm.pow 2)
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (hβ0 _) (by positivity)
  have hall := sr_eq_zero μ hψc hψ0 hψi hψz
  have := hall (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ hy₀)
  have hval : (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ hy₀ : G n).val = y₀ := rfl
  simp only [hψ, hval] at this
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' hβpos.ne'
  · simpa using h'

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateCommutes
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def lTrL {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun y : G n => x * y) (measurePreserving_mul_left μ x)).toContinuousLinearMap

theorem memLp_lTr {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) : MemLp (fun y : G n => lTr x f y.val) 2 μ :=
  hf.comp_measurePreserving (measurePreserving_mul_left μ x)

theorem lTrL_cls {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) : lTrL μ V x (cls μ f) = cls μ (lTr x f) := by
  unfold cls
  rw [dite_eq_left hf, dite_eq_left (memLp_lTr μ x hf)]
  exact Lp.toLp_compMeasurePreserving hf (measurePreserving_mul_left μ x)

theorem ltComm_of_ltSob : LtSob → LtComm := by
  intro hL n _ _ μ _ E _ Ω T F c hS h x f f' hf hf' hff'
  obtain ⟨hLg, hU, hR, -, -, -, -, hCS, -, -, hM, -, -, -, hO, -⟩ := hS
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  have hcomm : lTrL μ E.V x * F.Φ h = F.Φ h * lTrL μ E.V x := by
    refine F.comm _ (fun m => ?_) h
    obtain ⟨f₀, hf₀, hc⟩ := hM m.1 m.2
    have hL₀ := hL n μ E.V hLg hU hR x f₀ hf₀
    have hmem : cls μ (lTr x f₀) ∈ Msob μ E.V := Submodule.subset_span ⟨_, hL₀.1, rfl⟩
    have hm₀ : cls μ f₀ ∈ Msob μ E.V := hc ▸ m.2
    have hm : m = ⟨cls μ f₀, hm₀⟩ := Subtype.ext hc.symm
    have hO₀ : Sob μ (Om f₀) := (hOps n μ E.V hLg hU hR f₀ hf₀).1
    have hf₀m : MemLp (fun y : G n => f₀ y.val) 2 μ := hf₀.2 []
    have hO₀m : MemLp (fun y : G n => Om f₀ y.val) 2 μ := hO₀.2 []
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · change cls μ (lTr x f₀) = lTrL μ E.V x m.1
      rw [← hc, lTrL_cls μ x hf₀m]
    · rw [hO _ hmem hL₀.1, hm, hO _ hm₀ hf₀, lTrL_cls μ x hO₀m]
      exact (hCl n μ E.V hU).2.2.1 _ _ hL₀.2
  have hfm : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []
  have hfm' : MemLp (fun y : G n => f' y.val) 2 μ := hf'.2 []
  rw [← lTrL_cls μ x hfm', hff', ← lTrL_cls μ x hfm]
  exact DFunLike.congr_fun hcomm (cls μ f)

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivative
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.ExpCurve

section Entries

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  haveI : FiniteDimensional ℝ (Mat n) := inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))
  haveI : CompleteSpace (Mat n) := FiniteDimensional.complete ℝ (Mat n)
  have h : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n))
      (NormedSpace.exp (t • X) * X : Mat n) t := hasDerivAt_exp_smul_const X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

end Entries

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_exp {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  exact hasDerivAt_exp_entry X t i j

theorem expC_continuous_hasDerivAt :
    ∀ (n : ℕ) (X : Mat n), Continuous (expC X) ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  intro n X
  refine ⟨?_, hasDerivAt_exp X⟩
  refine (GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG (n := n)).isInducing.continuous_iff.2 ?_
  exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp X t).continuousAt

end GlobalTheory.CompanionTheory.PresSobA.ExpCurve
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReflectionRootUnipotentShift
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapRoot.Unip

variable {L : Type} [Field L] {n : ℕ}

theorem sR_uR_mul_unip : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (v : GU σ n), IsUnipU v →
    ∃ y : L, ∀ x : L, ∃ b : GU σ n, IsUnipU b ∧
      sR σ hσ a h * uR σ hσ a h x * v = b * (sR σ hσ a h * uR σ hσ a h (x + y)) :=
  _root_.UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR_uR_mul_unip

end GlobalTheory.CompanionTheory.SwapRoot.Unip

end
end

