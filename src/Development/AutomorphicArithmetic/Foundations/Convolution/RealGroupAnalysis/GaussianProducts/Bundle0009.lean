module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AbsFin1
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CoordinateEmbedNormZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.UxCen
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatFock
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ZetaFin

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AbsFin
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.absFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h : GL (Fin 2) (A E), ∑' ξ, abelian₂ M (ux W f.1 φ h ξ) ≠ ⊤ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  obtain ⟨s, hs⟩ := UpperTheory.ConvolutionTheory.R2.G.nuPos F E D h
  obtain ⟨h₁, c, hnu, hux⟩ := UpperTheory.ConvolutionTheory.R2.G.uxCen F E D W π s h
  have hnu₁ : ((nu F h₁ : (A F)ˣ) : A F).1 = 1 := by
    have e : nu F h * (s ^ 4)⁻¹ = nu F h₁ := by
      rw [hnu, mul_comm, inv_mul_cancel_left]
    rw [← e]
    exact hs
  have hLf : Pp.Lf f.1 := (Pp.cuspZero F π f hf).1
  have hterm : ∀ ξ, abelian₂ M (ux W f.1 φ h ξ) = ‖c‖ₑ * abelian₂ M (ux W f.1 φ h₁ ξ) := by
    intro ξ
    have e : ux W f.1 φ h ξ = fun g => c * ux W f.1 φ h₁ ξ (g * mD (s ^ 2)⁻¹) :=
      funext fun g => hux f hf φ ξ g
    rw [e]
    exact UpperTheory.ConvolutionTheory.R2.G.lamRight F M _ (UpperTheory.ConvolutionTheory.R2.G.uxAv F E D W f.1 hLf φ h₁ ξ).1 c _
  simp only [hterm]
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top enorm_ne_top (UpperTheory.ConvolutionTheory.R2.G.absFin1 F E D W M π f hf φ hφ h₁ hnu₁)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.EqNUMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem eq_nU_mul {F : Type} [Field F] [NumberField F] {g g' : G1 F} (hr : row g = row g') :
    ∃ b, g' = nU b * g := by
  have h0 : g 1 0 = g' 1 0 := congrFun hr 0
  have h1 : g 1 1 = g' 1 1 := congrFun hr 1
  have hi : ∀ i j, (g⁻¹) i j = (!![g 1 1, -g 0 1; -g 1 0, g 0 0] : Matrix (Fin 2) (Fin 2) (A F)) i j :=
    fun i j => congrFun (congrFun (specialLinear_inv_val g) i) j
  have hn : g' * g⁻¹ = nU ((g' * g⁻¹) 0 1) := by
    have d := specialLinear_det_entries g
    have d' := specialLinear_det_entries g'
    apply specialLinear_ext_entries
    · rw [specialLinear_mul_entry, hi, hi]
      simp only [nU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      simp
      rw [h0, h1]
      linear_combination d'
    · simp [nU]
    · rw [specialLinear_mul_entry, hi, hi]
      simp [nU]
      rw [h0, h1]
      ring
    · rw [specialLinear_mul_entry, hi, hi]
      simp [nU]
      rw [← h0, ← h1]
      linear_combination d
  exact ⟨_, by rw [← hn, inv_mul_cancel_right]⟩

theorem UpperTheory.ConvolutionTheory.R2.G.contW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ,
    ContinuousOn (fun p : IdeleGroup F × G1 F => w1 W f.1 φ 1 (mD p.1 * p.2)) (Set.univ ×ˢ KK F) ∧
    ∀ g g', row g = row g' → w1 W f.1 φ 1 g = w1 W f.1 φ 1 g' := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ
  refine ⟨?_, fun g g' hr => ?_⟩
  · have hL : ∀ g, w1 W f.1 φ 1 g = Wf f.1 (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0] := by
      intro g
      have h1 : nu F (1 : GL (Fin 2) (A E)) = 1 := by simp [nu]
      simp [w1, h1]
    simp only [hL]
    obtain ⟨hLf, -⟩ := UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf
    obtain ⟨hWc, -⟩ := UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 hLf
    have hKc : IsCompact (KK F) := (_root_.UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2
    obtain ⟨U, -, hfd, hmem⟩ := (fockSt F E D W).om φ hφ (KK F) hKc (fun k hk => hk.1)
    obtain ⟨n, b, c, B, -, hc, hk⟩ := coefBd F E D W φ (KK F) U hKc hfd hmem
    obtain ⟨H, hH⟩ := hatLin F
    have hS := hatSt F E D W
    have e : ∀ p ∈ (Set.univ ×ˢ KK F : Set (IdeleGroup F × G1 F)),
        hat (W.Om (mD p.1 * p.2) φ).1 ![0, 1, 1, 0] = ((W.η.1 p.1 : ℂˣ) : ℂ) * ((ab p.1 : ℝ) : ℂ) *
          ∑ i, c i p.2 * (H (b i)).1 ![0, ((p.1⁻¹ : (A F)ˣ) : A F), (p.1 : A F), 0] := by
      rintro ⟨a, k⟩ ⟨-, hk'⟩
      have hv : (![(a : A F) * (![0, 1, 1, 0] : V4 F) 0, ((a⁻¹ : (A F)ˣ) : A F) * (![0, 1, 1, 0] : V4 F) 1,
          (a : A F) * (![0, 1, 1, 0] : V4 F) 2, (a : A F) * (![0, 1, 1, 0] : V4 F) 3] : V4 F) =
          ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] := by
        funext i
        fin_cases i <;> simp
      simp only []
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, Module.End.mul_apply, hS.m, hv, (hk k hk').2, ← hH, map_sum]
      simp [Finset.sum_apply]
    have hcont1 : Continuous fun p : IdeleGroup F × G1 F => Wf f.1 (gl (mD p.1 * p.2)) :=
      hWc.comp (continuous_gl.comp ((continuous_mD.comp continuous_fst).mul continuous_snd))
    refine hcont1.continuousOn.mul (ContinuousOn.congr ?_ e)
    refine ContinuousOn.mul (Continuous.continuousOn ?_) (continuousOn_finsetSum _ fun i _ => ?_)
    · refine Continuous.mul ?_ ?_
      · exact Units.continuous_val.comp (W.η.2.1.comp continuous_fst)
      · exact Complex.continuous_ofReal.comp (continuous_ab.comp continuous_fst)
    · refine ContinuousOn.mul ((hc i).comp continuousOn_snd fun p hp => hp.2) (Continuous.continuousOn ?_)
      refine (continuous_of_mem_schwartzBruhatPi (H (b i)).2).comp (continuous_pi fun j => ?_)
      fin_cases j
      · exact continuous_const
      · exact Units.continuous_coe_inv.comp continuous_fst
      · exact Units.continuous_val.comp continuous_fst
      · exact continuous_const
  · obtain ⟨b, rfl⟩ := eq_nU_mul hr
    exact ((conv F E D W M π f hf φ hφ 1).2.2.2.1 b g).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExpInt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.expIntegrability

variable {F : Type} [Field F] [NumberField F]

private theorem adelicWeightFour_eq_product (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (x y : A F) :
    wt4 L N ![0, x, y, 0] = GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N x * GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N y := by
  simp [wt4, Fin.prod_univ_four, GlobalTheory.CompanionTheory.EpConvB.adeleWeight_zero]

private theorem term_int {N : ℕ} (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hN : ∫⁻ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F,
      ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ∂(ideleMeasure F) ≠ ⊤) :
    Integrable (fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 * wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0]) (ideleMeasure F) := by
  have hc : Continuous fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 * wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] := by
    simp only [adelicWeightFour_eq_product]
    have h1 := GlobalTheory.CompanionTheory.EpConvB.continuous_adeleWeight L N
    refine ((UpperTheory.ConvolutionTheory.R2.continuous_ab.inv₀ fun a => UpperTheory.ConvolutionTheory.R2.ab_ne_zero a).pow 2).mul
      ((h1.comp Units.continuous_coe_inv).mul (h1.comp Units.continuous_val))
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun a => ?_) (lt_top_iff_ne_top.2 hN)
  have hnn : 0 ≤ (ab a)⁻¹ ^ 2 * wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] := by
    have : 0 ≤ wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] :=
      Finset.prod_nonneg fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _
    positivity
  rw [Real.enorm_of_nonneg hnn, ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' le_rfl ?_
  have h := ENNReal.le_tsum (f := fun ξ : Fin 2 → F =>
    ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)])) ![1, 0]
  simpa using h

variable [IsTotallyReal F]

private theorem abs_entry_le {k : G1 F} (hk : k ∈ KK F) (j : Fin 2) (w : InfinitePlace F) :
    |TR.pInf F (k 1 j) w| ≤ 1 := by
  have h1 : TR.pInf F ((k.1 * k.1ᵀ) 1 1) = TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) 1 1) :=
    congrArg (TR.infEq F).symm (hk.1 1 1)
  have h2 : (TR.pInf F (k 1 0) w) ^ 2 + (TR.pInf F (k 1 1) w) ^ 2 = 1 := by
    have h3 := congrFun h1 w
    simpa [Matrix.mul_apply, Fin.sum_univ_two, pow_two] using h3
  rw [abs_le_one_iff_mul_self_le_one]
  fin_cases j
  · show TR.pInf F (k 1 0) w * TR.pInf F (k 1 0) w ≤ 1
    nlinarith [sq_nonneg (TR.pInf F (k 1 1) w)]
  · show TR.pInf F (k 1 1) w * TR.pInf F (k 1 1) w ≤ 1
    nlinarith [sq_nonneg (TR.pInf F (k 1 0) w)]

private theorem sz_le (a : (A F)ˣ) {k : G1 F} (hk : k ∈ KK F) :
    sz (row (mD a * k)) ≤ 2 * ∑ w, |TR.pInf F ((a⁻¹ : (A F)ˣ) : A F) w| := by
  have e : ∀ (j : Fin 2) w, |TR.pInf F (row (mD a * k) j) w| ≤ |TR.pInf F ((a⁻¹ : (A F)ˣ) : A F) w| := by
    intro j w
    have h : row (mD a * k) j = ((a⁻¹ : (A F)ˣ) : A F) * k 1 j := by
      rw [row, specialLinear_mul_entry]
      simp [mD]
    rw [h, map_mul, Pi.mul_apply, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_entry_le hk j w)
  simp only [sz, Fin.sum_univ_two]
  rw [two_mul]
  exact add_le_add (Finset.sum_le_sum fun w _ => e 0 w) (Finset.sum_le_sum fun w _ => e 1 w)

private theorem sz_nonneg (r : Fin 2 → A F) : 0 ≤ sz r :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem continuous_sz : Continuous fun g : G1 F => sz (row g) := by
  have h : Continuous (TR.infEq F).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  have hp : Continuous (TR.pInf F) := h.comp continuous_fst
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun w _ => ?_
  exact ((continuous_apply w).comp (hp.comp (UpperTheory.ConvolutionTheory.R2.continuous_entry 1 i))).abs

end UpperTheory.ConvolutionTheory.R2.G.expIntegrability

open UpperTheory.ConvolutionTheory.R2.G.expIntegrability in
theorem UpperTheory.ConvolutionTheory.R2.G.expInt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ R : ℝ,
    Integrable (fun p : IdeleGroup F × G1 F => ((Real.exp (R * sz (row (mD p.1 * p.2))) : ℝ) : ℂ) * iw (w1 W f.1 φ 1) p) M.ν := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ R
  have hS := UpperTheory.ConvolutionTheory.R2.hatSt F E D W
  have hK : IsCompact (KK F) := (UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2
  obtain ⟨U, hUle, hUfd, hUmem⟩ := (UpperTheory.ConvolutionTheory.R2.fockSt F E D W).om φ hφ (KK F) hK fun k hk => hk.1
  obtain ⟨n, b, c, Bc, hb, -, hbd⟩ := UpperTheory.ConvolutionTheory.R2.G.coefBd F E D W φ (KK F) U hK hUfd hUmem
  obtain ⟨H, hH⟩ := UpperTheory.ConvolutionTheory.R2.G.hatLin F
  obtain ⟨N, hN⟩ := UpperTheory.ConvolutionTheory.R2.G.zetaFin F
  have hhat : ∀ i, hat (b i).1 ∈ FockFn D.δ := fun i =>
    UpperTheory.ConvolutionTheory.R2.G.hatFock F D.δ _ (mem_fock.1 (hUle (hb i)))
  have hg := fun i => UpperTheory.ConvolutionTheory.R2.G.fockGauss F D.δ D.neg (hat (b i).1) (hhat i) (2 * |R|) N
  choose Bg L hBg0 hBg using hg
  obtain ⟨Bf, hBf0, hBf⟩ := UpperTheory.ConvolutionTheory.R2.G.bdInv F π f hf (gl '' KK F) (hK.image UpperTheory.ConvolutionTheory.R2.continuous_gl)
  obtain ⟨-, -, -, -, hint⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ 1
  haveI := M.prob

  let T : Fin n → IdeleGroup F → ℝ := fun i a =>
    (ab a)⁻¹ ^ 2 * wt4 (L i) N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0]
  have hT : ∀ i, Integrable (T i) (ideleMeasure F) := fun i => term_int (L i) (hN (L i))
  let G : IdeleGroup F × G1 F → ℝ := fun p => ∑ i, Bf * |Bc| * Bg i * T i p.1
  have hG : Integrable G M.ν := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact ((hT i).comp_fst M.κ).const_mul (Bf * |Bc| * Bg i)
  have hexp : Continuous fun p : IdeleGroup F × G1 F => ((Real.exp (R * sz (row (mD p.1 * p.2))) : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul ?_))
    exact continuous_sz.comp ((UpperTheory.ConvolutionTheory.R2.continuous_mD.comp continuous_fst).mul continuous_snd)
  refine hG.mono' (hexp.aestronglyMeasurable.mul hint.1) ?_
  have hae : ∀ᵐ p ∂M.ν, p.2 ∈ KK F := by
    have h0 : ∀ᵐ k ∂M.κ, k ∈ KK F := by
      rw [ae_iff]
      exact M.supp
    exact Measure.quasiMeasurePreserving_snd.ae h0
  filter_upwards [hae] with p hp
  obtain ⟨a, k⟩ := p
  change k ∈ KK F at hp
  have hnu : nu F (1 : GL (Fin 2) (A E)) = 1 := by simp [nu]
  have hA0 : 0 < ab a := UpperTheory.ConvolutionTheory.R2.ab_pos a
  set v : V4 F := ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] with hv
  have hw : w1 W f.1 φ 1 (mD a * k) =
      Wf f.1 (gl (mD a * k)) * (((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) * hat (W.Om k φ).1 v) := by
    rw [w1, hnu, UpperTheory.ConvolutionTheory.R2.dM_one, mul_one, map_one, Module.End.one_apply, map_mul, Module.End.mul_apply, hS.m, hv]
    simp
  have hsum : hat (W.Om k φ).1 v = ∑ i, c i k * hat (b i).1 v := by
    have h1 := (hbd k hp).2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hH, h1, map_sum]
    simp [Finset.sum_apply, hH]
  have hη : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
    have h1 : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
      have := congrArg (Units.val) (W.η_sq a)
      simpa using this
    have h2 : ‖((W.η.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  have hWf : ‖Wf f.1 (gl (mD a * k))‖ * ab a ≤ Bf := by
    have h1 := (hBf 0 a (gl k) ⟨k, hp, rfl⟩).2
    rw [UpperTheory.ConvolutionTheory.R2.nU_zero, one_mul, ← UpperTheory.ConvolutionTheory.R2.gl_mul] at h1
    calc ‖Wf f.1 (gl (mD a * k))‖ * ab a ≤ Bf * (ab a)⁻¹ * ab a := mul_le_mul_of_nonneg_right h1 hA0.le
      _ = Bf := by field_simp
  set e : ℝ := Real.exp (R * sz (row (mD a * k))) with he
  have he0 : 0 < e := Real.exp_pos _
  have hterm : ∀ i, e * ‖hat (b i).1 v‖ ≤ Bg i * wt4 (L i) N v := by
    intro i
    have h1 : e ≤ Real.exp (2 * |R| * ∑ w, |TR.pInf F (v 1) w|) := by
      refine Real.exp_le_exp.2 ?_
      have h2 := sz_le a hp
      have h3 := sz_nonneg (row (mD a * k))
      have h4 : v 1 = ((a⁻¹ : (A F)ˣ) : A F) := by simp [hv]
      rw [h4]
      calc R * sz (row (mD a * k)) ≤ |R| * sz (row (mD a * k)) := mul_le_mul_of_nonneg_right (le_abs_self R) h3
        _ ≤ |R| * (2 * ∑ w, |TR.pInf F ((a⁻¹ : (A F)ˣ) : A F) w|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg R)
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans (hBg i v)
  have hS1 : e * ‖∑ i, c i k * hat (b i).1 v‖ ≤ ∑ i, |Bc| * (Bg i * wt4 (L i) N v) := by
    calc e * ‖∑ i, c i k * hat (b i).1 v‖ ≤ e * ∑ i, ‖c i k * hat (b i).1 v‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) he0.le
      _ = ∑ i, ‖c i k‖ * (e * ‖hat (b i).1 v‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul]
          ring
      _ ≤ ∑ i, |Bc| * (Bg i * wt4 (L i) N v) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul (((hbd k hp).1 i).trans (le_abs_self _)) (hterm i)
            (mul_nonneg he0.le (norm_nonneg _)) (abs_nonneg _)
  have hn : ‖((e : ℝ) : ℂ) * iw (w1 W f.1 φ 1) (a, k)‖ =
      (ab a)⁻¹ ^ 2 * (‖Wf f.1 (gl (mD a * k))‖ * ab a) * (e * ‖∑ i, c i k * hat (b i).1 v‖) := by
    simp only [iw]
    rw [hw, hsum]
    simp only [norm_mul, hη, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he0, abs_of_pos hA0, abs_pow, abs_inv]
    ring
  show ‖((e : ℝ) : ℂ) * iw (w1 W f.1 φ 1) (a, k)‖ ≤ ∑ i, Bf * |Bc| * Bg i * T i a
  rw [hn]
  have hq : 0 ≤ (ab a)⁻¹ ^ 2 := by positivity
  calc (ab a)⁻¹ ^ 2 * (‖Wf f.1 (gl (mD a * k))‖ * ab a) * (e * ‖∑ i, c i k * hat (b i).1 v‖)
      ≤ (ab a)⁻¹ ^ 2 * Bf * ∑ i, |Bc| * (Bg i * wt4 (L i) N v) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hWf hq) hS1 (by positivity) (by positivity)
    _ = ∑ i, Bf * |Bc| * Bg i * T i a := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [T, ← hv]
        ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ThetaFourierCoeffZeroAndEqShiftedWhittaker
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem normOneIntegral_diagonal_invariant {F : Type} [Field F] [NumberField F] (M₀ : Meas F) (t : IdeleGroup F) (ht : ab t = 1)
    (v : G1 F → ℂ) : M₀.I0 (fun g => v (mD t * g)) = M₀.I0 v := by
  haveI := M₀.prob
  let e : (IdeleGroup F × G1 F) ≃ᵐ (IdeleGroup F × G1 F) :=
    (MeasurableEquiv.mulLeft t).prodCongr (MeasurableEquiv.refl _)
  have hp : MeasurePreserving e M₀.ν M₀.ν :=
    (measurePreserving_mul_left (ideleMeasure F) t).prod (MeasurePreserving.id M₀.κ)
  have hi := hp.integral_comp' (g := iw v)
  rw [Meas.I0, Meas.I0, ← hi]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  change iw (fun g => v (mD t * g)) p = iw v (t * p.1, p.2)
  simp only [iw]
  rw [M.ab_mul, ht, one_mul, M.mD_mul, mul_assoc]

theorem UpperTheory.ConvolutionTheory.R2.G.thetaFourierCoeff_zero_and_eq_shifted_whittaker :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, Wx W M f.1 φ h 0 = 0 ∧ Wx W M f.1 φ h ![1, 0] = W1 W M f.1 φ h ∧
    ∀ ξ, ξ ≠ 0 → Wx W M f.1 φ h ξ = W1 W M f.1 φ (aE (al D ξ) * h) := by
  intro F E _ _ _ _ _ _ _ D W M₀ π f hf φ hφ h
  obtain ⟨hL, hz⟩ := Pp.cuspZero F π f hf
  refine ⟨?_, ?_, fun ξ hξ => ?_⟩
  · have e : wx W f.1 φ h 0 = fun _ => 0 := by
      funext g
      have h1 : ∀ b : A F, ψ (rt ((0 : Fin 2 → F) 0 ^ 2 - D.δ * (0 : Fin 2 → F) 1 ^ 2) * b) = 1 := by
        intro b
        simp [ψ]
      simp only [wx, h1, mul_one, hz, zero_mul]
    simp [Wx, e, Meas.I0, iw]
  · have e : wx W f.1 φ h ![1, 0] = w1 W f.1 φ h := by
      funext g
      simp [wx, w1, Wf, pt]
    rw [Wx, e, W1]
  · obtain ⟨t, ht⟩ := wxPt F E D W ξ hξ
    obtain ⟨-, -, a1, a2, a3⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M₀ π f hf φ hφ (aE (al D ξ) * h)
    have hc := ((UpperTheory.ConvolutionTheory.R2.inv F M₀ _ a1 a2 a3).2 (IdeleGroup.diagonal F t)).2
    have e : wx W f.1 φ h ξ = fun g => (fun g => w1 W f.1 φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) g)) (mD (IdeleGroup.diagonal F t) * g) :=
      funext fun g => (ht f.1 hL φ h g).symm
    have hm := normOneIntegral_diagonal_invariant M₀ (IdeleGroup.diagonal F t) (ab_diagonal t)
      (fun g => w1 W f.1 φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) g))
    rw [Wx, e, hm, hc, W1, ab_diagonal t]
    simp
end

