module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.HatMaj
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RowMaj
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg' {F : Type} [Field F] [NumberField F]
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

theorem UpperTheory.ConvolutionTheory.R2.Ff.rowMaj :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), RowMaj W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ y hy c hc
  obtain ⟨K, hK, hBK⟩ := hatMaj F E D W φ hφ y hy
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨C, hC⟩ := hN K hK c hc
  obtain ⟨B, hB⟩ := hBK N
  refine ⟨|B| * C, fun b a k hk hca => ?_⟩
  obtain ⟨hs, hle⟩ := hC a hca
  have hab : 0 < ab a := (IdeleGroup.ideleModule F a).2
  let ι : (Fin 2 → F) → (Fin 4 → F) := fun ξ => ![0, 0, ξ 0, ξ 1]
  have hι : Function.Injective ι := by
    intro ξ ξ' h
    funext i
    fin_cases i
    · exact congrFun h 2
    · exact congrFun h 3
  have hpt : ∀ ξ : Fin 2 → F,
      (![0, ((a⁻¹ : (A F)ˣ) : A F) * 0, a * rt (ξ 0), a * rt (ξ 1)] : V4 F) = sc a (ι ξ) := by
    intro ξ
    funext i
    fin_cases i <;> simp [sc, ι]
  have hterm : ∀ ξ : Fin 2 → F,
      ‖hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖ ≤
        |B| * ab a * wt K N (sc a (ι ξ)) := by
    intro ξ
    have h := hB b a k hk 0 (rt (ξ 0)) (rt (ξ 1))
    rw [hpt] at h
    refine h.trans ?_
    have hw := wt_nonneg' K N (sc a (ι ξ))
    have : B ≤ |B| := le_abs_self B
    gcongr
  have hsι : Summable fun ξ : Fin 2 → F => wt K N (sc a (ι ξ)) := hs.comp_injective hι
  have hsn : Summable fun ξ : Fin 2 → F =>
      ‖hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsι.mul_left _)
  have hsum : ∑' ξ : Fin 2 → F, wt K N (sc a (ι ξ)) ≤ C :=
    (Summable.tsum_le_tsum_of_inj ι hι (fun _ _ => wt_nonneg' K N _) (fun _ => le_rfl) hsι hs).trans hle
  unfold ThRow
  calc ‖∑' ξ : Fin 2 → F, hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖
      ≤ ∑' ξ : Fin 2 → F, ‖hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' ξ : Fin 2 → F, |B| * ab a * wt K N (sc a (ι ξ)) :=
        Summable.tsum_le_tsum hterm hsn (hsι.mul_left _)
    _ = |B| * ab a * ∑' ξ : Fin 2 → F, wt K N (sc a (ι ξ)) := tsum_mul_left
    _ ≤ |B| * ab a * C := by gcongr
    _ = |B| * C * ab a := by ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical Pointwise

theorem UpperTheory.ConvolutionTheory.R2.Ff.thBound :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2), ThBound W π := by
  intro F E _ _ _ _ _ _ _ D W π f hf φ hφ C hC
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red F
  obtain ⟨B₁, N, hB₁⟩ := UpperTheory.ConvolutionTheory.R2.Ff.thMaj F E D W φ hφ c hc
  have hKc : IsCompact (KK F) := (UpperTheory.ConvolutionTheory.R2.Ff.iwa F).1
  have hC' : IsCompact ((gl (F := F) '' KK F) * C) := (hKc.image continuous_gl).mul hC
  obtain ⟨B₂, hB₂⟩ := (UpperTheory.ConvolutionTheory.R2.decay F π f hf).2 _ hC' c hc 2
  refine ⟨B₂ * B₁, N, fun y hy g x hx => ?_⟩
  obtain ⟨γ, b, a, k, hk, hg, ha⟩ := hred g
  have hp : 0 < ab a := ab_pos a
  have e1 : f.1 (gl g * x) = f.1 (gl (nU b * mD a) * (gl k * x)) := by
    rw [← mul_assoc, ← gl_mul, ← hg, gl_mul, gl_ratS, mul_assoc, (π.cusp _ hf).1.left]
  have e2 : Th (W.Om g (W.L (infGL E 2 y) φ)).1 = Th (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 := by
    rw [← hg]
    exact ((UpperTheory.ConvolutionTheory.R2.Ff.thMeas F E D W (W.L (infGL E 2 y) φ)).2.1 γ g).symm
  have h1 := hB₂ b a (gl k * x) (Set.mul_mem_mul ⟨k, hk, rfl⟩ hx) ha
  have h2 := hB₁ y hy b a k hk ha
  rw [e1, e2, norm_mul]
  calc _ ≤ (B₂ * (ab a)⁻¹ ^ 2) * (B₁ * Ht y ^ N * ab a ^ 2) :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = B₂ * B₁ * Ht y ^ N := by
        field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThDerOm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.thDerOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ThDerOm W := by
  intro F E _ _ _ _ _ _ _ D W φ φ' hφ' G hG hD g h t

  have hcomm : ∀ (g : G1 F) (x : S4 F),
      W.Om g (W.L h x) = W.L h (W.Om (cD (nu F h)⁻¹ g) x) := by
    intro g x
    have e := W.comm h (cD (nu F h)⁻¹ g)
    rw [← cD_mul_left, mul_inv_cancel, cD_one_left] at e
    have e' := congrArg (fun T : Module.End ℂ (S4 F) => T x) e
    simpa only [Module.End.mul_apply] using e'.symm
  have hmul : ∀ (a b : G1 F) (x : S4 F), W.Om (a * b) x = W.Om a (W.Om b x) := by
    intro a b x
    rw [map_mul, Module.End.mul_apply]

  have hDL : Der (fun s => W.L h (W.Om (G s) φ)) (fun s => W.L h (W.Om (G s) φ')) := by
    intro s v
    simp only [W.L_apply]
    exact (hD s _).const_mul _

  have hdom : ∀ (g : G1 F) (t : ℝ),
      Dom (Metric.ball t 1) fun s => (W.Om g (W.L h (W.Om (G s) φ'))).1 := by
    intro g t
    let c : ℝ → G1 F := fun s => cD (nu F h)⁻¹ g * G s
    have hc : Continuous c := continuous_const.mul hG
    have hC : IsCompact (c '' Metric.closedBall t 1) := (isCompact_closedBall t 1).image hc
    obtain ⟨K, hK, hB⟩ := lDom F E D W (G1 F) (c '' Metric.closedBall t 1) (fun k => W.Om k φ')
      (omCpt F E D W φ' hφ' _ hC) {h} isCompact_singleton
    refine ⟨K, hK, fun N => ?_⟩
    obtain ⟨B, hB⟩ := hB N
    refine ⟨B, fun s hs v => ?_⟩
    have hmem : ((h, c s) : GL (Fin 2) (A E) × G1 F) ∈ ({h} : Set _) ×ˢ (c '' Metric.closedBall t 1) :=
      ⟨rfl, s, Metric.ball_subset_closedBall hs, rfl⟩
    have := hB _ hmem v
    simpa only [hcomm, hmul, c] using this
  exact thDer F _ _ (omDer F E D W _ _ hDL hdom g) t (hdom g t)
end

