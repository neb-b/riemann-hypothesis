module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0820
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0241
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscCoverLatticeBasisRealHolomorphic
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem latBasis_logCover_real_holo : ∀ (n a g r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ), IsLatFam (Metric.ball 0 1) K → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → r = 2 * g ∧ (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s)) ∧ ∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a) := by
  intro n a g r K lam hK hlam hB

  have hne : (fun k : Fin n => if (k : ℕ) < a then (-1 : ℂ) else 0) ∈ logDom n a := by
    intro k
    by_cases h : (k : ℕ) < a <;> simp [h]
  obtain ⟨hOpen, -, hAn, hMaps⟩ := GlobalTheory.logDom_chart_props n a

  have hmem : ∀ s ∈ logDom n a, ∀ j, lam s j ∈ K (logExp a s) := by
    intro s hs j
    refine ((hB s hs).2.2 _).2 ⟨Pi.single j 1, ?_⟩
    simp [Pi.single_apply]
  have hreal : ∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) := by
    intro s hs
    obtain ⟨hli, hsp, hK'⟩ := hB s hs
    have hspanK : Submodule.span ℝ (K (logExp a s)) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact hmem s hs j)
    exact (GlobalTheory.LatReal.isRealBasis_of_isLatFam n g r (Metric.ball 0 1) K (logExp a s) (lam s) hK
      (hMaps hs) hspanK hli hK').1
  refine ⟨?_, hreal, ?_⟩
  · set s₀ := (fun k : Fin n => if (k : ℕ) < a then (-1 : ℂ) else 0)
    have hli := hreal s₀ hne
    have hsp := (hB s₀ hne).2.1
    have h1 := linearIndependent_iff_card_eq_finrank_span.1 hli
    rw [Set.finrank, hsp, finrank_top, Fintype.card_fin] at h1
    rw [h1, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  · intro j k
    have hF := IsLatFam.pullback_analytic n n g (Metric.ball 0 1) (logDom n a) K (logExp a) hK hOpen
      (fun s _ => hAn s) hMaps
    intro s₀ hs₀
    have hnhds : logDom n a ∈ 𝓝 s₀ := hOpen.mem_nhds hs₀
    obtain ⟨ζ, hζ0, hζa, hev⟩ := hF.2.2.2 s₀ hs₀ (lam s₀ j) (hmem s₀ hs₀ j)
    have hc : ContinuousAt (fun s => (s, lam s j)) s₀ :=
      continuousAt_id.prodMk ((continuous_apply j).continuousAt.comp (hlam.continuousAt hnhds))
    have hev' : ∀ᶠ s in 𝓝 s₀, (lam s j ∈ K (logExp a s) ↔ lam s j = ζ s) := by
      have := hc.tendsto.eventually hev
      simpa [hζ0] using this
    have heq : (fun s => lam s j) =ᶠ[𝓝 s₀] ζ := by
      filter_upwards [hev', hnhds] with s h1 h2
      exact h1.1 (hmem s h2 j)
    have hd : DifferentiableAt ℂ (fun s => lam s j) s₀ :=
      hζa.differentiableAt.congr_of_eventuallyEq heq
    exact (differentiableAt_pi.1 hd k).differentiableWithinAt

end GlobalTheory.ShFam.Hor.LogCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def ReadTw (D : D7) (a : D.nd.Loc) : Prop :=
  ∃ (φ : FractionRing (D.ntw.O0 (D.ntw.twOf a)) →+* Qbar (D.ntw.l (D.ntw.twOf a)))
    (ι : Qbar (D.ntw.l (D.ntw.twOf a)) ≃+* ℂ),
    (∀ z : ℤ_[D.ntw.l (D.ntw.twOf a)], φ (algebraMap (D.ntw.O0 (D.ntw.twOf a)) _
        (algebraMap ℤ_[D.ntw.l (D.ntw.twOf a)] (D.ntw.O0 (D.ntw.twOf a)) z)) =
      algebraMap ℚ_[D.ntw.l (D.ntw.twOf a)] (Qbar (D.ntw.l (D.ntw.twOf a))) (z : ℚ_[D.ntw.l (D.ntw.twOf a)])) ∧
    (∀ x : ↥D.LL0, ι (φ ((if D.ntw.twSide a then D.ntw.emb0 (D.ntw.twOf a) else D.ntw.emb0b (D.ntw.twOf a)) x)) =
      embLL0 D x) ∧
    ∀ y : D.ntw.O0 (D.ntw.twOf a), ι (φ (algebraMap _ (FractionRing (D.ntw.O0 (D.ntw.twOf a))) y)) =
      iotaO D.nd D.naut a (D.ntw.twist₂ a y)

end GlobalTheory.RowTriple

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
section
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GrassTop

def wt {ι : Type} (d : ι × ℕ →₀ ℕ) : ℕ := d.sum fun x i => x.2 * i

def rel (k : ℕ) : MvPolynomial (Bool × ℕ) ℝ :=
  ∑ a ∈ Finset.range (k + 1), C ((-1 : ℝ) ^ (k - a)) * X (true, a) * X (false, k - a)

def gens (p q : ℕ) : Set (MvPolynomial (Bool × ℕ) ℝ) :=
  {f | (∃ k, 1 ≤ k ∧ f = rel k) ∨ (∃ b, f = X (b, 0) - 1) ∨ (∃ k, p < k ∧ f = X (true, k)) ∨
    (∃ k, q < k ∧ f = X (false, k))}

def J (p q : ℕ) : Ideal (MvPolynomial (Bool × ℕ) ℝ) := Ideal.span (gens p q)

def basis (p q : ℕ) : Set (MvPolynomial (Bool × ℕ) ℝ) :=
  {f | (∃ d, wt d < p * q ∧ f = monomial d 1) ∨ f = X (true, p) ^ q}

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def renVar {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (y : Bool × ℕ) : (E →+* ℂ) × ℕ :=
  (if y.1 then τ.1 else conjEmb τ.1, y.2)

def ren {H : Host E} (τ : GlobalTheory.AllWt.Psi H) :
    MvPolynomial (Bool × ℕ) ℝ →ₐ[ℝ] MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  rename (renVar τ)

end GlobalTheory.GrassTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsRationalCombinationFrame
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeriodFrame

theorem frame_hermForm_sum_left {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : Fin n → ℂ)
    (E : Fin n → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
  unfold hermForm
  rw [sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul]

theorem frame_hermForm_sum_right {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : Fin n → ℂ)
    (E : Fin n → Fin g → ℂ) (z : Fin g → ℂ) :
    hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
  have hs : star (∑ i, c i • E i) = ∑ i, star (c i) • star (E i) := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext k
    simp [mul_comm]
  simp only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem frame_col {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) (i : Fin g) :
    (fun k => combMat l ε k i) = ∑ m, (ε i m : ℂ) • l m := by
  funext k
  simp [combMat, Finset.sum_apply]

theorem frame_im_hermForm {g r : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ)
    (l : Fin r → Fin g → ℂ) (hM : ∀ i j, (hermForm Hm (l i) (l j)).im = M i j)
    (A B : Matrix (Fin g) (Fin r) ℚ) (i k : Fin g) :
    (hermForm Hm (fun x => combMat l A x i) (fun x => combMat l B x k)).im
      = (((A * M.map (Int.cast : ℤ → ℚ) * Bᵀ) i k : ℚ) : ℝ) := by
  rw [frame_col, frame_col, frame_hermForm_sum_left]
  simp only [frame_hermForm_sum_right, Finset.mul_sum, Complex.im_sum]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  push_cast
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  simp [Complex.mul_im, hM]
  ring

theorem riemann_relations_frame : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), 0 < D → Hm.IsHermitian → (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ l → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ε * M.map (Int.cast : ℤ → ℚ) * εᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * εᵀ = 1 → IsUnit (GlobalTheory.PeriodFrame.combMat l ε).det ∧ ((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).IsSymm ∧ (((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).PosDef ∧ (GlobalTheory.PeriodFrame.combMat l ε)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat l ε)ᵀᴴ = ((D : ℝ) : ℂ) • ((((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).map Complex.ofReal)⁻¹ := by
  intro g r Hm M l ε φ D hD hH hpos _hl hM hεε hφφ hφε
  set P := combMat l ε with hP
  set Q := combMat l φ with hQ
  set E : Fin g → Fin g → ℂ := fun i k => P k i with hE
  set F : Fin g → Fin g → ℂ := fun j k => Q k j with hF
  have hEE : ∀ i j, (hermForm Hm (E i) (E j)).im = 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM ε ε i j
    rw [hεε] at h
    simpa using h
  have hFF : ∀ i j, (hermForm Hm (F i) (F j)).im = 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM φ φ i j
    rw [hφφ] at h
    simpa using h
  have hFE : ∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM φ ε i j
    rw [hφε] at h
    change (hermForm Hm (F i) (E j)).im = _ at h
    rw [h]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hind : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have h1 : hermForm Hm (F j) (∑ i, ((a i : ℝ) : ℂ) • E i) = 0 := by
      have hs : (∑ i, ((a i : ℝ) : ℂ) • E i) = ∑ i, a i • E i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ext k
        simp
      rw [hs, ha]
      simp [hermForm]
    rw [frame_hermForm_sum_right] at h1
    have h2 := congrArg Complex.im h1
    simpa [Complex.im_sum, Complex.mul_im, hFE] using h2
  have hdet : P.det ≠ 0 := by
    have h := GlobalTheory.det_ne_zero_of_real_indep_isotropic g Hm E hpos hind hEE
    exact h
  have hU : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  set τ := P⁻¹ * Q with hτ
  have hPτ : P * τ = Q := by
    rw [hτ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have hFτ : ∀ j, F j = ∑ i, τ i j • E i := by
    intro j
    funext k
    have h := congrFun (congrFun hPτ k) j
    simp only [Matrix.mul_apply] at h
    simp only [hF, hE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨hposτ, hsymτ⟩ := GlobalTheory.riemann_relations_period_matrix g g Hm E F τ hH hpos hFτ hEE hFE
  have hτs : ∀ i j, τ i j = τ j i := fun i j => by
    have h := hsymτ i j
    rw [hFF] at h
    simpa [sub_eq_zero] using h
  set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hY
  set a : Matrix (Fin g) (Fin g) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hEE])
  have hYA : Y * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hFτ j, frame_hermForm_sum_left] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero, zero_add] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hY, Matrix.map_apply]
    rw [hτs j i]
  have hTim : ((D : ℂ) • τ).map Complex.im = (D : ℝ) • Y := by
    ext i j
    simp [hY]
  have hTre : (((D : ℂ) • τ).map Complex.im).map Complex.ofReal = (D : ℂ) • Y.map Complex.ofReal := by
    rw [hTim]
    ext i j
    simp
  have hYAc : Y.map Complex.ofReal * a.map Complex.ofReal = 1 := by
    ext i k
    have h := congrFun (congrFun hYA i) k
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hinv : ((((D : ℂ) • τ).map Complex.im).map Complex.ofReal)⁻¹ = (D : ℂ)⁻¹ • a.map Complex.ofReal := by
    apply Matrix.inv_eq_right_inv
    rw [hTre, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hDne, one_smul, hYAc]
  refine ⟨hU, ?_, ?_, ?_⟩
  · show ((D : ℂ) • τ)ᵀ = (D : ℂ) • τ
    ext i j
    simp only [Matrix.transpose_apply, Matrix.smul_apply]
    rw [hτs j i]
  · rw [Matrix.posDef_iff_dotProduct_mulVec, hTim]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, star_trivial, hY, Matrix.map_apply]
      rw [hτs j i]
    · have e : star x ⬝ᵥ (((D : ℝ) • Y) *ᵥ x) = (D : ℝ) * (∑ i, ∑ j, (x i : ℂ) * τ i j * (x j : ℂ)).im := by
        simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Complex.im_sum,
          Finset.mul_sum, hY, Matrix.map_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [Complex.mul_im]
        ring
      rw [e]
      exact mul_pos (by exact_mod_cast hD) (hposτ x hx)
  · rw [hinv, smul_smul, Complex.ofReal_natCast, mul_inv_cancel₀ hDne, one_smul]
    ext i j
    rw [Matrix.map_apply, ← hAr i j]
    simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.conjTranspose_apply, Pi.star_apply, Matrix.map_apply, hE, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    ring

end GlobalTheory.PeriodFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowDepthOfPrimitive
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowDepthTrue


set_option maxHeartbeats 1000000 in
theorem rowDepth_rowRepR : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → D.host.F = maximalRealSubfield D.host.E →
    GlobalTheory.HeightCounting.RowDepth D (fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) := by
  intro hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHo hF σ k v
  obtain ⟨s, hs⟩ := GlobalTheory.FixedPlaceOverType.exists_splitPlace_w_plGw D k v
  obtain ⟨τ, hτ⟩ := GlobalTheory.RowLocalRows2.finTyp_rows_exists_isLocS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHo hF σ s
  have hβ := hP.char.base.lev.βY 0 Y.hm
  obtain ⟨h, hA⟩ := GlobalTheory.RowLevelSplit.lemA_pf
    (GlobalTheory.RowLevelSplit.stdFrame_splitPlace_entries_off_place GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one GlobalTheory.ConjLt.frame_mat_sub_one_lt GlobalTheory.SplitFrameW.main
      GlobalTheory.PlaceOverSplit.eq_or_eq_cP) D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) _ _ Y.stdPsi.1 hβ s
  have hh : ∀ (b : Bool) (κ : Formalism.AUTREP.GAf D.host.E D.R.r), TrivOutside {s.v} κ →
      h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) →
      Y.PY.ψ κ ∈ levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) ∧
        levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) (Y.PY.ψ κ) = 1 := by
    intro b κ hκ hk
    classical
    exact GlobalTheory.RowLevelSplit.lemB_pf D (Yc D 0) (R.βY 0) _ (_ ∪ _) (Y.PY.ψ κ) Finset.subset_union_left
      Finset.subset_union_right (Y.PY.into κ) (hA κ hκ hk _)
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.RowFix.exists_fixed_rowRep D (Yc D 0) D.R.r _ R.θ Y.PY (R.MY 0) _ _ _ (Y.eFT σ)
    (fun κ => TrivOutside {s.v} κ ∧
      h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r))
    (fun b κ hκ => hh b κ hκ.1 hκ.2)
  exact ⟨s, τ, hs, hτ, GlobalTheory.RowLevelSplitData.fixed_ne_bot_of_fixed_vector_conj D.host.E D.R.r _ s τ h hτ f hfS hf0
    (fun κ h1 h2 => hfix κ ⟨h1, h2⟩)⟩


open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up in
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl in
theorem stepW_of_ev {Q : Ctx → Prop} (h : Ev Q) (p : WP) : StepW p fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)



end GlobalTheory.RowDepthTrue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellsFiniteCoverUpToAutStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_cells_finite_cover_up_to_aut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar ψ' γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  first | exact @GlobalTheory.PolFan.isStarOf_finite_cover | exact GlobalTheory.PolFan.isStarOf_finite_cover | (intros; apply GlobalTheory.PolFan.isStarOf_finite_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMulStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_linearSubst_eq_absDet_sq_mul : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ), topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) P) = J.det * starRingEnd ℂ J.det * topCoeff P := by
  first | exact @GlobalTheory.GoodMetric.topCoeff_subst_conj | exact GlobalTheory.GoodMetric.topCoeff_subst_conj | (intros; apply GlobalTheory.GoodMetric.topCoeff_subst_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceLocalIndex
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.LocEx

theorem exists_loc_of_thetaT {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M) {v : D.what₂.places.Pl} (hv : TwistedAt D v) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hne : ∃ f, D.what₂.thetaT (D.what₂.muTw v) j f ≠ 0) :
    ∃ i : D.nd.Loc, D.nd.w i = v ∧ D.nd.j i = j := by
  obtain ⟨f, hf⟩ := hne
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)
  have hidx : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h3 := (D.what₂.jMt_basis (D.what₂.muTw v) j b).2
    rw [Set.range_eq_empty, Submodule.span_empty] at h3
    exact hf ((Submodule.mem_bot ℂ).1 (h3 ▸ Submodule.mem_top))
  obtain ⟨k⟩ := hidx
  haveI : Nontrivial (T.B.V j v) := ⟨⟨_, 0, (T.B.iV_basis j v b).1.ne_zero k⟩⟩
  haveI : Nontrivial (Formalism.L2.heckeAlg T.B j v) := inferInstance
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (Formalism.L2.heckeAlg T.B j v)
  obtain ⟨i, hi, -⟩ := T.mx_all j v h1 h2 hv I hI
  obtain ⟨ej, ew⟩ := (D.nd.locs_mem _ _ _).1 hi
  exact ⟨i, ew, ej⟩

theorem thetaT_ne_of_lamTr {D : D7} {μ : D.what₂.Tup} {j : ℕ} {σ : D.what₂.FT} (hpos : 0 < DV.lamTr D μ j σ) :
    ∃ f ∈ D.what₂.isot j σ, D.what₂.thetaT μ j f ≠ 0 := by
  by_contra h
  push_neg at h
  have hT : D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ ((D.what₂.isot j σ).starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) = 0 := by
    ext y
    simp [h _ ((D.what₂.isot j σ).starProjection_apply_mem y)]
  unfold DV.lamTr at hpos
  rw [hT, map_zero, Complex.zero_re, zero_div] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.HeightCounting.Up.LocEx

end
end

