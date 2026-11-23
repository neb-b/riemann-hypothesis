module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0635
public import Formalism.DegreeFormula.PointDegree.PowSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0241
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralEqZeroOfMemRelIdeal
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop.RelVanish

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rho_eq_flagMap (H : Host E) (Dw : Datum H) : rho H Dw = GlobalTheory.Schubert.flagMap Dw := by
  unfold rho GlobalTheory.Schubert.flagMap
  congr 1

noncomputable def numLin (H : Host E) (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ :=
  GlobalTheory.Schubert.flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) ∘ₗ (GlobalTheory.Schubert.flagMap Dw).toLinearMap ∘ₗ
    LinearMap.mulRight ℝ (rootDiscr Dw.mult) ∘ₗ (chernRoots Dw.mult).toLinearMap

theorem numLin_apply (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    numLin H Dw Q = Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (GlobalTheory.Schubert.flagMap Dw (chernRoots Dw.mult Q * rootDiscr Dw.mult)) := by
  simp [numLin, GlobalTheory.Schubert.flagLin_apply]

theorem numLin_of_chernRoots_eq_zero (H : Host E) (Dw : Datum H) (g : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)
    (hg : chernRoots Dw.mult g = 0) (a : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : numLin H Dw (g * a) = 0 := by
  rw [numLin_apply, map_mul (chernRoots Dw.mult), hg, zero_mul, zero_mul, map_zero, ← GlobalTheory.Schubert.flagLin_apply, map_zero]

theorem chernRoots_X_zero_sub_one (H : Host E) (Dw : Datum H) (τ : E →+* ℂ) :
    chernRoots Dw.mult (X (τ, 0) - 1 : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) = 0 := by
  simp [chernRoots, esymm_zero]

theorem chernRoots_X_of_lt (H : Host E) (Dw : Datum H) (τ : E →+* ℂ) (k : ℕ) (hk : Dw.mult τ < k) :
    chernRoots Dw.mult (X (τ, k) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) = 0 := by
  have h0 : esymm (Fin (Dw.mult τ)) ℝ k = 0 := by
    unfold esymm
    rw [Finset.powersetCard_eq_empty.mpr (by simpa using hk)]
    simp
  simp [chernRoots, h0]

theorem numLin_relPoly (H : Host E) (Dw : Datum H) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) (hk : 1 ≤ k)
    (a : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : numLin H Dw (GlobalTheory.PointChern.relPoly τ k * a) = 0 := by
  rw [numLin_apply, map_mul (chernRoots Dw.mult), mul_assoc, map_mul, GlobalTheory.Schubert.RelKill.flagMap_relPoly]
  exact Formalism.DegreeFormula.degreeEsymmMulEqZero _ _ τ k _ hk

theorem numLin_mul_eq_zero (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)
    (hQ : Q ∈ relIdeal H Dw) : ∀ a, numLin H Dw (Q * a) = 0 := by
  unfold relIdeal at hQ
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    intro a
    rcases hx with (⟨τ, rfl⟩ | ⟨τ, k, hk, rfl⟩) | ⟨τ, k, hk, rfl⟩
    · exact numLin_of_chernRoots_eq_zero H Dw _ (chernRoots_X_zero_sub_one H Dw τ) a
    · exact numLin_of_chernRoots_eq_zero H Dw _ (chernRoots_X_of_lt H Dw τ k hk) a
    · exact numLin_relPoly H Dw τ k hk a
  | zero => intro a; simp
  | add x y _ _ hx hy => intro a; rw [add_mul, map_add (f := _), hx, hy, add_zero]
  | smul r x _ hx => intro a; rw [smul_eq_mul, mul_assoc, mul_comm r, mul_assoc]; exact hx _

end GlobalTheory.GrassTop.RelVanish

namespace GlobalTheory.GrassTop

theorem intGr_eq_zero_of_mem_relIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Q ∈ relIdeal H Dw → intGr H Dw Q = 0 := by
  intro E _ _ _ H Dw Q hQ
  have h := RelVanish.numLin_mul_eq_zero H Dw Q hQ 1
  rw [mul_one, RelVanish.numLin_apply, ← RelVanish.rho_eq_flagMap] at h
  rw [intGr, h, zero_div]

end GlobalTheory.GrassTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeGramLocalModelAlgebraicChartHolomorphic
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

theorem lieGram_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ ix : Fin X.dim ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q, ∃ (φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim) (g : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ) (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧ AnalyticAt ℂ φ (c'.e y) ∧ (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) (c'.e y)) ∧ (∀ τ, IsUnit (g (c'.e y) τ).det) ∧ InDom (coordOf ix (φ (c'.e y))) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∀ τ, lieGram e U hj f₀ A₀ A (c'.e.symm w) τ = (cc τ : ℂ) • (g w τ * modelGram H Dw (coordOf ix (φ w)) τ * (g w τ)ᴴ) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hc' A hA ix
  obtain ⟨hoi, -, hT⟩ := hL
  obtain ⟨k', s, hs, hev⟩ := _root_.GlobalTheory.LieBase.exists_analytic_frame_lift E H Dw l Xo c O β Y T F e σ U hσ hU X j hj hoi y hy c' hc'
  obtain ⟨K, hK, hKu, hKev⟩ :=
    _root_.GlobalTheory.FrameLift.exists_holomorphic_frame_coords E H Dw l Xo c O β Y T F e σ U hσ hU X j f₀ Eb A₀ hj hoi hT y hy c' hc' A hA k' s hs hev
  obtain ⟨G, z, cc, hcc, hG⟩ := _root_.GlobalTheory.HodgeGramGen.hodge_gram_frame E H Dw l Xo c O β T.Z σ U hσ hU k'
  obtain ⟨hs0, -⟩ := hev.self_of_nhds
  obtain ⟨hGa, hza, hGu, hzD, -⟩ := hG (s (c'.e y)) hs0
  let φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun w =>
    (EuclideanSpace.equiv (Fin X.dim) ℂ).symm (fun i => z (s w) (ix i).1 (ix i).2.1 (ix i).2.2)
  have hco : ∀ w, coordOf ix (φ w) = z (s w) := fun w => by
    funext τ a b
    simp [φ, coordOf]
  refine ⟨φ, fun w τ => (K w τ)ᵀ * G (s w) τ, cc, hcc, ?_, ?_, ?_, ?_, ?_⟩
  · refine (EuclideanSpace.equiv (Fin X.dim) ℂ).symm.analyticAt _ |>.comp ?_
    refine analyticAt_pi_iff.2 fun i => ?_
    exact (hza (ix i).1 (ix i).2.1 (ix i).2.2).comp hs
  · intro τ a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.analyticAt_fun_sum Finset.univ (fun i _ => (hK τ i a).mul ((hGa τ i b).comp hs))
  · intro τ
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact (hKu τ).mul (hGu τ)
  · rw [hco]
    exact hzD
  · filter_upwards [hKev, hev] with w ⟨⟨g0, hg0⟩, hKw⟩ ⟨hsw, _⟩ τ
    have hex : ∃ g, FrameAt e f₀ A₀ A (c'.e.symm w) g := ⟨g0, hg0⟩
    rw [lieGram, dite_eq_left hex]
    show ((hodgeMet T.Z U).gram _ hex.choose τ)ᵀ = _
    rw [hKw hsw _ hex.choose_spec, Matrix.transpose_mul, Matrix.transpose_mul, (hG (s w) hsw).2.2.2.2 τ, hco]
    have hKt : ((K w τ)ᴴ)ᵀ = ((K w τ)ᵀ)ᴴ := by ext; simp
    rw [hKt]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end GlobalTheory.PointChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationGramLocalHolomorphic
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix

namespace GlobalTheory.HodgeUnifFrame

theorem transpose_hermitian_gram_submatrix_bijection {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : n → m)
    (he : Function.Bijective e) (K G : Matrix m m ℂ) (W P : Matrix n n ℂ) (c : ℂ)
    (hG : G.submatrix e e = c • (Wᴴ * P * W)) :
    ((Kᴴ * G * K)ᵀ).submatrix e e = c • ((W * K.submatrix e e)ᵀ * Pᵀ * ((W * K.submatrix e e)ᵀ)ᴴ) := by
  have h1 : (Kᴴ * G * K).submatrix e e = (K.submatrix e e)ᴴ * G.submatrix e e * K.submatrix e e := by
    rw [Matrix.submatrix_mul _ _ _ e _ he, Matrix.submatrix_mul _ _ _ e _ he, Matrix.conjTranspose_submatrix]
  have h2 : ((Kᴴ * G * K)ᵀ).submatrix e e = ((Kᴴ * G * K).submatrix e e)ᵀ := by ext; rfl
  rw [h2, h1, hG]
  have h3 : ((W * K.submatrix e e)ᵀ)ᴴ = ((W * K.submatrix e e)ᴴ)ᵀ := by ext; rfl
  rw [h3]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

theorem lieGram_unif_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), ∀ (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U), ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ c : ℝ, 0 < c ∧ ∃ g : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin Dw.p) (Fin Dw.p) ℂ, (∀ i j, AnalyticAt ℂ (fun w => g w i j) v) ∧ IsUnit (g v).det ∧ ∀ᶠ w in nhds v, (lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) τ.1).submatrix (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) = (c : ℂ) • (g w * ((hP (unflat (GlobalTheory.UnifDens.flatL h w) (GlobalTheory.HodgeGenUnf.letter hσ hU k τ)))⁻¹)ᵀ * (g w)ᴴ) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA τ
  obtain ⟨hoi, -, hT⟩ := hL
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  obtain ⟨s, hsa, hWa, hsev⟩ := _root_.GlobalTheory.FrameLift.exists_analytic_section E Dw.p Dw.q X.dim (U.X k) hp h v hv
  obtain ⟨K, hKa, hKu, hKev⟩ := _root_.GlobalTheory.UnifFrameChange.exists_holomorphic_frame_change E H Dw l Xo c O β Y T F e σ U hσ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v hv A hA s hsa hsev
  have hex := _root_.GlobalTheory.UnifFrame.eventually_frameAt_unif E H Dw l Xo c O β Y T F e σ U hσ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v hv A hA
  set τ' := GlobalTheory.HodgeGenUnf.letter hσ hU k τ with hτ'
  set ec : Fin Dw.p → Fin (Dw.mult τ.1) := Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm with hec
  have he : Function.Bijective ec := (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm).bijective
  refine ⟨2 * Real.pi, Real.two_pi_pos,
    fun w => (coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ' * (K w τ.1).submatrix ec ec)ᵀ, ?_, ?_, ?_⟩
  · intro a b
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.submatrix_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ => (hWa τ' b i).mul (hKa τ.1 (ec i) (ec a))
  · obtain ⟨hs0, -⟩ := hsev.self_of_nhds
    rw [Matrix.det_transpose, Matrix.det_mul]
    refine (isUnit_coW (U.X k) _ hp hs0 τ').mul ?_
    have : (K v τ.1).submatrix ec ec = (K v τ.1).submatrix (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm)
      (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) := rfl
    rw [this, Matrix.det_submatrix_equiv_self]
    exact hKu τ.1
  · filter_upwards [hsev, hKev, hex] with w ⟨hs, hflat⟩ hKw ⟨g0, hg0⟩
    have hexw : ∃ g, FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g := ⟨g0, hg0⟩
    rw [lieGram, dite_eq_left hexw]
    show (((hodgeMet T.Z U).gram _ hexw.choose τ.1)ᵀ).submatrix ec ec = _
    rw [hKw hs _ hexw.choose_spec (hodgeMet T.Z U) τ.1]
    have hG := GlobalTheory.HodgeGenUnf.hodgeMet_gram_frame T.Z hσ hU k ⟨s w, hs⟩ τ τ' rfl (Nat.le_add_right Dw.p Dw.q)
    have hz : domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (s w) τ' = unflat (GlobalTheory.UnifDens.flatL h w) τ' := by
      rw [← hflat]; rfl
    have hG' : ((hodgeMet T.Z U).gram (cxPt T.Z (U.un k ⟨s w, hs⟩)) (cxFrame T.Z (U.un k ⟨s w, hs⟩)) τ.1).submatrix ec ec =
        ((2 * Real.pi : ℝ) : ℂ) • ((coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ')ᴴ *
          (hP (unflat (GlobalTheory.UnifDens.flatL h w) τ'))⁻¹ * coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ') := by
      rw [← hz]; exact hG
    rw [transpose_hermitian_gram_submatrix_bijection ec he _ _ _ _ _ hG']

end GlobalTheory.HodgeUnifFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyFanOfStarSubdivisionCells
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarFan

theorem homog_of_cover : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) → ∀ B ∈ psdCone (bar := bar) (X := X), ∀ t : ℝ, 0 ≤ t → evalR φ (t • B) = t * evalR φ B := by
  intro O _ bar φ X _ _ _ hcov B hB t ht
  obtain ⟨e, m, γ, c, hγ, hc, he⟩ := hcov B hB
  have key : ∀ (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (c₀ : Fin m → ℝ), (∀ i, 0 ≤ c₀ i) →
      (∀ a b, B₀ (e a) (e b) = ∑ i, c₀ i * (γ i a b : ℝ)) → evalR φ B₀ = ∑ i, c₀ i * φ.evalZ (γ i) :=
    fun B₀ c₀ hc₀ hB₀ => hγ.linear.eval_eq_sum (r := e.toLinearMap) e.surjective hc₀ hB₀
  have hv : ∀ a b, B (e a) (e b) = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    have := LinearMap.congr_fun₂ he a b
    simpa [LinearMap.sum_apply] using this
  rw [key B c hc hv, key (t • B) (fun i => t * c i) (fun i => mul_nonneg ht (hc i)) fun a b => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem isPolyFan_star : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, ψ'.evalZ β = n) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ψ'.evalZ β) → IsPolyFan H.bar q ψ' := by
  intro E _ _ _ H q ψ w ψ' hψ hw hst hint hpos X _ _ _ _ hX
  obtain ⟨S, hS, hcov⟩ := GlobalTheory.T.starSubdivision_cells_finite_cover_up_to_aut E H q ψ w ψ' hψ hw hst X hX
  have hcov' : ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      IsCell H.bar ψ' γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := fun B hB => by
    obtain ⟨e, m, γ, c, h1, -, h3, h4⟩ := hcov B hB
    exact ⟨e, m, γ, c, h1, h3, h4⟩
  exact
    { homog := homog_of_cover (𝓞 E) H.bar ψ' X hcov'
      superadd := GlobalTheory.T.superadditive_of_cells_cover_cone (𝓞 E) H.bar ψ' X hcov'
      integral := hint X hX
      pos := hpos X hX
      finite := ⟨S, hS, hcov⟩ }

end GlobalTheory.PolFan.StarFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRhoOfRowOfFrobeniusEigenvalues
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.TripRho

open GlobalTheory.TwistedSelmerCompare GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions Formalism.L2.NR


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isRhoOfRow_of_frobEig : ∀ (D : D7) (Rw : RowSide D) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT), GlobalTheory.HeightCounting.RhoSpec D Rw rowS → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (a : D.nd.Loc) (σ : D.what₂.FT) (s : D.ntw.Sig (D.ntw.twOf a)), GlobalTheory.RowTriple.ReadTw D a → D.ntw.side _ s = D.ntw.twSide a → D.ntw.jS _ s = D.nd.j a → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsGoodRow D a σ → (∀ w, IsSplitPl D.host w → D.naut.locW a σ w = Rw.locR σ w) → (∀ᶠ P in Filter.cofinite, IsSplitPl D.host P → D.naut.frobEig (Rw.locR (rowS _ s) P) = D.naut.frobEig (Rw.locR σ P)) → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsRhoOfRow D a σ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s) := by
  intro D Rw rowS hRho hGP a σ s hRT hs hj hg hloc hfe
  obtain ⟨hiso, hgood, hspec⟩ := hRho (D.ntw.twOf a) s
  have hjr := D.nd.j_range a
  have hσs : D.what₂.isot (D.nd.j a) (rowS _ s) ≠ ⊥ := by rw [← hj]; exact hiso
  obtain ⟨π', hc', hr', hl', -, -, -⟩ := hGP (D.nd.j a) hjr.1 hjr.2 (rowS _ s) hσs hgood
  obtain ⟨π'', -, -, hl'', -, -, -⟩ := hGP (D.nd.j a) hjr.1 hjr.2 σ hg.1 hg.2
  obtain ⟨φ, ι, h1, h2, h3⟩ := hRT
  have h2' : ∀ x : ↥D.LL0, ι (φ ((if D.ntw.side (D.ntw.twOf a) s then D.ntw.emb0 (D.ntw.twOf a)
      else D.ntw.emb0b (D.ntw.twOf a)) x)) = embLL0 D x := by
    intro x; rw [hs]; exact h2 x
  obtain ⟨-, hss, hev⟩ := hspec π' hc' hr' hl' φ ι h1 h2'
  refine ⟨?_, ?_⟩
  · have : CharZero (FractionRing (D.nd.O a)) :=
      ((D.nd.embK a).charZero_iff (D.nd.embK a).injective).1 inferInstance
    have : CharZero (FractionRing (D.ntw.O0 (D.ntw.twOf a))) :=
      ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
    have e1 : mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s) =
        mapRep (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a)) (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      exact (fracMap_alg _ (twO_inj D.ntw a) _).symm
    have e2 : mapRep (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))))
        (D.ntw.rhoS _ s) = mapRep φ (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      rfl
    rw [e1, isSSRep_map_iff]
    rw [e2, isSSRep_map_iff] at hss
    exact hss
  · filter_upwards [hev, D.naut.locG_unr_ae π', D.naut.locG_unr_ae π'', hfe] with w hw hu' hu'' hf hsp
    intro B g hB hg'
    have hR : Rw.locR (rowS _ s) w = Rw.locR σ w := by
      have u1 : D.naut.unr (Rw.locR (rowS _ s) w) := by rw [← hl' w hsp]; exact hu'
      have u2 : D.naut.unr (Rw.locR σ w) := by rw [← hl'' w hsp]; exact hu''
      rw [D.naut.unr_eq_lpUnr _ u1, D.naut.unr_eq_lpUnr _ u2, hf hsp]
    have hpar : D.naut.locG (D.naut.tw π' D.naut.etaTinv) w =
        D.naut.lpChar (D.naut.locW a σ w) (D.naut.locG D.naut.etaTinv w) := by
      rw [D.naut.locG_tw, hl' w hsp, hR, hloc w hsp]
    have hcp := hw B g hB hg'
    rw [hpar] at hcp
    refine Eq.trans ?_ hcp
    have hcomp : (iotaO D.nd D.naut a).comp (D.ntw.twist₂ a) =
        ι.toRingHom.comp (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))) := by
      ext y
      exact (h3 y).symm
    have e1 : ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) =
        ((D.ntw.rhoS (D.ntw.twOf a) s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).map (D.ntw.twist₂ a) := rfl
    have e2 : ((mapRep (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))))
          (D.ntw.rhoS (D.ntw.twOf a) s) g : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((D.ntw.rhoS (D.ntw.twOf a) s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).map
            (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))) := rfl
    rw [e1, Matrix.charpoly_map, Polynomial.map_map, hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map, ← e2]

end GlobalTheory.TripRho

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetRationalCombinationFrameClosedBall
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFrame

theorem combMat_mul_left {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) :
    combMat l (b * ε) = combMat l ε * bᵀ.map (Rat.cast : ℚ → ℂ) := by
  have h := combMat_add_mul l ε 0 bᵀ
  have h0 : combMat l (0 : Matrix (Fin g) (Fin r) ℚ) = 0 := by
    ext k j; simp [combMat]
  rwa [h0, zero_add, zero_add, Matrix.transpose_transpose] at h

theorem combMat_add {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) :
    combMat l (ε + φ) = combMat l ε + combMat l φ := by
  ext k j
  simp [combMat, add_mul, Finset.sum_add_distrib]

theorem isUnit_det_combMat_on_ball : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ) (rk D : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ → (∀ m (j : Fin g), j.val < rk → dl m j = 0) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 1)) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det := by
  intro n a g r₀ r ha ζ lam c α φ gm dl rk D τ₀ B hD hζ hstd hlam hc hdl hP hτ hB hper z hz
  choose I hI using hstd
  let sel : Matrix (Fin g) (Fin r₀) ℚ := Matrix.of fun j i => if i = I j then 1 else 0
  let Dl : Matrix (Fin g) (Fin g) ℂ := (sel * dl)ᵀ.map (Rat.cast : ℚ → ℂ)
  let G : Matrix (Fin g) (Fin g) ℂ := (sel * gm)ᵀ.map (Rat.cast : ℚ → ℂ)
  have hsel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, combMat (ζ z) sel = 1 := by
    intro z hz
    ext k j
    have h1 : combMat (ζ z) sel k j = ζ z (I j) k := by
      simp only [combMat, sel, Matrix.of_apply]
      rw [Finset.sum_eq_single (I j)]
      · simp
      · intro i _ hi; simp [hi]
      · simp
    rw [h1, hI j z hz, Matrix.one_apply, Pi.single_apply]
  have hBD : ∀ k, (B k).map (Int.cast : ℤ → ℂ) * Dl = 0 := by
    intro k
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply, Dl, Matrix.transpose_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < rk
    · simp [hdl _ l hl]
    · simp [hB k i l (Or.inr (not_lt.mp hl))]
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPc : ContinuousOn (fun z => combMat (ζ z) α) (Metric.ball (0 : Fin n → ℂ) 1) := by
    refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun i => ?_
    simp only [combMat, Matrix.of_apply]
    refine continuousOn_finsetSum _ fun m _ => continuousOn_const.mul ?_
    exact continuousOn_pi.1 (continuousOn_pi.1 hζ.continuousOn m) k
  have hτc : ContinuousOn τ₀ (Metric.ball (0 : Fin n → ℂ) 1) :=
    continuousOn_pi.2 fun k => continuousOn_pi.2 fun i => (hτ k i).continuousOn
  have hQ : Continuous (fun p : Matrix (Fin g) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ =>
      p.1 * (G + (D : ℂ)⁻¹ • (p.2 * Dl))) := by fun_prop
  have hQc : ContinuousOn (fun z => combMat (ζ z) α * (G + (D : ℂ)⁻¹ • (τ₀ z * Dl)))
      (Metric.ball (0 : Fin n → ℂ) 1) := by
    have h := hQ.comp_continuousOn (hPc.prodMk hτc)
    simpa only [Function.comp_def] using h
  have key := GlobalTheory.eq_on_ball_of_eq_on_logExp_image n a 1 (Matrix (Fin g) (Fin g) ℂ)
    (fun z => combMat (ζ z) α * (G + (D : ℂ)⁻¹ • (τ₀ z * Dl))) (fun _ => 1) le_rfl
    hQc continuousOn_const (by
      intro s hs hb
      have h1 := hsel _ hb
      rw [combMat_comb _ _ c sel (hlam s hs), hc, Matrix.mul_add, ← Matrix.mul_assoc sel gm, ← Matrix.mul_assoc sel dl,
        combMat_add, combMat_mul_left, combMat_mul_left, ← combMat_comb _ _ c α (hlam s hs)] at h1
      have h2 := congrArg (fun T => T * Dl) (hper s hs hb)
      simp only [perTau, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul, hBD, smul_zero, Finset.sum_const_zero,
        add_zero] at h2
      rw [← h2, smul_smul, inv_mul_cancel₀ hDc, one_smul, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hP s hs), Matrix.one_mul]
      exact h1) z hz
  exact Matrix.isUnit_det_of_right_inverse key

end GlobalTheory.PeriodFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormPiecesInEveryCellCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan.OrbMark

theorem inRCone_pullAdd_of_isCell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)),
  IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell H.bar φ δ₀ → ∀ t : Fin m₀ → ℝ, (∀ i, 0 ≤ t i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] (π : X₀ →ₗ[𝓞 E] Y), Function.Surjective π → ∀ (τ : 𝓞 E ≃+* 𝓞 E) (f : X →+ Y), τ H.w0 = H.w0 →
    Function.Surjective f → (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y,
    (∀ i, 0 < t i → pull π (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms H.bar X ∧ ∀ y, 0 ≤ pullAdd f (u i) y y) →
  ∀ β : LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (pullAdd f (u i)) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ i, 0 < t i → InRCone δ (pullAdd f (u i)) := by
  intro E _ _ _ H φ htw X₀ _ _ _ m₀ δ₀ h₀ t ht X Y _ _ _ _ _ _ π hπ τ f hτ hf hsm u hu β hβ m δ hδ c hc hβc i hi
  classical
  let S : Finset (Fin m₀) := Finset.univ.filter fun j => 0 < t j
  let s : Fin S.card ↪ Fin m₀ := (S.orderEmbOfFin rfl).toEmbedding
  have hrange : Set.range s = (S : Set (Fin m₀)) := Finset.range_orderEmbOfFin S rfl
  have hs : ∀ j, 0 < t (s j) := fun j => by
    have : s j ∈ (S : Set (Fin m₀)) := hrange ▸ Set.mem_range_self j
    simpa [S] using this
  have hmem : ∀ j, 0 < t j → j ∈ Set.range s := fun j hj => by
    rw [hrange]; simpa [S] using hj
  have h1 : φ.LinearOn (fun j => δ₀ (s j)) := linearOn_comp h₀.linear s
  have e1 : (fun j => δ₀ (s j)) = fun j => pull π (u (s j)) := funext fun j => ((hu _ (hs j)).1).symm
  rw [e1] at h1
  have h2 : φ.LinearOn (fun j => u (s j)) := (linearOn_pull_iff hπ).1 h1
  have h3 : φ.LinearOn (fun j => pullAdd f (u (s j))) := by
    intro a ha
    have hz : ∀ j, φ.evalZ (pullAdd f (u (s j))) = φ.evalZ (u (s j)) := fun j =>
      eval_pull_semilinear_of_isTwInv E H φ htw τ hτ f hf hsm fun x y => ((u (s j) x y : ℤ) : ℝ)
    have := h2 a ha
    simp only [hz]
    rw [← this]
    exact eval_pull_semilinear_of_isTwInv E H φ htw τ hτ f hf hsm fun x y => ∑ j, a j * ((u (s j) x y : ℤ) : ℝ)
  have hsum : toReal β = ∑ j, t (s j) • toReal (pullAdd f (u (s j))) := by
    rw [hβ]
    refine (Fintype.sum_of_injective s s.injective _ _ (fun j hj => ?_) (fun j => rfl)).symm
    have : t j = 0 := le_antisymm (not_lt.1 fun h => hj (hmem j h)) (ht j)
    rw [this, zero_smul]
  obtain ⟨j, rfl⟩ := hmem i hi
  exact GlobalTheory.T.inRealCone_cell_of_linearPiece_through_cellPoint H.bar φ δ (fun j => pullAdd f (u (s j))) hδ (fun j => (hu _ (hs j)).2.1) (fun j => (hu _ (hs j)).2.2) h3
    β c (fun j => t (s j)) hc hs hβc hsum j

end GlobalTheory.PolFan.OrbMark
end
end

