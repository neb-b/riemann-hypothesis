module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0241
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0929
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0931

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormEqMulPointClassValue
section
noncomputable section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def S (H : Host E) (Dw : Datum H) : Submodule ℝ (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) where
  carrier := {P | ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ →
    Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw)}
  zero_mem' := ⟨0, fun Θ _ => by simp⟩
  add_mem' := by
    rintro a b ⟨β, hβ⟩ ⟨β', hβ'⟩
    exact ⟨β + β', fun Θ h => by rw [map_add (f := _), hβ Θ h, hβ' Θ h]; ring⟩
  smul_mem' := by
    rintro c a ⟨β, hβ⟩
    exact ⟨c * β, fun Θ h => by rw [map_smul, hβ Θ h, smul_eq_mul]; ring⟩

theorem prod_update {H : Host E} (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ) (σ : GlobalTheory.AllWt.Psi H)
    (h : MvPolynomial (Bool × ℕ) ℝ) :
    ∏ τ, ren τ (Function.update g σ h τ) = ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem prod_ren_mem (H : Host E) (Dw : Datum H) (s : Finset (GlobalTheory.AllWt.Psi H)) :
    ∀ g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ, (∀ τ ∉ s, g τ ∈ basis Dw.p Dw.q) →
      ∏ τ, ren τ (g τ) ∈ S H Dw := by
  induction s using Finset.induction_on with
  | empty =>
    intro g hg
    exact ⟨_, _root_.GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly E H Dw g fun τ => hg τ (Finset.notMem_empty τ)⟩
  | insert σ s hσ ih =>
    intro g hg
    have key : ∀ h ∈ (J Dw.p Dw.q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis Dw.p Dw.q),
        ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) ∈ S H Dw := by
      intro h hh
      obtain ⟨j, hj, b, hb, rfl⟩ := Submodule.mem_sup.1 hh
      rw [map_add (f := _), add_mul]
      refine add_mem ⟨0, fun Θ hΘ => ?_⟩ ?_
      · rw [zero_mul, mul_comm]
        exact _root_.GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies E H Dw Θ hΘ σ j hj _
      · clear hh
        induction hb using Submodule.span_induction with
        | mem b hb =>
          rw [← prod_update]
          refine ih _ fun τ hτ => ?_
          by_cases e : τ = σ
          · subst e; rw [Function.update_self]; exact hb
          · rw [Function.update_of_ne e]; exact hg τ (by simp [e, hτ])
        | zero => simp
        | add x y _ _ hx hy => rw [map_add (f := _), add_mul]; exact add_mem hx hy
        | smul c x _ hx => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ c hx
    have := key (g σ) (_root_.GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top _ _ _)
    rwa [← prod_update, Function.update_eq_self] at this

theorem var_eq {H : Host E} (x : (E →+* ℂ) × ℕ) : ∃ σ : GlobalTheory.AllWt.Psi H, ∃ y, x = renVar σ y := by
  by_cases h : x.1 (H.rt : E) = H.rt0
  · exact ⟨⟨x.1, h⟩, (true, x.2), by simp [renVar]⟩
  · refine ⟨⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩, (false, x.2), ?_⟩
    simp [renVar, GlobalTheory.AllWt.conjEmb_conjEmb]

theorem mul_prod_ren_mem (H : Host E) (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    ∀ g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ, P * ∏ τ, ren τ (g τ) ∈ S H Dw := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro g
    rw [C_mul']
    exact Submodule.smul_mem _ a (prod_ren_mem H Dw Finset.univ g (by simp))
  | add a b ha hb => intro g; rw [add_mul]; exact add_mem (ha g) (hb g)
  | mul_X P x ih =>
    intro g
    obtain ⟨σ, y, rfl⟩ := var_eq (H := H) x
    have e : X (renVar σ y) * ∏ τ, ren τ (g τ) = ∏ τ, ren τ (Function.update g σ (X y * g σ) τ) := by
      rw [prod_update, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), map_mul, ren, rename_X]
      ring
    rw [mul_assoc, e]
    exact ih _

end GlobalTheory.GrassTop

theorem GlobalTheory.GrassTop.span_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ,
      GlobalTheory.Schubert.admitted H Dw Θ → Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  intro E _ _ _ H Dw P
  have := GlobalTheory.GrassTop.mul_prod_ren_mem H Dw P (fun _ => 1)
  simp only [map_one, Finset.prod_const_one, mul_one] at this
  exact this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainInvariant
section
open Formalism.DegreeFormula

open Matrix Formalism.MJ Formalism.UG GlobalTheory.HodgeDomain GlobalTheory.HermFrame GlobalTheory.TrueCx
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.DomDensInv

variable {ι : Type} [Fintype ι] {p q n : ℕ}

theorem unflat_zero : unflat (0 : ι × Fin p × Fin q → ℂ) = 0 := by
  funext i; ext a b; rfl

theorem exists_upqI {z : ι → Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ DomI ι p q) :
    ∃ g ∈ UpqI ι p q, moebI g 0 = z := by
  have : ∀ τ, ∃ g : GL (Fin p ⊕ Fin q) ℂ, g ∈ Upq p q ∧ moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = z τ := by
    intro τ
    obtain ⟨g, hg, hgz⟩ := GlobalTheory.TrueCx.FrameOnto.exists_moeb_zero (hz τ)
    have hd : g.det ≠ 0 := by
      intro h0
      have h1 := congrArg det hg
      have h2 := congrArg det (Jpq_sq (p := p) (q := q))
      rw [det_mul, h0, mul_zero] at h1
      rw [det_mul, ← h1] at h2
      simp at h2
    exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, upq_iff.2 hg, hgz⟩
  choose g hg hgz using this
  exact ⟨g, fun τ _ => hg τ, funext fun τ => hgz τ⟩

theorem normSq_det_jW {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    Complex.normSq (jW g 0).det = ((hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det).re := by
  have h := hP_moeb hg (zero_mem_hcDom p q)
  have e0 : hP (0 : Matrix (Fin p) (Fin q) ℂ) = 1 := by simp [hP]
  rw [e0, Matrix.mul_one] at h
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_conjTranspose, hP, det_one_sub_mul_comm] at h2
  rw [hQ, ← h2, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem normSq_det_kapQ_inv {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    Complex.normSq ((kapQ g 0)⁻¹).det = ((hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det).re := by
  have h := hQ_moeb hg (zero_mem_hcDom p q)
  have e0 : hQ (0 : Matrix (Fin p) (Fin q) ℂ) = 1 := by simp [hQ]
  rw [e0] at h
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_mul, det_conjTranspose, det_one] at h2
  set d := (kapQ g 0).det
  set H := (hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det
  have h3 : H * ((Complex.normSq d : ℝ) : ℂ) = 1 := by
    rw [← Complex.mul_conj, ← h2, Complex.star_def]; ring
  have h4 : H = ((Complex.normSq d : ℝ) : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left h3
  rw [det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, h4, ← Complex.ofReal_inv, Complex.ofReal_re]

end GlobalTheory.DomDensInv

namespace GlobalTheory.DomDensInv

variable {ι : Type} [Fintype ι] {p q n : ℕ}

theorem det_flat_mul (A : ι → Matrix (Fin p) (Fin p) ℂ) (B : ι → Matrix (Fin q) (Fin q) ℂ)
    (L : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ))
    (hL : ∀ x, L x = flat (fun τ => A τ * unflat x τ * B τ)) :
    LinearMap.det L = ∏ τ, (A τ).det ^ q * (B τ).det ^ p := by
  let E : (ι × Fin p × Fin q → ℂ) ≃ₗ[ℂ] (ι → Matrix (Fin p) (Fin q) ℂ) :=
    { toFun := unflat, invFun := flat, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have key : (E : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι → Matrix (Fin p) (Fin q) ℂ)) ∘ₗ L ∘ₗ
      (E.symm : (ι → Matrix (Fin p) (Fin q) ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ)) =
      LinearMap.pi fun τ => (GlobalTheory.ModuLR.lrLin (A τ) (B τ)).comp (LinearMap.proj τ) := by
    refine LinearMap.ext fun x => funext fun τ => ?_
    change unflat (L (flat x)) τ = A τ * x τ * B τ
    rw [hL]; rfl
  rw [← LinearMap.det_conj L E, key, LinearMap.det_pi]
  simp only [GlobalTheory.ModuLR.det_lrLin, Fintype.card_fin]

theorem model_smooth (h : Fintype.card (ι × Fin p × Fin q) = n) {u : ReciprocityTheory.L2DbarEstimates.V n}
    (hu : GlobalTheory.UnifDens.flatL h u ∈ DomFlat ι p q) (τ : ι) :
    MContDiffAt 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => ((hP (unflat (GlobalTheory.UnifDens.flatL h w) τ))⁻¹)ᵀ) u ∧
      IsUnit (((hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹)ᵀ).det := by
  have hp := hP_posDef (hu τ)
  have hunit : IsUnit (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ)).det := hp.det_pos.ne'.isUnit
  refine ⟨MContDiffAt.transpose (MContDiffAt.inv ?_ hunit), ?_⟩
  · have hY : MContDiffAt 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => unflat (GlobalTheory.UnifDens.flatL h w) τ) u := by
      intro a b
      have e : (fun w : ReciprocityTheory.L2DbarEstimates.V n => unflat (GlobalTheory.UnifDens.flatL h w) τ a b) =
          fun w => (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι × Fin p × Fin q => ℂ) (τ, a, b)).comp
            (GlobalTheory.UnifDens.flatL h : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ))).restrictScalars ℝ) w := rfl
      rw [e]; exact (ContinuousLinearMap.contDiff _).contDiffAt
    exact (mContDiffAt_const 1).sub (hY.mul hY.conjTranspose)
  · rw [det_transpose]; exact isUnit_nonsing_inv_det _ hunit

theorem gram_transpose_of_congr {J Hg Hy : Matrix (Fin p) (Fin p) ℂ} (hJ : IsUnit J.det) (h : Jᴴ * Hg * J = Hy) :
    Hgᵀ = (J⁻¹)ᵀ * Hyᵀ * ((J⁻¹)ᵀ)ᴴ := by
  have hJ' : IsUnit Jᴴ.det := by rw [det_conjTranspose]; exact hJ.star
  have h1 : Hg = (J⁻¹)ᴴ * Hy * J⁻¹ := by
    rw [← h, conjTranspose_nonsing_inv]
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hJ', Matrix.one_mul]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hJ, Matrix.mul_one]
  rw [h1, transpose_mul, transpose_mul]
  have e : ((J⁻¹)ᴴ)ᵀ = ((J⁻¹)ᵀ)ᴴ := by ext i j; rfl
  rw [e, Matrix.mul_assoc]

theorem chernTop_model_moeb : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ Formalism.DegreeFormula.DomFlat ι p q → GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 * ∏ i, ((Formalism.DegreeFormula.hQ (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((p + q : ℕ) : ℤ)) := by
  intro ι _ p q n h v hv
  classical
  set e := GlobalTheory.UnifDens.flatL h with he
  set K : ReciprocityTheory.L2DbarEstimates.V n → ι → Matrix (Fin p) (Fin p) ℂ := fun u τ => ((hP (unflat (e u) τ))⁻¹)ᵀ with hK
  set R : MvPolynomial (ι × ℕ) ℝ := ∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q with hR
  set z := unflat (e v) with hz
  have hzD : z ∈ DomI ι p q := hv
  obtain ⟨g, hg, hgz⟩ := exists_upqI hzD
  set Φ : (ι × Fin p × Fin q → ℂ) → (ι × Fin p × Fin q → ℂ) := fun w => flat (moebI g (unflat w)) with hΦ
  set φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n := fun u => e.symm (Φ (e u)) with hφ
  have h0D : (0 : ι × Fin p × Fin q → ℂ) ∈ DomFlat ι p q := by
    intro τ; rw [unflat_zero]; exact zero_mem_hcDom p q
  have he0 : e 0 = 0 := map_zero e
  have hφ0 : φ 0 = v := by
    show e.symm (flat (moebI g (unflat (e 0)))) = v
    rw [he0, unflat_zero, hgz]
    exact e.symm_apply_apply v
  obtain ⟨ho, H⟩ := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_and_fderiv_moebI ι p q
  obtain ⟨hd, hD⟩ := H g hg
  have hΦan : AnalyticAt ℂ Φ 0 := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn ho hd 0 h0D
  have hΦan' : AnalyticAt ℂ Φ (e 0) := by rw [he0]; exact hΦan
  have hφan : AnalyticAt ℂ φ 0 :=
    (e.symm : (ι × Fin p × Fin q → ℂ) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n).analyticAt _ |>.comp
      (hΦan'.comp ((e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)).analyticAt 0))
  have hKv := fun τ => model_smooth h (u := v) hv τ
  have h0S : e 0 ∈ DomFlat ι p q := by rw [he0]; exact h0D
  have hK0 := fun τ => model_smooth h (u := 0) h0S τ

  have hA := GlobalTheory.ChernPull.chernTop_comp R K φ 0 hφan (by rw [hφ0]; exact fun τ => (hKv τ).1)
    (by rw [hφ0]; exact fun τ => (hKv τ).2)
  rw [hφ0] at hA

  set S : Set (ReciprocityTheory.L2DbarEstimates.V n) := e ⁻¹' DomFlat ι p q with hS
  have hSo : IsOpen S := ho.preimage e.continuous
  have h0S' : (0 : ReciprocityTheory.L2DbarEstimates.V n) ∈ S := h0S
  set g' : ReciprocityTheory.L2DbarEstimates.V n → ι → Matrix (Fin p) (Fin p) ℂ :=
    fun w τ => ((jW (g τ) (unflat (e w) τ))⁻¹)ᵀ with hg'
  have hΦcd : ContDiffOn ℂ 1 Φ (DomFlat ι p q) :=
    (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn ho hd).contDiffOn ho.uniqueDiffOn
  have hΨ : ContDiffOn ℂ 1 (fun w => Φ (e w)) S :=
    hΦcd.comp (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)).contDiff.contDiffOn fun w hw => hw
  have hg'an : ∀ τ i j, AnalyticAt ℂ (fun w => g' w τ i j) 0 := by
    intro τ i j
    have hent : ∀ a b, ContDiffOn ℂ 1 (fun w => jW (g τ) (unflat (e w) τ) a b) S := by
      intro a b
      have ee : (fun w => jW (g τ) (unflat (e w) τ) a b) = fun w =>
          (g τ).1.toBlocks₁₁ a b - ∑ k, Φ (e w) (τ, a, k) * (g τ).1.toBlocks₂₁ k b := by
        funext w; simp only [jW, Matrix.sub_apply, Matrix.mul_apply]; rfl
      rw [ee]
      exact contDiffOn_const.sub (ContDiffOn.sum fun k _ => ((contDiffOn_pi.1 hΨ) (τ, a, k)).mul contDiffOn_const)
    have hinv := GlobalTheory.HodgeDomain.ActionDeriv.diffOn_inv (s := S) (M := fun w => jW (g τ) (unflat (e w) τ)) hent
      (fun w hw => (jW_isUnit (hg τ (Set.mem_univ _)) (hw τ)).ne_zero) j i
    exact GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hSo (hinv.differentiableOn one_ne_zero) 0 h0S'
  have hg'u : ∀ τ, IsUnit (g' 0 τ).det := by
    intro τ
    rw [hg', det_transpose]
    exact isUnit_nonsing_inv_det _ (jW_isUnit (hg τ (Set.mem_univ _)) (h0S τ))
  have hev : ∀ᶠ w in nhds (0 : ReciprocityTheory.L2DbarEstimates.V n), ∀ τ, K (φ w) τ =
      (((fun _ : ι => (1 : ℝ)) τ : ℝ) : ℂ) • (g' w τ * K w τ * (g' w τ)ᴴ) := by
    filter_upwards [hSo.mem_nhds h0S'] with w hw τ
    have hy : unflat (e w) τ ∈ hcDom p q := hw τ
    have hgt := hg τ (Set.mem_univ _)
    have key := gram_transpose_of_congr (jW_isUnit hgt hy) (hP_inv_moeb hgt hy)
    have e1 : K (φ w) τ = ((hP (moeb ((g τ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (unflat (e w) τ)))⁻¹)ᵀ := by
      show ((hP (unflat (e (e.symm (Φ (e w)))) τ))⁻¹)ᵀ = _
      rw [e.apply_symm_apply]; rfl
    rw [e1, key, Complex.ofReal_one, one_smul]
  have hB := GlobalTheory.PointChern.chernTop_changeFrame R (fun w => K (φ w)) K g' (fun _ => (1 : ℝ)) 0
    (fun _ => one_pos) hg'an hg'u (fun τ => (hK0 τ).1) (fun τ => (hK0 τ).2) hev

  have hΦd : HasFDerivAt Φ (fderiv ℂ Φ 0) (e 0) := by rw [he0]; exact hΦan.differentiableAt.hasFDerivAt
  have hφd : HasFDerivAt φ ((e.symm : (ι × Fin p × Fin q → ℂ) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n).comp
      ((fderiv ℂ Φ 0).comp (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)))) 0 :=
    e.symm.hasFDerivAt.comp 0 (hΦd.comp 0 e.hasFDerivAt)
  have hdetF : LinearMap.det (fderiv ℂ Φ 0 : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ)) =
      ∏ τ, (jW (g τ) 0).det ^ q * ((kapQ (g τ) 0)⁻¹).det ^ p := by
    refine det_flat_mul _ _ _ fun x => ?_
    have := hD 0 (fun τ => zero_mem_hcDom p q) (unflat x)
    exact this
  have hdet : LinearMap.det (fderiv ℂ φ 0 : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n) =
      ∏ τ, (jW (g τ) 0).det ^ q * ((kapQ (g τ) 0)⁻¹).det ^ p := by
    rw [hφd.fderiv, ← hdetF, ← LinearMap.det_conj (fderiv ℂ Φ 0 : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ))
      e.symm.toLinearEquiv]
    rfl
  have hx : ∀ τ, Complex.normSq (jW (g τ) 0).det = ((hQ (z τ)).det).re ∧
      Complex.normSq ((kapQ (g τ) 0)⁻¹).det = ((hQ (z τ)).det).re := by
    intro τ
    have hgt := hg τ (Set.mem_univ _)
    have hzτ : moeb ((g τ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = z τ := congrFun hgz τ
    rw [← hzτ]
    exact ⟨normSq_det_jW hgt, normSq_det_kapQ_inv hgt⟩
  have hN : Complex.normSq (LinearMap.det (fderiv ℂ φ 0 : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n)) =
      ∏ τ, ((hQ (z τ)).det).re ^ (p + q) := by
    rw [hdet, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_mul, map_pow, map_pow, (hx τ).1, (hx τ).2, pow_add, mul_comm]
  have hpos : ∀ τ, 0 < ((hQ (z τ)).det).re := fun τ =>
    (Complex.pos_iff.1 (show (hQ (z τ)).PosDef from hzD τ).det_pos).1
  have hNpos : 0 < ∏ τ, ((hQ (z τ)).det).re ^ (p + q) := Finset.prod_pos fun τ _ => pow_pos (hpos τ) _
  rw [hB, hN] at hA
  have e2 : ∏ τ, ((hQ (z τ)).det).re ^ (-((p + q : ℕ) : ℤ)) = (∏ τ, ((hQ (z τ)).det).re ^ (p + q))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [_root_.zpow_neg, zpow_natCast]
  show GlobalTheory.GoodMetric.chernTop R K v = GlobalTheory.GoodMetric.chernTop R K 0 * ∏ τ, ((hQ (z τ)).det).re ^ (-((p + q : ℕ) : ℤ))
  rw [e2, hA]
  field_simp

end GlobalTheory.DomDensInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRationalPolyhedralCellsUptoAutStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_rational_polyhedral_cells_upto_aut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → HasRedCover H.bar X → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  first | exact @GlobalTheory.PolCell.exists_cells | exact GlobalTheory.PolCell.exists_cells | (intros; apply GlobalTheory.PolCell.exists_cells <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMarkedFormPiecesRaysOfSimplicialCells
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan.OrbMark

theorem exists_pieces_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
  ∃ p : Fin m₀ → LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) ∧
    (∀ i, 0 < t i → p i ∈ balForms H.bar X ∧ (∀ y, 0 ≤ p i y y) ∧
      (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = p i → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (p i) = lab.evalZ (δ₀ i)) ∧
    ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ → LinearIndependent ℤ δ →
      ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
        (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
        (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  intro E _ _ _ H φ hφ X₀ _ _ _ m₀ δ₀ h₀ hind hprim v t hv ht hvt X _ _ _ β hβ
  obtain ⟨τ, f, hτ, hf, hsemi, hrel⟩ := _root_.GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one H.w0 v β hβ
  obtain ⟨u, hsum, hli, hu⟩ := _root_.GlobalTheory.PolFan.OrbMark.exists_desc_rays_pullAdd E H δ₀ h₀.mem h₀.nonneg hind hprim v t ht hvt β τ f hτ hf hsemi hrel
  refine ⟨fun i => pullAdd f (u i), hsum, fun i hi => (hu i hi).2, ?_⟩
  intro m δ hδ hδi c hc hβc
  have hA := _root_.GlobalTheory.PolFan.OrbMark.inRCone_pullAdd_of_isCell E H φ hφ δ₀ h₀ t ht (CarDim.orad v : Submodule (𝓞 E) X₀).mkQ (Submodule.mkQ_surjective _) τ f hτ
    hf hsemi u (fun i hi => ⟨(hu i hi).1, (hu i hi).2.1, (hu i hi).2.2.1⟩) β hsum m δ hδ c hc hβc
  have hB := _root_.GlobalTheory.PolFan.OrbMark.exists_coord_pullAdd_of_pos E H φ hφ δ₀ h₀ hind v t ht hvt (CarDim.orad v : Submodule (𝓞 E) X₀).mkQ
    (Submodule.mkQ_surjective _) τ f hτ hf hsemi u (fun i hi => (hu i hi).1) β
    (fun x y x₀ y₀ hx hy => hrel x y x₀ y₀ hx hy) m δ hδ c hc hβc
  exact GlobalTheory.T.cone_match_rays_after_dropping_zero_coords (fun i => pullAdd f (u i)) t ht hli β hsum m δ hδi c hc hβc hA hB

end GlobalTheory.PolFan.OrbMark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueNeZeroOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
namespace GlobalTheory.ResThree

theorem two_ne_zero_one (g : ℕ) (hg : 3 ≤ g) : (2 : ZMod g) ≠ 0 ∧ (2 : ZMod g) ≠ 1 := by
  constructor
  · intro h
    have h' : ((2 : ℕ) : ZMod g) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  · intro h
    have h' : ((2 : ℕ) : ZMod g) = ((1 : ℕ) : ZMod g) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
    omega

end GlobalTheory.ResThree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTransportedStateHeckeGaloisStage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw

theorem exists_st_copyN : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I → (∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR) → ∃ x' : St P, x'.o = ⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ ∧ HEq (repOf x'.r.Y) (repOf x.r.Y) := by
  intro K B f T w P x N hG hGA hCen
  have fits' : RowPk.Over.Fits (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over) := ⟨x.fits.div, hG, hGA, hCen⟩
  obtain ⟨m, hc, hco⟩ := Mv.exists_moved B f T w P.Z₀ P.hX P.Wt P.z P.q _ P.intersectionNumber_baseChange P.exAt P.inGeo P.grp fits'
  obtain ⟨sg, s, h1, h2, h3⟩ := CopySide.side_copy x N hG
  obtain ⟨r, hpin, hrep⟩ := GlobalTheory.T.adelicRowsReading_transport_laterHeckeGaloisStage x N hG hGA hCen m hc hco sg s h1 h2 h3
  exact ⟨⟨_, fits', x.G_eq, x.etaF, x.bk, m, hc, hco, s, r, hpin⟩, rfl, hrep⟩

end GlobalTheory.Mem.R3.Rw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqRationalDataOfEigen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple.Lay.EigCopy


theorem eigTrue_congr {D : D7} {cf : CharFrame D} {Rw Rw' : RowSide D} {Sb : Finset (PlE D.host)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (h : Rw.locR = Rw'.locR) (hT : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) :
    GlobalTheory.TwInputs.EigTrue D cf Rw' Sb eig := by
  unfold GlobalTheory.TwInputs.EigTrue at hT ⊢
  rw [← h]
  exact hT


end GlobalTheory.RowTriple.Lay.EigCopy
end
end

