module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfAbstract
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutGenA
section
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct Matrix Kronecker Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix Formalism.IndefR.DatumF

namespace PositivityTheory.ThKW.GenA

section Abstract

theorem det_unit_sig {K ι G : Type} [Field K] [Fintype ι] [DecidableEq ι] [FunLike G K K] [RingHomClass G K K] (σ : G)
    {M P : Matrix ι ι K} (hP : P.det ≠ 0) (h : (M.map σ)ᵀ * P * M = P) :
    M.det * σ M.det = 1 ∧ M.det * σ (M - 1).det = (-1) ^ Fintype.card ι * (M - 1).det := by
  have hd : ∀ N : Matrix ι ι K, (N.map σ)ᵀ.det = σ N.det := fun N => by
    rw [det_transpose]; exact (RingHom.map_det (σ : K →+* K) N).symm
  constructor
  · have := congrArg Matrix.det h
    rw [det_mul, det_mul, hd] at this
    refine mul_right_cancel₀ hP ?_
    linear_combination this
  · have hm : (M - 1).map σ = M.map σ - 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    have e : ((M - 1).map σ)ᵀ * P * M = P * -(M - 1) := by
      rw [hm, transpose_sub, transpose_one, Matrix.sub_mul, Matrix.sub_mul, h, Matrix.one_mul, neg_sub, Matrix.mul_sub,
        Matrix.mul_one]
    have := congrArg Matrix.det e
    rw [det_mul, det_mul, det_mul, hd, det_neg] at this
    refine mul_right_cancel₀ hP ?_
    linear_combination this

theorem kron_unit_sig {K G : Type} [Field K] [FunLike G K K] [RingHomClass G K K] (σ : G) {m n : ℕ}
    {a Gm : Matrix (Fin n) (Fin n) K} {b H : Matrix (Fin m) (Fin m) K} (hG : IsUnit Gm.det)
    (ha : (a.map σ)ᵀ * Gm * a = Gm) (hb : (b.map σ)ᵀ * H * b = H) :
    ((b ⊗ₖ aᵀ).map σ)ᵀ * (H ⊗ₖ Gm⁻¹ᵀ) * (b ⊗ₖ aᵀ) = H ⊗ₖ Gm⁻¹ᵀ := by
  have h1 : (Gm⁻¹ * (a.map σ)ᵀ * Gm) * a = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (a.map σ)ᵀ, ha, Matrix.nonsing_inv_mul _ hG]
  have h2 : a * Gm⁻¹ * (a.map σ)ᵀ = Gm⁻¹ := by
    have h3 := mul_eq_one_comm.1 h1
    calc a * Gm⁻¹ * (a.map σ)ᵀ = a * (Gm⁻¹ * (a.map σ)ᵀ * Gm) * Gm⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
      _ = Gm⁻¹ := by rw [h3, Matrix.one_mul]
  have e : ((b ⊗ₖ aᵀ).map σ)ᵀ = (b.map σ)ᵀ ⊗ₖ a.map σ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [Matrix.kroneckerMap_apply, map_mul]
  rw [e, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hb]
  congr 1
  conv_rhs => rw [← h2]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem cart_exists {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ = G) (hd : G.det ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    ∃ s, Formalism.IndefR.Datum.IsCartanInv ((r : ℂ) • G) s := by
  refine GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv ?_ (isUnit_iff_ne_zero.2 ?_)
  · show ((r : ℂ) • G)ᴴ = (r : ℂ) • G
    rw [conjTranspose_smul, hG, Complex.star_def, Complex.conj_ofReal]
  · rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 hr)) hd

theorem cart_refl {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ = G) (hd : G.det ≠ 0) (r : ℝ) (hr : r ≠ 0)
    (y : Fin k → ℂ) (hy : star y ⬝ᵥ G *ᵥ y ≠ 0) (d : ℂ) :
    ∃ s, Formalism.IndefR.Datum.IsCartanInv ((r : ℂ) • G) s ∧
      s * (1 + d • vecMulVec y (star y ᵥ* G)) = (1 + d • vecMulVec y (star y ᵥ* G)) * s := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  obtain ⟨s, h1, h2⟩ := _root_.GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection _ ((r : ℂ) • G)
    (by rw [conjTranspose_smul, hG, Complex.star_def, Complex.conj_ofReal])
    (by rw [det_smul]; exact mul_ne_zero (pow_ne_zero _ hr') hd) y
    (by
      have e : star y ⬝ᵥ ((r : ℂ) • G) *ᵥ y = (r : ℂ) * (star y ⬝ᵥ G *ᵥ y) := by
        simp only [dotProduct, mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [e]
      exact mul_ne_zero hr' hy)
  refine ⟨s, h1, ?_⟩
  have e : d • vecMulVec y (star y ᵥ* G) = (d / r) • vecMulVec y (star y ᵥ* ((r : ℂ) • G)) := by
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, vecMul, dotProduct, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp
  rw [e]
  exact h2 _

theorem blk_comm {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ} {sT b : O → Matrix (Fin m) (Fin m) ℂ}
    {sS a : O → Matrix (Fin n) (Fin n) ℂ} (h1 : ∀ w, sT w * b w = b w * sT w) (h2 : ∀ w, a w * sS w = sS w * a w) :
    GlobalTheory.RealWeil.blk sT sS * GlobalTheory.RealWeil.blk b a = GlobalTheory.RealWeil.blk b a * GlobalTheory.RealWeil.blk sT sS := by
  rw [GlobalTheory.RealWeil.blk_mul, GlobalTheory.RealWeil.blk_mul]
  congr 1 <;> funext w
  exacts [h1 w, h2 w]

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incAF_injective : Function.Injective (incAF F E) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem mt_unitary (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) :
    ((mtF σ J g).map (cAF σ))ᵀ * J.map (incAF F E) * mtF σ J g = J.map (incAF F E) := g.2

theorem mt_ext {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g h : GAF σ J} (e : mtF σ J g = mtF σ J h) :
    g = h := Subtype.ext (Units.ext e)

theorem mt_one (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mtF σ J 1 = 1 := rfl

theorem mt_mul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g h : GAF σ J) :
    mtF σ J (g * h) = mtF σ J g * mtF σ J h := rfl

theorem map_unitary (σ : E →ₐ[F] E) {n : ℕ} (J a : Matrix (Fin n) (Fin n) E) :
    ((a.map (incAF F E)).map (cAF σ))ᵀ * J.map (incAF F E) * a.map (incAF F E) =
      ((a.map σ)ᵀ * J * a).map (incAF F E) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

theorem det_ne_of_unitary {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {a : Matrix (Fin n) (Fin n) E} (h : (a.map σ)ᵀ * J * a = J) : a.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [det_mul, det_mul, h0, mul_zero] at this
  exact hJ.2 this.symm

theorem infPart_incAF (x : E) : infPartF F E (incAF F E x) = (1 : Ainf F) ⊗ₜ[F] x := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem herm_map {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hJ.1]

theorem det_map_ne {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (τ : E →+* ℂ) :
    (J.map τ).det ≠ 0 := by
  rw [show (J.map τ).det = τ J.det from (RingHom.map_det τ J).symm]
  exact (map_ne_zero τ).2 hJ.2

theorem im_ne {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {ξ₀ : E} (h0 : ξ₀ ≠ 0) (hξ : σ ξ₀ = -ξ₀) (τ : E →+* ℂ) :
    (τ ξ₀).im ≠ 0 := by
  intro him
  have h1 : star (τ ξ₀) = -τ ξ₀ := by rw [← hcm.2.2.2, hξ, map_neg]
  have hre : (τ ξ₀).re = 0 := by
    have := congrArg Complex.re h1
    rw [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  apply h0
  apply τ.injective
  rw [map_zero]
  exact Complex.ext (by rw [hre, Complex.zero_re]) (by rw [him, Complex.zero_im])

theorem hermE_alt (c : E ≃ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    GlobalTheory.UnRep.hermE c Jᵀ x y = (fun b => c (y b)) ⬝ᵥ J *ᵥ x := by
  simp only [GlobalTheory.UnRep.hermE, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isUnE_iff (c : E ≃ₐ[F] E) {n : ℕ} (J M : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.UnRep.IsUnE c Jᵀ M ↔ (M.map (c : E →ₐ[F] E))ᵀ * J * M = J := by
  have e1 : ∀ y : Fin n → E, (fun b => c ((M *ᵥ y) b)) = (fun b => c (y b)) ᵥ* (M.map (c : E →ₐ[F] E))ᵀ :=
    fun y => by
      rw [vecMul_transpose]
      funext i
      exact RingHom.map_mulVec ((c : E →ₐ[F] E) : E →+* E) M y i
  have e : ∀ x y, GlobalTheory.UnRep.hermE c Jᵀ (M *ᵥ x) (M *ᵥ y) =
      (fun b => c (y b)) ⬝ᵥ ((M.map (c : E →ₐ[F] E))ᵀ * J * M) *ᵥ x := fun x y => by
    rw [hermE_alt, e1, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hs : ∀ i : Fin n, (fun b => c ((Pi.single i (1 : E) : Fin n → E) b)) = (Pi.single i (1 : E) : Fin n → E) :=
    fun i => funext fun b => by by_cases h : b = i <;> simp [h]
  refine ⟨fun h => ?_, fun h x y => by rw [e, h, hermE_alt]⟩
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rw [e, hermE_alt, hs] at this
  simpa using this

theorem quad_map {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (c : E ≃ₐ[F] E) (hc : (c : E →ₐ[F] E) = σ) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (τ : E →+* ℂ) :
    star (τ ∘ x) ⬝ᵥ J.map τ *ᵥ (τ ∘ x) = τ (GlobalTheory.UnRep.hermE c Jᵀ x x) := by
  have h' : ∀ z, τ (c z) = star (τ z) := fun z => by rw [← hcm.2.2.2, ← hc]; rfl
  rw [hermE_alt, RingHom.map_dotProduct]
  congr 1
  · funext i
    simp [h']
  · funext i
    exact (RingHom.map_mulVec τ J x i).symm

theorem refl_map {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (c : E ≃ₐ[F] E) (hc : (c : E →ₐ[F] E) = σ) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) (τ : E →+* ℂ) :
    (GlobalTheory.UnRep.refl c Jᵀ x u).map τ =
      1 + τ ((u - 1) / GlobalTheory.UnRep.hermE c Jᵀ x x) • vecMulVec (τ ∘ x) (star (τ ∘ x) ᵥ* J.map τ) := by
  have h' : ∀ z, τ (c z) = star (τ z) := fun z => by rw [← hcm.2.2.2, ← hc]; rfl
  have e : τ ∘ (Jᵀ *ᵥ fun b => c (x b)) = star (τ ∘ x) ᵥ* J.map τ := by
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Function.comp_apply, mulVec, vecMul, dotProduct, transpose_apply, map_sum, map_mul, Matrix.map_apply,
      Pi.star_apply, h']
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [GlobalTheory.UnRep.refl, ← RingHom.mapMatrix_apply, map_add (f := _), map_one, ← e]
  congr 1
  ext i j
  simp [vecMulVec_apply, map_mul]

end PositivityTheory.ThKW.GenA

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutRealB
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

theorem gaussV_eq {κ : Type} [Fintype κ] [DecidableEq κ] {H s g : Matrix κ κ ℂ} (hH : Hᴴ = H) (hQ : (H * s).PosDef)
    (v : κ → ℂ) : gaussV H s g v =
      Complex.exp (-(Real.pi : ℂ) * (star v ⬝ᵥ GlobalTheory.RatAut.RealInt.expM H s g *ᵥ v)) := by
  rw [GlobalTheory.RatAut.RealInt.dot_expM hH hQ, gaussV, omV_apply, omV_apply, jV_apply, ← Complex.exp_add]
  congr 1
  ring

theorem integral_gaussV_B {κ : Type} [Fintype κ] [DecidableEq κ] {H s g g' : Matrix κ κ ℂ} (hH : Hᴴ = H) (hs : s * s = 1)
    (hQ : (H * s).PosDef) (hg : gᴴ * H * g = H) (hc : s * g = g * s) (hi : g * g' = 1) (hd : (g - 1).det ≠ 0) :
    Integrable (gaussV H s g) volume ∧ GlobalTheory.RealWeil.dP s g' ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (∫ v, gaussV H s g v) * (g - 1).det = r * (-s).det * (g.det * GlobalTheory.RealWeil.dP s g') := by
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MatrixGaussian.integral_gaussian κ _ (GlobalTheory.RatAut.RealInt.expM_herm hQ hd)
  have e : gaussV H s g = fun v => Complex.exp (-(Real.pi : ℂ) * (star v ⬝ᵥ GlobalTheory.RatAut.RealInt.expM H s g *ᵥ v)) :=
    funext (gaussV_eq hH hQ)
  refine ⟨by rw [e]; exact h1, ?_, (H * s).det.re⁻¹, inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1, ?_⟩
  · have h3 := congrArg det (GlobalTheory.RatAut.RealInt.expM_mul hH hs hg hc hi)
    simp only [det_mul] at h3
    have h4 : (-H).det * (-s).det = (H * s).det := by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    intro h0
    unfold GlobalTheory.RealWeil.dP at h0
    have h5 : (-H).det * (g - 1).det = 0 := by rw [← h3, h0]; ring
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact hQ.det_pos.ne' (by rw [← h4, h6, zero_mul])
    · exact hd h6
  · rw [e, h2]
    exact GlobalTheory.RatAut.RealInt.gauss_det hH hs hQ hg hc hi hd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}

theorem det_mMF_B (C : Ctx σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (mMF σ JS JT θ (g⁻¹, h⁻¹)).det = ∏ v, tauB B v (b ⊗ₖ aᵀ).det ∧
      (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det = ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det := by
  have e1 : ∀ w, compAtF θ w (mtF σ JT h⁻¹) = b.map (tauB B w) := fun w => by
    rw [show mtF σ JT h⁻¹ = b.map (incAF F E) from hb]
    ext i j
    exact PositivityTheory.ThKW.RealC.theta_inc (C.inf w) _
  have e2 : ∀ w, compAtF θ w (mtF σ JS g⁻¹⁻¹) = a.map (tauB B w) := fun w => by
    rw [inv_inv, show mtF σ JS g = a.map (incAF F E) from ha]
    ext i j
    exact PositivityTheory.ThKW.RealC.theta_inc (C.inf w) _
  have e3 : ∀ w, (b.map (tauB B w) ⊗ₖ (a.map (tauB B w))ᵀ) = (b ⊗ₖ aᵀ).map (tauB B w) := fun w => by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.transpose_apply, map_mul]
  rw [mMF_apply]
  simp only [e1, e2]
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.RatAut.RealInt.det_blk]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [e3]
    exact (RingHom.map_det _ _).symm
  · rw [GlobalTheory.RatAut.RealInt.det_blk_sub_one]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [e3, RingHom.map_det, map_sub, map_one]
    rfl

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoBis
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.LagrangianIntegralFactorisation

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end PositivityTheory.ThKW.LagrangianIntegralFactorisation

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoTer
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.ParsevalPolarization

open GlobalTheory.ThetaTransform

end PositivityTheory.ThKW.ParsevalPolarization

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBS
section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {nS nT : ℕ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}


variable (F) in
def inrA : Af F →ₗ[F] AF F where
  toFun a := pairA F 0 a
  map_add' _ _ := Prod.ext (add_zero 0).symm rfl
  map_smul' c _ := Prod.ext (smul_zero c).symm rfl


variable (F E) in
def liftF : Af F ⊗[F] E →ₗ[F] AEF F E := TensorProduct.map (inrA F) LinearMap.id

theorem liftF_tmul (a : Af F) (t : E) : liftF F E (a ⊗ₜ[F] t) = pairA F 0 a ⊗ₜ[F] t := rfl


variable (E) in
abbrev hatO : AddSubgroup (Af F ⊗[F] E) := GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))

theorem fin_mul_eq (y : AEF F E) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) * y = liftF F E (finPartF F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a t =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      show finPartF F E (a ⊗ₜ[F] t) = sndA F a ⊗ₜ[F] t from rfl, liftF_tmul]
    congr 1
    exact Prod.ext (zero_mul _) (one_mul _)
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), map_add (f := _)]

theorem liftF_smul_mem {z : Af F ⊗[F] E} (hz : z ∈ hatO (F := F) E) {u : WOF F E nS nT}
    (hu : u ∈ latOF F E nS nT Λ) : liftF F E z • u ∈ latOF F E nS nT Λ := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨b, rfl⟩, rfl⟩ := hz
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨α, hα, γ, hγ, rfl⟩ := hu
      refine AddSubgroup.subset_closure ⟨a * α, fun v => GlobalTheory.AdLat.adele_mul_integral F (ha v) (hα v),
        b • γ, Λ.smul_mem b hγ, ?_⟩
      ext i j
      simp only [liftF_tmul, Matrix.smul_apply, smul_eq_mul, ratWF, Matrix.map_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      show (pairA F 0 a ⊗ₜ[F] (b : E)) * ((pairA F 0 α ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] γ i j)) =
        (pairA F 0 (a * α) ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] ((b • γ) i j))
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul, one_mul, Matrix.smul_apply]
      congr 1
      exact Prod.ext (mul_zero _) rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  | zero => rw [map_zero, zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, neg_smul]; exact neg_mem hx

theorem idem_smul_mem {e : AEF F E} (he : e * e = e) (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e)
    {u : WOF F E nS nT} (hu : u ∈ latOF F E nS nT Λ) : e • u ∈ latOF F E nS nT Λ := by
  have h1 : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, he])
  rw [← hf, fin_mul_eq]
  exact liftF_smul_mem h1 hu

theorem fin_of_place {e : AEF F E} {α : Af F} (h : algebraMap (AF F) (AEF F E) (pairA F 0 α) * e = e) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e := by
  rw [← h, ← mul_assoc, ← map_mul]
  congr 2
  exact Prod.ext (zero_mul _) (one_mul _)

theorem split_parts {e : AEF F E} (he : IsSplitIdemF σ e) :
    (algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) ∧
      (algebraMap (AF F) (AEF F E) (pairA F 0 1) * cAF σ e = cAF σ e) ∧ cAF σ e * cAF σ e = cAF σ e := by
  obtain ⟨hee, hec, v, ε, ⟨α, rfl, -⟩, hs⟩ := he
  have hce : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, hee]
  refine ⟨fin_of_place (α := α) ?_, fin_of_place (α := α) ?_, hce⟩
  · rw [← hs, add_mul, hee, mul_comm, hec, add_zero]
  · rw [← hs, add_mul, hec, hce, zero_add]

end PositivityTheory.ThKW.LatB

end
end

