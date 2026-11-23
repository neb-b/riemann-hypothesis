module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjXPreservesEmbeddingLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory

theorem projX_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e * d.qX) *ᵥ v ∈ a.lat Λ 𝔟 := by
  intro D A B B₀ c ρ a d hA Λ 𝔟 v hv
  obtain ⟨hc, he, s, he'⟩ := hA
  obtain ⟨y, hy, u, hu, rfl⟩ := hv
  have hGh : B.gramᴴ = B.gram := GlobalTheory.MixModel.gram_conjTranspose B
  have hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0 := a.perp
  have hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  set N : Matrix (Fin c) (Fin c) D.host.E := antiDiagonalSignGramMatrix c (-1) with hN
  have hK : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have := congrArg Matrix.conjTranspose hperp
    simpa [Matrix.conjTranspose_mul, hGh, Matrix.mul_assoc] using this
  have hρc : ρ ≤ c := by omega
  let P : Matrix (Fin c) (Fin ρ) D.host.E := fun q p => if q = (Fin.castLE hρc p).rev then s p else 0
  let Q : Matrix (Fin c) (Fin ρ) D.host.E := fun q p => if q = Fin.castLE hρc p then (-D.host.xi0) ^ (p.1 + 1) else 0
  have heP : d.e' = a.a * P := by
    rw [he']; ext i p; rw [Matrix.mul_apply]; simp [colsOf, P, mul_comm]
  have heQ : d.e = a.a * Q := by
    rw [he]; ext i p; rw [Matrix.mul_apply]; simp [colsOf, Q, mul_comm]
  have hPN : ∀ p q, (Pᴴ * N) p q = if q = Fin.castLE hρc p then star (s p) else 0 := by
    intro p q
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    simp only [P, apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := p.2; have := q.2
    simp only [hN, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, Fin.val_castLE]
    split_ifs <;> first | (exfalso; omega) | ring
  have hdiag : ∀ p : Fin ρ, star (s p) * (-D.host.xi0) ^ (p.1 + 1) = 1 := by
    intro p
    have h1 := d.e'e
    rw [heP, heQ, Matrix.conjTranspose_mul] at h1
    have h2 : Pᴴ * a.aᴴ * B.gram * (a.a * Q) = Pᴴ * N * Q := by
      rw [← hgram]; simp only [Matrix.mul_assoc]
    rw [h2] at h1
    have h3 := congrFun (congrFun h1 p) p
    rw [Matrix.mul_apply] at h3
    simp only [hPN, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Q, Matrix.one_apply_eq] at h3
    simpa using h3
  have hqX : d.qX = Pᴴ * a.aᴴ * B.gram := by
    rw [HypDec.qX, heP, Matrix.conjTranspose_mul]
  have ht : d.qX *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) = (Pᴴ * N) *ᵥ u := by
    have h1 : Pᴴ * a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
      calc _ = Pᴴ * (a.aᴴ * B.gram * frameMat B A a.ι) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hK, Matrix.mul_zero]
    have h2 : Pᴴ * a.aᴴ * B.gram * a.a = Pᴴ * N := by
      rw [← hgram]; simp only [Matrix.mul_assoc]
    rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hqX, h1, h2, zero_mulVec, zero_add]
  have hu' : ∀ q : Fin c, (Q *ᵥ ((Pᴴ * N) *ᵥ u)) q = if q.1 < ρ then u q else 0 := by
    intro q
    simp only [mulVec, dotProduct, hPN, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Q]
    split_ifs with hq
    · rw [Finset.sum_eq_single ⟨q.1, hq⟩]
      · have e1 : q = Fin.castLE hρc ⟨q.1, hq⟩ := Fin.ext rfl
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [← mul_assoc, mul_comm ((-D.host.xi0) ^ _), hdiag, one_mul, if_pos e1, ← e1]
      · intro b _ hb
        rw [if_neg]
        intro e; apply hb; ext; simp only [Fin.ext_iff, Fin.val_castLE, Fin.val_mk] at e ⊢; omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro e; apply hq; rw [e]; simp
  refine ⟨0, Λ.zero_mem, Q *ᵥ ((Pᴴ * N) *ᵥ u), fun q => ?_, ?_⟩
  · rw [hu']; split_ifs
    · exact hu q
    · exact (𝔟 q).val.zero_mem
  · rw [mulVec_zero, zero_add, ← mulVec_mulVec, ht, heQ, ← mulVec_mulVec]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjYPreservesEmbeddingLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

variable {D : D7}

theorem colsOf_eq_mul {n c k : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (s : Fin k → D.host.E) :
    colsOf a f s = a * Matrix.of (fun q p => if q = f p then s p else 0) := by
  ext i p
  simp only [colsOf, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm _ _

theorem antiDiagonalGram_neg_one_castLE_row {c ρ : ℕ} (h : 2 * ρ ≤ c) (p : Fin ρ) (r : Fin c) :
    antiDiagonalSignGramMatrix c (-1 : D.host.E) (Fin.castLE (by omega) p) r = if r = (Fin.castLE (by omega) p : Fin c).rev then 1 else 0 := by
  have := p.2; have := r.2
  unfold antiDiagonalSignGramMatrix
  simp only [Fin.ext_iff, Fin.val_rev, Fin.val_castLE]
  split_ifs <;> first | rfl | omega

theorem projY_mem_lat : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e' * d.qY) *ᵥ v ∈ a.lat Λ 𝔟 := by
  intro D A B B₀ c ρ a d ⟨h, he, s, he'⟩ Λ 𝔟 v ⟨y, hy, u, hu, hv⟩
  subst hv
  set f : Fin ρ → Fin c := Fin.castLE (by omega) with hf
  set t : Fin ρ → D.host.E := fun p => (-D.host.xi0) ^ (p.1 + 1) with ht
  set Pe : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = f p then t p else 0) with hPe
  set Pe' : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = (f p).rev then s p else 0) with hPe'
  have hE : d.e = a.a * Pe := by rw [he, colsOf_eq_mul]
  have hE' : d.e' = a.a * Pe' := by rw [he', colsOf_eq_mul]
  have hG : B.gramᴴ = B.gram := GlobalTheory.MixModel.gram_conjTranspose B
  have hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0 := a.perp
  have hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  have hperp' : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have := congrArg Matrix.conjTranspose hperp
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero, ← Matrix.mul_assoc] at this
  have hQF : d.qY * frameMat B A a.ι = 0 := by
    rw [HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hperp', Matrix.mul_zero]
  have hQA : d.qY * a.a = Matrix.of (fun p r => if r = (f p).rev then star (t p) else 0) := by
    rw [HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hgram]
    ext p r
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hPe, Matrix.of_apply, apply_ite star, star_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hf, antiDiagonalGram_neg_one_castLE_row h, mul_ite, mul_one, mul_zero]
  have hS : ∀ p, s p * star (t p) = 1 := by
    intro p
    have h1 : d.eᴴ * B.gram * d.e' = 1 := by
      have := congrArg Matrix.conjTranspose d.e'e
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_one, ← Matrix.mul_assoc] at this
    have h2 : (d.qY * a.a * Pe') p p = 1 := by
      rw [Matrix.mul_assoc, ← hE', HypDec.qY, h1, Matrix.one_apply_eq]
    rw [hQA] at h2
    simp only [Matrix.mul_apply, hPe', Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h2
    rw [mul_comm]; exact h2
  refine ⟨0, Λ.zero_mem, fun q => ∑ p, if q = (f p).rev then u q else 0, fun q => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun p _ => ?_
    split_ifs
    · exact hu q
    · exact Submodule.zero_mem _
  · rw [mulVec_zero, zero_add, ← mulVec_mulVec, mulVec_add, mulVec_mulVec, mulVec_mulVec, hQF, zero_mulVec, zero_add,
      mulVec_mulVec, hQA, hE', Matrix.mul_assoc, ← mulVec_mulVec]
    apply congrArg (fun x => a.a *ᵥ x)
    ext q
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hPe', Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hq : q = (f p).rev
    · subst hq
      simp only [if_true, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, hS p, one_mul]
    · simp only [hq, if_false, zero_mul, Finset.sum_const_zero]

end GlobalTheory.AscFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedIdealLatticeHo
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.TwistHatMx

theorem homLat_conj {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (h : Matrix (Fin m) (Fin n) D.host.E) (hh : h ∈ homLat Λ Λ') : q * h * j ∈ homLat M M' := by
  intro y hy
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hq _ (hh _ (hj _ hy))

theorem smul_homLat_conj {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (x : Matrix (Fin m) (Fin n) D.host.E) (hx : x ∈ 𝔪 • homLat Λ Λ') : q * x * j ∈ 𝔪 • homLat M M' := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro c hc h hh
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact Submodule.smul_mem_smul hc (homLat_conj j q hj hq h hh)
  · intro a b ha hb
    rw [Matrix.mul_add, Matrix.add_mul]
    exact Submodule.add_mem _ ha hb

theorem gen_conj {D : D7} {m n m' n' : ℕ} (a : AF D.host.F) (x : Matrix (Fin m) (Fin n) D.host.E) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) :
    rat q * (Matrix.of fun i k => a ⊗ₜ[D.host.F] x i k) * rat j = Matrix.of fun i k => a ⊗ₜ[D.host.F] (q * x * j) i k := by
  have e : ∀ {r s : ℕ} (y : Matrix (Fin r) (Fin s) D.host.E), (Matrix.of fun i k => a ⊗ₜ[D.host.F] y i k) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) • rat y := by
    intro r s y
    ext i k
    simp [rat, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, e, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [rat, Matrix.map_mul]

theorem rat_conj_mem_hatMx {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (x : Mx D m n) (hx : x ∈ hatMx (𝔪 • homLat Λ Λ')) : rat q * x * rat j ∈ hatMx (𝔪 • homLat M M') := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    rw [gen_conj]
    exact AddSubgroup.subset_closure ⟨α, hα, q * y * j, smul_homLat_conj 𝔪 j q hj hq y hy, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Matrix.mul_add, Matrix.add_mul]
    exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha =>
    rw [Matrix.mul_neg, Matrix.neg_mul]
    exact AddSubgroup.neg_mem _ ha

end GlobalTheory.TwistHatMx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPreimageEqZero
section
open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.FourierPush

theorem real_case {Y : Type} [MeasurableSpace Y] (m : Measure Y) (G : Y → ℝ) (hG : Integrable G m)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (p : Y → E) (hp : Measurable p)
    (h : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * ((G y : ℝ) : ℂ) ∂m = 0)
    (s : Set E) (hs : MeasurableSet s) : ∫ y in p ⁻¹' s, G y ∂m = 0 := by
  let P := m.withDensity fun y => ENNReal.ofReal (G y)
  let P' := m.withDensity fun y => ENNReal.ofReal (-G y)
  haveI : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hG.2
  haveI : IsFiniteMeasure P' := isFiniteMeasure_withDensity_ofReal hG.neg.2
  have hcont : ∀ l : E →L[ℝ] ℝ, Continuous fun x : E => Complex.exp ((l x : ℂ) * Complex.I) :=
    fun l => by fun_prop
  have hbd : ∀ (l : E →L[ℝ] ℝ) (y : Y), ‖Complex.exp ((l (p y) : ℂ) * Complex.I)‖ ≤ 1 :=
    fun l y => (Complex.norm_exp_ofReal_mul_I _).le
  have hmeas : ∀ l : E →L[ℝ] ℝ,
      AEStronglyMeasurable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
    fun l => ((hcont l).measurable.comp hp).aestronglyMeasurable
  have e1 : ∀ l : E →L[ℝ] ℝ, charFunDual (P.map p) l
      = ∫ y, ((G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I) ∂m := by
    intro l
    rw [charFunDual_apply, integral_map hp.aemeasurable (hcont l).aestronglyMeasurable]
    exact integral_withDensity_eq_integral_smul₀ hG.aemeasurable.real_toNNReal _
  have e2 : ∀ l : E →L[ℝ] ℝ, charFunDual (P'.map p) l
      = ∫ y, ((-G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I) ∂m := by
    intro l
    rw [charFunDual_apply, integral_map hp.aemeasurable (hcont l).aestronglyMeasurable]
    exact integral_withDensity_eq_integral_smul₀ hG.neg.aemeasurable.real_toNNReal _
  have hmap : P.map p = P'.map p := by
    refine Measure.ext_of_charFunDual (funext fun l => ?_)
    rw [e1, e2, ← sub_eq_zero]
    have i1 : Integrable (fun y => ((G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
      hG.real_toNNReal.smul_of_top_left
        (memLp_top_of_bound (hmeas l) 1 (Filter.Eventually.of_forall (hbd l)))
    have i2 : Integrable (fun y => ((-G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
      hG.neg.real_toNNReal.smul_of_top_left
        (memLp_top_of_bound (hmeas l) 1 (Filter.Eventually.of_forall (hbd l)))
    rw [← integral_sub i1 i2, ← h l]
    congr 1; funext y
    rw [← sub_smul, Complex.real_smul, mul_comm]
    congr 2
    simp only [Real.coe_toNNReal']
    rcases le_total 0 (G y) with h' | h'
    · rw [max_eq_left h', max_eq_right (by linarith)]; simp
    · rw [max_eq_right h', max_eq_left (by linarith)]; simp
  have hval : ∀ f : Y → ℝ, ∫⁻ y in p ⁻¹' s, ENNReal.ofReal (f y) ∂m
      = (m.withDensity fun y => ENNReal.ofReal (f y)).map p s := fun f => by
    rw [Measure.map_apply hp hs, withDensity_apply _ (hp hs)]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hG.integrableOn, hval G,
    hval (fun y => -G y)]
  change (P.map p s).toReal - (P'.map p s).toReal = 0
  rw [hmap, sub_self]

theorem setIntegral_preimage_eq_zero (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ)
    (hF : Integrable F m) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (p : Y → E) (hp : Measurable p)
    (h : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * F y ∂m = 0)
    (s : Set E) (hs : MeasurableSet s) : ∫ y in p ⁻¹' s, F y ∂m = 0 := by
  have hcont : ∀ l : E →L[ℝ] ℝ, Continuous fun x : E => Complex.exp ((l x : ℂ) * Complex.I) :=
    fun l => by fun_prop
  have hI : ∀ l : E →L[ℝ] ℝ, Integrable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I) * F y) m :=
    fun l => hF.bdd_mul ((hcont l).measurable.comp hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)
  have hic : Integrable (fun y => (starRingEnd ℂ) (F y)) m := by
    refine ⟨hF.1.star, ?_⟩
    simpa [HasFiniteIntegral] using hF.2
  have hI' : ∀ l : E →L[ℝ] ℝ,
      Integrable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I) * (starRingEnd ℂ) (F y)) m :=
    fun l => hic.bdd_mul ((hcont l).measurable.comp hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)
  have hconj : ∀ (l : E →L[ℝ] ℝ) (x : E),
      (starRingEnd ℂ) (Complex.exp ((((-l) x : ℝ) : ℂ) * Complex.I)) = Complex.exp (((l x : ℝ) : ℂ) * Complex.I) := by
    intro l x
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    simp
  have hc' : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (starRingEnd ℂ) (F y) ∂m = 0 := by
    intro l
    have := congrArg (starRingEnd ℂ) (h (-l))
    rw [← integral_conj, map_zero] at this
    simpa only [map_mul, hconj] using this
  have hre : ∀ l : E →L[ℝ] ℝ,
      ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (((F y).re : ℝ) : ℂ) ∂m = 0 := fun l => by
    simp only [Complex.re_eq_add_conj, mul_div_assoc', mul_add]
    rw [integral_div, integral_add (hI l) (hI' l), h l, hc' l]; simp
  have him : ∀ l : E →L[ℝ] ℝ,
      ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (((F y).im : ℝ) : ℂ) ∂m = 0 := fun l => by
    simp only [Complex.im_eq_sub_conj, mul_div_assoc', mul_sub]
    rw [integral_div, integral_sub (hI l) (hI' l), h l, hc' l]; simp
  have h1 := real_case m (fun y => (F y).re) hF.re p hp hre s hs
  have h2 := real_case m (fun y => (F y).im) hF.im p hp him s hs
  apply Complex.ext
  · rw [Complex.zero_re, ← h1]
    exact (integral_re hF.integrableOn).symm
  · rw [Complex.zero_im, ← h2]
    exact (integral_im hF.integrableOn).symm

end GlobalTheory.FourierPush

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameLinkMapInvertsHermitianSkewAdjoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.KapAdjLine

theorem kap_starAdj : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (x : WO (negSp F.Lz) (G.V (.core (2 * ρ + 1)))), (F.lnk ρ).κ _ (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ x) = x := by
  unfold OnStd
  intro D _ _ _ _ _ _ G _ _ _ F hF ρ x
  have hτ : (F.lnk ρ).τ = D.host.xi0 • (1 : Matrix (Fin (negSp F.Lz).rank) (Fin (negSp F.Lz).rank) D.host.E) := by
    have hl := F.line ρ
    have hu : Unique (Fin (negSp F.Lz).rank) := by rw [hl.1]; infer_instance
    have hz : F.ζ (ρ + 1) = (-D.host.xi0) • F.ζ ρ := by rw [hF.ζ, hF.ζ (ρ), pow_succ', mul_smul]
    have e : (F.lnk ρ).τ *ᵥ F.ζ ρ = -((-D.host.xi0) • F.ζ ρ) := by rw [← hz]; exact (F.lnk ρ).map
    have h2 := hl.2
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at h2
    have b : F.ζ ρ default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
    have e1 := congrFun e default
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_unique, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_mul, neg_neg] at e1
    funext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact mul_right_cancel₀ b e1
  rw [Lnk.κ, hτ, rat_smul, rat_one, Matrix.smul_mul, Matrix.one_mul, smul_smul, ← map_mul,
    mul_inv_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one, one_smul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]

end GlobalTheory.KapAdjLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStageCartanFrameConjValuesCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto

theorem conj_stage_val_mem_A0_and_cartan_frame : ∀ D : D7, ForStage D fun c _ s => ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  intro D c hc j _ s hs
  obtain ⟨a, ha, hmaj⟩ := GlobalTheory.ChainOnto.RealData.exists_maj_cart c.θ hc.inf s.M
  exact ⟨GlobalTheory.ChainOnto.RealData.sortedFrame s.M hs.sigOK, a, GlobalTheory.ChainOnto.RealData.isCartanFrame_sortedFrame _ _,
    fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart _ τ, fun τ => GlobalTheory.ChainOnto.RealData.sortedFrame_cart _ _ τ, ha, hmaj,
    fun u v hv => GlobalTheory.ChainOnto.RealData.conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite c.θ hc.inf s.M hs.sigOK u.1 u.2 v hv⟩

end GlobalTheory.EvenOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainUnitVacuumOtherLatticesExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreVacRe

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem reLat_sigOK (G : GridData L sc) (i : ℕ) (h : i ≤ D.R.m) (r : ReLat (G.V (.core i))) : r.sp.SigOK :=
  (G.isV (X := .core i) (by simpa [Node.InRange] using h) (by simp)).sigOK

theorem frameLat_selfDual (V : HSp D) : IsSelfDualC V (GlobalTheory.AdelicU.frameLat V) := by
  have e : GlobalTheory.AdelicU.frameLat V = GlobalTheory.PlaceModel.latFrame V := by
    ext y; rw [GlobalTheory.AdelicU.mem_frameLat, GlobalTheory.PlaceModel.mem_latFrame]
  rw [e]; exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem vacExists_reLat : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ (r : ReLat (G.V (.core i)))
    (r' : ReLat (G.V (.core (i + 1)))) (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'),
    ∃ f₀, IsVacO W.ψ W.θ r.sp r'.sp (cart M) (cart M') (GlobalTheory.AdelicU.frameLat r.sp : Set _)
      (GlobalTheory.AdelicU.frameLat r'.sp : Set _) f₀ := by
  intro D _ _ _ _ _ _ G W _ _ i hi r r' S S' M M'
  exact GlobalTheory.VacuumO.vacExists D W.ψ W.θ W.ψ_std W.θ_is r.sp r'.sp (cart M) (cart M')
    (reLat_sigOK G i hi.le r) (reLat_sigOK G (i + 1) hi r')
    (fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M τ) (fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M' τ)
    _ _ (frameLat_selfDual r.sp) (frameLat_selfDual r'.sp)

end GlobalTheory.CoreVacRe

end
end

