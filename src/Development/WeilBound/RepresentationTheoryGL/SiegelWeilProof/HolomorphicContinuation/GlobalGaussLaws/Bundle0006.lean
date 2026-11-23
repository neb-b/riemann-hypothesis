module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HermCocompact
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def NbFacts : Prop :=
  ∀ (D : D7) (n : ℕ) (nb : hermA D n → G D n), PositivityTheory.PfSWUS.IsNMap nb →
    Continuous nb ∧ (∀ b c, nb (b + c) = nb b * nb c) ∧ ∀ γ ∈ ratHerm D n, nb γ ∈ GF D n

def CharFacts : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ β : HermE D n,
    Continuous (fun b : hermA D n => ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) ∧
    ∀ b : hermA D n, ‖ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1

def HermCocompact : Prop :=
  ∀ (D : D7) (r : ℕ), ∃ K : Set (hermA D r), IsCompact K ∧ ∀ x, ∃ l ∈ ratHerm D r, x - l ∈ K

theorem gLamBd_of (hNb : NbFacts) (hCh : CharFacts) (hCo : HermCocompact) : GLamBd := by
  intro D n ψ hψ L hL
  obtain ⟨nb, lam, 𝓖, β, g, ⟨hnb, hlam, hfd, hvol⟩, -, rfl⟩ := hL
  obtain ⟨hcont, hadd, hrat⟩ := hNb D n nb hnb
  obtain ⟨hχc, hχn⟩ := hCh D n ψ hψ β
  obtain ⟨K, hK, hKc⟩ := hCo D n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  set χ : hermA D n → ℂ := fun b => ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) with hχ
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hcm : Continuous fun b : hermA D n => nb b * g := hcont.mul continuous_const

  have hper : ∀ (F : G D n → ℂ), (∀ γ ∈ GF D n, ∀ x, F (γ * x) = F x) → ∀ b, ∃ k ∈ K,
      F (nb b * g) = F (nb k * g) := by
    intro F hF b
    obtain ⟨l, hl, hbl⟩ := hKc b
    refine ⟨b - l, hbl, ?_⟩
    have e : nb b = nb l * nb (b - l) := by rw [← hadd, add_sub_cancel]
    rw [e, mul_assoc, hF _ (hrat l hl)]

  have hbd : ∀ (F : G D n → ℂ) (M : ℝ), (∀ γ ∈ GF D n, ∀ x, F (γ * x) = F x) →
      (∀ x ∈ (fun b => nb b * g) '' K, ‖F x‖ ≤ M) → ∀ b, ‖F (nb b * g) * χ b‖ ≤ M := by
    intro F M hF hM b
    obtain ⟨k, hk, e⟩ := hper F hF b
    rw [norm_mul, hχn b, mul_one, e]
    exact hM _ ⟨k, hk, rfl⟩
  have hint : ∀ (F : G D n → ℂ), Continuous F → (∀ γ ∈ GF D n, ∀ x, F (γ * x) = F x) →
      IntegrableOn (fun b => F (nb b * g) * χ b) 𝓖 lam := by
    intro F hFc hF
    obtain ⟨M, hM⟩ := (hK.image hcm).exists_bound_of_continuousOn hFc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne ?_ ?_
    · exact ((hFc.comp hcm).mul hχc).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun b => hbd F M hF hM b
  refine ⟨fun a F F' hFc hF'c hF hF' => ?_, ⟨(fun b => nb b * g) '' K, hK.image hcm, fun F M hFc hF hM => ?_⟩⟩
  · simp only [PositivityTheory.PfSWUS.fc]
    have e : (fun b : hermA D n => (a • F + F') (nb b * g) *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) =
        fun b => a * (F (nb b * g) * χ b) + F' (nb b * g) * χ b := by
      funext b; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]; ring
    rw [e, integral_add ((hint F hFc hF).const_mul a) (hint F' hF'c hF'), integral_const_mul]
  · show ‖∫ b in 𝓖, F (nb b * g) * χ b ∂lam‖ ≤ M
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun b _ => hbd F M hF hM b)
    have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
    rwa [hr, mul_one] at h1

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HermSmulOne
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem phiS_eq' {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ}
    {Ψ : Mx D m n → ℂ} {P : PX m n} (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : phiS θ τ fr c Ψ P = ⟨_, h⟩ := by
  unfold phiS
  rw [dite_eq_left h]

theorem herm_smul_one (t : ℝ) : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HolValueAtFinsum
section
noncomputable section

namespace PositivityTheory.Rg.Sw.Glob

theorem holValueAt_finsum {ι : Type} (T : Finset ι) {f : ι → ℂ → ℂ} {c : ι → ℂ} {s₀ : ℂ}
    (h : ∀ i ∈ T, GlobalTheory.Cont.HolValueAt (f i) s₀ (c i)) :
    GlobalTheory.Cont.HolValueAt (fun s => ∑ i ∈ T, f i s) s₀ (∑ i ∈ T, c i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using GlobalTheory.Cont.holValueAt_const 0 s₀
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cosetSum_finsum {G : Type} [Group G] (Pp Γ : Subgroup G) {ι : Type} (T : Finset ι) (f : ι → G → ℂ) (g : G)
    (h : ∀ i ∈ T, GlobalTheory.Eis.CosetConv Pp Γ (f i) g) :
    GlobalTheory.Eis.cosetSum Pp Γ (fun x => ∑ i ∈ T, f i x) g = ∑ i ∈ T, GlobalTheory.Eis.cosetSum Pp Γ (f i) g := by
  unfold GlobalTheory.Eis.cosetSum GlobalTheory.Eis.term
  exact Summable.tsum_finsetSum fun i hi => (h i hi).of_norm

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.InvGroup
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {m n : ℕ}

def IsUe (ε : Fin m → Bool) (X : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  Xᴴ * Matrix.diagonal (sgn ε) + Matrix.diagonal (sgn ε) * X = 0

def xyP (X : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (if b then star (X a c) else X a c) * MvPolynomial.X (c, i, b)

def vfX (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyP X a i false * pderiv (a, i, false) P + xyP X a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyP X a i false * MvPolynomial.X (a, i, true) + xyP X a i true * MvPolynomial.X (a, i, false)) * P)

def zRe (ε : Fin m → Bool) (a b : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  (1 / 2 : ℂ) • (Matrix.single a b 1 - (sgn ε a * sgn ε b) • Matrix.single b a 1)

def zIm (ε : Fin m → Bool) (a b : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  (-(Complex.I / 2) : ℂ) • (Matrix.single a b 1 + (sgn ε a * sgn ε b) • Matrix.single b a 1)


end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocCellA

end PositivityTheory.Rg.Sw.Glob.LocCellA

namespace PositivityTheory.Rg.Sw.Glob

end PositivityTheory.Rg.Sw.Glob

namespace PositivityTheory.Rg.Sw.Glob.LocCellA

theorem block_matrix_mul_comm_ring {R : Type} [Ring R] {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_diagonal_one_eq_one {R : Type} [Ring R] {n : ℕ} : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = blk4 1 0 0 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem block_matrix_map {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.fromBlocks_map]
  rfl

theorem map_neg_one' {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) :
    (-1 : Matrix (Fin n) (Fin n) R).map f = -1 := by
  change (f.mapMatrix) (-1) = -1
  rw [map_neg, map_one]

theorem map_one' {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) :
    (1 : Matrix (Fin n) (Fin n) R).map f = 1 := by
  change (f.mapMatrix) 1 = 1
  rw [map_one]

theorem blockMatrixTwoByTwoFin_transpose {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d)ᵀ = blk4 aᵀ cᵀ bᵀ dᵀ := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

end PositivityTheory.Rg.Sw.Glob.LocCellA

namespace PositivityTheory.Rg.Sw.Glob


open LocCellA in
theorem wEx : WEx := by
  intro D n
  let M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := blk4 0 1 (-1) 0
  let Mi : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := blk4 0 (-1) 1 0
  have h1 : M * Mi = 1 := by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]
  have h2 : Mi * M = 1 := by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]
  let u : GL (Fin (n + n)) (AE D) := ⟨M, Mi, h1, h2⟩
  have hu : u ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M * JR (AF D.host.F) (Jst D n) * M = JR (AF D.host.F) (Jst D n)
    have hJ : JR (AF D.host.F) (Jst D n) = M := by
      simp [JR, Jst, M, block_matrix_map, map_neg_one', map_one']
    rw [hJ]
    simp [Formalism.UG.cT, M, block_matrix_map, blockMatrixTwoByTwoFin_transpose, block_matrix_mul_comm_ring, map_neg_one', map_one']
  exact ⟨⟨u, hu⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstA
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

variable {σ : Type}

def reP (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (AddMonoidAlgebra.coeff p m).re

def imaginary (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (AddMonoidAlgebra.coeff p m).im

theorem coeff_reP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (reP p) m = (AddMonoidAlgebra.coeff p m).re := by
  classical
  unfold reP
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : AddMonoidAlgebra.coeff p m = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem coeff_imP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (imaginary p) m = (AddMonoidAlgebra.coeff p m).im := by
  classical
  unfold imaginary
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : AddMonoidAlgebra.coeff p m = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem eq_map_re_add_im (p : MvPolynomial σ ℂ) :
    p = map (algebraMap ℝ ℂ) (reP p) + C Complex.I * map (algebraMap ℝ ℂ) (imaginary p) := by
  ext m
  rw [MvPolynomial.coeff_add, coeff_C_mul, coeff_map, coeff_map, coeff_reP, coeff_imP]
  apply Complex.ext <;> simp

theorem eq_zero_of_eval_real (p : MvPolynomial σ ℂ) (h : ∀ y : σ → ℝ, eval (fun i => (y i : ℂ)) p = 0) : p = 0 := by
  have hev : ∀ (y : σ → ℝ) (q : MvPolynomial σ ℝ),
      eval (fun i => (y i : ℂ)) (map (algebraMap ℝ ℂ) q) = ((eval y q : ℝ) : ℂ) := by
    intro y q
    rw [eval_map]
    change _ = (algebraMap ℝ ℂ) (eval₂ (RingHom.id ℝ) y q)
    rw [hom_eval₂]
    rfl
  have key : ∀ y : σ → ℝ, eval y (reP p) = 0 ∧ eval y (imaginary p) = 0 := by
    intro y
    have hy := h y
    rw [eq_map_re_add_im p, eval_add, eval_mul, eval_C, hev, hev] at hy
    have hre := congrArg Complex.re hy
    have him := congrArg Complex.im hy
    simp at hre him
    exact ⟨hre, him⟩
  have hr : reP p = 0 := MvPolynomial.funext fun y => by simpa using (key y).1
  have hi : imaginary p = 0 := MvPolynomial.funext fun y => by simpa using (key y).2
  rw [eq_map_re_add_im p, hr, hi]
  simp

end PositivityTheory.Rg.Sw.Glob.LocInstH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReidxConjTranspose
section
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open EmbP
open Formalism.IndefR.Eqv (psiT thetaC eq_thetaC)

variable {D : D7} {n : ℕ}

theorem reidx_mul (a b : M2 n) : reidx (a * b) = reidx a * reidx b := by
  simp only [reidx, Matrix.submatrix_mul_equiv]

theorem reidx_one : reidx (1 : M2 n) = 1 := Matrix.submatrix_one_equiv _

theorem reidx_conjTranspose (a : M2 n) : reidx aᴴ = (reidx a)ᴴ := by
  simp only [reidx, Matrix.conjTranspose_submatrix]

theorem continuous_reidx : Continuous (fun a : M2 n => reidx a) :=
  continuous_id.matrix_submatrix _ _

theorem Jst_map (τ : D.what₂.Tau) : (Jst D n).map (tauE D τ) = reidx (JJ n) := by
  ext i j
  simp only [Jst, blk4, reidx, JJ, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem mR_mul_inv (a : GR n) : mR a * mR a⁻¹ = 1 := by
  rw [← mR_mul, mul_inv_cancel, mR_one]

theorem mR_inv_mul (a : GR n) : mR a⁻¹ * mR a = 1 := by
  rw [← mR_mul, inv_mul_cancel, mR_one]

theorem reidx_unitary (τ : D.what₂.Tau) (y : GR n) :
    (reidx (mR y))ᴴ * (Jst D n).map (tauE D τ) * reidx (mR y) = (Jst D n).map (tauE D τ) := by
  have h : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  rw [Jst_map, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, h]

def iotaF (τ : D.what₂.Tau) (y : GR n) : G D n :=
  (⟨⟨atMN D τ (reidx (mR y)), atMN D τ (reidx (mR y⁻¹)),
      by rw [← atMN_mul, ← reidx_mul, mR_mul_inv, reidx_one, atMN_one],
      by rw [← atMN_mul, ← reidx_mul, mR_inv_mul, reidx_one, atMN_one]⟩,
    atMN_unitary D τ (Jst D n) _ (reidx_unitary τ y)⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

def iota (τ : D.what₂.Tau) : GR n →* G D n where
  toFun := iotaF τ
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show atMN D τ (reidx (mR 1)) = 1
    rw [mR_one, reidx_one, atMN_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    show atMN D τ (reidx (mR (a * b))) = atMN D τ (reidx (mR a)) * atMN D τ (reidx (mR b))
    rw [mR_mul, reidx_mul, atMN_mul]

theorem continuous_iota (τ : D.what₂.Tau) : Continuous (iota (D := D) (n := n) τ) := by
  have hm : Continuous fun y : GR n => mR y := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun y : GR n => mR y⁻¹ := hm.comp continuous_inv
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_atMN D τ).comp (continuous_reidx.comp hm)
  · exact (continuous_atMN D τ).comp (continuous_reidx.comp hmi)

theorem sEmb : SEmb := by
  intro D n θ τ hθ
  obtain rfl := eq_thetaC D hθ
  refine ⟨iota τ, continuous_iota τ, fun y => ⟨?_, fun τ' hτ' => ?_, ?_⟩⟩
  · have e := psi_atMN D τ τ (reidx (mR y))
    rw [if_pos rfl] at e
    exact e
  · have e := psi_atMN D τ τ' (reidx (mR y))
    rw [if_neg hτ'] at e
    exact e
  · exact fin_atMN D τ (reidx (mR y))

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigOKOf
section
noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem cnt_add {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at h
  exact h

theorem sigOK_of (hlt : WittLBlt) (heq : WittLBeq) : SigOK := by
  intro D n V s hr hs
  by_contra hne
  push Not at hne
  choose ε fr hfr hng using hne
  obtain ⟨h1, h2, h3⟩ := hr
  have hb : ∀ τ, V.rank - n ≤ cnt (ε τ) true ∧ V.rank - n ≤ cnt (ε τ) false := by
    intro τ
    have hc := cnt_add (ε τ)
    unfold GoodSig at hng
    have := hng τ
    push Not at this
    obtain ⟨a, b, c, d⟩ := this
    constructor <;> omega
  have hS : SigAtLeast D V (V.rank - n) := fun τ =>
    ⟨ε τ, fr τ, (hfr τ).1, (hfr τ).2.1, (hb τ).1, (hb τ).2⟩
  have hw : V.rank - n ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
    rcases Nat.lt_or_ge (2 * (V.rank - n)) V.rank with h | h
    · exact hlt D V _ h hS
    · exact heq D V _ (by omega) hS
  omega

end PositivityTheory.Rg.Sw.Glob
end
end

