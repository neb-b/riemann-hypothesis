module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeFiniteExpansionsLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentRadicalSurjectsUnitriangularCharact
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem fourierBesselBasePoint_castSucc_column (i : Fin B.V.rank) (j : Fin σ) : x0 B i (Fin.castSucc j) = B.d.jX i j := by
  simp [x0, xLast, Fin.snoc_castSucc]

theorem fourierBesselBasePoint_last_column (i : Fin B.V.rank) : x0 B i (Fin.last σ) = (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) i := by
  simp [x0, xLast, Fin.snoc_last]

theorem mul_fourierBesselBasePoint_castSucc_column {m : ℕ} (M : Mx D m B.V.rank) (i : Fin m) (j : Fin σ) :
    (M * x0 B) i (Fin.castSucc j) = (M * B.d.jX) i j := by
  simp only [Matrix.mul_apply, fourierBesselBasePoint_castSucc_column]

theorem mul_fourierBesselBasePoint_last_column {m : ℕ} (M : Mx D m B.V.rank) (i : Fin m) :
    (M * x0 B) i (Fin.last σ) = (M *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, fourierBesselBasePoint_last_column]

theorem fourierBesselBasePoint_mul_eq (U : Mx D (σ + 1) (σ + 1)) (i : Fin B.V.rank) (j : Fin (σ + 1)) :
    (x0 B * U) i j = ∑ k : Fin σ, B.d.jX i k * U (Fin.castSucc k) j +
      (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) i * U (Fin.last σ) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [fourierBesselBasePoint_castSucc_column, fourierBesselBasePoint_last_column]

theorem besselAnisotropicEmbedding_fixes_basePoint (h : GA D B.A) : mt B.V (embA B.d B.o h) * x0 B = x0 B := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [mul_fourierBesselBasePoint_last_column, fourierBesselBasePoint_last_column, embA_apply, Matrix.mulVec_mulVec, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, vecB, ratV_mulVec,
      Matrix.mulVec_mulVec (ratV B.ζ), show rat B.o.iB = B.o.jB from rfl, B.o.emb_jB, mt_one, Matrix.mul_one]
  · rw [mul_fourierBesselBasePoint_castSucc_column, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, fourierBesselBasePoint_castSucc_column]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem upSum_succ (U : Mx D (σ + 1) (σ + 1)) :
    upSum U = upSum (fun i j : Fin σ => U (Fin.castSucc i) (Fin.castSucc j)) +
      ell D σ ⬝ᵥ (fun i => U (Fin.castSucc i) (Fin.last σ)) := by
  have h1 : ∀ j : Fin σ, ¬ (j.1 = σ + 1) := fun j => by omega
  have h2 : ¬ (σ = σ + 1) := by omega
  simp only [upSum, ell, dotProduct, Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last, h1, h2, if_false,
    Finset.sum_const_zero, add_zero, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : σ = i.1 + 1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem besselFlagProjection_mul_fourierBesselBasePoint_apply (i : Fin σ) (k : Fin (σ + 1)) : (B.d.pX * x0 B) i k = if k = Fin.castSucc i then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [mul_fourierBesselBasePoint_last_column, Matrix.mulVec_mulVec, B.d.pX_j0, Matrix.zero_mulVec, if_neg (Fin.castSucc_lt_last i).ne']
    rfl
  · rw [mul_fourierBesselBasePoint_castSucc_column, B.d.pX_jX, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e).symm)]

theorem besselFlagProjection_mul_basePoint_mul_apply (U : Mx D (σ + 1) (σ + 1)) (i : Fin σ) (k : Fin (σ + 1)) :
    (B.d.pX * (x0 B * U)) i k = U (Fin.castSucc i) k := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply]
  simp only [besselFlagProjection_mul_fourierBesselBasePoint_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem simpleSum_eq_upSum {n : GA D B.V} {U : Mx D (σ + 1) (σ + 1)} (e : mt B.V n * x0 B = x0 B * U) :
    simpleSum B.d (vecB B.o B.ζ) n = upSum U := by
  have hb : blockX B.d n = fun i j : Fin σ => U (Fin.castSucc i) (Fin.castSucc j) := by
    ext i j
    have h := mul_fourierBesselBasePoint_castSucc_column B (B.d.pX * mt B.V n) i j
    rw [Matrix.mul_assoc, Matrix.mul_assoc] at h
    rw [blockX, ← besselFlagProjection_mul_basePoint_mul_apply B U i, ← e, h]
  have hc : coefX B.d (vecB B.o B.ζ) n = fun i => U (Fin.castSucc i) (Fin.last σ) := by
    ext i
    have h := mul_fourierBesselBasePoint_last_column B (B.d.pX * mt B.V n) i
    rw [Matrix.mul_assoc] at h
    rw [coefX, ← besselFlagProjection_mul_basePoint_mul_apply B U i, ← e, h, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [simpleSum, hb, hc, upSum_succ]

theorem psiBes_eq_psiUni (ψ : AddChar (AF D.host.F) ℂ) {n : GA D B.V} (h : GA D B.A) (u : UX D (σ + 1))
    (e : mt B.V (n * embA B.d B.o h) * x0 B = x0 B * u.1.1) :
    psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u.1 := by
  rw [mt_mul, Matrix.mul_assoc, besselAnisotropicEmbedding_fixes_basePoint] at e
  rw [psiBes, simpleSum_eq_upSum B e, map_one, one_mul, psiUni]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem vecB_ne : vecB B.o B.ζ ≠ 0 := by
  have hζ : B.ζ ≠ 0 := fun h => B.line.2 (by rw [h]; simp)
  intro h
  apply hζ
  have := congrArg (B.o.qB *ᵥ ·) h
  simpa [vecB, Matrix.mulVec_mulVec, B.o.qB_iB] using this

theorem exists_form : ∃ r₀ : Fin B.V₀.rank → D.host.E, ratV r₀ ⬝ᵥ ratV (vecB B.o B.ζ) = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, vecB B.o B.ζ k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact vecB_ne B (funext hc)
  refine ⟨Pi.single k (vecB B.o B.ζ k)⁻¹, ?_⟩
  rw [dotProduct, Finset.sum_eq_single k]
  · simp only [ratV, Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ hk, map_one]
  · intro l _ hl
    simp only [ratV, Pi.single_eq_of_ne hl, map_zero, zero_mul]
  · exact fun h => absurd (Finset.mem_univ k) h

theorem vecMulVec_mulVec' {m k : ℕ} (w : Fin m → AE D) (r v : Fin k → AE D) (hr : r ⬝ᵥ v = 1) :
    vecMulVec w r *ᵥ v = w := by
  ext i
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum] at hr ⊢
  rw [hr, mul_one]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

def blk (U : Mx D (σ + 1) (σ + 1)) : Mx D σ σ := fun i j => U (Fin.castSucc i) (Fin.castSucc j)

theorem det_blk {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    (blk U).det = 1 := by
  have hT : (blk U).BlockTriangular id := fun i j h => (hU _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h)
  rw [Matrix.det_of_upperTriangular hT]
  exact Finset.prod_eq_one fun i _ => (hU (Fin.castSucc i) (Fin.castSucc i)).2

def blkU {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    GL (Fin σ) (AE D) :=
  Matrix.nonsingInvUnit (blk U) (by rw [det_blk hU]; exact isUnit_one)

theorem blkU_val {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    (blkU hU).1 = blk U := rfl

theorem blkU_mem {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    blkU hU ∈ upperUni σ (AE D) := fun i j =>
  ⟨fun h => (hU (Fin.castSucc i) (Fin.castSucc j)).1 (Fin.castSucc_lt_castSucc_iff.2 h),
    (hU (Fin.castSucc i) (Fin.castSucc i)).2⟩

def blkQ (γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E) : Matrix (Fin σ) (Fin σ) D.host.E :=
  fun i j => γ (Fin.castSucc i) (Fin.castSucc j)

theorem blk_rat (γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E) : blk (rat γ : Mx D (σ + 1) (σ + 1)) = rat (blkQ γ) := rfl

theorem blkU_rat {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1)
    {γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E} (hγ : rat γ = U) :
    (blkU hU).1 ∈ ratMx D σ σ ∧ ((blkU hU)⁻¹).1 ∈ ratMx D σ σ := by
  have ha1 : (blkU hU).1 = rat (blkQ γ) := by rw [blkU_val, ← hγ, blk_rat]
  have hdet : (blkQ γ).det = 1 := by
    apply incA_injective
    rw [map_one, RingHom.map_det]
    have e : (incA D).mapMatrix (blkQ γ) = blk U := by rw [← hγ, blk_rat]; rfl
    rw [e, det_blk hU]
  have e : rat (blkQ γ)⁻¹ * (blkU hU).1 = 1 := by
    rw [ha1, ← rat_mul, Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one), rat_one]
  refine ⟨by rw [ha1]; exact rat_mem _, ?_⟩
  have hinv : ((blkU hU)⁻¹).1 = rat (blkQ γ)⁻¹ := by
    calc ((blkU hU)⁻¹).1 = (rat (blkQ γ)⁻¹ * (blkU hU).1) * ((blkU hU)⁻¹).1 := by rw [e, Matrix.one_mul]
      _ = rat (blkQ γ)⁻¹ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hinv]; exact rat_mem _

theorem rat_vecMulVec {m k : ℕ} (w : Fin m → D.host.E) (r : Fin k → D.host.E) :
    (rat (vecMulVec w r) : Mx D m k) = vecMulVec (ratV w) (ratV r) := by
  ext i j
  simp only [rat, Matrix.map_apply, vecMulVec_apply, ratV, map_mul]

theorem besselFlagElement_mul_basePoint_eq_basePoint_mul {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1)
    (a : GL (Fin σ) (AE D)) (ha : a.1 = blk U) (b : Mx D σ B.V₀.rank)
    (hbz : a.1 *ᵥ (b *ᵥ ratV (vecB B.o B.ζ)) = fun i => U (Fin.castSucc i) (Fin.last σ)) :
    mt B.V (B.d.levi a * B.d.nB b) * x0 B = x0 B * U := by
  have hX : mt B.V (B.d.levi a * B.d.nB b) * B.d.jX = B.d.jX * a.1 := by
    rw [mt_mul, Matrix.mul_assoc, B.d.nB_jX, B.d.levi_jX]
  have h0 : mt B.V (B.d.levi a * B.d.nB b) * B.d.j0 = B.d.j0 + B.d.jX * (a.1 * b) := by
    rw [mt_mul, Matrix.mul_assoc, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, B.d.levi_jX,
      Matrix.mul_assoc]
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [mul_fourierBesselBasePoint_last_column, fourierBesselBasePoint_mul_eq, Matrix.mulVec_mulVec, h0, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hbz, Pi.add_apply, (hU (Fin.last σ) (Fin.last σ)).2, mul_one]
    exact add_comm _ _
  · rw [mul_fourierBesselBasePoint_castSucc_column, fourierBesselBasePoint_mul_eq, hX, (hU (Fin.last σ) (Fin.castSucc j)).1 (Fin.castSucc_lt_last j), mul_zero, add_zero,
      Matrix.mul_apply, ha]
    rfl

theorem exists_flag (u : UX D (σ + 1)) :
    ∃ n ∈ flagN B.d, mt B.V n * x0 B = x0 B * u.1.1 ∧ (u ∈ UXQ D (σ + 1) → n ∈ GQ B.V) := by
  have hU : ∀ i j : Fin (σ + 1), (j < i → u.1.1 i j = 0) ∧ u.1.1 i i = 1 := u.2
  obtain ⟨r₀, hr⟩ := exists_form B
  obtain ⟨c, hc⟩ : ∃ c : Fin σ → AE D, c = fun i => u.1.1 (Fin.castSucc i) (Fin.last σ) := ⟨_, rfl⟩
  have hbz : (blkU hU).1 *ᵥ (vecMulVec (((blkU hU)⁻¹).1 *ᵥ c) (ratV r₀) *ᵥ ratV (vecB B.o B.ζ)) = c := by
    rw [vecMulVec_mulVec' _ _ _ hr, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hc] at hbz
  refine ⟨_, mul_mem (B.d.levi_mem_NFlag (blkU_mem hU)) (B.d.nB_mem_NFlag _),
    besselFlagElement_mul_basePoint_eq_basePoint_mul B hU (blkU hU) (blkU_val hU) _ hbz, fun hq => ?_⟩
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 hq.1
  have hr' := blkU_rat hU hγ
  have hc' : c = ratV (fun i => γ (Fin.castSucc i) (Fin.last σ)) := by
    rw [hc]; ext i; simp only [ratV, ← hγ, rat, Matrix.map_apply]
  obtain ⟨δ, hδ⟩ := mem_ratMx.1 hr'.2
  have hbq : vecMulVec (((blkU hU)⁻¹).1 *ᵥ c) (ratV r₀) ∈ ratMx D σ B.V₀.rank := by
    rw [← hδ, hc', ← ratV_mulVec, ← rat_vecMulVec]
    exact rat_mem _
  rw [hc] at hbq
  exact mul_mem (B.d.levi_mem_GQ hr'.1 hr'.2) (B.d.nB_mem_GQ hbq)

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB

theorem uniRad_surj_psi : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ u : UX D (σ + 1), ∃ n ∈ flagN B.d, mt B.V n * x0 B = x0 B * u.1.1 ∧ (u ∈ UXQ D (σ + 1) → n ∈ GQ B.V)) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ), ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (u : UX D (σ + 1)), mt B.V (n * embA B.d B.o h) * x0 B = x0 B * u.1.1 → psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u.1 :=
  fun _ _ B => ⟨UniRad.exists_flag B, fun ψ _ _ h u e => UniRad.psiBes_eq_psiUni B ψ h u e⟩

end GlobalTheory.Unf.FB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointRationalWithRationalLeftIn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

def x0Mat (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun k => Fin.snoc (α := fun _ => D.host.E) (B.d.e k) ((B.d.i₀ *ᵥ vecB B.o B.ζ) k)

theorem rat_x0Mat (B : BesLev D σ) : rat (x0Mat B) = x0 B := by
  refine Matrix.ext fun k j => ?_
  refine Fin.lastCases ?_ (fun b => ?_) j
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [x0Mat, x0, xLast, rat, HypDec.j0, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  · simp [x0Mat, x0, xLast, rat, HypDec.jX]

def besselBasePointLevelNorm (B : BesLev D σ) : D.host.E := star (vecB B.o B.ζ) ⬝ᵥ B.V₀.gram *ᵥ vecB B.o B.ζ

theorem besselBasePointLevelNorm_eq_gram_form (B : BesLev D σ) : besselBasePointLevelNorm B = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
  rw [besselBasePointLevelNorm, vecB, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    B.o.isoB]

theorem besselBasePointLevelNorm_ne_zero (B : BesLev D σ) : besselBasePointLevelNorm B ≠ 0 := by
  rw [besselBasePointLevelNorm_eq_gram_form]; exact B.line.2

def besselBasePointLeftInverse (B : BesLev D σ) : Matrix (Fin (σ + 1)) (Fin B.V.rank) D.host.E :=
  Matrix.of (Fin.snoc (α := fun _ => Fin B.V.rank → D.host.E) (fun a => B.d.qX a)
    ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))))

theorem besselLevelDatum_qX_dot_e_eq_one (B : BesLev D σ) : B.d.qX * B.d.e = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact B.d.pX_jX)

theorem wittDecomposition_projectionX_mul_anisotropicInclusion_eq_zero (B : BesLev D σ) : B.d.qX * B.d.i₀ = 0 :=
  rat_injective (by rw [rat_mul, rat_zero]; exact B.d.pX_j0)

theorem wittDecomposition_projectionZero_mul_e_eq_zero (B : BesLev D σ) : B.d.q0 * B.d.e = 0 :=
  rat_injective (by rw [rat_mul, rat_zero]; exact B.d.p0_jX)

theorem wittDecomposition_projectionZero_mul_anisotropicInclusion_eq_one (B : BesLev D σ) : B.d.q0 * B.d.i₀ = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact B.d.p0_j0)

theorem besselBasePointLeftInverse_mul_snocMatrix (B : BesLev D σ) : besselBasePointLeftInverse B * x0Mat B = 1 := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · have h : ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))) ⬝ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = 1 := by
      rw [smul_dotProduct, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc, wittDecomposition_projectionZero_mul_anisotropicInclusion_eq_one, Matrix.mul_one,
        ← Matrix.dotProduct_mulVec, smul_eq_mul]
      exact inv_mul_cancel₀ (besselBasePointLevelNorm_ne_zero B)
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last]
    exact h
  · have h : ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))) ᵥ* B.d.e = 0 := by
      rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc, wittDecomposition_projectionZero_mul_e_eq_zero, Matrix.mul_zero, Matrix.vecMul_zero, smul_zero]
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last b).symm]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc]
    exact congrFun h b
  · have h : B.d.qX *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = 0 := by
      rw [Matrix.mulVec_mulVec, wittDecomposition_projectionX_mul_anisotropicInclusion_eq_zero, Matrix.zero_mulVec]
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last a)]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc]
    exact congrFun h a
  · rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Fin.castSucc_inj]
    rw [← Matrix.one_apply (α := D.host.E) (i := a) (j := b), ← besselLevelDatum_qX_dot_e_eq_one B, Matrix.mul_apply]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_castSucc]

theorem fourierBesselBasePoint_rational_with_rational_leftInverse : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ),
    (∃ P ∈ ratMx D (σ + 1) B.V.rank, P ⬝ x0 B = 1) ∧ x0 B ∈ ratMx D B.V.rank (σ + 1) := fun _ _ B =>
  ⟨⟨rat (besselBasePointLeftInverse B), rat_mem _, by rw [← rat_x0Mat, ← rat_mul, besselBasePointLeftInverse_mul_snocMatrix, rat_one]⟩, rat_x0Mat B ▸ rat_mem _⟩

end GlobalTheory.Unf.FB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiInvariantFunctionIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open scoped Pointwise

namespace GlobalTheory.Unf

theorem vol_fund_lt_top {D : D7} {V : HSp D} (hc : CoCpt V) (v : Vol V) : v.μ v.𝓕 < ⊤ := by
  obtain ⟨_, _, _, _, _, _, hΓc⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := v.haar
  obtain ⟨K, hKc, hKcov⟩ := hc
  have hcover : v.𝓕 ⊆ ⋃ g : GQ V, (g • K) := by
    intro h _
    obtain ⟨γ, hγ, hk⟩ := hKcov h
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
    simp [Subgroup.smul_def]
  have hle : v.μ v.𝓕 ≤ v.μ K := by
    calc v.μ v.𝓕 = v.μ ((⋃ g : GQ V, (g • K)) ∩ v.𝓕) := by rw [Set.inter_eq_right.2 hcover]
      _ = v.μ (⋃ g : GQ V, (g • K ∩ v.𝓕)) := by rw [Set.iUnion_inter]
      _ ≤ ∑' g : GQ V, v.μ (g • K ∩ v.𝓕) := measure_iUnion_le _
      _ = v.μ K := (v.fund.measure_eq_tsum K).symm
  exact hle.trans_lt hKc.measure_lt_top

theorem jac_bound (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ) (hK : Continuous K)
    (hinv : ∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) (h : GA D J.W) :
    ∃ C, ∀ (n : flagN J.d) (h' : GA D J.W₀), ‖K (n.1 * J.d.emb0 h' * h)‖ ≤ C := by
  have hcont := J.d.continuous_embed
  obtain ⟨-, -, -, -, hnorm, -, -⟩ := GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d
  obtain ⟨⟨Kn, hKn, hcov⟩, -⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D J.W ρ J.d.e (isIsoSub_e J.d)
  obtain ⟨K₀, hK₀, hcov₀⟩ := J.cpt
  obtain ⟨-, -, -, -, htop, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  let f : flagN J.d × GA D J.W₀ → GA D J.W := fun p => p.1.1 * J.d.emb0 p.2 * h
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_fst).mul (hcont.comp continuous_snd)).mul continuous_const
  have hS : IsCompact (f '' (Kn ×ˢ K₀)) := (hKn.prod hK₀).image hf
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hK.continuousOn
  refine ⟨C, fun n h' => ?_⟩
  obtain ⟨γ₀, hγ₀, hk₀⟩ := hcov₀ h'
  have hemb : J.d.emb0 γ₀ ∈ GQ J.W := J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hγ₀
  let n' : flagN J.d := ⟨J.d.emb0 γ₀ * n.1 * (J.d.emb0 γ₀)⁻¹, hnorm n.1 n.2 γ₀⟩
  obtain ⟨γ, hγ, k, hk, hn'⟩ := hcov n'
  have hδ : (J.d.emb0 γ₀)⁻¹ * γ.1 ∈ GQ J.W ⊓ jacGrp J.d :=
    Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hemb) (Subgroup.mem_subgroupOf.1 hγ),
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right (MonoidHom.mem_range.2 ⟨γ₀, rfl⟩)))
        (Subgroup.mem_sup_left γ.2)⟩
  have h1 : γ.1 * k.1 = J.d.emb0 γ₀ * n.1 * (J.d.emb0 γ₀)⁻¹ := (congrArg Subtype.val hn').symm
  have heq : n.1 * J.d.emb0 h' * h = ((J.d.emb0 γ₀)⁻¹ * γ.1) * (k.1 * J.d.emb0 (γ₀ * h') * h) := by
    rw [map_mul, show ((J.d.emb0 γ₀)⁻¹ * γ.1) * (k.1 * (J.d.emb0 γ₀ * J.d.emb0 h') * h) =
      (J.d.emb0 γ₀)⁻¹ * (γ.1 * k.1) * J.d.emb0 γ₀ * J.d.emb0 h' * h by simp only [mul_assoc], h1]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [heq, hinv _ hδ]
  exact hC _ ⟨(k, γ₀ * h'), ⟨hk, hk₀⟩, rfl⟩

theorem jac_absConv : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ), Continuous K →
    (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) → ∀ h,
      AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => K (n.1 * J.d.emb0 h' * h) := by
  intro D ρ J K hK hinv h
  obtain ⟨C, hC⟩ := jac_bound D ρ J K hK hinv h
  have hcont := J.d.continuous_embed
  obtain ⟨-, h2W, -, hbW, htW, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨-, h20, -, hb0, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  have hμ : J.v0.μ J.v0.𝓕 < ⊤ := vol_fund_lt_top J.cpt J.v0
  have hν : J.vN.ν J.vN.𝓝 < ⊤ := by rw [J.vN.unit.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2 hμ.ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  unfold AbsConv
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun p => hC p.2 p.1)
  exact (hK.comp (((continuous_subtype_val.comp continuous_snd).mul (hcont.comp continuous_fst)).mul
    continuous_const)).aestronglyMeasurable

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeFiniteExpansionsLocalFieldStatement
section
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData ValuativeRel IsLocalRing Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_finite_expansions_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ), χ ≠ 1 → ∀ (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsFullLattice k], (∀ P : Pair k n', latInd (gluedS q 1 P.ker P.vec) Λ = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ • (tensCol (latInd P.ker Λ) (vecInd Λ) + ∑ Q ∈ withLat Λ, tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q)) ∧ latInd P.ker Λ + ∑ Q ∈ withLat Λ, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) = ((resCard k : ℂ) ^ Fintype.card n) • latInd P.lat Λ) ∧ (∀ R : Pair k n', latInd Λ (gluedS q 1 R.ker R.vec) = tensRow (latInd Λ R.ker) (dualInd Λ) + ∑ Q ∈ withLat Λ, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red)) ∧ ∀ (L : Submodule 𝒪[k] (n' → k)) [L.IsFullLattice k], latInd Λ (lastKer L) = tensRow (latInd Λ L) (dualInd Λ) ∧ latInd Λ (lastPair q L).lat = tensRow (latInd Λ L) (dualInd Λ + ∑ Q ∈ withLat Λ, cosetInd q Q.lat Q.red) := by
  intro k _ _ _ _ n n' _ _ _ _ q χ hχ Λ _
  refine ⟨fun P => ⟨GlobalTheory.GluedExp.glued_col q χ hχ Λ P,
    GlobalTheory.GluedExp.glued_sum q χ hχ Λ P⟩, GlobalTheory.GluedExp.glued_row q Λ, ?_⟩
  intro L _
  have hlast : latInd Λ (lastPair q L).lat =
      tensRow (latInd Λ L) (dualInd Λ + ∑ Q ∈ withLat Λ, cosetInd q Q.lat Q.red) := by
    classical
    funext x
    rw [tensRow, GlobalTheory.GluedExp.coset_total, latInd, latInd, ite_zero_mul_ite_zero, mul_one]
    have hm (v : n' ⊕ Fin 1 → k) :
        v ∈ (lastPair q L).lat ↔ v ∘ Sum.inl ∈ L ∧ q.1 • v (Sum.inr 0) ∈ 𝒪[k] := by
      rw [Pair.mem_lat_iff]
      simp only [GlobalTheory.LastSteps.lastPair_hasVal]
      constructor
      · rintro ⟨a, h, s, hs, -⟩
        exact ⟨h, hs ▸ s.2⟩
      · rintro ⟨h, hs⟩
        exact ⟨_, h, ⟨_, hs⟩, rfl, rfl⟩
    refine if_congr ⟨fun h => ⟨fun y hy => ((hm _).1 (h y hy)).1, fun y hy => ?_⟩,
      fun h y hy => (hm _).2 ⟨h.1 y hy, ?_⟩⟩ rfl rfl
    · rw [smul_dotProduct]
      exact ((hm _).1 (h y hy)).2
    · have hη := h.2 y hy
      rw [smul_dotProduct] at hη
      exact hη
  exact ⟨GlobalTheory.GluedExp.last_ker Λ L, hlast⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMem
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem inK_mul {D : D7} (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a b : GA D S) :
    InK S L P a → InK S L P b → InK S L P (a * b) := by
  rintro ⟨ha, hma⟩ ⟨hb, hmb⟩
  refine ⟨(grpAt S P).mul_mem ha hb, ?_⟩
  intro y hy
  have hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P := by
    intro i
    have : (mt S b *ᵥ y) i = ∑ j, mt S b i j * y j := rfl
    rw [this]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  have hmul : mt S (a * b) = mt S a * mt S b := rfl
  rw [hmul, ← Matrix.mulVec_mulVec]
  exact (hmb y hy).trans (hma _ hy')

end GlobalTheory.FinPl
end
end

