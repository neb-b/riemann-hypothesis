module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0164

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymbolFramePolynomialEqZeroOfGenericVanish
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA.Dense

theorem eq_zero_of_vanish_off {σ Kc : Type} [Field Kc] (ι : ℂ →+* Kc) (R : MvPolynomial σ Kc)
    (h : MvPolynomial σ ℂ) (x0 : σ → ℂ) (hx0 : MvPolynomial.eval x0 h ≠ 0)
    (hR : ∀ x : σ → ℂ, MvPolynomial.eval x h ≠ 0 → MvPolynomial.eval (ι ∘ x) R = 0) : R = 0 := by
  have hev : ∀ x : σ → ℂ, MvPolynomial.eval (ι ∘ x) (MvPolynomial.map ι h) = ι (MvPolynomial.eval x h) := by
    intro x
    rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left,
      RingHom.comp_id]
  have hh : MvPolynomial.map ι h ≠ 0 := by
    intro h0
    apply hx0
    apply ι.injective
    rw [← hev, h0, map_zero, map_zero]
  have hinf : ∀ _ : σ, (Set.range ι).Infinite := fun _ => Set.infinite_range_of_injective ι.injective
  have hprod : R * MvPolynomial.map ι h = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range ι) hinf (fun y hy => ?_)
    choose x hx using fun i => hy i (Set.mem_univ i)
    have hy' : y = ι ∘ x := funext fun i => (hx i).symm
    rw [hy', map_mul, map_zero, hev]
    by_cases hz : MvPolynomial.eval x h = 0
    · rw [hz, map_zero, mul_zero]
    · rw [hR x hz, zero_mul]
  exact (mul_eq_zero.mp hprod).resolve_right hh

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  {j : ℕ} (hN : RankTie X D j)

def idxSym (τ : D.what₂.Tau) (a : Fin (D.R.N j)) (b : Fin (D.R.N (j + 1))) : X.ZA j :=
  ⟨(pos.symm τ).1, ((pos.symm τ).2, Fin.cast hN.1 a, Fin.cast hN.2 b)⟩

def dOf (x : X.ZA j → ℂ) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ :=
  fun a b => x (idxSym X D pos hN τ a b)

theorem dOf_read (x : X.ZA j → ℂ) (z : X.ZA j) :
    dOf X D pos hN x (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2) = x z := by
  obtain ⟨v, s, a, b⟩ := z
  have key : ∀ q : (Σ v : X.Pl, Fin (X.G.P.n' v)), q = ⟨v, s⟩ →
      (⟨q.1, (q.2, a, b)⟩ : X.ZA j) = ⟨v, (s, a, b)⟩ := by
    rintro q rfl; rfl
  simp only [dOf, idxSym, Fin.cast_cast, Fin.cast_eq_self]
  rw [key _ (pos.symm_apply_apply _)]

theorem dOf_surj (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) :
    dOf X D pos hN (fun z => d (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2)) = d := by
  funext τ a b
  simp [dOf, idxSym]

def hD (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) : MvPolynomial (X.ZA j) ℂ :=
  ∏ τ, Matrix.det (Matrix.of fun a b : Fin (D.R.N j) => ∑ k : Fin (D.R.N (j + 1)),
    MvPolynomial.X (idxSym X D pos hN τ a k) * MvPolynomial.C (f' τ k (Fin.castLE (rk_le X D hN) b)))

theorem eval_hD (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (x : X.ZA j → ℂ) :
    MvPolynomial.eval x (hD X D pos hN f') = ∏ τ, (dfr X D hN (dOf X D pos hN x) f' τ).det := by
  rw [hD, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [dfr, Matrix.mul_apply, dOf]

def idxFr (τ : D.what₂.Tau) (a b : Fin (D.R.N (j + 1))) : Formalism.L2.G.Cmp.Var (X.Pj (j + 1)) :=
  ⟨(pos.symm τ).1, ((pos.symm τ).2, Fin.cast (rkT X D hN).symm a, Fin.cast (rkT X D hN).symm b)⟩

def blkOf (w : Formalism.L2.G.Cmp.Var (X.Pj (j + 1)) → ℂ) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ :=
  fun a b => w (idxFr X D pos hN τ a b)

theorem blkOf_read (w : Formalism.L2.G.Cmp.Var (X.Pj (j + 1)) → ℂ) (y : Formalism.L2.G.Cmp.Var (X.Pj (j + 1))) :
    blkOf X D pos hN w (pos ⟨y.1, y.2.1⟩) (Fin.cast (rkT X D hN) y.2.2.1) (Fin.cast (rkT X D hN) y.2.2.2) = w y := by
  obtain ⟨v, s, a, b⟩ := y
  have key : ∀ q : (Σ v : X.Pl, Fin (X.G.P.n' v)), q = ⟨v, s⟩ →
      (⟨q.1, (q.2, a, b)⟩ : Formalism.L2.G.Cmp.Var (X.Pj (j + 1))) = ⟨v, (s, a, b)⟩ := by
    rintro q rfl; rfl
  simp only [blkOf, idxFr, Fin.cast_cast, Fin.cast_eq_self]
  rw [key _ (pos.symm_apply_apply _)]

def hY : MvPolynomial (Formalism.L2.G.Cmp.Var (X.Pj (j + 1))) ℂ :=
  ∏ τ, Matrix.det (Matrix.of fun a b : Fin (D.R.N (j + 1)) => MvPolynomial.X (idxFr X D pos hN τ a b))

theorem eval_hY (w : Formalism.L2.G.Cmp.Var (X.Pj (j + 1)) → ℂ) :
    MvPolynomial.eval w (hY X D pos hN) = ∏ τ, (blkOf X D pos hN w τ).det := by
  rw [hY, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [blkOf]

def fOf {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  if IsOddPos (pos.symm τ).2 then (((g τ).submatrix id Fin.rev).transpose)⁻¹ else g τ

theorem det_rev_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) : (M.submatrix id Fin.rev).transpose.det ≠ 0 := by
  rw [Matrix.det_transpose]
  have h := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) M
  rw [show M.submatrix id ⇑(Fin.revPerm : Equiv.Perm (Fin n)) = M.submatrix id Fin.rev from rfl] at h
  rw [h]
  exact mul_ne_zero (Int.cast_ne_zero.mpr (Units.ne_zero _)) hM

theorem zT_fOf {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, (g τ).det ≠ 0) :
    zT X D pos (fOf X D pos g) = g := by
  funext τ
  unfold zT fOf
  by_cases ho : IsOddPos (pos.symm τ).2
  · rw [if_pos ho, if_pos ho,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_rev_ne_zero (g τ) (hg τ)))]
    ext a b
    simp
  · rw [if_neg ho, if_neg ho]

theorem det_fOf {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, (g τ).det ≠ 0) (τ : D.what₂.Tau) :
    (fOf X D pos g τ).det ≠ 0 := by
  unfold fOf
  by_cases ho : IsOddPos (pos.symm τ).2
  · rw [if_pos ho]
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr (det_rev_ne_zero (g τ) (hg τ)))).ne_zero
  · rw [if_neg ho]; exact hg τ

def yv {Kc : Type} [Field Kc] (ι : ℂ →+* Kc) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) :
    Formalism.L2.G.Cmp.Var (X.Pj (j + 1)) → Kc := fun y =>
  ι (zT X D pos f' (pos ⟨y.1, y.2.1⟩) (Fin.cast (rkT X D hN) y.2.2.1) (Fin.cast (rkT X D hN) y.2.2.2))

theorem evD_eq_eval {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (P : DA X Kc j) :
    evD X D pos ι hN d f' P = MvPolynomial.eval
      (fun z : X.ZA j => ι (d (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2)))
      (MvPolynomial.map (MvPolynomial.eval (yv X D pos hN ι f')) P) := by
  rw [MvPolynomial.eval_map]
  rfl

end GlobalTheory.TwV.DelA.Dense


open GlobalTheory.TwV.DelA.Dense in
theorem GlobalTheory.TwV.DelA.eq_zero_of_evD_generic : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (P : DA X Kc j), (∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' P = 0) → P = 0 := by
  intro p _ X D pos Kc _ _ ι j hN P hP
  have step1 : ∀ f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ, (∀ τ, (f' τ).det ≠ 0) →
      MvPolynomial.map (MvPolynomial.eval (yv X D pos hN ι f')) P = 0 := by
    intro f' hf'
    set E : Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ :=
      (1 : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ).submatrix (Fin.castLE (rk_le X D hN)) id with hE
    set d0 : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ := fun τ => E * (f' τ)⁻¹ with hd0
    refine eq_zero_of_vanish_off ι _ (hD X D pos hN f')
      (fun z => d0 (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2)) ?_ ?_
    · rw [eval_hD, dOf_surj]
      refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
      have : dfr X D hN d0 f' τ = 1 := by
        unfold dfr
        rw [hd0]
        simp only
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hf' τ)), Matrix.mul_one, hE,
          Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
        exact Matrix.submatrix_one _ (Fin.castLE_injective _)
      rw [this, Matrix.det_one]
      exact one_ne_zero
    · intro x hx
      rw [eval_hD] at hx
      have hdet : ∀ τ, (dfr X D hN (dOf X D pos hN x) f' τ).det ≠ 0 :=
        fun τ => (Finset.prod_ne_zero_iff.mp hx) τ (Finset.mem_univ _)
      have h := hP (dOf X D pos hN x) f' hf' hdet
      rw [evD_eq_eval] at h
      have hxv : (fun z : X.ZA j => ι (dOf X D pos hN x (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1)
          (Fin.cast hN.2.symm z.2.2.2))) = ι ∘ x := by
        funext z
        simp only [Function.comp_apply, dOf_read]
      rw [hxv] at h
      exact h
  ext m : 1
  rw [MvPolynomial.coeff_zero]
  refine eq_zero_of_vanish_off ι _ (hY X D pos hN)
    (fun y => if y.2.2.1 = y.2.2.2 then 1 else 0) ?_ ?_
  · rw [eval_hY]
    refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
    have : blkOf X D pos hN (fun y => if y.2.2.1 = y.2.2.2 then 1 else 0) τ = 1 := by
      ext a b
      simp [GlobalTheory.TwV.DelA.Dense.blkOf, GlobalTheory.TwV.DelA.Dense.idxFr, Matrix.one_apply]
    rw [this, Matrix.det_one]
    exact one_ne_zero
  · intro w hw
    rw [eval_hY] at hw
    have hg : ∀ τ, (blkOf X D pos hN w τ).det ≠ 0 := fun τ => (Finset.prod_ne_zero_iff.mp hw) τ (Finset.mem_univ _)
    have h1 := step1 (fOf X D pos (blkOf X D pos hN w)) (det_fOf X D pos _ hg)
    have h2 : yv X D pos hN ι (fOf X D pos (blkOf X D pos hN w)) = ι ∘ w := by
      funext y
      simp only [yv, zT_fOf X D pos _ hg, Function.comp_apply, blkOf_read]
    have h3 := congrArg (AddMonoidAlgebra.coeff · m) h1
    rw [MvPolynomial.coeff_map, h2, MvPolynomial.coeff_zero] at h3
    exact h3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateEntireAlgebraic
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.translate_entire_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), TaylorLogMetric.admitted D a b N N' → ∀ s : TaylorLogMetric.VC D a b, (∃ m : ℕ, 0 < m ∧ m • s ∈ TaylorLogMetric.La D B.tor N N') → Differentiable ℂ (TaylorLogMetric.U D B.tor s (B.eNat χ a b N N')) ∧ TaylorLogMetric.CoefIn D (TaylorLogMetric.U D B.tor s (B.eNat χ a b N N')) TaylorLogMetric.Qbar := by
  intro D cc δ B χ hc hδ hχ a b N N' hA s hs
  obtain ⟨h1, -⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.vector_bound_link D cc hc δ hδ B χ hχ a b N N' hA
  exact ⟨Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_diff _ s h1.1, fun α => GlobalTheory.ThLoc.algTAll D cc δ B χ hc hδ hχ a b N N' hA s hs α⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceField
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem stdU_star_det_mul_det {n : ℕ} (D : D7) (M : GL (Fin n) D.host.E) (hU : StdU D M) :
    star (M : Matrix (Fin n) (Fin n) D.host.E).det * (M : Matrix (Fin n) (Fin n) D.host.E).det = 1 := by
  rw [← Matrix.det_conjTranspose, ← Matrix.det_mul]
  have : (M : Matrix (Fin n) (Fin n) D.host.E).conjTranspose = star (M : Matrix (Fin n) (Fin n) D.host.E) := rfl
  rw [this, hU, Matrix.det_one]

theorem stdU_inv_eq_star {n : ℕ} (D : D7) (M : GL (Fin n) D.host.E) (hU : StdU D M) :
    ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = star (M : Matrix (Fin n) (Fin n) D.host.E) := by
  have h1 : ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (M : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)
      = ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((M : Matrix (Fin n) (Fin n) D.host.E) * ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = star (M : Matrix (Fin n) (Fin n) D.host.E) * (M : Matrix (Fin n) (Fin n) D.host.E) * ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        rw [← Matrix.mul_assoc, h1, hU]
    _ = star (M : Matrix (Fin n) (Fin n) D.host.E) := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem blkC_atR_read : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ {n : ℕ} (M : GL (Fin n) D.host.E), StdU D M → ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), (if IsOddPos s then ((((atR D M (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose) else (atR D M (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).map ι = ((M : Matrix (Fin n) (Fin n) D.host.E).map (ρ v)).map (Formalism.L2.G.Pend.tw X Kc v s) ∧ Formalism.L2.G.Pend.tw X Kc v s (ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det) = ι (embT D (pos ⟨v, s⟩) (M : Matrix (Fin n) (Fin n) D.host.E).det) ^ (if IsOddPos s then (-1 : ℤ) else 1) := by
  intro p _ X D pos Kc _ _ ι ρ hT n M hU v s
  have hT' := hT v s
  constructor
  · ext i j
    simp only [Matrix.map_apply]
    split_ifs with hs
    · have hinv : ((atR D M (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) = atR D M⁻¹ (pos ⟨v, s⟩) := by
        simp [atR, map_inv]
      rw [Matrix.transpose_apply, hinv]
      simp only [atR, Matrix.GeneralLinearGroup.map_apply]
      rw [stdU_inv_eq_star D M hU, hT', if_pos hs]
      simp [Matrix.star_apply]
    · simp only [atR, Matrix.GeneralLinearGroup.map_apply]
      rw [hT', if_neg hs]
  · split_ifs with hs
    · have h := hT' (M : Matrix (Fin n) (Fin n) D.host.E).det
      rw [if_pos hs] at h
      have h2 := hT' (star (M : Matrix (Fin n) (Fin n) D.host.E).det)
      rw [if_pos hs, star_star] at h2
      rw [← h2, zpow_neg_one]
      have h3 := congrArg (fun x => ι (embT D (pos ⟨v, s⟩) x)) (stdU_star_det_mul_det D M hU)
      simp only [map_mul, map_one] at h3
      exact (eq_inv_of_mul_eq_one_left h3)
    · rw [hT', if_neg hs, zpow_one]

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeakRepIso
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut

theorem weak_repIso : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak π ι r' → UpperTheory.V.Af.RepIso r r' := by
  intro E Ω _ _ _ _ _ _ l _ ι a π r r' h h'
  obtain ⟨hc, hss, hev⟩ := h
  obtain ⟨hc', hss', hev'⟩ := h'
  refine GlobalTheory.IsoOfFrobFree.main E Ω l ι a r r' hc hc' hss hss' ?_
  filter_upwards [hev, hev'] with w ⟨B, hB, hF⟩ ⟨B', hB', hF'⟩
  obtain rfl := CG.HasSat.unique hB hB'
  exact ⟨_, hF, hF'⟩

end GlobalTheory.GalCut
end

