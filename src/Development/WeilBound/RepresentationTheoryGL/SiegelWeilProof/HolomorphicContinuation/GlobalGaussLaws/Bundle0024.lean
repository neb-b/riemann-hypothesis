module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0022
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0021
public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtAdd
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilBH

variable {D : D7} {n : ℕ}

theorem compAt_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem pointAt {m : ℕ} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (hfr : IsUnit fr.det) (x₀ : Mx D m n) (u : Fin m → Fin n → ℂ) :
    ∃ x : Mx D m n, fr⁻¹ * compAt θ τ x = Matrix.of u ∧ (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x₀) ∧
      x.map (finPart D) = x₀.map (finPart D) := by
  obtain ⟨L, _, hLf, hLz⟩ :=
    Formalism.IndefR.Eqv.lineAtExists_holds D θ hθ m n τ (fr * Matrix.of u - compAt θ τ x₀)
  refine ⟨x₀ + L 1, ?_, ?_, ?_⟩
  · rw [compAt_add, hLz 1 τ, if_pos rfl, Complex.ofReal_one, one_smul]
    have hs : compAt θ τ x₀ + (fr * Matrix.of u - compAt θ τ x₀) = fr * Matrix.of u := by abel
    rw [hs]
    exact Matrix.nonsing_inv_mul_cancel_left _ _ hfr
  · intro τ' h
    rw [compAt_add, hLz 1 τ', if_neg h, add_zero]
  · ext i j
    have h1 := congrFun (congrFun (hLf 1) i) j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add (f := _), Matrix.zero_apply] at h1 ⊢
    rw [h1, add_zero]

end PositivityTheory.Rg.Sw.Glob.DilBH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalc
section
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.Glob

open DCalcBH DCalcCH in
theorem dCalc : DCalc := by
  intro m n ε t c e X hc _
  have hfun : ∀ u : Fin m → Fin n → ℂ, (fun s' : ℝ => famC ε t c e 1 X (↑s') u) = fF c X 1 u :=
    fun u => funext fun s => famC_one ε t c e X u s
  refine ⟨fun s r u => ?_, fun r s => ?_⟩
  · rw [hfun, fF_iter]
    rfl
  · simp only [hfun, fF_iter]
    rw [pow_succ']
    exact DCalc2H.l2conv c hc X ((dil c X ^ r) 1) s

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetMMUnitary
section
noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacI

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacG

variable {n : ℕ}

theorem blocks_kak (u u' : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (hu' : u'ᴴ * u' = 1) (θ : Fin n → ℝ) :
    mM u * kth θ * mM u' = fromBlocks (u * (dR fun j => Real.cos (θ j)) * u') (u * (dR fun j => Real.sin (θ j)) * u')
      (-(u * (dR fun j => Real.sin (θ j)) * u')) (u * (dR fun j => Real.cos (θ j)) * u') := by
  have h1 : uᴴ⁻¹ = u := Matrix.inv_eq_right_inv hu
  have h2 : u'ᴴ⁻¹ = u' := Matrix.inv_eq_right_inv hu'
  simp only [mM, kth, dR, h1, h2, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, neg_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem det_mM_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) : (mM u).det = u.det * u.det := by
  rw [mM_unitary u hu, det_fromBlocks_zero₂₁]

private theorem det_kth_eq_one (θ : Fin n → ℝ) : (kth θ).det = 1 := by
  have hL : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (I • (1 : Matrix (Fin n) (Fin n) ℂ))
      (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  have hR : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-(I • (1 : Matrix (Fin n) (Fin n) ℂ)))
      (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  have key : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (I • (1 : Matrix (Fin n) (Fin n) ℂ))
        (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) * kth θ *
        fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-(I • (1 : Matrix (Fin n) (Fin n) ℂ)))
        (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)
      = fromBlocks (diagonal fun j => (Real.cos (θ j) : ℂ) - I * Real.sin (θ j)) (0 : Matrix (Fin n) (Fin n) ℂ)
          (-diagonal fun j => (Real.sin (θ j) : ℂ))
          (diagonal fun j => (Real.cos (θ j) : ℂ) + I * Real.sin (θ j)) := by
    simp only [kth, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul]
    congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [h, diagonal_apply] <;>
      first
      | ring1
      | linear_combination Complex.sin ((θ j : ℝ) : ℂ) * I_sq
  have hprod : ∏ j, (((Real.cos (θ j) : ℂ) - I * Real.sin (θ j)) * ((Real.cos (θ j) : ℂ) + I * Real.sin (θ j))) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    have hp := Real.sin_sq_add_cos_sq (θ j)
    generalize Real.cos (θ j) = c at *
    generalize Real.sin (θ j) = s at *
    have hp' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hp
    linear_combination hp' - (s : ℂ) ^ 2 * I_sq
  have h := congrArg Matrix.det key
  rw [det_mul, det_mul, hL, hR, det_fromBlocks_zero₁₂, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib,
    hprod, one_mul, mul_one] at h
  exact h

theorem det_kth (θ : Fin n → ℝ) (hθ : ∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) : (kth θ).det = 1 := by
  exact det_kth_eq_one θ

theorem jF_kak (e : ℤ) (p q : ℕ) (k : GR n) (u u' : Matrix (Fin n) (Fin n) ℂ) (θ : Fin n → ℝ) (hu : uᴴ * u = 1)
    (hu' : u'ᴴ * u' = 1) (hθ : ∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) (hkm : mR k = mM u * kth θ * mM u') :
    jF e p q k (I • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      (u.det * u.det * (u'.det * u'.det)) ^ e * (u.det * (∏ j, cexp (-(I * (θ j : ℂ)))) * u'.det) ^ (-(p : ℤ)) *
        (u.det * (∏ j, cexp (I * (θ j : ℂ))) * u'.det) ^ (-(q : ℤ)) := by
  have hdet : (mR k).det = u.det * u.det * (u'.det * u'.det) := by
    rw [hkm, det_mul, det_mul, det_mM_unitary u hu, det_mM_unitary u' hu', det_kth θ hθ, mul_one]
  have hk2 := hkm.trans (blocks_kak u u' hu hu' θ)
  have hdm : diagonal (fun j => cexp (-(I * (θ j : ℂ)))) =
      (dR fun j => Real.cos (θ j)) - I • (dR fun j => Real.sin (θ j)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [dR, diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show -(I * (θ a : ℂ)) = (-(θ a : ℂ)) * I by ring, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    · simp [dR, diagonal_apply, h]
  have hdp : diagonal (fun j => cexp (I * (θ j : ℂ))) =
      (dR fun j => Real.cos (θ j)) + I • (dR fun j => Real.sin (θ j)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [dR, diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show I * (θ a : ℂ) = (θ a : ℂ) * I by ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    · simp [dR, diagonal_apply, h]
  have hA : toBlocks₂₁ (mR k) * (I • (1 : Matrix (Fin n) (Fin n) ℂ)) + toBlocks₂₂ (mR k) =
      u * diagonal (fun j => cexp (-(I * (θ j : ℂ)))) * u' := by
    rw [hk2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hdm]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_neg]
    abel
  have hZ : (I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = -(I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, conj_I, neg_smul]
  have hB : toBlocks₂₁ (mR k) * (I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ + toBlocks₂₂ (mR k) =
      u * diagonal (fun j => cexp (I * (θ j : ℂ))) * u' := by
    rw [hZ, hk2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hdp, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg, neg_neg]
    abel
  simp only [jF, hdet, hA, hB, det_mul, det_diagonal]

end PositivityTheory.Rg.Sw.Glob.VacI
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussG
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem conj_half_smul (Z : Matrix (Fin n) (Fin n) ℂ) : ((1 / 2 : ℂ) • (Z + Zᴴ))ᴴ = (1 / 2 : ℂ) • (Z + Zᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp [Complex.ext_iff]

theorem exists_sqrt {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.PosDef) : ∃ S : Matrix (Fin n) (Fin n) ℂ, S * Sᴴ = Y ∧ IsUnit S.det := by
  classical
  have hH := hY.1
  let U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  let d : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ))
  have hd : d * dᴴ = diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos i).le]
    rfl
  have hS : U * d * (U * d)ᴴ = Y := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc d, hd]
    conv_rhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    simp [U, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  refine ⟨U * d, hS, ?_⟩
  have hYu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit
  rw [← hS, Matrix.det_mul] at hYu
  exact isUnit_of_mul_isUnit_left hYu

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFin
section
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenFinH

variable {n : ℕ}

theorem blkDm_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (blkDm M).map f = blkDm (M.map f) := by
  ext i j; rfl

theorem blkDm_one {R : Type} [CommRing R] : blkDm (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  unfold blkDm
  rw [Matrix.submatrix_one_equiv, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]

theorem det_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    f M.det = (M.map f).det := by
  rw [RingHom.map_det]; rfl

end PositivityTheory.Rg.Sw.Glob.GenFinH

namespace PositivityTheory.Rg.Sw.Glob

open GenFinH

theorem kInFin_of (hU : UnitD) (hL : LocFin) (hGL : GlueLevi) (hGW : GlueW) (hUA : UnitAE) : KInFin := by
  intro D n k hk hreal
  choose a I hgood using fun v => hL D n k hk v
  obtain ⟨m, hm, hmv, hmr⟩ := hGL D n a (fun v => (hgood v).1) (fun v => (hgood v).2.1)
  obtain ⟨w, hw, hwv, hwr⟩ := hGW D n I
  have hmat : ∀ {S : Type} [CommRing S] (f : AE D →+* S), (mat (k * m * w)).map f = (mat k).map f * (mat m).map f * (mat w).map f := by
    intro S _ f
    show (mat k * mat m * mat w).map f = _
    rw [Matrix.map_mul, Matrix.map_mul]
  have hd : IsUnit (blkDm (mat (k * m * w))).det := by
    apply hUA D
    · intro τ
      rw [det_map, blkDm_map, hmat, hreal τ, hmr τ, hwr τ, Matrix.mul_one, Matrix.mul_one, blkDm_one, Matrix.det_one]
      exact one_ne_zero
    · intro v
      rw [det_map, blkDm_map, hmat, hmv v, hwv v]
      exact (hgood v).2.2
  have h1 : k * m * w ∈ Subgroup.closure (genSet D n) := hU D n _ hd
  have hm' : m ∈ Subgroup.closure (genSet D n) := Subgroup.subset_closure hm
  have e : k = k * m * w * w⁻¹ * m⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hw)) (Subgroup.inv_mem _ hm')

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocB
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

theorem map_nonsing_inv (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) (h : IsUnit M.det) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  obtain ⟨u, hu⟩ := h
  have h' : IsUnit (M.map f).det := by rw [← det_map, ← hu]; exact (u.isUnit.map f)
  rw [Matrix.inv_def, Matrix.inv_def, ← det_map, ← hu, Ring.inverse_unit, Matrix.map_smul' _ _ _ (fun a b => map_mul f a b)]
  have hadj : M.adjugate.map f = (M.map f).adjugate := RingHom.map_adjugate f M
  have hinv : Ring.inverse (f ↑u) = f ↑u⁻¹ := by
    rw [show f ↑u = ((Units.map f.toMonoidHom u : Sˣ) : S) from rfl, Ring.inverse_unit]; rfl
  rw [hadj, hinv]

theorem bf_cT (σ : R →+* R) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    bf (Formalism.UG.cT σ M) = Formalism.UG.cT σ (bf M) := rfl

theorem cT_fromBlocks (σ : R →+* R) (A B C D : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (fromBlocks A B C D) =
      fromBlocks (Formalism.UG.cT σ A) (Formalism.UG.cT σ C) (Formalism.UG.cT σ B) (Formalism.UG.cT σ D) := by
  unfold Formalism.UG.cT; rw [fromBlocks_map, fromBlocks_transpose]

def Uni (σ : R →+* R) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Prop := Formalism.UG.cT σ M * J2 R n * M = J2 R n

theorem Uni.mul {σ : R →+* R} {M N : Matrix (Fin (n + n)) (Fin (n + n)) R} (hM : Uni σ M) (hN : Uni σ N) :
    Uni σ (M * N) := by
  unfold Uni at *
  rw [Formalism.UG.cT_mul]
  calc Formalism.UG.cT σ N * Formalism.UG.cT σ M * J2 R n * (M * N) = Formalism.UG.cT σ N * (Formalism.UG.cT σ M * J2 R n * M) * N := by
        simp only [Matrix.mul_assoc]
    _ = J2 R n := by rw [hM, hN]

theorem caseA (hF : LocRedField) (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal]
    (hfix : 𝔪.comap σ = 𝔪) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (g : Matrix (Fin (n + n)) (Fin (n + n)) R) (hg : Uni σ g) (hgu : IsUnit g.det) :
    ∃ I : Finset (Fin n), IsUnit (blkDm (g * wIm I)).det := by
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hle : 𝔪 ≤ 𝔪.comap σ := hfix.symm ▸ le_refl _
  let σb : R ⧸ 𝔪 →+* R ⧸ 𝔪 := Ideal.quotientMap 𝔪 σ hle
  have hπσ : ∀ x, Ideal.Quotient.mk 𝔪 (σ x) = σb (Ideal.Quotient.mk 𝔪 x) := fun x => (Ideal.quotientMap_mk ..).symm
  have hσb : ∀ x, σb (σb x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← hπσ, ← hπσ, hσ]
  have hdet : IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det := by rw [← det_map]; exact hgu.map _
  let gb : GL (Fin (n + n)) (R ⧸ 𝔪) := Matrix.nonsingInvUnit _ hdet
  have hgb : gb ∈ Formalism.UG.UJ σb (J2 (R ⧸ 𝔪) n) := by
    show Formalism.UG.cT σb (g.map (Ideal.Quotient.mk 𝔪)) * J2 (R ⧸ 𝔪) n * g.map (Ideal.Quotient.mk 𝔪) = J2 (R ⧸ 𝔪) n
    have := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) hg
    simp only [Matrix.map_mul, standard_symplectic_matrix_map] at this
    rwa [cT_map σ σb _ hπσ] at this
  obtain ⟨I, hI⟩ := hF (R ⧸ 𝔪) σb hσb n gb hgb
  refine ⟨I, isUnit_of σ 𝔪 horb _ ?_ ?_⟩
  · intro hm
    have h0 : Ideal.Quotient.mk 𝔪 (blkDm (g * wIm I)).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [det_map, blkDm_map, Matrix.map_mul, wIm_map] at h0
    exact hI.ne_zero h0
  · intro hm
    have : (blkDm (g * wIm I)).det ∈ 𝔪.comap σ := hm
    rw [hfix] at this
    have h0 : Ideal.Quotient.mk 𝔪 (blkDm (g * wIm I)).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 this
    rw [det_map, blkDm_map, Matrix.map_mul, wIm_map] at h0
    exact hI.ne_zero h0

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentBlockMulAdd
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {n : ℕ}

namespace FZNH

theorem unipotent_block_mul_add {R : Type} [CommRing R] (b c : Matrix (Fin n) (Fin n) R) :
    blk4 1 b 0 1 * blk4 1 c 0 1 = blk4 (1 : Matrix (Fin n) (Fin n) R) (b + c) 0 1 := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  simp [add_comm]

theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem mat_injective : Function.Injective (mat (D := D) (n := n)) := fun x y h =>
  GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext h)

theorem mat_mul (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem nb_add {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) (b c : hermA D n) :
    nb (b + c) = nb b * nb c := by
  apply mat_injective
  rw [mat_mul, h, h, h, unipotent_block_mul_add]
  rfl

theorem nb_zero {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) : nb 0 = 1 := by
  apply mat_injective
  rw [h, mat_one]
  exact block_matrix_one

theorem nb_neg {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) (b : hermA D n) : (nb b)⁻¹ = nb (-b) := by
  have h' : nb (-b) * nb b = 1 := by rw [← nb_add h, neg_add_cancel, nb_zero h]
  exact (eq_inv_of_mul_eq_one_left h').symm

set_option synthInstance.maxHeartbeats 400000 in
theorem nb_continuous {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) : Continuous nb := by
  obtain ⟨i1, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  have he := GlobalTheory.AdelicU.isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)
  rw [he.continuous_iff, Units.continuous_iff]
  have hc : Continuous fun b : hermA D n => blk4 (1 : Mx D n n) b.1 0 1 := by
    unfold blk4
    exact (continuous_const.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const).matrix_submatrix _ _
  refine ⟨?_, ?_⟩
  · convert hc using 1
    funext b
    exact h b
  · convert hc.comp continuous_neg using 1
    funext b
    simp only [Function.comp_apply]
    rw [← map_inv, nb_neg h]
    exact h (-b)

end FZNH

open FZNH

theorem fourierZeroN : FourierZeroN := by
  intro D n ψ hψ nb lam 𝓖 hcd f hf hinv hco
  obtain ⟨hnb, hH, h𝓖, -⟩ := hcd
  funext g
  have key := hermFourierZero D n ψ hψ lam hH 𝓖 h𝓖 (fun b => f (nb b * g))
    (hf.comp ((nb_continuous hnb).mul continuous_const)) (fun x l hl => by
      obtain ⟨β, hβ⟩ := (ofHermE_bijective (D := D) (r := n)).2 ⟨l, hl⟩
      show f (nb (x + l) * g) = f (nb x * g)
      rw [show x + l = l + x from add_comm x l, nb_add hnb, mul_assoc]
      refine hinv l ⟨β, ?_⟩ _
      rw [← ofHermE_val, hβ]) (fun β => hco β g) 0
  simpa [nb_zero hnb] using key

end PositivityTheory.Rg.Sw.Glob
end
end

