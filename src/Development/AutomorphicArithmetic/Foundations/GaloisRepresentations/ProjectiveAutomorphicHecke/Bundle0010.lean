module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClrHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTrRho
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pTrRho_of :
    UpperTheory.Gal.CertificateRingHomMap.TrRho := by
  intro E _ _ _ n W g
  set e := GlobalTheory.BCT.TrKer.wspEquivVV W
  set F : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] GlobalTheory.BCT.TrKer.Wsp W :=
    PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (W v) (g v)) with hF
  have hcomp : Formalism.L2.DIV.rhoK W g ∘ₗ (e : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] _) =
      (e : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] _) ∘ₗ F := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext (fun u => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hF, PiTensorProduct.map_tprod]
    dsimp only [e, GlobalTheory.BCT.TrKer.wspEquivVV, LinearEquiv.ofLinear_apply]
    show Formalism.L2.DIV.rhoK W g (GlobalTheory.BCT.TrKer.wspToVV W (PiTensorProduct.tprod ℂ u)) =
      GlobalTheory.BCT.TrKer.wspToVV W (PiTensorProduct.tprod ℂ _)
    rw [GlobalTheory.BCT.TrKer.wspToVV_tprod, GlobalTheory.BCT.TrKer.wspToVV_tprod, rhoK_tenMul]
  have hconj : Formalism.L2.DIV.rhoK W g = e.conj F := by
    rw [LinearEquiv.conj_apply, ← hcomp]
    refine LinearMap.ext (fun x => ?_)
    simp
  rw [hconj, LinearMap.trace_conj', hF, GlobalTheory.BCT.TrKer.trace_piMap]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTrSch
section
noncomputable section

open Matrix Polynomial

namespace UpperTheory.Gal.CertificateRingHomMap

open UpperTheory.Gal.Schur in
private theorem den_eq {n : ℕ} (t : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))).det = vdm t := by
  have hm : (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))) =
      Matrix.projVandermonde (fun _ => (1 : ℂ)) t := by
    ext i j
    simp only [Matrix.projVandermonde_apply, one_pow, one_mul, Matrix.of_apply, Fin.val_rev]
    congr 1
    omega
  rw [hm, Matrix.det_projVandermonde]
  simp only [one_mul, vdm]

open UpperTheory.Gal.Schur in
private theorem num_eq' {n : ℕ} (l : Fin n → ℤ) (t : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => t i ^ (l j + (n - 1 - (j : ℕ) : ℕ))).det =
      altnZ (fun i => l i + n - 1 - (i : ℕ)) t := by
  rw [← Matrix.det_transpose]
  unfold altnZ
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  congr 1
  have := i.isLt
  omega

theorem pTrSch_of : TrSch := by
  intro n lam m hpos g t ht hchar
  obtain ⟨d, hd0, hdchar, htr⟩ := GlobalTheory.ContraChar.exists_eig lam g
  have key : ∀ e : Fin n → ℂ, (∏ i, (X - C (e i))).roots = Multiset.map e Finset.univ.val := by
    intro e
    have he : (∏ i, (X - C (e i))) = ((Finset.univ.val.map e).map fun a => X - C a).prod := by
      rw [Multiset.map_map]
      rfl
    rw [he, Polynomial.roots_multiset_prod_X_sub_C]
  have hroots : Multiset.map d Finset.univ.val = Multiset.map t Finset.univ.val := by
    rw [← key d, ← key t, ← hdchar, ← hchar]
  obtain ⟨π, hπ⟩ := GlobalTheory.ContraChar.exists_perm_of_map_eq d t hroots
  have ht0 : ∀ i, t i ≠ 0 := fun i => by rw [← hπ i]; exact hd0 _
  have hgt : ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar n lam.w t = ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar n lam.w d := by
    rw [← GlobalTheory.ContraChar.gtChar_perm lam d hd0 π]
    congr 1
    funext i
    exact (hπ i).symm
  have hw := GlobalTheory.CompanionTheory.RmCharacter.weylChar_eq_gtChar lam.w lam.anti t ht0 ht
  rw [htr, ← hgt, ← hw]
  unfold PositivityTheory.RgBcC.weylChar
  rw [num_eq' lam.w t, den_eq t]
  rw [UpperTheory.Gal.Schur.WeylTie_holds ℂ n lam.w m (fun i => (lam.w i + m).toNat) t
    (fun i => (Int.toNat_of_nonneg (hpos i)).symm) ht ht0]
  have hp : (∏ k, t k) ^ m ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _ => ht0 i)
  exact div_mul_cancel₀ _ hp

end UpperTheory.Gal.CertificateRingHomMap

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PWtAtOf
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pWtAt_of :
    UpperTheory.Gal.CertificateRingHomMap.WtAt := by
  intro E _ _ _ n _ π
  refine ⟨⟨(AU.mk π).wt, AutSub.finPart_wt_ne_bot E n π⟩, fun W hW τ lam hlam => ?_⟩
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hT :=
    GlobalTheory.Cong.ofType_of_finPart_fixed E n π W ⊥ f hf hf0 (by
      intro k hk v g
      rw [Subgroup.mem_bot.1 hk, mul_one])
  exact hasWeightAt_unique π τ hlam (hT.wt τ)
end

