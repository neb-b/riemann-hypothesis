module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0130
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocSupStep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianPerturbedVectorOrthogonal
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section N2d

variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (ν : Fin (2 * (m + 1) + k + 1) → ℂ)

def VpF : Fin (2 * (m + 1) + k + 1) → ℂ := fun p =>
  bvec (esI k (m + 1) i) p - ν p + (-(herm (Hpk k (m + 1)) ν ν) / 2) * bvec (eI k (m + 1) i) p

theorem eI_ne_esI (a b : Fin (m + 1)) : eI k (m + 1) a ≠ esI k (m + 1) b := by
  intro h; have := congrArg Fin.val h; simp [eI, esI] at this; have := a.isLt; have := b.isLt; omega

theorem VpF_star (hν : inWb k (m + 1) ν) (q : Fin (2 * (m + 1) + k + 1)) (hq : m + 1 + k < q.val) :
    VpF m i ν q = if (NFOne.sg k (m + 1) q).val = i.val then 1 else 0 := by
  unfold VpF
  rw [hν q (Or.inr hq)]
  have hq2 : q ≠ eI k (m + 1) i := by intro h; rw [h] at hq; simp [eI] at hq; omega
  by_cases h : q = esI k (m + 1) i
  · rw [if_pos (by rw [sg_val', h]; simp [esI]; omega)]; simp [bvec, h, Pi.single_apply, hq2, Ne.symm (eI_ne_esI m i i)]
  · rw [if_neg]
    · simp [bvec, Pi.single_apply, h, hq2]
    · intro h'; apply h; ext; rw [sg_val'] at h'; simp [esI]; omega

theorem VpF_iso (hν : inWb k (m + 1) ν) : herm (Hpk k (m + 1)) (VpF m i ν) (VpF m i ν) = 0 := by
  have hi := i.isLt
  set γ : ℂ := -(herm (Hpk k (m + 1)) ν ν) / 2 with hγ
  have hpt : ∀ l, star (VpF m i ν l) * (WeylGroupFacts.sgn k (m + 1) l * VpF m i ν (WeylGroupFacts.tau k (m + 1) l)) =
      (if l = eI k (m + 1) i then star γ else 0) + (if l = esI k (m + 1) i then γ else 0) +
        star (ν l) * (WeylGroupFacts.sgn k (m + 1) l * ν (WeylGroupFacts.tau k (m + 1) l)) := by
    intro l
    unfold VpF
    rw [← hγ]
    by_cases h1 : l = eI k (m + 1) i
    · subst h1
      rw [tau_eI, hν (eI k (m + 1) i) (Or.inl (by simp only [eI]; omega)), hν (esI k (m + 1) i) (Or.inr (by simp [esI]; omega)),
        sgn_one _ (by simp [eI]; omega)]
      simp [bvec, Pi.single_apply, eI_ne_esI]
    by_cases h2 : l = esI k (m + 1) i
    · subst h2
      rw [tau_esI, hν (eI k (m + 1) i) (Or.inl (by simp only [eI]; omega)), hν (esI k (m + 1) i) (Or.inr (by simp [esI]; omega)),
        sgn_one _ (by simp [esI]; omega)]
      simp [bvec, Pi.single_apply, Ne.symm (eI_ne_esI m i i)]
    by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
    · have ht : WeylGroupFacts.tau k (m + 1) l = l := by ext; rw [tau_val]; split_ifs <;> omega
      rw [ht]
      simp [bvec, Pi.single_apply, h1, h2]
      try ring
    · rw [hν l (by omega)]
      have ha : bvec (esI k (m + 1) i) l = 0 := by simp [bvec, Pi.single_apply, h2]
      have hb : bvec (eI k (m + 1) i) l = 0 := by simp [bvec, Pi.single_apply, h1]
      rw [ha, hb]
      simp [h1, h2]
  rw [herm_expand, Finset.sum_congr rfl (fun l _ => hpt l), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), ← herm_expand]
  have hreal : star (herm (Hpk k (m + 1)) ν ν) = herm (Hpk k (m + 1)) ν ν := (herm_swap k (m + 1) ν ν).symm
  rw [hγ, star_div₀, star_neg, hreal]
  simp
  try ring

theorem VpF_esI (hν : inWb k (m + 1) ν) (c : Fin (m + 1)) (hc : c ≠ i) :
    herm (Hpk k (m + 1)) (VpF m i ν) (bvec (esI k (m + 1) c)) = 0 := by
  rw [herm_bvec_esI]
  unfold VpF
  rw [hν _ (Or.inl (by simp only [eI]; omega))]
  have h1 : eI k (m + 1) c ≠ eI k (m + 1) i := by
    intro h; apply hc; ext; have := congrArg Fin.val h; simpa [eI] using this
  simp [bvec, Pi.single_apply, h1, eI_ne_esI]

theorem hermitian_perturbed_vector_orthogonal (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (hz : inWb k (m + 1) z') (hν : inWb k (m + 1) ν)
    (hzν : herm (Hpk k (m + 1)) z' ν = 0) : herm (Hpk k (m + 1)) z' (VpF m i ν) = 0 := by
  have : herm (Hpk k (m + 1)) z' (VpF m i ν) = -herm (Hpk k (m + 1)) z' ν := by
    rw [herm_expand, herm_expand, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
    · unfold VpF
      have h1 : l ≠ eI k (m + 1) i := by intro h; rw [h] at hW; simp [eI] at hW; omega
      have h2 : l ≠ esI k (m + 1) i := by intro h; rw [h] at hW; simp [esI] at hW; omega
      simp [bvec, Pi.single_apply, h1, h2]
    · rw [hz (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp
  rw [this, hzν, neg_zero]

theorem bvec_esI_iso (b c : Fin (m + 1)) :
    herm (Hpk k (m + 1)) (bvec (esI k (m + 1) b)) (bvec (esI k (m + 1) c)) = 0 := by
  rw [herm_bvec_esI]; simp [bvec, Pi.single_apply, Ne.symm (eI_ne_esI m c b)]

theorem bvec_esI_star (c : Fin (m + 1)) (q : Fin (2 * (m + 1) + k + 1)) :
    bvec (esI k (m + 1) c) q = if (NFOne.sg k (m + 1) q).val = c.val then 1 else 0 := by
  have := c.isLt
  simp only [bvec, Pi.single_apply]
  by_cases h : q = esI k (m + 1) c
  · rw [if_pos h, if_pos (by rw [sg_val', h]; simp [esI]; omega)]
  · rw [if_neg h, if_neg]; intro h'; apply h; ext; rw [sg_val'] at h'; simp [esI]; have := q.isLt; omega

end N2d

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalNablaHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section ring

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

private theorem natDegree_prod_X_add_C_le_card (S : Finset ℕ) (a : ℕ → ℂ) :
    (∏ i ∈ S, (X + C (a i))).natDegree ≤ S.card := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun i _ => (Polynomial.natDegree_X_add_C (a i)).le)).trans ?_
  simp

private theorem xpol_natDegree_le (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree ≤ P.k - 1 := by
  have h2 := natDegree_prod_X_add_C_le_card (Finset.Icc 1 (P.k - 1)) (fun i => ((M.rho P ρ i : ℝ) : ℂ))
  beta_reduce at h2
  have h3 : (Finset.Icc 1 (P.k - 1)).card = P.k - 1 := by rw [Nat.card_Icc]; omega
  unfold xpol
  omega

theorem xpol_half_deg (P : M.Par) (hk : 1 ≤ P.k) (ρ : M.Ty P) (s : ℂ) :
    ((xpol P ρ) * (X + C s)).natDegree ≤ P.k := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_add_C]
  have := xpol_natDegree_le P ρ
  omega

theorem xpol_halfm_deg (P : M.Par) (hk : 1 ≤ P.k) (ρ : M.Ty P) (s : ℂ) :
    ((xpol P ρ) * (X - C s)).natDegree ≤ P.k := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_sub_C]
  have := xpol_natDegree_le P ρ
  omega

theorem xpol_deg (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree ≤ P.k := by
  have := xpol_natDegree_le P ρ
  omega

private theorem xepol_natDegree_le (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    (xepol P l ρ).natDegree ≤ P.k - 2 := by
  have h2 := natDegree_prod_X_add_C_le_card (Finset.Icc 1 (P.k - 1) \ {l}) (fun i => ((M.rho P ρ i : ℝ) : ℂ))
  beta_reduce at h2
  have h3 : (Finset.Icc 1 (P.k - 1) \ {l}).card = P.k - 2 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl, Nat.card_Icc]; omega
  unfold xepol
  omega

theorem xepol_deg (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) (c : ℂ) :
    (C c * xepol P l ρ).natDegree ≤ P.k := by
  have := xepol_natDegree_le P hl ρ
  exact (Polynomial.natDegree_C_mul_le c _).trans (by omega)

theorem xepol_coeff (P : M.Par) (hk : 2 ≤ P.k) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) (c : ℂ) :
    (C c * xepol P l ρ).coeff (P.k - 1) = 0 := by
  have := xepol_natDegree_le P hl ρ
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le c _) (by omega))

theorem nab_eq (d : Q.NFData P A) (hR : d.Rel) (hk : 2 ≤ P.k) :
    ∃ (lam : Fin (P.k + 1) → ℂ) (e : M.Ty P → ℂ),
      d.L.nab = ∑ ρ, d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0)) -
        e ρ • (d.κ (dl ρ) * d.L.ζb)) := by
  classical
  obtain ⟨lam, hlam⟩ := lag_weights P.k
  refine ⟨lam, fun ρ => ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1), ?_⟩
  have key : ∀ ρ, ∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0) =
      -(d.L.GG * d.κ (dl ρ) * d.L.nab) +
        ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1) • (-(d.κ (dl ρ) * d.L.ζb)) := by
    intro ρ
    simp_rw [e10 d hR ρ, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    rw [comb hlam _ (xpol_deg P ρ), comb hlam _ (xpol_half_deg P (by omega) ρ _), xpol_coeff, one_smul]
    have h3 : ∑ j : Fin (P.k + 1), ∑ l ∈ Finset.Icc 1 (P.k - 1), ∑ ρ0,
        lam j • ((C (fl P l ρ ρ0) * xepol P l ρ0).eval ((j : ℕ) : ℂ) • (d.SS l * d.κ (dl ρ0))) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun ρ0 _ => ?_
      rw [comb hlam _ (xepol_deg P hl ρ0 _), xepol_coeff P hk hl, zero_smul]
    rw [h3, add_zero]
  have hρ : ∀ ρ, d.κ (dl ρ) * d.L.nab = d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) *
      d.QQ ((j : ℕ) : ℂ) 1 0)) - ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1) • (d.κ (dl ρ) * d.L.ζb)) := by
    intro ρ
    rw [key ρ, smul_neg, neg_add, neg_neg, neg_neg, add_sub_cancel_right, ← mul_assoc, ← mul_assoc,
      d.L.GGi_GG, one_mul]
  calc d.L.nab = (∑ ρ, d.κ (dl ρ)) * d.L.nab := by rw [sum_dl, one_mul]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => hρ ρ

theorem nabs_eq (d : Q.NFData P A) (hR : d.Rel) (hk : 2 ≤ P.k) :
    ∃ (lam : Fin (P.k + 1) → ℂ) (e : M.Ty P → ℂ),
      d.L.nabs = ∑ ρ, d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1)) -
        e ρ • (d.κ (dl ρ) * d.L.ζ)) := by
  classical
  obtain ⟨lam, hlam⟩ := lag_weights P.k
  refine ⟨lam, fun ρ => ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1), ?_⟩
  have key : ∀ ρ, ∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1) =
      -(d.L.GG * d.κ (dl ρ) * d.L.nabs) +
        ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1) • (-(d.κ (dl ρ) * d.L.ζ)) := by
    intro ρ
    simp_rw [e01 d hR ρ, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    rw [comb hlam _ (xpol_deg P ρ), comb hlam _ (xpol_halfm_deg P (by omega) ρ _), xpol_coeff, one_smul]
    have h3 : ∑ j : Fin (P.k + 1), ∑ l ∈ Finset.Icc 1 (P.k - 1),
        lam j • ((xepol P l ρ).eval ((j : ℕ) : ℂ) • (d.κ (dl ρ) * star (d.SS l))) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hd : (xepol P l ρ).natDegree ≤ P.k := by rw [xepol_natDegree P hl]; omega
      rw [comb hlam _ hd, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [xepol_natDegree P hl]; omega),
        zero_smul]
    rw [h3, add_zero]
  have hρ : ∀ ρ, d.κ (dl ρ) * d.L.nabs = d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) *
      d.QQ ((j : ℕ) : ℂ) 0 1)) - ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1) • (d.κ (dl ρ) * d.L.ζ)) := by
    intro ρ
    rw [key ρ, smul_neg, neg_add, neg_neg, neg_neg, add_sub_cancel_right, ← mul_assoc, ← mul_assoc,
      d.L.GGi_GG, one_mul]
  calc d.L.nabs = (∑ ρ, d.κ (dl ρ)) * d.L.nabs := by rw [sum_dl, one_mul]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => hρ ρ

end ring

section fst

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem fst_mul' (a b : Q.Pr V) : (a * b).1 = a.1 * b.1 := rfl
theorem fst_neg' (a : Q.Pr V) : (-a).1 = -a.1 := rfl
theorem fst_sub' (a b : Q.Pr V) : (a - b).1 = a.1 - b.1 := rfl
theorem fst_smul' (c : ℂ) (a : Q.Pr V) : (c • a).1 = c • a.1 := by
  first
  | rfl
  | exact Prod.smul_fst _ _
theorem fst_sum' {ι : Type*} (s : Finset ι) (f : ι → Q.Pr V) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  first
  | exact Prod.fst_sum
  | exact map_sum (AddMonoidHom.fst (Module.End ℂ V) (Module.End ℂ V)ᵐᵒᵖ) f s

end fst

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]

theorem radDZ_expr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (hT : ∀ (Y : ℂ) (a b : Fin 2), RadDZ P Bs (X.t Y a b))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (lam : Fin (P.k + 1) → ℂ) (c : ℂ) (j0 : Fin 6) (hj0 : j0 = 0 ∨ j0 = 2) (a b : Fin 2) (ρ : M.Ty P) :
    RadDZ P Bs (X.fn 5 * (-(∑ j : Fin (P.k + 1), lam j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) a b)) -
      c • ((d.κ (dl ρ)).1 * X.fn j0))) := by
  have hpl := hH.1
  refine radDZ_fn_left P Bs hpl X 5 (Or.inr (Or.inr rfl)) ?_
  rw [sub_eq_add_neg]
  refine radDZ_add (radDZ_neg (radDZ_sum _ _ fun j _ => radDZ_smul ?_ _)) (radDZ_neg (radDZ_smul ?_ _))
  · exact radDZ_kap_left P Bs X d hH e he hk ρ (hT _ a b)
  · refine radDZ_kap_left P Bs X d hH e he hk ρ ?_
    simpa using radDZ_fn_left P Bs hpl X j0 (hj0.imp_right Or.inl) (radDZ_one P Bs)

theorem local_nabla_holds : GTCLNab := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH hT e he hk
  have hpl := hH.1
  have hk2 := hH.2.1
  have hL := hH.2.2.2.1
  have hR := hH.2.2.2.2.2.1
  have hQ := hH.2.2.2.2.2.2
  have hQt : ∀ (Y : ℂ) (a b : Fin 2), (d.QQ Y a b).1 = X.t Y a b := by
    intro Y a b
    rw [← hQ Y]
    rfl
  have hGGi : d.L.GGi.1 = X.fn 5 := by rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; rfl
  have hζb : d.L.ζb.1 = X.fn 2 := by rw [hL.2.2.2.2.2.2.2.2.1]; rfl
  have hζ : d.L.ζ.1 = X.fn 0 := by rw [hL.2.2.2.2.2.2.1]; rfl
  obtain ⟨lam, c, hn⟩ := nab_eq d hR hk2
  obtain ⟨lam', c', hns⟩ := nabs_eq d hR hk2
  constructor
  · rw [hn, fst_sum']
    refine radDZ_sum _ _ fun ρ _ => ?_
    rw [fst_mul', fst_sub', fst_neg', fst_sum', fst_smul', fst_mul', hGGi, hζb]
    have hs : ∀ j : Fin (P.k + 1), (lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0)).1 =
        lam j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) 1 0) := by
      intro j; rw [fst_smul', fst_mul', hQt]
    simp_rw [hs]
    exact radDZ_expr P Bs X d hH hT e he hk lam (c ρ) 2 (Or.inr rfl) 1 0 ρ
  · rw [hns, fst_sum']
    refine radDZ_sum _ _ fun ρ _ => ?_
    rw [fst_mul', fst_sub', fst_neg', fst_sum', fst_smul', fst_mul', hGGi, hζ]
    have hs : ∀ j : Fin (P.k + 1), (lam' j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1)).1 =
        lam' j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) 0 1) := by
      intro j; rw [fst_smul', fst_mul', hQt]
    simp_rw [hs]
    exact radDZ_expr P Bs X d hH hT e he hk lam' (c' ρ) 0 (Or.inl rfl) 0 1 ρ

end main

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem local_nabla_holds : GTCLNab := LNab.local_nabla_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCChain
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem tsum_mix {ι W : Type} (Wd : Finset W) (m : ι → ℝ) (hm0 : ∀ i, 0 ≤ m i) (hms : Summable m)
    (hM : 0 < ∑' i, m i) (q : ι → W → ℝ) (hq : ∀ i, TB.IsProb Wd (q i)) :
    ∃ θ : W → ℝ, TB.IsProb Wd θ ∧ ∀ N : W → ℝ,
      Summable (fun i => m i * ∑ u ∈ Wd, q i u * N u) ∧
      ∑' i, m i * ∑ u ∈ Wd, q i u * N u = (∑' i, m i) * ∑ u ∈ Wd, θ u * N u := by
  set M := ∑' i, m i with hMdef
  have hq1 : ∀ i u, q i u ≤ 1 := by
    intro i u
    by_cases hu : u ∈ Wd
    · rw [← (hq i).2.2]
      exact Finset.single_le_sum (fun a _ => (hq i).1 a) hu
    · rw [(hq i).2.1 u hu]
      exact zero_le_one
  have hsu : ∀ u, Summable (fun i => m i * q i u) := fun u =>
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hm0 i) ((hq i).1 u))
      (fun i => mul_le_of_le_one_right (hm0 i) (hq1 i u)) hms
  refine ⟨fun u => (∑' i, m i * q i u) / M, ⟨fun u => div_nonneg (tsum_nonneg fun i =>
    mul_nonneg (hm0 i) ((hq i).1 u)) hM.le, fun u hu => ?_, ?_⟩, fun N => ⟨?_, ?_⟩⟩
  · simp [(hq _).2.1 u hu]
  · rw [← Finset.sum_div, div_eq_one_iff_eq hM.ne', ← Summable.tsum_finsetSum (fun u _ => hsu u)]
    refine tsum_congr fun i => ?_
    rw [← Finset.mul_sum, (hq i).2.2, mul_one]
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    exact summable_sum fun u _ => (hsu u).mul_right (N u)
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Summable.tsum_finsetSum (fun u _ => (hsu u).mul_right (N u))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [tsum_mul_right]
    field_simp

theorem mL_pat {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) :
    crystallineComparison.mL K L σ * ∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K = ∏ v ∈ crystallineComparison.pat L σ, L v ^ K := by
  have h1 : ∀ v ∈ crystallineComparison.pat L σ, crystallineComparison.mfac K (L v) ‖σ v‖ * ‖σ v‖ ^ K = L v ^ K := by
    intro v hv
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have ha : 0 < ‖σ v‖ := lt_of_le_of_lt (hL v) hv
    have hle : (L v / ‖σ v‖) ^ K ≤ 1 :=
      pow_le_one₀ (div_nonneg (hL v) ha.le) ((div_le_one ha).mpr hv.le)
    unfold crystallineComparison.mfac
    rw [if_neg ha.ne', min_eq_right hle, div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ ha.ne'
  have h2 : ∀ v ∈ (Finset.univ : Finset (Fin f)), v ∉ crystallineComparison.pat L σ → crystallineComparison.mfac K (L v) ‖σ v‖ = 1 := by
    intro v _ hv
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
    unfold crystallineComparison.mfac
    split_ifs with h0
    · rfl
    · have ha : 0 < ‖σ v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      exact min_eq_left (one_le_pow₀ ((one_le_div ha).mpr hv))
  unfold crystallineComparison.mL
  rw [← Finset.prod_subset (Finset.subset_univ _) h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl h1

theorem bound_mL {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) (X Y : ℝ)
    (h : (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * X ≤ (∏ v ∈ crystallineComparison.pat L σ, L v ^ K) * Y) : X ≤ crystallineComparison.mL K L σ * Y := by
  have hP : 0 < ∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K := by
    refine Finset.prod_pos fun v hv => pow_pos ?_ _
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact lt_of_le_of_lt (hL v) hv
  rw [← mL_pat K L hL σ] at h
  refine le_of_mul_le_mul_left ?_ hP
  calc (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * X
      ≤ crystallineComparison.mL K L σ * (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * Y := h
    _ = (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * (crystallineComparison.mL K L σ * Y) := by ring

theorem mL_nonneg {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) : 0 ≤ crystallineComparison.mL K L σ := Finset.prod_nonneg fun v _ => by
    unfold crystallineComparison.mfac
    split_ifs
    · exact zero_le_one
    · exact le_min zero_le_one (pow_nonneg (div_nonneg (hL v) (norm_nonneg _)) _)

theorem mL_zero {f : ℕ} (K : ℕ) (L : Fin f → ℝ) : crystallineComparison.mL K L 0 = 1 := by
  unfold crystallineComparison.mL crystallineComparison.mfac
  simp

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem prod_gN (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i : ℕ) (w : S.W) (p q : Fin S.f → C.LPt) :
    ∏ v, KB.gN S v ε i (w.1 v) (p v) (q v) =
      (∏ v, S.gramLoc v ε i (w.1 v) (p v) (q v)) / (C.Word.size S.P w.1 : ℂ) := by
  unfold KB.gN C.Word.size
  rw [Finset.prod_div_distrib]
  congr 1
  push_cast
  rfl

theorem nstV_eq (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : Fin S.f → ℂ) :
    KB.NstV S ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' *
      ∏ v, KB.gN S v ε i (w.1 v) (C.loc (S.σ v) h ++ [(s, t v)]) (C.loc (S.σ v) h' ++ [(s, t' v)]) := by
  unfold KB.NstV
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h' _ => ?_
  have e := prod_gN S ε i w (fun v => C.loc (S.σ v) h ++ [(s, t v)]) (fun v => C.loc (S.σ v) h' ++ [(s, t' v)])
  rw [e, mul_div_assoc]

end setting

end

end Formalism.FourierDecayAlt.P.PBC
end

