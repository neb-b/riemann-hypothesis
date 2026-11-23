module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001
public import Formalism.RealPlaceAnalysis.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rhoC_mul_sign_sum (ε : Fin n → Bool) (g : Bool → ℝ) :
    ∑ a, rhoC ε a * g (ε a) = 0 := by
  have hT : ∑ a : Fin n, ∑ b : Fin n, (if a < b ∧ ε b = ε a then g (ε a) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if b < a ∧ ε b = ε a then g (ε a) else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    by_cases h : b < a ∧ ε a = ε b
    · rw [if_pos h, if_pos ⟨h.1, h.2.symm⟩, h.2]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.symm⟩)]
  have e : ∀ a, rhoC ε a * g (ε a) = (∑ b, (if a < b ∧ ε b = ε a then g (ε a) else 0) -
      ∑ b, (if b < a ∧ ε b = ε a then g (ε a) else 0)) / 2 := by
    intro a
    unfold rhoC
    rw [natCast_card_filter, natCast_card_filter]
    have e1 : ∑ b, (if a < b ∧ ε b = ε a then g (ε a) else 0) =
        g (ε a) * ∑ b, (if a < b ∧ ε b = ε a then (1:ℝ) else 0) := by
      rw [mul_sum]; simp [mul_ite]
    have e2 : ∑ b, (if b < a ∧ ε b = ε a then g (ε a) else 0) =
        g (ε a) * ∑ b, (if b < a ∧ ε b = ε a then (1:ℝ) else 0) := by
      rw [mul_sum]; simp [mul_ite]
    rw [e1, e2]; ring
  simp only [e]
  rw [← sum_div, sum_sub_distrib, hT, sub_self, zero_div]

theorem card_same_split (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => ε b = ε a).card = (univ.filter fun b => b < a ∧ ε b = ε a).card + 1 +
      (univ.filter fun b => a < b ∧ ε b = ε a).card := by
  rw [card_filter, card_filter, card_filter,
    show (1:ℕ) = ∑ b : Fin n, if b = a then 1 else 0 by simp, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b a with h | rfl | h
  · simp [h, h.ne, not_lt_of_gt h]
  · simp
  · simp [h, h.ne', not_lt_of_gt h]

theorem card_same_eq (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => ε b = ε a).card = if ε a then pOf ε else qOf ε := by
  cases h : ε a <;> simp [pOf, qOf]

theorem carU_pOf_add_qOf (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  rw [card_filter, card_filter, ← sum_add_distrib]
  have : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a; cases ε a <;> simp
  simp [this]

def carUPos (ε : Fin n → Bool) (a : Fin n) : ℕ :=
  (if ε a then 0 else pOf ε) + (univ.filter fun b => b < a ∧ ε b = ε a).card

theorem carUPos_lt (ε : Fin n → Bool) (a : Fin n) : carUPos ε a < n := by
  have h1 := card_same_split ε a
  have h2 := card_same_eq ε a
  have h3 := carU_pOf_add_qOf ε
  unfold carUPos
  cases h : ε a <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢ <;> omega

theorem carUPos_injective (ε : Fin n → Bool) : Function.Injective (carUPos ε) := by
  have key : ∀ a a' : Fin n, a < a' → ε a = ε a' → carUPos ε a < carUPos ε a' := by
    intro a a' hlt he
    unfold carUPos
    rw [he]
    have hs : (univ.filter fun b => b < a ∧ ε b = ε a') ⊂ (univ.filter fun b => b < a' ∧ ε b = ε a') := by
      rw [ssubset_iff_of_subset]
      · exact ⟨a, by simp [hlt, he], by simp⟩
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb ⊢
        exact ⟨hb.1.trans hlt, hb.2⟩
    have := card_lt_card hs
    omega
  have key2 : ∀ a a' : Fin n, ε a = true → ε a' = false → carUPos ε a < carUPos ε a' := by
    intro a a' ha ha'
    have h1 := card_same_split ε a
    have h2 := card_same_eq ε a
    unfold carUPos
    simp only [ha, ha', Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
    omega
  intro a a' hq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · by_cases he : ε a = ε a'
    · exact (key a a' h he).ne hq
    · cases ha : ε a <;> cases ha' : ε a' <;> simp_all
      · exact (key2 a' a ha' ha).ne hq.symm
      · exact (key2 a a' ha ha').ne hq
  · by_cases he : ε a' = ε a
    · exact (key a' a h he).ne hq.symm
    · cases ha : ε a <;> cases ha' : ε a' <;> simp_all
      · exact (key2 a' a ha' ha).ne hq.symm
      · exact (key2 a a' ha ha').ne hq

theorem rhoC_add_rhoHol_eq (ε : Fin n → Bool) (a : Fin n) :
    (rhoC ε + rhoHol ε) a = ((n : ℝ) - 1) / 2 - (carUPos ε a : ℝ) := by
  have h1 : ((univ.filter fun b => ε b = ε a).card : ℝ) =
      ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) + 1 +
        ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := by
    exact_mod_cast card_same_split ε a
  have h2 := card_same_eq ε a
  have h3 : (pOf ε : ℝ) + (qOf ε : ℝ) = n := by exact_mod_cast carU_pOf_add_qOf ε
  simp only [Pi.add_apply, rhoC, rhoHol, carUPos]
  cases h : ε a <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢ <;> rw [h2] at h1 <;> push_cast <;>
    linarith

theorem carU_nsq_add (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  unfold nsq dot
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply]; ring

theorem dot_rhoC_rhoHol (ε : Fin n → Bool) : dot (rhoC ε) (rhoHol ε) = 0 :=
  rhoC_mul_sign_sum ε (fun t => if t then (qOf ε : ℝ) / 2 else -(pOf ε : ℝ) / 2)

theorem nsq_rho_split (ε : Fin n → Bool) : nsq (rho n) = nsq (rhoC ε) + nsq (rhoHol ε) := by
  let σ : Fin n → Fin n := fun a => ⟨carUPos ε a, carUPos_lt ε a⟩
  have hinj : Function.Injective σ := fun a a' h => carUPos_injective ε (congrArg Fin.val h)
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  have hval : ∀ a, (rhoC ε + rhoHol ε) a = rho n (σ a) := fun a => rhoC_add_rhoHol_eq ε a
  have hs : nsq (rhoC ε + rhoHol ε) = nsq (rho n) := by
    unfold nsq dot
    simp only [hval]
    exact (Equiv.ofBijective σ hbij).sum_comp (fun b => rho n b * rho n b)
  rw [← hs, carU_nsq_add, dot_rhoC_rhoHol]; ring

section Unitary
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

end Unitary

section Value
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem pair_apply_khw {E : Fin n → Fin n → Module.End ℂ W} {μ : Fin n → ℝ} {v : W} {a b : Fin n}
    (hc : E a b * E b a - E b a * E a b = E a a - E b b) (hd : ∀ a, E a a v = (μ a : ℂ) • v)
    (hab : a < b → E a b v = 0) (hba : b < a → E b a v = 0) :
    (E a b * E b a) v = ((hwTerm μ a b : ℝ) : ℂ) • v := by
  unfold hwTerm
  rcases lt_trichotomy a b with h | rfl | h
  · have hc' : E a b * E b a = E b a * E a b + (E a a - E b b) := by
      rw [← hc]; abel
    rw [hc']
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply, hab h, map_zero,
      hd, zero_add, if_neg h.ne, if_pos h]
    push_cast
    rw [sub_smul]
  · simp only [Module.End.mul_apply, hd, map_smul, smul_smul, if_true]
    push_cast; ring_nf
  · simp [Module.End.mul_apply, hba h, h.ne', not_lt_of_gt h]

theorem casimirK_khwVec_compact (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ W}
    (hE : ∀ a b, ε a = ε b → E a b * E b a - E b a * E a b = E a a - E b b)
    {μ : Fin n → ℝ} {v : W} (hv : IsKHWVec ε E μ v) :
    casimirK ε E v = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • v := by
  have hsum : casimirK ε E v =
      ((∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), hwTerm μ a b : ℝ) : ℂ) • v := by
    unfold casimirK
    simp only [LinearMap.sum_apply]
    push_cast
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact pair_apply_khw (hE a b hb.symm) hv.1 (fun h => hv.2 a b h hb.symm) (fun h => hv.2 b a h hb)
  rw [hsum]
  congr 3
  exact sum_hwTerm (fun a b : Fin n => ε b = ε a) (fun _ => rfl) (fun a b h => h.symm) μ (rhoC ε)
    (fun a => by unfold rhoC; ring)

theorem E_comm_sgE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (a b c d : Fin n) : E a b * sgE ε cp cm c d = sgE ε cp cm c d * E a b := by
  have h1 : ∀ i j k l, E a b * (cp i j * cm k l) = (cp i j * cm k l) * E a b := by
    intro i j k l
    rw [← mul_assoc, (hEC a b i j).1, mul_assoc, (hEC a b k l).2, mul_assoc]
  unfold sgE
  split_ifs
  · rw [mul_sum, sum_mul]; exact sum_congr rfl fun x _ => h1 _ _ _ _
  · rw [mul_neg, neg_mul, mul_sum, sum_mul]; congr 1; exact sum_congr rfl fun x _ => h1 _ _ _ _
  · simp

theorem diagE_compact {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (h : ε a = ε b) :
    diagE ε E cp cm a b * diagE ε E cp cm b a - diagE ε E cp cm b a * diagE ε E cp cm a b =
      diagE ε E cp cm a a - diagE ε E cp cm b b := by
  have e1 := hE a b b a
  have e2 := sgE_comm hC ε a b b a h h.symm
  simp only [if_true] at e1 e2
  rw [sub_eq_iff_eq_add] at e1 e2
  unfold diagE
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, E_comm_sgE hEC ε a b b a,
    E_comm_sgE hEC ε b a a b, e1, e2]
  abel

theorem khw_real_identity (ε : Fin n → Bool) (δ : Fin n → ℝ) :
    nsq (δ + rhoHol ε + rhoC ε) - nsq (rhoC ε) - 2 * dot (rhoHol ε) (δ + rhoHol ε) =
      nsq (δ + rhoC ε) - nsq (rho n) := by
  rw [nsq_rho_split ε]
  have h0 := dot_rhoC_rhoHol ε
  have : nsq (δ + rhoHol ε + rhoC ε) - nsq (rhoC ε) - 2 * dot (rhoHol ε) (δ + rhoHol ε) -
      (nsq (δ + rhoC ε) - (nsq (rhoC ε) + nsq (rhoHol ε))) = 2 * dot (rhoC ε) (rhoHol ε) := by
    unfold nsq dot
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply]; ring
  rw [h0] at this
  linarith

theorem two_D_sq_khw {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hC : IsCAR cp cm) (hEC : CommutesCAR E cp cm) {δ : Fin n → ℝ} {v : W}
    (hv : IsKHWVec ε (diagE ε E cp cm) (δ + rhoHol ε) v) {c : ℂ} (hc : casimir E v = c • v) :
    (2 : ℂ) • ((dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm)) v =
      (((nsq (δ + rhoC ε) - nsq (rho n) : ℝ) : ℂ) - c) • v := by
  have hK := casimirK_khwVec_compact ε (diagE_compact hE hC hEC ε) hv
  have hs : ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε E cp cm a a v =
      ((dot (rhoHol ε) (δ + rhoHol ε) : ℝ) : ℂ) • v := by
    simp only [hv.1, smul_smul, ← sum_smul]
    congr 1
    unfold dot
    push_cast
    rfl
  rw [← LinearMap.smul_apply, two_D_sq hE hC hEC ε]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hc, hK, hs]
  rw [← khw_real_identity ε δ]
  simp only [smul_smul, sub_smul]
  push_cast
  simp only [sub_smul, mul_smul]
  abel

end Value

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lfPhysModes (ε : Fin n → Bool) : Finset (Fin (n * n)) :=
  univ.filter fun m => ε (finProdFinEquiv.symm m).1 = true ∧ ε (finProdFinEquiv.symm m).2 = false

abbrev LfIdx (ε : Fin n → Bool) : Type := {S : Finset (Fin (n * n)) // S ⊆ lfPhysModes ε}

def lfMatFull (ε : Fin n → Bool) (a b : Fin n) : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (sgE ε cpFock cmFock a b)

def lfMat (ε : Fin n → Bool) (a b : Fin n) : Matrix (LfIdx ε) (LfIdx ε) ℂ :=
  (lfMatFull ε a b).submatrix Subtype.val Subtype.val

def lfP (i a : Fin n) : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpFock i a)

theorem lf_toMatrix_cp (i a : Fin n) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpFock i a) = lfP i a := rfl

theorem lf_toMatrix_cm (i a : Fin n) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cmFock i a) = (lfP i a)ᵀ := by
  ext T S
  simp only [LinearMap.toMatrix_apply, lfP, transpose_apply]
  exact lf_repr_cm_eq (i, a) S T

theorem fockMatrix_conjTranspose_eq_transpose (i a : Fin n) : (lfP i a)ᴴ = (lfP i a)ᵀ := by
  ext T S
  simp only [conjTranspose_apply, transpose_apply, lfP, LinearMap.toMatrix_apply]
  exact lf_repr_cp_star (i, a) T S

theorem fockMatrix_transpose_conjTranspose (i a : Fin n) : (lfP i a)ᵀᴴ = lfP i a := by
  rw [← fockMatrix_conjTranspose_eq_transpose, Matrix.conjTranspose_conjTranspose]

theorem lfMatFull_eq (ε : Fin n → Bool) (a b : Fin n) : lfMatFull ε a b =
    if ε a = true ∧ ε b = true then ∑ x ∈ minusIdx ε, lfP a x * (lfP b x)ᵀ
    else if ε a = false ∧ ε b = false then -∑ i ∈ plusIdx ε, lfP i b * (lfP i a)ᵀ
    else 0 := by
  unfold lfMatFull sgE
  split_ifs <;> simp only [map_sum, map_neg, map_zero, LinearMap.toMatrix_mul, lf_toMatrix_cp, lf_toMatrix_cm]

theorem lfMatFull_kRel (ε : Fin n → Bool) : Formalism.REAL.KRel ε (lfMatFull ε) := by
  intro a b c d hab hcd
  have h := congrArg (LinearMap.toMatrix (fockBasis n) (fockBasis n))
    (sgE_comm isCAR_fock ε a b c d hab hcd)
  split_ifs at h ⊢ <;> simpa only [lfMatFull, map_sub, map_zero, LinearMap.toMatrix_mul] using h

theorem lfMatFull_conjTranspose (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    lfMatFull ε b a = (lfMatFull ε a b)ᴴ := by
  rw [lfMatFull_eq, lfMatFull_eq]
  simp only [h]
  split_ifs <;> simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, fockMatrix_conjTranspose_eq_transpose,
    fockMatrix_transpose_conjTranspose, Matrix.conjTranspose_neg]

theorem lf_mem_phys (ε : Fin n → Bool) (i a : Fin n) :
    finProdFinEquiv (i, a) ∈ lfPhysModes ε ↔ ε i = true ∧ ε a = false := by
  simp only [lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]

theorem lf_cm_phys {ε : Fin n → Bool} (i a : Fin n) {S : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) :
    ∃ c : ℂ, ∃ U, U ⊆ lfPhysModes ε ∧ cmFock i a (fockBasis n S) = c • fockBasis n U := by
  by_cases hx : finProdFinEquiv (i, a) ∈ S
  · obtain ⟨σ, -, h1, -⟩ := lf_cm_basis_of_mem (x := (i, a)) hx
    exact ⟨σ, S.erase (finProdFinEquiv (i, a)), (Finset.erase_subset _ _).trans hS, h1⟩
  · exact ⟨0, S, hS, by rw [zero_smul]; exact lf_cm_basis_of_not_mem (x := (i, a)) hx⟩

theorem lf_cp_phys {ε : Fin n → Bool} {i a : Fin n} (hia : ε i = true ∧ ε a = false)
    {S : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) :
    ∃ c : ℂ, ∃ U, U ⊆ lfPhysModes ε ∧ cpFock i a (fockBasis n S) = c • fockBasis n U := by
  by_cases hx : finProdFinEquiv (i, a) ∈ S
  · exact ⟨0, S, hS, by rw [zero_smul]; exact lf_cp_basis_of_mem (x := (i, a)) hx⟩
  · obtain ⟨σ, -, h1, -⟩ := lf_cp_cm_basis (x := (i, a)) hx
    exact ⟨σ, insert (finProdFinEquiv (i, a)) S, Finset.insert_subset ((lf_mem_phys ε i a).2 hia) hS, h1⟩

theorem lf_cpcm_repr {ε : Fin n → Bool} {i a : Fin n} (j b : Fin n) (hia : ε i = true ∧ ε a = false)
    {S T : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) (hT : ¬ T ⊆ lfPhysModes ε) :
    (fockBasis n).repr ((cpFock i a * cmFock j b) (fockBasis n S)) T = 0 := by
  obtain ⟨c, U, hU, hcm⟩ := lf_cm_phys (ε := ε) j b hS
  obtain ⟨c', U', hU', hcp⟩ := lf_cp_phys hia hU
  have e : (cpFock i a * cmFock j b) (fockBasis n S) = (c * c') • fockBasis n U' := by
    show cpFock i a (cmFock j b (fockBasis n S)) = _
    rw [hcm, map_smul, hcp, smul_smul]
  rw [e, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
  rintro rfl
  exact hT hU'

theorem lfMatFull_eq_zero (ε : Fin n → Bool) (a b : Fin n) {S T : Finset (Fin (n * n))}
    (hS : S ⊆ lfPhysModes ε) (hT : ¬ T ⊆ lfPhysModes ε) : lfMatFull ε a b T S = 0 := by
  rw [lfMatFull, LinearMap.toMatrix_apply]
  unfold sgE
  split_ifs with h1 h2
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    exact lf_cpcm_repr b x ⟨h1.1, by simpa [minusIdx] using hx⟩ hS hT
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Finsupp.coe_neg, Pi.neg_apply,
      Finsupp.coe_finsetSum, Finset.sum_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    exact lf_cpcm_repr i a ⟨by simpa [plusIdx] using hi, h2.2⟩ hS hT
  · simp

theorem lfMat_mul_apply (ε : Fin n → Bool) (a b c d : Fin n) (T S : LfIdx ε) :
    (lfMat ε a b * lfMat ε c d) T S = (lfMatFull ε a b * lfMatFull ε c d) T.1 S.1 := by
  simp only [Matrix.mul_apply, lfMat, Matrix.submatrix_apply]
  have key : ∑ U : Finset (Fin (n * n)), lfMatFull ε a b T.1 U * lfMatFull ε c d U S.1 =
      ∑ U ∈ Finset.univ.filter (fun U : Finset (Fin (n * n)) => U ⊆ lfPhysModes ε),
        lfMatFull ε a b T.1 U * lfMatFull ε c d U S.1 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro U _ hU
    have hU' : ¬ U ⊆ lfPhysModes ε := by simpa using hU
    rw [lfMatFull_eq_zero ε c d S.2 hU', mul_zero]
  rw [key, Finset.sum_subtype (p := fun U : Finset (Fin (n * n)) => U ⊆ lfPhysModes ε) _ (fun U => by simp)]

theorem lfMat_kRel (ε : Fin n → Bool) : Formalism.REAL.KRel ε (lfMat ε) := by
  intro a b c d hab hcd
  ext T S
  have h := congrFun (congrFun (lfMatFull_kRel ε a b c d hab hcd) T.1) S.1
  simp only [Matrix.sub_apply, lfMat_mul_apply] at h ⊢
  split_ifs at h ⊢ <;> simpa only [lfMat, Matrix.submatrix_apply, Matrix.zero_apply] using h

theorem lfMat_conjTranspose (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    lfMat ε b a = (lfMat ε a b)ᴴ := by
  ext T S
  simp only [lfMat, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  rw [lfMatFull_conjTranspose ε h, Matrix.conjTranspose_apply]

theorem lfMat_basis (ε : Fin n → Bool) (a b : Fin n) (S : LfIdx ε) :
    sgE ε cpFock cmFock a b (fockBasis n S.1) = ∑ T : LfIdx ε, lfMat ε a b T S • fockBasis n T.1 := by
  have key : sgE ε cpFock cmFock a b (fockBasis n S.1) =
      ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin (n * n)) => T ⊆ lfPhysModes ε),
        (fockBasis n).repr (sgE ε cpFock cmFock a b (fockBasis n S.1)) T • fockBasis n T := by
    conv_lhs => rw [← (fockBasis n).sum_repr (sgE ε cpFock cmFock a b (fockBasis n S.1))]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro T _ hT
    have hT' : ¬ T ⊆ lfPhysModes ε := by simpa using hT
    have h0 := lfMatFull_eq_zero ε a b S.2 hT'
    rw [lfMatFull, LinearMap.toMatrix_apply] at h0
    rw [h0, zero_smul]
  rw [key, Finset.sum_subtype (p := fun T : Finset (Fin (n * n)) => T ⊆ lfPhysModes ε) _ (fun T => by simp)]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [lfMat, lfMatFull, Matrix.submatrix_apply, LinearMap.toMatrix_apply]

theorem lfMat_mulVec_single (ε : Fin n → Bool) (a b : Fin n) (S : LfIdx ε) (c : ℂ)
    (h : sgE ε cpFock cmFock a b (fockBasis n S.1) = c • fockBasis n S.1) :
    lfMat ε a b *ᵥ Pi.single S 1 = c • Pi.single S 1 := by
  ext T
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [lfMat, Matrix.submatrix_apply, lfMatFull, LinearMap.toMatrix_apply]
  rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Pi.smul_apply, Finsupp.single_apply,
    Pi.single_apply]
  by_cases hTS : T = S
  · subst hTS
    simp
  · rw [if_neg (fun h' => hTS (Subtype.ext h'.symm)), if_neg hTS]

end ReciprocityTheory.ChartRestriction.DS
end
end

