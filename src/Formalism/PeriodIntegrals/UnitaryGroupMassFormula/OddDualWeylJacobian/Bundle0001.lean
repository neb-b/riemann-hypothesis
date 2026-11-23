module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.DegreeBalance
section
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

namespace MiscB

theorem abel (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) :
    ∀ n, ∑ s ∈ Finset.range n, (s + 1) * (f s - f (s + 1)) + n * f n = ∑ s ∈ Finset.range n, f s
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← abel f hf n, add_assoc, ← Nat.mul_add,
      Nat.sub_add_cancel (hf n)]
    ring

def ext0 {k : ℕ} (ν : Fin k → ℕ) (t : ℕ) : ℕ := if h : t < k then ν ⟨t, h⟩ else 0

theorem degW_eq {k : ℕ} (ν : Fin k → ℕ) (hν : Antitone ν) : degW ν = ∑ s, ν s := by
  have hf : ∀ s, ext0 ν (s + 1) ≤ ext0 ν s := by
    intro s
    unfold ext0
    split_ifs with h1 h2
    · exact hν (Fin.mk_le_mk.2 (Nat.le_succ s))
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have h := abel (ext0 ν) hf k
  have hk : ext0 ν k = 0 := by
    unfold ext0
    simp
  rw [hk, mul_zero, add_zero] at h
  have e1 : ∑ s : Fin k, (s.val + 1) * (ν s - nuNext ν s) =
      ∑ s ∈ Finset.range k, (s + 1) * (ext0 ν s - ext0 ν (s + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => (s + 1) * (ext0 ν s - ext0 ν (s + 1))) k]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [ext0, dif_pos s.2]
    rfl
  have e2 : ∑ s : Fin k, ν s = ∑ s ∈ Finset.range k, ext0 ν s := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => ext0 ν s) k]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [ext0, dif_pos s.2]
  unfold degW
  rw [e1, e2, h]

variable {m : ℕ} {lam : Fin (m + 1) → ℤ}

theorem nu_cast (hl : Antitone lam) (t : Fin (m + 1)) : (nuOf lam t : ℤ) = lam t - lam (Fin.last m) := by
  unfold nuOf
  exact Int.toNat_of_nonneg (sub_nonneg.2 (hl (Fin.le_last t)))

theorem nu_anti (hl : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  have ha := nu_cast hl a
  have hb := nu_cast hl b
  have h := hl hab
  omega

theorem sum_nu_le (hl : Antitone lam) : ∑ t, nuOf lam t ≤ m * nuOf lam 0 := by
  rw [Fin.sum_univ_castSucc]
  have hl0 : nuOf lam (Fin.last m) = 0 := by
    unfold nuOf
    simp
  rw [hl0, add_zero]
  calc ∑ t : Fin m, nuOf lam t.castSucc ≤ ∑ _t : Fin m, nuOf lam 0 :=
        Finset.sum_le_sum fun t _ => nu_anti hl (Fin.zero_le _)
    _ = m * nuOf lam 0 := by simp

end MiscB

theorem degreeBalance : Bk := by
  intro m lam hl
  have hs : Antitone (lamStar lam) := fun i j hij => by
    unfold lamStar
    exact neg_le_neg (hl (Fin.rev_le_rev.2 hij))
  unfold expM
  rw [MiscB.degW_eq _ (MiscB.nu_anti hs), Nat.cast_sub (MiscB.sum_nu_le hl)]
  push_cast
  simp only [MiscB.nu_cast hs, MiscB.nu_cast hl]
  have hr : ∑ t : Fin (m + 1), (lamStar lam t - lamStar lam (Fin.last m)) =
      ∑ t : Fin (m + 1), (lam 0 - lam t) := by
    unfold lamStar
    rw [Fin.rev_last, ← Equiv.sum_comp Fin.revPerm (fun t => lam 0 - lam t)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Fin.revPerm_apply]
    ring
  rw [hr]
  unfold lamStar
  rw [Fin.rev_last]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end PI.OddDualWeyl
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.ExistsEqMulOfColumnSpanLe
section
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

namespace Misc

theorem sgn (K : Type) [Field K] (m : ℕ) : sgnK K m = 1 ∨ sgnK K m = -1 := by
  have h : PI.OddDualWeyl.sgnK K m =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : K) := by
    unfold PI.OddDualWeyl.sgnK PI.OddDualWeyl.revCol
    have hr : (Fin.rev : Fin (m + 1) → Fin (m + 1)) = ⇑(Fin.revPerm : Equiv.Perm (Fin (m + 1))) := rfl
    rw [hr, Matrix.det_permute', Matrix.det_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with hs | hs <;>
    simp [h, hs]

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

theorem exists_eq_mul_of_columnSpan_le {n : ℕ} (g g' : Matrix (Fin n) (Fin n) K) (h : colSpan O g ≤ colSpan O g') :
    ∃ v : Matrix (Fin n) (Fin n) O, g = g' * v.map (algebraMap O K) := by
  have h2 : Submodule.span O (Set.range fun c : Fin n => fun i => g i c) ≤
      Submodule.span O (Set.range fun c : Fin n => fun i => g' i c) := h
  have hc : ∀ c : Fin n, ∃ a : Fin n → O, ∑ j, a j • (fun i => g' i j) = fun i => g i c := by
    intro c
    have hm : (fun i => g i c) ∈ Submodule.span O (Set.range fun c : Fin n => fun i => g' i c) :=
      h2 (Submodule.subset_span ⟨c, rfl⟩)
    exact (Submodule.mem_span_range_iff_exists_fun (R := O)).1 hm
  choose a ha using hc
  refine ⟨Matrix.of fun j c => a c j, ?_⟩
  ext i c
  have hi := congrFun (ha c) i
  rw [← hi, Finset.sum_apply]
  simp only [Pi.smul_apply, Algebra.smul_def, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem colSpan_mul_le {n : ℕ} (h' : Matrix (Fin n) (Fin n) K) (v : Matrix (Fin n) (Fin n) O) :
    colSpan O (h' * v.map (algebraMap O K)) ≤ colSpan O h' := by
  unfold PI.OddDualWeyl.colSpan
  rw [Submodule.span_le]
  rintro x ⟨c, rfl⟩
  have hv : (fun i => (h' * v.map (algebraMap O K)) i c) = ∑ j, v j c • fun i => h' i j := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Algebra.smul_def, Matrix.mul_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  dsimp only
  rw [hv]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem invT_eq {n : ℕ} {g g' : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) (hg' : IsUnit g'.det)
    (u : Matrix (Fin n) (Fin n) O) (hu : g' = g * u.map (algebraMap O K)) :
    (g⁻¹)ᵀ = (g'⁻¹)ᵀ * (uᵀ).map (algebraMap O K) := by
  have hU : g⁻¹ * g' = u.map (algebraMap O K) := by
    rw [hu, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]
  have hinv : g⁻¹ = u.map (algebraMap O K) * g'⁻¹ := by
    rw [← hU, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg', Matrix.mul_one]
  rw [hinv, Matrix.transpose_mul, Matrix.transpose_map]

end Misc

theorem reverseSignUnit : SgnPM := by
  intro K _ m
  exact PI.OddDualWeyl.Misc.sgn K m

theorem columnSpanDual : DualB := by
  intro O K _ _ _ m g g' hg hg' h
  obtain ⟨v, hv⟩ := PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le (O := O) g' g h.ge
  obtain ⟨w, hw⟩ := PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le (O := O) g g' h.le
  apply le_antisymm
  · rw [PI.OddDualWeyl.Misc.invT_eq hg hg' v hv]
    exact PI.OddDualWeyl.Misc.colSpan_mul_le _ _
  · rw [PI.OddDualWeyl.Misc.invT_eq hg' hg w hw]
    exact PI.OddDualWeyl.Misc.colSpan_mul_le _ _

end PI.OddDualWeyl
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacobiMinorIdentity
section
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl.Jac

theorem block {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A B : Matrix (m ⊕ n) (m ⊕ n) R) (d : R)
    (h : B * A = d • (1 : Matrix (m ⊕ n) (m ⊕ n) R)) :
    B.toBlocks₂₂.det * A.det = d ^ Fintype.card n * A.toBlocks₁₁.det := by
  have hX : (fromBlocks (1 : Matrix m m R) 0 B.toBlocks₂₁ B.toBlocks₂₂) * A =
      fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ 0 (d • (1 : Matrix n n R)) := by
    ext i j
    have hij := congrFun (congrFun h i) j
    rcases i with i | i <;> rcases j with j | j <;>
      first
      | (simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toBlocks₁₁,
          Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]; done)
      | (simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toBlocks₁₁,
          Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂] at hij ⊢; exact hij)
  have hdet := congrArg Matrix.det hX
  simp only [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_one, det_smul, one_mul,
    mul_one] at hdet
  linear_combination hdet

theorem det_sub {R : Type*} [CommRing R] {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eI eJ : ι ≃ Fin k) (A : Matrix (Fin k) (Fin k) R) :
    (A.submatrix eI eJ).det = ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det := by
  have h1 : A.submatrix eI eJ = (A.submatrix eI eI).submatrix id (eJ.trans eI.symm) := by
    ext i j
    simp
  rw [h1]
  rw [det_permute', det_submatrix_equiv_self]

theorem sign_sq {R : Type*} [CommRing R] (u : ℤˣ) : ((u : ℤ) : R) * ((u : ℤ) : R) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

private theorem mapMatrix_eval_generic_eq {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    (MvPolynomial.eval₂Hom (Int.castRingHom R) fun p : Fin k × Fin k => A p.1 p.2).mapMatrix
      (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin k × Fin k) ℤ)) = A := by
  ext i j
  simp

private theorem det_generic_int_ne_zero (k : ℕ) :
    (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin k × Fin k) ℤ)).det ≠ 0 := by
  intro h
  have h1 := congrArg
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ)
      fun p : Fin k × Fin k => (1 : Matrix (Fin k) (Fin k) ℤ) p.1 p.2) h
  rw [RingHom.map_det, mapMatrix_eval_generic_eq (1 : Matrix (Fin k) (Fin k) ℤ), det_one, map_zero] at h1
  exact one_ne_zero h1

private theorem det_toBlocks22_adjugate_submatrix_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {k : ℕ} {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Nonempty n]
    (eI eJ : m ⊕ n ≃ Fin k) (A : Matrix (Fin k) (Fin k) R) (hA : A.det ≠ 0) :
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det =
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det ^ (Fintype.card n - 1) *
        (A.submatrix eI eJ).toBlocks₁₁.det := by
  have hBA : (adjugate A).submatrix eJ eI * A.submatrix eI eJ =
      A.det • (1 : Matrix (m ⊕ n) (m ⊕ n) R) := by
    rw [submatrix_mul_equiv, adjugate_mul]
    ext i j
    simp [Matrix.one_apply]
  have key := block (A.submatrix eI eJ) ((adjugate A).submatrix eJ eI) A.det hBA
  rw [det_sub] at key
  have hs2 := sign_sq (R := R) (Equiv.Perm.sign (eJ.trans eI.symm))
  have hpow : A.det ^ Fintype.card n = A.det * A.det ^ (Fintype.card n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Fintype.card_pos (α := n))]
  have h2 : A.det * (((adjugate A).submatrix eJ eI).toBlocks₂₂.det *
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R)) =
      A.det * (A.det ^ (Fintype.card n - 1) * (A.submatrix eI eJ).toBlocks₁₁.det) := by
    linear_combination key + (A.submatrix eI eJ).toBlocks₁₁.det * hpow
  have h3 := mul_left_cancel₀ hA h2
  linear_combination ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * h3 -
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det * hs2

theorem jacobi {R : Type*} [CommRing R] {k : ℕ} {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty n] (eI eJ : m ⊕ n ≃ Fin k)
    (A : Matrix (Fin k) (Fin k) R) :
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det =
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det ^ (Fintype.card n - 1) *
        (A.submatrix eI eJ).toBlocks₁₁.det := by
  obtain ⟨G, hG0, φ, hφG⟩ : ∃ G : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) ℤ),
      G.det ≠ 0 ∧ ∃ φ : MvPolynomial (Fin k × Fin k) ℤ →+* R, φ.mapMatrix G = A :=
    ⟨_, det_generic_int_ne_zero k, _, mapMatrix_eval_generic_eq A⟩
  have hcore := det_toBlocks22_adjugate_submatrix_of_det_ne_zero eI eJ G hG0
  have hadj : φ.mapMatrix (adjugate G) = adjugate A := by
    rw [RingHom.map_adjugate, hφG]
  have e1 : φ.mapMatrix (((adjugate G).submatrix eJ eI).toBlocks₂₂) =
      ((adjugate A).submatrix eJ eI).toBlocks₂₂ := by
    ext i j
    exact congrFun (congrFun hadj (eJ (Sum.inr i))) (eI (Sum.inr j))
  have e2 : φ.mapMatrix ((G.submatrix eI eJ).toBlocks₁₁) = (A.submatrix eI eJ).toBlocks₁₁ := by
    ext i j
    exact congrFun (congrFun hφG (eI (Sum.inl i))) (eJ (Sum.inl j))
  have h := congrArg φ hcore
  simp only [map_mul, map_pow, map_intCast, RingHom.map_det, hφG, e1, e2] at h
  exact h

end PI.OddDualWeyl.Jac

namespace PI.OddDualWeyl.Jac

def mkE {a b k : ℕ} (f : Fin a → Fin k) (g : Fin b → Fin k) (h : a + b = k)
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : ∀ x y, f x ≠ g y) :
    Fin a ⊕ Fin b ≃ Fin k :=
  Equiv.ofBijective (Sum.elim f g) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hf.sumElim hg hfg, by simp [h]⟩)

def eR (k s : ℕ) (hs : s + 1 ≤ k) : Fin (k - 1 - s) ⊕ Fin (s + 1) ≃ Fin k :=
  mkE (a := k - 1 - s) (b := s + 1) (fun x => Fin.castLE (Nat.sub_le _ _ |>.trans (Nat.sub_le _ _)) x) (fun y => Fin.rev (Fin.castLE hs y)) (by omega)
    (Fin.castLE_injective _) (Fin.rev_injective.comp (Fin.castLE_injective _))
    (by
      intro x y h
      have h1 := congrArg Fin.val h
      have := x.isLt; have := y.isLt
      simp [Fin.val_rev] at h1; omega)

theorem dualSub_pMinor (R : Type*) [CommRing R] {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : ℕ)
    (hs : s ≤ k) :
    dualSub R k (pMinor R σ s hs) =
      (Matrix.of fun p q : Fin s =>
        adjugate (genM R k) (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det := by
  rw [PI.OddDualWeyl.dualSub, PI.OddDualWeyl.pMinor, AlgHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun p q => by simp [PI.OddDualWeyl.dualM])

theorem sign_pm (R : Type*) [CommRing R] (u : ℤˣ) :
    ((u : ℤ) : R) = 1 ∨ ((u : ℤ) : R) = -1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

end PI.OddDualWeyl.Jac

namespace PI.OddDualWeyl

open Jac in
theorem jacobiMinorReverse : JacRev := by
  unfold JacRev
  intro R _ k s hs
  refine ⟨((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) : R),
    PI.OddDualWeyl.Jac.sign_pm R _, ?_⟩
  calc dualSub R k (pMinor R Fin.revPerm (s + 1) hs)
      = (Matrix.of fun p q : Fin (s + 1) => adjugate (genM R k) (Fin.rev (Fin.castLE hs q))
          ((Fin.revPerm : Equiv.Perm (Fin k)) (Fin.castLE hs p))).det :=
        PI.OddDualWeyl.Jac.dualSub_pMinor R Fin.revPerm (s + 1) hs
    _ = (((adjugate (genM R k)).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₂₂)ᵀ.det :=
        congrArg Matrix.det (Matrix.ext fun p q => rfl)
    _ = ((adjugate (genM R k)).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₂₂.det :=
        det_transpose _
    _ = ((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) :
          MvPolynomial (Fin k × Fin k) R) * (genM R k).det ^ (Fintype.card (Fin (s + 1)) - 1) *
          ((genM R k).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₁₁.det :=
        PI.OddDualWeyl.Jac.jacobi (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs) (genM R k)
    _ = C (((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) : R)) *
          (genM R k).det ^ s * pMinor R 1 (k - 1 - s) (by omega) := by
        rw [map_intCast, Fintype.card_fin, Nat.add_sub_cancel, pMinor]
        all_goals rfl

end PI.OddDualWeyl
end
end

