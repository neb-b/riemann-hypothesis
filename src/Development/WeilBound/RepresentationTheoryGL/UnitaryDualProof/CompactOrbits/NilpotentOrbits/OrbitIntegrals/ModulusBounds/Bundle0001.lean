module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.LaurentCoeffZero
section
noncomputable section

open Matrix Module Polynomial

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

namespace LaurentWeightBound

variable {k : Type} [Field k] {n : ℕ}

theorem laurent_coeff_zero [Infinite k] (M : Finset ℤ) (c : ℤ → k)
    (h : ∀ t : kˣ, ∑ m ∈ M, ((t ^ m : kˣ) : k) * c m = 0) : ∀ m ∈ M, c m = 0 := by
  classical
  set N : ℕ := ∑ m ∈ M, m.natAbs with hN
  have hle : ∀ m ∈ M, 0 ≤ m + N := by
    intro m hm
    have h1 : m.natAbs ≤ N := Finset.single_le_sum (f := fun m : ℤ => m.natAbs) (fun _ _ => Nat.zero_le _) hm
    have h2 : -(m.natAbs : ℤ) ≤ m := by
      rcases Int.natAbs_eq m with h | h <;> omega
    omega
  let e : ℤ → ℕ := fun m => (m + N).toNat
  let p : k[X] := ∑ m ∈ M, C (c m) * X ^ (e m)
  have heval : ∀ t : kˣ, p.eval (t : k) = 0 := by
    intro t
    have hx : ∀ m ∈ M, (t : k) ^ (e m) = (t : k) ^ N * ((t ^ m : kˣ) : k) := by
      intro m hm
      have h3 : ((e m : ℕ) : ℤ) = m + N := Int.toNat_of_nonneg (hle m hm)
      have h4 : (t ^ ((e m : ℕ) : ℤ) : kˣ) = t ^ (N : ℤ) * t ^ m := by
        rw [h3, ← _root_.zpow_add, add_comm]
      have h5 := congrArg (fun u : kˣ => (u : k)) h4
      simpa [zpow_natCast] using h5
    simp only [p, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.sum_congr rfl (fun m hm => by rw [hx m hm])]
    rw [show (∑ m ∈ M, c m * ((t : k) ^ N * ((t ^ m : kˣ) : k))) =
      (t : k) ^ N * ∑ m ∈ M, ((t ^ m : kˣ) : k) * c m by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)]
    rw [h t, mul_zero]
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinf : Set.Infinite ({0}ᶜ : Set k) := (Set.finite_singleton (0 : k)).infinite_compl
    refine hinf.mono ?_
    intro x hx
    have hx' : x ≠ 0 := hx
    exact heval (Units.mk0 x hx')
  intro m hm
  have hc := congrArg (fun q : k[X] => q.coeff (e m)) hp
  simp only [p, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single m] at hc
  · simpa using hc
  · intro b hb hbm
    have : e m ≠ e b := by
      intro heq
      have h3 : ((e m : ℕ) : ℤ) = m + N := Int.toNat_of_nonneg (hle m hm)
      have h4 : ((e b : ℕ) : ℤ) = b + N := Int.toNat_of_nonneg (hle b hb)
      apply hbm
      have : ((e m : ℕ) : ℤ) = ((e b : ℕ) : ℤ) := by rw [heq]
      omega
    simp [this]
  · intro h; exact absurd hm h

def gt (P : GL (Fin n) k) (w : Fin n → ℤ) (t : kˣ) : Matrix (Fin n) (Fin n) k :=
  P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val

def cut (w : Fin n → ℤ) (m : ℤ) (u : Fin n → k) : Fin n → k := fun i => if w i = m then u i else 0

def prj (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (y : Fin n → k) : Fin n → k :=
  P.val *ᵥ cut w m (P⁻¹.val *ᵥ y)

theorem inv_mulVec_prj (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (y : Fin n → k) :
    P⁻¹.val *ᵥ prj P w m y = cut w m (P⁻¹.val *ᵥ y) := by
  simp [prj, mulVec_mulVec]

theorem gt_mulVec (P : GL (Fin n) k) (w : Fin n → ℤ) (t : kˣ) (y : Fin n → k) :
    gt P w t *ᵥ y = ∑ m ∈ Finset.univ.image w, ((t ^ m : kˣ) : k) • prj P w m y := by
  classical
  simp only [prj, ← mulVec_smul, ← mulVec_sum]
  rw [gt, ← mulVec_mulVec, ← mulVec_mulVec]
  congr 1
  ext i
  simp only [mulVec_diagonal, Finset.sum_apply, Pi.smul_apply, cut, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem sum_prj (P : GL (Fin n) k) (w : Fin n → ℤ) (y : Fin n → k) :
    ∑ m ∈ Finset.univ.image w, prj P w m y = y := by
  have h := gt_mulVec P w 1 y
  have hg : gt P w 1 = 1 := by
    simp only [gt, _root_.one_zpow, Units.val_one]
    rw [diagonal_one, mul_one, Units.mul_inv]
  rw [hg, one_mulVec] at h
  simpa using h.symm

theorem gt_prj (P : GL (Fin n) k) (w : Fin n → ℤ) (t : kˣ) (m : ℤ) (y : Fin n → k) :
    gt P w t *ᵥ prj P w m y = ((t ^ m : kˣ) : k) • prj P w m y := by
  rw [gt, ← mulVec_mulVec, ← mulVec_mulVec, inv_mulVec_prj, prj, ← mulVec_smul]
  congr 1
  ext i
  simp only [mulVec_diagonal, cut, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · simp

theorem prj_prj (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (y : Fin n → k) :
    prj P w m (prj P w m y) = prj P w m y := by
  rw [prj, inv_mulVec_prj]
  congr 1
  ext i
  simp only [cut]
  split_ifs <;> rfl

theorem prj_mem [Infinite k] (P : GL (Fin n) k) (w : Fin n → ℤ) (W : Submodule k (Fin n → k))
    (hinv : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W) (m : ℤ) (y : Fin n → k) (hy : y ∈ W) :
    prj P w m y ∈ W := by
  classical
  by_cases hm : m ∈ Finset.univ.image w
  · rw [← Submodule.Quotient.mk_eq_zero]
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro ℓ
    have key := laurent_coeff_zero (Finset.univ.image w)
      (fun m => ℓ (Submodule.Quotient.mk (p := W) (prj P w m y))) (fun t => by
        have h1 := hinv t y hy
        rw [← Submodule.Quotient.mk_eq_zero, gt_mulVec] at h1
        have h2 : (ℓ ∘ₗ W.mkQ) (∑ m ∈ Finset.univ.image w, ((t ^ m : kˣ) : k) • prj P w m y) = 0 := by
          rw [LinearMap.comp_apply, Submodule.mkQ_apply, h1, map_zero]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum] at h2
        simpa only [map_smul, LinearMap.comp_apply, Submodule.mkQ_apply, smul_eq_mul] using h2) m hm
    exact key
  · have : prj P w m y = 0 := by
      rw [prj]
      have hc : cut w m (P⁻¹.val *ᵥ y) = 0 := by
        ext i
        simp only [cut, Pi.zero_apply]
        split_ifs with h
        · exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩) hm
        · rfl
      rw [hc, mulVec_zero]
    rw [this]; exact W.zero_mem

theorem prj_neg (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (hm : m < 0) (y : Fin n → k)
    (hy : ∃ u : Fin n → k, y = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) : prj P w m y = 0 := by
  obtain ⟨u, rfl, hu⟩ := hy
  rw [prj, mulVec_mulVec]
  simp only [Units.inv_mul, one_mulVec]
  have hc : cut w m u = 0 := by
    ext i
    simp only [cut, Pi.zero_apply]
    split_ifs with h
    · exact hu i (h ▸ hm)
    · rfl
  rw [hc, mulVec_zero]

end LaurentWeightBound

open LaurentWeightBound

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

theorem wt (P : GL (Fin n) k) (w : Fin n → ℤ) (W : Submodule k (Fin n → k))
    (hinv : ∀ t : kˣ, ∀ y ∈ W,
      Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val) y ∈ W)
    (hpos : ∀ y ∈ W, ∃ u : Fin n → k, y = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) :
    ∃ m : ℕ, ∀ t : kˣ,
      LinearMap.det ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict
        (hinv t)) = (t : k) ^ m := by
  classical
  have hinv' : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W := fun t y hy => by
    have := hinv t y hy
    rwa [Matrix.toLin'_apply] at this

  let S : Set W := {y | ∃ m : ℕ, prj P w m (y : Fin n → k) = y}
  have hspan : Submodule.span k S = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hsum := sum_prj P w y
    have hmem : ∀ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) ∈ Submodule.span k S := by
      intro m _
      by_cases hm : m < 0
      · have h0 : (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) = 0 :=
          Subtype.ext (prj_neg P w m hm y (hpos y hy))
        rw [h0]; exact Submodule.zero_mem _
      · apply Submodule.subset_span
        refine ⟨m.toNat, ?_⟩
        have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
        simp only [this]
        exact prj_prj P w m y
    have : (⟨y, hy⟩ : W) = ∑ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hsum.symm
    rw [this]
    exact Submodule.sum_mem _ hmem
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent k S
  have hfin : Finite b := hli.finite
  let _ : Fintype b := Fintype.ofFinite b
  let B : Basis b k W := Basis.mk hli (by
    rw [Subtype.range_coe, hbspan, hspan])
  have hwt : ∀ j : b, ∃ m : ℕ, prj P w m ((j : W) : Fin n → k) = (j : W) := fun j => hbS j.2
  choose mj hmj using hwt
  refine ⟨∑ j, mj j, fun t => ?_⟩
  rw [← LinearMap.det_toMatrix B]
  have hdiag : LinearMap.toMatrix B B ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) *
      P⁻¹.val)).restrict (hinv t)) = diagonal (fun j => (t : k) ^ (mj j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hfj : (Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict (hinv t) (B j)
        = (t : k) ^ (mj j) • B j := by
      apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, Matrix.toLin'_apply, Basis.mk_apply, Submodule.coe_smul]
      have h1 := gt_prj P w t (mj j) ((j : W) : Fin n → k)
      rw [hmj j] at h1
      have h2 : ((t ^ ((mj j : ℕ) : ℤ) : kˣ) : k) = (t : k) ^ (mj j) := by simp [zpow_natCast]
      rw [h2] at h1
      exact h1
    rw [hfj, map_smul, Basis.repr_self, diagonal_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hdiag, det_diagonal, Finset.prod_pow_eq_pow_sum]

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.RelIndexEq
section
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

theorem relIndex_eq {k : Type} [Field k] {n : ℕ} (I J : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (GI GJ : Subgroup (GL (Fin n) k)) (hJI : J ≤ I)
    (hGI : ∀ u : GL (Fin n) k, u ∈ GI ↔ u.val - 1 ∈ I)
    (hGJ : ∀ u : GL (Fin n) k, u ∈ GJ ↔ u.val - 1 ∈ J)
    (hsurj : ∀ x ∈ I, ∃ u : GL (Fin n) k, u.val = 1 + x)
    (hmul : ∀ u ∈ GI, ∀ y ∈ J, u.val * y ∈ J) :
    GJ.relIndex GI = J.relIndex I := by
  classical
  have hinv : ∀ x ∈ I, ∃ u : GL (Fin n) k, u ∈ GI ∧ u.val = 1 + x := fun x hx => by
    obtain ⟨u, hu⟩ := hsurj x hx
    refine ⟨u, (hGI u).2 ?_, hu⟩
    rw [hu, add_sub_cancel_left]
    exact hx
  let f : GI → I := fun u => ⟨u.1.val - 1, (hGI u.1).1 u.2⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h : a.1.val - 1 = b.1.val - 1 := congrArg Subtype.val hab
    exact Subtype.ext (Units.ext (sub_left_inj.mp h))
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨u, hu, hux⟩ := hinv x.1 x.2
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    show u.val - 1 = x.1
    rw [hux, add_sub_cancel_left]
  let e : GI ≃ I := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have key : ∀ a b : GI, (QuotientGroup.leftRel (GJ.subgroupOf GI)) a b ↔
      (QuotientAddGroup.leftRel (J.addSubgroupOf I)) (e a) (e b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply, Subgroup.mem_subgroupOf,
      AddSubgroup.mem_addSubgroupOf]
    show ((a.1⁻¹ * b.1 : GL (Fin n) k)) ∈ GJ ↔ -(a.1.val - 1) + (b.1.val - 1) ∈ J
    have h1 : -(a.1.val - 1) + (b.1.val - 1) = b.1.val - a.1.val := by abel
    rw [h1, hGJ, Units.val_mul]
    have ha : a.1⁻¹ ∈ GI := GI.inv_mem a.2
    constructor
    · intro h
      have h2 := hmul a.1 a.2 _ h
      have e2 : a.1.val * ((a.1⁻¹).val * b.1.val - 1) = b.1.val - a.1.val := by
        rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
      rwa [e2] at h2
    · intro h
      have h2 := hmul a.1⁻¹ ha _ h
      have e2 : (a.1⁻¹).val * (b.1.val - a.1.val) = (a.1⁻¹).val * b.1.val - 1 := by
        rw [mul_sub, Units.inv_mul]
      rwa [e2] at h2
  have hc := Nat.card_congr (Quotient.congr e key)
  exact hc

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
end

