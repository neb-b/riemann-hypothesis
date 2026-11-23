module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetBasis
section
noncomputable section

open Matrix CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.GradEig

variable {n : ℕ}

theorem Jm_mul_self (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem trace_eq_zero {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (h : IsGrad ε A) : A.trace = 0 := by
  obtain ⟨hG, hH, -, -⟩ := h
  have hG' : A.conjTranspose * Jm ε + Jm ε * A = 0 := hG
  rw [hH] at hG'
  have h1 : A * Jm ε = -(Jm ε * A) := eq_neg_of_add_eq_zero_left hG'
  have h2 : (A * Jm ε * Jm ε).trace = -(Jm ε * A * Jm ε).trace := by
    rw [h1, Matrix.neg_mul, Matrix.trace_neg]
  rw [Matrix.mul_assoc A, Jm_mul_self, Matrix.mul_one, Matrix.trace_mul_cycle, Jm_mul_self,
    Matrix.one_mul] at h2
  linear_combination h2 / 2

theorem eigenvalue_cases {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (h3 : A * A * A = A) (i : Fin n) :
    hA.eigenvalues i = -1 ∨ hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
  have hev := hA.mulVec_eigenvectorBasis i
  obtain ⟨v, hv⟩ : ∃ v, v = (hA.eigenvectorBasis i).ofLp := ⟨_, rfl⟩
  rw [← hv] at hev
  obtain ⟨r, hr⟩ : ∃ r, r = hA.eigenvalues i := ⟨_, rfl⟩
  rw [← hr] at hev ⊢
  have h3v : (A * A * A) *ᵥ v = (r ^ 3) • v := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [hev, Matrix.mulVec_smul, smul_smul]
    congr 1
    ring
  rw [h3, hev] at h3v
  have hne : v ≠ 0 := by
    intro h0
    have h1 : ‖hA.eigenvectorBasis i‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 i
    have h2 : hA.eigenvectorBasis i = 0 := by
      rw [hv] at h0
      simpa using h0
    rw [h2, norm_zero] at h1
    exact zero_ne_one h1
  have hr3 : r ^ 3 = r := by
    have h4 : (r ^ 3 - r) • v = 0 := by rw [sub_smul, ← h3v, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd h5 hne
  have hf : r * (r - 1) * (r + 1) = 0 := by linear_combination hr3
  rcases mul_eq_zero.1 hf with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by linarith))
  · exact Or.inl (by linarith)

theorem exists_perm_blocks {c : Fin n → Fin 3} {d : Fin 3 → ℕ} (hd : ∑ i, d i = n)
    (hc : ∀ i, Fintype.card {x // c x = i} = d i) :
    ∃ σ : Fin n ≃ Fin n, ∀ p, c (σ p) = ((stdBlocks d hd).symm p).1 := by
  classical
  let e : ∀ i, {x // c x = i} ≃ Fin (d i) := fun i => Fintype.equivFinOfCardEq (hc i)
  let τ : Fin n ≃ Fin n :=
    ((Equiv.sigmaFiberEquiv c).symm.trans (Equiv.sigmaCongrRight e)).trans (stdBlocks d hd)
  refine ⟨τ.symm, fun p => ?_⟩
  have hτ : τ.symm p = (((e ((stdBlocks d hd).symm p).1).symm ((stdBlocks d hd).symm p).2) : Fin n) := rfl
  rw [hτ]
  exact ((e _).symm _).2

theorem exists_gradBasis {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (h : IsGrad ε A) :
    Nonempty (GradBasis A) := by
  classical
  have htr := trace_eq_zero h
  obtain ⟨_, hH, h3, _⟩ := h
  have hA : A.IsHermitian := hH
  have hcase := eigenvalue_cases hA h3
  let c : Fin n → Fin 3 := fun x =>
    if hA.eigenvalues x = -1 then 0 else if hA.eigenvalues x = 0 then 1 else 2
  have hc0 : ∀ x, c x = 0 ↔ hA.eigenvalues x = -1 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hc1 : ∀ x, c x = 1 ↔ hA.eigenvalues x = 0 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hc2 : ∀ x, c x = 2 ↔ hA.eigenvalues x = 1 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hval : ∀ x, (![-1, 0, 1] : Fin 3 → ℂ) (c x) = ((hA.eigenvalues x : ℝ) : ℂ) := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> rfl
  obtain ⟨j, hj⟩ : ∃ j, (Finset.univ.filter fun x => hA.eigenvalues x = -1).card = j := ⟨_, rfl⟩
  have hsumR : ∑ x, hA.eigenvalues x = 0 := by
    have h1 := hA.trace_eq_sum_eigenvalues
    rw [htr] at h1
    have h2 := congrArg Complex.re h1
    simpa [Complex.re_sum] using h2.symm
  have hk1 : (Finset.univ.filter fun x => hA.eigenvalues x = 1).card = j := by
    have hs : ∑ x, hA.eigenvalues x = ∑ x, ((if hA.eigenvalues x = 1 then (1 : ℝ) else 0) -
        (if hA.eigenvalues x = -1 then (1 : ℝ) else 0)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases hcase x with hx | hx | hx <;> norm_num [hx]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hsumR, hj] at hs
    have hs' : ((Finset.univ.filter fun x => hA.eigenvalues x = 1).card : ℝ) = j := by linarith
    exact_mod_cast hs'
  have htot : j + (Finset.univ.filter fun x => hA.eigenvalues x = 0).card + j = n := by
    have hs : ∑ x : Fin n, ((if hA.eigenvalues x = -1 then 1 else 0) +
        (if hA.eigenvalues x = 0 then 1 else 0) + (if hA.eigenvalues x = 1 then 1 else 0) : ℕ) =
        ∑ x : Fin n, 1 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases hcase x with hx | hx | hx <;> norm_num [hx]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
      Finset.sum_boole, hj, hk1] at hs
    simpa using hs
  have hcard : ∀ i, Fintype.card {x // c x = i} = dims n j i := by
    intro i
    fin_cases i
    · show Fintype.card {x // c x = 0} = j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc0 x, hj]
    · show Fintype.card {x // c x = 1} = n - 2 * j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc1 x]
      omega
    · show Fintype.card {x // c x = 2} = j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc2 x, hk1]
  have hd : ∑ i, dims n j i = n := by
    rw [Fin.sum_univ_three]
    show j + (n - 2 * j) + j = n
    omega
  obtain ⟨σ, hσ⟩ := exists_perm_blocks hd hcard
  have hs := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hUU : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2
  have hUU' : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  have hdiag : (diagonal fun p => (![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n j) hd).symm p).fst) =
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues)).submatrix σ σ := by
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1
    funext p
    rw [← hσ p, hval]
    rfl
  have e1 : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ *
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, hUU, Matrix.submatrix_id_id]
  have e2 : (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hUU', Matrix.submatrix_one_equiv]
  have e3 : A = ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ *
      diagonal fun p => (![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n j) hd).symm p).fst) *
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id := by
    rw [hdiag, ← Matrix.submatrix_mul _ _ _ _ _ σ.bijective,
      ← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, Matrix.submatrix_id_id]
    exact hs
  exact ⟨⟨_, _, e1, e2, j, hd, e3⟩⟩

end GlobalTheory.CompanionTheory.GradEig

theorem GlobalTheory.CompanionTheory.GradEig.basis : CompanionTheory.RgExh.Dec.J.Basis := by
  intro n ε A h
  exact GlobalTheory.CompanionTheory.GradEig.exists_gradBasis h
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LabelTracking
section
open Finset

namespace GlobalTheory.CompanionTheory.Labels

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec.J

variable {n : ℕ}

theorem tie_step {χ₀ χ : Fin n → ℂ} {t : Fin n}
    (hT : ∀ r s, r ≠ s → χ r = χ s → χ r = χ₀ r ∧ χ s = χ₀ s) (hg : ∀ r, χ r ≠ χ t + 1) :
    ∀ r s, r ≠ s → (χ + Pi.single t 1 : Fin n → ℂ) r = (χ + Pi.single t 1 : Fin n → ℂ) s →
      (χ + Pi.single t 1 : Fin n → ℂ) r = χ₀ r ∧ (χ + Pi.single t 1 : Fin n → ℂ) s = χ₀ s := by
  intro r s hrs h
  by_cases hr : r = t
  · subst hr
    have hs : s ≠ r := hrs.symm
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hs, add_zero] at h
    exact absurd h.symm (hg s)
  by_cases hs : s = t
  · subst hs
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hr, add_zero] at h
    exact absurd h (hg r)
  simp only [Pi.add_apply, Pi.single_eq_of_ne hr, Pi.single_eq_of_ne hs, add_zero] at h ⊢
  exact hT r s hrs h

theorem apply_swap_of_eq (χ : Fin n → ℂ) {r s : Fin n} (h : χ r = χ s) (i : Fin n) :
    χ i = χ (Equiv.swap r s i) := by
  by_cases h1 : i = r
  · subst h1; simp [h]
  by_cases h2 : i = s
  · subst h2; simp [h]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem sum_filter_swap (χ : Fin n → ℂ) (L : Fin n → Fin 3) {r s : Fin n} (h : χ r = χ s) (a : Fin 3) :
    ∑ i ∈ univ.filter (fun i => (L ∘ Equiv.swap r s) i = a), χ i = ∑ i ∈ univ.filter (fun i => L i = a), χ i :=
  Finset.sum_equiv (Equiv.swap r s) (by simp) fun i _ => apply_swap_of_eq χ h i

theorem deg_swap (χ : Fin n → ℂ) (L : Fin n → Fin 3) {r s : Fin n} (h : χ r = χ s) :
    deg χ (L ∘ Equiv.swap r s) = deg χ L := by
  simp only [deg, sum_filter_swap χ L h]

theorem isLabel_swap {j : ℕ} {L : Fin n → Fin 3} (h : IsLabel j L) (r s : Fin n) :
    IsLabel j (L ∘ Equiv.swap r s) := by
  intro a
  rw [← h a]
  exact Finset.card_equiv (Equiv.swap r s) (by simp)

theorem moved_labels (χ₀ : Fin n → ℂ) (j : ℕ) : ∀ (ss : List (Fin n)) (χ : Fin n → ℂ) (Λ : Set (Fin n → Fin 3)),
    GoodPath χ ss → (∀ r s, r ≠ s → χ r = χ s → χ r = χ₀ r ∧ χ s = χ₀ s) →
    (∀ L ∈ Λ, IsLabel j L ∧ (deg χ₀ L).re < 0) →
    ∀ L ∈ moveIter χ Λ ss, IsLabel j L ∧ (deg χ₀ L).re < 0 := by
  intro ss
  induction ss with
  | nil =>
    intro χ Λ _ _ hΛ L hL
    exact hΛ L hL
  | cons t ss ih =>
    intro χ Λ hg hT hΛ L hL
    refine ih (χ + Pi.single t 1) (move χ Λ t) hg.2 (tie_step hT hg.1) ?_ L hL
    rintro _ ⟨L₀, hL₀, r, hr, rfl⟩
    obtain ⟨hl, hd⟩ := hΛ L₀ hL₀
    refine ⟨isLabel_swap hl r t, ?_⟩
    by_cases hrt : r = t
    · subst hrt
      simpa using hd
    · obtain ⟨h1, h2⟩ := hT r t hrt hr
      rw [deg_swap χ₀ L₀ (h1.symm.trans (hr.trans h2))]
      exact hd

theorem labelTrack : LabelTrack := by
  intro n χ ss B j hg hf L hL
  obtain ⟨hl, hd⟩ := moved_labels χ j ss χ _ hg (fun _ _ _ _ => ⟨rfl, rfl⟩) (fun _ h => h) L hL
  refine hf (univ.filter fun s => L s = 2) (univ.filter fun s => L s = 0) ?_ ?_ hd
  · refine Finset.disjoint_filter.2 fun x _ h1 h2 => ?_
    rw [h1] at h2
    exact absurd h2 (by decide)
  · rw [hl 2, hl 0]
    simp [dims]

end GlobalTheory.CompanionTheory.Labels
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LevelWeightSumBound
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.ClusterBound

theorem card_first_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) :
    (A.filter fun i => i.1.1 = c).card ≤ n := by
  have h : (A.filter fun i => i.1.1 = c).card ≤ (univ : Finset (Fin n)).card :=
    Finset.card_le_card_of_injOn (fun i => i.1.2) (fun _ _ => mem_univ _) (by
      intro x hx y hy hxy
      have h1 := (mem_filter.1 (mem_coe.1 hx)).2
      have h2 := (mem_filter.1 (mem_coe.1 hy)).2
      exact Subtype.ext (Prod.ext (h1.trans h2.symm) hxy))
  simpa using h

theorem card_second_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) :
    (A.filter fun i => i.1.2 = c).card ≤ n := by
  have h : (A.filter fun i => i.1.2 = c).card ≤ (univ : Finset (Fin n)).card :=
    Finset.card_le_card_of_injOn (fun i => i.1.1) (fun _ _ => mem_univ _) (by
      intro x hx y hy hxy
      have h1 := (mem_filter.1 (mem_coe.1 hx)).2
      have h2 := (mem_filter.1 (mem_coe.1 hy)).2
      exact Subtype.ext (Prod.ext hxy (h1.trans h2.symm)))
  simpa using h

theorem abs_wt_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) : |wt A c| ≤ n := by
  have h1 : (((A.filter fun i => i.1.1 = c).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast card_first_le A c
  have h2 : (((A.filter fun i => i.1.2 = c).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast card_second_le A c
  have h3 : (0 : ℝ) ≤ ((A.filter fun i => i.1.1 = c).card : ℕ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((A.filter fun i => i.1.2 = c).card : ℕ) := Nat.cast_nonneg _
  unfold wt
  rw [abs_le]
  constructor <;> linarith

theorem abs_two_rhoC_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    |(2 : ℝ) * PI.UpqRep.rhoC ε a| ≤ n := by
  have h1 : (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
  have h2 : (((univ.filter fun b => b < a ∧ ε b = ε a).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
  have h3 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℕ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℕ) := Nat.cast_nonneg _
  unfold PI.UpqRep.rhoC
  rw [abs_le]
  constructor <;> linarith

theorem abs_modExp_le {M N : ℕ} (d : Fin M → ℕ) (h : ∑ j, d j = N) (i : Fin M) :
    |modExp (fun j => Fin (d j)) i| ≤ (N : ℤ) := by
  have hN : ∑ j, (d j : ℤ) = N := by exact_mod_cast h
  have key : ∀ p : Fin M → Prop, ∀ [DecidablePred p],
      (0 : ℤ) ≤ ∑ b with p b, (d b : ℤ) ∧ ∑ b with p b, (d b : ℤ) ≤ N := fun p _ =>
    ⟨sum_nonneg fun _ _ => Int.natCast_nonneg _, hN ▸ sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) fun _ _ _ => Int.natCast_nonneg _⟩
  obtain ⟨a1, a2⟩ := key (fun b => i < b)
  obtain ⟨b1, b2⟩ := key (fun b => b < i)
  simp only [modExp, Fintype.card_fin]
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.CompanionTheory.RgCOBlock.ClusterBound

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem norm_cluster_sum_le (n M : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (i : Fin M) (h : ∑ j, sz lev M j = n) :
    ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ) -
      ((sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2))‖ ≤ 3 * (n : ℝ) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsz : ((sz lev M i : ℕ) : ℝ) ≤ n := by
    have : sz lev M i ≤ n := (card_le_univ _).trans_eq (Fintype.card_fin n)
    exact_mod_cast this
  have hsz0 : (0 : ℝ) ≤ ((sz lev M i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm : ((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) ≤ n := by
    exact_mod_cast ClusterBound.abs_modExp_le (sz lev M) h i
  have hm0 : (0 : ℝ) ≤ ((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) := by
    exact_mod_cast abs_nonneg _
  have hterm : ∀ a ∈ univ.filter (fun a => lev a = (i : ℕ)),
      ‖((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ)‖ ≤ 2 * (n : ℝ) := by
    intro a _
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := ClusterBound.abs_wt_le (omU ε lev) a
    have h2 := ClusterBound.abs_two_rhoC_le ε a
    have h3 := abs_sub (wt (omU ε lev) a) ((2 : ℝ) * PI.UpqRep.rhoC ε a)
    linarith
  have hsum : ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)),
      ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ)‖ ≤
      ((sz lev M i : ℕ) : ℝ) * (2 * (n : ℝ)) := by
    refine (norm_sum_le_of_le _ hterm).trans_eq ?_
    rw [sum_const, nsmul_eq_mul]
    rfl
  have hmod : ‖(sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2)‖ =
      ((sz lev M i : ℕ) : ℝ) * (((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) / 2) := by
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_intCast]
    simp
  refine (norm_sub_le _ _).trans ?_
  rw [hmod]
  have e1 : ((sz lev M i : ℕ) : ℝ) * (2 * (n : ℝ)) ≤ (n : ℝ) * (2 * n) :=
    mul_le_mul_of_nonneg_right hsz (by positivity)
  have e2 : ((sz lev M i : ℕ) : ℝ) * (((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) / 2) ≤
      (n : ℝ) * ((n : ℝ) / 2) :=
    mul_le_mul hsz (by linarith) (by linarith) hn
  nlinarith [sq_nonneg (n : ℝ)]

end GlobalTheory.CompanionTheory.RgCOBlock
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionPreservesSupportDegree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp

open Finset
open CompanionTheory.D.LK (Pos Cn ann cre lift sg)
open CompanionTheory.RgExh.U

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cre_ann_ne (i k : Pos n) (x : Cn n V) (A : Finset (Pos n))
    (h : (cre k * ann i : Module.End ℂ (Cn n V)) x A ≠ 0) :
    k ∈ A ∧ i ∉ A.erase k ∧ x (insert i (A.erase k)) ≠ 0 := by
  change (if k ∈ A then sg k A • (if i ∈ A.erase k then 0 else
    sg i (A.erase k) • x (insert i (A.erase k))) else 0) ≠ 0 at h
  by_cases hk : k ∈ A
  · by_cases hi : i ∈ A.erase k
    · rw [if_pos hk, if_pos hi, smul_zero] at h
      exact absurd rfl h
    · refine ⟨hk, hi, fun hx => ?_⟩
      rw [if_pos hk, if_neg hi, hx, smul_zero, smul_zero] at h
      exact h rfl
  · rw [if_neg hk] at h
    exact absurd rfl h

theorem lF_ne (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cn n V) (A : Finset (Pos n))
    (h : lF E p q x A ≠ 0) :
    x A ≠ 0 ∨ ∃ i k : Pos n, adC p q i k ≠ 0 ∧ (cre k * ann i : Module.End ℂ (Cn n V)) x A ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, hall⟩ := hcon
  apply h
  change ((lift n (E p q) + adL p q : Module.End ℂ (Cn n V)) x) A = 0
  rw [LinearMap.add_apply, Pi.add_apply, CompanionTheory.D.LK.lift_apply, h0, map_zero, zero_add]
  unfold adL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply]
  by_cases hc : adC p q i k = 0
  · rw [hc, zero_smul]
  · rw [hall i k hc, smul_zero]

theorem inU_of_adC {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {i k : Pos n}
    (h : adC p q i k ≠ 0) (hi : inU lev i) : inU lev k := by
  unfold adC at h
  unfold inU at hi ⊢
  by_cases h1 : q = (i : Fin n × Fin n).1 ∧ (k : Fin n × Fin n) = (p, (i : Fin n × Fin n).2)
  · rw [h1.2]
    show lev p < lev (i : Fin n × Fin n).2
    rw [hpq, h1.1]
    exact hi
  · by_cases h2 : (i : Fin n × Fin n).2 = p ∧ (k : Fin n × Fin n) = ((i : Fin n × Fin n).1, q)
    · rw [h2.2]
      show lev (i : Fin n × Fin n).1 < lev q
      rw [← hpq, ← h2.1]
      exact hi
    · rw [if_neg h1, if_neg h2, sub_zero] at h
      exact absurd rfl h

theorem lF_suppIn_deg (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (_hlev : Monotone lev) (x : Cn n V)
    (hx : SuppIn (inU lev) x) (p q : Fin n) (hpq : lev p = lev q) :
    SuppIn (inU lev) (lF E p q x) ∧ ∀ j, Deg j x → Deg j (lF E p q x) := by
  unfold SuppIn at hx ⊢
  unfold Deg
  constructor
  · intro A hA l hl
    rcases lF_ne E p q x A hA with h0 | ⟨i, k, hc, hne⟩
    · exact hx A h0 l hl
    · obtain ⟨hk, hi, hx'⟩ := cre_ann_ne i k x A hne
      have hsupp := hx _ hx'
      by_cases hlk : l = k
      · subst hlk
        exact inU_of_adC hpq hc (hsupp i (Finset.mem_insert_self _ _))
      · exact hsupp l (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hlk, hl⟩))
  · intro j hj A hA
    rcases lF_ne E p q x A hA with h0 | ⟨i, k, hc, hne⟩
    · exact hj A h0
    · obtain ⟨hk, hi, hx'⟩ := cre_ann_ne i k x A hne
      have hcard := hj _ hx'
      rw [Finset.card_insert_of_notMem hi, Finset.card_erase_of_mem hk] at hcard
      have hpos : 0 < A.card := Finset.card_pos.2 ⟨k, hk⟩
      omega

end GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp
end
end

