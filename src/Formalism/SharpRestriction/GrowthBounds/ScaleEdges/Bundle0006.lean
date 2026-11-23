module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.GainBoundAt
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RankMulConductorDivLeOne
section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem basis_fin {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] (Sg : Submodule O M)
    {ιb : Type} (b : Module.Basis ιb O Sg) (hc : ∃ T : Submodule O M, IsCompl Sg T) (Pr : M → Prop)
    (hb : ∀ i, Pr (b i : M)) :
    ∃ B : Fin (Module.finrank O Sg) → M, (∀ i, Pr (B i)) ∧ LinearIndependent O B ∧
      ∃ T : Submodule O M, IsCompl (Submodule.span O (Set.range B)) T := by
  classical
  by_cases hfin : Finite ιb
  · have := Fintype.ofFinite ιb
    let e : ιb ≃ Fin (Module.finrank O Sg) :=
      Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
    refine ⟨fun i => (b (e.symm i) : M), fun i => hb _, ?_, ?_⟩
    · exact (b.linearIndependent.map' Sg.subtype (Submodule.ker_subtype Sg)).comp e.symm e.symm.injective
    · have hr : Set.range (fun i => (b (e.symm i) : M)) = Sg.subtype '' Set.range b := by
        rw [← Set.range_comp]
        exact e.symm.surjective.range_comp (fun j => (b j : M))
      obtain ⟨T, hT⟩ := hc
      refine ⟨T, ?_⟩
      rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
      exact hT
  · have := Module.Free.of_basis b
    have hnf : ¬ Module.Finite O Sg := fun h => hfin (Module.Finite.finite_basis b)
    rw [Module.finrank_of_not_finite hnf]
    refine ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, ⊤, ?_⟩
    rw [Set.range_eq_empty, Submodule.span_empty]
    exact isCompl_bot_top

theorem flW_dom {n' m : ℕ} (d : Fin n' → ℕ) : IsDominant (flW (m := m) d) := by
  intro s i j hij
  simp only [flW, Pi.single_apply]
  by_cases hj : j = 0
  · subst hj
    have hi : i = 0 := le_antisymm hij (Fin.zero_le _)
    subst hi
    exact le_refl _
  · rw [if_neg hj]
    split_ifs <;> positivity

theorem restW_dom {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (h : IsDominant lam0) : IsDominant (restW TT lam0) := by
  intro s i j hij
  have hA := h s
  have h1v : (1 : Fin (m + 1)).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hd : (dT TT lam0 s : ℤ) = if s ∈ TT then lam0 s 0 - lam0 s 1 else 0 := by
    unfold dT flatDeg
    split_ifs
    · exact Int.toNat_of_nonneg (sub_nonneg.mpr (hA (Fin.zero_le _)))
    · rfl
  simp only [restW, flW, Pi.sub_apply, Pi.single_apply, hd]
  by_cases hj : j = 0
  · subst hj
    have hi : i = 0 := le_antisymm hij (Fin.zero_le _)
    subst hi
    exact le_refl _
  · have h1j : (1 : Fin (m + 1)) ≤ j := by
      rw [Fin.le_def, h1v]
      have : j.val ≠ 0 := fun h0 => hj (Fin.ext h0)
      omega
    rw [if_neg hj]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl]
      split_ifs
      · linarith [hA h1j]
      · linarith [hA (Fin.zero_le j)]
    · rw [if_neg hi]
      linarith [hA hij]

theorem lambda_zero_eq_product {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    lam0 = flW (dT TT lam0) + restW TT lam0 := by
  funext s i
  simp only [restW, Pi.add_apply, Pi.sub_apply]
  ring

theorem norm_index_count_bound (A A' x u dV Pi q : ℝ) (nb n2 : ℕ) (hA : A ≤ A') (hx : 0 ≤ x) (hu : 0 ≤ u) (hdV : 0 ≤ dV)
    (hPi : 0 ≤ Pi) (hq : 0 < q) (h1 : q⁻¹ * ((1 - A * x) * Pi) ≤ nb) (h2 : u * dV ≤ Pi * n2) :
    (1 - A' * x) * u * dV / q ≤ ((nb * n2 : ℕ) : ℝ) := by
  push_cast
  have hq' : 0 < q⁻¹ := inv_pos.mpr hq
  rcases le_or_gt 0 (1 - A' * x) with hB | hB
  · have e1 : 1 - A' * x ≤ 1 - A * x := by nlinarith
    have s1 : (1 - A' * x) * u * dV ≤ (1 - A' * x) * (Pi * n2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 hB
    have s2 : (1 - A' * x) * (Pi * n2) ≤ (1 - A * x) * (Pi * n2) :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    have s3 : q⁻¹ * ((1 - A * x) * Pi) * n2 ≤ nb * n2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    rw [div_eq_mul_inv]
    calc (1 - A' * x) * u * dV * q⁻¹ ≤ (1 - A * x) * (Pi * n2) * q⁻¹ :=
          mul_le_mul_of_nonneg_right (s1.trans s2) hq'.le
      _ = q⁻¹ * ((1 - A * x) * Pi) * n2 := by ring
      _ ≤ nb * n2 := s3
  · have hn : (1 - A' * x) * u * dV ≤ 0 := by
      have := mul_nonneg hu hdV
      nlinarith
    exact (div_nonpos_of_nonpos_of_nonneg hn hq.le).trans (by positivity)

theorem rank_mul_conductor_div_le_one {C : ℝ} (hC : 2 ≤ C) {p n' m r : ℕ} {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {de h x : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar) :
    ((m + 1 : ℕ) : ℝ) * c0 / a ≤ 1 := by
  unfold Hyps at H
  obtain ⟨hp, hr, -, hN1, -, hY, -, -, -, -, hcS, hsz⟩ := H
  have hcard : 1 ≤ TT.card := by
    have h1 : 1 ≤ orbitWindowCount r de h x := by unfold orbitWindowCount; omega
    have h2 : 1 ≤ r * TT.card := le_trans (Nat.one_le_pow _ _ h1) hN1
    rcases Nat.eq_zero_or_pos TT.card with h0 | h0
    · rw [h0] at h2
      simp at h2
    · exact h0
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hY' : (2 : ℝ) ≤ Y := hr'.trans hY
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hQ : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp'
  have hcS' : (8 : ℝ) ≤ cStar := by exact_mod_cast (by omega : 8 ≤ cStar)
  have hk : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  have hN : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hcard
  obtain ⟨ha, hkc⟩ := num_size C ((m + 1 : ℕ) : ℝ) r TT.card (p ^ goodG' r de h x) cStar c0
    (2 * r * n' * cpp) Y a hC hk hr' hN hQ hcS' (Nat.cast_nonneg _) (by positivity) hY' hsz
  have hle : ((m + 1 : ℕ) : ℝ) * c0 ≤ a := by
    have h0 : 0 ≤ ((m + 1 : ℕ) : ℝ) * c0 := by positivity
    nlinarith [mul_le_mul hN (by linarith : (1 : ℝ) ≤ Y) zero_le_one (by linarith)]
  exact div_le_one_of_le₀ hle (by linarith)

private lemma mul_mul_add_le_of_abs_le (Cdeg CLa C Ct0 s s' w v N : ℝ) (h1 : |Cdeg| ≤ Ct0) (h3 : |CLa| ≤ C)
    (hs : 0 ≤ s) (hss : s ≤ s') (hw : 0 ≤ w) (hv : 0 ≤ v) (hN : 0 ≤ N) :
    Cdeg * N * (CLa * s * w + v) ≤ Ct0 * N * (C * s' * w + v) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans h3
  have hCt0 : 0 ≤ Ct0 := (abs_nonneg _).trans h1
  have hX : |CLa * s * w + v| ≤ C * s' * w + v := by
    have hm : |CLa| * s ≤ C * s' := mul_le_mul h3 hss hs hC0
    calc |CLa * s * w + v| ≤ |CLa * s * w| + |v| := abs_add_le _ _
      _ = |CLa| * s * w + v := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hw, abs_of_nonneg hv]
      _ ≤ C * s' * w + v := by linarith [mul_le_mul_of_nonneg_right hm hw]
  calc Cdeg * N * (CLa * s * w + v) ≤ |Cdeg * N * (CLa * s * w + v)| := le_abs_self _
    _ = |Cdeg| * N * |CLa * s * w + v| := by rw [abs_mul, abs_mul, abs_of_nonneg hN]
    _ ≤ Ct0 * N * (C * s' * w + v) :=
      mul_le_mul (mul_le_mul_of_nonneg_right h1 hN) hX (abs_nonneg _) (mul_nonneg hCt0 hN)

theorem level_lower_bound_terms (Cdeg CLa C Ct0 : ℝ) (h1 : |Cdeg| ≤ Ct0) (h3 : |CLa| ≤ C)
    (p N N₁ Ns L₁ G' k : ℕ) (hNs : Ns ≤ N₁) (hp : 1 ≤ p) (hk : 1 ≤ k) (a : ℝ) (ha : 1 ≤ a) :
    Cdeg * (N : ℝ) * (CLa * (Ns : ℝ) ^ 2 * Real.log a * a / ((p : ℝ) * (k : ℝ)) + a * (p : ℝ) ^ (-(L₁ : ℤ)) +
      (k : ℝ) * (p : ℝ) ^ G') ≤ t0 C Ct0 p N N₁ L₁ G' k a := by
  unfold t0 tableLineDegreeFive.La
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hNs' : (Ns : ℝ) ^ 2 ≤ (N₁ : ℝ) ^ 2 := by
    have : (Ns : ℝ) ≤ N₁ := by exact_mod_cast hNs
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hw : 0 ≤ Real.log a * a / ((p : ℝ) * (k : ℝ)) := by positivity
  have hv : 0 ≤ a * (p : ℝ) ^ (-(L₁ : ℤ)) + (k : ℝ) * (p : ℝ) ^ G' := by positivity
  have key := mul_mul_add_le_of_abs_le Cdeg CLa C Ct0 ((Ns : ℝ) ^ 2) ((N₁ : ℝ) ^ 2) _ _ (N : ℝ) h1 h3 (by positivity) hNs' hw hv
    (Nat.cast_nonneg _)
  refine le_trans (le_of_eq ?_) (key.trans_eq ?_) <;> ring

end Formalism.MainNotions.Pf14
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SPbound
section
noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Pos

variable {n' : ℕ} [NeZero n']

end Pos

section Fr

variable {n' r : ℕ} [NeZero n'] {F : Frames n' r} {L₁ N₁ : ℕ}

private theorem fr_lt_fr_of_lt (hV : F.Valid L₁ N₁) (j : ℤ) {l l' : ℕ} (hll : l < l') (hl' : l' < r) :
    F.fr j l < F.fr j l' := by
  obtain ⟨-, -, hinc, -⟩ := hV
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hll
  induction m with
  | zero => exact hinc j l (by omega)
  | succ m ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hinc j (l + m + 1) (by omega)
    show F.fr j l < F.fr j (l + m + 1 + 1)
    exact lt_trans h1 h2

private theorem fr_le_fr_of_le (hV : F.Valid L₁ N₁) (j : ℤ) {l l' : ℕ} (hll : l ≤ l') (hl' : l' < r) :
    F.fr j l ≤ F.fr j l' := by
  rcases Nat.lt_or_eq_of_le hll with h | rfl
  · exact le_of_lt (fr_lt_fr_of_lt hV j h hl')
  · exact le_rfl

theorem fr_le_last (hV : F.Valid L₁ N₁) (j : ℤ) {l : ℕ} (hl : l < r) : F.fr j l ≤ F.fr j (r - 1) := by
  exact fr_le_fr_of_le hV j (by omega) (by omega)

end Fr

end Formalism.MainNotions.Pf14
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleZpowMono
section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_zpow_mono (w : O) (hw : algebraMap O Kf w ≠ 0) {a b : ℤ} (hab : b ≤ a) (M : Submodule O X) :
    scale (algebraMap O Kf w ^ a) M ≤ scale (algebraMap O Kf w ^ b) M := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_scale.1 hx
  refine mem_scale.2 ⟨w ^ (a - b).toNat • y, M.smul_mem _ hy, ?_⟩
  rw [← algebraMap_smul Kf (w ^ (a - b).toNat) y, smul_smul, map_pow, ← zpow_natCast, ← zpow_add₀ hw]
  congr 2
  rw [Int.toNat_of_nonneg (by omega)]
  ring

theorem scale_mono (c : Kf) {M N : Submodule O X} (h : M ≤ N) : scale c M ≤ scale c N :=
  Submodule.map_mono h

end Scale

section Be

variable {Kf : Type} [Field Kf] {n' m : ℕ}

theorem be_add_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F F' : Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 (F + F') G = be p r lam0 F G + be p r lam0 F' G := by
  unfold be
  rw [smul_add, map_add (f := _)]

theorem be_smulK_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (c : Kf) (F : Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 (c • F) G = c * be p r lam0 F G := by
  unfold be
  rw [smul_comm, map_smul, smul_eq_mul]

end Be

theorem edgeFamOf : EdgeFamOf := by
  intro D hM hBP hInc p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m r fl rest lam0 hnu h1 h2 e he nb n2 T oS tT D1
    cStar c' hc' hD Fvb Sy sh hF1 hF2 hF3 hSy hsh hT
  have hw := w_ne_zero hS
  have hdom : IsDominant lam0 := by
    rw [hnu]
    exact isDominant_add h1 h2
  let eqv : Fin nb × Fin n2 ≃ Fin (nb * n2) := finProdFinEquiv
  let Fs : Fin nb × Fin n2 → Vsp Kf lam0 := fun x => mulV hnu h1 h2 (Fvb x.1) (sh x.2)
  let Ss : Fin nb × Fin n2 → Vsp Kf lam0 := fun x => mulV hnu h1 h2 (Sy x.1) (sh x.2)
  have hdiff : ∀ x, Fs x - Ss x ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r lam0 e) := by
    intro x
    have hz : ((Fs x - Ss x : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ((Fvb x.1 - Sy x.1 : Vsp Kf fl) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
          ((sh x.2 : Vsp Kf rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      simp only [Fs, Ss, AddSubgroupClass.coe_sub, mulV_coe, sub_mul]
    have h0 : sh x.2 ∈ scale (algebraMap O Kf w ^ (0 : ℤ)) (Re p ι σ w r rest e) := by
      rw [zpow_zero]
      exact mem_scale.2 ⟨_, (hsh x.2).1, one_smul _ _⟩
    have h3 := Re_mul D hM p ι σ w hw r hnu h1 h2 e (c' : ℤ) 0 hz (hF2 x.1) h0
    rwa [add_zero] at h3
  have hSs : ∀ x, Ss x ∈ Re p ι σ w r lam0 e := fun x =>
    edge_lattice_mul_of_weight_sum D hM p ι σ w hw r hnu h1 h2 e (z := Ss x) rfl (hSy x.1) (hsh x.2).1
  refine ⟨fun i => Fs (eqv.symm i), ?_, ?_, ?_⟩
  · intro i
    constructor
    · have h3 := HL_mul (O := O) D hM ι σ hnu h1 h2 e.src (algebraMap O Kf w) hw (-(T : ℤ)) (-(oS : ℤ))
        (z := Fs (eqv.symm i)) rfl (hF1 _) (hsh _).2
      have e1 : (-(T : ℤ)) + (-(oS : ℤ)) = -((T + oS : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [e1] at h3
    · have e2 : Fs (eqv.symm i) = Ss (eqv.symm i) + (Fs (eqv.symm i) - Ss (eqv.symm i)) := by abel
      show Fs (eqv.symm i) ∈ Re p ι σ w r lam0 e
      rw [e2]
      exact Submodule.add_mem _ (hSs _) (scale_pos_le w c' _ (hdiff _))
  · intro i e' he' hsrc hne
    have hI := (hInc p n' W Qq O Kf ι σ j w hS m r rest h2 e' he').1
    have hs : sh (eqv.symm i).2 ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (Re p ι σ w r rest e') := by
      apply scale_mono _ hI
      rw [hsrc]
      exact (hsh _).2
    have h3 := Re_mul D hM p ι σ w hw r hnu h1 h2 e' (c' : ℤ) (-(oS : ℤ)) (z := Fs (eqv.symm i)) rfl
      (hF3 _ e' he' hsrc hne) hs
    exact scale_zpow_mono w hw (by omega) _ h3
  · rintro c ⟨i0, hi0⟩
    obtain ⟨G, hG1, hG2, hG3, ⟨a, b, ha, hab⟩⟩ := hT (fun x => c (eqv x))
      ⟨eqv.symm i0, by simpa using hi0⟩
    refine ⟨G, hG1, hG2, hG3, ?_⟩
    have e1 : (∑ i, c i • Fs (eqv.symm i)) =
        (∑ x, c (eqv x) • Ss x) + ∑ x, c (eqv x) • (Fs x - Ss x) := by
      rw [← Finset.sum_add_distrib, ← Equiv.sum_comp eqv]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Equiv.symm_apply_apply, ← smul_add]
      congr 1
      abel
    have hE : (∑ x, c (eqv x) • (Fs x - Ss x)) ∈
        scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r lam0 e) :=
      Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hdiff x)
    obtain ⟨y, hy, hyE⟩ := mem_scale.1 hE
    obtain ⟨z, hz⟩ := ((hBP p n' W Qq O Kf ι σ j w hS m r lam0 hdom e he).1 G).1 hG2 y hy
    have hwc : w ^ c' = (p : O) ^ (D1 + 1) * w ^ (c' - 2 * (D1 + 1)) := by
      rw [← hS.w_sq, ← pow_mul, ← pow_add]
      congr 1
      omega
    obtain ⟨b', hb'⟩ := dvd_of_add (p : O) (p_nonunit hS) D1 a (w ^ (c' - 2 * (D1 + 1)) * z) ⟨b, hab.symm⟩
    refine ⟨a + (p : O) ^ (D1 + 1) * (w ^ (c' - 2 * (D1 + 1)) * z), b', ?_, hb'.symm⟩
    show be p r lam0 (∑ i, c i • Fs (eqv.symm i)) G = _
    rw [e1, be_add_left, ha, ← hyE, be_smulK_left, ← hz, zpow_natCast, ← map_pow, hwc]
    simp only [map_add (f := _), map_mul]
    ring

end Formalism.MainNotions.Pf14
end
end

