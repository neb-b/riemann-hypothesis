module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0007
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.AntisymmetryTowerTheorem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem comp_swap_eq_swapWt {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (x : Ψ × Fin N → ℝ) (τ : Ψ) (a b : Fin N) :
    x ∘ ⇑(Equiv.swap (τ, a) (τ, b)) = fun z : Ψ × Fin N => swapWt τ a b (fun s i => x (s, i)) z.1 z.2 := by
  funext z
  obtain ⟨s, i⟩ := z
  simp only [swapWt, Function.comp_apply, Equiv.swap_apply_def, Prod.mk.injEq]
  by_cases hs : s = τ
  · subst hs
    by_cases hia : i = a
    · subst hia
      simp
    · by_cases hib : i = b
      · subst hib
        simp [hia]
      · simp [hia, hib]
  · simp [hs]

private theorem inWall_and_dominant_of_eq_neighbors {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (hj0 : 1 ≤ j) (hjN : j < N)
    (τ : Ψ) (x : Ψ × Fin N → ℝ)
    (hx : x ∈ Metric.closedBall (fun y : Ψ × Fin N => -(1 / (4 * ((N : ℝ) + 1)) *
        (((y.2 : ℕ) : ℝ) - if y.1 = τ ∧ j ≤ (y.2 : ℕ) then 1 else 0))) (1 / (16 * ((N : ℝ) + 1))))
    (hxe : x (τ, ⟨j - 1, by omega⟩) = x (τ, ⟨j, hjN⟩)) :
    InWall j τ (1 / (8 * ((N : ℝ) + 1))) (fun s i => x (s, i)) ∧
      Dominant (Ψ := Ψ) (N := N) (fun s i => x (s, i)) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (4 * ((N : ℝ) + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδN : δ * ((N : ℝ) + 1) = 1 / 4 := by
    rw [hδ]
    field_simp
  have hr : 1 / (16 * ((N : ℝ) + 1)) = δ / 4 := by
    rw [hδ]
    field_simp
    ring
  have hc : 1 / (8 * ((N : ℝ) + 1)) = δ / 2 := by
    rw [hδ]
    field_simp
    ring
  rw [← hδ, hr] at hx
  rw [hc]
  have hb : ∀ (s : Ψ) (i : Fin N),
      |x (s, i) - -(δ * (((i : ℕ) : ℝ) - if s = τ ∧ j ≤ (i : ℕ) then 1 else 0))| ≤ δ / 4 := by
    intro s i
    have h1 := (dist_pi_le_iff (by linarith)).1 (Metric.mem_closedBall.1 hx) (s, i)
    rwa [Real.dist_eq] at h1
  have G : ∀ (s : Ψ) (a b : Fin N), (b : ℕ) = (a : ℕ) + 1 → ¬ (s = τ ∧ (b : ℕ) = j) →
      δ / 2 ≤ x (s, a) - x (s, b) := by
    intro s a b hab hn
    have hite : (if s = τ ∧ j ≤ (a : ℕ) then (1 : ℝ) else 0) = if s = τ ∧ j ≤ (b : ℕ) then 1 else 0 := by
      by_cases hs : s = τ
      · have hbj : (b : ℕ) ≠ j := fun h => hn ⟨hs, h⟩
        simp only [hs, true_and]
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp [hs]
    have hbR : ((b : ℕ) : ℝ) = ((a : ℕ) : ℝ) + 1 := by exact_mod_cast hab
    have ha := abs_le.1 (hb s a)
    have hb2 := abs_le.1 (hb s b)
    rw [hite] at ha
    rw [hbR] at hb2
    linarith [ha.1, ha.2, hb2.1, hb2.2]
  have hcons : ∀ (s : Ψ) (a b : Fin N), (b : ℕ) = (a : ℕ) + 1 → x (s, b) ≤ x (s, a) := by
    intro s a b hab
    by_cases hs : s = τ ∧ (b : ℕ) = j
    · obtain ⟨rfl, hbj⟩ := hs
      have ha : a = ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩ := Fin.ext (show (a : ℕ) = j - 1 by omega)
      have hb' : b = ⟨j, hjN⟩ := Fin.ext hbj
      have e1 : x (s, b) = x (s, ⟨j, hjN⟩) := congrArg (fun i => x (s, i)) hb'
      have e2 : x (s, a) = x (s, ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩) :=
        congrArg (fun i => x (s, i)) ha
      rw [e1, e2]
      exact hxe.ge
    · have := G s a b hab hs
      linarith
  have hdom : ∀ (s : Ψ) (k : ℕ) (a b : Fin N), (b : ℕ) = (a : ℕ) + k → x (s, b) ≤ x (s, a) := by
    intro s k
    induction k with
    | zero =>
      intro a b h
      have : b = a := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro a b h
      have hbl := b.isLt
      have hc : (a : ℕ) + k < N := by omega
      exact le_trans (hcons s ⟨(a : ℕ) + k, hc⟩ b (show (b : ℕ) = (a : ℕ) + k + 1 by omega))
        (ih a ⟨(a : ℕ) + k, hc⟩ rfl)
  refine ⟨?_, ?_⟩
  · show _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun s =>
        (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
      show ‖x (s, i)‖ ≤ 1 / 2
      rw [Real.norm_eq_abs]
      have hiN : ((i : ℕ) : ℝ) ≤ N := by exact_mod_cast i.isLt.le
      have hI0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) - (if s = τ ∧ j ≤ (i : ℕ) then 1 else 0) := by
        split_ifs with hh
        · have h1 : 1 ≤ (i : ℕ) := le_trans hj0 hh.2
          have h2 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h1
          linarith
        · simp
      have hI1 : ((i : ℕ) : ℝ) - (if s = τ ∧ j ≤ (i : ℕ) then 1 else 0) ≤ N := by
        split_ifs <;> linarith
      have hA := mul_nonneg hδpos.le hI0
      have hB := mul_le_mul_of_nonneg_left hI1 hδpos.le
      have h1 := abs_le.1 (hb s i)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2]
    · simp only [gap, ent, dite_eq_left (show j - 1 < N by omega), dite_eq_left hjN]
      exact sub_eq_zero.2 hxe
    · intro τ' hτ'
      simp only [gap, ent, dite_eq_left (show j - 1 < N by omega), dite_eq_left hjN]
      exact G τ' ⟨j - 1, by omega⟩ ⟨j, hjN⟩ (show j = j - 1 + 1 by omega) (fun h => hτ' h.1)
    · intro s i hi hij
      simp only [ent, dite_eq_left (show i < N by omega), dite_eq_left hi]
      exact G s ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl (fun h => hij h.2)
  · intro s a b hab
    exact hdom s ((b : ℕ) - (a : ℕ)) a b (by have := Fin.le_iff_val_le_val.1 hab; omega)

set_option maxHeartbeats 800000 in
open GroundTheory.Heights₂.Heights in
theorem antisymmetry_tower_theorem : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh := by
  intro hS II Ψ _ _ N T hh hprop hW h8 h9
  obtain ⟨hvol, -, -⟩ := hprop
  have hj0 : 1 ≤ T.j := T.j_pos
  have hjN : T.j < N := T.j_lt
  have hv : 0 < T.volT := by
    show 0 < ∑ c : T.Comp, T.vol c
    exact Finset.sum_pos (fun c _ => hvol c) Finset.univ_nonempty
  obtain ⟨h, hhom, hev, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional (Ψ × Fin N) (dimFl Ψ N + 1) hh
  let x0 : Ψ → Ψ × Fin N → ℝ := fun τ y => -(1 / (4 * ((N : ℝ) + 1)) *
    (((y.2 : ℕ) : ℝ) - if y.1 = τ ∧ T.j ≤ (y.2 : ℕ) then 1 else 0))
  let K : Ψ → Set (Ψ × Fin N → ℝ) := fun τ =>
    diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ∩ Metric.closedBall (x0 τ) (1 / (16 * ((N : ℝ) + 1)))
  have hK : ∀ τ : Ψ, IsCompact (K τ) ∧ K τ ⊆ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ∧
      (∃ O : Set (Ψ × Fin N → ℝ), IsOpen O ∧
        (O ∩ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩).Nonempty ∧
        O ∩ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ⊆ K τ) ∧
      ∀ x ∈ K τ, eval x h = 0 := by
    intro τ
    have hHc : IsClosed (diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩) :=
      isClosed_eq (continuous_apply _) (continuous_apply _)
    refine ⟨(isCompact_closedBall _ _).inter_left hHc, Set.inter_subset_left,
      ⟨Metric.ball (x0 τ) (1 / (16 * ((N : ℝ) + 1))), Metric.isOpen_ball,
        ⟨x0 τ, Metric.mem_ball_self (by positivity), ?_⟩, ?_⟩, ?_⟩
    · show x0 τ (τ, ⟨T.j - 1, by omega⟩) = x0 τ (τ, ⟨T.j, hjN⟩)
      simp [x0, show ¬ T.j ≤ T.j - 1 by omega, Nat.cast_sub hj0]
    · rintro x ⟨hxO, hxH⟩
      exact ⟨hxH, Metric.ball_subset_closedBall hxO⟩
    · rintro x ⟨hxH, hxB⟩
      obtain ⟨-, hdom⟩ := inWall_and_dominant_of_eq_neighbors hj0 hjN τ x hxB hxH
      rw [hev x]
      exact h9.1 (fun s i => x (s, i)) hdom
        ⟨τ, ⟨T.j - 1, by omega⟩, ⟨T.j, hjN⟩, (show T.j = T.j - 1 + 1 by omega), hxH⟩
  obtain ⟨C0, hC⟩ := hS Ψ N T.j (by omega) hjN h K hK
  obtain ⟨CW, B₁, hB⟩ := hW (1 / (8 * ((N : ℝ) + 1))) (by positivity)
  unfold RootTower.ThmB
  refine ⟨C0 * CW, max B₁ 2, fun B hB₂ => ?_⟩
  have hB1 : B₁ ≤ B := le_trans (le_max_left _ _) hB₂
  have hB2 : 2 ≤ B := le_trans (le_max_right _ _) hB₂
  let L : RP Ψ N →ₗ[ℝ] ℝ :=
    ∑ c : T.Comp, ((T.M B c).PP II).comp (rename (some : Ψ × Fin N → Option (Ψ × Fin N))).toLinearMap
  have hL : ∀ F, L F = T.PPt II B F := by
    intro F
    simp [L, RootTower.PPt, RootTower.PPc, toA, LinearMap.sum_apply]
  obtain ⟨P, hPhom, hPev, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional (Ψ × Fin N) (dimFl Ψ N + 1) L
  have hQev : ∀ x : Ψ × Fin N → ℝ, eval x (P - T.volT • h) =
      (L - T.volT • hh) ((-∑ z, MvPolynomial.C (x z) * X z) ^ (dimFl Ψ N + 1)) := by
    intro x
    rw [map_sub, MvPolynomial.smul_eval, hPev, hev]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hQhom : (P - T.volT • h).IsHomogeneous (dimFl Ψ N + 1) :=
    (mem_homogeneousSubmodule _ _).1 (Submodule.sub_mem _ ((mem_homogeneousSubmodule _ _).2 hPhom)
      (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).2 hhom)))
  have key : ∀ F, T.PPt II B F - T.volT * hh F = ∑ c, (T.PPc II B c F - T.vol c * hh F) := by
    intro F
    simp only [RootTower.PPt, RootTower.volT, Finset.sum_sub_distrib, Finset.sum_mul]
  have hanti : P - T.volT • h ∈ antisymSpace Ψ N T.j := by
    show _ ∧ _
    refine ⟨?_, ?_⟩
    · have hd : antisymDegree Ψ N + 1 = dimFl Ψ N + 1 := by
        simp only [antisymDegree, dimFl, Nat.choose_two_right]
      rw [hd]
      exact (mem_homogeneousSubmodule _ _).2 hQhom
    · rintro σ ⟨τ, a, b, hab, hj, rfl⟩
      have hbj : (b : ℕ) ≠ T.j := by omega
      apply MvPolynomial.funext
      intro x
      rw [eval_rename, map_neg, hQev, hQev, comp_swap_eq_swapWt x τ a b]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL]
      rw [key, key]
      have hsum := Finset.sum_congr rfl fun c (_ : c ∈ (Finset.univ : Finset T.Comp)) =>
        h8 B hB2 c τ a b hab hbj (fun s i => x (s, i))
      rw [Finset.sum_neg_distrib] at hsum
      exact hsum
  have hsmall : ∀ τ : Ψ, ∀ x ∈ K τ, |eval x P| ≤ CW * Real.log B / B := by
    rintro τ x ⟨hxH, hxB⟩
    obtain ⟨hwall, -⟩ := inWall_and_dominant_of_eq_neighbors hj0 hjN τ x hxB hxH
    rw [hPev x, hL]
    exact hB B hB1 τ (fun s i => x (s, i)) hwall
  obtain ⟨l, hl, hlc⟩ := hC P T.volT (CW * Real.log B / B) hanti hsmall
  obtain ⟨α, β, hαβ⟩ := GlobalTheory.T.antisymmetric_perturbation_bound Ψ N T.j (L - T.volT • hh) T.volT (C0 * (CW * Real.log B / B))
    (P - T.volT • h) l hv (fun lam => hQev _) hQhom hl hlc
  refine ⟨α, β, fun m hm => ?_⟩
  have h1 := hαβ m hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL] at h1
  rw [show C0 * CW * Real.log B / B = C0 * (CW * Real.log B / B) by ring]
  refine (le_of_eq ?_).trans h1
  congr 1
  ring

end RootFieldNumerics
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMultilinearExpansion
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

open Ii in
theorem intersection_multilinear_expansion : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin d → J → ℤ), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (fun k => combLine ℓ (n k)) = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) := by
  intro II hII K _ ι _ P d J _ _ ℓ n hP hℓ
  have hsm : ∀ c : J → ℤ, IsSmoothHerm (combLine ℓ c) := fun c => (combLine_smooth_conj_invariant K ι J ℓ c).1 hℓ
  have key : ∀ (c : Fin d → J → ℤ) (k : Fin d) (v : J → ℤ),
      II K ι P d (fun i => combLine ℓ (Function.update c k v i)) =
        ∑ j, (v j : ℝ) * II K ι P d (Function.update (fun i => combLine ℓ (c i)) k (ℓ j)) := by
    intro c k v
    have e : (fun i => combLine ℓ (Function.update c k v i)) =
        Function.update (fun i => combLine ℓ (c i)) k (combLine ℓ v) := by
      funext i
      by_cases h : i = k
      · subst h
        simp
      · simp [Function.update_of_ne h]
    rw [e, intersection_multilinear_one_position II hII K ι P d _ k J ℓ v hP (fun i => hsm _) hℓ]
  let f : MultilinearMap (Int.castRingHom ℝ) (fun _ : Fin d => J → ℤ) ℝ :=
    { toFun := fun c => II K ι P d (fun i => combLine ℓ (c i))
      map_update_add' := by
        intro inst c k x y
        obtain rfl := Subsingleton.elim inst (instDecidableEqFin d)
        simp only [key, ← Finset.sum_add_distrib, Pi.add_apply, Int.cast_add, add_mul]
      map_update_smul' := by
        intro inst c k a x
        obtain rfl := Subsingleton.elim inst (instDecidableEqFin d)
        simp only [key, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum, mul_assoc]
        rfl }
  have hn : (fun k => n k) = fun k => ∑ j, n k j • (Pi.single j (1 : ℤ) : J → ℤ) := by
    funext k
    conv_lhs => rw [← Finset.univ_sum_single (n k)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ext j'
    by_cases h : j' = j
    · subst h
      simp
    · simp [Pi.single_apply, h]
  calc II K ι P d (fun k => combLine ℓ (n k))
      = f (fun k => ∑ j, n k j • (Pi.single j (1 : ℤ) : J → ℤ)) := by
        rw [← hn]
        rfl
    _ = ∑ r : Fin d → J, f (fun k => n k (r k) • (Pi.single (r k) (1 : ℤ) : J → ℤ)) := f.map_sum _
    _ = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [f.map_smul_univ]
        simp [f, smul_eq_mul, combLine_single]

end RootFieldNumerics
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.SumChooseLe
section
noncomputable section

open Polynomial

namespace RootFieldNumerics.M5

variable {N : ℕ}

theorem gdet_rho (N : ℕ) : ∃ c : ℝ, ∀ v : Fin N → Polynomial ℝ,
    gdet (fun c' : Fin N => N - 1 - (c' : ℕ)) v = Polynomial.C c * ∏ a, ∏ b ∈ Finset.Ioi a, (v b - v a) := by
  refine ⟨(∏ c : Fin N, (((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ)⁻¹) *
    (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤ) : ℝ)), fun v => ?_⟩
  have hM : (Matrix.of fun (c b : Fin N) => C ((((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ))⁻¹ * v b ^ (N - 1 - (c : ℕ)))
      = Matrix.of fun (c b : Fin N) => C ((((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ))⁻¹ *
        ((Matrix.vandermonde v).transpose.submatrix Fin.revPerm id) c b := by
    ext c b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Fin.revPerm_apply, Fin.val_rev, id]
    rw [show N - ((c : ℕ) + 1) = N - 1 - (c : ℕ) by omega]
  unfold gdet
  rw [hM, Matrix.det_mul_column, Matrix.det_permute, Matrix.det_transpose, Matrix.det_vandermonde]
  simp only [map_mul, map_prod, map_intCast]
  ring

theorem sum_choose_le (M n : ℕ) : ∑ i ∈ Finset.range M, n.choose i ≤ 2 ^ n := by
  rw [← Nat.sum_range_choose]
  apply Finset.sum_le_sum_of_ne_zero
  intro i _ hi
  rw [Finset.mem_range]
  by_contra h
  exact hi (Nat.choose_eq_zero_of_lt (by omega))

theorem pow_eq_sum_rr (w : ℕ → Polynomial ℝ) (m a : ℕ) (ha : a < N) :
    w a ^ m = ∑ c : Fin N, (rr w m N).coeff (N - 1 - (c : ℕ)) * w a ^ (N - 1 - (c : ℕ)) := by
  have hd : (rr w m N).natDegree < N := by
    have : (rr w m N).natDegree ≤ N - 1 :=
      natDegree_le_iff_coeff_eq_zero.mpr fun n hn => rr_coeff_big w m N n (by omega)
    omega
  rw [← rr_eval w m N a ha, eval_eq_sum_range' hd, ← Finset.sum_range_reflect,
    ← Fin.sum_univ_eq_sum_range (fun i => (rr w m N).coeff (N - 1 - i) * w a ^ (N - 1 - i))]

theorem gdet_bump (k : ℕ) (hk : 1 ≤ k) (U : ℝ) (hU : 0 < U) (v : Fin N → Polynomial ℝ)
    (hv : ∀ b, Maj (v b) U (1 / U)) :
    ∃ r : Polynomial ℝ, Maj r (2 ^ (k - 1) / (k.factorial : ℝ) * U ^ k) (k / U) ∧
      ∑ c : Fin N, gdet (fun c' : Fin N => N - 1 - (c' : ℕ) + if c' = c then k else 0) v =
        r * gdet (fun c' : Fin N => N - 1 - (c' : ℕ)) v := by
  classical
  set w : ℕ → Polynomial ℝ := fun a => if h : a < N then v ⟨a, h⟩ else 0 with hw
  have hwv : ∀ b : Fin N, w b = v b := fun b => by simp [hw, b.isLt]
  have hwM : ∀ a, Maj (w a) U (1 / U) := by
    intro a
    by_cases h : a < N
    · simp only [hw, dif_pos h]
      exact hv _
    · simp only [hw, dif_neg h]
      exact Maj.zero hU.le (by positivity)
  refine ⟨∑ c : Fin N, C ((((N - 1 - (c : ℕ) + k).factorial : ℕ) : ℝ)⁻¹ * (((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ)) *
      (rr w (N - 1 - (c : ℕ) + k) N).coeff (N - 1 - (c : ℕ)), ?_, ?_⟩
  · have hk0 : (0 : ℝ) ≤ k / U := by positivity
    have h1 := Maj.sum Finset.univ
      (fun c : Fin N => C ((((N - 1 - (c : ℕ) + k).factorial : ℕ) : ℝ)⁻¹ * (((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ)) *
        (rr w (N - 1 - (c : ℕ) + k) N).coeff (N - 1 - (c : ℕ)))
      (fun c : Fin N => ((((N - 1 - (c : ℕ) + k).factorial : ℕ) : ℝ)⁻¹ * (((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ)) *
        ((cnt (N - 1 - (c : ℕ)) k N : ℝ) * U ^ k)) hk0
      (fun c _ => (rr_maj U hU w hwM _ _ k N rfl).C_mul _ (by positivity))
    apply h1.mono hk0 _ le_rfl
    have hterm : ∀ c : Fin N, ((((N - 1 - (c : ℕ) + k).factorial : ℕ) : ℝ)⁻¹ * (((N - 1 - (c : ℕ)).factorial : ℕ) : ℝ)) *
        ((cnt (N - 1 - (c : ℕ)) k N : ℝ) * U ^ k) = ((k - 1).choose (c : ℕ) : ℝ) / (k.factorial : ℝ) * U ^ k := by
      intro c
      have hc : N - 1 - (c : ℕ) < N := by omega
      have hk1 : k ≠ 0 := by omega
      simp only [cnt, if_pos hc, if_neg hk1]
      rw [show N - 1 - (N - 1 - (c : ℕ)) = (c : ℕ) by omega]
      have hf := Nat.add_choose_mul_factorial_mul_factorial k (N - 1 - (c : ℕ))
      rw [add_comm k] at hf
      have hf' : (((N - 1 - (c : ℕ) + k).choose (N - 1 - (c : ℕ)) : ℕ) : ℝ) * (k.factorial : ℝ) *
          ((N - 1 - (c : ℕ)).factorial : ℝ) = ((N - 1 - (c : ℕ) + k).factorial : ℝ) := by
        exact_mod_cast hf
      push_cast
      rw [← hf']
      have h2 : (k.factorial : ℝ) ≠ 0 := by positivity
      have h3 : ((N - 1 - (c : ℕ)).factorial : ℝ) ≠ 0 := by positivity
      have h4 : (((N - 1 - (c : ℕ) + k).choose (N - 1 - (c : ℕ)) : ℕ) : ℝ) ≠ 0 := by
        have := Nat.choose_pos (show N - 1 - (c : ℕ) ≤ N - 1 - (c : ℕ) + k by omega)
        positivity
      field_simp
    rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.sum_mul, ← Finset.sum_div]
    have hs : (∑ c : Fin N, ((k - 1).choose (c : ℕ) : ℝ)) ≤ 2 ^ (k - 1) := by
      have := sum_choose_le N (k - 1)
      rw [← Fin.sum_univ_eq_sum_range (fun i => (k - 1).choose i) N] at this
      exact_mod_cast this
    gcongr
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [gdet]
    set A : Matrix (Fin N) (Fin N) (Polynomial ℝ) := Matrix.of fun (c' b : Fin N) =>
      C ((((N - 1 - (c' : ℕ)).factorial : ℕ) : ℝ))⁻¹ * v b ^ (N - 1 - (c' : ℕ)) with hA
    have hrow : (Matrix.of fun (c' b : Fin N) =>
        C ((((N - 1 - (c' : ℕ) + if c' = c then k else 0).factorial : ℕ) : ℝ))⁻¹ *
          v b ^ (N - 1 - (c' : ℕ) + if c' = c then k else 0))
        = A.updateRow c (∑ c' : Fin N,
          (C ((((N - 1 - (c : ℕ) + k).factorial : ℕ) : ℝ)⁻¹ * (((N - 1 - (c' : ℕ)).factorial : ℕ) : ℝ)) *
            (rr w (N - 1 - (c : ℕ) + k) N).coeff (N - 1 - (c' : ℕ))) • A c') := by
      refine Matrix.ext fun i b => ?_
      rw [Matrix.updateRow_apply]
      by_cases hi : i = c
      · subst hi
        simp only [if_pos rfl, if_true, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA]
        rw [← hwv b, pow_eq_sum_rr w _ b b.isLt, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c' _ => ?_)
        have hP : C ((((N - 1 - (c' : ℕ)).factorial : ℕ) : ℝ)) * C ((((N - 1 - (c' : ℕ)).factorial : ℕ) : ℝ))⁻¹
            = (1 : Polynomial ℝ) := by
          rw [← map_mul, mul_inv_cancel₀ (by positivity), map_one]
        rw [map_mul]
        linear_combination (-(C ((((N - 1 - (i : ℕ) + k).factorial : ℕ) : ℝ))⁻¹ *
          (rr w (N - 1 - (i : ℕ) + k) N).coeff (N - 1 - (c' : ℕ)) * w b ^ (N - 1 - (c' : ℕ)))) * hP
      · simp only [if_neg hi, Matrix.of_apply, hA, add_zero]
    rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]

end RootFieldNumerics.M5
end
end

