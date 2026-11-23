module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixOneAddPowSubEntryLe
section
namespace GlobalTheory

open Matrix

theorem ultra_matrix_mul_entry_le {E : Type} [NormedField E] [IsUltrametricDist E] {n : Type} [Fintype n]
    [DecidableEq n] (A B : Matrix n n E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : n) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) ?_
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha

theorem matrix_one_add_pow_sub_entry_le :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (Y : Matrix n n E) (t : ℝ), 0 ≤ t → t ≤ 1 → (∀ i j, ‖Y i j‖ ≤ t) →
      ∀ (m : ℕ) i j, ‖((1 + Y) ^ m - 1 - (m : E) • Y) i j‖ ≤ t ^ 2 := by
  intro E _ _ n _ _ Y t ht0 ht1 hY m
  induction m with
  | zero => intro i j; simp; positivity
  | succ m ih =>
    have key : (1 + Y) ^ (m + 1) - 1 - ((m + 1 : ℕ) : E) • Y
        = ((1 + Y) ^ m - 1 - (m : E) • Y) + ((1 + Y) ^ m - 1 - (m : E) • Y) * Y
          + (m : E) • (Y * Y) := by
      rw [pow_succ]
      push_cast
      simp only [mul_add, add_mul, mul_one, one_mul, sub_mul, smul_mul_assoc, add_smul, one_smul]
      abel
    intro i j
    rw [key]
    have h1 := ih i j
    have h2 : ‖(((1 + Y) ^ m - 1 - (m : E) • Y) * Y) i j‖ ≤ t ^ 2 := by
      have := ultra_matrix_mul_entry_le _ Y (t ^ 2) t (by positivity) ht0 ih hY i j
      calc _ ≤ t ^ 2 * t := this
        _ ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
        _ = t ^ 2 := mul_one _
    have h3 : ‖((m : E) • (Y * Y)) i j‖ ≤ t ^ 2 := by
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
      have := ultra_matrix_mul_entry_le Y Y t t ht0 ht0 hY hY i j
      calc ‖(m : E)‖ * ‖(Y * Y) i j‖ ≤ 1 * (t * t) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one E m) this (norm_nonneg _) zero_le_one
        _ = t ^ 2 := by ring
    rw [Matrix.add_apply, Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)) h3)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixRankMapField
section
open Matrix
namespace GlobalTheory
private lemma rank_fromBlocks_one_zero_lemma {F G : Type} [Field F] [Field G] (r s : ℕ) :
    (fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0 (0 : Matrix (Fin s) (Fin s) F)).rank =
      (fromBlocks (1 : Matrix (Fin r) (Fin r) G) 0 0 (0 : Matrix (Fin s) (Fin s) G)).rank := by
  classical
  rw [← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, rank_diagonal,
    ← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => by cases i <;> simp)
theorem matrix_rank_map_field {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := exists_rank_normal_form M
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det _).1 hV
  have hUd : IsUnit U.det := (isUnit_iff_isUnit_det _).1 hU
  have hV' : IsUnit (V.map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hVd.map φ
  have hU' : IsUnit (U.map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hUd.map φ
  have hmap : V.map φ * M.map φ * U.map φ =
      (fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) L) 0 0 0).submatrix e e := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h, ← submatrix_map, fromBlocks_map]
    simp
  calc (M.map φ).rank = (V.map φ * M.map φ * U.map φ).rank := by
        rw [rank_mul_eq_left_of_isUnit_det _ _ hU', rank_mul_eq_right_of_isUnit_det _ _ hV']
    _ = (fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) K) 0 0 0).rank := by
        rw [hmap, rank_submatrix]
        exact rank_fromBlocks_one_zero_lemma _ _
    _ = (V * M * U).rank := by rw [h, rank_submatrix]
    _ = M.rank := by
        rw [rank_mul_eq_left_of_isUnit_det _ _ hUd, rank_mul_eq_right_of_isUnit_det _ _ hVd]
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxIdealExactPowDvdSpanPrime
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem maxIdeal_exact_pow_dvd_span_prime : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsMaximal], ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ∃ (e' : ℕ) (J : Ideal (𝓞 L)), 0 < e' ∧ e' ≤ e ∧ la ⊔ J = ⊤ ∧ Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e' * J := by
  intro L _ _ l e _ la hmax hin hout
  classical
  have hex : ∃ k, ((l : ℕ) : 𝓞 L) ∉ la ^ (k + 1) := ⟨e, hout⟩
  have hspec : ((l : ℕ) : 𝓞 L) ∉ la ^ (Nat.find hex + 1) := Nat.find_spec hex
  have hle : Nat.find hex ≤ e := Nat.find_min' hex hout
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso; rw [h, zero_add, pow_one] at hspec; exact hspec hin
    · exact h
  have hmem : ((l : ℕ) : 𝓞 L) ∈ la ^ Nat.find hex := by
    have h1 := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    rw [not_not] at h1
    have h4 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rwa [h4] at h1
  have hdvd : la ^ Nat.find hex ∣ Ideal.span {((l : ℕ) : 𝓞 L)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hmem
  obtain ⟨J, hJ⟩ := hdvd
  refine ⟨Nat.find hex, J, hpos, hle, ?_, hJ⟩
  by_contra hne
  have hJle : J ≤ la := by
    have h2 := hmax.eq_of_le hne le_sup_left
    calc J ≤ la ⊔ J := le_sup_right
      _ = la := h2.symm
  apply hspec
  have h3 : Ideal.span {((l : ℕ) : 𝓞 L)} ≤ la ^ (Nat.find hex + 1) := by
    rw [hJ, pow_succ]; exact Ideal.mul_mono_right hJle
  exact h3 (Ideal.subset_span (Set.mem_singleton _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmulTopOfEntries
section
namespace GlobalTheory.SpanOfResidue

theorem mem_smul_top_of_entries {A : Type} [CommRing A] {r : ℕ} (I : Ideal A)
    (d : Matrix (Fin r) (Fin r) A) (hd : ∀ i j, d i j ∈ I) :
    d ∈ I • (⊤ : Submodule A (Matrix (Fin r) (Fin r) A)) := by
  rw [Matrix.matrix_eq_sum_single d]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h : Matrix.single i j (d i j) = d i j • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  exact Submodule.smul_mem_smul (hd i j) Submodule.mem_top

theorem span_eq_top_of_residue {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  have key : ∀ y ∈ Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)),
      ∃ n ∈ Submodule.span A (Set.range f),
        Matrix.map n (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A) = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨f i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      ext i j
      simp
    | add x y _ _ hx hy =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine ⟨n + m, Submodule.add_mem _ hn hm, ?_⟩
      ext i j
      simp
    | smul c x _ hx =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨a • n, Submodule.smul_mem _ a hn, ?_⟩
      ext i j
      simp
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal A)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro x _
  obtain ⟨n, hn, hnx⟩ := key (Matrix.map x (IsLocalRing.residue A)) (h ▸ Submodule.mem_top)
  have hx : x = n + (x - n) := by abel
  rw [hx]
  refine Submodule.add_mem_sup hn (mem_smul_top_of_entries _ _ fun i j => ?_)
  rw [← IsLocalRing.residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun hnx i) j).symm

end GlobalTheory.SpanOfResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanIndicatorLowerSetsFinitePoset
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem mem_span_indicator_lowerSets :
    ∀ (X L : Type) [Fintype L] [PartialOrder L] (ρ : X → Option L) (Φ : X → ℂ),
      (∀ x, ρ x = none → Φ x = 0) → (∀ x x', ρ x = ρ x' → Φ x = Φ x') →
      Φ ∈ Submodule.span ℂ {Ψ | ∃ l : L, Ψ = Set.indicator {x | ∃ l', ρ x = some l' ∧ l' ≤ l}
        (fun _ => (1 : ℂ))} := by
  classical
  intro X L _ _ ρ Φ h0 hΦ
  set S := Submodule.span ℂ {Ψ : X → ℂ | ∃ l : L, Ψ = Set.indicator
    {x | ∃ l', ρ x = some l' ∧ l' ≤ l} (fun _ => (1 : ℂ))} with hS
  have key : ∀ l : L, Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) ∈ S := by
    intro l
    induction l using WellFoundedLT.induction with
    | ind l ih =>
      have hsum : Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) =
          Set.indicator {x | ∃ l', ρ x = some l' ∧ l' ≤ l} (fun _ => (1 : ℂ)) -
            ∑ l' ∈ Finset.univ.filter (· < l),
              Set.indicator {x | ρ x = some l'} (fun _ => (1 : ℂ)) := by
        funext x
        simp only [Pi.sub_apply, Finset.sum_apply, Set.indicator_apply, Set.mem_setOf_eq]
        cases hx : ρ x with
        | none => simp
        | some m =>
          have h1 : (∃ l', some m = some l' ∧ l' ≤ l) ↔ m ≤ l := by simp
          simp only [Option.some.injEq, h1]
          rw [Finset.sum_ite_eq]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hml : m = l
          · subst hml; simp
          · by_cases hle : m ≤ l
            · have hlt : m < l := lt_of_le_of_ne hle hml
              simp [hml, hle, hlt]
            · have hlt : ¬ m < l := fun h => hle h.le
              simp [hml, hle, hlt]
      rw [hsum]
      exact S.sub_mem (Submodule.subset_span ⟨l, rfl⟩)
        (S.sum_mem fun l' hl' => ih l' (by simpa using hl'))
  let c : L → ℂ := fun l => if h : ∃ x, ρ x = some l then Φ h.choose else 0
  have hdecomp : Φ = ∑ l, c l • Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_setOf_eq,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    cases hx : ρ x with
    | none => simpa using h0 x hx
    | some m =>
      simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hex : ∃ y, ρ y = some m := ⟨x, hx⟩
      simp only [c, dif_pos hex]
      exact hΦ _ _ (hx.trans hex.choose_spec.symm)
  rw [hdecomp]
  exact S.sum_mem fun l _ => S.smul_mem _ (key l)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanKilledUnionAverages
section
namespace GlobalTheory

private theorem exists_equivariant_projection_onto_invariant_submodule {G M : Type} [Group G] [Fintype G] [AddCommGroup M]
    [Module ℂ M] (S W : Submodule ℂ M) (π : G → Module.End ℂ M)
    (h1 : ∀ v ∈ S, π 1 v = v)
    (hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v))
    (hWS : W ≤ S) (hW : ∀ g, ∀ w ∈ W, π g w ∈ W) :
    ∃ P : M →ₗ[ℂ] M, (∀ x, P x ∈ W) ∧ (∀ w ∈ W, P w = w) ∧
      (∀ g, ∀ x ∈ S, P (π g x) = π g (P x)) := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl W
  refine ⟨(Fintype.card G : ℂ)⁻¹ • ∑ g, π g⁻¹ ∘ₗ W.projection q hq ∘ₗ π g,
    ?_, ?_, ?_⟩
  · intro x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    exact W.smul_mem _ (W.sum_mem fun g _ => hW _ _ (Submodule.projection_apply_mem _ _))
  · intro w hw
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    have key : ∀ g : G, π g⁻¹ (W.projection q hq (π g w)) = w := by
      intro g
      rw [Submodule.projection_apply_of_mem_left hq (hW g w hw), ← hmul _ _ w (hWS hw)]
      simp [h1 w (hWS hw)]
    simp only [key, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
  · intro h x hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    refine congrArg (fun y => (Fintype.card G : ℂ)⁻¹ • y) ?_
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft]
    rw [← hmul _ _ x hx, ← hmul _ h _ (hWS (Submodule.projection_apply_mem _ _))]
    simp only [mul_inv_rev, inv_mul_cancel_right]

theorem mem_span_killed_union_averages {G M : Type} [Group G] [Fintype G] [AddCommGroup M]
    [Module ℂ M] (S : Submodule ℂ M) (π : G → Module.End ℂ M)
    (hS : ∀ g, ∀ v ∈ S, π g v ∈ S) (h1 : ∀ v ∈ S, π 1 v = v)
    (hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v))
    (C : Set (G → ℂ)) (hC : ∀ c ∈ C, ∀ x : G, (fun g => c (x * g * x⁻¹)) ∈ C)
    (v : M) (hv : v ∈ S) :
    v ∈ Submodule.span ℂ ({w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} ∪
      {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}) := by
  classical
  have hAS : ∀ (c : G → ℂ), ∀ w ∈ S, ∑ g, c g • π g w ∈ S := fun c w hw =>
    S.sum_mem fun g _ => S.smul_mem _ (hS g w hw)
  have hWS : Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} ≤ S :=
    Submodule.span_le.2 (by rintro u ⟨c, -, w, hw, rfl⟩; exact hAS c w hw)
  have hWst : ∀ h, ∀ u ∈ Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w},
      π h u ∈ Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} := by
    intro h u hu
    have hle : Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w} ≤
        (Submodule.span ℂ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}).comap (π h) := by
      refine Submodule.span_le.2 ?_
      rintro u ⟨c, hc, w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Submodule.subset_span ⟨fun k => c (h * k * h⁻¹), hC c hc h, π h w, hS h w hw, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv,
        map_smul]
      rw [show h * (h⁻¹ * g * h) * h⁻¹ = g by group, ← hmul _ _ w hw, ← hmul _ _ w hw,
        show g * h = h * (h⁻¹ * g * h) by group]
    exact hle hu
  obtain ⟨P, hPW, hPid, hPc⟩ := exists_equivariant_projection_onto_invariant_submodule S _ π h1 hmul hWS hWst
  have hPv : P v ∈ S := hWS (hPW v)
  have hPc' : ∀ g, P (π g v) = π g (P v) := fun g => hPc g v hv
  have hkill : v - P v ∈ {w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} := by
    refine ⟨S.sub_mem hv hPv, fun c hc => ?_⟩
    have hA : ∑ g, c g • π g (P v) = P (∑ g, c g • π g v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hPc']
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib, hA]
    rw [hPid _ (Submodule.subset_span ⟨c, hc, v, hv, rfl⟩), sub_self]
  have hsum := Submodule.add_mem _ (Submodule.subset_span (Set.mem_union_left _ hkill))
    (Submodule.span_mono Set.subset_union_right (hPW v))
  rwa [sub_add_cancel] at hsum

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicDvdXPowCardSubOneExistsRoot
section
open Polynomial IsLocalRing

namespace GlobalTheory

theorem monic_dvd_X_pow_card_sub_one_exists_root :
    ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]),
      f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 →
        ∃ y : S, f.eval y = 0 := by
  intro S _ _ _ f hmon hdeg hdvd
  classical
  letI : Fintype (ResidueField S) := Fintype.ofFinite _
  have hQ : Nat.card (ResidueField S) = Fintype.card (ResidueField S) := Nat.card_eq_fintype_card
  set Q := Fintype.card (ResidueField S) with hQdef
  set g : (ResidueField S)[X] := f.map (residue S) with hgdef
  have hgm : g.Monic := hmon.map _
  have hgdeg : g.natDegree ≠ 0 := by rw [hgdef, hmon.natDegree_map]; exact hdeg
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hdvd' : g ∣ X ^ Q - X := by
    have h1 : g ∣ X ^ (Q - 1) - 1 := by
      have := Polynomial.map_dvd (residue S) hdvd
      simpa [hQ, g] using this
    have : (X ^ Q - X : (ResidueField S)[X]) = X * (X ^ (Q - 1) - 1) := by
      conv_lhs => rw [show Q = (Q - 1) + 1 by omega]
      ring
    rw [this]; exact dvd_mul_of_dvd_right h1 _
  have hne : (X ^ Q - X : (ResidueField S)[X]) ≠ 0 :=
    Polynomial.X_pow_sub_X_ne_zero hQ1
  have hsplit : Splits (X ^ Q - X : (ResidueField S)[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      Polynomial.natDegree_X_pow_sub_X (R := (ResidueField S)) hQ1]
    simp [Q]
  have hgs : Splits g := hsplit.of_dvd hne hdvd'
  obtain ⟨abar, habar⟩ := hgs.exists_eval_eq_zero
    (by rw [degree_eq_natDegree hgm.ne_zero]; exact_mod_cast hgdeg)
  have hchar : ringChar (ResidueField S) ∣ Q := by
    apply (ringChar.spec (ResidueField S) Q).mp
    exact FiniteField.cast_card_eq_zero (ResidueField S)
  have hsep : (X ^ Q - X : (ResidueField S)[X]).Separable :=
    galois_poly_separable (ringChar (ResidueField S)) Q hchar
  have hgsep := hsep.of_dvd hdvd'
  have hder : eval abar (derivative g) ≠ 0 := by
    have := hgsep.aeval_derivative_ne_zero (S := ResidueField S) (x := abar)
      (by simpa [aeval_def] using habar)
    simpa [aeval_def] using this
  obtain ⟨a, rfl⟩ := residue_surjective abar
  have key : ∀ p : S[X], residue S (p.eval a) = (p.map (residue S)).eval (residue S a) := by
    intro p; rw [eval_map, eval₂_hom]
  obtain ⟨y, hy, -⟩ := HenselianLocalRing.is_henselian f hmon a
    (by rw [← residue_eq_zero_iff, key]; exact habar)
    (by
      rw [← residue_ne_zero_iff_isUnit, key, ← derivative_map]
      exact hder)
  exact ⟨y, hy⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonoidAlgebraExistsRightInvOfMapField
section
namespace GlobalTheory

open MonoidAlgebra

theorem groupAlgebra_coeff_mul_fintype {R G : Type} [CommRing R] [Group G] [Fintype G]
    (x y : MonoidAlgebra R G) (a : G) :
    (x * y).coeff a = ∑ c : G, x.coeff (a * c⁻¹) * y.coeff c := by
  classical
  have hs : ∀ (f : G →₀ R) (g : G → R → R), (∀ i, g i 0 = 0) → f.sum g = ∑ i, g i (f i) :=
    fun f g h => Finsupp.sum_fintype f g h
  rw [MonoidAlgebra.coeff_mul, hs _ _ (fun i => by simp)]
  rw [Finset.sum_congr rfl fun b _ => hs _ _ (fun i => by simp)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ∀ m : G, (m * c = a) ↔ (m = a * c⁻¹) := fun m => eq_mul_inv_iff_mul_eq.symm
  simp_rw [this]
  simp

theorem groupAlgebra_exists_right_inv_of_map {E L G : Type} [Field E] [Field L] [Group G]
    [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G) :
    (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) →
      ∃ v : MonoidAlgebra E G, x * v = 1 := by
  classical
  rintro ⟨vL, hvL⟩
  let M : Matrix G G E := fun a c => x.coeff (a * c⁻¹)

  have hsurj : Function.Surjective (M.map j).mulVec := by
    intro w
    let y : MonoidAlgebra L G := ofCoeff (Finsupp.equivFunOnFinite.symm w)
    refine ⟨fun c => (vL * y).coeff c, ?_⟩
    funext a
    have h1 : (MonoidAlgebra.mapRingHom G j x * (vL * y)).coeff a = w a := by
      rw [← mul_assoc, hvL, one_mul]
      rfl
    rw [groupAlgebra_coeff_mul_fintype] at h1
    simp only [MonoidAlgebra.coeff_mapRingHom] at h1
    exact h1
  have hU : IsUnit (M.map j) := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hdetL : IsUnit (j M.det) := by
    rw [RingHom.map_det]
    exact (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdet : M.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdetL
    exact not_isUnit_zero hdetL
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM
    (fun a => (1 : MonoidAlgebra E G).coeff a)
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm u), ?_⟩
  apply MonoidAlgebra.ext
  ext a
  rw [groupAlgebra_coeff_mul_fintype]
  have := congrFun hu a
  simpa [Matrix.mulVec, dotProduct, M] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEvalLeSumNormCoeff
section
namespace GlobalTheory.EvalNormCoefficientBound

theorem norm_eval_le_sum_norm_coeff {σ : Type} (P : MvPolynomial σ ℂ) (v : σ → ℂ)
    (hv : ∀ (s : σ), ‖v s‖ ≤ (1 : ℝ)) :
    ‖(MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P‖ ≤
      ∑ d ∈ MvPolynomial.support P, ‖AddMonoidAlgebra.coeff P d‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => ?_))
  rw [norm_mul]
  have h1 : ‖∏ s ∈ d.support, v s ^ d s‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun s _ => norm_nonneg _) (fun s _ => ?_)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hv s)
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end GlobalTheory.EvalNormCoefficientBound
end

