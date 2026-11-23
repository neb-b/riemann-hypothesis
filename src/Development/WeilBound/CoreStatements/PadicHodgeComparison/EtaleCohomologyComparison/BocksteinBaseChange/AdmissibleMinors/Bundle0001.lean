module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.ConnAbs
section
noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Inj

theorem cup_fil {K B : Type*} [Field K] [CommRing B] (P : Subring B) (t : B) (ht : t ∈ P) (o : K →+* B)
    (ho : ∀ k, o k ∈ P) {H1 H2 H3 : Type*} [AddCommGroup H1] [Module K H1] [AddCommGroup H2] [Module K H2]
    [AddCommGroup H3] [Module K H3] (F1 : ℕ → Set H1) (F2 : ℕ → Set H2) (F3 : ℕ → Set H3)
    (cup : H1 →ₗ[K] H2 →ₗ[K] H3) (hcup : ∀ r s, ∀ x ∈ F1 r, ∀ y ∈ F2 s, cup x y ∈ F3 (r + s))
    (d : ℕ) (hd : ∀ e, d < e → ∀ x ∈ F3 e, x = 0)
    {m m' : ℕ} (b : Module.Basis (Fin m) K H1) (w : Fin m → ℕ)
    (hb : ∀ s, b s ∈ F1 (w s) ∧ ∀ x ∈ F1 (w s + 1), b.coord s x = 0)
    (b' : Module.Basis (Fin m') K H2) (w' : Fin m' → ℕ)
    (hb' : ∀ s, b' s ∈ F2 (w' s) ∧ ∀ x ∈ F2 (w' s + 1), b'.coord s x = 0)
    (C1 : Module.Dual K H1 → B) (hC1 : ∀ r φ, (∀ x ∈ F1 (r + 1), φ x = 0) → t ^ r * C1 φ ∈ P)
    (C2 : Module.Dual K H2 → B) (hC2 : ∀ r φ, (∀ x ∈ F2 (r + 1), φ x = 0) → t ^ r * C2 φ ∈ P)
    (φ : Module.Dual K H3) :
    t ^ d * ∑ s, ∑ s', C1 (b.coord s) * C2 (b'.coord s') * o (φ (cup (b s) (b' s'))) ∈ P := by
  rw [Finset.mul_sum]
  refine P.sum_mem fun s _ => ?_
  rw [Finset.mul_sum]
  refine P.sum_mem fun s' _ => ?_
  by_cases h : w s + w' s' ≤ d
  · have h1 := hC1 (w s) (b.coord s) (hb s).2
    have h2 := hC2 (w' s') (b'.coord s') (hb' s').2
    have e : t ^ d * (C1 (b.coord s) * C2 (b'.coord s') * o (φ (cup (b s) (b' s')))) =
        t ^ (d - (w s + w' s')) * (t ^ w s * C1 (b.coord s)) * (t ^ w' s' * C2 (b'.coord s')) *
          o (φ (cup (b s) (b' s'))) := by
      have : d = (d - (w s + w' s')) + w s + w' s' := by omega
      conv_lhs => rw [this]
      ring
    rw [e]
    exact P.mul_mem (P.mul_mem (P.mul_mem (P.pow_mem ht _) h1) h2) (ho _)
  · have h0 : cup (b s) (b' s') = 0 :=
      hd _ (by omega) _ (hcup _ _ _ (hb s).1 _ (hb' s').1)
    rw [h0, map_zero, map_zero, mul_zero, mul_zero]
    exact P.zero_mem

theorem exists_int_mul {p : ℕ} [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]
    (v : ℚ_[p] ⊗[ℤ_[p]] T) : ∃ s : ℤ_[p], s ≠ 0 ∧ ∃ x : T, (s : ℚ_[p]) • v = (1 : ℚ_[p]) ⊗ₜ x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q y =>
    obtain ⟨⟨ζ, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[p]) q
    refine ⟨s, nonZeroDivisors.ne_zero s.2, ζ • y, ?_⟩
    simp only at hs
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    calc ((s : ℤ_[p]) : ℚ_[p]) • q = q * algebraMap ℤ_[p] ℚ_[p] s := by rw [smul_eq_mul, mul_comm]; rfl
      _ = algebraMap ℤ_[p] ℚ_[p] ζ := hs
      _ = ζ • (1 : ℚ_[p]) := by rw [Algebra.smul_def, mul_one]
  | add v v' hv hv' =>
    obtain ⟨s, hs, x, hx⟩ := hv
    obtain ⟨s', hs', x', hx'⟩ := hv'
    refine ⟨s * s', mul_ne_zero hs hs', s' • x + s • x', ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hx, ← hx', smul_add]
    simp only [PadicInt.coe_mul]
    rw [← algebraMap_smul ℚ_[p] s', ← algebraMap_smul ℚ_[p] s, smul_smul, smul_smul]
    congr 2 <;> simp [PadicInt.algebraMap_apply] <;> ring

end CrystallineSemistableComparison.Inj
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.ExistsWeightBasisFiltration
section
namespace CrystallineSemistableComparison.Inj

open Submodule

theorem exists_weight_basis_filtration {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (F : ℕ → Set H) (N : ℕ) (hN : ∀ j, N ≤ j → ∀ x ∈ F j, x = 0) :
    ∀ i, ∃ (s : Set H) (w : H → ℕ), LinearIndepOn K id s ∧
      (∀ v ∈ s, v ∈ F (w v) ∧ N - i ≤ w v) ∧
      ∀ j, N - i ≤ j → F j ⊆ span K {v | v ∈ s ∧ j ≤ w v} := by
  intro i
  induction i with
  | zero =>
    refine ⟨∅, fun _ => 0, linearIndepOn_empty K id, by simp, ?_⟩
    intro j hj x hx
    rw [hN j (by omega) x hx]
    exact zero_mem _
  | succ i ih =>
    obtain ⟨s, w, hli, hs, hspan⟩ := ih
    by_cases hi : N - (i + 1) = N - i
    · exact ⟨s, w, hli, fun v hv => by rw [hi]; exact hs v hv, fun j hj => hspan j (hi ▸ hj)⟩
    obtain ⟨b, hbt, hsb, htb, hlib⟩ :=
      exists_linearIndepOn_extension hli (Set.subset_union_left : s ⊆ s ∪ F (N - (i + 1)))
    classical
    refine ⟨b, fun v => if v ∈ s then w v else N - (i + 1), hlib, ?_, ?_⟩
    · intro v hv
      by_cases h : v ∈ s
      · simp only [h, if_true]
        exact ⟨(hs v h).1, by have := (hs v h).2; omega⟩
      · simp only [h, if_false]
        refine ⟨?_, le_rfl⟩
        rcases hbt hv with h' | h'
        · exact absurd h' h
        · exact h'
    · intro j hj
      rcases Nat.eq_or_lt_of_le hj with hjk | hlt
      · subst hjk
        intro x hx
        have hx' : x ∈ span K (id '' b) := htb ⟨x, Or.inr hx, rfl⟩
        rw [Set.image_id] at hx'
        refine span_mono ?_ hx'
        intro v hv
        refine ⟨hv, ?_⟩
        by_cases h : v ∈ s
        · simp only [h, if_true]
          have := (hs v h).2
          omega
        · simp [h]
      · have hj' : N - i ≤ j := by omega
        refine (hspan j hj').trans (span_mono ?_)
        rintro v ⟨hv, hw⟩
        exact ⟨hsb hv, by simp [hv, hw]⟩

theorem wt_basis {K H : Type*} [Field K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (F : ℕ → Set H) (hF : Antitone F) (h0 : F 0 = Set.univ) (N : ℕ) (hN : ∀ x ∈ F N, x = 0) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) K H) (w : Fin m → ℕ),
      ∀ s, b s ∈ F (w s) ∧ ∀ x ∈ F (w s + 1), b.coord s x = 0 := by
  obtain ⟨s, w, hli, hs, hspan⟩ := exists_weight_basis_filtration (K := K) F N (fun j hj x hx => hN x (hF hj hx)) N
  have hli' : LinearIndependent K ((↑) : s → H) := hli
  have htop : ⊤ ≤ span K (Set.range ((↑) : s → H)) := by
    rw [Subtype.range_coe]
    intro x _
    have := hspan 0 (by omega) (h0 ▸ Set.mem_univ x)
    exact span_mono (show {v | v ∈ s ∧ 0 ≤ w v} ⊆ s from fun v hv => hv.1) this
  let b0 := Module.Basis.mk hli' htop
  have hb0 : ∀ v, b0 v = (v : H) := fun v => Module.Basis.mk_apply hli' htop v
  have : Finite s := Module.Finite.finite_basis b0
  haveI : Fintype s := Fintype.ofFinite s
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, b0.reindex e, fun t => w (e.symm t), fun t => ⟨?_, ?_⟩⟩
  · rw [Module.Basis.reindex_apply, hb0]
    exact (hs _ (e.symm t).2).1
  · intro x hx
    rw [Module.Basis.coord_apply, Module.Basis.repr_reindex_apply]
    have hx' := hspan (w (e.symm t) + 1) (by omega) hx
    have himg : {v | v ∈ s ∧ w (e.symm t) + 1 ≤ w v} = b0 '' {u : s | w (e.symm t) + 1 ≤ w u} := by
      ext v
      constructor
      · rintro ⟨hv, hw⟩
        exact ⟨⟨v, hv⟩, hw, hb0 _⟩
      · rintro ⟨u, hu, rfl⟩
        rw [hb0]
        exact ⟨u.2, hu⟩
    rw [himg, SetLike.mem_coe, Module.Basis.mem_span_image] at hx'
    by_contra hne
    have := hx' (Finsupp.mem_support_iff.mpr hne)
    simp at this

end CrystallineSemistableComparison.Inj
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.RedAbs
section
namespace CrystallineSemistableComparison.Inj

theorem dual_span {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Module.Dual k V) (hf : ∀ v, (∀ i, f i v = 0) → v = 0) (g : Module.Dual k V) :
    ∃ c : ι → k, ∀ v, g v = ∑ i, c i * f i v := by
  have hker : LinearMap.ker (LinearMap.pi f) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hf v fun i => congrFun hv i
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.pi f) hker
  refine ⟨fun i => g (ρ (Pi.single i 1)), fun v => ?_⟩
  have h1 : v = ρ (LinearMap.pi f v) := by rw [← LinearMap.comp_apply, hρ, LinearMap.id_apply]
  have h2 : LinearMap.pi f v = ∑ i, f i v • Pi.single i (1 : k) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h1, h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, mul_comm]

theorem red_abs {k B V : Type*} [Field k] [CommRing B] [AddCommGroup V] [Module k V] (q : k →+* B) (S : AddSubgroup B)
    (hS : ∀ x s, s ∈ S → q x * s ∈ S) {ι : Type*} [Fintype ι] (f : ι → Module.Dual k V)
    (hf : ∀ v, (∀ i, f i v = 0) → v = 0) {n : ℕ} (b : Module.Basis (Fin n) k V) (z : Fin n → B)
    (hy : ∀ i, ∑ m, z m * q (f i (b m)) ∈ S) (m' : Fin n) : z m' ∈ S := by
  classical
  obtain ⟨c, hc⟩ := dual_span f hf (b.coord m')
  have key : z m' = ∑ i, q (c i) * ∑ m, z m * q (f i (b m)) := by
    calc z m' = ∑ m, z m * q (b.coord m' (b m)) := by
          simp [Module.Basis.coord_apply, Finsupp.single_apply]
      _ = ∑ m, z m * q (∑ i, c i * f i (b m)) := by simp_rw [← hc]
      _ = _ := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp_rw [map_sum, map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
  rw [key]
  exact sum_mem fun i _ => hS _ _ (hy i)

end CrystallineSemistableComparison.Inj
end

