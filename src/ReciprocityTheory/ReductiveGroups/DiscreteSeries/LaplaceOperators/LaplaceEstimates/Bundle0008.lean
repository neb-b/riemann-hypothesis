module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ClosedIrreducibleLowestTypeData
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0011

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinProj
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem finProj (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam' : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (hp : pOf ε = k + r) (hq : qOf ε = r + 1) (hgap : StepGap ε r h) (hlam : S7.IsHCParam lam')
    (hgl : GapAtLeast ε lam' h) (Wf : Submodule ℂ (Mat k r → ℂ)) (W' : Submodule ℂ (smD ε (rreg ε)))
    (hWf : ∀ F ∈ Wf, ContinuousOn F (UJset ε) ∧ ∃ C : ℝ, ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h))
    (hW' : ∀ v : smD ε (rreg ε), v ∈ W' ↔ ∃ F ∈ Wf, (v : L2 ε) = toL2 ε F)
    (hirr : IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam') W')
    (hcas : ∀ v ∈ W', casimir (smE ε (rreg ε)) v = (casVal lam' : ℂ) • v)
    (hK : ∀ k' ∈ Kset ε, ∀ v ∈ W', ∃ v'' ∈ W', (v'' : L2 ε) = rreg ε k' (v : L2 ε))
    (F : Mat k r → ℂ) (hF : F ∈ Wf) (hFW : ∃ v ∈ W', v ≠ 0 ∧ (v : L2 ε) = toL2 ε F) :
    ∃ (T' : S7.KType ε (lowK ε lam')) (μ' : Fin (2 * r + k + 1) → ℤ) (v₁ v₂ : T'.V), S7.IsMu lam' μ' ∧
      ∀ x ∈ UJset ε, F x = ∫ y, F (Formalism.MainNotions.S.umat y) *
        ⟪v₂, S7.PsiM T' μ' ((Formalism.MainNotions.S.umat y)⁻¹ * x) v₁⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  obtain ⟨v, hvW, hv0, hvF⟩ := hFW
  obtain ⟨hq0, hNd⟩ := gapNeed k r ε h hp hq hgap
  have hstd : StdGap ε lam' := by
    refine ⟨hlam.1, h, hgl, ?_⟩
    have h1 := hgap.1
    have h2 := le_max_right (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2)
      (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith
  have h8 : 8 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) < h := by
    have hmq : (min (pOf ε) (qOf ε) : ℝ) = (S7.q0 ε : ℝ) := by
      delta S7.q0
      simp only [Nat.cast_min]
    unfold hNeed at hNd
    rw [hmq, max_lt_iff, max_lt_iff] at hNd
    obtain ⟨-, hB, -⟩ := hNd
    have hs := Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))
    have hnq : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
    nlinarith
  obtain ⟨T', μ', hμ, C, hC, d, hd, hcoef, hstab, hS⟩ :=
    closed_irreducible_lowest_type_data ε lam' h hstd hlam hgl hq0 h8 W' hirr hcas hK
  obtain ⟨t, ht⟩ := hcoef v hvW
  rw [hvF] at ht
  have hf0 : toL2 ε F ≠ 0 := by
    intro h0; apply hv0; apply Subtype.ext; rw [hvF, h0]; rfl
  have hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
    by_contra hn; exact hf0 (toL2_eq_zero_of_not_memLp ε hn)
  have hfK : toL2 ε F ∈ closGen (smE ε (rreg ε)) W' := hvF ▸ mem_closure_generated_of_mem W' hvW
  have hrep := reproducing_formula_closed_invariant (hWf F hF).1 hF2 (closure_generated_isClosed W') hfK hstab hS
  have hff : ⟪toL2 ε F, toL2 ε F⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hf0
  have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  set κ : ℂ := (C : ℂ) * (d : ℂ) / ⟪toL2 ε F, toL2 ε F⟫_ℂ with hκ
  refine ⟨T', μ', κ • t, t, hμ, fun x hx => ?_⟩
  obtain ⟨x', rfl⟩ := exists_unitary_preimage ε hx
  have e : ∀ y : Formalism.REAL.UJ ε, F (Formalism.MainNotions.S.umat y) *
      ⟪t, S7.PsiM T' μ' ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat x') (κ • t)⟫_ℂ =
      (κ / C) * (F (Formalism.MainNotions.S.umat y) *
        ⟪toL2 ε F, rreg ε ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat x') (toL2 ε F)⟫_ℂ) := by
    intro y
    have hg : (Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat x' ∈ UJset ε := by
      rw [← unitary_matrix_inv_alt, ← unitary_matrix_mul]; exact unitary_matrix_mem_set ε _
    rw [ht _ hg, map_smul, inner_smul_right]
    field_simp
  rw [integral_congr_ae (ae_of_all _ e), integral_const_mul, hrep _ hx, hκ]
  field_simp

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotPA
section
noncomputable section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.QuotA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

section Map

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def tL (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] (Mat k r → ℂ) where
  toFun f := tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H))
  map_add' f f' := by
    funext g
    simp only [tMap, coefX, Pi.add_apply, Submodule.coe_add, map_add (f := _), inner_add_right, mul_add,
      Finset.sum_add_distrib]
  map_smul' a f := by
    funext g
    simp only [tMap, coefX, Pi.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

end Map

section Hull

variable {n : ℕ} {ε : Fin n → Bool} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem exists_kStable_finiteDimensional_submodule_of_mem_Xs (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {θ : ℝ}
    {x : Fin n → M} (hx : x ∈ Xs (LemK.eeV E) (genSub E V) θ) :
    ∃ S : Submodule ℂ (Fin n → M), S ≤ Xs (LemK.eeV E) (genSub E V) θ ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensV E) S ∧ x ∈ S := by
  classical
  have hxg := (mem_eigenTensorSpace_gen_iff.1 hx).1
  choose m hm using fun c => exists_layer_of_mem_genSub hE hVk (hxg c)
  set K := Finset.univ.sup m
  have hxK : ∀ c, x c ∈ layer ε E V K := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hfdL : FiniteDimensional ℂ (layer ε E V K) := finiteDimensional_layer hVfd K
  have hLk := layer_kStable hE hVk K
  have := pi_submodule_finiteDimensional (n := n) (layer ε E V K)
  refine ⟨Submodule.pi Set.univ (fun _ => layer ε E V K) ⊓ Xs (LemK.eeV E) (genSub E V) θ, inf_le_right,
    Submodule.finiteDimensional_of_le inf_le_left, ?_, ⟨mem_pi_submodule_iff.2 hxK, hx⟩⟩
  intro a b hab f hf
  refine ⟨mem_pi_submodule_iff.2 fun c => ?_, eigenTensorSpace_stable hE a b hf.2⟩
  rw [entry_bounds_of_partialSum]
  refine add_mem (hLk a b hab _ (mem_pi_submodule_iff.1 hf.1 c)) ?_
  split_ifs
  · exact mem_pi_submodule_iff.1 hf.1 b
  · exact zero_mem _

end Hull

section Line

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D}

theorem line_V (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hmono : StrictAnti lam) (hGL : GapLap ε lam h)
    (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (s : Fin n) {N : Type*} [AddCommGroup N] [Module ℂ N]
    (EN : Fin n → Fin n → Module.End ℂ N) :
    ∃ ys ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), ∀ ψ : (Fin n → D) →ₗ[ℂ] N,
      (∀ a b, ∀ y ∈ Submodule.pi Set.univ (fun _ => genSub E V), ψ (LemK.tensV E a b y) = EN a b (ψ y)) →
      ∀ w' ∈ (Xs (LemK.eeV E) (genSub E V) (thV lam s)).map ψ,
        IsKHWVec ε EN (lowK ε (lam + Pi.single s 1)) w' → ∃ c : ℂ, w' = c • ψ ys := by
  classical
  have hK2 := (k2V n ε lam h H σ D E V s hσ hD hV hc hVK hint hmono hGL hp hq).2
  have hKD : IsKUnitary ε E := isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hE : IsGlRep E := hD.glRep
  have hXG : ∀ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), y ∈ Submodule.pi Set.univ (fun _ => genSub E V) :=
    fun y hy => by simpa [Submodule.mem_pi] using (mem_eigenTensorSpace_gen_iff.1 hy).1

  have hlift : ∀ ψ : (Fin n → D) →ₗ[ℂ] N,
      (∀ a b, ∀ y ∈ Submodule.pi Set.univ (fun _ => genSub E V), ψ (LemK.tensV E a b y) = EN a b (ψ y)) →
      ∀ w' ∈ (Xs (LemK.eeV E) (genSub E V) (thV lam s)).map ψ,
        IsKHWVec ε EN (lowK ε (lam + Pi.single s 1)) w' →
        ∃ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), IsKHWVec ε (LemK.tensV E) (lowK ε (lam + Pi.single s 1)) y ∧
          ψ y = w' := by
    intro ψ hψ w' hw' hw'K
    obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.1 hw'
    obtain ⟨S, hSX, hfd, hSk, hy₀S⟩ := exists_kStable_finiteDimensional_submodule_of_mem_Xs hE hV.1 hV.2.1 hy₀
    obtain ⟨y, hyS, hyK, hyeq⟩ := partialSum_succ_alt hKD ψ hfd hSk (fun a b _ z hz => hψ a b z (hXG z (hSX hz)))
      hy₀S hw'K
    exact ⟨y, hSX hyS, hyK, hyeq⟩
  by_cases hex : ∃ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), y ≠ 0 ∧
      IsKHWVec ε (LemK.tensV E) (lowK ε (lam + Pi.single s 1)) y
  · obtain ⟨ys, hysX, hys0, hysK⟩ := hex
    refine ⟨ys, hysX, fun ψ hψ w' hw' hw'K => ?_⟩
    obtain ⟨y, hyX, hyK, rfl⟩ := hlift ψ hψ w' hw' hw'K
    obtain ⟨c₁, c₂, hne, hrel⟩ := hK2 y ys hyX hysX hyK hysK
    by_cases hc1 : c₁ = 0
    · exfalso
      rw [hc1, zero_smul, zero_add] at hrel
      exact hys0 ((smul_eq_zero.1 hrel).resolve_left (hne.resolve_left (not_not.2 hc1)))
    · refine ⟨-(c₁⁻¹ * c₂), ?_⟩
      have h2 : c₁ • y = -(c₂ • ys) := eq_neg_of_add_eq_zero_left hrel
      have hy : y = -(c₁⁻¹ * c₂) • ys := by
        calc y = c₁⁻¹ • (c₁ • y) := by rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
          _ = -(c₁⁻¹ * c₂) • ys := by rw [h2, smul_neg, smul_smul, neg_smul]
      rw [hy, map_smul]
  · refine ⟨0, zero_mem _, fun ψ hψ w' hw' hw'K => ⟨0, ?_⟩⟩
    obtain ⟨y, hyX, hyK, rfl⟩ := hlift ψ hψ w' hw' hw'K
    have hy0 : y = 0 := by
      by_contra hy0
      exact hex ⟨y, hyX, hy0, hyK⟩
    rw [hy0, map_zero, zero_smul]

end Line

end ReciprocityTheory.ChartRestriction.DS.Lap.QuotA
end
end

