module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SymmetricKMapEqZeroOfVminusSlices
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

def sliceIns (α' : Fin j → Fin n × Fin n) (m : Arr V n 1) : Arr V n (j + 1) :=
  WithLp.toLp 2 (fun α : Fin (j + 1) → Fin n × Fin n =>
    if Fin.tail α = α' then m (fun _ => α 0) else 0)

theorem slice_sliceIns (α' β' : Fin j → Fin n × Fin n) (m : Arr V n 1) :
    sliceLin V n β' (sliceIns α' m) = if β' = α' then m else 0 := by
  apply indexArray_ext
  intro β
  rw [firstPositionSlice_apply]
  have hβ : (fun _ : Fin 1 => β 0) = β := by
    funext i
    rw [Fin.fin_one_eq_zero i]
  simp only [sliceIns, PiLp.toLp_apply, Fin.tail_cons, Fin.cons_zero]
  split_ifs with h
  · rw [hβ]
  · rfl

theorem sliceIns_mem {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {α' : Fin j → Fin n × Fin n} (hα : ∀ i, ε (α' i).1 ≠ ε (α' i).2) {m : Arr V n 1}
    (hm : m ∈ arrV0 ε E u 1) : sliceIns α' m ∈ arrV0 ε E u (j + 1) := by
  rw [mem_admissibleArrays]
  intro α
  by_cases ht : Fin.tail α = α'
  · have hv : (sliceIns α' m) α = m (fun _ => α 0) := by simp [sliceIns, ht]
    rw [hv]
    by_cases h0 : ε (α 0).1 ≠ ε (α 0).2
    · have hall : ∀ i, ε (α i).1 ≠ ε (α i).2 := by
        intro i
        cases i using Fin.cases with
        | zero => exact h0
        | succ k =>
          have hk := hα k
          rw [← ht] at hk
          simpa [Fin.tail] using hk
      rw [if_pos hall]
      exact admissibleArrays_apply_mem hm _
    · rw [admissibleArrays_apply_eq_zero hm _ (fun h => h0 (h 0))]
      split_ifs <;> exact Submodule.zero_mem _
  · have hv : (sliceIns α' m) α = 0 := by simp [sliceIns, ht]
    rw [hv]
    split_ifs <;> exact Submodule.zero_mem _

theorem slice_mem_highest_jets {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n (j + 1)} (hF : F ∈ arrV0 ε E u (j + 1)) (α' : Fin j → Fin n × Fin n) :
    sliceLin V n α' F ∈ arrV0 ε E u 1 := by
  rw [mem_admissibleArrays]
  intro β
  rw [firstPositionSlice_apply]
  split_ifs with h
  · exact admissibleArrays_apply_mem hF _
  · rw [admissibleArrays_apply_eq_zero hF _ (fun h' => h (fun i => by rw [Fin.fin_one_eq_zero i]; simpa using h' 0))]
    exact Submodule.zero_mem _

theorem slice_eq_zero_of_compact {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n (j + 1)} (hF : F ∈ arrV0 ε E u (j + 1)) (α' : Fin j → Fin n × Fin n)
    (hα : ¬ ∀ i, ε (α' i).1 ≠ ε (α' i).2) : sliceLin V n α' F = 0 := by
  apply indexArray_ext
  intro β
  rw [firstPositionSlice_apply, admissibleArrays_apply_eq_zero hF _ (fun h => hα (fun i => by simpa using h i.succ))]
  rfl

theorem permute_mem_highest_jets {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n j} (hF : F ∈ arrV0 ε E u j) (s : Equiv.Perm (Fin j)) :
    permArr V n s F ∈ arrV0 ε E u j := by
  rw [mem_admissibleArrays]
  intro α
  rw [permutePositions_apply]
  split_ifs with h
  · exact admissibleArrays_apply_mem hF _
  · rw [admissibleArrays_apply_eq_zero hF _ (fun h' => h (fun i => by simpa using h' (s.symm i)))]
    exact Submodule.zero_mem _

private theorem finiteDimensional_arrV0_of_finiteDimensional_kSpan (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V) (h : FiniteDimensional ℂ (kSpan ε E u)) :
    FiniteDimensional ℂ (arrV0 ε E u j) := by
  let ψ : arrV0 ε E u j →ₗ[ℂ] ((Fin j → Fin n × Fin n) → kSpan ε E u) :=
    LinearMap.pi fun α => LinearMap.codRestrict (kSpan ε E u)
      ((LinearMap.proj α ∘ₗ arrOf V n j) ∘ₗ (arrV0 ε E u j).subtype)
      (fun F => by simpa [arrOf] using admissibleArrays_apply_mem F.2 α)
  refine Module.Finite.of_injective ψ ?_
  intro F G hFG
  apply Subtype.ext
  apply indexArray_ext
  intro α
  have h1 := congrArg Subtype.val (congrFun hFG α)
  simpa [ψ, arrOf] using h1

private theorem permArr_inv_permArr (s : Equiv.Perm (Fin j)) (F : Arr V n j) : permArr V n s⁻¹ (permArr V n s F) = F := by
  apply indexArray_ext
  intro α
  rw [permutePositions_apply, permutePositions_apply]
  simp

end

theorem jet_map_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V) (j : ℕ), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → ∀ T : Arr V n (j + 1) →ₗ[ℂ] V, (∀ F ∈ arrV0 ε E u (j + 1), T F ∈ kSpan ε E u) → (∀ c d, ε c = ε d → ∀ F ∈ arrV0 ε E u (j + 1), T (arrE E (j + 1) c d F) = E c d (T F)) → (∀ F ∈ arrV0 ε E u (j + 1), ∀ s : Equiv.Perm (Fin (j + 1)), T (permArr V n s F) = T F) → (∀ F ∈ arrV0 ε E u (j + 1), (∀ α', sliceLin V n α' F ∈ Vminus ε E (LamOf ε lam) u) → T F = 0) → ∀ F ∈ arrV0 ε E u (j + 1), T F = 0 := by
  intro V _ _ n ε E lam g u j hgl hun hhi hfd hgap hg T hT hE hS hM
  have hsplit := typesSplit V n ε E (LamOf ε lam) u hgl hun hhi hfd
  have hstab := admissibleArrays_invariant ε E u (j + 1)
  let K : Submodule ℂ (Arr V n (j + 1)) := arrV0 ε E u (j + 1) ⊓ LinearMap.ker T
  have memK : ∀ G, G ∈ arrV0 ε E u (j + 1) → T G = 0 → G ∈ K := fun G h1 h2 => ⟨h1, h2⟩

  have key : ∀ f ∈ arrV0 ε E u (j + 1), (∀ k ∈ K, ⟪k, f⟫_ℂ = 0) → f = 0 := by
    intro f hf horth

    have hsym : f ∈ symSub V n (j + 1) := by
      rw [mem_symmetricArrays]
      intro s
      have hGW : permArr V n s f - f ∈ arrV0 ε E u (j + 1) := sub_mem (permute_mem_highest_jets hf s) hf
      have hGT : T (permArr V n s f - f) = 0 := by rw [map_sub, hS f hf s, sub_self]
      have hGK : permArr V n s f - f ∈ K := memK _ hGW hGT
      have hG'K : permArr V n s⁻¹ (permArr V n s f - f) ∈ K :=
        memK _ (permute_mem_highest_jets hGW s⁻¹) (by rw [hS _ hGW s⁻¹, hGT])
      have h1 : ⟪permArr V n s f - f, permArr V n s f⟫_ℂ = 0 := by
        rw [← inner_permutePositions s⁻¹, permArr_inv_permArr]
        exact horth _ hG'K
      have h2 : ⟪permArr V n s f - f, f⟫_ℂ = 0 := horth _ hGK
      have h3 : ⟪permArr V n s f - f, permArr V n s f - f⟫_ℂ = 0 := by
        rw [inner_sub_right, h1, h2, sub_self]
      exact sub_eq_zero.mp (inner_self_eq_zero.mp h3)

    have hplus : ∀ α' : Fin j → Fin n × Fin n, sliceLin V n α' f ∈ Vplus ε E (LamOf ε lam) u := by
      intro α'
      by_cases hα : ∀ i, ε (α' i).1 ≠ ε (α' i).2
      · have hmem : sliceLin V n α' f ∈ Vplus ε E (LamOf ε lam) u ⊔ Vminus ε E (LamOf ε lam) u := by
          rw [hsplit.2]
          exact slice_mem_highest_jets hf α'
        obtain ⟨p, hp, m, hm, hpm⟩ := Submodule.mem_sup.mp hmem
        have hm0 : m ∈ arrV0 ε E u 1 := by
          rw [← hsplit.2]
          exact Submodule.mem_sup_right hm
        have hGW : sliceIns α' m ∈ arrV0 ε E u (j + 1) := sliceIns_mem hα hm0
        have hGT : T (sliceIns α' m) = 0 := by
          apply hM _ hGW
          intro β'
          rw [slice_sliceIns]
          split_ifs
          · exact hm
          · exact Submodule.zero_mem _
        have hin : ⟪sliceIns α' m, f⟫_ℂ = 0 := horth _ (memK _ hGW hGT)
        have hsum : ∑ β' : Fin j → Fin n × Fin n,
            ⟪sliceLin V n β' (sliceIns α' m), sliceLin V n β' f⟫_ℂ = ⟪m, sliceLin V n α' f⟫_ℂ := by
          rw [Finset.sum_eq_single α']
          · rw [slice_sliceIns, if_pos rfl]
          · intro b _ hb
            rw [slice_sliceIns, if_neg hb, inner_zero_left]
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [inner_eq_sum_firstPositionSlice, hsum, ← hpm, inner_add_right] at hin
        have hmp : ⟪m, p⟫_ℂ = 0 := by
          rw [← inner_conj_symm, hsplit.1 p hp m hm, map_zero]
        rw [hmp, zero_add] at hin
        have hm' : m = 0 := inner_self_eq_zero.mp hin
        rw [← hpm, hm', add_zero]
        exact hp
      · rw [slice_eq_zero_of_compact hf α' hα]
        exact Submodule.zero_mem _
    have hN : f ∈ Formalism.REAL.Nset ε E (LamOf ε lam) u j := by
      unfold Formalism.REAL.Nset
      exact ⟨⟨hf, hsym⟩, (Submodule.mem_iInf _).mpr fun α' => Submodule.mem_comap.mpr (hplus α')⟩

    have hCasW : CasK ε (arrE E (j + 1)) f ∈ arrV0 ε E u (j + 1) := by
      rw [compactCasimir_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      split_ifs with hab
      · exact hstab a b hab _ (hstab b a hab.symm _ hf)
      · exact Submodule.zero_mem _
    have hCasT : T (CasK ε (arrE E (j + 1)) f) = CasK ε E (T f) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [compactCasimir_apply, compactCasimir_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with hab
      · rw [hE a b hab _ (hstab b a hab.symm _ hf), hE b a hab.symm _ hf]
      · exact map_zero T
    have hKf : CasK ε E (T f) = ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • T f :=
      kCasSpan V n ε E (LamOf ε lam) u (glRel_kRel ε E hgl) hhi (T f) (hT f hf)
    have hkK : CasK ε (arrE E (j + 1)) f - ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • f ∈ K :=
      memK _ (sub_mem hCasW (Submodule.smul_mem _ _ hf))
        (by rw [map_sub, map_smul, hCasT, hKf, sub_self])
    have hfk : ⟪f, CasK ε (arrE E (j + 1)) f - ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • f⟫_ℂ = 0 := by
      rw [← inner_conj_symm, horth _ hkK, map_zero]
    have hre : (⟪f, CasK ε (arrE E (j + 1)) f⟫_ℂ).re = ckv ε (LamOf ε lam) * ‖f‖ ^ 2 := by
      rw [inner_sub_right, sub_eq_zero] at hfk
      rw [hfk, inner_smul_right, Complex.re_ofReal_mul, re_inner_self_indexArray]

    have hpos := nPos V n ε E lam g u j hgl hun hhi hfd hgap f hN
    rw [hre] at hpos
    have hcoef : 0 < 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ)) := by
      have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < g - 2 * (n : ℝ) := by linarith
      positivity
    have h4 : 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ)) * ‖f‖ ^ 2 ≤ 0 := by nlinarith
    have h5 : ‖f‖ ^ 2 = 0 := le_antisymm (by nlinarith) (by positivity)
    simpa using h5

  haveI : FiniteDimensional ℂ (arrV0 ε E u (j + 1)) := finiteDimensional_arrV0_of_finiteDimensional_kSpan ε E u hfd
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  intro F hF
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K) F
  have hzW : z ∈ arrV0 ε E u (j + 1) := by
    have hz' : z = F - y := by rw [hyz]; abel
    rw [hz']
    exact sub_mem hF hy.1
  have hz0 : z = 0 := key z hzW (fun k hk => (Submodule.mem_orthogonal K z).mp hz k hk)
  rw [hyz, hz0, add_zero]
  exact hy.2

end GlobalTheory.Jet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TailMassLeOfMajorantLengthMomentBound
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Cheb

theorem isClosed_GG (k r : ℕ) : IsClosed (GG k r) := by
  unfold GG UH
  exact isClosed_eq (by fun_prop) continuous_const

theorem measurableSet_len_gt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (T : ℝ) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} := by
  obtain ⟨u, hu, h⟩ := continuousOn_iff'.1 ((LenCont.lA_Sg_continuousOn k r z).1 a) (Set.Ioi T) isOpen_Ioi
  have h1 : MeasurableSet (α := Mt k r) u := IsOpen.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

theorem cheb_one {X : Type*} [MeasurableSpace X] (ν : Measure X) (l : X → ℝ) (f : X → ℝ≥0∞) (E : Set X)
    (hE : MeasurableSet E) (T : ℝ) (hT : 0 < T) (hl : ∀ x ∈ E, T < l x) (n : ℕ) :
    ∫⁻ x in E, f x ∂ν ≤ ENNReal.ofReal ((T ^ n)⁻¹) * ∫⁻ x, ENNReal.ofReal (l x ^ n) * f x ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (setLIntegral_mono' hE fun x hx => ?_) (setLIntegral_le_lintegral E _)
  have hTn : 0 < T ^ n := pow_pos hT n
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hTn.le)]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hTn]
  exact pow_le_pow_left₀ hT.le (hl x hx).le n

theorem tail_mass_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ), 1 ≤ H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → ∀ i : ℕ, ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z (Matrix.of x))}, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal ((r + 1) * 4 ^ q * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
  intro k r Wp _ _ _ z νS Φ q H₁ hH _ _ hM i
  rcases i with _ | j
  · refine (setLIntegral_le_lintegral _ _).trans ?_
    refine le_mul_of_one_le_left' ?_
    rw [ENNReal.one_le_ofReal]
    have h1 : (1 : ℝ) ≤ 4 ^ q := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    simp only [pow_zero, one_pow, inv_one, mul_one]
    nlinarith
  · set T : ℝ := 2 ^ (j + 1) * H₁ / 2 with hTdef
    have hT' : T = 2 ^ j * H₁ := by rw [hTdef]; ring
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hT1 : 1 ≤ T := by rw [hT']; nlinarith
    have hsub : {x : Mt k r | Matrix.of x ∈ GG k r ∧ (j + 1 = 0 ∨ T < Sg k r z (Matrix.of x))} ⊆
        ⋃ a : Fin (r + 1), {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} := by
      rintro x ⟨hx, h | h⟩
      · omega
      · unfold Sg at h
        rw [Finset.lt_fold_max] at h
        rcases h with h | ⟨a, -, h⟩
        · linarith
        · exact Set.mem_iUnion.2 ⟨a, hx, h⟩
    refine (lintegral_mono_set hsub).trans ((lintegral_iUnion_le _ _).trans ?_)
    rw [tsum_fintype]
    have hone : ∀ a : Fin (r + 1),
        ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a},
          (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤
          ENNReal.ofReal (4 ^ q * ((2 ^ (j + 1) : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
      intro a
      refine (cheb_one νS (fun x => lA k r z (Matrix.of x) a) _ _ (measurableSet_len_gt k r z a T) T
        (by linarith) (fun x hx => hx.2) (2 * q)).trans ?_
      refine (mul_le_mul_right (hM a) _).trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have hH0 : H₁ ≠ 0 := by linarith
      have h4 : (4 : ℝ) ^ q = 2 ^ (2 * q) := by rw [pow_mul]; norm_num
      rw [hT', h4, pow_succ, mul_pow, mul_pow]
      field_simp
    refine (Finset.sum_le_sum fun a _ => hone a).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, mul_assoc ((r : ℝ) + 1),
      ENNReal.ofReal_mul (p := (r : ℝ) + 1) (by positivity)]
    congr 2
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl

end GlobalTheory.Amp.Cheb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoMulPiPowLeFourPow
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem two_mul_pi_pow_le_four_pow (k : ℕ) (hk : 3 ≤ k) : 2 * Real.pi ^ k ≤ (4 : ℝ) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h0 := Real.pi_pos.le
  have h1 : Real.pi ^ 3 ≤ (3.15 : ℝ) ^ 3 := pow_le_pow_left₀ h0 Real.pi_lt_d2.le 3
  have h2 : Real.pi ^ m ≤ (4 : ℝ) ^ m := pow_le_pow_left₀ h0 Real.pi_le_four m
  have h3 : 2 * Real.pi ^ 3 ≤ (4 : ℝ) ^ 3 := by norm_num at h1 ⊢; linarith
  rw [pow_add, pow_add, ← mul_assoc]
  exact mul_le_mul h3 h2 (by positivity) (by positivity)

theorem box_volume_arith : ∀ (r j n₁ n₂ n₃ : ℕ) (M : ℝ), 1 ≤ j → j ≤ r → 2 * n₁ ≤ r * (r - 1) → 2 * n₂ ≤ r * (r - 1) → n₃ ≤ r → 1 ≤ M → (Real.pi * M ^ 2) ^ n₁ * (Real.pi * (2 * r * M ^ 2) ^ 2) ^ n₂ * (2 * (2 * r * M ^ 2)) ^ n₃ * (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2)) ≤ (4 * r : ℝ) ^ (4 * r ^ 2) * M ^ (8 * r ^ 2) := by
  intro r j n₁ n₂ n₃ M hj hjr h1 h2 h3 hM
  have hr : 1 ≤ r := hj.trans hjr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpi := Real.pi_pos.le
  have hpi4 := Real.pi_le_four
  have hM0 : 0 ≤ M := by linarith
  have hA : (1 : ℝ) ≤ 4 * r := by linarith
  have hrr : r * (r - 1) + r = r ^ 2 := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
    simp only [Nat.add_sub_cancel_left]; ring
  have hjj : j ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hjr 2
  have hr2 : r ≤ r ^ 2 := by nlinarith
  have hj2 : 1 ≤ j ^ 2 := by nlinarith
  have e : (Real.pi * M ^ 2) ^ n₁ * (Real.pi * (2 * r * M ^ 2) ^ 2) ^ n₂ * (2 * (2 * r * M ^ 2)) ^ n₃ * (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2))
      = (Real.pi ^ n₁ * (Real.pi * (2 * r) ^ 2) ^ n₂ * (4 * r) ^ n₃ * (2 * Real.pi ^ (2 * j + j ^ 2))) *
        M ^ (2 * n₁ + 4 * n₂ + 2 * n₃ + 4 * j + 2 * j ^ 2) := by
    have a1 : Real.pi * (2 * r * M ^ 2) ^ 2 = (Real.pi * (2 * r) ^ 2) * M ^ 4 := by ring
    have a2 : 2 * (2 * r * M ^ 2) = (4 * (r : ℝ)) * M ^ 2 := by ring
    rw [a1, a2, mul_pow Real.pi, mul_pow _ (M ^ 4), mul_pow _ (M ^ 2), mul_pow Real.pi (M ^ 2)]
    generalize Real.pi * (2 * (r : ℝ)) ^ 2 = B
    generalize 4 * (r : ℝ) = C
    ring
  rw [e]
  have b1 : Real.pi ^ n₁ ≤ (4 * r : ℝ) ^ n₁ := pow_le_pow_left₀ hpi (by linarith) _
  have b2 : (Real.pi * (2 * r) ^ 2) ^ n₂ ≤ (4 * r : ℝ) ^ (2 * n₂) := by
    rw [pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (0 : ℝ) ≤ (2 * r) ^ 2 := by positivity
    nlinarith
  have b4 : 2 * Real.pi ^ (2 * j + j ^ 2) ≤ (4 * r : ℝ) ^ (2 * j + j ^ 2) :=
    (two_mul_pi_pow_le_four_pow _ (by omega)).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith) _)
  refine mul_le_mul ?_ (pow_le_pow_right₀ hM (by omega)) (by positivity) (by positivity)
  calc _ ≤ (4 * r : ℝ) ^ n₁ * (4 * r : ℝ) ^ (2 * n₂) * (4 * r) ^ n₃ * (4 * r : ℝ) ^ (2 * j + j ^ 2) := by
        gcongr
    _ = (4 * r : ℝ) ^ (n₁ + 2 * n₂ + n₃ + (2 * j + j ^ 2)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ hA (by omega)

end GlobalTheory.Amp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWN
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem IsClosedSub.isMatGroup_of_unitary {S : Set (Mat k r)} (hS : IsClosedSub k r S) : PI.IsMatGroup S := by
  obtain ⟨hG, hcl, h1, hmul, hinv⟩ := hS
  refine ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, ?_⟩⟩

  have e : aᴴ * Hpk k r * a = Hpk k r := hG ha
  have hH := Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r
  have hd := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have hdet : IsUnit a.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at hd
    exact hH.ne_zero hd.symm
  exact Matrix.mul_nonsing_inv a hdet

theorem map_invM_eq {S : Set (Mat k r)} (hS : PI.IsMatGroup S) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) (hR : ∀ s ∈ S, μ.map (rmulM s) = μ) : μ.map invM = μ := by
  have hL : PI.IsHaarOnM S μ := hμ
  have hR' : PI.IsRightInvM S μ := hR
  ext B hB
  rw [Measure.map_apply measurable_invM hB]

  have h := GlobalTheory.HaarInversion.lintegral_inv_eq _ S μ hS hL hR' (B.indicator 1)
    (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB] at h
  rw [← h, ← lintegral_indicator_one (measurable_invM hB)]
  rfl

theorem rightInv_of_multiple {S : Set (Mat k r)} (hS : PI.IsMatGroup S) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) (hν : PI.IsHaarOnM S ν) (hR : PI.IsRightInvM S ν) :
    ∀ s ∈ S, μ.map (rmulM s) = μ := by
  intro s hs
  have hL : PI.IsHaarOnM S μ := hμ

  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ S ν hS hν).1 μ hL
  have hνs : ν.map (rmulM s) = ν := hR s hs
  rw [hc, Measure.map_smul, hνs]
  exact (continuous_rmulM s).measurable.aemeasurable

private theorem exists_isHaarOnM_of_isMatGroup {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : PI.IsMatGroup G) :
    ∃ μ : Measure (PI.MtM m), PI.IsHaarOnM G μ := by
  have he := GlobalTheory.MatHaar.inc_memb (G := G) (hG := hG)
  refine ⟨(GlobalTheory.MatHaar.haar0 hG).map GlobalTheory.MatHaar.inc, he.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    rw [Measure.map_eq_zero_iff he.measurable.aemeasurable] at h0
    exact (NeZero.ne (GlobalTheory.MatHaar.haar0 hG)) h0
  · rw [he.map_apply]
    have : (GlobalTheory.MatHaar.inc (G := G) (hG := hG)) ⁻¹' {x | Matrix.of x ∉ G} = ∅ := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact GlobalTheory.MatHaar.inc_mem g
    rw [this, measure_empty]
  · intro a ha
    let g0 : GlobalTheory.MatHaar.Grp G hG := ⟨a, ha⟩
    have hcomp : PI.lmulQ a ∘ GlobalTheory.MatHaar.inc (G := G) (hG := hG) =
        GlobalTheory.MatHaar.inc ∘ (fun g => g0 * g) := by
      funext g
      exact (GlobalTheory.MatHaar.inc_mul g0 g).symm
    rw [Measure.map_map (GlobalTheory.MatHaar.lmulQ_cont a).measurable he.measurable, hcomp,
      ← Measure.map_map he.measurable (measurable_const_mul g0), map_mul_left_eq_self]

theorem unimodular_S_N_UW : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ μ : Measure (Mt k r), (IsHaarOn (Sset k r z) μ → IsUnimod (Sset k r z) μ) ∧ (IsHaarOn (Nset k r) μ → IsUnimod (Nset k r) μ ∧ ∀ h ∈ UWset k r z, μ.map (conjM h) = μ) ∧ (IsHaarOn (UWset k r z) μ → IsUnimod (UWset k r z) μ ∧ μ Set.univ < ⊤) := by
  intro k r z hz hT μ
  obtain ⟨-, hNc, hWc, -, -⟩ := closedSub_groups k r z hz hT
  have hN := hNc.isMatGroup_of_unitary
  have hW := hWc.isMatGroup_of_unitary
  obtain ⟨μN0, hμN0⟩ := exists_isHaarOnM_of_isMatGroup hN
  obtain ⟨μW0, hμW0⟩ := exists_isHaarOnM_of_isMatGroup hW
  refine ⟨fun hμ => ?_, fun hμ => ?_, fun hμ => ?_⟩
  ·
    obtain ⟨hSg, -, hSH, hSR⟩ := GlobalTheory.muSof_isHaar k r z μW0 μN0 hz hT hμW0 hμN0
    have hR := rightInv_of_multiple hSg hμ hSH hSR
    exact ⟨hR, map_invM_eq hSg hμ hR⟩
  · obtain ⟨-, -, hNR, -, hconj⟩ :=
      GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW0 μ hz hT hμW0 hμ
    have hR : ∀ s ∈ Nset k r, μ.map (rmulM s) = μ := hNR
    exact ⟨⟨hR, map_invM_eq hN hμ hR⟩, fun h hh => hconj h hh⟩
  · obtain ⟨hWR, hfin, -, -, -⟩ :=
      GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μ μN0 hz hT hμ hμN0
    have hR : ∀ s ∈ UWset k r z, μ.map (rmulM s) = μ := hWR
    exact ⟨⟨hR, map_invM_eq hW hμ hR⟩, measure_lt_top μ _⟩

end GlobalTheory.SgInf
end

