module

public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharDataA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HloweqTransfer
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.HilbertConeOfStableMollifier
section
noncomputable section

open Finset

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem hilbert_cone_of_stable_mollifier : StepStable → StepMoll → StepWtSpan → StepCone := by
  intro hSt hMo hWt n ε lam T Ψ _hHC hPsi hKey η S hSH hSK
  have : FiniteDimensional ℂ S := hSK.1
  have hcl : IsClosed ((Hlam ε Ψ T.w : Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    unfold Hlam closGen
    exact Submodule.isClosed_topologicalClosure _
  obtain ⟨A, hAK, hAinj, hAsm, hAW⟩ :=
    hMo n ε (Hlam ε Ψ T.w) S hcl (hSt n ε lam T Ψ hPsi) inferInstance hSH hSK.2.1
  set S₂ : Submodule ℂ (L2 ε) := S.map A with hS₂
  have hfin : FiniteDimensional ℂ S₂ := Module.Finite.map S A
  have hK₂ : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S₂ := by
    rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨rreg ε g w, hSK.2.1 g hg w hw, hAK g hg w⟩
  have hne : S₂ ≠ ⊥ := by
    obtain ⟨v, hv, hv0, -⟩ := hSK.2.2.2.1
    intro h
    have hmem : A v ∈ S₂ := ⟨v, hv, rfl⟩
    rw [h] at hmem
    exact hv0 (hAinj v hv ((Submodule.mem_bot ℂ).1 hmem))
  obtain ⟨N, _i1, _i2, e, φ, h1, h2, -⟩ := hKey S₂ hfin (hAW.trans le_rfl) hK₂
  obtain ⟨x₀, -, hx₀⟩ := h1 S₂ le_rfl hK₂ hne
  have he : e ≠ 0 := by
    intro h
    apply hx₀
    rw [h, LinearMap.zero_apply]
  obtain ⟨ν, x, hxw, hex⟩ := hWt n ε S₂ hfin hAsm hK₂ N e he
  have hνc : InCone (lowK ε lam) ν := h2 ν x hxw hex
  have hx0 : (x : L2 ε) ≠ 0 := by
    intro h
    apply hex
    have : x = 0 := Subtype.ext h
    rw [this, map_zero]
  obtain ⟨y, hy, hyx⟩ := x.2
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    rw [← hyx, h, map_zero]
  have hyw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) ν y := by
    intro θ hθ
    have h1' : A (rreg ε (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) y -
        Complex.exp (((∑ a, ν a * θ a : ℝ) : ℂ) * Complex.I) • y) = 0 := by
      rw [map_sub, map_smul, hAK _ hθ, hyx, hxw θ hθ, sub_self]
    have h2' := hAinj _ (Submodule.sub_mem _ (hSK.2.1 _ hθ y hy) (Submodule.smul_mem _ _ hy)) h1'
    exact sub_eq_zero.1 h2'
  obtain ⟨c', hc', hd⟩ := hSK.2.2.2.2 ν y hy hy0 hyw
  obtain ⟨c, hc, hν⟩ := hνc
  refine ⟨fun a b => c a b + c' a b, ?_, ?_⟩
  · intro a b hab
    have hab' : c a b + c' a b ≠ 0 := hab
    by_cases h : c a b = 0
    · rw [h, zero_add] at hab'
      exact (hc' a b hab').1
    · exact hc a b h
  · have hη : η = ν + (η - ν) := by abel
    rw [hη, hd, hν]
    simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib]
    abel

end PositivityTheory.RgDs.Hilb
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.HilbertLowestWeightOfInputs
section
noncomputable section

open Finset

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem hloweq_transfer {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (A : L2 ε →ₗ[ℂ] L2 ε)
    (hAK : ∀ k ∈ Kset ε, ∀ x, A (rreg ε k x) = rreg ε k (A x)) {S : Submodule ℂ (L2 ε)}
    (hinj : ∀ w ∈ S, A w = 0 → w = 0) (hS : Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) Λ S) :
    Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) Λ (S.map A) :=
  _root_.UpperTheory.Reformulated.B.Re4.hloweq_transfer A hAK hinj hS

theorem hloweq_brIdx {n : ℕ} (c : Fin n → Fin n → ℕ) :
    brIdxSum (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) =
      ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) := by
  unfold brIdxSum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := brIdxSum_root a b
  unfold brIdxSum at this
  rw [← this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem hloweq_eq_of_cone {n : ℕ} {ε : Fin n → Bool} {ν Λ : Fin n → ℝ} (h1 : InCone Λ ν)
    (h2 : Formalism.MainNotions.S.CDom ε ν Λ) : ν = Λ := by
  have hle := brIdxSum_nonpos_of_cdom h2
  obtain ⟨c, hc, heq⟩ := h1
  have hterm : ∀ a b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) ≤ 0 := by
    intro a b
    by_cases h : c a b = 0
    · simp [h]
    · have hab := hc a b h
      have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast hab
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hs : brIdxSum (ν - Λ) = ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) := by
    rw [heq, add_sub_cancel_left, hloweq_brIdx]
  have hneg : brIdxSum (ν - Λ) = - brIdxSum (Λ - ν) := by
    rw [brIdxSum_sub, brIdxSum_sub]; ring
  have hz : ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) = 0 := by
    have : ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) ≤ 0 :=
      Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => hterm a b
    linarith
  have hc0 : ∀ a b, c a b = 0 := by
    intro a b
    by_contra hne
    have hlt : (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) < 0 := by
      have hab := hc a b hne
      have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast hab
      have hpos : (0 : ℝ) < c a b := by exact_mod_cast Nat.pos_of_ne_zero hne
      exact mul_neg_of_pos_of_neg hpos (by linarith)
    have hall := (Finset.sum_eq_zero_iff_of_nonpos
      (fun a _ => Finset.sum_nonpos fun b _ => hterm a b)).1 hz a (Finset.mem_univ _)
    have hall2 := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hterm a b)).1 hall b (Finset.mem_univ _)
    linarith
  rw [heq]
  simp [hc0]

theorem hilbert_lowest_weight_of_inputs : StepStable → StepMoll → StepWtSpan → StepDatum → StepLowEq := by
  intro hSt hMo hWt hDa n ε lam T Ψ _hHC hPsi hKey S hSH hSK
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hVK := hDa n ε lam T Ψ hPsi
  have hVH : V1 ε Ψ ≤ Hlam ε Ψ T.w := by
    rintro _ ⟨x, hx, rfl⟩
    have hg : x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) := by
      unfold genSub
      exact Submodule.mem_sInf.2 fun P hP => hP.1 hx
    exact ICD.mem_closGen hg
  by_contra hne
  have hS0 : S ≠ ⊥ := by
    obtain ⟨v, hv, hv0, -⟩ := hSK.2.2.2.1
    intro h
    rw [h] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  have hdisj : S ⊓ V1 ε Ψ = ⊥ := by
    have hK : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) (S ⊓ V1 ε Ψ) := fun g hg v hv =>
      Submodule.mem_inf.2 ⟨hSK.2.1 g hg v (Submodule.mem_inf.1 hv).1, hVK.2.1 g hg v (Submodule.mem_inf.1 hv).2⟩
    rcases hSK.2.2.1 _ inf_le_left hK with h | h
    · exact h
    · exfalso
      have hle : S ≤ V1 ε Ψ := h.symm.le.trans inf_le_right
      rcases hVK.2.2.1 S hle hSK.2.1 with h' | h'
      · exact hS0 h'
      · exact hne h'
  haveI : FiniteDimensional ℂ S := hSK.1
  haveI : FiniteDimensional ℂ (V1 ε Ψ) := hVK.1
  have hW0fin : FiniteDimensional ℂ (S ⊔ V1 ε Ψ : Submodule ℂ (L2 ε)) := inferInstance
  have hW0K : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) (S ⊔ V1 ε Ψ) := by
    intro g hg v hv
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hSK.2.1 g hg s hs) (hVK.2.1 g hg t ht)
  have hcl : IsClosed ((Hlam ε Ψ T.w : Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    unfold Hlam closGen
    exact Submodule.isClosed_topologicalClosure _
  obtain ⟨A, hAK, hAinj, hAsm, hAW⟩ :=
    hMo n ε (Hlam ε Ψ T.w) (S ⊔ V1 ε Ψ) hcl (hSt n ε lam T Ψ hPsi) hW0fin (sup_le hSH hVH) hW0K
  have hS2 := hloweq_transfer A hAK (fun w hw => hAinj w (Submodule.mem_sup_left hw)) hSK
  have hV2 := hloweq_transfer A hAK (fun w hw => hAinj w (Submodule.mem_sup_right hw)) hVK
  have hW2fin : FiniteDimensional ℂ ((S ⊔ V1 ε Ψ).map A) := Module.Finite.map _ A
  have hW2K : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) ((S ⊔ V1 ε Ψ).map A) := by
    rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨rreg ε g w, hW0K g hg w hw, hAK g hg w⟩
  obtain ⟨N, _i1, _i2, e, φ, h1, h2, h3⟩ := hKey _ hW2fin hAW hW2K
  have hdisj2 : ∀ z, z ∈ S.map A → z ∈ (V1 ε Ψ).map A → z = 0 := by
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
    have h0 : s - t = 0 := hAinj (s - t)
      (Submodule.sub_mem _ (Submodule.mem_sup_left hs) (Submodule.mem_sup_right ht))
      (by rw [map_sub, hts, sub_self])
    have hst : s = t := sub_eq_zero.1 h0
    have hsI : s ∈ S ⊓ V1 ε Ψ := Submodule.mem_inf.2 ⟨hs, by rw [hst]; exact ht⟩
    rw [hdisj] at hsI
    rw [(Submodule.mem_bot ℂ).1 hsI, map_zero]
  obtain ⟨w, hwS, hw0, hwH⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hS2
    ((Submodule.map_mono le_sup_left).trans hAsm)
  obtain ⟨w', hw'V, hw'0, hw'H⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hV2
    ((Submodule.map_mono le_sup_right).trans hAsm)
  have hwW : ((w : L2 ε)) ∈ (S ⊔ V1 ε Ψ).map A := Submodule.map_mono le_sup_left hwS
  have hw'W : ((w' : L2 ε)) ∈ (S ⊔ V1 ε Ψ).map A := Submodule.map_mono le_sup_right hw'V
  obtain ⟨c, hc⟩ := h3 ⟨w, hwW⟩ ((isWtOn_iff hσ hD w _).2 hwH.1)
  obtain ⟨c', hc'⟩ := h3 ⟨w', hw'W⟩ ((isWtOn_iff hσ hD w' _).2 hw'H.1)
  have hy : ∃ y : smD ε (rreg ε), ∃ hyW : (y : L2 ε) ∈ (S ⊔ V1 ε Ψ).map A,
      y ≠ 0 ∧ IsKHWVec ε (smE ε (rreg ε)) (lowK ε lam) y ∧ e ⟨y, hyW⟩ = 0 := by
    by_cases hcc : c = 0 ∧ c' = 0
    · refine ⟨w, hwW, hw0, hwH, ?_⟩
      rw [hc, hcc.1, zero_smul]
    · have hmem : ((c' • w - c • w' : smD ε (rreg ε)) : L2 ε) ∈ (S ⊔ V1 ε Ψ).map A := by
        rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hwW) (Submodule.smul_mem _ _ hw'W)
      refine ⟨c' • w - c • w', hmem, ?_, ?_, ?_⟩
      · intro h0
        have h0' : c' • (w : L2 ε) = c • (w' : L2 ε) := by
          have := congrArg (fun z : smD ε (rreg ε) => (z : L2 ε)) h0
          simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_zero] at this
          exact sub_eq_zero.1 this
        have hmV : c' • (w : L2 ε) ∈ (V1 ε Ψ).map A := by
          rw [h0']
          exact Submodule.smul_mem _ c hw'V
        have hz := hdisj2 _ (Submodule.smul_mem _ c' hwS) hmV
        have hz' : c • (w' : L2 ε) = 0 := h0' ▸ hz
        apply hcc
        constructor
        · rcases smul_eq_zero.1 hz' with h | h
          · exact h
          · exact absurd (Submodule.coe_eq_zero.1 h) hw'0
        · rcases smul_eq_zero.1 hz with h | h
          · exact h
          · exact absurd (Submodule.coe_eq_zero.1 h) hw0
      · refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
        · rw [map_sub, map_smul, map_smul, hwH.1 a, hw'H.1 a]
          module
        · rw [map_sub, map_smul, map_smul, hwH.2 a b hab hε, hw'H.2 a b hab hε, smul_zero, smul_zero,
            sub_zero]
      · have hyeq : (⟨_, hmem⟩ : ↥((S ⊔ V1 ε Ψ).map A)) =
            c' • (⟨w, hwW⟩ : ↥((S ⊔ V1 ε Ψ).map A)) - c • ⟨w', hw'W⟩ := by
          apply Subtype.ext
          simp
        rw [hyeq, map_sub, map_smul, map_smul, hc, hc', smul_smul, smul_smul, mul_comm c' c, sub_self]
  obtain ⟨y, hyW, hy0, hyH, hey⟩ := hy
  have hW2Dfin : FiniteDimensional ℂ (((S ⊔ V1 ε Ψ).map A).comap (smD ε (rreg ε)).subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hAsm).symm
  have hW2DK : IsKStableSub ε (smE ε (rreg ε)) (((S ⊔ V1 ε Ψ).map A).comap (smD ε (rreg ε)).subtype) := by
    refine isKStableSub_of_kStable hσ hD _ hW2Dfin ?_
    intro k hk v hv
    have hkv : rreg ε k (v : L2 ε) ∈ (S ⊔ V1 ε Ψ).map A := hW2K k hk _ (Submodule.mem_comap.1 hv)
    exact ⟨⟨rreg ε k v, hAsm hkv⟩, Submodule.mem_comap.2 hkv, rfl⟩
  obtain ⟨L, hLW, hyL, hL⟩ := exists_irr_sub_of_khw hE hU _ hW2Dfin hW2DK (Submodule.mem_comap.2 hyW) hy0 hyH
  have hLK := kStable_of_isKStableSub hσ hD L hL.1 hL.2.1
  have hLLle : L.map (smD ε (rreg ε)).subtype ≤ (S ⊔ V1 ε Ψ).map A := by
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.mem_comap.1 (hLW hx)
  have hLLK : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) (L.map (smD ε (rreg ε)).subtype) := by
    rintro g hg _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hLK g hg x hx
    exact ⟨z, hz, hzx⟩
  have hLL0 : L.map (smD ε (rreg ε)).subtype ≠ ⊥ := by
    intro h
    have hm : (y : L2 ε) ∈ L.map (smD ε (rreg ε)).subtype := ⟨y, hyL, rfl⟩
    rw [h] at hm
    exact hy0 (Submodule.coe_eq_zero.1 ((Submodule.mem_bot ℂ).1 hm))
  have hLLfin : FiniteDimensional ℂ (L.map (smD ε (rreg ε)).subtype) := by
    haveI := hL.1
    exact Module.Finite.map L _
  obtain ⟨x₀, hx₀L, hx₀⟩ := h1 _ hLLle hLLK hLL0
  have he' : e.comp (Submodule.inclusion hLLle) ≠ 0 := by
    intro h
    apply hx₀
    have := LinearMap.congr_fun h ⟨x₀, hx₀L⟩
    have hinc : Submodule.inclusion hLLle ⟨x₀, hx₀L⟩ = x₀ := Subtype.ext rfl
    rw [LinearMap.comp_apply, hinc, LinearMap.zero_apply] at this
    exact this
  obtain ⟨ν, x, hxw, hex⟩ := hWt n ε (L.map (smD ε (rreg ε)).subtype) hLLfin (hLLle.trans hAsm) hLLK N
    (e.comp (Submodule.inclusion hLLle)) he'
  have hνc : InCone (lowK ε lam) ν := h2 ν (Submodule.inclusion hLLle x) hxw hex
  have hx0 : (x : L2 ε) ≠ 0 := by
    intro h
    apply hex
    have : x = 0 := Subtype.ext h
    rw [this, map_zero]
  obtain ⟨z, hzL, hzx⟩ := x.2
  have hz0 : z ≠ 0 := by
    intro h
    apply hx0
    rw [← hzx, h, map_zero]
  have hzw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) ν (z : L2 ε) := by
    have : (z : L2 ε) = (x : L2 ε) := hzx
    rw [this]
    exact hxw
  have hzν := (isWtOn_iff hσ hD z ν).1 hzw
  have hcd := weights_le_of_irr_hw hE hU hL hzL hz0 hzν
  have hνΛ := hloweq_eq_of_cone hνc hcd
  subst hνΛ
  have hzH : IsKHWVec ε (smE ε (rreg ε)) (lowK ε lam) z := by
    refine ⟨hzν, fun a b hab hε => ?_⟩
    by_contra hne'
    have hm : smE ε (rreg ε) a b z ∈ L := hL.2.1 a b hε z hzL
    have hw2 := bhw_Ecc_Eab hE hzν a b
    have hd := weights_le_of_irr_hw hE hU hL hm hne' hw2
    exact not_cdom_add_root ε _ hab hd
  obtain ⟨k, hk⟩ := khw_line_of_irr hE hU hL hzL hyL hzH hyH hy0
  apply hex
  have hxy : Submodule.inclusion hLLle x = k • (⟨y, hyW⟩ : ↥((S ⊔ V1 ε Ψ).map A)) := by
    apply Subtype.ext
    simp only [Submodule.coe_inclusion, Submodule.coe_smul]
    rw [← hzx, hk]
    simp
  rw [LinearMap.comp_apply, hxy, map_smul, hey, smul_zero]

end PositivityTheory.RgDs.Hilb
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.HilbertSignatureHolds
section
noncomputable section

open Finset Matrix

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem hilbert_signature_holds : StepSig := by
  intro n ε lam T Ψ hP hst
  have hσ := rreg_isURepOn ε
  have hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x := by
    intro g hg x
    have hx : rreg ε g x ∈ Hlam ε Ψ T.w := hst g hg x x.2
    show (((Hlam ε Ψ T.w).orthogonalProjectionOnto (rreg ε g (x : L2 ε)) : Hlam ε Ψ T.w) : L2 ε) = _
    exact congrArg Subtype.val
      (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hx⟩ : Hlam ε Ψ T.w))
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show inUJ ε 1
    simp [inUJ]
  refine ⟨hcoe, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [hcoe 1 h1 x, hσ.1.1]
    rfl
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [ContinuousLinearMap.comp_apply, hcoe _ (mul_mem_unitaryJ ha hb) x,
      hcoe a ha, hcoe b hb, hσ.1.2 a ha b hb, ContinuousLinearMap.comp_apply]
  · intro g hg x
    have h := hσ.2.1 g hg (x : L2 ε)
    rw [← hcoe g hg x] at h
    simpa using h
  · intro v
    exact (Hlam ε Ψ T.w).orthogonalProjectionOnto.continuous.comp_continuousOn (hσ.2.2 (v : L2 ε))
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (datumV_ne_bot hP (HW.KType.w_ne_zero T))
    refine nontrivial_of_ne (⟨(x : L2 ε), UnitaryGroupOfForm.mem_closGen (E := smE ε (rreg ε)) _ x hx⟩ : Hlam ε Ψ T.w) 0 ?_
    intro h
    apply hx0
    have h2 : (x : L2 ε) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2

end PositivityTheory.RgDs.Hilb
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.HilbertStableHolds
section
noncomputable section

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem hilbert_stable_holds : StepStable := by
  intro n ε lam T Ψ hP
  have hv₀ : T.w ≠ 0 := HW.KType.w_ne_zero T
  have hσ := rreg_isURepOn ε
  have hV := datumV_isKIrrHW hP hv₀
  exact closure_genSub_stable hσ (isDerivedOn_smE hσ) hV.1 hV.2.1 (datumV_casimir hP T.w)

theorem hilbert_datum_holds : StepDatum := by
  intro n ε lam T Ψ hP
  have hv₀ : T.w ≠ 0 := HW.KType.w_ne_zero T
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV := datumV_isKIrrHW hP hv₀
  exact isKTypeOf_of_isKIrrHW hσ hD hV (datumV_kStable hP T.w) (fun μ x hx hx0 hμ =>
    weights_le_of_irr_hw hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hx hx0 hμ)

end PositivityTheory.RgDs.Hilb
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.WeightSpaceLeHilbert
section
noncomputable section

open Finset Matrix

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem weight_space_le_hilbert {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : V1 ε Ψ ≤ Hlam ε Ψ T.w := by
  rintro _ ⟨v, hv, rfl⟩
  exact UnitaryGroupOfForm.mem_closGen (E := smE ε (rreg ε)) (datumV ε Ψ T.w) v hv

theorem hilb_of (h1 : StepStable) (h2 : StepDatum) (h0 : StepSig) (h3 : StepMoll) (h4 : StepWtSpan)
    (h5 : StepStable → StepMoll → StepWtSpan → StepCone)
    (h6 : StepStable → StepMoll → StepWtSpan → StepDatum → StepLowEq)
    (h7 : StepDatum → StepIrred) (h8 : StepDatum → StepFormulaF) (h10 : StepSig → StepSqInt)
    (h9 : StepVogan) : Hilb := by
  intro n ε lam T Ψ hl hP hK
  have hst := h1 n ε lam T Ψ hP
  obtain ⟨hcoe, hU, hnt⟩ := h0 n ε lam T Ψ hP hst
  have hlow := h6 h1 h3 h4 h2 n ε lam T Ψ hl hP hK
  have hinj : Function.Injective (Hlam ε Ψ T.w).subtype := Subtype.val_injective
  have hint : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, (Hlam ε Ψ T.w).subtype (sigLam ε Ψ T.w g x) =
      rreg ε g ((Hlam ε Ψ T.w).subtype x) := by
    intro g hg x
    rw [mir_Kset_eq] at hg
    exact hcoe g (UnitaryGroupOfForm.K_mem_UJ hg) x
  have hcone : ∀ (η : Fin n → ℝ) (S : Submodule ℂ (Hlam ε Ψ T.w)),
      Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ T.w) η S → InCone (lowK ε lam) η := by
    intro η S hS
    rw [isKTypeOf_map_iff _ hinj hint] at hS
    exact h5 h1 h3 h4 n ε lam T Ψ hl hP hK η _ (Submodule.map_subtype_le _ _) hS
  have hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w) := by
    intro S hSc hSG
    have hcl : IsClosed ((S.map (Hlam ε Ψ T.w).subtype : Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
      have h := (Submodule.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal.isClosedMap
        (S : Set (Hlam ε Ψ T.w)) hSc
      rw [Submodule.map_coe]
      exact h
    have hst' : ∀ g ∈ UJset ε, ∀ x ∈ S.map (Hlam ε Ψ T.w).subtype,
        rreg ε g x ∈ S.map (Hlam ε Ψ T.w).subtype := by
      rintro g hg _ ⟨x, hx, rfl⟩
      exact ⟨sigLam ε Ψ T.w g x, hSG g (by rw [mir_UJset_eq]; exact hg) x hx, hcoe g hg x⟩
    rcases h7 h2 n ε lam T Ψ hP hst hlow _ (Submodule.map_subtype_le _ _) hcl hst' with h | h
    · left
      exact Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)
    · right
      apply Submodule.map_injective_of_injective hinj
      rw [h, Submodule.map_top, Submodule.range_subtype]
  refine ⟨⟨inferInstance, hnt, ?_, hirr, h10 h0 n ε lam T Ψ hP hst (h8 h2 n ε lam T Ψ hP hst hlow) hirr, ?_, ?_⟩, hcone⟩
  · rw [mir_isURepOn_iff, mir_UJset_eq]
    exact hU
  · refine ⟨(V1 ε Ψ).comap (Hlam ε Ψ T.w).subtype, ?_⟩
    rw [isKTypeOf_map_iff _ hinj hint, Submodule.map_comap_subtype, inf_eq_right.2 (weight_space_le_hilbert Ψ), mir_lowK_eq]
    exact h2 n ε lam T Ψ hP
  · intro μ S hS
    exact h9 n ε lam μ hl (hcone μ S hS)

end PositivityTheory.RgDs.Hilb
end
end

