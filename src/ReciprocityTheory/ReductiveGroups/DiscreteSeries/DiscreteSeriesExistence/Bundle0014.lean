module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Compact
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PuniqSmoothAddSmul
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0010
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0013
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroTopA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FinalExists
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

theorem final_existsG_of (hS7 : ∀ m : ℕ, S7.PsiExistsStatement m) :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
          (16 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) +
            8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))) < h →
        ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
          (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ := by
  intro n ε lam hlam h hh hmax
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  by_cases hpq : pOf ε = 0 ∨ qOf ε = 0
  · obtain ⟨σ, hDS, -⟩ := isDS_compact hpq hlam T
    exact ⟨T.V, inferInstance, inferInstance, σ, hDS⟩
  · simp only [not_or] at hpq
    have hq : 1 ≤ S7.q0 ε := by
      show 1 ≤ min (pOf ε) (qOf ε)
      omega
    have hgap : StdGap ε lam := ⟨hlam.1, h, hh, (le_max_left _ _).trans_lt hmax⟩
    have h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
      have h16 := (le_max_right _ _).trans_lt hmax
      have hs : 0 ≤ Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ)) := Real.sqrt_nonneg _
      have hnq : 0 ≤ (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) := by positivity
      show 8 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) < h
      nlinarith
    obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor (hS7 n) T hlam hh hq h8
    exact ⟨_, inferInstance, inferInstance, sigLam ε Ψ T.w, isDS_sigLam hgap hP (HW.KType.w_ne_zero T)⟩

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamEquivData
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_equiv_data (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    {V : Submodule ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hV0 : V ≠ ⊥) :
    ∃ U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] closGen E V, ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀,
      ((U (sigLam ε Ψ v₀ g x) : closGen E V) : H) = σ g ((U x : closGen E V) : H) := by
  have hσ₁ := rreg_isURepOn ε
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ₁ (isDerivedOn_smE hσ₁) (datumV_isKIrrHW hP hv₀)
    (datumV_casimir hP v₀) (datumV_kStable hP v₀) (datumV_ne_bot hP hv₀) hσ hD hV hc hVK hV0
  exact ⟨U, fun g hg x => hU g hg (sigLam ε Ψ v₀ g x) x (sigLam_coe hgap hP hv₀ hg x)⟩

theorem puniq_exists_h {lam' : Fin n → ℝ} (hgap : StdGap ε lam) (hgap' : StdGap ε lam') :
    ∃ h : ℝ, GapAtLeast ε lam h ∧ GapAtLeast ε lam' h ∧
      (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h ∧ (n : ℝ) - 1 < h := by
  obtain ⟨-, h1, hg1, hb1⟩ := hgap
  obtain ⟨-, h2, hg2, hb2⟩ := hgap'
  have hpq0 : (0 : ℝ) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by positivity
  by_cases hex : ∃ a b : Fin n, ε a ≠ ε b
  · obtain ⟨a, b, hab⟩ := hex

    have hp : 0 < pOf ε := by
      unfold pOf
      apply Finset.card_pos.mpr
      rcases Bool.eq_false_or_eq_true (ε a) with ha | ha
      · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
      · have hb : ε b = true := by
          rw [ha] at hab
          revert hab
          cases ε b <;> simp
        exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
    have hq : 0 < qOf ε := by
      unfold qOf
      apply Finset.card_pos.mpr
      rcases Bool.eq_false_or_eq_true (ε a) with ha | ha
      · have hb : ε b = false := by
          rw [ha] at hab
          revert hab
          cases ε b <;> simp
        exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
      · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    have hp' : (1 : ℝ) ≤ (pOf ε : ℝ) := by exact_mod_cast hp
    have hq' : (1 : ℝ) ≤ (qOf ε : ℝ) := by exact_mod_cast hq
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpq : (1 : ℝ) ≤ (pOf ε : ℝ) * (qOf ε : ℝ) := by nlinarith
    have hle : (n : ℝ) * 1 ≤ (n : ℝ) * ((pOf ε : ℝ) * (qOf ε : ℝ)) := mul_le_mul_of_nonneg_left hpq hn
    have hm := lt_min hb1 hb2
    refine ⟨min h1 h2, fun a b hab => le_trans (min_le_left _ _) (hg1 a b hab),
      fun a b hab => le_trans (min_le_right _ _) (hg2 a b hab), hm, ?_⟩
    nlinarith
  · push_neg at hex
    refine ⟨(n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + (n : ℝ) + 2, fun a b h => absurd (hex a b) h,
      fun a b h => absurd (hex a b) h, by linarith, ?_⟩
    linarith

theorem sigLam_inj (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {lam' : Fin n → ℝ} {T' : S7.KType ε (lowK ε lam')}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)} {v₀' : T'.V} (hgap' : StdGap ε lam')
    (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0) (U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] Hlam ε Ψ' v₀')
    (hU : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀, U (sigLam ε Ψ v₀ g x) = sigLam ε Ψ' v₀' g (U x)) :
    lam = lam' := by
  obtain ⟨h, hg, hg', hb, hn⟩ := puniq_exists_h hgap hgap'
  have hU' : ∀ g ∈ UJset ε, ∀ y : Hlam ε Ψ' v₀', U.symm (sigLam ε Ψ' v₀' g y) = sigLam ε Ψ v₀ g (U.symm y) := by
    intro g hgU y
    have := hU g hgU (U.symm y)
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    rw [← this, LinearIsometryEquiv.symm_apply_apply]
  have hK1 := puniq_isKTypeOf_map U (fun g hgK x => hU g (puniq_kset hgK) x) (sigLam_lowK hgap hP hv₀).1
  have hK2 := puniq_isKTypeOf_map U.symm (fun g hgK y => hU' g (puniq_kset hgK) y)
    (sigLam_lowK hgap' hP' hv₀').1
  have b1 := (sigLam_kType_bounds hgap' hP' hv₀' _ hK1).2 h hg' hb
  have b2 := (sigLam_kType_bounds hgap hP hv₀ _ hK2).2 h hg hb
  rw [mir_lowK_eq] at b1 b2
  by_contra hne
  have hne' : lowK ε lam ≠ lowK ε lam' := by
    intro heq
    apply hne
    funext a
    have := congrFun heq a
    simp only [lowK, Pi.add_apply, Pi.sub_apply] at this
    linarith
  have c1 := b1 hne'
  have c2 := b2 (Ne.symm hne')
  linarith

theorem puniq_psi_eq (hgap : StdGap ε lam) {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam T Ψ') (hv₀ : v₀ ≠ 0) :
    ∀ g ∈ UJset ε, Ψ' g = Ψ g := by
  have hσ₁ := rreg_isURepOn ε
  obtain ⟨U, hU⟩ := sigLam_equiv_data (Ψ := Ψ) hgap hP hv₀ hσ₁ (isDerivedOn_smE hσ₁)
    (datumV_isKIrrHW hP' hv₀) (datumV_casimir hP' v₀) (datumV_kStable hP' v₀) (datumV_ne_bot hP' hv₀)
  let U' : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] Hlam ε Ψ' v₀ := U
  have hUi : ∀ g ∈ UJset ε, ∀ x, U' (sigLam ε Ψ v₀ g x) = sigLam ε Ψ' v₀ g (U' x) := fun g hg x =>
    Subtype.ext ((hU g hg x).trans (sigLam_coe hgap hP' hv₀ hg (U' x)).symm)
  have hK := puniq_isKTypeOf_map U' (fun g hgK x => hUi g (puniq_kset hgK) x) (sigLam_lowK hgap hP hv₀).1
  have hKeq := (sigLam_lowK hgap hP' hv₀).2 _ hK
  let xv : T.V → Hlam ε Ψ v₀ := fun v => ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_Hlam hP v⟩
  have hxv_mem : ∀ v, xv v ∈ lowKSubLam ε Ψ v₀ := by
    intro v
    show (xv v : L2 ε) ∈ (datumV ε Ψ v₀).map (smD ε (rreg ε)).subtype
    exact ⟨⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩, (mem_datumV_iff hP v₀ _).2 ⟨v, rfl⟩, rfl⟩
  have hA : ∀ v, ∃ v', ((U' (xv v) : Hlam ε Ψ' v₀) : L2 ε) = uniformisationL2 ε Ψ' v₀ v' := by
    intro v
    have h1 : U' (xv v) ∈ lowKSubLam ε Ψ' v₀ := by
      rw [← hKeq]
      exact ⟨xv v, hxv_mem v, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 h1)
    obtain ⟨v', hv'⟩ := (mem_datumV_iff hP' v₀ y).1 hy
    exact ⟨v', hyx.symm.trans hv'⟩
  choose A hAv using hA
  have hj' := uniformisationL2_injective hP' hv₀
  have xv_add : ∀ v w, xv (v + w) = xv v + xv w := fun v w =>
    Subtype.ext (by rw [Submodule.coe_add]; exact datumEmbedding_add hP v₀ v w)
  have xv_smul : ∀ (c : ℂ) v, xv (c • v) = c • xv v := fun c v =>
    Subtype.ext (by rw [Submodule.coe_smul]; exact datumEmbedding_smul hP v₀ c v)
  have hAadd : ∀ v w, A (v + w) = A v + A w := by
    intro v w
    apply hj'
    rw [← hAv, xv_add, map_add (f := _), Submodule.coe_add, hAv, hAv, datumEmbedding_add hP']
  have hAsmul : ∀ (c : ℂ) v, A (c • v) = c • A v := by
    intro c v
    apply hj'
    rw [← hAv, xv_smul, map_smul, Submodule.coe_smul, hAv, datumEmbedding_smul hP']
  have hAk : ∀ (k : S7.KG ε) (v : T.V), A (T.op k v) = T.op k (A v) := by
    intro k v
    have hk : S7.toMK k ∈ UJset ε := (k : S7.UJ ε).2
    have e1 : xv (T.op k v) = sigLam ε Ψ v₀ (S7.toMK k) (xv v) :=
      Subtype.ext ((sigLam_coe hgap hP hv₀ hk (xv v)).trans (rightRegular_datumEmbedding hP v₀ v k)).symm
    apply hj'
    rw [← hAv, e1, hUi _ hk, sigLam_coe hgap hP' hv₀ hk, hAv, rightRegular_datumEmbedding hP' v₀ (A v) k]
  let Alin : T.V →ₗ[ℂ] T.V := { toFun := A, map_add' := hAadd, map_smul' := hAsmul }
  obtain ⟨c, hc⟩ := puniq_schur T Alin hAk
  have hc' : ∀ v, A v = c • v := hc
  have key : ∀ g ∈ UJset ε, ∀ v v' : T.V,
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v) =
        ((‖uniformisationL2 ε Ψ' v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ (A v') (Ψ' g (A v)) := by
    intro g hg v v'
    rw [← formulaF_sigLam hgap hP hv₀ hg v v', ← formulaF hgap hP' hv₀ hg (A v) (A v'), ← hAv, ← hAv,
      ← U'.inner_map_map (xv v') (sigLam ε Ψ v₀ g (xv v)), hUi g hg, Submodule.coe_inner,
      sigLam_coe hgap hP' hv₀ hg]
  have hr : ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := datumEmbedding_highest_ne_zero hgap hP hv₀
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr this)
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have hw0 : T.w ≠ 0 := by
    intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hW : inner ℂ T.w T.w ≠ 0 := inner_self_ne_zero.mpr hw0
  have e1 := key 1 h1 T.w T.w
  rw [hP.2.1, hP'.2.1] at e1
  simp only [hc', map_smul, ContinuousLinearMap.one_apply, inner_smul_left, inner_smul_right] at e1
  have hrr : ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) =
      ((‖uniformisationL2 ε Ψ' v₀ T.w‖ ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) c * c) := by
    apply mul_right_cancel₀ hW
    rw [e1]
    ring
  intro g hg
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun v' => ?_
  have e := key g hg v v'
  simp only [hc', map_smul, inner_smul_left, inner_smul_right] at e
  have e' : ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v) =
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ' g v) := by
    rw [e, hrr]
    ring
  exact (mul_left_cancel₀ hr e').symm

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamLeOfKTypes
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def opConv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (v : H) : H :=
  ∫ g : Formalism.REAL.UJ ε, α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) v ∂(Formalism.REAL.muG ε)

def IsAdKInv (ε : Fin n → Bool) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ k ∈ Kset ε, ∀ g, α (k * g * star k) = α g

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_le_of_kTypes (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (W : Submodule ℂ (Hlam ε Ψ v₀)) (hWf : FiniteDimensional ℂ W)
    (hWfull : ∀ (μ : Fin n → ℝ) (S : Submodule ℂ (Hlam ε Ψ v₀)),
      Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S →
        (∃ S' ≤ W, Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S') → S ≤ W)
    (hWsum : W ≤ sSup {S : Submodule ℂ (Hlam ε Ψ v₀) | ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S})
    (U : Set (Matrix (Fin n) (Fin n) ℂ)) (hU : IsOpen U) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) :
    ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ U ∧
      IsAdKInv ε α ∧ ∀ w ∈ W, opConv ε (sigLam ε Ψ v₀) α w = w := by
  obtain ⟨α, ⟨hsmooth, hcpt, hsupp, hinv⟩, hfix⟩ :=
    exists_cvA_idA (sigLam_isURepOn hgap hP hv₀) (sigLam_admissible hgap hP hv₀) W hWf hWsum hU h1
  exact ⟨α, hsmooth, hcpt, hsupp, fun k hk g => hinv k hk g, hfix⟩

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroTop
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem psi_eq_PsiM {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hK : ∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂)
    {μ : Fin n → ℤ} (hμ : S7.IsMu lam μ)
    (hF : ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
      Ψ (NormedSpace.exp X) =
        ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) •
          ∫ k, S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ •
            (T.op k * S7.projW T * T.op k⁻¹) ∂(S7.muK ε)) :
    ∀ g ∈ UJset ε, Ψ g = S7.PsiM T μ g := by
  intro g hg
  have hex : ∃ (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X ∧ g = S7.toMK k * NormedSpace.exp X :=
    S7.polar_exists hg
  have key : ∀ (kc : S7.KG ε) (Xc : Matrix (Fin n) (Fin n) ℂ), inP ε Xc → g = S7.toMK kc * NormedSpace.exp Xc →
      Ψ g = T.op kc * S7.psM T μ (NormedSpace.exp Xc) := by
    intro kc Xc hXc hgc
    have hu : inUJ ε (NormedSpace.exp Xc) := by
      have := S7.inUJ_kexp (1 : S7.KG ε) hXc
      rwa [pdA_toMK_one, Matrix.one_mul] at this
    have h1 := hK kc 1 (NormedSpace.exp Xc) hu
    rw [pdA_toMK_one, Matrix.mul_one, pdA_op_one, mul_one] at h1
    have hps : Ψ (NormedSpace.exp Xc) = S7.psM T μ (NormedSpace.exp Xc) := by
      rw [hF Xc hXc]
      simp only [szt_phiM_inv_conj μ hXc]
      rfl
    rw [hgc, h1, hps]
  unfold S7.PsiM
  rw [dite_eq_left hex]
  exact key _ _ hex.choose_spec.choose_spec.1 hex.choose_spec.choose_spec.2

theorem sigZero (hAll : ∀ m : ℕ, S7.PsiAllStatement m) : Lap.SigZeroStatement := by
  intro k r z c u v b h hS
  obtain ⟨hk, -, -, -, -, -, hlamR, -, -, -, hGL⟩ := hS
  have hqOf : qOf (Formalism.MainNotions.CayleySignature.eps48 k r) = r + 1 := Lap.noncompactCount_parabolicSign k r hk
  have hpOf : pOf (Formalism.MainNotions.CayleySignature.eps48 k r) = k + r := by
    rw [Lap.compactCount_parabolicSign k r hk]; omega
  obtain ⟨P, hPc⟩ := exists_cayley_unitary k r hk
  generalize Formalism.MainNotions.CayleySignature.lam48 k r v b = lam at hlamR hGL ⊢
  generalize Formalism.MainNotions.CayleySignature.eps48 k r = ε at hqOf hpOf hPc hGL ⊢
  have hlam : S7.IsHCParam lam := (mir_isHCParam_iff lam).1 hlamR
  obtain ⟨hanti, hgapAt, hN⟩ := hGL

  have hq0 : S7.q0 ε = min (k + r) (r + 1) := by unfold S7.q0; rw [hpOf, hqOf]
  have hq1 : 1 ≤ S7.q0 ε := by rw [hq0]; exact le_min (by omega) (by omega)
  have hQ1 : (1 : ℝ) ≤ (S7.q0 ε : ℝ) := by exact_mod_cast hq1
  have hp' : (pOf ε : ℝ) = (k : ℝ) + r := by rw [hpOf, Nat.cast_add]
  have hq' : (qOf ε : ℝ) = (r : ℝ) + 1 := by rw [hqOf, Nat.cast_add, Nat.cast_one]
  have hmin : min (pOf ε : ℝ) (qOf ε : ℝ) = (S7.q0 ε : ℝ) := by unfold S7.q0; rw [Nat.cast_min]
  unfold Lap.hNeed at hN
  try simp only [Nat.cast_min] at hN
  rw [hmin, hp', hq'] at hN
  obtain ⟨hN1, hN2⟩ := max_lt_iff.1 hN
  obtain ⟨hN2a, hN2b⟩ := max_lt_iff.1 hN2
  have hN1' := lt_of_le_of_lt (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)) hN1
  obtain ⟨-, hNpq⟩ := max_lt_iff.1 hN1'
  have hNn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgap : StdGap ε lam := ⟨hanti, h, hgapAt, by rw [hp', hq']; linarith⟩
  have hNQ : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := mul_nonneg hNn (by linarith)
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have h8 : 8 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) < h := by linarith
  have hthr : 4 * max (Lap.S0.bG k r) (Lap.S0.bS k r) < h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) - 1 := by
    have hbG : Lap.S0.bG k r = 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by
      unfold Lap.S0.bG Lap.S0.nS Lap.S0.q0S; rw [← hq0]
    have hbS : Lap.S0.bS k r = 2 * ((r : ℝ) + 1 - 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by
      unfold Lap.S0.bS Lap.S0.nS; ring
    rw [hbG, hbS]
    have hs : 0 < Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_pos.2 (by linarith)
    rw [lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
    nlinarith [hN2b]

  have hint := hlam.2
  choose mm hmm using hint
  let μ : Fin (2 * r + k + 1) → ℤ := fun a => mm a + ((2 * r + k + 1 : ℕ) : ℤ) - 1 - ((a : ℕ) : ℤ)
  have hμ : S7.IsMu lam μ := by
    unfold S7.IsMu
    intro a
    have ha := hmm a
    simp only [μ]
    unfold rho
    push_cast at ha ⊢
    linarith

  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨Ψ, ha, hb, hc, hd, hdec, he, -, hF⟩ := hAll (2 * r + k + 1) ε lam h T hlam hgapAt hq1
  have hP : IsPsiFor ε lam T Ψ := ⟨ha, hb, hc, hd, fun μ' hμ' => (he μ' hμ').2.1 h8⟩
  have hv₀ : T.w ≠ 0 := by
    intro h0
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hPsi := psi_eq_PsiM ha hμ (hF μ hμ)
  have hDS := isDS_sigLam hgap hP hv₀
  refine ⟨↥(Hlam ε Ψ T.w), inferInstance, inferInstance, inferInstance,
    fun g => sigLam ε Ψ T.w (P * g * P⁻¹), isDSHpk_of_isDS hPc hDS, isURepOn_UH_of hPc hDS.2.2.1, ?_⟩
  intro w₀ hw₀
  have hlow := isLowUnit_of_isLowUnitH hPc hDS hw₀
  have hlowK : Formalism.MainNotions.S.lowKSub ε lam (sigLam ε Ψ T.w) = lowKSubLam ε Ψ T.w := by
    obtain ⟨h1, h2⟩ := sigLam_lowK hgap hP hv₀
    unfold Formalism.MainNotions.S.lowKSub
    have hset : {S | Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ T.w) (Formalism.QuantumDeterminants.lowK ε lam) S} =
        {lowKSubLam ε Ψ T.w} :=
      Set.ext fun S => ⟨fun hS => h2 S hS, fun hS => by rw [Set.mem_singleton_iff.1 hS]; exact h1⟩
    rw [hset, sSup_singleton]
  have hmem : w₀ ∈ lowKSubLam ε Ψ T.w := hlowK ▸ hlow.2
  unfold lowKSubLam at hmem
  rw [Submodule.mem_comap, Submodule.mem_map] at hmem
  obtain ⟨x, hx, hxw⟩ := hmem
  obtain ⟨v₁, hv₁⟩ := (mem_datumV_iff hP T.w x).1 hx
  have hxw' : (x : L2 ε) = (w₀ : L2 ε) := hxw
  have hw0L : (w₀ : L2 ε) = uniformisationL2 ε Ψ T.w v₁ := by rw [← hv₁, hxw']
  have hw0 : w₀ = ⟨uniformisationL2 ε Ψ T.w v₁, datumEmbedding_mem_Hlam hP v₁⟩ := Subtype.ext hw0L
  have hv1 : v₁ ≠ 0 := by
    intro h0
    have hj0 : uniformisationL2 ε Ψ T.w 0 = 0 := by simpa using datumEmbedding_smul hP T.w 0 0
    have hz : w₀ = 0 := Subtype.ext (by rw [hw0L, h0, hj0]; rfl)
    have h1 := hlow.1
    rw [hz, norm_zero] at h1
    exact zero_ne_one h1
  have hc1 : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (pow_ne_zero 2 (norm_ne_zero_iff.2 (datumEmbedding_highest_ne_zero hgap hP hv₀)))
  obtain ⟨C, hC⟩ := dec_gN_sigLam hgap hP hv₀ hq1 hdec v₁ v₁
  refine ⟨fun μG hμG => fdegB_of_isDS hPc hDS μG hμG,
    ⟨h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))), C, hthr, fun g hg => ?_⟩,
    T, μ, P, v₁, _, hv1, hc1, hμ, hPc.1, fun g hg => ?_⟩
  · have hgJ := szt_conj_mem hPc hg
    show ‖inner ℂ w₀ (sigLam ε Ψ T.w (P * g * P⁻¹) w₀)‖ ≤ _
    rw [Submodule.coe_inner, sigLam_coe hgap hP hv₀ hgJ, hw0L]
    calc _ ≤ C * Real.sqrt (S7.hs (P * g * P⁻¹)) ^ (-(h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))))) :=
          hC _ hgJ
      _ = _ := by rw [szt_hs_conj hPc, szt_gN_eq]
  · have hgJ := szt_conj_mem hPc hg
    show inner ℂ w₀ (sigLam ε Ψ T.w (P * g * P⁻¹) w₀) = _
    rw [hw0, formulaF_sigLam hgap hP hv₀ hgJ v₁ v₁]
    unfold Lap.psiCoef
    rw [hPsi _ hgJ]
    rfl

end ReciprocityTheory.ChartRestriction.DS
end
end

