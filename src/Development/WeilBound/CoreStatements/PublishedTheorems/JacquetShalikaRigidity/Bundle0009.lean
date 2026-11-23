module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PrimePairSetFirst
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace primePairSetFirst

variable {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem cont_colT (hψ : StdPsi ψ) (m : ℕ) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g) :
    Continuous (colT ψ (m + 1) f) := by
  have key := _root_.GlobalTheory.CuspGeneric.continuous_avg_of_periodic (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1)))
    (isCoLat_ratV E _) (GA E k)
    (fun p => ψ (-dot (eLast k (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_
  · exact key
  · exact (hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
      (hc.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))
  · intro g γ hγ y
    exact (per_coef hψ (eLast k (m + 1)) hc hl g).2 γ hγ y

theorem colT_blkU (hψ : StdPsi ψ) (m : ℕ) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g)
    (y : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (g : GA E k) :
    colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast k (m + 1)) y) * colT ψ (m + 1) f g := by
  have hper := per_coef (a := k) hψ (eLast k (m + 1)) hc hl g
  have hT := GlobalTheory.T.quotientAverage_translate_invariant (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1)))
    (isCoLat_ratV E _) _ hper y
  have hpt : (fun x : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E =>
        ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) =
      fun x => ψ (dot (eLast k (m + 1)) y) *
        (ψ (-dot (eLast k (m + 1)) (x + y)) * f (blkU (x + y) * g)) := by
    funext x
    have hd : dot (eLast k (m + 1)) (x + y) = dot (eLast k (m + 1)) x + dot (eLast k (m + 1)) y := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hu : (blkU (x + y) : GA E k) = blkU x * blkU y := posU_add _ x y
    have h1 : ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]
    calc ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))
        = (ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y)) *
            (ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) := by rw [h1, one_mul]
      _ = _ := by ring
  change avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) =
    _ * avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * g))
  rw [hpt, avg_const_mul]
  exact congrArg _ hT

theorem colT_law (m : ℕ) (f : GA E k → ℂ) (j : ℕ) (hj : m + 1 < j)
    (hlaw : ∀ (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k), f (blkU y * g) = ψ (dot (eLast k j) y) * f g)
    (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k) :
    colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast k j) y) * colT ψ (m + 1) f g := by
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  have e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast k j) y) * f (blkU x * g) := by
    rw [← mul_assoc, blkU_mul_blkU hj x y, mul_assoc, hlaw, dot_eLast_shift hj x y]
  rw [e1]
  ring

theorem colT_rat (hψ : StdPsi ψ) (m : ℕ) (hmk : m + 1 < k) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ γ : GL (Fin k) E, IsMir (m + 1) γ → ∀ g, f (ratGL E k γ * g) = f g)
    (γ : GL (Fin k) E) (hγ : IsMir (m + 1) γ) (g : GA E k) :
    colT ψ (m + 1) f (ratGL E k γ * g) = coefF ψ (m + 1) (fun t => γ.val ⟨m, by omega⟩ t.1.1) f g := by
  unfold colT
  rw [_root_.GlobalTheory.CuspGeneric.coefF_ratGL_mul E k ψ hψ m f hc hl γ hγ (eLast k (m + 1)) g]
  congr 1
  funext t
  let s0 : UnipotentBlockColumnIndex k (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hmk⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
  rw [Finset.sum_eq_single s0]
  · have h1 : eLast (E := E) k (m + 1) s0 = 1 := by simp [eLast, s0]
    rw [h1, one_mul]
  · intro s _ hs
    have h0 : eLast (E := E) k (m + 1) s = 0 := by
      simp only [eLast]
      rw [if_neg]
      intro e
      apply hs
      have h2 := s.2.2
      apply Subtype.ext
      exact Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blk_eta {m : ℕ} (hmk : m + 1 < k) (t : UnipotentBlockColumnIndex k (m + 1) (m + 1)) :
    (⟨(t.1.1, ⟨m + 1, hmk⟩), t.2.1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex k (m + 1) (m + 1)) = t := by
  have h := t.2.2
  exact Subtype.ext (Prod.ext rfl (Fin.ext (by show m + 1 = (t.1.2 : ℕ); omega)))

def rowEquiv (m : ℕ) (hmk : m + 1 < k) : RowT E k (m + 1) ≃ {ξ : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E // ξ ≠ 0} where
  toFun ξ := ⟨fun t => ξ.1 t.1.1, by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ξ.2.1
    have him : (i : ℕ) < m + 1 := by
      by_contra h
      exact hi (ξ.2.2 i (by omega))
    intro h0
    exact hi (congrFun h0 ⟨(i, ⟨m + 1, hmk⟩), him, le_rfl, le_rfl⟩)⟩
  invFun η := ⟨fun i => if h : (i : ℕ) < m + 1 then η.1 ⟨(i, ⟨m + 1, hmk⟩), h, le_rfl, le_rfl⟩ else 0, by
    refine ⟨fun h0 => η.2 ?_, fun i hi => dif_neg (by omega)⟩
    funext t
    have h1 := congrFun h0 t.1.1
    simp only [Pi.zero_apply] at h1
    rw [dif_pos t.2.1, blk_eta hmk t] at h1
    exact h1⟩
  left_inv ξ := by
    apply Subtype.ext
    funext i
    by_cases h : (i : ℕ) < m + 1
    · exact dif_pos h
    · exact (dif_neg h).trans (ξ.2.2 i (by omega)).symm
  right_inv η := by
    apply Subtype.ext
    funext t
    show (if h : (t.1.1 : ℕ) < m + 1 then η.1 ⟨(t.1.1, ⟨m + 1, hmk⟩), h, le_rfl, le_rfl⟩ else 0) = η.1 t
    rw [dif_pos t.2.1, blk_eta hmk t]

end primePairSetFirst

theorem p1_holds : N0 → P0 → P1 := by
  intro hN _ E _ _ _ k ψ hψ m hm1 hmk f hf
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g
  simp only [Nat.add_sub_cancel]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ⟨primePairSetFirst.rowEquiv m hmk, fun ξ t => rfl⟩⟩
  · exact primePairSetFirst.cont_colT hψ m f hf.cont hl
  · intro γ hγ g
    have hγ1 : IsMir (m + 1) γ := fun i c h => hγ i c (by omega)
    rw [primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left γ hγ1 g]
    unfold colT
    congr 1
    funext t
    rw [hγ ⟨m, by omega⟩ t.1.1 (Or.inl le_rfl)]
    have ht := t.2.1
    simp only [eLast, Matrix.one_apply]
    by_cases h : (t.1.1 : ℕ) = m
    · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
    · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
  · intro j hj y g
    rcases Nat.lt_or_ge (m + 1) j with h1 | h1
    · exact primePairSetFirst.colT_law m f j h1 (hf.law j h1) y g
    · obtain rfl : j = m + 1 := by omega
      exact primePairSetFirst.colT_blkU hψ m f hf.cont hl y g
  · intro ξ g
    obtain ⟨hB, hrow⟩ := (hN E k (m + 1) (by omega) (by omega)).1 ξ
    have hγ : IsMir (m + 1) (gam ξ) := fun i c h => hB i c (by omega)
    rw [primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left _ hγ g]
    congr 1
    funext t
    exact (hrow _ _ rfl).symm
  · intro χ hχ
    funext g
    simp only [colT, coefF]
    rw [← avg_const_mul]
    congr 1
    funext x
    rw [hχ]
    ring

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.QuadraticTransferFirst
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace QuadraticTransferFirst

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem swap3 {μ ν ρ : Measure G} [SFinite μ] [SFinite ν] [SFinite ρ] (K : G → G → G → ℝ≥0∞)
    (hK : Measurable fun p : G × G × G => K p.1 p.2.1 p.2.2) :
    ∫⁻ g, ∫⁻ r, ∫⁻ h, K r h g ∂ν ∂ρ ∂μ = ∫⁻ r, ∫⁻ h, ∫⁻ g, K r h g ∂μ ∂ν ∂ρ := by
  have hF : Measurable (Function.uncurry fun g r => ∫⁻ h, K r h g ∂ν) := by
    have : Measurable fun q : (G × G) × G => K q.1.2 q.2 q.1.1 :=
      hK.comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine lintegral_congr fun r => ?_
  have hK' : Measurable (Function.uncurry fun g h => K r h g) :=
    hK.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  exact lintegral_lintegral_swap hK'.aemeasurable

theorem main (μ : Measure G) [μ.IsHaarMeasure] (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G)
    (β β₁ : G → ℝ≥0∞) (hinv : Measure.map (fun h => h⁻¹) ν = ν) (hH : ∀ᵐ h ∂ν, h ∈ H) (hβ : IsWt ν β)
    (hβ₁ : Measurable β₁) (h1 : ∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1) (Φ : G → ℝ≥0∞)
    (hΦ : Measurable Φ) (hΦH : ∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) :
    ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
  have hβm : Measurable β := hβ.1
  have hH' : ∀ᵐ h ∂ν, h⁻¹ ∈ H := by
    have hH2 := hH
    rw [← hinv] at hH2
    exact ae_of_ae_map measurable_inv.aemeasurable hH2
  have hinvβ : ∀ g, ∫⁻ h, β (h⁻¹ * g) ∂ν = 1 := by
    intro g
    have hm : Measurable fun h : G => β (h * g) := by fun_prop
    rw [show (∫⁻ h, β (h⁻¹ * g) ∂ν) = ∫⁻ h, β (h * g) ∂(Measure.map (fun h => h⁻¹) ν) from
      (lintegral_map hm measurable_inv).symm, hinv]
    exact hβ.2 g
  calc ∫⁻ g, Φ g ∂μ.withDensity β
      = ∫⁻ g, β g * Φ g ∂μ := lintegral_withDensity_eq_lintegral_mul _ hβm hΦ
    _ = ∫⁻ g, ∫⁻ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν ∂ρ ∂μ := by
        refine lintegral_congr fun g => ?_
        have hm1 : ∀ r, Measurable fun h => β₁ (r⁻¹ * h * g) := fun r => by fun_prop
        have hm2 : Measurable fun r => ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          have : Measurable fun p : G × G => β₁ (p.1⁻¹ * p.2 * g) := by fun_prop
          exact this.lintegral_prod_right'
        calc β g * Φ g = β g * Φ g * ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ := by rw [h1 g, mul_one]
          _ = _ := by
            rw [← lintegral_const_mul _ hm2]
            refine lintegral_congr fun r => ?_
            rw [lintegral_const_mul _ (hm1 r)]
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β g * Φ g * β₁ (r⁻¹ * h * g) ∂μ ∂ν ∂ρ :=
        swap3 (fun r h g => β g * Φ g * β₁ (r⁻¹ * h * g))
          (show Measurable fun p : G × G × G => β p.2.2 * Φ p.2.2 * β₁ (p.1⁻¹ * p.2.1 * p.2.2) by fun_prop)
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β (h⁻¹ * g) * Φ g * β₁ (r⁻¹ * g) ∂μ ∂ν ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr_ae (hH'.mono fun h hh => ?_)
        refine (lintegral_mul_left_eq_self (μ := μ) (fun x => β x * Φ x * β₁ (r⁻¹ * h * x)) h⁻¹).symm.trans
          (lintegral_congr fun g => ?_)
        show β (h⁻¹ * g) * Φ (h⁻¹ * g) * β₁ (r⁻¹ * h * (h⁻¹ * g)) = _
        rw [hΦH _ hh, mul_assoc r⁻¹ h, mul_inv_cancel_left]
    _ = ∫⁻ r, ∫⁻ g, ∫⁻ h, β (h⁻¹ * g) * Φ g * β₁ (r⁻¹ * g) ∂ν ∂μ ∂ρ := by
        refine lintegral_congr fun r => ?_
        exact lintegral_lintegral_swap
          (show Measurable fun p : G × G => β (p.1⁻¹ * p.2) * Φ p.2 * β₁ (r⁻¹ * p.2) by fun_prop).aemeasurable
    _ = ∫⁻ r, ∫⁻ g, Φ g * β₁ (r⁻¹ * g) ∂μ ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr fun g => ?_
        simp_rw [mul_assoc]
        rw [lintegral_mul_const _ (show Measurable fun h : G => β (h⁻¹ * g) by fun_prop), hinvβ g, one_mul]
    _ = ∫⁻ r, ∫⁻ g, Φ (r * g) * β₁ g ∂μ ∂ρ := by
        refine lintegral_congr fun r => ?_
        refine (lintegral_mul_left_eq_self (μ := μ) (fun x => Φ x * β₁ (r⁻¹ * x)) r).symm.trans
          (lintegral_congr fun g => ?_)
        show Φ (r * g) * β₁ (r⁻¹ * (r * g)) = _
        rw [inv_mul_cancel_left]
    _ = ∫⁻ g, ∫⁻ r, Φ (r * g) * β₁ g ∂ρ ∂μ :=
        lintegral_lintegral_swap
          (show Measurable fun p : G × G => Φ (p.1 * p.2) * β₁ p.2 by fun_prop).aemeasurable
    _ = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
        have hm : Measurable fun g => ∫⁻ r, Φ (r * g) ∂ρ := by
          have : Measurable fun p : G × G => Φ (p.2 * p.1) := by fun_prop
          exact this.lintegral_prod_right'
        rw [lintegral_withDensity_eq_lintegral_mul _ hβ₁ hm]
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const _ (show Measurable fun r : G => Φ (r * g) by fun_prop)]
        exact mul_comm _ _

end QuadraticTransferFirst

theorem isUnit_last_join : Q1 := by
  intro G _ _ _ _ _ _ _ μ _ ν ρ _ _ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH
  exact QuadraticTransferFirst.main μ ν ρ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.QuadraticTransferReal
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace QuadraticTransferReal

theorem swap3 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ρ : Measure β) (ν : Measure γ) [SFinite μ] [SFinite ρ] [SFinite ν]
    (F : α → β → γ → ℝ≥0∞) (hF : Measurable fun p : α × β × γ => F p.1 p.2.1 p.2.2) :
    ∫⁻ g, ∫⁻ r, ∫⁻ h, F g r h ∂ν ∂ρ ∂μ = ∫⁻ r, ∫⁻ h, ∫⁻ g, F g r h ∂μ ∂ν ∂ρ := by
  have h1 : Measurable fun q : α × β => ∫⁻ h, F q.1 q.2 h ∂ν := by
    have : Measurable fun p : (α × β) × γ => F p.1.1 p.1.2 p.2 :=
      hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap (f := fun g r => ∫⁻ h, F g r h ∂ν) h1.aemeasurable]
  refine lintegral_congr fun r => ?_
  have h2 : Measurable fun q : α × γ => F q.1 r q.2 :=
    hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact lintegral_lintegral_swap (f := fun g h => F g r h) h2.aemeasurable

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem q1' (μ : Measure G) [μ.IsHaarMeasure] (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G)
    (β β₁ : G → ℝ≥0∞) (hinv : Measure.map (fun h => h⁻¹) ν = ν) (hH : ∀ᵐ h ∂ν, h ∈ H)
    (hβ : IsWt ν β) (hβ₁ : Measurable β₁) (h1 : ∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦH : ∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) :
    ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
  have hβm := hβ.1
  have hm : Measurable fun p : G × G × G => β p.1 * Φ p.1 * β₁ (p.2.1⁻¹ * p.2.2 * p.1) := by fun_prop
  have hm' : Measurable fun p : G × G × G => β₁ p.1 * (Φ (p.2.1 * p.1) * β (p.2.2⁻¹ * p.2.1 * p.1)) := by
    fun_prop
  have hint : ∀ x, ∫⁻ h, β (h⁻¹ * x) ∂ν = 1 := by
    intro x
    have := lintegral_map (f := fun h => β (h * x)) (g := fun h : G => h⁻¹) (μ := ν)
      (hβm.comp (measurable_mul_const x)) measurable_inv
    rw [hinv, hβ.2 x] at this
    exact this.symm
  have hR : Measurable fun g => ∫⁻ r, Φ (r * g) ∂ρ := by
    have : Measurable fun p : G × G => Φ (p.2 * p.1) := hΦ.comp (measurable_snd.mul measurable_fst)
    exact this.lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβm hΦ, lintegral_withDensity_eq_lintegral_mul _ hβ₁ hR]
  calc ∫⁻ g, (β * Φ) g ∂μ
      = ∫⁻ g, ∫⁻ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν ∂ρ ∂μ := by
        refine lintegral_congr fun g => ?_
        have hr : Measurable fun r => ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          have : Measurable fun p : G × G => β₁ (p.1⁻¹ * p.2 * g) := by fun_prop
          exact this.lintegral_prod_right'
        have e : ∀ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν = β g * Φ g * ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          intro r
          exact lintegral_const_mul _ (by fun_prop)
        simp only [e, Pi.mul_apply]
        rw [lintegral_const_mul _ hr, h1 g, mul_one]
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β g * Φ g * β₁ (r⁻¹ * h * g) ∂μ ∂ν ∂ρ :=
        swap3 μ ρ ν (fun g r h => β g * Φ g * β₁ (r⁻¹ * h * g)) hm
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂μ ∂ν ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr_ae ?_
        filter_upwards [hH] with h hh
        rw [← lintegral_mul_left_eq_self _ (h⁻¹ * r)]
        refine lintegral_congr fun g => ?_
        have e1 : r⁻¹ * h * (h⁻¹ * r * g) = g := by group
        have e2 : Φ (h⁻¹ * r * g) = Φ (r * g) := by
          have := hΦH h hh (h⁻¹ * (r * g))
          rw [mul_inv_cancel_left] at this
          rw [mul_assoc]
          exact this.symm
        simp only [e1, e2]
        ring
    _ = ∫⁻ g, ∫⁻ r, ∫⁻ h, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂ν ∂ρ ∂μ :=
        (swap3 μ ρ ν (fun g r h => β₁ g * (Φ (r * g) * β (h⁻¹ * r * g))) hm').symm
    _ = ∫⁻ g, (β₁ * fun g => ∫⁻ r, Φ (r * g) ∂ρ) g ∂μ := by
        refine lintegral_congr fun g => ?_
        have e : ∀ r, ∫⁻ h, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂ν = β₁ g * Φ (r * g) := by
          intro r
          simp_rw [← mul_assoc (β₁ g)]
          rw [lintegral_const_mul _ (by fun_prop)]
          simp_rw [mul_assoc _ r g]
          rw [hint, mul_one]
        simp only [e, Pi.mul_apply]
        exact lintegral_const_mul _ (hΦ.comp (measurable_mul_const g))

end

theorem real_transfer {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (A : Measure X)
    (B : Measure Y) (m : Y → X) (F : X → ℝ) (hi : Integrable F A) (hiB : Integrable (fun y => F (m y)) B)
    (h₁ : ∫⁻ x, ENNReal.ofReal (F x) ∂A = ∫⁻ y, ENNReal.ofReal (F (m y)) ∂B)
    (h₂ : ∫⁻ x, ENNReal.ofReal (-F x) ∂A = ∫⁻ y, ENNReal.ofReal (-F (m y)) ∂B) :
    ∫ x, F x ∂A = ∫ y, F (m y) ∂B := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiB, h₁, h₂]

theorem transfer {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (A : Measure X)
    (B : Measure Y) (m : Y → X) (hm : Measurable m) (Φ : X → ℂ) (hΦ : Measurable Φ) (P : (X → ℝ≥0∞) → Prop)
    (hP : ∀ f, Measurable f → P f → ∫⁻ x, f x ∂A = ∫⁻ y, f (m y) ∂B)
    (hn : P fun x => ‖Φ x‖ₑ) (hr₁ : P fun x => ENNReal.ofReal (Φ x).re)
    (hr₂ : P fun x => ENNReal.ofReal (-(Φ x).re)) (hi₁ : P fun x => ENNReal.ofReal (Φ x).im)
    (hi₂ : P fun x => ENNReal.ofReal (-(Φ x).im)) (hi : Integrable Φ A) :
    Integrable (fun y => Φ (m y)) B ∧ ∫ x, Φ x ∂A = ∫ y, Φ (m y) ∂B := by
  have hiB : Integrable (fun y => Φ (m y)) B := by
    refine ⟨(hΦ.comp hm).aestronglyMeasurable, ?_⟩
    have := hP _ (by fun_prop) hn
    rw [HasFiniteIntegral, ← this]
    exact hi.2
  refine ⟨hiB, ?_⟩
  apply Complex.ext
  · have a1 := integral_re hi
    have a2 := integral_re hiB
    simp only [RCLike.re_to_complex] at a1 a2
    rw [← a1, ← a2]
    exact real_transfer A B m (fun x => (Φ x).re) hi.re hiB.re
      (hP _ (by fun_prop) hr₁) (hP _ (by fun_prop) hr₂)
  · have a1 := integral_im hi
    have a2 := integral_im hiB
    simp only [RCLike.im_to_complex] at a1 a2
    rw [← a1, ← a2]
    exact real_transfer A B m (fun x => (Φ x).im) hi.im hiB.im
      (hP _ (by fun_prop) hi₁) (hP _ (by fun_prop) hi₂)

end QuadraticTransferReal

theorem closedSubgroup_cutoff_exists : Q2 := by
  intro G _ _ _ _ _ _ _ μ _ ν ρ _ _ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH hi
  have hm : Measurable fun p : G × G => p.2 * p.1 := measurable_snd.mul measurable_fst
  have key := QuadraticTransferReal.transfer (μ.withDensity β) ((μ.withDensity β₁).prod ρ) (fun p : G × G => p.2 * p.1) hm Φ hΦ
    (fun f => ∀ h ∈ H, ∀ g, f (h * g) = f g)
    (fun f hf hfH => by
      rw [QuadraticTransferReal.q1' μ ν ρ H β β₁ hinv hH hβ hβ₁ h1 f hf hfH, lintegral_prod (fun p : G × G => f (p.2 * p.1)) (hf.comp hm).aemeasurable])
    (fun h hh g => by simp only [hΦH h hh]) (fun h hh g => by simp only [hΦH h hh])
    (fun h hh g => by simp only [hΦH h hh]) (fun h hh g => by simp only [hΦH h hh])
    (fun h hh g => by simp only [hΦH h hh]) hi
  obtain ⟨hiB, he⟩ := key
  refine ⟨hiB.integral_prod_left, ?_⟩
  rw [he, integral_prod _ hiB]

end PositivityTheory.AdelicQuotientData

end
end

