module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KernelEqualitySecondOf
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKEq2

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem continuous_lastRow : Continuous (lastRow : GA E k → Fin k → Ad E) := by
  unfold lastRow
  refine continuous_pi fun c => continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact Continuous.matrix_elem Units.continuous_val i c
  · exact continuous_const

theorem lastRow_mir (p : GL (Fin k) E) (hp : IsMir (k - 1) p) (g : GA E k) :
    lastRow (ratGL E k p * g) = lastRow g := by
  funext c
  unfold lastRow
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have hrow : ∀ j, (ratGL E k p).val i j = (1 : Matrix (Fin k) (Fin k) (Ad E)) i j := by
      intro j
      have := hp i j (Or.inl (by omega))
      simp only [ratGL] at *
      simp [this, Matrix.one_apply]
    rw [Units.val_mul, Matrix.mul_apply]
    simp_rw [hrow]
    simp [Matrix.one_apply]
  · rfl

theorem measurable_sumF [Countable (RowT E k k)] {f : GA E k → ℂ} (hf : Continuous f)
    (hfin : ∀ g, {ξ : RowT E k k | f (ratGL E k (gam ξ) * g) ≠ 0}.Finite) : Measurable (sumF f) := by
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (RowT E k k)))
    (f := fun T g => ∑ ξ ∈ T, f (ratGL E k (gam ξ) * g)) (fun T => ?_) ?_
  · exact Finset.measurable_sum _ fun ξ _ => (hf.comp (continuous_const.mul continuous_id)).measurable
  · rw [tendsto_pi_nhds]
    intro g
    have e : ∀ T : Finset (RowT E k k), (hfin g).toFinset ⊆ T →
        ∑ ξ ∈ T, f (ratGL E k (gam ξ) * g) = sumF f g := by
      intro T hT
      unfold sumF
      rw [tsum_eq_sum (s := T)]
      intro b hb
      by_contra h
      exact hb (hT ((hfin g).mem_toFinset.2 h))
    exact tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨_, fun T hT => (e T hT).symm⟩)

theorem fin_bd {X : ℂ} {B C x y : ℝ} (hB : 0 ≤ B) (hx : 0 ≤ x) (hxy : x ≤ y)
    (h : ‖X‖ₑ ≤ ENNReal.ofReal B * ENNReal.ofReal (C * x)) : ‖X‖ ≤ B * max C 0 * y := by
  rw [← ENNReal.ofReal_mul hB, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff'] at h
  have h0 : C * x ≤ max C 0 * y :=
    calc C * x ≤ max C 0 * x := mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ ≤ max C 0 * y := mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
  have h1 : B * (C * x) ≤ B * max C 0 * y := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h0 hB
  have h2 : 0 ≤ B * max C 0 * y := mul_nonneg (mul_nonneg hB (le_max_right _ _)) (hx.trans hxy)
  rcases h with h | h <;> linarith [norm_nonneg X]

theorem enorm_conj' (z : ℂ) : ‖conj z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_conj]

end PKEq2

open PKEq2 in
theorem kernel_equality_second_of : D0 → N0 → H0 → ThetaDecaying → RowsInCompactSet → PoissonCutoffFormula → KEq2 := by
  intro hD0 hN0 hH0 hG4t hG5t hK12 E _ _ _ k hk ψ hψ S α' φ' hφ' U φ η s hcut hinv hcen
  obtain ⟨hDpos, hDmul, hDcont, hDrat, -, hDinv, -⟩ := hD0 E k
  obtain ⟨-, -, -, -, -, -, hcount, -, hperm, -⟩ := hN0 E k k hk le_rfl
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hinv' : ∀ γ g, φ (ratGL E k γ * g) = φ g := hinv
  have hinv2 : ∀ γ g, φ' (ratGL E k γ * g) = φ' g := hφ'.inv
  have hp1 : ∀ g : GA E k, (Dt g : ℂ) ^ (-(((k : ℂ) - k) / 2)) = 1 := fun g => by simp
  set V : (Fin k → Ad E) → XB E k := fun y => (η y : ℂ) • Rt E k (s y)⁻¹ φ with hV
  set F : GA E k → ℂ := fun g => (η (lastRow g) : ℂ) * φ (g * (s (lastRow g))⁻¹) with hF
  have hVc : Continuous V := hcut.contV
  have hVcpt : HasCompactSupport V := by
    have h1 : HasCompactSupport (fun y => (η y : ℂ)) := hcut.cpt.comp_left (g := Complex.ofReal) (by simp)
    exact h1.smul_right (f' := fun y => Rt E k (s y)⁻¹ φ)
  have hFV : ∀ x, F x = V (lastRow x) x := fun x => by simp [hF, hV]
  have hFc : Continuous F := by
    have : F = fun x => (V (lastRow x), x).1 (V (lastRow x), x).2 := funext hFV
    rw [this]
    exact continuous_eval.comp ((hVc.comp continuous_lastRow).prodMk continuous_id)
  have hFmir : ∀ p, IsMir (k - 1) p → ∀ x, F (ratGL E k p * x) = F x := by
    intro p hp x
    simp only [hF, lastRow_mir p hp, mul_assoc, hinv']
  have hsumInv : ∀ γ g, sumF F (ratGL E k γ * g) = sumF F g := by
    intro γ g
    obtain ⟨e, he⟩ := hperm γ
    unfold sumF
    rw [← e.tsum_eq (fun ξ => F (ratGL E k (gam ξ) * g))]
    refine tsum_congr fun ξ => ?_
    obtain ⟨p, hp, hpe⟩ := he ξ
    rw [← mul_assoc, ← map_mul, hpe, map_mul, mul_assoc, hFmir p hp]
  have hcpt : IsCompact (tsupport η) := hcut.cpt
  have hFzero : ∀ x, lastRow x ∉ tsupport η → F x = 0 := by
    intro x hx
    simp [hF, image_eq_zero_of_notMem_tsupport hx]
  have hfin : ∀ g, {ξ : RowT E k k | F (ratGL E k (gam ξ) * g) ≠ 0}.Finite := by
    intro g
    refine ((hG5t E k hk (tsupport η) hcpt).1 g).subset fun ξ hξ => ?_
    by_contra h
    exact hξ (hFzero _ h)
  have hSmeas : Measurable (sumF F) := measurable_sumF hFc hfin

  have hint : Integrable V (vecMeasure E (Fin k)) := hVc.integrable_of_hasCompactSupport hVcpt
  set W : XB E k := ∫ y, V y ∂vecMeasure E (Fin k) with hW
  have hI : ∀ g, (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂vecMeasure E (Fin k)) = W g := by
    intro g
    have := ContinuousLinearMap.integral_comp_comm (BoundedContinuousFunction.evalCLM ℂ g) hint
    rw [hW, ← BoundedContinuousFunction.evalCLM_apply (𝕜 := ℂ), ← this]
    simp [hV]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hp1, mul_one]
    exact hSmeas.mul (Complex.continuous_conj.comp φ'.continuous).measurable
  · simp only [hI]
    exact (W.continuous.mul (Complex.continuous_conj.comp φ'.continuous)).measurable
  · intro γ g
    simp only [hp1, mul_one]
    rw [hsumInv γ g, hinv2]
  · intro γ g
    simp only [mul_assoc, hinv', hinv2]
  · intro t g
    simp only [mul_assoc, hcen, hφ'.cen]
  · refine ⟨‖W‖ * ‖φ'‖, fun g => ?_⟩
    rw [hI, norm_mul, RCLike.norm_conj]
    exact mul_le_mul (W.norm_coe_le_norm g) (φ'.norm_coe_le_norm g) (norm_nonneg _) (norm_nonneg _)
  · intro M
    obtain ⟨B, hB⟩ := hVc.bounded_above_of_compact_support hVcpt
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    obtain ⟨C, hC⟩ := (hG4t E k hk φ' hφ'.dec).2 (tsupport η) hcpt (k * M + k) (by nlinarith)
    refine ⟨B * max C 0, fun g hg => ?_⟩
    have hFbd : ∀ x, ‖F x‖ₑ ≤ ENNReal.ofReal B * (tsupport η).indicator (fun _ => (1 : ℝ≥0∞)) (lastRow x) := by
      intro x
      by_cases hx : lastRow x ∈ tsupport η
      · rw [Set.indicator_of_mem hx, mul_one, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by rw [hFV]; exact ((V (lastRow x)).norm_coe_le_norm x).trans (hB _))
      · rw [Set.indicator_of_notMem hx, hFzero x hx]; simp
    set θ := ∑' ξ : RowT E k k, (tsupport η).indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) with hθ
    have hS : ‖sumF F g‖ₑ ≤ ENNReal.ofReal B * θ :=
      enorm_tsum_le_tsum_enorm.trans ((ENNReal.tsum_le_tsum fun ξ => hFbd _).trans_eq ENNReal.tsum_mul_left)
    have hx : Dt g ^ (-((k * M + k : ℕ) : ℝ) / k) ≤ (Dt g ^ M)⁻¹ := by
      have e : (-((k * M + k : ℕ) : ℝ) / k) = -(((M + 1 : ℕ) : ℝ)) := by push_cast; field_simp
      rw [e, Real.rpow_neg (hDpos g).le, Real.rpow_natCast]
      exact inv_anti₀ (pow_pos (hDpos g) _) (pow_le_pow_right₀ hg (by omega))
    refine fin_bd hB0 (Real.rpow_nonneg (hDpos g).le _) hx ?_
    simp only [hp1, mul_one]
    rw [enorm_mul, enorm_conj']
    calc ‖sumF F g‖ₑ * ‖φ' g‖ₑ ≤ (ENNReal.ofReal B * θ) * ‖φ' g‖ₑ := by gcongr
      _ = ENNReal.ofReal B * (θ * ‖φ' g‖ₑ) := mul_assoc _ _ _
      _ ≤ _ := by gcongr; exact hC g
  · obtain ⟨Cf, hCf, hft⟩ := hcut.ft
    obtain ⟨M, C, hC⟩ := (hG4t E k hk (fun x => φ' (invT x)) hφ'.dec').1 Cf hCf k le_rfl
    obtain ⟨C', hC'⟩ := hft M
    refine ⟨max C' 0 * max C 0, fun g _ => ?_⟩
    have hJ : ∀ (z : Fin k → Ad E), ‖∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) * ψ (∑ i, y i * z i) ∂vecMeasure E (Fin k)‖ₑ ≤
        ENNReal.ofReal (max C' 0) * ENNReal.ofReal (Cf.indicator (fun _ => ((1 + ‖fun i => pInf E (z i)‖) ^ M)⁻¹)
          fun i => pFin E (z i)) := by
      intro z
      have h := hC' z g
      by_cases hz : (fun i => pFin E (z i)) ∈ Cf
      · rw [Set.indicator_of_mem hz] at h ⊢
        rw [← ENNReal.ofReal_mul (le_max_right _ _), ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      · rw [Set.indicator_of_notMem hz] at h ⊢
        rw [← ofReal_norm, le_antisymm h (norm_nonneg _)]
        simp
    have hgg : invT (invT g) = g := ((hH0 E k).2.2.2.2.2.2 g g).2
    have hCg := hC (invT g)
    simp only [hgg, hDinv] at hCg
    have e1 : ((Dt g)⁻¹) ^ (-(k : ℝ) / k) = Dt g := by
      rw [neg_div, div_self hk0, Real.rpow_neg_one, inv_inv]
    rw [e1] at hCg
    have hK : (Dt g : ℂ) * sumF F g = _ := hK12 E k hk ψ hψ S U φ η s hcut hinv g
    rw [hp1, mul_one, ← mul_assoc, hK, add_mul, add_sub_cancel_left]
    refine fin_bd (le_max_right _ _) (hDpos g).le le_rfl ?_
    rw [enorm_mul, enorm_conj']
    calc _ ≤ (ENNReal.ofReal (max C' 0) * ∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (Cf.indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* (invT g).val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* (invT g).val) i))) * ‖φ' g‖ₑ := by
          gcongr
          exact enorm_tsum_le_tsum_enorm.trans ((ENNReal.tsum_le_tsum fun ξ => hJ _).trans_eq ENNReal.tsum_mul_left)
      _ = ENNReal.ofReal (max C' 0) * (_ * ‖φ' g‖ₑ) := mul_assoc _ _ _
      _ ≤ _ := by gcongr

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KernelLessSecondOf
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKLt2

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem lastRow_eq (hk : 1 ≤ k) (y : GA E k) (c : Fin k) :
    lastRow y c = y.val ⟨k - 1, by omega⟩ c := by
  unfold lastRow
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [if_pos (by simp; omega)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp only
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lastRow_mir (hk : 1 ≤ k) (p y : GA E k) (hp : Mir (k - 1) p) : lastRow (p * y) = lastRow y := by
  funext c
  rw [lastRow_eq hk, lastRow_eq hk, Units.val_mul, Matrix.mul_apply]
  have h1 : ∀ j, p.val ⟨k - 1, by omega⟩ j = (1 : Matrix (Fin k) (Fin k) (Ad E)) ⟨k - 1, by omega⟩ j :=
    fun j => hp _ _ (Or.inl le_rfl)
  simp only [h1, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp

omit [NumberField E] in
theorem isMir_emb {m : ℕ} (ιE : GL (Fin k) E →* GL (Fin m) E) (h : IsEmb ιE) (γ : GL (Fin k) E) :
    IsMir k (ιE γ) := by
  intro i c hic
  rw [h γ, embM, Matrix.of_apply, dite_eq_right (by omega)]

end PKLt2

theorem kernel_less_second_of : D0 → N0 → H0 → RowsInCompactSet → K1 → CornerEmbedding → TransformsEmbedding → FourierSeriesColumn → ShortRowsEmbedding → K6 → KLt2 := by
  intro hD0 hN0 hH0 hG5 hK1 hK5e hK5a hK5b hK5c hK6 E _ _ _ m k hk hkm ψ hψ S hS ι hι α α' φ' hsec U φ hprep
  obtain ⟨hDpos, hDmul, hDcont, hDrat, -⟩ := hD0 E k
  obtain ⟨hFgood, hpT, -, -, hsupp, hbd⟩ := hK5a E m k hk hkm ψ hψ ι hι φ hprep.good
  obtain ⟨C6, hC6c, hC6⟩ := hK6 E m k hk hkm ψ hψ S hS ι hι α (m ^ 3) U φ hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, hNlast⟩ := hN0 E k k hk le_rfl
  obtain ⟨hhtpos, -, -, -, hB5, -, -⟩ := hH0 E k
  obtain ⟨-, hdminpos, -⟩ := hK1 E m (by omega)
  obtain ⟨hιc, -, -, -, -, -, hιrat, -⟩ := (hK5e E m k hkm.le).2 ι hι
  obtain ⟨ιE, hιE⟩ := (hK5e E m k hkm.le).1 E
  have hrow : ∀ (g : GA E k) (ξ : RowT E k k),
      pT ψ k (m - k) (φ : GA E m → ℂ) (ι (ratGL E k (gam ξ) * g)) ≠ 0 →
      lastRow (ratGL E k (gam ξ) * g) ∈ C6 := by
    intro g ξ hne
    obtain ⟨p, hp, hw⟩ := hsupp _ hne
    have := hC6 _ hw
    rwa [PKLt2.lastRow_mir hk _ _ hp] at this
  have hfin : ∀ g : GA E k,
      {ξ : RowT E k k | colT ψ k (pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ))
        (ι (ratGL E k (gam ξ) * g)) ≠ 0}.Finite := by
    intro g
    exact ((hG5 E k hk C6 hC6c).1 g).subset fun ξ hξ => hrow g ξ (by rw [hpT]; exact hξ)
  have hsumF : ∀ g, sumF (fun g => pT ψ k (m - k) (φ : GA E m → ℂ) (ι g)) g =
      pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) := by
    intro g
    rw [hpT]
    exact (hK5b E m k hk hkm ψ hψ ι hι _ hFgood g).2 (hfin g)
  have hFb : ∀ x, ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) x‖ ≤ ‖φ‖ := fun x =>
    hbd (k + 1) x ‖φ‖ (by omega) (by omega) fun u _ => φ.norm_coe_le_norm _
  have hcpow : ∀ g : GA E k, ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖ = Dt g ^ (-(((m : ℝ) - k) / 2)) := by
    intro g
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hDpos g)]
    congr 1
    simp
  have hcont : Continuous fun g : GA E k => pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) *
      conj (φ' g) * (Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2)) := by
    refine ((hFgood.cont.comp hιc).mul (Complex.continuous_conj.comp φ'.continuous)).mul ?_
    exact (Complex.continuous_ofReal.comp hDcont).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g)
  simp_rw [hsumF]
  refine ⟨hcont.measurable, measurable_zero, ?_, fun _ _ => rfl, fun _ _ => rfl, ⟨0, fun _ => by simp⟩, ?_, ?_⟩
  · intro γ g
    dsimp only
    rw [map_mul ι, hιrat ιE hιE γ, hFgood.left _ (PKLt2.isMir_emb ιE hιE γ), hsec.inv γ g, hDmul, hDrat, one_mul]
  · intro M
    obtain ⟨C₂, hC₂⟩ := hsec.dec (k * M)
    obtain ⟨B, hB⟩ := hB5 C6 hC6c
    refine ⟨‖φ‖ * max C₂ 0 * max B 0 ^ (k * M), fun g hg => ?_⟩
    have hD := hDpos g
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hnorm : ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖ ≤ 1 := by
      rw [hcpow]
      apply Real.rpow_le_one_of_one_le_of_nonpos hg
      have : (k : ℝ) < m := by exact_mod_cast hkm
      linarith
    have hnn : 0 ≤ max B 0 ^ (k * M) * (Dt g ^ M)⁻¹ := by positivity
    by_cases hz : pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) = 0
    · rw [hz, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (le_max_right _ _)) (by positivity))
        (by positivity)
    obtain ⟨ξ, hξ⟩ : ∃ ξ : RowT E k k, pT ψ k (m - k) (φ : GA E m → ℂ) (ι (ratGL E k (gam ξ) * g)) ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      apply hz
      rw [← hsumF g, sumF]
      simp only [hcon, tsum_zero]
    have hlr := hrow g ξ hξ
    rw [hNlast ξ g] at hlr
    have hht := hB g ξ.1 ξ.2.1 hlr
    have hp := hhtpos g ξ.1 ξ.2.1
    have hht2 : ht g ξ.1 ≤ max B 0 / Dt g ^ ((k : ℝ)⁻¹) := by
      unfold ht
      gcongr
      exact hht.trans (le_max_left _ _)
    have hDk : (Dt g ^ ((k : ℝ)⁻¹)) ^ (k * M) = Dt g ^ M := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul,
        Real.rpow_natCast]
    have hpow : ht g ξ.1 ^ (k * M) ≤ max B 0 ^ (k * M) * (Dt g ^ M)⁻¹ := by
      calc ht g ξ.1 ^ (k * M) ≤ (max B 0 / Dt g ^ ((k : ℝ)⁻¹)) ^ (k * M) := pow_le_pow_left₀ hp.le hht2 _
        _ = _ := by rw [div_pow, hDk, div_eq_mul_inv]
    have hφ' : ‖φ' g‖ ≤ max C₂ 0 * (max B 0 ^ (k * M) * (Dt g ^ M)⁻¹) :=
      (hC₂ g ξ.1 ξ.2.1).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    calc ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ * ‖φ' g‖ * ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖
        ≤ ‖φ‖ * (max C₂ 0 * (max B 0 ^ (k * M) * (Dt g ^ M)⁻¹)) * 1 :=
          mul_le_mul (mul_le_mul (hFb _) hφ' (norm_nonneg _) (norm_nonneg _)) hnorm (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans hφ'))
      _ = _ := by ring
  · obtain ⟨C5, hC5⟩ := hK5c E m k hk hkm ι hι
    obtain ⟨Cφ, hCφ⟩ := hprep.dec
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    have hkm' : (k : ℝ) < m := by exact_mod_cast hkm
    have hm0 : (m : ℝ) ≠ 0 := by linarith
    have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
    have he : (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ) = (m : ℝ) ^ 2 / ((m : ℝ) - 1) := by
      push_cast
      field_simp
      ring
    have hmle : (m : ℝ) ≤ (m : ℝ) ^ 2 / ((m : ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have hexp : 0 ≤ (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ) + -(((m : ℝ) - k) / 2) := by
      rw [he]
      linarith
    refine ⟨max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖, fun g hg => ?_⟩
    have hD := hDpos g
    have hFs : ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ ≤ max Cφ 0 * (max C5 0 ^ (m ^ 3) *
        Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ))) := by
      refine hbd (k + 1) (ι g) _ (by omega) (by omega) fun u hu => ?_
      have hdm := (hC5 g u).2 hu
      have hpos := hdminpos (u * ι g)
      have hw0 : 0 ≤ wt (m ^ 3) (u * ι g) := pow_nonneg (le_min zero_le_one hpos.le) _
      calc ‖φ (u * ι g)‖ ≤ Cφ * wt (m ^ 3) (u * ι g) := hCφ _
        _ ≤ max Cφ 0 * wt (m ^ 3) (u * ι g) := mul_le_mul_of_nonneg_right (le_max_left _ _) hw0
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          unfold wt
          calc min 1 (dmin (u * ι g)) ^ (m ^ 3)
              ≤ (max C5 0 * Dt g ^ (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹)) ^ (m ^ 3) :=
                pow_le_pow_left₀ (le_min zero_le_one hpos.le) ((min_le_right _ _).trans (hdm.trans
                  (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hD.le _)))) _
            _ = _ := by rw [mul_pow, ← Real.rpow_natCast (Dt g ^ _), ← Real.rpow_mul hD.le]
    have hrp : Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ)) * Dt g ^ (-(((m : ℝ) - k) / 2)) ≤ 1 := by
      rw [← Real.rpow_add hD]
      exact Real.rpow_le_one hD.le hg.le hexp
    have hφ'b : ‖φ' g‖ ≤ ‖φ'‖ := φ'.norm_coe_le_norm g
    have hA : 0 ≤ max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg (le_max_right _ _) _)) (norm_nonneg _)
    rw [Pi.zero_apply, sub_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le, norm_mul, norm_mul,
      RCLike.norm_conj, hcpow, mul_comm _ (Dt g)]
    apply mul_le_mul_of_nonneg_left _ hD.le
    calc ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ * ‖φ' g‖ * Dt g ^ (-(((m : ℝ) - k) / 2))
        ≤ max Cφ 0 * (max C5 0 ^ (m ^ 3) * Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ))) *
            ‖φ'‖ * Dt g ^ (-(((m : ℝ) - k) / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hD.le _)
          exact mul_le_mul hFs hφ'b (norm_nonneg _) ((norm_nonneg _).trans hFs)
      _ = max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ * (Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ)) *
            Dt g ^ (-(((m : ℝ) - k) / 2))) := by ring
      _ ≤ max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ * 1 := mul_le_mul_of_nonneg_left hrp hA
      _ = _ := mul_one _

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KuOf
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

theorem ku_of : jumpWindows.G5 → D0 → KU := by
  intro hG hD E _ _ _ k ψ hψ φ u hφ h1
  obtain ⟨-, -, -, hW⟩ := hG E k ψ hψ
  have hWc : Continuous (Wh ψ φ) := (hW φ hφ).1
  obtain ⟨hpos, hmul, hcont, -⟩ := hD E k
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hmul 1 1
    rw [show (1 : GA E k) * 1 = 1 from mul_one 1] at h
    exact mul_left_cancel₀ (hpos 1).ne' (h.symm.trans (mul_one _).symm)
  set F : GA E k → ℂ := fun c => conj (Wh ψ φ c) * (Dt c : ℂ) ^ ((u : ℂ) * Complex.I) with hF
  have hDc : Continuous fun c : GA E k => (Dt c : ℂ) := Complex.continuous_ofReal.comp hcont
  have hFc : Continuous F := (Complex.continuous_conj.comp hWc).mul
    (hDc.cpow continuous_const fun c => Complex.ofReal_mem_slitPlane.2 (hpos c))
  have hF1 : F 1 = 1 := by simp [F, h1, hD1]
  refine ⟨{c | Dt c ∈ Set.Ioo (1 / 2 : ℝ) 2} ∩ {c | 0 < (F c).re}, ?_, ?_⟩
  · apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.preimage hcont).inter (isOpen_lt continuous_const (Complex.continuous_re.comp hFc))
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, hD1, hF1]
      norm_num
  · rintro c ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha.le, hb.le, hc⟩

end PositivityTheory.AdelicQuotientData

end
end

