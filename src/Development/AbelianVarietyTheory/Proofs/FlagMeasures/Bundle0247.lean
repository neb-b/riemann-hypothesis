module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Formalism.LocalRingCardinality.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProdPowLeOfMomentsMassLeOne
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem lintegral_prod_pow_le_of_moments : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (ρ : Fin r → Ω → ℝ) (Ph : Ω → ℝ) (Rr : ℝ) (s : Finset (Fin r)), (∀ a, AEMeasurable (ρ a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 ≤ ρ a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν ≤ 1 → 1 ≤ Rr → (∀ a, ∫⁻ x, ENNReal.ofReal (ρ a x ^ (2 * (r * q)) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q)))) → ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q))) := by
  classical
  intro Ω _ ν r q ρ Ph Rr s hρm hρ0 hPm hP0 hP1 hR hbd
  have hR0 : (0:ℝ) ≤ Rr := le_trans zero_le_one hR
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
    subst hs
    simpa using hP1
  · set N : ℕ := 2 * (r * q) with hN
    let u : Fin r → Ω → ℝ := fun a x => if a ∈ s then ρ a x else Rr
    have hrR : (0:ℝ) < r := by exact_mod_cast hr
    have hr0 : r ≠ 0 := Nat.pos_iff_ne_zero.mp hr
    have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x)
        ≤ ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) := by
      have hall : ∀ᵐ x ∂ν, ∀ a, 0 ≤ ρ a x := ae_all_iff.mpr hρ0
      filter_upwards [hall] with x hx
      have hu0 : ∀ a, 0 ≤ u a x := fun a => by
        by_cases ha : a ∈ s <;> simp [u, ha, hx a, hR0]
      have h1 : (∏ a ∈ s, ρ a x) ^ (2 * q) ≤ ∏ a : Fin r, u a x ^ (2 * q) := by
        have : (∏ a ∈ s, ρ a x) ^ (2 * q)
            = ∏ a : Fin r, (if a ∈ s then ρ a x ^ (2 * q) else 1) := by
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pow]
        rw [this]
        apply Finset.prod_le_prod₀
        · intro a _
          by_cases ha : a ∈ s
          · simp [ha, pow_nonneg (hx a)]
          · simp [ha]
        · intro a _
          by_cases ha : a ∈ s
          · simp [u, ha]
          · simp [u, ha, one_le_pow₀ hR]
      have h2 : ∏ a : Fin r, u a x ^ (2 * q) ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N := by
        have hw : ∑ _a : Fin r, (r:ℝ)⁻¹ = 1 := by
          simp [Finset.card_univ, Fintype.card_fin, hrR.ne']
        have key := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin r))
          (fun _ => (r:ℝ)⁻¹) (fun a => (u a x ^ (2 * q)) ^ r)
          (fun _ _ => inv_nonneg.mpr hrR.le) hw (fun a _ => pow_nonneg (pow_nonneg (hu0 a) _) _)
        have e1 : ∀ a, ((u a x ^ (2 * q)) ^ r) ^ ((r:ℝ)⁻¹) = u a x ^ (2 * q) := fun a =>
          Real.pow_rpow_inv_natCast (pow_nonneg (hu0 a) _) hr0
        have e2 : ∀ a, (u a x ^ (2 * q)) ^ r = u a x ^ N := fun a => by
          rw [← pow_mul, hN]; congr 1; ring
        simp only [e1] at key
        simp only [e2] at key
        exact key
      have hP : 0 ≤ Ph x := hP0 x
      have h3 : (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x
          ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x) := by
        calc (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x
            ≤ (∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N) * Ph x :=
              mul_le_mul_of_nonneg_right (h1.trans h2) hP
          _ = ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x) := by
              rw [Finset.sum_mul]; congr 1; ext a; ring
      calc ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x)
          ≤ ENNReal.ofReal (∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x)) :=
            ENNReal.ofReal_le_ofReal h3
        _ = ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            · congr 1; ext a
              rw [ENNReal.ofReal_mul (inv_nonneg.mpr hrR.le)]
            · intro a _
              exact mul_nonneg (inv_nonneg.mpr hrR.le) (mul_nonneg (pow_nonneg (hu0 a) _) hP)
    have hum : ∀ a, AEMeasurable (u a) ν := fun a => by
      by_cases ha : a ∈ s
      · simpa [u, ha] using hρm a
      · simp only [u, ha, if_false]; exact aemeasurable_const
    have hint : ∀ a, ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ N) := by
      intro a
      by_cases ha : a ∈ s
      · simpa [u, ha] using hbd a
      · simp only [u, ha, if_false]
        have hRN : (0:ℝ) ≤ Rr ^ N := pow_nonneg hR0 _
        simp_rw [ENNReal.ofReal_mul hRN]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc ENNReal.ofReal (Rr ^ N) * ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν
            ≤ ENNReal.ofReal (Rr ^ N) * 1 := by gcongr
          _ = ENNReal.ofReal (Rr ^ N) := mul_one _
    calc ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν
        ≤ ∫⁻ x, ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) ∂ν :=
          lintegral_mono_ae hpt
      _ = ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν := by
          rw [lintegral_finsetSum']
          · congr 1; ext a
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          · intro a _
            exact (((hum a).pow_const N).mul hPm).ennreal_ofReal.const_mul _
      _ ≤ ∑ _a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (Rr ^ N) := by
          gcongr with a
          exact hint a
      _ = ENNReal.ofReal (Rr ^ N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
          have : (r : ℝ≥0∞) * ENNReal.ofReal ((r:ℝ)⁻¹) = 1 := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg r),
              mul_inv_cancel₀ hrR.ne', ENNReal.ofReal_one]
          rw [this, one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTailBoundOfMoments
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp.TailTwo

theorem cheb_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (l : X → ℝ) (f : X → ℝ≥0∞) (E : Set X)
    (hE : MeasurableSet E) (T : ℝ) (hT : 0 < T) (hl : ∀ x ∈ E, T ≤ l x) (n : ℕ) :
    ∫⁻ x in E, f x ∂ν ≤ ENNReal.ofReal ((T ^ n)⁻¹) * ∫⁻ x, ENNReal.ofReal (l x ^ n) * f x ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (setLIntegral_mono' hE fun x hx => ?_) (setLIntegral_le_lintegral E _)
  have hTn : 0 < T ^ n := pow_pos hT n
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hTn.le)]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hTn]
  exact pow_le_pow_left₀ hT.le (hl x hx) n

theorem meas_closed (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ) (hg : ContinuousOn g (GG k r)) (t : Set ℝ) (ht : IsClosed t) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} := by
  obtain ⟨u, hu, h⟩ := (continuousOn_iff_isClosed.1 hg) t ht
  have h1 : MeasurableSet (α := Mt k r) u := IsClosed.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

theorem meas_open (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ) (hg : ContinuousOn g (GG k r)) (t : Set ℝ) (ht : IsOpen t) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} := by
  obtain ⟨u, hu, h⟩ := continuousOn_iff'.1 hg t ht
  have h1 : MeasurableSet (α := Mt k r) u := IsOpen.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

end GlobalTheory.Amp.TailTwo

namespace GlobalTheory.Amp.TailTwo

theorem tailBd_of_moments : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r)) (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (q : ℕ) (H₁ : ℝ), inWb k r z → 0 < H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → (∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lA k r z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) → TailBd z νS Φ q H₁ := by
  intro k r Wp _ _ _ z νS Φ q H₁ _ hH hG _ hM hI la hla
  set T : ℝ := la * H₁ with hTdef
  have hT : 0 < T := mul_pos hla hH
  set f : Mt k r → ℝ≥0∞ := fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 with hf
  set A : Fin (r + 1) → Set (Mt k r) := fun a =>
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Ici T} with hA
  set B : Fin (r + 1) → Set (Mt k r) := fun a =>
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Ioi 0} ∩
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Iic T⁻¹} with hB
  set N : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hN
  have hGc : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have hNm : MeasurableSet N := hGc.compl
  have hAm : ∀ a, MeasurableSet (A a) := fun a =>
    meas_closed k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isClosed_Ici
  have hBm : ∀ a, MeasurableSet (B a) := fun a =>
    (meas_open k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isOpen_Ioi).inter
      (meas_closed k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isClosed_Iic)
  set U : Set (Mt k r) := N ∪ ⋃ a, (A a ∪ B a) with hU
  have hUm : MeasurableSet U := hNm.union (MeasurableSet.iUnion fun a => (hAm a).union (hBm a))
  have hsub : {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹} ⊆ U := by
    rintro x ⟨a, ha⟩
    by_cases hx : Matrix.of x ∈ GG k r
    · refine Or.inr (Set.mem_iUnion.2 ⟨a, ?_⟩)
      rcases le_max_iff.1 ha with h | h
      · exact Or.inl ⟨hx, h⟩
      · have hpos : 0 < lA k r z (Matrix.of x) a := inv_pos.1 (lt_of_lt_of_le hT h)
        refine Or.inr ⟨⟨hx, hpos⟩, hx, ?_⟩
        show lA k r z (Matrix.of x) a ≤ T⁻¹
        exact (le_inv_comm₀ hT hpos).1 h
    · exact Or.inl hx
  have hc : ∀ a, ∫⁻ x in A a ∪ B a, f x ∂νS ≤ 2 * (ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ) := by
    intro a
    have key : ENNReal.ofReal ((T ^ (2 * q))⁻¹) * (ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) =
        ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Real.rpow_neg hla.le, hTdef, mul_pow]
      have : la ^ (2 * (q : ℝ)) = la ^ (2 * q) := by
        rw [← Real.rpow_natCast]; push_cast; ring_nf
      rw [this]
      have h1 : H₁ ^ (2 * q) ≠ 0 := pow_ne_zero _ hH.ne'
      field_simp
    have hA' : ∫⁻ x in A a, f x ∂νS ≤ ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      refine (cheb_le νS (fun x => lA k r z (Matrix.of x) a) f (A a) (hAm a) T hT (fun x hx => hx.2) (2 * q)).trans ?_
      rw [← key]
      gcongr
      exact hM a
    have hB' : ∫⁻ x in B a, f x ∂νS ≤ ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      refine (cheb_le νS (fun x => (lA k r z (Matrix.of x) a)⁻¹) f (B a) (hBm a) T hT (fun x hx => ?_) (2 * q)).trans ?_
      · have hpos : 0 < lA k r z (Matrix.of x) a := hx.1.2
        exact (le_inv_comm₀ hT hpos).2 hx.2.2
      · rw [← key]
        gcongr
        exact hI a
    refine (lintegral_union_le _ _ _).trans ?_
    exact (add_le_add hA' hB').trans (le_of_eq (two_mul _).symm)
  calc ∫⁻ x, Set.indicator {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹}
          (fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂νS
        ≤ ∫⁻ x, U.indicator f x ∂νS := lintegral_mono fun x => Set.indicator_le_indicator_of_subset hsub (fun _ => by simp) x
    _ = ∫⁻ x in U, f x ∂νS := lintegral_indicator hUm _
    _ ≤ ∫⁻ x in N, f x ∂νS + ∫⁻ x in ⋃ a, (A a ∪ B a), f x ∂νS := lintegral_union_le _ _ _
    _ ≤ 0 + ∑ a : Fin (r + 1), ∫⁻ x in A a ∪ B a, f x ∂νS := by
        gcongr
        · exact (setLIntegral_measure_zero _ _ hG).le
        · exact (lintegral_iUnion_le _ _).trans (le_of_eq (tsum_fintype _))
    _ ≤ ∑ _a : Fin (r + 1), 2 * (ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ) := by
        rw [zero_add]; exact Finset.sum_le_sum fun a _ => hc a
    _ ≤ ENNReal.ofReal (2 * (2 * r + 2 : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
          ENNReal.ofReal_mul (by positivity)]
        gcongr ?_ * _ * _
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        nlinarith

end GlobalTheory.Amp.TailTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.SnMass.SkewVol

section Fixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem differentIdeal_eq_map_of_unramified (hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)) :
    differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hu, Ideal.top_mul]

theorem dInv_eq_inv_coe (K : Type) [Field K] [NumberField K] (j : ℕ) :
    GlobalTheory.SgGlob.dInv K j = ((↑(differentIdeal ℤ (𝓞 K) ^ j) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [GlobalTheory.SgGlob.dInv, FractionalIdeal.coeIdeal_pow, inv_pow]

theorem algebraMap_mem_inv_map_iff (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (y : F) :
    algebraMap F E y ∈ ((↑(I.map (algebraMap (𝓞 F) (𝓞 E))) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ ↔
      y ∈ ((↑I : FractionalIdeal (𝓞 F)⁰ F))⁻¹ := by
  have hIE : I.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hIE),
    FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI)]
  have key : ∀ a : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) =
      algebraMap F E (algebraMap (𝓞 F) F a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  constructor
  · intro h z hz
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have h1 := h (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a))
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mem_map_of_mem _ ha, rfl⟩)
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [key, ← map_mul] at hc
    have hint : IsIntegral ℤ (y * algebraMap (𝓞 F) F a) := by
      rw [← isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom) (algebraMap F E).injective]
      show IsIntegral ℤ (algebraMap F E (y * algebraMap (𝓞 F) F a))
      rw [← hc]
      exact c.2
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, hint⟩, rfl⟩
  · intro h z hz
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    let T : Ideal (𝓞 E) := Submodule.comap
      ((LinearMap.mulLeft (𝓞 E) (algebraMap F E y)) ∘ₗ Algebra.linearMap (𝓞 E) E)
      ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
    have hle : I.map (algebraMap (𝓞 F) (𝓞 E)) ≤ T := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
        (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩))
      show algebraMap F E y * algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) ∈
        (1 : FractionalIdeal (𝓞 E)⁰ E)
      rw [key, ← map_mul, ← hc]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨algebraMap (𝓞 F) (𝓞 E) c, key c⟩
    exact hle hb

theorem cm_sigma_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

theorem mem_range_of_cm_fixed {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hne := cm_sigma_ne_id h
  have hxS : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
  have hle : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) ≤ 2 := by
    rw [← Subalgebra.finrank_toSubmodule, ← h.2.2.1]
    exact Submodule.finrank_le _
  have hpos : 0 < Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) := Module.finrank_pos
  have hS : AlgHom.equalizer σ (AlgHom.id F E) = ⊥ := by
    rcases (by omega : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 1 ∨
        Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 2) with h1 | h2
    · exact Subalgebra.finrank_eq_one_iff.1 h1
    · exfalso
      apply hne
      have htop : Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [Subalgebra.finrank_toSubmodule, h2, h.2.2.1])
      ext z
      have hz : z ∈ Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) :=
        htop ▸ Submodule.mem_top
      exact hz
  rw [hS] at hxS
  exact Algebra.mem_bot.1 hxS

theorem imV_eq_zero_iff {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : imV x = 0 ↔ σ x = x := by
  constructor
  · intro hx
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    let w : InfinitePlace E := InfinitePlace.mk τ
    have him : (w.embedding x).im = 0 := congrFun hx w
    apply w.embedding.injective
    rw [h.2.2.2]
    exact Complex.conj_eq_iff_im.2 him
  · intro hx
    funext w
    show (w.embedding x).im = 0
    have := h.2.2.2 w.embedding x
    rw [hx] at this
    exact Complex.conj_eq_iff_im.1 this.symm

end Fixed

theorem mem_dInv_imV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) →
    ∀ (j : ℕ) (x : E), (x ∈ GlobalTheory.SgGlob.dInv E j ∧ imV x = 0) ↔ ∃ y ∈ GlobalTheory.SgGlob.dInv F j, algebraMap F E y = x := by
  intro F E _ _ _ _ _ σ h hu j x
  have hIne : differentIdeal ℤ (𝓞 F) ^ j ≠ ⊥ := pow_ne_zero _ differentIdeal_ne_bot
  have hE : GlobalTheory.SgGlob.dInv E j = ((↑((differentIdeal ℤ (𝓞 F) ^ j).map (algebraMap (𝓞 F) (𝓞 E))) :
      FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
    rw [dInv_eq_inv_coe, differentIdeal_eq_map_of_unramified hu, Ideal.map_pow]
  constructor
  · rintro ⟨hx, him⟩
    obtain ⟨y, rfl⟩ := mem_range_of_cm_fixed h ((imV_eq_zero_iff h x).1 him)
    refine ⟨y, ?_, rfl⟩
    rw [dInv_eq_inv_coe]
    rw [hE] at hx
    exact (algebraMap_mem_inv_map_iff _ hIne y).1 hx
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, (imV_eq_zero_iff h _).2 (σ.commutes y)⟩
    rw [hE]
    rw [dInv_eq_inv_coe] at hy
    exact (algebraMap_mem_inv_map_iff _ hIne y).2 hy

end GlobalTheory.SnMass.SkewVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledSkewLatticeFundamentalDomainOfImaginaryPar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

open scoped Pointwise

namespace GlobalTheory.SnMass.SkewDom

theorem im_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (w : InfinitePlace E) (z : E) :
    (w.embedding (σ z)).im = -(w.embedding z).im := by
  rw [h.2.2.2 w.embedding z]; simp

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply w.embedding.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem mem_skewLat_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : ∀ x ∈ I, σ x ∈ I)
    {θ : 𝓞 E} (hθ : (θ : E) + σ θ = 1) (c : ℝ) (z : InfinitePlace E → ℝ) :
    z ∈ (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) ↔
      ∃ b ∈ {b | ∃ x ∈ I, imV x = b}, z = (2 * c) • b := by
  change (∃ y ∈ I, (σ : E →+* E) y = -y ∧ ∀ w, z w = c * (w.embedding y).im) ↔ _
  simp only [AlgHom.coe_toRingHom]
  constructor
  · rintro ⟨y, hy, hs, hz⟩
    have hθy : (θ : E) * y ∈ I := by
      have := (I : Submodule (𝓞 E) E).smul_mem θ hy
      rwa [Algebra.smul_def] at this
    refine ⟨imV ((θ : E) * y), ⟨(θ : E) * y, hθy, rfl⟩, ?_⟩
    funext w
    have hy2 : y = (θ : E) * y - σ ((θ : E) * y) := by
      rw [map_mul, hs]; linear_combination (-y) * hθ
    rw [hz w, Pi.smul_apply, smul_eq_mul, imV]
    conv_lhs => rw [hy2]
    rw [map_sub, Complex.sub_im, im_sigma hcm]; ring
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x - σ x, (I : Submodule (𝓞 E) E).sub_mem hx (hI x hx), ?_, fun w => ?_⟩
    · rw [map_sub, sigma_sigma hcm]; ring
    · rw [Pi.smul_apply, smul_eq_mul, imV, map_sub, Complex.sub_im, im_sigma hcm]; ring

theorem skewDom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, σ x ∈ I) → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ (c : ℝ), 0 < c → ∀ (D : Set (InfinitePlace E → ℝ)) (m : ℝ≥0∞), MeasurableSet D → (∀ y, ∃! l, l ∈ {b | ∃ x ∈ I, imV x = b} ∧ y + l ∈ D) → volume D = m → HasDom volume (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal ((2 * c) ^ Fintype.card (InfinitePlace E)) * m) := by
  intro F E _ _ _ _ _ σ hcm I hI θ hθ c hc D m hD hU hm
  have hmem := mem_skewLat_iff hcm hI hθ c
  have h2c : (2 * c) ≠ 0 := by positivity
  refine ⟨(2 * c) • D, hD.const_smul₀ _, fun v => ?_, ?_⟩
  · obtain ⟨l, ⟨hl, hlD⟩, hu⟩ := hU ((2 * c)⁻¹ • v)
    refine ⟨(2 * c) • l, ⟨(hmem _).2 ⟨l, hl, rfl⟩, ?_⟩, ?_⟩
    · refine Set.mem_smul_set.2 ⟨_, hlD, ?_⟩
      rw [smul_add, smul_inv_smul₀ h2c]
    · rintro l' ⟨hl', hl'D⟩
      obtain ⟨b, hb, rfl⟩ := (hmem _).1 hl'
      obtain ⟨d, hd, hdv⟩ := Set.mem_smul_set.1 hl'D
      have hbd : (2 * c)⁻¹ • v + b = d := by
        rw [← inv_smul_smul₀ h2c d, hdv, smul_add, inv_smul_smul₀ h2c]
      rw [hu b ⟨hb, hbd ▸ hd⟩]
  · rw [Measure.addHaar_smul, hm, Module.finrank_fintype_fun_eq_card, abs_of_pos (by positivity)]

end GlobalTheory.SnMass.SkewDom
end

