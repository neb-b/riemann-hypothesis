module

public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0002
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.CyclotomicNorms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
public import Formalism.LocalToGlobal.HermitianForms.Bundle0003
public import Formalism.LocalToGlobal.Columns.RecLevelLocT

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem zsumR_eq_sum_toFinset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℝ)
    (h : (zerosIn χ t T).Finite) :
    zsumR χ t T f = ∑ ρ ∈ h.toFinset, (zmult χ ρ : ℝ) * f ρ := by
  unfold zsumR
  exact finsum_mem_eq_finite_toFinset_sum _ h


open Classical in
theorem sum_indicator_le_zsumR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (S : Finset ℂ)
    (h : (zerosIn χ t T).Finite) :
    ∑ ρ ∈ S, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ t T then 1 else 0) ≤ zsumR χ t T (fun _ => 1) := by
  rw [zsumR_eq_sum_toFinset χ t T _ h]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact h.mem_toFinset.mpr hx.2
  · intro x _ _
    exact Nat.cast_nonneg _


open Classical in
theorem recip_le_sum_windows {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) (ρ : ℂ)
    (hρ : ρ ∈ zerosIn χ 0 T) :
    (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0 : ℝ) ≤
      ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) +
        (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ (j : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (j : ℝ) 1 then 1 else 0) +
      (if ρ ∈ zerosIn χ (-(j : ℝ)) 1 then 1 else 0)) := by
    intro j
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg j))
    apply add_nonneg <;> split_ifs <;> norm_num
  by_cases h1 : 1 < |ρ.im|
  · rw [if_pos h1]
    obtain ⟨hre0, hre1, hT, hL⟩ := hρ
    rw [sub_zero] at hT
    have hk1 : 1 ≤ ⌊|ρ.im|⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact h1.le)
    have hkT : ⌊|ρ.im|⌋₊ ≤ ⌊T⌋₊ := Nat.floor_mono hT
    have hkle : (⌊|ρ.im|⌋₊ : ℝ) ≤ |ρ.im| := Nat.floor_le (abs_nonneg _)
    have hklt : |ρ.im| < ⌊|ρ.im|⌋₊ + 1 := Nat.lt_floor_add_one _
    have hkpos : (0 : ℝ) < ⌊|ρ.im|⌋₊ := by exact_mod_cast hk1
    have hind : (1 : ℝ) ≤ (if ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 then 1 else 0) +
        (if ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 then 1 else 0) := by
      rcases le_or_gt 0 ρ.im with him | him
      · have hmem : ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 := by
          refine ⟨hre0, hre1, ?_, hL⟩
          have hab : |ρ.im| = ρ.im := abs_of_nonneg him
          rw [abs_le]
          constructor <;> linarith
        rw [if_pos hmem]
        split_ifs <;> norm_num
      · have hmem : ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 := by
          refine ⟨hre0, hre1, ?_, hL⟩
          have hab : |ρ.im| = -ρ.im := abs_of_neg him
          rw [abs_le]
          constructor <;> linarith
        rw [if_pos hmem]
        split_ifs <;> norm_num
    calc 1 / ‖ρ‖ ≤ ((⌊|ρ.im|⌋₊ : ℕ) : ℝ)⁻¹ := by
          rw [one_div]
          exact inv_anti₀ hkpos (hkle.trans (Complex.abs_im_le_norm ρ))
      _ ≤ ((⌊|ρ.im|⌋₊ : ℕ) : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 then 1 else 0) +
          (if ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 then 1 else 0)) :=
          le_mul_of_one_le_right (inv_nonneg.mpr hkpos.le) hind
      _ ≤ _ := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_Icc.mpr ⟨hk1, hkT⟩)
  · rw [if_neg h1]
    exact Finset.sum_nonneg (fun j _ => hnn j)

theorem zsumR_recip_le : GlobalTheory.Mem.An.ZeroCount → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T → zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) ≤ C * Real.log (q * T) ^ 2 ∧ zsumR χ 0 1 (fun _ => 1) ≤ C * Real.log (3 * q) := by
  classical
  rintro ⟨C0, hC0⟩
  set D := max C0 0 with hD
  have hD0 : 0 ≤ D := le_max_right _ _
  have hZ : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
      zsumR χ t 1 (fun _ => 1) ≤ D * Real.log (q * (|t| + 2)) := by
    intro q _ χ hχ t
    refine (hC0 q χ hχ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg ?_))
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    nlinarith [abs_nonneg t]
  refine ⟨12 * D, ?_⟩
  intro q _ χ hχ T hT
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine ⟨?_, ?_⟩
  · obtain ⟨hfin, _⟩ := _root_.GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult q χ 0 T
    have hfin' : ∀ t : ℝ, (zerosIn χ t 1).Finite := fun t => (_root_.GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult q χ t 1).1
    have hN1 : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; linarith)
    have hNT : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
    have hNpos : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast hN1
    rw [zsumR_eq_sum_toFinset χ 0 T _ hfin]
    have hsplit : ∀ k : ℕ, ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ((k : ℝ)⁻¹ *
        ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0))) =
        (k : ℝ)⁻¹ * (∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) +
          ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
      intro k
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      ring
    have hLA : 0 ≤ Real.log (q * (T + 2)) := Real.log_nonneg (by nlinarith)
    calc ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0)
        ≤ ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ *
            ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          exact mul_le_mul_of_nonneg_left (recip_le_sum_windows χ T ρ (hfin.mem_toFinset.mp hρ))
            (Nat.cast_nonneg _)
      _ = ∑ k ∈ Icc 1 ⌊T⌋₊, ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ((k : ℝ)⁻¹ *
            ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0))) := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ * (2 * D * Real.log (q * (T + 2))) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' := Finset.mem_Icc.mp hk
          have hkT : (k : ℝ) ≤ T := (Nat.cast_le.mpr hk'.2).trans hNT
          rw [hsplit k]
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg k))
          have e1 := (sum_indicator_le_zsumR χ (k : ℝ) 1 hfin.toFinset (hfin' _)).trans (hZ q χ hχ k)
          have e2 := (sum_indicator_le_zsumR χ (-(k : ℝ)) 1 hfin.toFinset (hfin' _)).trans
            (hZ q χ hχ (-(k : ℝ)))
          rw [abs_neg] at e2
          have hlog : Real.log (q * (|(k : ℝ)| + 2)) ≤ Real.log (q * (T + 2)) := by
            apply Real.log_le_log (by nlinarith [abs_nonneg (k : ℝ)])
            rw [abs_of_nonneg (Nat.cast_nonneg k)]
            nlinarith
          have := mul_le_mul_of_nonneg_left hlog hD0
          linarith
      _ = 2 * D * Real.log (q * (T + 2)) * ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ ≤ 2 * D * Real.log (q * (T + 2)) * (1 + Real.log T) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) hLA)
          have h := harmonic_le_one_add_log ⌊T⌋₊
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
          have := Real.log_le_log hNpos hNT
          linarith
      _ ≤ 12 * D * Real.log (q * T) ^ 2 := by
          have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
          have hu : Real.log 2 ≤ Real.log (q * T) := Real.log_le_log (by norm_num) hqT
          have hl2 := Real.log_two_gt_d9
          have hA : Real.log (q * (T + 2)) ≤ 2 * Real.log (q * T) := by
            have h := Real.log_le_log (by nlinarith : (0 : ℝ) < q * (T + 2))
              (by nlinarith : (q : ℝ) * (T + 2) ≤ 2 * (q * T))
            rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (by nlinarith : (0 : ℝ) < q * T))] at h
            linarith
          have hB : 1 + Real.log T ≤ 3 * Real.log (q * T) := by
            have := Real.log_le_log (by linarith : (0 : ℝ) < T) (by nlinarith : T ≤ (q : ℝ) * T)
            linarith
          have hB0 : 0 ≤ 1 + Real.log T := by
            have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
            linarith
          have h := mul_le_mul hA hB hB0 (by linarith)
          have h' := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * D)
          calc 2 * D * Real.log (q * (T + 2)) * (1 + Real.log T)
              = 2 * D * (Real.log (q * (T + 2)) * (1 + Real.log T)) := by ring
            _ ≤ 2 * D * (2 * Real.log (q * T) * (3 * Real.log (q * T))) := h'
            _ = 12 * D * Real.log (q * T) ^ 2 := by ring
  · have h := hZ q χ hχ 0
    rw [abs_zero, zero_add] at h
    refine h.trans ?_
    have h1 : Real.log (q * 2) ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
    have h2 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 hD0, mul_nonneg hD0 h2]

end GlobalTheory.Mem.An
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitary
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.ChiLaws

theorem infDiag_mul_finPart {L : Type} [Field L] [NumberField L] (k : Lˣ) :
    Formalism.L2.Host.infDiag k * finPartI L (Neutral.B1.diagUnits L k) = Neutral.B1.diagUnits L k := by
  have h : ((Formalism.L2.Host.infDiag k : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold Formalism.L2.Host.infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
      ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem phase_sq {a u : ℂ} (ha : a ≠ 0) (h : u * starRingEnd ℂ a = a) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = u := by
  have hc : starRingEnd ℂ a ≠ 0 := by simpa using ha
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', div_eq_iff (mul_ne_zero ha hc)]
  linear_combination (-a) * h

theorem chi_laws (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : Formalism.L2.Host.HChar H.E) (hχ : Formalism.L2.Host.IsChiPsi H χ) :
    (∀ x ∈ UOT H, tildeD H χ x = 1) ∧
    (letI := H.cmStar; ∀ z : unitary H.E,
      ((tildeD H χ (e1T H z) : ℂˣ) : ℂ) = ∏ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹) := by
  have hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
    (_root_.GlobalTheory.Mem.KerDet.kernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v => (hχ.unr v).levelLe 1) (fun v _ => hχ.unr v)
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_UOT H).1 hx
    rw [tildeD_mk H hK]
    refine GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 ha) (fun _ => rfl) fun v y hy => ?_
    refine hχ.unr v y ?_
    unfold Formalism.L2.Host.IsUnitAt
    rw [hy]
    exact ha v
  · letI := H.cmStar
    intro z
    obtain ⟨h1, h2⟩ := GlobalTheory.T.exists_conj_quotient_of_rationalUnitaryDeterminantMap R H
    obtain ⟨k, hk⟩ := h2 z
    rw [← h1 k z hk, tildeD_mk H hK]
    have e := congrArg χ.1 (infDiag_mul_finPart k)
    rw [map_mul, χ.2.2 k, mul_comm, mul_eq_one_iff_eq_inv] at e
    have hi : ((χ.1 (Formalism.L2.Host.infDiag k) : ℂˣ) : ℂ) = _ := hχ.inf k
    rw [e, Units.val_inv_eq_inv_val, hi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine phase_sq ((map_ne_zero _).2 k.ne_zero) ?_
    have hc : Formalism.L2.Host.embPsi H τ (H.conj (k : H.E)) = starRingEnd ℂ (Formalism.L2.Host.embPsi H τ (k : H.E)) :=
      H.conjE_apply _ _
    rw [← hc]
    exact (map_mul (Formalism.L2.Host.embPsi H τ) _ _).symm.trans (congrArg _ hk)

end GlobalTheory.Mem.ChiLaws
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ULocDualHformOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

theorem uLocDual_intOE_map {E : Type} [Field E] [NumberField E] (σ : E →+* E) {a : E}
    (ha : a ∈ intOE E) : σ a ∈ intOE E := by
  obtain ⟨r, rfl⟩ := ha
  exact ⟨⟨σ r, (RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom⟩, rfl⟩

theorem uLocDual_hform_one {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (x y : Fin n → E) :
    Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold Formalism.UG.hform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, mul_one]
  · intro j _ hj; rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem uLocDual_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : ∀ x, σ (σ x) = x) (n : ℕ) [NeZero n] (p q : 𝓞 E) (_ : (p : E) ≠ 0) (_ : (q : E) = σ (p : E)),
    Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹))) = rll_dLat n (q : E) := by
  intro F E _ _ _ _ _ σ _ n _ p q hp hq
  have e : dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹)) =
      (rll_dLat n (q : E) : Set (Fin n → E)) := by
    ext y
    rw [SetLike.mem_coe, rll_mem_dLat]
    show (∀ x ∈ rll_dLat n ((p : E)⁻¹), Formalism.UG.hform (σ : E →+* E) 1 x y ∈ (algebraMap (𝓞 E) E).range) ↔ _
    simp only [uLocDual_hform_one]
    constructor
    · intro hy
      refine ⟨fun i hi => ?_, ?_⟩
      · have := hy (Pi.single i 1) ⟨fun j _ => by
          by_cases hj : j = i
          · subst hj; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _, by
          rw [Pi.single_eq_of_ne (Ne.symm hi), mul_zero]; exact zero_mem _⟩
        rw [Finset.sum_eq_single i] at this
        · rwa [Pi.single_eq_same, map_one, one_mul] at this
        · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have := hy (Pi.single (lastIdx n) (p : E)) ⟨fun j hj => by
          rw [Pi.single_eq_of_ne hj]; exact zero_mem _, by
          rw [Pi.single_eq_same, inv_mul_cancel₀ hp]; exact one_mem _⟩
        rw [Finset.sum_eq_single (lastIdx n)] at this
        · rw [Pi.single_eq_same] at this
          show (q : E) * y (lastIdx n) ∈ intOE E
          rw [hq]; exact this
        · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨h1, h2⟩ x ⟨hx1, hx2⟩
      refine sum_mem fun i _ => ?_
      by_cases hi : i = lastIdx n
      · subst hi
        have hl : x (lastIdx n) = (p : E) * ((p : E)⁻¹ * x (lastIdx n)) := by
          rw [mul_inv_cancel_left₀ hp]
        rw [hl, map_mul, mul_comm ((σ : E →+* E) (p : E)), mul_assoc]
        refine mul_mem (uLocDual_intOE_map _ hx2) ?_
        have : (σ : E →+* E) (p : E) = (q : E) := by rw [hq]; rfl
        rw [this]; exact h2
      · exact mul_mem (uLocDual_intOE_map _ (hx1 i hi)) (h1 i hi)
  rw [e, Submodule.span_eq]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UlocOfTrivDisc
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem uloc_of_triv_disc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (_ : (T : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ levelVL σ J v S.Lb)
    (_ : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb),
    x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad S v hT x hx hy
  have hL : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := by
    unfold Formalism.UG.levelVL Formalism.UG.level at hx
    exact hx.2
  have hLi : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔
      ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
        latS (F := F) (v.adicCompletion F) (intV E v) S.Lb :=
    (stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)).inv_mem hL
  have hsub : latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    unfold Formalism.UG.latS
    apply Submodule.span_mono
    apply Set.image_mono
    intro z hz
    exact Submodule.subset_span (S.Lb_int z hz)
  have hfw : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    intro y hy'
    have h2 := Submodule.add_mem _ (hsub (hy y hy')) hy'
    rwa [sub_add_cancel] at h2
  have hbw : ∀ y, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) →
      y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    intro y hw
    have hd := hy _ hw
    have hi := hsub ((hLi _).1 hd)
    have key : y = (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y -
        ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
          ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
            ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) -
            (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) := by
      have hinv : ∀ u, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
          ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ u) = u := by
        intro u
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [Matrix.mulVec_sub, hinv, hinv, sub_sub_cancel]
    rw [key]
    exact Submodule.sub_mem _ hw hi
  rw [S.UlocAlt v hT, Subgroup.mem_inf]
  refine ⟨hx, ⟨?_, ?_⟩⟩
  · show ∀ y, y ∈ _ ↔ _
    exact fun y => ⟨hfw y, hbw y⟩
  · intro z
    have h0 := S.fT_L v hT
      (⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (z : Fin n → E ⊗[F] v.adicCompletion F), hfw z z.2⟩ - z)
      (by
        show (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (z : Fin n → E ⊗[F] v.adicCompletion F) -
          (z : Fin n → E ⊗[F] v.adicCompletion F) ∈ _
        exact hy z z.2)
    rw [map_sub, sub_eq_zero] at h0
    exact h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValNatCastLtOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.LevCong

variable {F : Type} [Field F] [NumberField F]

theorem val_natCast_lt_one (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hv : (p : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (p : v.adicCompletion F) < 1 := by
  have : (p : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
  rw [this]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v (algebraMap (𝓞 F) F (p : 𝓞 F))
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v _).2 hv
  exact h2 ▸ h3

theorem redM_eq_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hv : (p : 𝓞 F) ∈ v.asIdeal)
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hM : ∀ r c, ∃ t ∈ v.adicCompletionIntegers F, M r c = (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) r c + p * t) :
    redM F v M = 1 := by
  have hp : IsLocalRing.residue (v.adicCompletionIntegers F) (p : v.adicCompletionIntegers F) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    refine (Valuation.mem_maximalIdeal_iff _ _).2 ?_
    simpa using val_natCast_lt_one v p hv
  ext r c
  obtain ⟨t, ht, e⟩ := hM r c
  set u : v.adicCompletionIntegers F := (if r = c then 1 else 0) + p * ⟨t, ht⟩ with hu
  have e' : M r c = (u : v.adicCompletion F) := by
    rw [e, hu, Matrix.one_apply]
    split_ifs <;> simp
  have hm : M r c ∈ v.adicCompletionIntegers F := e' ▸ u.2
  unfold redM
  rw [dite_eq_left hm]
  have : (⟨M r c, hm⟩ : v.adicCompletionIntegers F) = u := Subtype.ext e'
  rw [this, hu, map_add (f := _), map_mul, hp, zero_mul, add_zero, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_Uloc_of_cong : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (_ : GLevH S G H lam) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (_ : (gp a : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ levelVL σ J v S.Lb)
    (_ : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = ((gp a : ℕ) : E ⊗[F] v.adicCompletion F) • z),
    x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad gp S G H lam L a v h x hx hc
  refine (L.mem a v h x hx).2 ⟨1, (H a v h).one_mem, ?_⟩
  rw [Units.val_one]
  refine (redM_eq_one v (gp a) h _ fun r c => ?_).symm
  set fr := L.fr a v h with hfr
  set φ := G.phi a v h with hφ
  have hinv : ∀ w : Fin n → v.adicCompletion F,
      ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
        ((fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  obtain ⟨y, hy, hyw⟩ := (L.fr_lat a v h ((fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single c 1)).2 (fun b => by
    show (((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ _) b ∈ _
    rw [hinv, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _)
  obtain ⟨z, hz, e⟩ := hc y hy
  have ht := (L.fr_lat a v h (fun b => φ (z b))).1 ⟨z, hz, fun _ => rfl⟩ r
  refine ⟨_, ht, ?_⟩
  have hy' : (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single c 1 = φ ∘ y := (funext hyw).symm
  have e2 : ((bc φ x : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ (φ ∘ y) =
      φ ∘ y + ((gp a : ℕ) : v.adicCompletion F) • fun b => φ (z b) := by
    funext b
    have e3 := congrArg φ (congrFun e b)
    rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, sub_eq_iff_eq_add'] at e3
    exact e3
  have e4 : G.mat a v h fr x *ᵥ Pi.single c 1 = Pi.single c 1 + ((gp a : ℕ) : v.adicCompletion F) •
      (((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ fun b => φ (z b)) := by
    unfold GLoc.mat
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hy', ← hφ, e2, Matrix.mulVec_add,
      Matrix.mulVec_smul, ← hy', hinv]
  have e5 := congrFun e4 r
  rw [Matrix.mulVec_single_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at e5
  rw [Matrix.one_apply]
  exact e5

end GlobalTheory.Mem.LevCong
end

