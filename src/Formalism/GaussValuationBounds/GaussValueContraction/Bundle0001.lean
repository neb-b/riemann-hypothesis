module

public import Formalism.GaussValuationBounds.Bundle0001
public import Formalism.GaussValuationBounds.Statement
public import Formalism.WindowSums.PowerSeriesRelationList

@[expose] public section

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.GaussBasic
section
noncomputable section

namespace Formalism.NOK

open scoped ENNReal

open IsDiscreteValuationRing in
theorem minLeGaussValAdd : GaussAdd := by
  intro O _ _ _ x f g
  refine le_iInf fun n => ?_
  have h1 : min (gaussV x f) (gaussV x g) ≤
      min ((((addVal O (PowerSeries.coeff n f) : ℕ∞)) : ℝ≥0∞) + ENNReal.ofReal (x * n))
        ((((addVal O (PowerSeries.coeff n g) : ℕ∞)) : ℝ≥0∞) + ENNReal.ofReal (x * n)) :=
    min_le_min (iInf_le _ n) (iInf_le _ n)
  refine h1.trans ?_
  rw [min_add_add_right, map_add (f := _)]
  gcongr ?_ + _
  have h2 := addVal_add (R := O) (a := PowerSeries.coeff n f) (b := PowerSeries.coeff n g)
  rcases le_total (addVal O (PowerSeries.coeff n f)) (addVal O (PowerSeries.coeff n g)) with h | h
  · rw [min_eq_left (ENat.toENNReal_le.mpr h)]
    exact ENat.toENNReal_le.mpr (by rwa [min_eq_left h] at h2)
  · rw [min_eq_right (ENat.toENNReal_le.mpr h)]
    exact ENat.toENNReal_le.mpr (by rwa [min_eq_right h] at h2)

open IsDiscreteValuationRing in
theorem gaussValC : GaussC := by
  intro O _ _ _ x _ c
  refine le_antisymm ((iInf_le _ 0).trans (by simp)) (le_iInf fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [PowerSeries.coeff_C, if_neg hn.ne', addVal_zero]
    simp

open IsDiscreteValuationRing in
theorem gaussValUnit : GaussUnit := by
  intro O _ _ _ x _ u hu
  obtain ⟨w, hw⟩ := hu.map (PowerSeries.constantCoeff (R := O))
  refine le_antisymm ((iInf_le _ 0).trans ?_) (by simp)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hw, addVal_eq_zero_of_unit]
  simp


end Formalism.NOK
end
end

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.GaussMul
section
noncomputable section

namespace Formalism.NOK

open scoped ENNReal
open IsDiscreteValuationRing

section GaussMulAux

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private def gaussTerm (x : ℝ) (f : PowerSeries O) (n : ℕ) : ℝ≥0∞ :=
  ((addVal O (PowerSeries.coeff n f) : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (x * n)

private theorem gaussV_le_term (x : ℝ) (f : PowerSeries O) (n : ℕ) : gaussV x f ≤ gaussTerm x f n := by
  unfold gaussV gaussTerm
  exact iInf_le _ n

private theorem ofReal_mul_natAdd {x : ℝ} (hx : 0 ≤ x) (i j : ℕ) :
    ENNReal.ofReal (x * ((i + j : ℕ) : ℝ)) = ENNReal.ofReal (x * i) + ENNReal.ofReal (x * j) := by
  rw [Nat.cast_add, mul_add]
  exact ENNReal.ofReal_add (mul_nonneg hx (Nat.cast_nonneg _)) (mul_nonneg hx (Nat.cast_nonneg _))

private theorem gaussV_zero (x : ℝ) : gaussV x (0 : PowerSeries O) = ⊤ := by
  unfold gaussV
  refine le_antisymm le_top (le_iInf fun n => ?_)
  exact le_of_eq (by rw [map_zero, (addVal O).map_zero, ENat.toENNReal_top, top_add])

private theorem exists_coeff_ne_zero {f : PowerSeries O} (hf : f ≠ 0) : ∃ m, PowerSeries.coeff m f ≠ 0 := by
  by_contra h
  push Not at h
  exact hf (PowerSeries.ext fun n => by rw [h n, map_zero])

private theorem enat_toENNReal_ne_top_of_ne_top {a : ℕ∞} (h : a ≠ ⊤) : (a : ℝ≥0∞) ≠ ⊤ := by
  lift a to ℕ using h
  simp

private theorem gaussTerm_ne_top {x : ℝ} {f : PowerSeries O} {n : ℕ} (h : PowerSeries.coeff n f ≠ 0) :
    gaussTerm x f n ≠ ⊤ := by
  have h1 : addVal O (PowerSeries.coeff n f) ≠ ⊤ := fun h' => h (addVal_eq_top_iff.mp h')
  unfold gaussTerm
  exact ENNReal.add_ne_top.mpr ⟨enat_toENNReal_ne_top_of_ne_top h1, ENNReal.ofReal_ne_top⟩

private theorem addVal_ne_top_of_term {x : ℝ} {f : PowerSeries O} {n : ℕ} (h : gaussTerm x f n ≠ ⊤) :
    addVal O (PowerSeries.coeff n f) ≠ ⊤ := by
  intro h'
  apply h
  unfold gaussTerm
  rw [h', ENat.toENNReal_top, top_add]

private theorem gaussV_ne_top {x : ℝ} {f : PowerSeries O} (hf : f ≠ 0) : gaussV x f ≠ ⊤ := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  exact ne_top_of_le_ne_top (gaussTerm_ne_top (x := x) hm) (gaussV_le_term x f m)

private theorem gaussTerm_add_gaussTerm_eq_addVal_coeff_mul {x : ℝ} (hx : 0 ≤ x) (f g : PowerSeries O) (i j : ℕ) :
    gaussTerm x f i + gaussTerm x g j =
      ((addVal O (PowerSeries.coeff i f * PowerSeries.coeff j g) : ℕ∞) : ℝ≥0∞) +
        ENNReal.ofReal (x * ((i + j : ℕ) : ℝ)) := by
  unfold gaussTerm
  rw [(addVal O).map_mul, ENat.toENNReal_add, ofReal_mul_natAdd hx]
  exact add_add_add_comm _ _ _ _

private theorem gaussV_add_le_mul {x : ℝ} (hx : 0 ≤ x) (f g : PowerSeries O) :
    gaussV x f + gaussV x g ≤ gaussV x (f * g) := by
  have hR : gaussV x (f * g) = ⨅ n : ℕ, gaussTerm x (f * g) n := rfl
  rw [hR]
  refine le_iInf fun n => ?_
  have key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, gaussV x f + gaussV x g ≤
      ((addVal O (PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g) : ℕ∞) : ℝ≥0∞) +
        ENNReal.ofReal (x * n) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    calc gaussV x f + gaussV x g ≤ gaussTerm x f p.1 + gaussTerm x g p.2 :=
          add_le_add (gaussV_le_term x f p.1) (gaussV_le_term x g p.2)
      _ = _ := by rw [gaussTerm_add_gaussTerm_eq_addVal_coeff_mul hx, hp]
  obtain ⟨p0, hp0, hmin⟩ := (Finset.HasAntidiagonal.antidiagonal n).exists_min_image
      (fun p => addVal O (PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g))
      ⟨(0, n), by simp⟩
  have hle : addVal O (PowerSeries.coeff p0.1 f * PowerSeries.coeff p0.2 g) ≤
      addVal O (PowerSeries.coeff n (f * g)) := by
    rw [PowerSeries.coeff_mul]
    exact (addVal O).map_le_sum hmin
  calc gaussV x f + gaussV x g ≤ _ := key p0 hp0
    _ ≤ ((addVal O (PowerSeries.coeff n (f * g)) : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (x * n) :=
        add_le_add (ENat.toENNReal_le.mpr hle) le_rfl

private theorem gaussV_exists_eq {x : ℝ} (hx : 0 < x) {f : PowerSeries O} (hf : f ≠ 0) :
    ∃ i, gaussTerm x f i = gaussV x f := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  have hTtop : gaussTerm x f m ≠ ⊤ := gaussTerm_ne_top hm
  obtain ⟨N', hN'⟩ := exists_nat_gt ((gaussTerm x f m).toReal / x)
  obtain ⟨N, hmN, hN'N⟩ : ∃ N, m ≤ N ∧ N' ≤ N := ⟨max m N', le_max_left _ _, le_max_right _ _⟩
  obtain ⟨i, -, hmin⟩ := (Finset.range (N + 1)).exists_min_image (gaussTerm x f)
    ⟨m, Finset.mem_range.mpr (by omega)⟩
  refine ⟨i, le_antisymm ?_ (gaussV_le_term x f i)⟩
  have hR : gaussV x f = ⨅ n : ℕ, gaussTerm x f n := rfl
  rw [hR]
  refine le_iInf fun n => ?_
  by_cases hn : n ≤ N
  · exact hmin n (Finset.mem_range.mpr (by omega))
  · push Not at hn
    have h1 : gaussTerm x f i ≤ gaussTerm x f m := hmin m (Finset.mem_range.mpr (by omega))
    have h4 : (N' : ℝ) < n := by exact_mod_cast lt_of_le_of_lt hN'N hn
    have h3 : (gaussTerm x f m).toReal < N' * x := (div_lt_iff₀ hx).mp hN'
    have h2 : gaussTerm x f m < ENNReal.ofReal (x * n) := by
      rw [ENNReal.lt_ofReal_iff_toReal_lt hTtop]
      nlinarith
    have h5 : ENNReal.ofReal (x * n) ≤ gaussTerm x f n := by
      unfold gaussTerm
      exact le_add_self
    exact (h1.trans h2.le).trans h5

private theorem addVal_add_eq_left_of_addVal_lt {a b : O} (h : addVal O a < addVal O b) :
    addVal O (a + b) = addVal O a := by
  apply le_antisymm
  · by_contra hc
    push Not at hc
    have h1 := (addVal O).map_add (a + b) (-b)
    rw [add_neg_cancel_right, (addVal O).map_neg] at h1
    exact absurd h1 (not_le.mpr (lt_min hc h))
  · have h2 := (addVal O).map_add a b
    rwa [min_eq_left h.le] at h2

private theorem gaussV_mul_le {x : ℝ} (hx : 0 < x) {f g : PowerSeries O} (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussV x (f * g) ≤ gaussV x f + gaussV x g := by
  classical
  have ef := gaussV_exists_eq hx hf
  have eg := gaussV_exists_eq hx hg
  obtain ⟨i0, hi0, ltf⟩ : ∃ i0, gaussTerm x f i0 = gaussV x f ∧
      ∀ i < i0, gaussV x f < gaussTerm x f i :=
    ⟨Nat.find ef, Nat.find_spec ef, fun i hi =>
      lt_of_le_of_ne (gaussV_le_term x f i) fun h => Nat.find_min ef hi h.symm⟩
  obtain ⟨j0, hj0, ltg⟩ : ∃ j0, gaussTerm x g j0 = gaussV x g ∧
      ∀ j < j0, gaussV x g < gaussTerm x g j :=
    ⟨Nat.find eg, Nat.find_spec eg, fun j hj =>
      lt_of_le_of_ne (gaussV_le_term x g j) fun h => Nat.find_min eg hj h.symm⟩
  have haf : addVal O (PowerSeries.coeff i0 f) ≠ ⊤ :=
    addVal_ne_top_of_term (x := x) (by rw [hi0]; exact gaussV_ne_top hf)
  have hbg : addVal O (PowerSeries.coeff j0 g) ≠ ⊤ :=
    addVal_ne_top_of_term (x := x) (by rw [hj0]; exact gaussV_ne_top hg)
  have ha : PowerSeries.coeff i0 f ≠ 0 := fun h => haf (by rw [h, (addVal O).map_zero])
  have hb : PowerSeries.coeff j0 g ≠ 0 := fun h => hbg (by rw [h, (addVal O).map_zero])
  have habtop : addVal O (PowerSeries.coeff i0 f * PowerSeries.coeff j0 g) ≠ ⊤ :=
    fun h => mul_ne_zero ha hb (addVal_eq_top_iff.mp h)
  have hlt : ∀ p ∈ (Finset.HasAntidiagonal.antidiagonal (i0 + j0)).erase (i0, j0),
      addVal O (PowerSeries.coeff i0 f * PowerSeries.coeff j0 g) <
        addVal O (PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g) := by
    intro p hp
    rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨hne, hsum⟩ := hp
    have hstrict : gaussTerm x f i0 + gaussTerm x g j0 < gaussTerm x f p.1 + gaussTerm x g p.2 := by
      rw [hi0, hj0]
      rcases lt_trichotomy p.1 i0 with h | h | h
      · calc gaussV x f + gaussV x g < gaussTerm x f p.1 + gaussV x g :=
            (ENNReal.add_lt_add_iff_right (gaussV_ne_top hg)).mpr (ltf _ h)
          _ ≤ _ := add_le_add le_rfl (gaussV_le_term x g p.2)
      · exact absurd (Prod.ext h (by show p.2 = j0; omega)) hne
      · have h' : p.2 < j0 := by omega
        calc gaussV x f + gaussV x g < gaussV x f + gaussTerm x g p.2 :=
            (ENNReal.add_lt_add_iff_left (gaussV_ne_top hf)).mpr (ltg _ h')
          _ ≤ _ := add_le_add (gaussV_le_term x f p.1) le_rfl
    rw [gaussTerm_add_gaussTerm_eq_addVal_coeff_mul hx.le f g i0 j0, gaussTerm_add_gaussTerm_eq_addVal_coeff_mul hx.le f g p.1 p.2, hsum]
      at hstrict
    exact ENat.toENNReal_lt.mp ((ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).mp hstrict)
  have hcoeff : addVal O (PowerSeries.coeff (i0 + j0) (f * g)) =
      addVal O (PowerSeries.coeff i0 f * PowerSeries.coeff j0 g) := by
    rw [PowerSeries.coeff_mul, ← Finset.add_sum_erase _ _
      (show (i0, j0) ∈ Finset.HasAntidiagonal.antidiagonal (i0 + j0) by simp)]
    exact addVal_add_eq_left_of_addVal_lt ((addVal O).map_lt_sum habtop hlt)
  calc gaussV x (f * g) ≤ gaussTerm x (f * g) (i0 + j0) := gaussV_le_term x (f * g) (i0 + j0)
    _ = gaussTerm x f i0 + gaussTerm x g j0 := by
        rw [gaussTerm_add_gaussTerm_eq_addVal_coeff_mul hx.le f g i0 j0]
        unfold gaussTerm
        rw [hcoeff]
    _ = gaussV x f + gaussV x g := by rw [hi0, hj0]

end GaussMulAux

theorem gaussValMul : GaussMul := by
  intro O _ _ _ x hx f g
  by_cases hf : f = 0
  · subst hf
    rw [zero_mul, gaussV_zero, top_add]
  by_cases hg : g = 0
  · subst hg
    rw [mul_zero, gaussV_zero, add_top]
  exact le_antisymm (gaussV_mul_le hx hf hg) (gaussV_add_le_mul hx.le f g)

end Formalism.NOK
end
end

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.GaussValueContractionProofFactBis
section
noncomputable section

namespace Formalism.NOK

open Polynomial

theorem padicInt_valuation_unit (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) :
    (u : ℤ_[ℓ]).valuation = 0 := by
  have h := PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero u⁻¹)
  rw [Units.mul_inv, PadicInt.valuation_one] at h
  omega

theorem cjExist_proof : CjExist := by
  intro ℓ _ hℓ χ hχ
  have hZ := Formalism.WindowSums.arc_ZpowVal ℓ χ 1 le_rfl (fun h => absurd h hℓ) hχ
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hdvd : ∀ j : ℤ, (ℓ : ℤ_[ℓ]) ∣ ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp
    · obtain ⟨hne, hv⟩ := hZ (-j) (neg_ne_zero.2 hj)
      rw [PadicInt.unitCoeff_spec hne]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (by rw [hv]; omega)) _
  choose d hd using hdvd
  have hc1 : ∀ j, -(ℓ : ℤ_[ℓ]) * (-d j) = ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro j
    rw [hd j]
    ring
  have key : ∀ j j' : ℤ, j ≠ j' → -d j' - -d j ≠ 0 ∧
      PadicInt.valuation (-d j' - -d j) = padicValInt ℓ (j' - j) := by
    intro j j' hjj
    have hid : χ ^ (-j) = χ ^ (-j') * χ ^ (j' - j) := by
      rw [← zpow_add]
      congr 1
      ring
    have hkey : (ℓ : ℤ_[ℓ]) ^ 1 * (-d j' - -d j) =
        ((χ ^ (-j') : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (((χ ^ (j' - j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) := by
      have e1 := hd j
      have e2 := hd j'
      rw [hid, Units.val_mul] at e1
      linear_combination e2 - e1
    obtain ⟨hne, hv⟩ := hZ (j' - j) (sub_ne_zero.2 (Ne.symm hjj))
    have hw : -d j' - -d j ≠ 0 := by
      intro h
      rw [h, mul_zero] at hkey
      exact mul_ne_zero (Units.ne_zero _) hne hkey.symm
    refine ⟨hw, ?_⟩
    have h1 := PadicInt.valuation_p_pow_mul 1 (-d j' - -d j) hw
    rw [hkey, PadicInt.valuation_mul (Units.ne_zero _) hne, padicInt_valuation_unit, hv] at h1
    omega
  refine ⟨fun j => -d j, hc1, ?_, fun j j' h => key j' j (Ne.symm h)⟩
  have h0 : (ℓ : ℤ_[ℓ]) * d 0 = 0 := by
    rw [← hd 0]
    simp
  show -d 0 = 0
  rw [neg_eq_zero]
  exact (mul_eq_zero.1 h0).resolve_left hℓ0

end Formalism.NOK
end
end

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.KapBoundProof
section
namespace Formalism.NOK

theorem kapBound_proof : KapBound := by
  intro ℓ _ hℓ χ hχ ell g h a JJ hJJ hbd
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.arc_KillerVal ℓ hℓ χ hχ ell JJ
  refine ⟨hne, ?_⟩

  have hcard : (JJ.erase 0).card ≤ 20 * g := by
    calc (JJ.erase 0).card ≤ JJ.card := Finset.card_le_card (Finset.erase_subset _ _)
      _ ≤ (Finset.univ.biUnion (fun t : Fin 5 => Finset.Ico (a t) (a t + 4 * (g : ℤ)))).card :=
          Finset.card_le_card hJJ
      _ ≤ ∑ t : Fin 5, (Finset.Ico (a t) (a t + 4 * (g : ℤ))).card := Finset.card_biUnion_le
      _ = ∑ t : Fin 5, 4 * g := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Int.card_Ico, add_sub_cancel_left]
          omega
      _ = 20 * g := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring

  have hsumv : ((∑ i ∈ JJ.erase 0, padicValInt ℓ i : ℕ) : ℝ) ≤
      5 * (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) := by
    have hle : (∑ i ∈ JJ.erase 0, padicValInt ℓ i) ≤
        ∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
          padicValInt ℓ i := by
      calc (∑ i ∈ JJ.erase 0, padicValInt ℓ i)
          ≤ ∑ i ∈ JJ.erase 0, ∑ t : Fin 5,
              (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) := by
            apply Finset.sum_le_sum
            intro i hi
            obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (hJJ (Finset.mem_of_mem_erase hi))
            calc padicValInt ℓ i
                = (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
                  (if_pos ht).symm
              _ ≤ ∑ t' : Fin 5,
                    (if i ∈ Finset.Ico (a t') (a t' + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
                  Finset.single_le_sum
                    (f := fun t' => if i ∈ Finset.Ico (a t') (a t' + 4 * (g : ℤ)) then padicValInt ℓ i else 0)
                    (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
        _ = ∑ t : Fin 5, ∑ i ∈ JJ.erase 0,
              (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
            Finset.sum_comm
        _ = ∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
              padicValInt ℓ i := by
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.sum_filter]
    have hwin : ∀ t : Fin 5,
        ((∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
            padicValInt ℓ i : ℕ) : ℝ) ≤ 4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ)) := by
      intro t
      have hw := Formalism.WindowSums.arc_WindowSum ℓ (a t) (4 * g) (2 * h)
        ((JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)))) ?_ ?_ ?_
      · push_cast at hw ⊢
        exact hw
      · intro i hi
        rw [Finset.mem_filter] at hi
        push_cast
        exact hi.2
      · intro h0
        rw [Finset.mem_filter] at h0
        exact (Finset.mem_erase.mp h0.1).1 rfl
      · intro i hi
        rw [Finset.mem_filter] at hi
        push_cast
        exact hbd i (Finset.mem_of_mem_erase hi.1)
    calc ((∑ i ∈ JJ.erase 0, padicValInt ℓ i : ℕ) : ℝ)
        ≤ ((∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter
              (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ = ∑ t : Fin 5, ((∑ i ∈ (JJ.erase 0).filter
              (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
      _ ≤ ∑ _t : Fin 5, (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) :=
          Finset.sum_le_sum (fun t _ => hwin t)
      _ = 5 * (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hsplit : (∑ i ∈ JJ.erase 0, (1 + ell + padicValInt ℓ i)) =
      (JJ.erase 0).card * (1 + ell) + ∑ i ∈ JJ.erase 0, padicValInt ℓ i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  have hc : (((JJ.erase 0).card * (1 + ell) : ℕ) : ℝ) ≤ 20 * (g : ℝ) * (1 + (ell : ℝ)) := by
    have h1 : (JJ.erase 0).card * (1 + ell) ≤ 20 * g * (1 + ell) := Nat.mul_le_mul_right _ hcard
    exact_mod_cast h1
  rw [hval, hsplit]
  push_cast at hc hsumv ⊢
  linarith

end Formalism.NOK
end

