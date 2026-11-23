module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointLocalRingClosedPointCentreOfPlace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem exists_locRing_closedPoint_centre : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (A : Subalgebra ℂ κ'),
    Algebra.Smooth ℂ A → A.toSubring ≤ F.ring.toSubring →
    (∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B), RatRes (algebraMap ℂ κ') B ∧
      A.toSubring ≤ B ∧ B ≤ F.ring.toSubring ∧
      ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro κ' _ _ F A hsm hAF hfrac
    haveI : IsFractionRing A κ' := IsFractionRing.of_field A κ' fun z => by
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac z
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by simp [← e, hb0]⟩
    let ι : A →+* F.ring := (algebraMap A κ').codRestrict F.ring (fun x => hAF x.2)
    let q : Ideal A := (IsLocalRing.maximalIdeal F.ring).comap ι
    have hq : q ≠ ⊤ := by
      intro h
      have h1 : (1 : A) ∈ q := h ▸ Submodule.mem_top
      exact (IsLocalRing.mem_maximalIdeal _).1 (show ι 1 ∈ _ from h1) (by simp)
    obtain ⟨n, hn, hqn⟩ := Ideal.exists_le_maximal q hq
    have hinv : ∀ s ∈ n.primeCompl, ((s : A) : κ')⁻¹ ∈ F.ring := by
      intro s hs
      have hs' : ι s ∉ IsLocalRing.maximalIdeal F.ring := fun h => hs (hqn h)
      have hu : IsUnit (ι s) := by
        by_contra h
        exact hs' ((IsLocalRing.mem_maximalIdeal _).2 h)
      obtain ⟨u, hu⟩ := hu.exists_right_inv
      have e : ((s : A) : κ') * (u : κ') = 1 := congrArg Subtype.val hu
      rw [← eq_inv_of_mul_eq_one_right e]
      exact u.2
    have hle : n.primeCompl ≤ nonZeroDivisors A := n.primeCompl_le_nonZeroDivisors
    let B0 : Subalgebra A κ' := Localization.subalgebra.ofField κ' n.primeCompl hle
    haveI : IsLocalization.AtPrime B0 n := Localization.subalgebra.isLocalization_ofField κ' _ hle
    have hAB : A.toSubring ≤ B0.toSubring := fun x hx => B0.algebraMap_mem (⟨x, hx⟩ : A)
    have hc : ∀ a, algebraMap ℂ κ' a ∈ B0.toSubring := fun a => hAB (A.algebraMap_mem a)
    letI : Algebra ℂ B0 := ((algebraMap A B0).comp (algebraMap ℂ A)).toAlgebra
    haveI : IsScalarTower ℂ A B0 := IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := A) (A := B0) rfl
    have hloc : IsLocalRing B0 := IsLocalization.AtPrime.isLocalRing B0 n
    refine ⟨B0.toSubring, ⟨hc, hloc, ?_, ?_⟩, ?_, hAB, ?_, ?_⟩
    · show (algebraMap ℂ B0).EssFiniteType
      refine RingHom.EssFiniteType.comp ?_ ?_
      · exact RingHom.essFiniteType_algebraMap.2 inferInstance
      · exact RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization B0 n.primeCompl)
    · intro f
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac f
      exact ⟨a, hAB ha, b, hAB hb, hb0, e⟩
    · intro r hr
      let r' : B0 := ⟨r, hr⟩
      letI : Field (A ⧸ n) := Ideal.Quotient.field n
      haveI : Module.Finite ℂ (A ⧸ n) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ n)
      have hsurj : Function.Surjective (algebraMap ℂ (A ⧸ n)) :=
        IsAlgClosed.algebraMap_bijective_of_isIntegral.2
      let e := IsLocalization.AtPrime.equivQuotMaximalIdeal n B0
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk _ r'))
      obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk n x)
      refine ⟨a, ?_⟩
      let z : B0 := algebraMap A B0 (algebraMap ℂ A a)
      have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B0) z = Ideal.Quotient.mk _ r' := by
        rw [← e.apply_symm_apply (Ideal.Quotient.mk _ r'), ← hx, ← ha]
        exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk n B0 (algebraMap ℂ A a)).symm
      have hm : r' - z ∈ IsLocalRing.maximalIdeal B0 := Ideal.Quotient.eq.1 hz.symm
      have hnu := (nonUnit_iff (R := B0.toSubring) (r' - z)).2 ((IsLocalRing.mem_maximalIdeal _).1 hm)
      exact hnu
    · rintro x ⟨a, s, hs, rfl⟩
      exact F.ring.toSubring.mul_mem (hAF a.2) (hinv s hs)
    · show (algebraMap ℂ B0).FormallySmooth
      haveI : Algebra.FormallyEtale A B0 := Algebra.FormallyEtale.of_isLocalization n.primeCompl
      haveI : Algebra.FormallySmooth ℂ B0 := Algebra.FormallySmooth.comp ℂ A B0
      exact RingHom.formallySmooth_algebraMap.2 inferInstance

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChernIntegralTensPow
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernPoly

theorem chernInt_tens_pow_poly : ∀ (Y : Var ℂ) (L H : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (ψ : Weight Y.str (RingHom.id ℂ) H), φ.IsCInf → ψ.IsCInf → ∃ P : Polynomial ℝ,
      P.eval 0 = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) ∧ ∀ m : ℕ,
        Weight.chernInt (φ.tens (ψ.pow m)) Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  intro Y L H φ ψ hφ hψ
  obtain ⟨hc, ht, _, A, hA⟩ := _root_.GlobalTheory.cxPts_var_compact_manifold Y
  have := hc
  have := ht

  have hφs : φ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hφ
  have hψs : ψ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hψ
  have hΦ : IsPotential A φ.locPot := hφs.isPotential hA
  have hΨ : IsPotential A ψ.locPot := hψs.isPotential hA

  obtain ⟨P, hP⟩ := _root_.GlobalTheory.MongeAmperePoly.mInt_add_zsmul_poly Y.dim _ A (fun _ => φ.locPot) (fun _ => ψ.locPot)
    (fun _ => hΦ) (fun _ => hΨ)

  refine ⟨P, ?_, fun m => ?_⟩
  · rw [(_root_.GlobalTheory.chernInt_one_eq_mInt Y L φ hφ).2 A hA, ← (by simpa using hP 0 :
      mInt A (fun _ => φ.locPot + ψ.locPot.zsmul 0) (fun _ => 1) = P.eval 0)]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine (Weight.sameForm_of_eq φ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A 0 _ hΨ))
      (fun x => ⟨pick φ.isLB x, mem_pick φ.isLB x, fun z => ?_⟩)).symm
    show φ.φ (pick φ.isLB x) z / 2 = φ.locPot.φ x z + ((0 : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.locPot_φ]
    simp
  · have hT : (φ.tens (ψ.pow m)).IsCInf := hφ.tens (hψ.zpow m)
    rw [(_root_.GlobalTheory.chernInt_one_eq_mInt Y _ _ hT).2 A hA, show ((m : ℕ) : ℝ) = (((m : ℕ) : ℤ) : ℝ) by push_cast; rfl,
      ← hP m]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine Weight.sameForm_of_eq _ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A m _ hΨ))
      (fun x => ⟨(pick φ.isLB x, fun _ => pick ψ.isLB x),
        mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick ψ.isLB x)⟩, fun z => ?_⟩)
    show (φ.φ (pick φ.isLB x) z + (ψ.zpow m).φ (fun _ => pick ψ.isLB x) z) / 2 =
      φ.locPot.φ x z + ((m : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.zpow_φ, Weight.locPot_φ, Weight.locPot_φ]
    ring

end GlobalTheory.ChernPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalBudgetsTwoPointInduction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_rat_budget_term (r : ℕ) (hr : 0 < r) (e : ℕ) (he : e ≠ 0) (c : ℝ) (hc : 0 < c) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) ∧
      ∀ t : ℤ, c ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heR : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hapos : 0 < ((r : ℝ) * c) ^ e := by positivity
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = ⌊((r : ℝ) * c) ^ e⌋ + 1 := ⟨_, rfl⟩
  have hTa : ((r : ℝ) * c) ^ e < (T : ℝ) := by
    rw [hT]; push_cast; exact Int.lt_floor_add_one _
  have hTpos : (0 : ℝ) < T := hapos.trans hTa
  have hupos : 0 < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) := by positivity
  have hue : ((2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c)) ^ e = 2 * (e : ℝ) ^ e / ((r : ℝ) * c) ^ e := by
    rw [div_pow, mul_pow, one_div, Real.rpow_inv_natCast_pow (by norm_num) he]
  have hv0 : 0 ≤ (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) := by positivity
  have hve : ((2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹)) ^ e = 2 * (e : ℝ) ^ e / T :=
    Real.rpow_inv_natCast_pow (by positivity) he
  have hvu : (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) := by
    rw [← pow_lt_pow_iff_left₀ hv0 hupos.le he, hve, hue]
    exact div_lt_div_of_pos_left (by positivity) hapos hTa
  obtain ⟨q, hvq, hqu⟩ := exists_rat_btwn hvu
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt hv0 hvq
  refine ⟨q, by exact_mod_cast hq0, hqu, ?_⟩
  intro t ht
  have hct : c ^ e * (r : ℝ) ^ e < t := (lt_div_iff₀ (by positivity)).1 ht
  have hat : ((r : ℝ) * c) ^ e < t := by
    calc ((r : ℝ) * c) ^ e = c ^ e * (r : ℝ) ^ e := by rw [mul_pow, mul_comm]
      _ < t := hct
  have hTt : (T : ℝ) ≤ t := by
    have h1 := Int.floor_lt.2 hat
    have : T ≤ t := by omega
    exact_mod_cast this
  have key : 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * t := by
    have h1 := pow_lt_pow_left₀ hvq hv0 he
    rw [hve, div_lt_iff₀ hTpos] at h1
    calc 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * T := h1
      _ ≤ (q : ℝ) ^ e * t := mul_le_mul_of_nonneg_left hTt (by positivity)
  exact_mod_cast key

theorem exists_rat_budgets : ∀ (n r : ℕ) (c : ℕ → ℝ), 0 < r → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
    ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 →
    ∃ (h : ℕ → ℚ), (∀ e, 0 < h e) ∧ ∑ e ∈ Finset.Icc 1 n, h e < 1 / (r : ℚ) ∧
      ∀ e ∈ Finset.Icc 1 n, ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e →
        2 * (e : ℚ) ^ e < h e ^ e * t := by
  intro n r c hr hc hsum
  have hex : ∀ e, ∃ q : ℚ, 0 < q ∧ (e ∈ Finset.Icc 1 n →
      (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) ∧
      ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t) := by
    intro e
    by_cases he : e ∈ Finset.Icc 1 n
    · have he0 : e ≠ 0 := by
        have := (Finset.mem_Icc.1 he).1
        omega
      obtain ⟨q, hq0, hqu, hqt⟩ := exists_rat_budget_term r hr e he0 (c e) (hc e he)
      exact ⟨q, hq0, fun _ => ⟨hqu, hqt⟩⟩
    · exact ⟨1, one_pos, fun h => absurd h he⟩
  choose h hpos hprop using hex
  refine ⟨h, hpos, ?_, fun e he => (hprop e he).2⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hR : ∑ e ∈ Finset.Icc 1 n, (h e : ℝ) < 1 / (r : ℝ) := by
    rcases (Finset.Icc 1 n).eq_empty_or_nonempty with hE | hE
    · rw [hE, Finset.sum_empty]; positivity
    · calc ∑ e ∈ Finset.Icc 1 n, (h e : ℝ)
          < ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) :=
            Finset.sum_lt_sum_of_nonempty hE (fun e he => (hprop e he).1)
        _ = 1 / (r : ℝ) * ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun e _ => by ring
        _ ≤ 1 / (r : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 / (r : ℝ) := mul_one _
  have hR' : ((∑ e ∈ Finset.Icc 1 n, h e : ℚ) : ℝ) < ((1 / (r : ℚ) : ℚ) : ℝ) := by
    push_cast; exact hR
  exact Rat.cast_lt.mp hR'

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealOneParamProductChartAdelicUnitary
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.UnitChart

open GlobalTheory.Orb (archMat)

def lieU {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * H + H * X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hX, smul_zero]

theorem exists_realLines_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) ∧
      ∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u := by
  intro F E _ _ _ _ _ σ h n J hJ
  classical
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.choice inferInstance
  let H : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ := fun w => J.map (τ w).1
  have hHu : ∀ w, IsUnit (H w).det := fun w => by
    show IsUnit (J.map (τ w).1).det
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hHh : ∀ w, (H w)ᴴ = H w := fun w => by
    ext i k
    simp only [H, conjTranspose_apply, map_apply]
    rw [← h.2.2.2, hJ.1 i k]
  let e : InfinitePlace F → ℕ := fun w => Module.finrank ℝ (lieU (H w))
  let b : ∀ w, Module.Basis (Fin (e w)) ℝ (lieU (H w)) := fun w => Module.finBasis ℝ _
  let q : (Σ w : InfinitePlace F, Fin (e w)) ≃ Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) :=
    Fintype.equivFin _
  let Zg : Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → Matrix (Fin n) (Fin n) ℂ :=
    fun a => (b (q.symm a).1 (q.symm a).2 : Matrix (Fin n) (Fin n) ℂ)
  have hZg : ∀ a, (Zg a)ᴴ * H (q.symm a).1 + H (q.symm a).1 * Zg a = 0 := fun a => (b (q.symm a).1 (q.symm a).2).2
  have hy : ∀ a (t : ℝ), ∃ y : GArch σ J (q.symm a).1,
      archMat σ J (τ (q.symm a).1) y = NormedSpace.exp (t • Zg a) := fun a t => by
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Zg a)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (hHu (q.symm a).1) (X := t • Zg a) ((lieU (H (q.symm a).1)).smul_mem t (hZg a))
    refine ⟨(archEquiv J h (τ (q.symm a).1)).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose y hy using hy
  let δ : Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → ℝ → GAd σ J :=
    fun a t => embArch σ J (q.symm a).1 (y a t)
  let Zw : InfinitePlace F → Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → Matrix (Fin n) (Fin n) ℂ :=
    fun w a => if (q.symm a).1 = w then Zg a else 0
  have hK : ∀ w a (t : ℝ), archMat σ J (τ w) (projArch σ J w (δ a t)) = NormedSpace.exp (t • Zw w a) := by
    intro w a t
    by_cases hw : (q.symm a).1 = w
    · subst hw
      simp only [δ, Zw, if_pos rfl, projArch_embArch_self, hy]
    · simp only [δ, Zw, if_neg hw, smul_zero, NormedSpace.exp_zero, projArch_embArch_ne σ J (Ne.symm hw), map_one]
  have hunit : ∀ w (g : GArch σ J w), (archMat σ J (τ w) g)ᴴ * H w * archMat σ J (τ w) g = H w := fun w g => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact (archEquiv J h (τ w) g).2
  have hinj : ∀ w, Function.Injective (archMat σ J (τ w)) := fun w g g' hg =>
    (archEquiv J h (τ w)).injective (Subtype.ext (Units.ext (by
      rwa [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at hg)))
  have hloc : ∀ w, ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin _ → ℝ),
      ContinuousAt s 1 ∧ ∀ g ∈ V, gᴴ * H w * g = H w → g = (List.ofFn fun a => NormedSpace.exp (s g a • Zw w a)).prod := by
    intro w
    have hj : Function.Injective fun i : Fin (e w) => q ⟨w, i⟩ := fun i i' hi => by
      simpa using q.injective hi
    have hZj : ∀ i, Zw w (q ⟨w, i⟩) = (b w i : Matrix (Fin n) (Fin n) ℂ) := fun i => by
      show (if (q.symm (q ⟨w, i⟩)).1 = w then Zg (q ⟨w, i⟩) else 0) = _
      rw [if_pos (by simp)]
      show ((b (q.symm (q ⟨w, i⟩)).1 (q.symm (q ⟨w, i⟩)).2 : Matrix (Fin n) (Fin n) ℂ)) = _
      rw [q.symm_apply_apply]
    refine _root_.GlobalTheory.UnitaryGroupChart.unitary_chart n (H w) (hHh w) (hHu w) _ (e w) (Zw w) (fun i => q ⟨w, i⟩) hj ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Zw]
      rw [if_neg]
      intro hw
      apply ha
      rcases hqa : q.symm a with ⟨w', i⟩
      rw [hqa] at hw
      subst hw
      have h2 := congrArg q hqa
      rw [Equiv.apply_symm_apply] at h2
      exact ⟨i, h2.symm⟩
    · intro a
      simp only [Zw]
      split_ifs with hw
      · subst hw; exact hZg a
      · simp
    · simp only [hZj]
      refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
      refine Fintype.linearIndependent_iff.1 (b w).linearIndependent c (Subtype.ext ?_) i
      simpa using hc
    · intro X hX
      simp only [hZj]
      have e1 := congrArg Subtype.val ((b w).sum_repr ⟨X, hX⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e1
      rw [← e1]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose V hV sw hsw hdec using hloc
  let gw : InfinitePlace F → GAd σ J → Matrix (Fin n) (Fin n) ℂ := fun w x => archMat σ J (τ w) (projArch σ J w x)
  have hgc : ∀ w, Continuous (gw w) := fun w =>
    (GlobalTheory.Orb.continuous_archMat σ J (τ w)).comp (continuous_projArch σ J w)
  have hg1 : ∀ w, gw w 1 = 1 := fun w => by simp [gw]
  refine ⟨_, δ, fun a => ⟨(q.symm a).1, τ _, Zg a, hZg a, fun t => ⟨y a t, rfl, hy a t⟩⟩, fun U hU => ?_⟩
  have hfc : Continuous fun x => ofFin σ J (projFin σ J x) := (continuous_ofFin σ J).comp (continuous_projFin σ J)
  refine ⟨{x | ∀ w, gw w x ∈ V w} ∩ {x | ofFin σ J (projFin σ J x) ∈ U}, ?_,
    fun x a => sw (q.symm a).1 (gw (q.symm a).1 x) a, ?_, ?_⟩
  · refine Filter.inter_mem (Filter.eventually_all.2 fun w => (hgc w).continuousAt.preimage_mem_nhds ?_)
      (hfc.continuousAt.preimage_mem_nhds ?_)
    · rw [hg1]; exact hV w
    · simpa using hU
  · exact continuousAt_pi.2 fun a =>
      (continuous_apply a).continuousAt.comp ((hsw _).comp_of_eq (hgc _).continuousAt (hg1 _))
  · intro x hx
    refine ⟨ofFin σ J (projFin σ J x), hx.2, mem_finPts.2 (projInf_ofFin _ _ _), ?_⟩
    conv_lhs => rw [← ofInf_projInf_mul_ofFin_projFin σ J x]
    congr 1
    apply GAd_ext σ J
    · intro w
      apply hinj w
      rw [projArch_ofInf, projInfArch_projInf, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      have e2 : (⇑(archMat σ J (τ w)) ∘ ⇑(projArch σ J w) ∘ fun a => δ a (sw (q.symm a).1 (gw (q.symm a).1 x) a)) =
          fun a => NormedSpace.exp (sw w (gw w x) a • Zw w a) := funext fun a => by
        simp only [Function.comp_apply]
        rw [hK]
        by_cases hw : (q.symm a).1 = w
        · subst hw; rfl
        · simp [Zw, hw]
      rw [e2]
      exact hdec w _ (hx.1 w) (hunit w _)
    · intro v
      rw [proj_ofInf, map_list_prod, List.map_ofFn]
      have e3 : (⇑(proj σ J v) ∘ fun a => δ a (sw (q.symm a).1 (gw (q.symm a).1 x) a)) = fun _ => 1 :=
        funext fun a => by simp [δ]
      rw [e3]
      simp

end GlobalTheory.UnitChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueToComplexOfRationalResidue
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem exists_residue_complex : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K) (h : IsLocModel (algebraMap ℂ K) R),
  RatRes (algebraMap ℂ K) R →
  ∃ ε : R →+* ℂ, (∀ a : ℂ, ε ⟨algebraMap ℂ K a, h.const_mem a⟩ = a) ∧ ∀ r : R, ε r = 0 ↔ NonUnit R (r : K) := by
  intro K _ _ R h hr
  haveI := h.isLocalRing
  let c0 : ℂ →+* R := (algebraMap ℂ K).codRestrict R h.const_mem
  let φ : ℂ →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp c0
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun y => ?_⟩
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := hr r r.2
    refine ⟨a, ?_⟩
    have hn : NonUnit R ((r - c0 a : R) : K) := by simpa [c0] using ha
    have hm : r - c0 a ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).2 ((nonUnit_iff (R := R) (r - c0 a)).1 hn)
    have := (IsLocalRing.residue_eq_zero_iff (r - c0 a)).2 hm
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  let e := RingEquiv.ofBijective φ hφ
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue R), fun a => ?_, fun r => ?_⟩
  · show e.symm (φ a) = a
    exact e.symm_apply_apply a
  · rw [nonUnit_iff (R := R) r, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_eq_zero_iff _ e.symm.injective, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenVar
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open scoped TensorProduct

namespace GlobalTheory.GenericMember

noncomputable def genVar (k : Type) [Field k] (N : ℕ) {X' : Scheme.{0}}
    (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (i : Fin N) : Γ(X', ⊤) :=
  f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (MvPolynomial (Fin N) k)))).inv
    (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i)))

noncomputable def genSec (k : Type) [Field k] (N : ℕ) {X X' : Scheme.{0}}
    (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X)
    (b : Fin N → L.Sec) : (L.pull π).Sec :=
  ∑ i, genVar k N f' i • secPull (b i) π

end GlobalTheory.GenericMember
end

