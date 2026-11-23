module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeEqSteinitzFormCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0462
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsMultiplicativeGroup
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIsAlgebraicOfEllipticCMTheorems
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open GlobalTheory.HilbFam GlobalTheory.QFam GlobalTheory.WpFam
open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.RoadELatAlg

theorem isAlgebraic_of_sq_eq_ratCast {x : ℂ} (q : ℚ) (h : x ^ 2 = (q : ℂ)) : IsAlgebraic ℚ x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C q, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (by norm_num) q
  · simp [h]

theorem exists_theta {K : Type} [Field K] [NumberField K] (ι : K →+* ℂ) (Λ : PeriodPair)
    (hΛ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ) (c : ℂ) (τ : ℍ) (hτ : IsTauOf Λ c τ) :
    ∃ θ : K, ι θ = (τ : ℂ) ∧ IsAlgebraic ℚ c := by
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice → ∃ a : K, ι a = z := by
    intro z hz
    have : z ∈ (Λ.lattice : Set ℂ) := hz
    rw [hΛ] at this
    obtain ⟨a, -, ha⟩ := this
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hmem c ((hτ.2 c).2 ⟨0, 1, by simp⟩)
  obtain ⟨b, hb⟩ := hmem (c * τ) ((hτ.2 _).2 ⟨1, 0, by simp⟩)
  have hc : c ≠ 0 := hτ.1
  refine ⟨b / a, ?_, ?_⟩
  · rw [map_div₀, ha, hb]; field_simp
  · rw [← ha]; exact (Algebra.IsAlgebraic.isAlgebraic a).algHom ι.toRatAlgHom

theorem term_div_eq (r Y H ω : ℂ) (a w W : ℕ) (h : W = 2 * a + w) :
    r * Y ^ a * H / ω ^ W = r * ((Y / ω ^ 2) ^ a * (H / ω ^ w)) := by
  subst h
  rw [pow_add, pow_mul, div_pow]
  ring

theorem coord_id (c0 S0 D Ω c cW P pi im r p sg : ℂ) (W K : ℕ) (hsg : sg ≠ 0) (hD : D = cW * (sg * P) * S0)
    (hc0 : c0 = cW * P * (2 * pi / r) ^ K) (hΩ : Ω ≠ 0) (hc : c ≠ 0) (hp : p ≠ 0) (him : im ≠ 0) (hr : r ≠ 0) :
    c0 * S0 / Ω ^ W = sg⁻¹ * (2 * im / r) ^ K * c ^ W * (D * (pi / im) ^ K / p ^ W / (Ω * c / p) ^ W) := by
  have h2 : (2 * im / r) ^ K * (pi / im) ^ K = (2 * pi / r) ^ K := by
    rw [← mul_pow]; congr 1; field_simp
  have h3 : c ^ W / p ^ W / (Ω * c / p) ^ W = 1 / Ω ^ W := by
    rw [div_pow, mul_pow]; field_simp
  calc c0 * S0 / Ω ^ W = (sg⁻¹ * sg) * (cW * P * S0) * ((2 * im / r) ^ K * (pi / im) ^ K) *
        (c ^ W / p ^ W / (Ω * c / p) ^ W) := by
          rw [inv_mul_cancel₀ hsg, h2, h3, hc0]; ring
    _ = _ := by rw [hD]; ring

theorem latAlg_of_siegelKlingen : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation →
    GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatAlg := by
  intro hSKDR hPZ _ _
  intro K _ _ d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ s 𝔣 Q hDat κ y S hS
  classical
  obtain ⟨hUn, hCM, hφι, hs, h𝔣, hQ⟩ := hDat
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.two_le_finrank hUn
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hΩ0 : Ω₀ ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ₀ (by rw [← hΩ]; simp)
  have hW2 := _root_.GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe hPZ
  have hSt := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke hW2
  have hEis := _root_.GlobalTheory.HilbertEis.eisExp _root_.GlobalTheory.LipschitzTR.lipschitz hW2 hPZ
  obtain ⟨⟨z, hz⟩, -⟩ := GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet hSKDR E s hs
  obtain ⟨⟨g, hg⟩, hD⟩ := (((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1
  obtain ⟨u, hu⟩ := GlobalTheory.LatAlgebraic.exists_list_count κ
  have hDg := ((hD g hg).2 κ u hu).1 S hS
  obtain ⟨c, τ, hτ⟩ := latTau Λ₀
  obtain ⟨θ, hθτ, hcalg⟩ := exists_theta ι Λ₀ hΛ c τ hτ
  have hc : c ≠ 0 := hτ.1
  have hφθ : ∀ i, φ i (algebraMap K E θ) = (τ : ℂ) := by
    intro i; rw [← RingHom.comp_apply, hφι i, hθτ]
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeEmb.exists_equiv E I φ hCM
  have hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.card_eq_finrank hCM
  have hI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hI
  have hθF : algebraMap K E θ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) := by
    rintro ⟨x, hx⟩
    have h1 := he i₀ x
    change (x : E) = _ at hx
    rw [hx, hφθ i₀] at h1
    have h2 := congrArg Complex.im h1
    simp only [Complex.ofReal_im] at h2
    exact τ.im_pos.ne' h2
  obtain ⟨n, N, L, hn, hN, hN2, hL, hLΛ⟩ := GlobalTheory.RoadE.exists_level E (algebraMap K E θ) (condQ 𝔣 Q) y 2 hc0 hθF (by norm_num)
  have hN2' : 2 ≤ N := Nat.le_of_dvd hN hN2
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨by omega⟩
  let y₁ : Fin 2 → ZMod N := ![1, 0]
  have hy₁ : y₁ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [y₁] at this
  have hval := GlobalTheory.HilbFam.eValue_derivs hEis E I φ e (algebraMap K E θ) τ (lattice (condQ 𝔣 Q) y) L n s N g κ u
    (wB N y₁) hf2 hs hN hL he hφθ hn hLΛ hg hu
  obtain ⟨hωDD, hj, hG2, hwp⟩ := GlobalTheory.AlgTau.main K d δ ι 1 Λ₀ c Ω₀ τ hd hδ hΛ hτ hΩ

  set ω : ℂ := Ω₀ * c / (2 * Real.pi * Complex.I) with hω
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have hω0 : ω ≠ 0 := div_ne_zero (mul_ne_zero hΩ0 hc) h2piI
  have hH : ∀ μ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb (maximalRealSubfield E) → ℕ,
      IsAlgebraic ℚ (GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ / ω ^ GlobalTheory.HilbFam.wt (2 * s) μ) := by
    intro μ
    have h := GlobalTheory.QFam.fam_value_isAlgebraic (GL (Fin 2) (ZMod N)) (GlobalTheory.WpFam.gact N 1) (GlobalTheory.HilbFam.wt (2 * s) μ) N
      (fun α ↦ GlobalTheory.HilbFam.hfun (2 * s) (GlobalTheory.HilbFam.twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) μ (wB N (GlobalTheory.WpFam.vmul y₁ α)))
      τ ω (by omega) (((_root_.GlobalTheory.WpFam.Act.rightActions N).2.1 1).actBij)
      (GlobalTheory.HilbFam.isFam_hfun_GL hEis (maximalRealSubfield E) hf2 s N L hs hL y₁ μ)
      (fun α ↦ GlobalTheory.HilbFam.qAll_isAlgebraic_hfun_twist hEis (maximalRealSubfield E) hf2 s N L hs hL z hz μ y₁ hy₁ α)
      hj hωDD 1
    simpa only [Units.val_one, GlobalTheory.HilbFam.twist_one_of_hasLevel _ N L hL, (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.1] using h
  have hX : IsAlgebraic ℚ ((((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y₁ τ) / ω ^ 2) := by
    rw [GlobalTheory.wB_nonhol_correction, neg_div, add_div]
    exact ((hG2.add (hwp N y₁))).neg
  set f := Module.finrank ℚ (maximalRealSubfield E) with hf
  set k := ∑ i, κ i with hk
  set P : ℂ := 2 * Real.pi * Complex.I with hP
  set Y : ℂ := ((Real.pi / τ.im : ℝ) : ℂ) / P ^ 2 - wB N y₁ τ with hY
  set κ' : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb (maximalRealSubfield E) → ℕ := fun j ↦ κ (e.symm j) with hκ'
  have hsum' : ∑ j, κ' j = k := Equiv.sum_comp e.symm κ
  have hA : ∀ x : ℂ, IsAlgebraic ℚ x → x ∈ algebraicClosure ℚ ℂ := fun x h ↦ mem_algebraicClosure_iff.2 h

  have hRalg : IsAlgebraic ℚ (((n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ',
      ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) * Y ^ (∑ j, (κ' j - μ j)) *
        GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ) / ω ^ (2 * s * f + 2 * k)) := by
    have key : ((n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ',
        ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) * Y ^ (∑ j, (κ' j - μ j)) *
          GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ) / ω ^ (2 * s * f + 2 * k) =
        (n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ', ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) *
          ((Y / ω ^ 2) ^ (∑ j, (κ' j - μ j)) * (GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ / ω ^ GlobalTheory.HilbFam.wt (2 * s) μ)) := by
      rw [mul_div_assoc, Finset.sum_div]
      refine congrArg _ (Finset.sum_congr rfl fun μ hμ ↦ ?_)
      have hle : μ ≤ κ' := Finset.mem_Iic.1 hμ
      have hexp : 2 * s * f + 2 * k = 2 * (∑ j, (κ' j - μ j)) + GlobalTheory.HilbFam.wt (2 * s) μ := by
        have h1 : ∑ j, (κ' j - μ j) + ∑ j, μ j = ∑ j, κ' j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ ↦ Nat.sub_add_cancel (hle j)
        change 2 * s * f + 2 * k = 2 * (∑ j, (κ' j - μ j)) + (2 * s * f + 2 * ∑ j, μ j)
        omega
      exact term_div_eq _ _ _ _ _ _ _ hexp
    rw [key, ← mem_algebraicClosure_iff]
    refine mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun μ _ ↦ mul_mem (intCast_mem _ _)
      (mul_mem (pow_mem (hA _ hX) _) (hA _ (hH μ))))
  have hRalg' : IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ k / P ^ (2 * s * f + 2 * k) /
      ω ^ (2 * s * f + 2 * k)) := by
    rw [hval]; exact hRalg
  rw [Complex.ofReal_div] at hRalg'
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have him : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hcW : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt
      have h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
      exact mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos h1 _)
    exact_mod_cast this.ne'
  have hP' : (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j) :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => by positivity
    exact_mod_cast this.ne'
  have hsgn : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hC0 : ((C0 E d (2 * s) κ : ℝ) : ℂ) = (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) *
      (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ k := by
    rw [GlobalTheory.LatAlgebraic.cmPeriodConstant_eq_of_card_cmType hcard d s hs κ]; push_cast; ring
  rw [GlobalTheory.LatAlgebraic.risingFactor_eq] at hDg
  have key2 : GlobalTheory.ToricTransport.coordIn E d s κ Ω₀ (S 0) = ((-1 : ℂ) ^ k)⁻¹ *
      (2 * ((τ.im : ℝ) : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ k * c ^ (2 * s * f + 2 * k) *
      (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ((Real.pi : ℂ) / ((τ.im : ℝ) : ℂ)) ^ k / P ^ (2 * s * f + 2 * k) /
        ω ^ (2 * s * f + 2 * k)) := by
    rw [GlobalTheory.ToricTransport.coordIn, hcard]
    exact coord_id _ (S 0) (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0) Ω₀ c _ _ (Real.pi : ℂ) ((τ.im : ℝ) : ℂ)
      ((Real.sqrt d : ℝ) : ℂ) P ((-1 : ℂ) ^ k) (2 * s * f + 2 * k) k hsgn hDg hC0 hΩ0 hc h2piI him hsd
  have hτalg : IsAlgebraic ℚ (τ : ℂ) := by
    rw [← hθτ]; exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom ι.toRatAlgHom
  have hτc : IsAlgebraic ℚ (starRingEnd ℂ (τ : ℂ)) := by
    rw [← hθτ]; exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom ((starRingEnd ℂ).comp ι).toRatAlgHom
  have hIalg : IsAlgebraic ℚ Complex.I := isAlgebraic_of_sq_eq_ratCast (-1) (by simp [Complex.I_sq])
  have himalg : IsAlgebraic ℚ ((τ.im : ℝ) : ℂ) := by
    rw [← UpperHalfPlane.coe_im, Complex.im_eq_sub_conj, ← mem_algebraicClosure_iff]
    exact div_mem (sub_mem (hA _ hτalg) (hA _ hτc)) (mul_mem (ofNat_mem _ 2) (hA _ hIalg))
  have hsdalg : IsAlgebraic ℚ ((Real.sqrt d : ℝ) : ℂ) := by
    refine isAlgebraic_of_sq_eq_ratCast (d : ℚ) ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  rw [key2, ← mem_algebraicClosure_iff]
  exact mul_mem (mul_mem (mul_mem (inv_mem (pow_mem (neg_mem (one_mem _)) _))
    (pow_mem (div_mem (mul_mem (ofNat_mem _ 2) (hA _ himalg)) (hA _ hsdalg)) _)) (pow_mem (hA _ hcalg) _)) (hA _ hRalg')

end GlobalTheory.RoadELatAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LatDiv

variable {p : ℕ} [Fact p.Prime]

def intAf (p : ℕ) : AddSubgroup (AfP p) where
  carrier := {a | IsIntAf a}
  zero_mem' := fun v => by simp
  add_mem' := fun ha hb v => by
    rw [map_add]
    exact add_mem (ha v) (hb v)
  neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v)

def extF (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) : AfP p ⊗[ℚ] VQ D →ₗ[AfP p] AfP p :=
  LinearMap.liftBaseChange (AfP p)
    ((Algebra.linearMap ℚ (AfP p)) ∘ₗ LinearMap.liftBaseChange ℚ ((Algebra.linearMap ℤ ℚ) ∘ₗ f))

theorem extF_tmul (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) (a : AfP p) (x : D.La) :
    extF D f (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = a * ((f x : ℤ) : AfP p) := by
  simp [extF, LinearMap.liftBaseChange_tmul, Algebra.smul_def]

theorem extF_mem (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) {w : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) :
    extF D f w ∈ intAf p := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    intro v
    rw [extF_tmul, map_mul, map_intCast]
    exact mul_mem (ha v) (intCast_mem _ _)
  | zero => simpa using (intAf p).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem int_dvd (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) (x : D.La) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p)
    (w : AfP p ⊗[ℚ] VQ D) (hw : w ∈ LaHat D) (h : inAf D x = n • w) : (n : ℤ) ∣ f x := by
  have hb := extF_mem D f hw
  have e : ((f x : ℤ) : AfP p) = (n : AfP p) * extF D f w := by
    have := congrArg (extF D f) h
    rw [inAf, extF_tmul, _root_.one_mul, _root_.map_nsmul, nsmul_eq_mul] at this
    exact this
  set q : ℚ := (f x : ℚ) / n with hq
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hval : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, v.valuation ℚ q ≤ 1 := by
    intro v
    by_cases hv : v.asIdeal = Ideal.span {(p : ℤ)}
    · have h1 : v.valuation ℚ (n : ℚ) = 1 := by
        have : (n : ℚ) = algebraMap ℤ ℚ (n : ℤ) := by simp
        rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff, hv, Ideal.mem_span_singleton]
        intro hd
        have : (p : ℤ) ∣ (n : ℤ) := hd
        have h2 : p ∣ n := by exact_mod_cast this
        have h3 : p ∣ Nat.gcd n p := Nat.dvd_gcd h2 dvd_rfl
        rw [hnp] at h3
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
      have h2 : v.valuation ℚ ((f x : ℤ) : ℚ) ≤ 1 := by
        rw [← eq_intCast (algebraMap ℤ ℚ), IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact v.intValuation_le_one _
      rw [hq, map_div₀, h1, div_one]; exact h2
    · let v' : AwayP p := ⟨v, hv⟩
      have hbv := hb v'
      have e2 := congrArg (AfP.eval v') e
      rw [map_intCast, map_mul, map_natCast] at e2
      have hqv : algebraMap ℚ (v.adicCompletion ℚ) q = AfP.eval v' (extF D f w) := by
        have hn' : algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) ≠ 0 := (map_ne_zero _).2 hn0
        have : algebraMap ℚ (v.adicCompletion ℚ) q * algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) =
            ((f x : ℤ) : v.adicCompletion ℚ) := by
          rw [← map_mul, hq, div_mul_cancel₀ _ hn0, map_intCast]
        rw [← mul_left_inj' hn', this, e2, map_natCast]
        ring
      have hc : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
      rw [← hc, hqv]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hbv
  obtain ⟨k, hk⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q hval
  refine ⟨k, ?_⟩
  have : ((k : ℤ) : ℚ) = (f x : ℚ) / n := by rw [← eq_intCast (algebraMap ℤ ℚ)]; exact hk.trans hq
  have h4 : ((f x : ℤ) : ℚ) = ((n : ℤ) * k : ℤ) := by
    push_cast; rw [this]; field_simp
  exact_mod_cast h4

end GlobalTheory.LKGeo.LatDiv

namespace GlobalTheory.LKGeo.LatDiv

theorem eq_nsmul_of_inAf_eq_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (x : D.La) (n : ℕ), 0 < n → n.Coprime p →
    ∀ w ∈ LaHat D, inAf D x = n • w → ∃ z, x = n • z := by
  intro p _ D x n hn hnp w hw h
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hd : ∀ i, (n : ℤ) ∣ b.coord i x := fun i => int_dvd D (b.coord i) x n hn hnp w hw h
  choose c hc using hd
  refine ⟨∑ i, c i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : b.repr x i = (n : ℤ) * c i := hc i
  rw [this, mul_smul]
  exact Nat.cast_smul_eq_nsmul ℤ n _

end GlobalTheory.LKGeo.LatDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagSqAxes

theorem lift_mul_lift₂ {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x x' : T ⟶ A) (y y' : T ⟶ B) :
    lift x y * lift x' y' = lift (x * x') (y * y') := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem weilIs_one_of_gen {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) {N : ℕ} {T : Over S} {x y : T ⟶ A}
    (hx : x ^ N = 1) (hy : y ^ N = 1) : Out.WeilIs A L N x y 1 := by
  have hG := GlobalTheory.globalFns_holds
  have hM : (GlobalTheory.UU.trivRig A).L.IsLB := Out.Inh.trivLB_isLB _
  have h1 : Out.WeilIs A (GlobalTheory.UU.trivRig A).L N (x ≫ 𝟙 A) (y ≫ 𝟙 A) 1 := by
    rw [Category.comp_id, Category.comp_id]
    exact (GlobalTheory.UU.cubWeil_iff_weilIs (c := GlobalTheory.UU.trivCub A) hG hA hx hy 1).1 (GlobalTheory.UU.cubWeil_triv hx hy)
  have hw : LBIso (lbPow L 1) ((GlobalTheory.UU.trivRig A).L.pull (Over.Hom.left (𝟙 A))) :=
    LBIso.trans (GlobalTheory.isLB_lbPow hL 1) hL (pull_isLB hM _) (GlobalTheory.lbIso_lbPow_one hL)
      (GlobalTheory.ZH.AbelianFibre.lbIso_of_gens t ht (GlobalTheory.UU.unitGen _ _) (GlobalTheory.UU.unitGen_isGen _ _))
  have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hM (𝟙 A) hw h1
  simp only [Nat.cast_one, _root_.mul_one] at h2
  exact h2

theorem weilIs_axis {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB B.left} (hP : P.IsLB) (ψ : A ⟶ B) [IsMonHom ψ]
    (ht : ∃ t : (P.pull ψ.left).Gen, t.IsGen) (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N : ℕ)
    (hN : 0 < N) (hNk : (N : κ) ≠ 0) (a b : Over.mk y ⟶ A) (ha : a ^ N = 1) (hb : b ^ N = 1) :
    Out.WeilIs B P N (a ≫ ψ) (b ≫ ψ) 1 := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨t, ht⟩ := ht
  have hL : (P.pull ψ.left).IsLB := pull_isLB hP _
  have pa : (a ≫ ψ) ^ N = 1 := by rw [← MonObj.pow_comp, ha, MonObj.one_comp]
  have pb : (b ≫ ψ) ^ N = 1 := by rw [← MonObj.pow_comp, hb, MonObj.one_comp]
  obtain ⟨c', hc'⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S B P hB hP κ y N hN hNk _ _ pa pb
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hP ψ (GlobalTheory.lbIso_lbPow_one hL) hc'
  simp only [Nat.cast_one, _root_.mul_one] at h1
  have h2 := weilIs_one_of_gen hA hL t ht ha hb
  rwa [GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h1 h2] at hc'

end GlobalTheory.DiagSqAxes

namespace GlobalTheory.DiagSqAxes

theorem weilIs_diag_sq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N : ℕ), 0 < N → (N : κ) ≠ 0 → ∀ (a b : Over.mk y ⟶ A), a ^ N = 1 → b ^ N = 1 → ∀ (c : (Γ((Over.mk y).left, ⊤))ˣ), Out.WeilIs (G2 A) P N (lift a 1) (lift 1 b) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N a b (c ^ 2) := by
  intro S A _ _ hA P hP h₂ h₁ hsym κ _ _ y N hN hNk a b ha hb c hc
  have hG := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  have e11 : Out.WeilIs (G2 A) P N (lift a 1) (lift b 1) 1 := by
    have h := weilIs_axis hA hAA hP (lift (𝟙 A) (1 : A ⟶ A)) h₁ κ y N hN hNk a b ha hb
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using h
  have e22 : Out.WeilIs (G2 A) P N (lift 1 a) (lift 1 b) 1 := by
    have h := weilIs_axis hA hAA hP (lift (1 : A ⟶ A) (𝟙 A)) h₂ κ y N hN hNk a b ha hb
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using h
  have e21 : Out.WeilIs (G2 A) P N (lift 1 a) (lift b 1) c := by
    have hw : LBIso (lbPow P 1) (P.pull (lift (snd A A) (fst A A)).left) :=
      LBIso.trans (GlobalTheory.isLB_lbPow hP 1) hP (pull_isLB hP _) (GlobalTheory.lbIso_lbPow_one hP) hsym
    have h' : Out.WeilIs (G2 A) P N (lift 1 a ≫ lift (snd A A) (fst A A)) (lift b 1 ≫ lift (snd A A) (fst A A)) c := by
      simpa only [comp_lift, lift_fst, lift_snd] using hc
    have h := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hAA hP hP _ hw h'
    simp only [Nat.cast_one, _root_.mul_one] at h
    exact h
  have r1 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP e11 e21
  have r2 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP hc e22
  rw [lift_mul_lift₂] at r1 r2
  have s := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP (GlobalTheory.CommPairing.weilIs_symm hP r1)
    (GlobalTheory.CommPairing.weilIs_symm hP r2)
  have s' := GlobalTheory.CommPairing.weilIs_symm hP s
  rw [lift_mul_lift₂] at s'
  simp only [_root_.mul_one, _root_.one_mul] at s'
  have hd : Out.WeilIs (G2 A) P N (a ≫ lift (𝟙 A) (𝟙 A)) (b ≫ lift (𝟙 A) (𝟙 A)) (c ^ 2) := by
    simp only [comp_lift, Category.comp_id]
    convert s' using 1
    rw [← _root_.mul_inv, inv_inv, pow_two]
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have h := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hD hP (lift (𝟙 A) (𝟙 A)) (GlobalTheory.lbIso_lbPow_one hD) hd
  simp only [Nat.cast_one, _root_.mul_one] at h
  exact h

end GlobalTheory.DiagSqAxes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralOfRegularAtAllTraits
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem locInt_of_traitReg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (k : ℕ) (s : SecK L α k), TraitReg M G L s → LocInt M G L α t hpb.w s := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs
  have h4 := _root_.GlobalTheory.Mum.intAt_closed_of_traitReg R M G hsm hqc hgi L hL Y α t hpb k s hs
  have h5 := _root_.GlobalTheory.Mum.intAt_of_closedFibre R M G hsm hqc hgi L hL Y α t hpb k s h4
  intro j W U hW hWU hWa hUa
  exact _root_.GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart R M G hsm Y α t hpb W U hWU hWa hUa _
    (_root_.GlobalTheory.Mum.chartVal_isIntegral_of_intAt L α k s j W hW hWa (_root_.GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange R M G Y α t hpb W hWa) (fun x _ => h5 x))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqOfSeparableCommutantCommStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natDegree_minpoly_eq_of_separable_commutant_comm : ∀ (K : Type) [Field K] [IsAlgClosed K] (k : ℕ) (N : Matrix (Fin k) (Fin k) K), (minpoly K N).Separable → (∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B) → (minpoly K N).natDegree = k := by
  first | (exact @GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm) | (exact GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm) | (intros; apply GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm  <;> assumption)
end

