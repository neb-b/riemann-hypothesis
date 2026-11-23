module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0019
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AutSubApplyMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowersEqInv

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.NMPseudoOf
section
open NumberField Module IsDedekindDomain Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

theorem nMPseudo_of (hE : JordanExists) (hD : DetLocal) (hC : CountExt) (hA : NormAssembly) : NMPseudo := by
  intro K F V ι _ _ _ _ _ _ _ _ _ _ _ _ _ h X x 𝔞 hcm hfix h2 hsymm hstar hne hind hspan hdet hint
  have hJ0 : (∏ i, 𝔞 i ^ 2) * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hne i))
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdet)
  have key : ∀ (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)), 𝔭.IsMaximal →
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          ((P.asIdeal.ramificationIdx (𝓞 F) * vJ h X (pbLat x 𝔞) 𝔭 : ℕ) : ℤ) := by
    intro 𝔭 P h𝔭 hP
    obtain ⟨b, a, hba⟩ := hE K F V ι h X x 𝔞 hcm hfix h2 hsymm hstar hne hind hspan hdet hint 𝔭 h𝔭
    have hcount : ∀ b' a', IsJordanIn h X (pbLat x 𝔞) 𝔭 b' a' →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          ((P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a' : ℕ) : ℤ) := by
      intro b' a' h'
      rw [hD K F V ι h X x 𝔞 hfix hstar hne hind hspan hdet 𝔭 b' a' h𝔭 h' P hP,
        hC K F _ 𝔭 P a' h𝔭 hP h'.2.2.2.2]
      rfl
    have he : P.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := by
      haveI := P.isPrime
      exact (Ideal.ramificationIdx_pos (R := 𝓞 F) P.asIdeal).ne'
    have hv : vJ h X (pbLat x 𝔞) 𝔭 = vJof 𝔭 a := by
      unfold vJ
      have hset : {v | ∃ b a, IsJordanIn h X (pbLat x 𝔞) 𝔭 b a ∧ v = vJof 𝔭 a} = {vJof 𝔭 a} := by
        ext v
        constructor
        · rintro ⟨b', a', h', rfl⟩
          have h3 := (hcount b' a' h').symm.trans (hcount b a hba)
          have h4 : P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a' = P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a := by
            exact_mod_cast h3
          exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) h4
        · rintro rfl
          exact ⟨b, a, hba, rfl⟩
      rw [hset, csInf_singleton]
    rw [hv]
    exact hcount b a hba
  exact hA K F h2 _ (vJ h X (pbLat x 𝔞)) hJ0 key

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeMapExtension
section
open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

namespace OrbitSumPf

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

def split (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (hz0 : h1 z z ≠ 0) : VecSplit h1 (hPerp h1 z) where
  x₀ := z
  ι := (wPerp h1 z).subtype
  inj := Subtype.val_injective
  hx₀ := hz0
  isom := fun _ _ => rfl
  orth := fun a => a.2
  cover := fun v => ⟨h1 z v / h1 z z, ⟨v - (h1 z v / h1 z z) • z, by
      show h1 z (v - (h1 z v / h1 z z) • z) = 0
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hz0, sub_self]⟩, by simp⟩

variable {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1}

theorem mul_mem_hz {σ τ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) (hτ : τ ∈ hz h1 z) : σ * τ ∈ hz h1 z := by
  simp only [hz, Set.mem_setOf_eq] at *
  refine ⟨mul_mem hσ.1 hτ.1, ?_⟩
  show σ (τ z) = z
  rw [hτ.2, hσ.2]

theorem inv_mem_hz {σ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) : σ⁻¹ ∈ hz h1 z := by
  simp only [hz, Set.mem_setOf_eq] at *
  refine ⟨inv_mem hσ.1, ?_⟩
  show σ.symm z = z
  rw [LinearEquiv.symm_apply_eq, hσ.2]

variable (hz0 : h1 z z ≠ 0)

private theorem gmap_mul_lemma {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (a b : W ≃ₗ[K] W) (N : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.gmap (a * b) N = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b N) := by
  simp only [Formalism.HermitianLatticesTheory.gmap, ← Submodule.map_comp]
  rfl

theorem gmap_inv_gmap' {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (a : W ≃ₗ[K] W) (N : Submodule (𝓞 K) W) : Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a N) = N := by
  rw [← gmap_mul_lemma, inv_mul_cancel]
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem card_stabZ_conj {τ : V1 ≃ₗ[K] V1} (hτ : τ ∈ hz h1 z) (M : Submodule (𝓞 K) V1) :
    Nat.card (stabZ h1 z (Formalism.HermitianLatticesTheory.gmap τ M)) = Nat.card (stabZ h1 z M) := by
  apply Nat.card_congr
  refine
    { toFun := fun σ => ⟨τ⁻¹ * σ.1 * τ, ?_⟩
      invFun := fun σ => ⟨τ * σ.1 * τ⁻¹, ?_⟩
      left_inv := fun σ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun σ => Subtype.ext (by simp [mul_assoc]) }
  · obtain ⟨a1, a2⟩ := σ.2
    exact ⟨mul_mem_hz (mul_mem_hz (inv_mem_hz hτ) a1) hτ, by
      rw [gmap_mul_lemma, gmap_mul_lemma, a2, gmap_inv_gmap']⟩
  · obtain ⟨a1, a2⟩ := σ.2
    refine ⟨mul_mem_hz (mul_mem_hz hτ a1) (inv_mem_hz hτ), ?_⟩
    rw [gmap_mul_lemma, gmap_mul_lemma, gmap_inv_gmap', a2]

end OrbitSumPf

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ProdAbsNormDifferentIdealPowers
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical ValuativeRel

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gZ_ne_zero (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D)
    (hpos : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ T T' Z)) : GZ T T' Z ≠ 0 := by
  intro h0
  have hc : 0 < Fintype.card D.what₂.Tau := by
    rw [D.what₂.card_Tau]
    have := D.R.m_le_f
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    omega
  obtain ⟨τ⟩ := Fintype.card_pos_iff.mp hc
  have := hpos τ
  rw [h0, map_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem gS_ne_zero (D : Formalism.BasicNotions.D7) : ((gS D : D.host.E)) ≠ 0 := by
  have h1 := (D.host.g_prime 0).pos
  have h2 := (D.host.g_prime 1).pos
  unfold gS
  exact_mod_cast (Nat.mul_pos h1 h2).ne'

theorem prod_tri {c : ℚ} (hc : c ≠ 0) :
    ∀ n : ℕ, (∏ a : Fin n, c ^ (-((n : ℤ) - (a : ℕ)))) ^ 2 = c ^ (-((n * (n + 1) : ℕ) : ℤ))
  | 0 => by simp
  | n + 1 => by
    rw [Fin.prod_univ_succ, mul_pow]
    have h1 : ∀ a : Fin n, c ^ (-(((n + 1 : ℕ) : ℤ) - ((a.succ : Fin (n + 1)) : ℕ))) =
        c ^ (-((n : ℤ) - (a : ℕ))) := by
      intro a
      congr 1
      simp only [Fin.val_succ]
      push_cast
      ring
    simp only [h1, prod_tri hc n, Fin.val_zero]
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hc]
    congr 1
    push_cast
    ring

theorem prod_absNorm_differentIdealPowers (D : Formalism.BasicNotions.D7) :
    (∏ a : Fin (D.R.rS + 1), FractionalIdeal.absNorm (differentIdealPowers D a)) ^ 2 =
      (((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ^ (-((D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) := by
  have hd : (((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ≠ 0 := by
    have := NumberField.discr_ne_zero D.host.F
    positivity
  rw [Fin.prod_univ_castSucc]
  simp only [differentIdealPowers, Fin.snoc_castSucc, Fin.snoc_last, map_one, mul_one, map_zpow₀, absNorm_ddS]
  exact prod_tri hd D.R.rS

theorem abs_norm_negOnePow {K : Type} [Field K] [NumberField K] (k : ℕ) (y : K) :
    |(Algebra.norm ℚ ((-1) ^ k * y) : ℚ)| = |(Algebra.norm ℚ y : ℚ)| := by
  rw [map_mul, map_pow, abs_mul, abs_pow]
  have h1 : |(Algebra.norm ℚ (-1 : K) : ℚ)| = 1 := by
    have h2 : (Algebra.norm ℚ (-1 : K)) * (Algebra.norm ℚ (-1 : K)) = 1 := by
      rw [← map_mul]; simp
    have h3 : |(Algebra.norm ℚ (-1 : K) : ℚ)| * |(Algebra.norm ℚ (-1 : K) : ℚ)| = 1 := by
      rw [← abs_mul, h2, abs_one]
    nlinarith [abs_nonneg (Algebra.norm ℚ (-1 : K) : ℚ)]
  rw [h1, one_pow, one_mul]

theorem normMM_of (hN : NMPseudo) (hM : MMPseudo) (hΔ : DetGa) : NormMM := by
  intro D u u' hc F0 what₂ hr Z F' hz hZ hpos hint
  have hMM := hM D u u' hc F0 what₂ hr Z F' hz hZ hpos hint
  rw [hMM] at hint ⊢
  obtain ⟨hcm, hfix, -⟩ := field_dictionary_holds D
  have hG := gZ_ne_zero D _ _ Z hpos
  have hg := gS_ne_zero D
  have hdetGa := hΔ D (Tn u) (Tn u') (star_natCast _) (star_natCast _) Z
  have hdet := det_gram_flagDifference F0 F' Z hZ
  rw [hdetGa] at hdet
  have hdet0 : (gram (VS D).hT (flagDifferenceVectors D F0 F')).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hg)) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hG)
  have hstar : ∀ i, ∀ a ∈ ((Sum.elim (differentIdealPowers D) (differentIdealPowers D) i : FractionalIdeal _ _) : Submodule (𝓞 D.host.E) D.host.E),
      star a ∈ ((Sum.elim (differentIdealPowers D) (differentIdealPowers D) i : FractionalIdeal _ _) : Submodule (𝓞 D.host.E) D.host.E) := by
    rintro (a | a) <;> exact stable_differentIdealPowers D a
  have hne : ∀ i, (Sum.elim (differentIdealPowers D) (differentIdealPowers D) i) ≠ 0 := by
    rintro (a | a) <;> exact differentIdealPowers_ne_zero D a
  have hsq := hN D.host.E D.host.F (VS D).V _ (VS D).hT (UPair D F0 F') (flagDifferenceVectors D F0 F')
    (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) hcm hfix D.sp.cm.deg2 (VS D).herm hstar hne
    (linearIndependent_of_det_gram _ _ hdet0) (span_flagDifferenceBasis F0 F') hdet0 hint

  have hm : D.R.m = 2 * (D.R.rS + 1) := by
    have h2 := D.R.two_le_m
    obtain ⟨a, ha⟩ := D.R.m_even
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hy : (gram (VS D).hT (flagDifferenceVectors D F0 F')).det = (-1) ^ (D.R.rS + 1) * (GZ (Tn u) (Tn u') Z / ((gS D : D.host.E) ^ D.R.m)) := by
    rw [hdet, hm, div_eq_mul_inv, ← inv_pow]
    ring
  have hN2 : (FractionalIdeal.absNorm ((∏ i, (Sum.elim (differentIdealPowers D) (differentIdealPowers D) i) ^ 2) *
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (gram (VS D).hT (flagDifferenceVectors D F0 F')).det) : ℝ) =
      ((((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ^ (-((D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) : ℚ) ^ 2 *
        |(Algebra.norm ℚ (GZ (Tn u) (Tn u') Z / ((gS D : D.host.E) ^ D.R.m)) : ℚ)| := by
    rw [map_mul, FractionalIdeal.absNorm_span_singleton, hy, abs_norm_negOnePow, map_prod,
      Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, map_pow]
    rw [Finset.prod_pow, ← prod_absNorm_differentIdealPowers D]
    push_cast
    ring
  have hnm0 : 0 ≤ nM D.host.F (VS D).hT (UPair D F0 F') (pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D))) :=
    tprod_nonneg fun _ => by positivity
  have hr0 : 0 ≤ |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) *
      sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z := by
    unfold sqrtAbsNormOfScaledGram; positivity
  refine (pow_left_inj₀ hnm0 hr0 two_ne_zero).mp ?_
  rw [hsq, hN2, mul_pow]
  unfold sqrtAbsNormOfScaledGram
  rw [Real.sq_sqrt (abs_nonneg _)]
  congr 1
  have hcast : (((NumberField.discr D.host.F).natAbs : ℕ) : ℝ) = |(NumberField.discr D.host.F : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  push_cast
  rw [hcast]
  have e1 : (|(NumberField.discr D.host.F : ℝ)| ^ 2) ^ (-((D.R.rS : ℤ) * (D.R.rS + 1))) =
      |(NumberField.discr D.host.F : ℝ)| ^ (-(2 * (D.R.rS : ℤ) * (D.R.rS + 1))) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [e1]
  exact Rat.cast_abs _

theorem normMM_of_NM (hN : NMPseudo) : NormMM :=
  normMM_of hN mass_pseudo_basis gram_determinant_formula_alt

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.VFEqEmultiplicity
section
open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem vF_eq_emultiplicity {F : Type} [Field F] [NumberField F] (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsPrime)
    (h0 : 𝔭 ≠ ⊥) (α : 𝓞 F) (hα : α ≠ 0) :
    ((vF 𝔭 α : ℕ) : ℕ∞) = emultiplicity 𝔭 (Ideal.span {α}) := by
  have hs : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hfm : FiniteMultiplicity 𝔭 (Ideal.span {α}) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime h0 h𝔭) hs
  rw [hfm.emultiplicity_eq_multiplicity]
  congr 1
  unfold vF
  have hset : {e : ℕ | α ∈ 𝔭 ^ e} = Set.Iic (multiplicity 𝔭 (Ideal.span {α})) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [← hfm.pow_dvd_iff_le_multiplicity, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [hset, csSup_Iic]

end

theorem countExt_single (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)) (α : 𝓞 F) (h𝔭 : 𝔭.IsMaximal)
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭) (hα : α ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (α : F))) =
      ((P.asIdeal.ramificationIdx (𝓞 F) * vF 𝔭 α : ℕ) : ℤ) := by
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  haveI : P.asIdeal.LiesOver 𝔭 := ⟨by rw [Ideal.under_def, hP]⟩
  set β : 𝓞 K := algebraMap (𝓞 F) (𝓞 K) α
  have hβ : β ≠ 0 := by
    intro h
    apply hα
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (by rw [map_zero]; exact h)
  have hsβ : Ideal.span {β} ≠ ⊥ := by simpa using hβ
  have hsα : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hK : algebraMap F K (α : F) = algebraMap (𝓞 K) K β := rfl
  rw [hK, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K P hsβ,
    Ideal.count_associates_factors_eq hsβ P.isPrime P.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hsβ P]
  congr 1
  have hfmP : FiniteMultiplicity P.asIdeal (Ideal.span {β}) :=
    FiniteMultiplicity.of_prime_left P.prime hsβ
  have hmap : Ideal.span {β} = (Ideal.span {α}).map (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have he := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hsα
    (Ideal.prime_of_isPrime h0 h𝔭.isPrime).irreducible P.irreducible P.ne_bot
  rw [← hmap, hfmP.emultiplicity_eq_multiplicity, ← vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 α hα,
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔭 P.asIdeal h0] at he
  exact_mod_cast he

theorem count_extension : CountExt := by
  intro K F _ _ _ _ _ n 𝔭 P α h𝔭 hP hα
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hprod : (∏ j, ((α j : 𝓞 F) : F)) = ((∏ j, α j : 𝓞 F) : F) := by simp
  have hne : (∏ j, α j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hα j
  rw [hprod, countExt_single K F 𝔭 P _ h𝔭 hP hne]
  congr 2
  have key : ((vF 𝔭 (∏ j, α j) : ℕ) : ℕ∞) = ((∑ j, vF 𝔭 (α j) : ℕ) : ℕ∞) := by
    rw [vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 _ hne, ← Ideal.prod_span_singleton, Nat.cast_sum]
    rw [Finset.emultiplicity_prod (Ideal.prime_of_isPrime h0 h𝔭.isPrime)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 _ (hα j)]
  exact_mod_cast key

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

