module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFourthProperty
section
open Polynomial

namespace GlobalTheory.CompanionTheory.UnitLattice

open PositivityTheory.Rg.Tf.Loc

variable {n : ℕ}

theorem mem_unitGL_of_integral {F : Type*} [Field F] [ValuativeRel F] (u : GL (Fin n) F)
    (h1 : ∀ i j, (u : Matrix (Fin n) (Fin n) F) i j ∈ intO F)
    (h2 : ∀ i j, ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F) :
    u ∈ unitGL (n := Fin n) F := by
  have hinj : Function.Injective ((intO F).subtype) := Subtype.val_injective
  let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, h2 i j⟩
  have hA : A.map (intO F).subtype = (u : Matrix (Fin n) (Fin n) F) := by
    ext i j; rfl
  have hB : B.map (intO F).subtype = ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    ext i j; rfl
  have hAB : A * B = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : B * A = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

theorem integral_of_mem_unitGL {F : Type*} [Field F] [ValuativeRel F] {u : GL (Fin n) F}
    (hu : u ∈ unitGL (n := Fin n) F) (i j : Fin n) :
    (u : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  obtain ⟨v, rfl⟩ := hu
  exact ((v : Matrix (Fin n) (Fin n) (intO F)) i j).2

theorem pow_entry_mem {F : Type*} [Field F] (S : Subring F) {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ i j, M i j ∈ S) (m : ℕ) : ∀ i j, (M ^ m) i j ∈ S := by
  induction m with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | succ m ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact S.sum_mem fun l _ => S.mul_mem (ih i l) (hM l j)

theorem aeval_entry_mem {F : Type*} [Field F] (S : Subring F) {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ i j, M i j ∈ S) {p : F[X]} (hp : ∀ i, p.coeff i ∈ S) (i j : Fin n) :
    (aeval M p) i j ∈ S := by
  rw [aeval_eq_sum_range, Matrix.sum_apply]
  refine S.sum_mem fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact S.mul_mem (hp l) (pow_entry_mem S hM l i j)

theorem conj_aeval {F : Type*} [Field F] (u : GL (Fin n) F) (M : Matrix (Fin n) (Fin n) F)
    (p : F[X]) :
    ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * aeval M p * (u : Matrix (Fin n) (Fin n) F) =
      aeval (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M * (u : Matrix (Fin n) (Fin n) F)) p := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.conj_pow', mul_smul_comm, smul_mul_assoc]

theorem conj_mem_unitGL {F : Type*} [Field F] [ValuativeRel F] {Γ c g : GL (Fin n) F} {p q : F[X]}
    (hp : (c : Matrix (Fin n) (Fin n) F) = aeval (Γ : Matrix (Fin n) (Fin n) F) p)
    (hpi : ∀ i, p.coeff i ∈ intO F)
    (hq : ((c⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = aeval (Γ : Matrix (Fin n) (Fin n) F) q)
    (hqi : ∀ i, q.coeff i ∈ intO F)
    (hΓ : g⁻¹ * Γ * g ∈ unitGL (n := Fin n) F) :
    g⁻¹ * c * g ∈ unitGL (n := Fin n) F := by
  have hent := integral_of_mem_unitGL hΓ
  simp only [Units.val_mul] at hent
  apply mem_unitGL_of_integral
  · intro i j
    simp only [Units.val_mul]
    rw [hp, conj_aeval]
    exact aeval_entry_mem _ hent hpi i j
  · intro i j
    have : (g⁻¹ * c * g)⁻¹ = g⁻¹ * c⁻¹ * g := by group
    rw [this]
    simp only [Units.val_mul]
    rw [hq, conj_aeval]
    exact aeval_entry_mem _ hent hqi i j

theorem conj_eq_of_commute {F : Type*} [Field F] {Γ c g : GL (Fin n) F} {p : F[X]}
    (hp : (c : Matrix (Fin n) (Fin n) F) = aeval (Γ : Matrix (Fin n) (Fin n) F) p)
    (hg : g * Γ = Γ * g) : g⁻¹ * c * g = c := by
  apply Units.ext
  have h1 : g⁻¹ * Γ * g = Γ := by rw [mul_assoc, ← hg]; group
  have h2 : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (Γ : Matrix (Fin n) (Fin n) F) *
      (g : Matrix (Fin n) (Fin n) F) = Γ := by
    have := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h1
    simpa only [Units.val_mul] using this
  simp only [Units.val_mul]
  rw [hp, conj_aeval, h2]

theorem twNorm_mem {G : Type*} [Group G] (θ : Monoid.End G) (K : Subgroup G)
    (hK : ∀ x ∈ K, θ x ∈ K) {u : G} (hu : u ∈ K) (m : ℕ) : twNorm θ m u ∈ K := by
  have hpow : ∀ i : ℕ, (θ ^ i) u ∈ K := by
    intro i
    induction i with
    | zero => simpa using hu
    | succ i ih => rw [pow_succ_apply']; exact hK _ ih
  induction m with
  | zero => simpa using K.one_mem
  | succ m ih => rw [twNorm_succ]; exact K.mul_mem ih (hpow m)

theorem exists_incl_of_fixed {k E : Type*} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (g : GL (Fin n) E)
    (hg : sigmaGL σ g = g) : ∃ y : GL (Fin n) k, incl y = g := by
  have hfix : ∀ x : E, σ x = x → ∃ a : k, algebraMap k E a = x := by
    intro x hx
    have hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact hx
    have hall : ∀ τ : E ≃ₐ[k] E, τ x = x := by
      intro τ
      have := (Subgroup.zpowers_le.mpr hσ) (hgen τ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    have := (IsGalois.mem_bot_iff_fixed x).mpr hall
    rwa [IntermediateField.mem_bot] at this
  have hent : ∀ (h : GL (Fin n) E), sigmaGL σ h = h → ∀ i j,
      σ ((h : Matrix (Fin n) (Fin n) E) i j) = (h : Matrix (Fin n) (Fin n) E) i j := by
    intro h hh i j
    have := congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E) i j) hh
    exact this
  have hg' : sigmaGL σ g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  choose A hA using fun i j => hfix _ (hent g hg i j)
  choose B hB using fun i j => hfix _ (hent g⁻¹ hg' i j)
  have hinj : Function.Injective (algebraMap k E) := (algebraMap k E).injective
  have hAm : (Matrix.of A).map (algebraMap k E) = (g : Matrix (Fin n) (Fin n) E) := by
    ext i j; exact hA i j
  have hBm : (Matrix.of B).map (algebraMap k E) = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    ext i j; exact hB i j
  have hAB : Matrix.of A * Matrix.of B = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hAm, hBm, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : Matrix.of B * Matrix.of A = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hAm, hBm, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨Matrix.of A, Matrix.of B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hAm

theorem sigmaGL_incl {k E : Type*} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E)
    (y : GL (Fin n) k) : sigmaGL σ (incl y) = incl y := by
  apply Units.ext
  ext i j
  exact σ.commutes _

theorem incl_injective {k E : Type*} [Field k] [Field E] [Algebra k E] :
    Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := by
  intro a b hab
  apply Units.ext
  apply Matrix.map_injective (algebraMap k E).injective
  exact congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E)) hab

theorem cstable_iff_and_twCent : D0a → A1 → L4 := by
  intro hD _ k E _ _ _ _ _ _ _ _ _ _ _ _ hur σ hgen n γ c _ hpc hqc hN
  obtain ⟨p, hp, hpi⟩ := hpc
  obtain ⟨q, hq, hqi⟩ := hqc
  have hσℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hσℓ, sigmaGL_one]
  have hstab : ∀ x ∈ unitGL (n := Fin n) E, sigmaGL σ x ∈ unitGL (n := Fin n) E :=
    fun x hx => ((hD k E hur σ hgen).2.2.2.1 σ n x).2 hx
  have hNc : twNorm (sigmaGL σ) (Module.finrank k E) c = incl γ := hN
  have hq' : (((c⁻¹)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p := by rw [inv_inv]; exact hp
  refine ⟨fun g => ⟨fun hu => ?_, fun h => ?_⟩, ?_⟩
  · have hγ : g⁻¹ * incl γ * g ∈ unitGL (n := Fin n) E := by
      have := twNorm_mem (sigmaGL σ) _ hstab hu (Module.finrank k E)
      rwa [twNorm_twConj_of_pow_eq_one _ hθ, hNc] at this
    refine ⟨?_, hγ⟩
    have hcg : g⁻¹ * c⁻¹ * g ∈ unitGL (n := Fin n) E := conj_mem_unitGL hq hqi hq' hpi hγ
    have he : g⁻¹ * sigmaGL σ g = (g⁻¹ * c⁻¹ * g) * twConj (sigmaGL σ) g c := by
      simp only [twConj]; group
    rw [he]
    exact mul_mem hcg hu
  · have hcg : g⁻¹ * c * g ∈ unitGL (n := Fin n) E := conj_mem_unitGL hp hpi hq hqi h.2
    have he : twConj (sigmaGL σ) g c = (g⁻¹ * c * g) * (g⁻¹ * sigmaGL σ g) := by
      simp only [twConj]; group
    rw [he]
    exact mul_mem hcg h.1
  · ext g
    constructor
    · intro hg
      have hcomm := twCent_commute_twNorm (sigmaGL σ) hθ c hg
      rw [hNc] at hcomm
      have hcg : g⁻¹ * c * g = c := conj_eq_of_commute hp hcomm
      have hg' : g⁻¹ * c * sigmaGL σ g = c := hg
      have hfix : sigmaGL σ g = g := by
        have h1 : g⁻¹ * c * sigmaGL σ g = g⁻¹ * c * g := by rw [hg', hcg]
        exact mul_left_cancel h1
      obtain ⟨y, rfl⟩ := exists_incl_of_fixed σ hgen g hfix
      refine ⟨y, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply incl_injective (E := E)
      rw [map_mul, map_mul]
      exact hcomm
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
      have hcomm : incl y * incl γ = (incl γ : GL (Fin n) E) * incl y := by
        rw [← map_mul, ← map_mul, hy]
      have hcg := conj_eq_of_commute hp hcomm
      show (incl y)⁻¹ * c * sigmaGL σ (incl y) = c
      rw [sigmaGL_incl, hcg]

end GlobalTheory.CompanionTheory.UnitLattice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSquareCongruenceConjugation
section
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.Twist

theorem block_twist {O L : Type} [CommRing O] [Field L] [Algebra O L] {n : ℕ} (ϖ : O) (w : L)
    (hw : w = algebraMap O L ϖ) (A B C D : Matrix (Fin n) (Fin n) O) :
    (fromBlocks A B (ϖ • C) D).map (algebraMap O L) *
        fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (w • 1) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (w • 1) *
        (fromBlocks A (ϖ • B) C D).map (algebraMap O L) := by
  subst hw
  rw [fromBlocks_map, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [smul_eq_mul] <;> simp [Algebra.smul_def]

theorem twist_gam : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ → ∀ γ ∈ Gam2 (n := n) ϖ,
      ∃ j' : GL (Ix n) O, inL γ * tauM w = tauM w * inL j' ∧ resK j' = 1 := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw γ hγ
  have hγ' : ∀ i j, (γ : Matrix (Ix n) (Ix n) O) i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈
      Ideal.span {ϖ ^ 2} := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) => u.1 i j)
      (MonoidHom.mem_ker.1 hγ)
    simpa [Matrix.one_apply, apply_ite] using this
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hm : Ideal.span {ϖ ^ 2} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self ϖ two_ne_zero)).trans
      ((Ideal.span_singleton_le_iff_mem _).2 hϖm)
  have hC : ∀ i j, ∃ c, (γ : Matrix (Ix n) (Ix n) O) (Sum.inr i) (Sum.inl j) = ϖ * (ϖ * c) := by
    intro i j
    have h0 := hγ' (Sum.inr i) (Sum.inl j)
    simp only [Matrix.one_apply, reduceCtorEq, if_false, sub_zero] at h0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h0
    exact ⟨c, by rw [← hc]; ring⟩
  choose C hCe using hC
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Ix n) (Ix n) O, M = fromBlocks (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₁
      (ϖ • (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₂) (ϖ • Matrix.of C)
      (γ : Matrix (Ix n) (Ix n) O).toBlocks₂₂ := ⟨_, rfl⟩
  have hγM : (γ : Matrix (Ix n) (Ix n) O) = fromBlocks (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₁
      (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₂ (ϖ • (ϖ • Matrix.of C))
      (γ : Matrix (Ix n) (Ix n) O).toBlocks₂₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, hCe]
  have hsc : Matrix.scalar (Fin n) (w : L) = (w : L) • (1 : Matrix (Fin n) (Fin n) L) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hrel : (γ : Matrix (Ix n) (Ix n) O).map (algebraMap O L) *
        fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L)) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L)) *
        M.map (algebraMap O L) := by
    rw [hsc, hM]
    conv_lhs => rw [hγM]
    exact block_twist ϖ (w : L) hw _ _ _ _
  have hτ : (fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L))).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, hsc, Matrix.det_smul, Matrix.det_one]
    simp
  have hdetM : M.det = (γ : Matrix (Ix n) (Ix n) O).det := by
    have h1 := congrArg Matrix.det hrel
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at h1
    have h2 := mul_left_cancel₀ hτ h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← RingHom.map_det] at h2
    exact (IsFractionRing.injective O L h2).symm
  have hdet : IsUnit M.det := by
    rw [hdetM]
    exact Matrix.isUnits_det_units γ
  have hMm : ∀ i j, M i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [hM]
    rcases i with i | i <;> rcases j with j | j
    · simpa [Matrix.toBlocks₁₁] using hm (hγ' (Sum.inl i) (Sum.inl j))
    · simpa using Ideal.mul_mem_right _ _ hϖm
    · simpa using Ideal.mul_mem_right _ _ hϖm
    · simpa [Matrix.toBlocks₂₂] using hm (hγ' (Sum.inr i) (Sum.inr j))
  refine ⟨Matrix.nonsingInvUnit M hdet, Units.ext ?_, Units.ext ?_⟩
  · exact hrel
  · have h3 : M.map (IsLocalRing.residue O) = (1 : Matrix (Ix n) (Ix n) O).map (IsLocalRing.residue O) := by
      ext i j
      exact Ideal.Quotient.eq.2 (hMm i j)
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at h3
    exact h3

end GlobalTheory.CompanionTheory.Jp.Twist
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralComplexPowerFinite
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_one_add_normSq_rpow_ne_top :
    ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  intro n t ht
  have ht0 : 0 < t := lt_of_le_of_lt n.cast_nonneg ht
  have hdim : (Module.finrank ℝ (Fin n → ℂ) : ℝ) < 2 * t := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    linarith
  have hint := integrable_rpow_neg_one_add_norm_sq (E := Fin n → ℂ) (μ := volume) hdim
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun v => ?_) hint.lintegral_lt_top)
  apply ENNReal.ofReal_le_ofReal

  have hS0 : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hnorm : ‖v‖ ≤ Real.sqrt (∑ i, Complex.normSq (v i)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    have h1 : ‖v i‖ ^ 2 ≤ ∑ j, Complex.normSq (v j) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
    simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt h1
  have hab : 1 + ‖v‖ ^ 2 ≤ 1 + ∑ i, Complex.normSq (v i) := by
    have h2 := pow_le_pow_left₀ (norm_nonneg v) hnorm 2
    rw [Real.sq_sqrt hS0] at h2
    linarith
  have ha : 0 < 1 + ‖v‖ ^ 2 := by positivity
  rw [show -(2 * t) / 2 = -t by ring, Real.rpow_neg (by linarith), Real.rpow_neg ha.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ha t) (Real.rpow_le_rpow ha.le hab ht0.le)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralLinearChangeVariablesComplex
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem det_restrictScalars_toLin' {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((Matrix.toLin' D).restrictScalars ℝ) = Complex.normSq (Matrix.det D) := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]

theorem lintegral_eq_normSq_det_mul_lintegral_mulVec (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : Matrix.det D ≠ 0) (g : (Fin n → ℂ) → ENNReal) (hg : Measurable g) :
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by
  set f : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' D).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = Complex.normSq (Matrix.det D) := det_restrictScalars_toLin' D
  have hpos : 0 < Complex.normSq (Matrix.det D) := Complex.normSq_pos.mpr hD
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact hpos.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin n → ℂ)) hne
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  have key : ∫⁻ v, g (D *ᵥ v) = ENNReal.ofReal (Complex.normSq (Matrix.det D))⁻¹ * ∫⁻ u, g u := by
    have e : ∀ v, D *ᵥ v = f v := fun v => by simp [hf, Matrix.toLin'_apply]
    simp_rw [e]
    rw [← lintegral_map hg hfm, hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.mpr hpos), smul_eq_mul]
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one,
    one_mul]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralPowerLineScaling
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_sq_add_sq_rpow_neg :
    ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  intro s hs
  have hint : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-s)) := by
    have h0 := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s)
      (by simp; linarith)
    have e : -(2 * s) / 2 = -s := by ring
    simpa [Real.norm_eq_abs, sq_abs, e] using h0
  refine ⟨∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s)), hint.lintegral_lt_top.ne, ?_⟩
  intro a ha m
  have hF : Measurable fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s)) := by fun_prop
  rw [lintegral_sub_right_eq_self (fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))) m]
  have hpt : ∀ t : ℝ, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) =
      ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) * ENNReal.ofReal ((1 + t ^ 2) ^ (-s)) := by
    intro t
    rw [← ENNReal.ofReal_mul (by positivity), show a ^ 2 + (a * t) ^ 2 = a ^ 2 * (1 + t ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast a 2,
      ← Real.rpow_mul ha.le]
  have hpow : a ^ (1 - 2 * s) = a * a ^ ((2 : ℕ) * -s : ℝ) := by
    rw [show (1 - 2 * s) = 1 + ((2 : ℕ) * -s : ℝ) by push_cast; ring, Real.rpow_add ha,
      Real.rpow_one]
  calc ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
      = ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
          ∂(ENNReal.ofReal |a| • Measure.map (a * ·) volume) := by
        rw [Real.smul_map_volume_mul_left ha.ne']
    _ = ENNReal.ofReal |a| * ∫⁻ t, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) := by
        rw [lintegral_smul_measure, lintegral_map hF (measurable_const_mul a), smul_eq_mul]
    _ = ENNReal.ofReal a * (ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) *
          ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s))) := by
        rw [abs_of_pos ha]
        simp_rw [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, ← hpow, mul_comm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialCoefficientComparisonStatement
section
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_coefficient_comparison : ∀ {n : ℕ} {ι κ : Type} (I : Finset ι) (J : Finset κ) (f : ι → ℂ) (g : κ → ℂ) (e : ι → Fin n → ℤ) (e' : κ → Fin n → ℤ), (∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) → ∑ i ∈ I, f i * mon (e i) z = ∑ j ∈ J, g j * mon (e' j) z) → ∀ m : Fin n → ℤ, ∑ i ∈ I.filter (fun i => e i = m), f i = ∑ j ∈ J.filter (fun j => e' j = m), g j := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus | exact GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus | (intros; apply GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatCardDualEq
section
namespace GlobalTheory.CompanionTheory.ZModDual

theorem nat_card_dual_eq : ∀ (n : ℕ) [NeZero n] (N : Type) [AddCommGroup N] [Module (ZMod n) N] [Finite N],
    Nat.card (Module.Dual (ZMod n) N) = Nat.card N := by
  intro n _ N _ _ _
  exact GlobalTheory.ZModDual.card_dual_eq n N

end GlobalTheory.CompanionTheory.ZModDual
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLawsStatement
section
open CrystallineSemistableComparison.Onto
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onto_form_laws : CrystallineSemistableComparison.Onto.FormLaws := by
  first | exact @GlobalTheory.CompanionTheory.OntoForms.formLaws | exact GlobalTheory.CompanionTheory.OntoForms.formLaws | (intros; apply GlobalTheory.CompanionTheory.OntoForms.formLaws <;> assumption)
end

