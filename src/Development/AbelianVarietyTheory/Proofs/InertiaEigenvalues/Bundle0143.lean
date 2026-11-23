module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
public import GroundTheory.LocalFields.Bundle0006
public import GroundTheory.LocalFields.UnramifiedGalois

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedIntegralEqVolMulOrbitalIntegral
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.TruncInt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem absK_ne_zero (A : Et F E) {t : A.K} (h : IsUnit t) : A.absK t ≠ 0 := by
  unfold Et.absK
  rw [dif_pos h]
  exact NNReal.coe_ne_zero.2 (IsUnit.map (distribHaarChar A.K) (Group.isUnit h.unit)).ne_zero

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK
  split_ifs <;> simp

theorem isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W) (c : ℂ) :
    IsLocallyConstant (W.indicator fun _ => c) := fun s => by
  have h := Set.indicator_const_preimage W s c
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hW.isOpen, hW.isClosed.isOpen_compl, isOpen_empty]

end GlobalTheory.JR.TruncInt


open GlobalTheory.JR.TruncInt in
theorem GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) → ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) → ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (y₀ : A.L), IsUnit y₀ → ∀ (D : AddSubgroup A.K), IsOpen (D : Set A.K) → IsCompact (D : Set A.K) → ∀ φ : A.L → ℂ, IsTest φ → (∀ b ∈ D, ∃ s s' : A.K, s ∈ A.OK ∧ s' ∈ A.OK ∧ s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse ((x : A.K) * A.NL y₀) * b ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y) → ∫ y, φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - (x : A.K) * A.NL y₀) ∂(m.μL x) = ((m.μK D).toReal : ℂ) * A.orbL m.ν φ y₀ := by
  intro F E _ _ _ _ _ A hN hK ψ hψ m x y₀ hy₀ D hDo hDc φ hφ hsq
  classical
  obtain ⟨hNs, hNmul, hNt, hNu1, hNu2⟩ := hN
  obtain ⟨habs, habs1, hvol⟩ := hK
  set a : A.K := (x : A.K) * A.NL y₀ with ha_def
  have ha : IsUnit a := x.isUnit.mul (hNu2 y₀ hy₀)
  have hx : IsUnit (x : A.K) := x.isUnit
  have hkey : ∀ b : A.K, ∀ s : A.K, s ^ 2 = 1 + Ring.inverse a * b → a * s ^ 2 = a + b := by
    intro b s hs
    rw [hs, mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel a ha, one_mul]
  have hsec : ∀ a' : A.K, ∀ s : A.K, s ^ 2 = 1 + Ring.inverse a * ((x : A.K) * a' - a) →
      A.NL (y₀ * algebraMap A.K A.L s) = a' := by
    intro a' s hs
    have h1 := hkey _ s hs
    rw [hNmul, hNs]
    apply hx.mul_left_cancel
    calc (x : A.K) * (A.NL y₀ * s ^ 2) = a * s ^ 2 := by rw [ha_def]; ring
      _ = _ := by rw [h1]; ring
  have habsT : ∀ a' : A.K, (x : A.K) * a' - a ∈ (D : Set A.K) →
      A.absK a' = A.absK a / A.absK x ∧ IsUnit a' := by
    intro a' hD
    obtain ⟨s, s', hs, hs', hss, hsq2, -⟩ := hsq _ hD
    have h1 := hkey _ s hsq2
    have h2 : (x : A.K) * a' = a * s ^ 2 := by rw [h1]; ring
    have hsu : IsUnit s := ⟨⟨s, s', hss, by rw [mul_comm]; exact hss⟩, rfl⟩
    have hu : IsUnit a' := by
      have : IsUnit ((x : A.K) * a') := by rw [h2]; exact ha.mul (hsu.pow 2)
      exact isUnit_of_mul_isUnit_right this
    refine ⟨?_, hu⟩
    have h3 := congrArg A.absK h2
    rw [habs (x : A.K) a', habs a (s ^ 2), pow_two, habs s s, habs1 s s' hs hs' hss, mul_one, mul_one] at h3
    rw [eq_div_iff (TruncInt.absK_ne_zero A hx), ← h3]; ring
  set f : A.L → A.K := fun y => (x : A.K) * A.NL y - a with hf
  have hfc : Continuous f := (continuous_const.mul (EtMeas.continuous_NL A)).sub continuous_const
  have hSu : ∀ y, f y ∈ (D : Set A.K) → IsUnit y := fun y hy => hNu1 y (habsT _ hy).2
  set h : A.L → ℂ := fun y => φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) (f y) with hh
  show ∫ y, h y ∂(m.μL x) = _
  have hDcl : IsClosed (D : Set A.K) := AddSubgroup.isClosed_of_isOpen D hDo
  have hTest : IsTest h := by
    refine ⟨hφ.1.mul ((TruncInt.isLocallyConstant_indicator ⟨hDcl, hDo⟩ (1 : ℂ)).comp_continuous hfc), ?_⟩
    exact hφ.2.mul_right
  have hsupp : tsupport h ⊆ {y | IsUnit y} := by
    refine (closure_minimal ?_ (hDcl.preimage hfc)).trans ?_
    · intro y hy
      by_contra hn
      exact hy (by simp only [h, Set.indicator_of_notMem (show f y ∉ (D : Set A.K) from hn), mul_zero])
    · intro y hy
      exact hSu y hy
  have hμ := (GlobalTheory.JR.exists_meas_and_scale F E A ψ hψ).2 m x
  rw [hμ, integral_smul_measure, ENNReal.toReal_ofReal (TruncInt.absK_nonneg A _)]
  have hxa : A.absK a / A.absK x ≠ 0 :=
    div_ne_zero (TruncInt.absK_ne_zero A ha) (TruncInt.absK_ne_zero A hx)
  have hxaC : ((A.absK a / A.absK x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxa
  have hpt : ∀ y, h y = ((A.absK a / A.absK x : ℝ) : ℂ) * (h y * ((A.absK (A.NL y) : ℂ))⁻¹) := by
    intro y
    by_cases hy : f y ∈ (D : Set A.K)
    · rw [(habsT _ hy).1, mul_comm (h y), mul_inv_cancel_left₀ hxaC]
    · simp only [h, Set.indicator_of_notMem hy, mul_zero, zero_mul]
  have hI1 : ∫ y, h y ∂(m.μL 1) = ∫ y, ((A.absK a / A.absK x : ℝ) : ℂ) * (h y * ((A.absK (A.NL y) : ℂ))⁻¹) ∂(m.μL 1) :=
    integral_congr_ae (ae_of_all _ hpt)
  rw [hI1, integral_const_mul]
  let σ : A.K → A.L := fun a' =>
    if hb : (x : A.K) * a' - a ∈ (D : Set A.K) then y₀ * algebraMap A.K A.L (Classical.choose (hsq _ hb))
    else if he : ∃ y : A.L, A.NL y = a' then Classical.choose he else 0
  have hσD : ∀ a' (hb : (x : A.K) * a' - a ∈ (D : Set A.K)), ∃ s : A.K, σ a' = y₀ * algebraMap A.K A.L s ∧
      s ^ 2 = 1 + Ring.inverse a * ((x : A.K) * a' - a) ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by
    intro a' hb
    obtain ⟨s', -, -, -, h4, h5⟩ := Classical.choose_spec (hsq _ hb)
    exact ⟨Classical.choose (hsq _ hb), by simp only [σ, dif_pos hb], h4, h5⟩
  have hσN : ∀ a', ((x : A.K) * a' - a ∈ (D : Set A.K) ∨ ∃ y : A.L, A.NL y = a') → A.NL (σ a') = a' := by
    intro a' hor
    by_cases hb : (x : A.K) * a' - a ∈ (D : Set A.K)
    · obtain ⟨s, hσs, hs2, -⟩ := hσD a' hb
      rw [hσs]; exact hsec a' s hs2
    · have he := hor.resolve_left hb
      simp only [σ, dif_neg hb, dif_pos he]
      exact Classical.choose_spec he
  have hσ : ∀ y : A.L, IsUnit y → A.NL (σ (A.NL y)) = A.NL y := fun y _ => hσN _ (Or.inr ⟨y, rfl⟩)
  rw [m.nat.2 σ hσ h hTest hsupp]
  set T : Set A.K := {a' | (x : A.K) * a' - a ∈ (D : Set A.K)} with hT
  have hTm : MeasurableSet T :=
    (hDo.preimage ((continuous_const.mul continuous_id).sub continuous_const)).measurableSet
  have hTN : T ⊆ {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'} := by
    intro a' hb
    refine ⟨σ a', ?_, hσN a' (Or.inl hb)⟩
    exact hNu1 _ (by rw [hσN a' (Or.inl hb)]; exact (habsT a' hb).2)
  have hNL0 : A.NL 0 = 0 := by simpa using hNs 0
  have hpt2 : ∀ a', A.orbL m.ν h (σ a') * ((A.absK a' : ℂ))⁻¹ =
      T.indicator (fun a' => A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹) a' := by
    intro a'
    by_cases hb : a' ∈ T
    · obtain ⟨s, hσs, -, hφs⟩ := hσD a' hb
      have hNσ : A.NL (σ a') = a' := hσN a' (Or.inl hb)
      rw [Set.indicator_of_mem hb]
      congr 1
      unfold Et.orbL
      congr 1
      funext t
      have hft : f (t.1 * σ a') ∈ (D : Set A.K) := by
        show (x : A.K) * A.NL (t.1 * σ a') - a ∈ (D : Set A.K)
        rw [hNmul, hNt, hNσ, one_mul]; exact hb
      show φ (t.1 * σ a') * Set.indicator _ _ (f (t.1 * σ a')) = φ (t.1 * y₀)
      rw [Set.indicator_of_mem hft, mul_one, hσs, ← mul_assoc, hφs]
    · rw [Set.indicator_of_notMem hb]
      have hz : ∀ t : unitary A.L, h (t.1 * σ a') = 0 := by
        intro t
        have hft : f (t.1 * σ a') ∉ (D : Set A.K) := by
          by_cases he : ∃ y : A.L, A.NL y = a'
          · show (x : A.K) * A.NL (t.1 * σ a') - a ∉ (D : Set A.K)
            rw [hNmul, hNt, hσN a' (Or.inr he), one_mul]; exact hb
          · have h0 : σ a' = 0 := by simp only [σ, dif_neg (show ¬ ((x : A.K) * a' - a ∈ (D : Set A.K)) from hb), dif_neg he]
            show (x : A.K) * A.NL (t.1 * σ a') - a ∉ (D : Set A.K)
            rw [h0, mul_zero, hNL0, mul_zero, zero_sub]
            intro hD
            obtain ⟨s, s', -, -, hss, hs2, -⟩ := hsq _ hD
            have h1 := hkey _ s hs2
            rw [add_neg_cancel] at h1
            have hsu : IsUnit s := ⟨⟨s, s', hss, by rw [mul_comm]; exact hss⟩, rfl⟩
            have hu : IsUnit (a * s ^ 2) := ha.mul (hsu.pow 2)
            rw [h1, isUnit_zero_iff] at hu
            haveI := subsingleton_of_zero_eq_one hu
            exact he ⟨0, Subsingleton.elim _ _⟩
        simp only [h, Set.indicator_of_notMem hft, mul_zero]
      simp only [Et.orbL, hz, integral_zero, zero_mul]
  have hI2 : ∫ a' in {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'}, A.orbL m.ν h (σ a') * ((A.absK a' : ℂ))⁻¹ ∂m.μK =
      ∫ a' in {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'},
        T.indicator (fun a' => A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹) a' ∂m.μK :=
    integral_congr_ae (ae_of_all _ hpt2)
  rw [hI2, setIntegral_indicator hTm, Set.inter_eq_right.2 hTN]
  have hI3 : ∫ a' in T, A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹ ∂m.μK =
      ∫ a' in T, A.orbL m.ν φ y₀ * (((A.absK a / A.absK x : ℝ) : ℂ))⁻¹ ∂m.μK :=
    setIntegral_congr_fun hTm (fun a' hb => by simp only [(habsT a' hb).1])
  rw [hI3, setIntegral_const, Measure.real, hT, hvol m.μK m.sdK.1 x a _ hDo.measurableSet, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 (TruncInt.absK_nonneg A _))]
  have hx0 : A.absK x ≠ 0 := TruncInt.absK_ne_zero A hx
  have ha0 : A.absK a ≠ 0 := TruncInt.absK_ne_zero A ha
  simp only [Complex.real_smul]
  have hx0C : ((A.absK x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx0
  have ha0C : ((A.absK a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha0
  push_cast
  field_simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescent
section
noncomputable section

namespace GlobalTheory.UnitLemma.LieEnd

open GlobalTheory.UnitLemma Polynomial Filter Topology

theorem eta_mul (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta val
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy), neg_add,
    zpow_add₀ (by norm_num)]

theorem eta_sq (K : UQ) (x : K.E) : K.eta x * K.eta x = 1 := by
  unfold UQ.eta
  rw [← mul_zpow]
  norm_num

theorem q_ne_zero (K : UQ) : K.q ≠ 0 := by
  intro hq
  have hc := K.card_res
  have hpos : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
  rw [hq] at hc
  simp at hc
  omega

theorem exists_small (K : UQ) : ∃ a : K.O, K.Small a := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨y, hy⟩ := K.c_int p
  have hinj := IsFractionRing.injective K.O K.E
  have hy' : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E p := by rw [← hy, K.c_c]
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : algebraMap K.O K.E p = 0 := by simpa using hy
    exact hp.ne_zero ((map_eq_zero_iff _ hinj).1 h0)
  refine ⟨p * y, mul_ne_zero hp.ne_zero hy0, Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hp.not_isUnit), ?_⟩
  rw [map_mul, map_mul, hy, hy', mul_comm]

variable {K : UQ}

theorem mulLeft_prod (B₁ B₂ : InvAlg K) (x : B₁.A × B₂.A) :
    LinearMap.mulLeft K.E x = (LinearMap.mulLeft K.E x.1).prodMap (LinearMap.mulLeft K.E x.2) := LinearMap.ext fun y => Prod.ext (by simp) (by simp)

theorem prod_P (B₁ B₂ : InvAlg K) : (B₁.prod B₂).P = B₁.P * B₂.P := by
  show (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly = _
  rw [mulLeft_prod]
  exact LinearMap.charpoly_prodMap _ _

theorem trace_prod (B₁ B₂ : InvAlg K) (x : B₁.A × B₂.A) :
    Algebra.trace K.E (B₁.A × B₂.A) x = Algebra.trace K.E B₁.A x.1 + Algebra.trace K.E B₂.A x.2 := Algebra.trace_prod_apply x

theorem linLim (h1 : CountIdentity) (h2 : UnitaryLimit) (B : InvAlg K) (hB : B.LieReg) (a : K.O)
    (ha : K.Small a) (x : B.A) (hx : B.Plus x) : B.LinLim a x (B.N x : ℝ) := by
  have hw : ∀ k : ℕ, IsUnit (algebraMap K.O B.A a ^ k) := by
    intro k
    apply IsUnit.pow
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    exact (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha.1)).map _
  have hσ : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ha.2.2]
  refine (h2 K B hB a ha x hx).congr fun k => ?_
  have e : x * algebraMap K.O B.A a ^ (2 * k) =
      x * (algebraMap K.O B.A a ^ k * B.σ (algebraMap K.O B.A a ^ k)) := by
    rw [map_pow, hσ, ← pow_add, two_mul]
  rw [e, h1 K B hB x _ hx (hw k), Rat.cast_natCast]

theorem nonempty_of_N_ne_zero (B : InvAlg K) (x : B.A) (h : B.N x ≠ 0) : (B.X x).Nonempty := by
  by_contra he
  apply h
  have : IsEmpty (B.X x) := Set.isEmpty_coe_sort.2 (Set.not_nonempty_iff_eq_empty.1 he)
  have : IsEmpty (Orb K.O B.T (B.X x)) := ⟨fun o => isEmptyElim (Quot.out o)⟩
  exact finsum_of_isEmpty _

theorem X_empty (B : InvAlg K) (y : B.A) (hy : y ≠ 0) (h : ∀ z, Algebra.trace K.E B.A (y * z) = 0) (x : B.A) :
    ¬ (B.X x).Nonempty := by
  rintro ⟨L, hL⟩
  obtain ⟨⟨hfg, -⟩, -, hdual⟩ := hL
  have hmem : ∀ s : B.A, y * s ∈ L := fun s => (hdual _).2 fun z _ => by
    have h0 : B.herm x (y * s) z = 0 := by
      unfold InvAlg.herm
      rw [show x * (y * s) * B.σ z = y * (x * s * B.σ z) by ring]
      exact h _
    rw [h0]
    exact zero_mem _
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K.E hy
  have htop : (⊤ : Submodule K.O K.E) ≤ L.map ((φ : B.A →ₗ[K.E] K.E).restrictScalars K.O) := by
    intro e _
    refine Submodule.mem_map.2 ⟨y * algebraMap K.E B.A e, hmem _, ?_⟩
    rw [LinearMap.restrictScalars_apply, mul_comm, ← Algebra.smul_def, map_smul, hφ, smul_eq_mul, mul_one]
  have : Module.Finite K.O K.E := ⟨by rw [← top_le_iff.1 htop]; exact hfg.map _⟩
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hp0 : algebraMap K.O K.E p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 hp.ne_zero
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.IsIntegral.isIntegral (R := K.O) (algebraMap K.O K.E p)⁻¹)
  apply hp.not_isUnit
  have hpr : p * r = 1 :=
    IsFractionRing.injective K.O K.E (by rw [map_mul, hr, map_one, mul_inv_cancel₀ hp0])
  exact ⟨⟨p, r, hpr, by rw [mul_comm, hpr]⟩, rfl⟩

theorem exists_rad (B : InvAlg K) (h : B.gramDet 1 = 0) :
    ∃ y : B.A, y ≠ 0 ∧ ∀ z, Algebra.trace K.E B.A (y * z) = 0 := by
  classical
  set b := Module.finBasis K.E B.A
  have h' : (Matrix.of fun i j => B.herm 1 (b i) (b j)).det = 0 := h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h'
  have hj : ∀ j, Algebra.trace K.E B.A ((∑ i, v i • b i) * B.σ (b j)) = 0 := by
    intro j
    have hvj := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, InvAlg.herm, one_mul, Pi.zero_apply] at hvj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    simpa [smul_mul_assoc] using hvj
  refine ⟨∑ i, v i • b i, fun h0 => hv0 (funext fun i => Fintype.linearIndependent_iff.1 b.linearIndependent v h0 i), ?_⟩
  intro z
  have hz : z = ∑ j, K.c (b.repr (B.σ z) j) • B.σ (b j) := by
    conv_lhs => rw [← B.σ_σ z, ← b.sum_repr (B.σ z)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, B.σ_alg]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hz, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [mul_smul_comm, map_smul, hj, smul_zero]

theorem rep_plus (B : InvAlg K) (k : B.Cl) : B.Plus k.rep := ⟨Units.isUnit _, (Quot.out k).2⟩

theorem eta_norm (B : InvAlg K) (h : B.gramDet 1 ≠ 0) (x : B.A) (hx : IsUnit x) :
    K.eta (Algebra.norm K.E x) = K.eta (B.gramDet 1) * K.eta (B.gramDet x) := by
  have hn : Algebra.norm K.E x ≠ 0 := (hx.map (Algebra.norm K.E)).ne_zero
  rw [_root_.GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul K B x, eta_mul K hn h, mul_left_comm, eta_sq, mul_one]

theorem cast_finsum {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℝ) = ∑ᶠ i, (f i : ℝ) := (Rat.castHom ℝ).toAddMonoidHom.map_finsum_of_injective Rat.cast_injective f

theorem unitLemmaLie_of (h1 : CountIdentity) (h2 : UnitaryLimit) (h3 : LinearDescent) : UnitLemmaLie := by
  intro K B₁ B₂ hg₁ hg₂ hsep
  show (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * InvAlg.kapSum B₁ B₂ = B₁.stSum * B₂.stSum
  obtain ⟨a, ha⟩ := exists_small K
  have hB : (B₁.prod B₂).LieReg := ⟨Prod.ext hg₁ hg₂, by rw [prod_P]; exact hsep⟩
  have hB₁ : B₁.LieReg := ⟨hg₁, hsep.of_mul_left⟩
  have hB₂ : B₂.LieReg := ⟨hg₂, hsep.of_mul_right⟩
  have hLD := h3 K B₁ B₂ hg₁ hg₂ hsep a ha (fun x => ((B₁.prod B₂).N x : ℝ)) (fun x => (B₁.N x : ℝ))
    (fun x => (B₂.N x : ℝ)) (fun x hx => linLim h1 h2 _ hB a ha x hx)
    (fun x hx => linLim h1 h2 _ hB₁ a ha x hx) (fun x hx => linLim h1 h2 _ hB₂ a ha x hx)
  simp only [← Rat.cast_mul] at hLD
  rw [← cast_finsum, ← cast_finsum, ← cast_finsum] at hLD
  have hq : (-(K.q : ℝ)) ^ val K.O (resultant B₁.P B₂.P) =
      (((-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) : ℚ) : ℝ) := by
    rw [Rat.cast_zpow, Rat.cast_neg, Rat.cast_natCast]
  rw [hq, ← Rat.cast_mul, ← Rat.cast_mul] at hLD
  have hQ := Rat.cast_injective hLD
  have hq0 : (-(K.q : ℚ)) ≠ 0 := by simpa using q_ne_zero K
  by_cases hd : B₁.gramDet 1 = 0
  · obtain ⟨y, hy0, hy⟩ := exists_rad B₁ hd
    have hN₁ : ∀ x, B₁.N x = 0 := fun x =>
      by_contra fun hx => X_empty B₁ y hy0 hy x (nonempty_of_N_ne_zero B₁ x hx)
    have hN : ∀ x, (B₁.prod B₂).N x = 0 := by
      intro x
      by_contra hx
      refine X_empty (B₁.prod B₂) ((y, 0) : B₁.A × B₂.A) (fun h0 => hy0 (congrArg Prod.fst h0))
        (fun z => ?_) x (nonempty_of_N_ne_zero _ x hx)
      have key : ∀ w : B₁.A × B₂.A, Algebra.trace K.E (B₁.A × B₂.A) ((y, 0) * w) = 0 := fun w => by
        rw [trace_prod]
        simp [hy]
      exact key z
    simp [InvAlg.kapSum, InvAlg.stSum, hN, hN₁]
  · have he : K.eta (B₁.gramDet 1) * K.eta (B₁.gramDet 1) = 1 := eta_sq K _
    have hS : ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) * (B₁.prod B₂).N k.rep =
        K.eta (B₁.gramDet 1) * InvAlg.kapSum B₁ B₂ := by
      unfold InvAlg.kapSum
      rw [mul_finsum]
      refine finsum_congr fun k => ?_
      rw [eta_norm B₁ hd _ (Prod.isUnit_iff.1 (rep_plus _ k).1).1, mul_assoc]
    have hS₁ : ∑ᶠ k : B₁.Cl, K.eta (Algebra.norm K.E k.rep) * B₁.N k.rep =
        K.eta (B₁.gramDet 1) * B₁.stSum := by
      unfold InvAlg.stSum
      rw [mul_finsum]
      refine finsum_congr fun k => ?_
      rw [eta_norm B₁ hd _ (rep_plus _ k).1]
      by_cases hk : B₁.N k.rep = 0
      · rw [hk, mul_zero, mul_zero]
      · rw [_root_.GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one K B₁ k.rep (rep_plus _ k).2 (nonempty_of_N_ne_zero B₁ _ hk), mul_one]
    have hst : ∑ᶠ k : B₂.Cl, B₂.N k.rep = B₂.stSum := rfl
    rw [hS, hS₁, hst] at hQ
    have hk : InvAlg.kapSum B₁ B₂ =
        (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (B₁.stSum * B₂.stSum) := by
      calc InvAlg.kapSum B₁ B₂
          = K.eta (B₁.gramDet 1) * (K.eta (B₁.gramDet 1) * InvAlg.kapSum B₁ B₂) := by
            rw [← mul_assoc, he, one_mul]
        _ = K.eta (B₁.gramDet 1) * ((-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) *
            (K.eta (B₁.gramDet 1) * B₁.stSum * B₂.stSum)) := by rw [hQ]
        _ = (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (B₁.stSum * B₂.stSum) *
            (K.eta (B₁.gramDet 1) * K.eta (B₁.gramDet 1)) := by ring
        _ = _ := by rw [he, mul_one]
    rw [hk, ← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, one_mul]

end GlobalTheory.UnitLemma.LieEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticUniformizerTraceNorm
section
open ValuativeRel

namespace GlobalTheory


open GroundTheory.LocalField IsLocalRing in
theorem unramified_quadratic_uniformizer_trace_norm : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L], (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 → Module.finrank K L = 2 → ∃ ϖ : K, ϖ ≠ 0 ∧ ϖ ≤ᵥ 1 ∧ ¬ (1 : K) ≤ᵥ ϖ ∧ (¬ ∃ y : L, Algebra.norm K y = ϖ) ∧ (∀ y : L, y ≤ᵥ 1 → (∃ z : L, z ≤ᵥ 1 ∧ y = algebraMap K L ϖ * z) ∨ ∃ z : L, z ≤ᵥ 1 ∧ y * z = 1) ∧ (∀ s : K, s ≤ᵥ 1 → ∃ z : L, z ≤ᵥ 1 ∧ Algebra.trace K L z = s) ∧ ∀ s : K, s ≤ᵥ 1 → 1 ≤ᵥ s → ∃ w : L, w ≤ᵥ 1 ∧ Algebra.norm K w = s := by
  open GroundTheory.LocalField IsLocalRing in
  intro K L _ _ _ _ _ _ _ _ _ _ _ he h2
  haveI : IsUnramified K L := ⟨he⟩
  have memK : ∀ x : K, x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := fun x ↦ by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation K), ← Valuation.vle_iff_le]
  have memL : ∀ x : L, x ∈ 𝒪[L] ↔ x ≤ᵥ 1 := fun x ↦ by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation L), ← Valuation.vle_iff_le]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  refine ⟨(ϖ : K), hϖ0, (memK _).1 ϖ.2, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h1
    have hv : ValuativeRel.valuation K (ϖ : K) = 1 :=
      le_antisymm ((Valuation.vle_iff_le _).1 ((memK _).1 ϖ.2) |>.trans_eq (map_one _))
        ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 h1))
    exact hϖ.not_isUnit ((Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv)
  ·
    rintro ⟨y, hy⟩
    have h := ord_norm (K := K) y
    rw [hy, ord_uniformizer hϖ, IsUnramified.residueDegree_eq_finrank K L, h2] at h
    omega
  ·
    intro y hy
    have hπ := irreducible_algebraMap_of_isUnramified (L := L) hϖ
    set y' : 𝒪[L] := ⟨y, (memL y).2 hy⟩
    by_cases hu : IsUnit y'
    · right
      refine ⟨((hu.unit⁻¹ : 𝒪[L]ˣ) : 𝒪[L]), (memL _).1 (hu.unit⁻¹ : 𝒪[L]ˣ).1.2, ?_⟩
      have h := hu.unit.mul_inv
      rw [IsUnit.unit_spec] at h
      have := congrArg (fun u : 𝒪[L] ↦ (u : L)) h
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
      exact this
    · left
      have hm : y' ∈ maximalIdeal 𝒪[L] := (mem_maximalIdeal y').2 hu
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨c, hc⟩ := hm
      refine ⟨(c : L), (memL _).1 c.2, ?_⟩
      have := congrArg (fun u : 𝒪[L] ↦ (u : L)) hc
      simp only [y', MulMemClass.coe_mul, coe_algebraMap_integer] at this
      exact this
  ·
    intro s hs
    obtain ⟨a, ha⟩ := trace_integer_surjective (K := K) (L := L) ⟨s, (memK s).2 hs⟩
    refine ⟨(a : L), (memL _).1 a.2, ?_⟩
    rw [← coe_trace_integer, ha]
  ·
    intro s hs1 hs2
    set s' : 𝒪[K] := ⟨s, (memK s).2 hs1⟩
    have hv : ValuativeRel.valuation K s = 1 :=
      le_antisymm ((Valuation.vle_iff_le _).1 hs1 |>.trans_eq (map_one _))
        ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 hs2))
    have hu : IsUnit s' := (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv
    obtain ⟨w, hw⟩ := normIntegerUnits_surjective (K := K) (L := L) hu.unit
    refine ⟨((w : 𝒪[L]) : L), (memL _).1 (w : 𝒪[L]).2, ?_⟩
    have := congrArg (fun u : 𝒪[K]ˣ ↦ ((u : 𝒪[K]) : K)) hw
    simp only [coe_normIntegerUnits_eq, IsUnit.unit_spec] at this
    rw [← coe_norm_integer]
    exact this

end GlobalTheory
end

