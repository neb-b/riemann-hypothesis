module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CircleIntegralInvSubEqZeroOfOutside
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsCoordLeOfLOneNormLe
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FamilyDegreeRatio

theorem gap_lam {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    (H : Num k r lam u b bv ga h q0) (a c : Fin (2 * r + k + 1)) (hac : a < c) :
    100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
  obtain ⟨hk, ⟨hanti, -⟩, -, -, -, hcl, hnd, -, -, hga, hh, -, hq1, hq2, -⟩ := H
  by_cases hc : c.val + 1 < k
  · linarith [hga a c hac hc]
  by_cases ha : a.val + 1 < k
  ·
    have hp : k - 1 < 2 * r + k + 1 := by omega
    have hq : k < 2 * r + k + 1 := by omega
    have hpq : PI.BesselPeriodGGP.eps48 k r ⟨k - 1, hp⟩ ≠ PI.BesselPeriodGGP.eps48 k r ⟨k, hq⟩ := by
      have h1 : ¬ (k < k - 1) := by omega
      have h2 : (k - (k - 1)) % 2 = 1 := by omega
      simp [PI.BesselPeriodGGP.eps48, h1, h2]
    have hgpq := hh _ _ hpq
    have ⟨p1, p2⟩ := hnd ⟨k - 1, hp⟩ (by show k ≤ k - 1 + 1; omega)
    have ⟨q1, q2⟩ := hnd ⟨k, hq⟩ (by show k ≤ k + 1; omega)
    have habs : |lam ⟨k - 1, hp⟩ - lam ⟨k, hq⟩| ≤ bv := abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 := (hcl a ha).1
    have h2 := (hnd c (by omega)).2
    linarith
  ·
    have hac' : a.val < c.val := hac
    have hd : a.val + 1 < 2 * r + k + 1 := by have := c.isLt; omega
    have had : a < ⟨a.val + 1, hd⟩ := by rw [Fin.lt_def]; simp
    have hdc : (⟨a.val + 1, hd⟩ : Fin (2 * r + k + 1)) ≤ c := by rw [Fin.le_iff_val_le_val]; simp; omega
    have hne : PI.BesselPeriodGGP.eps48 k r a ≠ PI.BesselPeriodGGP.eps48 k r ⟨a.val + 1, hd⟩ := by
      have h1 : ¬ (a.val < k - 1) := by omega
      have h2 : ¬ (a.val + 1 < k - 1) := by omega
      rcases Nat.mod_two_eq_zero_or_one (a.val - (k - 1)) with h3 | h3
      · have h4 : (a.val + 1 - (k - 1)) % 2 = 1 := by omega
        simp [PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]
      · have h4 : (a.val + 1 - (k - 1)) % 2 = 0 := by omega
        simp [PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]
    have hg := hh _ _ hne
    have hlt := hanti had
    have hle := hanti.antitone hdc
    rw [abs_of_pos (by linarith)] at hg
    linarith

theorem abs_coord_le_of_lOneNorm_le {n : ℕ} {ν : Fin n → ℤ} {q : ℕ} (hν : n1 ν ≤ q) (a : Fin n) : |(ν a : ℝ)| ≤ q := by
  have h1 : (ν a).natAbs ≤ n1 ν :=
    Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  have h2 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h2]
  exact_mod_cast h1.trans hν

theorem degree_ratios : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) ∧ (∀ I : Finset (Fin (2 * r + k + 1)), Formalism.QuantumDeterminants.fdegHC (fun a => lam a + ((ν + eZ I) a : ℝ)) ≤ ((2 * r + k + 1) : ℝ) ^ I.card * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ))) ∧ ∀ s, Formalism.QuantumDeterminants.fdegHC (fun a => lam a + ((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) / Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) = ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| / |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))| := by
  intro k r lam u b bv ga h q0 H ν hν
  have hgl := fun a c (hac : a < c) => gap_lam H a c hac
  have hνb := fun a => abs_le.mp (abs_coord_le_of_lOneNorm_le hν a)
  have hint := H.2.1.2
  have hq : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have hgap : ∀ a c : Fin (2 * r + k + 1), a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
    intro a c hac
    have := hgl a c hac
    have := hνb a
    have := hνb c
    linarith
  have hanti : StrictAnti (fun a => lam a + (ν a : ℝ)) := fun a c hac => by
    have := hgap a c hac
    simp only
    linarith
  have hinj := hanti.injective
  have hZ : ∀ a c, ∃ m : ℤ, (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) = (m : ℝ) := by
    intro a c
    obtain ⟨m1, hm1⟩ := hint a
    obtain ⟨m2, hm2⟩ := hint c
    exact ⟨m1 - m2 + ν a - ν c, by push_cast; linarith⟩
  have hpos : 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := Formalism.QuantumDeterminants.formal_degree_pos_holds _ _ hinj
  refine ⟨hpos, ?_, ?_⟩
  · intro I
    have hb := (Formalism.HermitianLatticeCounting.P.degree_set_cardinality_bound (2 * r + k + 1) (fun a => lam a + (ν a : ℝ)) I hanti hZ hgap).2
    have hfun : (fun a => lam a + (((ν + eZ I) a : ℤ) : ℝ)) =
        (fun a => (lam a + (ν a : ℝ)) + if a ∈ I then 1 else 0) := by
      funext a
      simp only [Pi.add_apply, eZ]
      split_ifs <;> push_cast <;> ring
    rw [hfun]
    rw [div_le_iff₀ hpos] at hb
    push_cast at hb
    exact hb
  · intro s
    have hfun : (fun a => lam a + (((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) =
        (fun a => lam a + (ν a : ℝ)) + Pi.single s (-1 : ℝ) := by
      funext a
      by_cases has : a = s
      · subst has
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Int.cast_sub, Int.cast_one]
        ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne has, sub_zero, add_zero]
    rw [hfun, GlobalTheory.CompareIterDegree.fdeg_ratio_abs _ s (-1) hinj]
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [abs_div]
    congr 2

end GlobalTheory.FamilyDegreeRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalProperties
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPsi

open Formalism.QuantumDeterminants

theorem hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem inv_fix {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g.det) {v : Fin n → ℂ}
    (h : g *ᵥ v = v) : g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hg, Matrix.one_mulVec]

theorem uw_inv {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) : g⁻¹ ∈ UWset k r z := by
  obtain ⟨hu, hi⟩ := (uHGroup _ _ (hpk_unit k r)).2.2 g hg.1
  exact ⟨hi, fun a => ⟨inv_fix hu (hg.2.1 a).1, inv_fix hu (hg.2.1 a).2⟩, inv_fix hu hg.2.2⟩

theorem uw_mul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {g g' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) (hg' : g' ∈ UWset k r z) : g * g' ∈ UWset k r z := by
  refine ⟨(uHGroup _ _ (hpk_unit k r)).2.1 g hg.1 g' hg'.1, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hg'.2.1 a).1, (hg.2.1 a).1]
  · rw [← Matrix.mulVec_mulVec, (hg'.2.1 a).2, (hg.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, hg'.2.2, hg.2.2]

theorem psi_character : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ g, ‖Formalism.QuantumDeterminants.psi k r z c g‖ = 1) ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ m' ∈ Formalism.QuantumDeterminants.Nset k r, m * m' ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (m * m') = Formalism.QuantumDeterminants.psi k r z c m * Formalism.QuantumDeterminants.psi k r z c m') ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c m⁻¹ = star (Formalism.QuantumDeterminants.psi k r z c m)) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, g * m * g⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ g⁻¹ * m * g ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (g * m * g⁻¹) = Formalism.QuantumDeterminants.psi k r z c m ∧ Formalism.QuantumDeterminants.psi k r z c (g⁻¹ * m * g) = Formalism.QuantumDeterminants.psi k r z c m) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ g' ∈ Formalism.QuantumDeterminants.UWset k r z, g * g' ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g ∈ GG k r) ∧ ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m ∈ GG k r := by
  intro k r z c hz
  refine ⟨fun g => ?_, fun m hm m' hm' => ⟨(nSubgroup k r).2.1 m hm m' hm', (psiChar k r z c hz m hm).1 m' hm'⟩,
    fun m hm => ⟨(nSubgroup k r).2.2 m hm, ?_⟩, fun g hg m hm => ?_,
    fun g hg g' hg' => ⟨uw_mul hg hg', uw_inv hg, hg.1⟩, fun m hm => hm.1⟩
  · unfold psi
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  · rw [← BesselUnipotentEquiv.star_psi_inv z c hz m hm, star_star]
  · have hu := ((uHGroup _ _ (hpk_unit k r)).2.2 g hg.1).1
    have h1 := uWNormal k r z hz g hg m hm
    have h2 := uWNormal k r z hz g⁻¹ (uw_inv hg) m hm
    rw [Matrix.nonsing_inv_nonsing_inv _ hu] at h2
    refine ⟨h1.1, h2.1, ?_, ?_⟩
    · unfold psi; rw [h1.2]
    · unfold psi; rw [h2.2]

end GlobalTheory.BesselPsi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSum
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFunctionBasic

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] in
theorem _root_.GlobalTheory.BesselFunctionBasic.JF_basic : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r), γ ∈ _root_.BranchingSupport.GG k r → (∀ F F' : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp), (∀ g ∈ _root_.BranchingSupport.GG k r, F g = F' g) → _root_.Formalism.FourierDecayAlt.B.JF D F γ = _root_.Formalism.FourierDecayAlt.B.JF D F' γ ∧ (Integrable (_root_.Formalism.FourierDecayAlt.JF.integrand D F γ) D.μSS → Integrable (_root_.Formalism.FourierDecayAlt.JF.integrand D F' γ) D.μSS)) ∧ (∀ (φ : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → ℂ) (F : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp)), (∀ p, D.inSS p → φ (_root_.Formalism.FourierDecayAlt.B.sgs p γ) = φ γ) → _root_.Formalism.FourierDecayAlt.B.JF D (fun g => φ g • F g) γ = φ γ • _root_.Formalism.FourierDecayAlt.B.JF D F γ) ∧ (∀ (ι : Type) [Fintype ι] (F : ι → _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp)), (∀ i, Integrable (_root_.Formalism.FourierDecayAlt.JF.integrand D (F i) γ) D.μSS) → _root_.Formalism.FourierDecayAlt.B.JF D (fun g => ∑ i, F i g) γ = ∑ i, _root_.Formalism.FourierDecayAlt.B.JF D (F i) γ) ∧ ∀ᵐ p ∂D.μSS, D.inSS p := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ D γ hγ
  have hJ : ∀ F : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp),
      _root_.Formalism.FourierDecayAlt.B.JF D F γ = ∫ p, _root_.Formalism.FourierDecayAlt.JF.integrand D F γ p ∂D.μSS := fun F => rfl
  have hae := _root_.Formalism.FourierDecayAlt.P.B6.ae_inSS D
  refine ⟨?_, ?_, ?_, hae⟩
  · intro F F' hF
    have heq : _root_.Formalism.FourierDecayAlt.JF.integrand D F γ =ᵐ[D.μSS] _root_.Formalism.FourierDecayAlt.JF.integrand D F' γ := by
      filter_upwards [hae] with p hp
      simp only [_root_.Formalism.FourierDecayAlt.JF.integrand, _root_.Formalism.FourierDecayAlt.P.B6.rho_eq, hF _ (_root_.Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hγ)]
    exact ⟨by rw [hJ, hJ]; exact integral_congr_ae heq, fun hi => hi.congr heq⟩
  · intro φ F hφ
    rw [hJ, hJ, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [hae] with p hp
    simp only [_root_.Formalism.FourierDecayAlt.JF.integrand, _root_.Formalism.FourierDecayAlt.P.B6.rho_eq, hφ p hp, map_smul]
    rw [smul_comm]
  · intro ι _ F hF
    simp only [hJ]
    rw [← MeasureTheory.integral_finsetSum _ (fun i _ => hF i)]
    congr 1
    funext p
    simp only [JF.integrand, P.B6.rho_eq, map_sum, Finset.smul_sum]

end GlobalTheory.BesselFunctionBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionalSideGrowth
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselLine

theorem psi_const : PsiConst := by
  intro k r z c g
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA
  rw [Finset.mul_sum]

theorem bessel_line : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  intro hH k r ε mu R Wp _ _ _ _ z π u μW μN μG νq l l₁ hDS hS hl hnz hl₁
  obtain ⟨w, hw, hne⟩ := hnz
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -⟩ := hS
  have hc : Formalism.QuantumDeterminants.cStd ≠ 0 := by
    unfold Formalism.QuantumDeterminants.cStd
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact Formalism.FourierDecayAlt.P.DDSmoothness.jsz_line hH.1.2.2.2 psi_const hDS.1 hDS.2 hz hT hc hπ hl hl₁ hw hne

end GlobalTheory.BesselLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRow
section
open Formalism.REAL

namespace GlobalTheory

theorem capelli_comatrix_last_row (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → A) (hE : GlRel E) (u : ℂ) (c : Fin (n + 1)) :
    ∑ l : Fin (n + 1), (((-1 : ℤ) ^ (n + (l : ℕ)) : ℤ) : A) *
        (qminor E Fin.castSucc (Fin.succAbove l) (u - 1) * Tm E u c l) =
      if c = Fin.last n then qdet E u else 0 := by
  have h := Formalism.FourierDecayAlt.P.expansion_last_line A (n + 1) n E hE
    (Fin.snoc (α := fun _ => Fin (n + 1)) Fin.castSucc c) id u
  have h1 : (Fin.snoc (α := fun _ => Fin (n + 1)) Fin.castSucc c : Fin (n + 1) → Fin (n + 1)) ∘
      Fin.castSucc = Fin.castSucc := by
    funext k
    simp
  rw [h1, Fin.snoc_last] at h
  simp only [Function.id_comp, id] at h
  rw [← h]
  split_ifs with hc
  · subst hc
    unfold qdet
    congr 1
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k <;> simp
  · obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.mpr hc
    exact quantumMinor_eq_zero_of_row_eq qSkewRow E _ _ u c'.castSucc (Fin.last n) hc (by simp)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixPicksSplitCasimirEigencomponent
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ComatrixEigen

open Formalism.REAL

theorem qminor_exists_poly {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) :
    ∃ p : Polynomial A, ∀ u : ℂ, qminor E a b u = ∑ d ∈ p.support, u ^ d • p.coeff d := by
  refine ⟨∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : Polynomial A) *
    (List.ofFn fun k : Fin t => ((if a (σ k) = b k then
      Polynomial.X - Polynomial.C (algebraMap ℂ A (k : ℂ)) else 0) + Polynomial.C (E (a (σ k)) (b k)) :
        Polynomial A)).prod, fun u => ?_⟩
  let φ : Polynomial A →+* A := Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u)
    (fun x => (Algebra.commutes u x).symm)
  have hφ : ∀ p : Polynomial A, φ p = ∑ d ∈ p.support, u ^ d • p.coeff d := by
    intro p
    change Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) p = _
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]
  have hX : φ Polynomial.X = algebraMap ℂ A u := Polynomial.eval₂_X _ _
  have hC : ∀ x, φ (Polynomial.C x) = x := fun x => Polynomial.eval₂_C _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hφ, map_sum, qminor]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp_apply, Tm, map_add, hC]
  split_ifs
  · rw [map_sub φ, hX, hC, map_sub]
  · rw [map_zero]

theorem continuous_qminor_apply {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n t : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin t → Fin n) (v : M) :
    Continuous fun u : ℂ => qminor E a b u v := by
  obtain ⟨p, hp⟩ := qminor_exists_poly E a b
  simp only [hp, LinearMap.sum_apply, LinearMap.smul_apply]
  fun_prop

theorem cof_eigen {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {m : ℕ}
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (x : Fin (m + 1) → M)
    (hE : GlRel E)
    (hq : ∀ (Y : ℂ) (w : M), qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w)
    (t : Fin (m + 1))
    (hx : splitCas E x = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • x) (i : Fin (m + 1)) (Y : ℂ) :
    ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) =
      (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
  have key : ∀ Y : ℂ, (Y + (mu t : ℂ)) • ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) =
      (Y + (mu t : ℂ)) • (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
    intro Y
    have hT : ∀ j, ∑ l, Tm E (Y + (m : ℂ) / 2 - (m : ℂ)) j l (x l) = (Y + (mu t : ℂ)) • x j := by
      intro j
      have h1 := congrFun hx j
      simp only [splitCas, Pi.smul_apply] at h1
      have h2 : ∀ l, Tm E (Y + (m : ℂ) / 2 - (m : ℂ)) j l (x l) =
          (if j = l then (Y + (m : ℂ) / 2 - (m : ℂ)) • x l else 0) + E j l (x l) := by
        intro l
        rw [Tm, LinearMap.add_apply]
        split_ifs
        · rw [Module.algebraMap_end_apply]
        · rw [LinearMap.zero_apply]
      simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [neg_eq_iff_eq_neg] at h1
      rw [h1, ← neg_smul, ← add_smul]
      congr 1
      push_cast
      ring
    have hu : Y + (m : ℂ) / 2 = Y + (((m + 1 : ℕ) : ℂ) - 1) / 2 := by push_cast; ring
    have h3 : ∑ l, (if i = l then qdet E (Y + (m : ℂ) / 2) else 0) (x l) =
        (Y + (mu t : ℂ)) • (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, hu, hq, smul_smul, Finset.mul_prod_erase _ (fun r => Y + (mu r : ℂ)) (Finset.mem_univ t)]
      · intro l _ hl
        rw [if_neg (Ne.symm hl), LinearMap.zero_apply]
      · simp
    rw [← h3]
    simp only [← qComatrix (Module.End ℂ M) m E hE (Y + (m : ℂ) / 2) i, LinearMap.sum_apply]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Module.End.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_sum, hT, map_smul, map_smul, Module.End.intCast_apply,
      ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    rfl
  have hc1 : Continuous fun Y : ℂ => ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) := by
    refine continuous_finsetSum _ fun j _ => Continuous.const_smul ?_ _
    exact (continuous_qminor_apply E _ _ (x j)).comp (continuous_add_const _)
  have hc2 : Continuous fun Y : ℂ => (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by fun_prop
  have hd : Dense ({-(mu t : ℂ)}ᶜ : Set ℂ) := dense_compl_singleton _
  refine congrFun (Continuous.ext_on hd hc1 hc2 fun Z hZ => ?_) Y
  have hne : Z + (mu t : ℂ) ≠ 0 := fun h => hZ (eq_neg_of_add_eq_zero_left h)
  exact smul_right_injective M hne (key Z)

end GlobalTheory.ComatrixEigen

namespace GlobalTheory

theorem comatrix_picks_eigencomponent : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (y : Fin (m + 1) → Fin (m + 1) → M), Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ t, splitCas E (y t) = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∀ s i, ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) • Formalism.REAL.qminor E (Fin.succAbove j) (Fin.succAbove i) (-(mu s : ℂ) + (m : ℂ) / 2) (∑ t, y t j) = (∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s)) • y s i := by
  intro M _ _ m E mu y hE hq hy s i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [fun t => ComatrixEigen.cof_eigen E mu (y t) hE hq t (hy t) i (-(mu s : ℂ))]
  rw [Finset.sum_eq_single s]
  · simp only [neg_add_eq_sub]
  · intro t _ ht
    rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨Ne.symm ht, Finset.mem_univ _⟩) (neg_add_cancel _),
      zero_smul]
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompoundMatrixCauchyBinetProperties
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem compound_mul {n : ℕ} (l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ) :
    BranchingSupport.cmp l (g * h) = BranchingSupport.cmp l g * BranchingSupport.cmp l h := by
  ext I J
  have e : (g * h).submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2)
      = g.submatrix (I.1.orderEmbOfFin I.2) id * h.submatrix id (J.1.orderEmbOfFin J.2) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [Matrix.mul_apply]
  unfold BranchingSupport.cmp
  rw [e, Formalism.HermitianLatticeCounting.P.ge_cauchyBinet]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [mul_comm]
  rfl

theorem compound_conjTranspose {n : ℕ} (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) :
    BranchingSupport.cmp l gᴴ = (BranchingSupport.cmp l g)ᴴ := by
  ext I J
  rw [Matrix.conjTranspose_apply]
  unfold BranchingSupport.cmp
  rw [← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]

theorem compound_one (n l : ℕ) : BranchingSupport.cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext I J
  unfold BranchingSupport.cmp
  by_cases hIJ : I = J
  · subst hIJ
    rw [Matrix.submatrix_one _ (I.1.orderEmbOfFin I.2).injective, Matrix.det_one, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hIJ]
    have hne : ¬ I.1 ⊆ J.1 := fun hs =>
      hIJ (Subtype.ext (Finset.eq_of_subset_of_card_le hs (by rw [I.2, J.2])))
    obtain ⟨x, hxI, hxJ⟩ := Finset.not_subset.mp hne
    have hx : x ∈ Set.range (I.1.orderEmbOfFin I.2) := by
      rw [Finset.range_orderEmbOfFin]; exact hxI
    obtain ⟨a, ha⟩ := hx
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b => ?_
    rw [Matrix.submatrix_apply, Matrix.one_apply_ne]
    intro hab
    apply hxJ
    rw [← ha, hab]
    exact Finset.orderEmbOfFin_mem _ _ _

theorem compound_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) := by
  ext I
  have e : (Matrix.of fun a b : Fin l => (g *ᵥ f b) (I.1.orderEmbOfFin I.2 a))
      = g.submatrix (I.1.orderEmbOfFin I.2) id * (Matrix.of fun (c : Fin n) (b : Fin l) => f b c) := by
    ext a b
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold BranchingSupport.wedge
  rw [e, Formalism.HermitianLatticeCounting.P.ge_cauchyBinet]
  unfold Matrix.mulVec dotProduct BranchingSupport.cmp
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [mul_comm]
  rfl

theorem compound_properties : ∀ (n l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ),
    BranchingSupport.cmp l (g * h) = BranchingSupport.cmp l g * BranchingSupport.cmp l h ∧ BranchingSupport.cmp l gᴴ = (BranchingSupport.cmp l g)ᴴ ∧
      BranchingSupport.cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 ∧
      ∀ f : Fin l → Fin n → ℂ, BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) :=
  fun n l g h => ⟨compound_mul l g h, compound_conjTranspose l g, compound_one n l, compound_mulVec_wedge g⟩

end GlobalTheory
end

