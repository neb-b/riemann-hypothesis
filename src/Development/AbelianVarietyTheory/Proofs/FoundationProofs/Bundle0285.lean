module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0207
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicUnitaryOfLocalFamilyAlmostAllTrivial
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalUnitaryGlue

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem exists_on_finset (γ : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ k : HA (Af F) σ J, (∀ v ∈ S, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = γ v) ∧
      ∀ v ∉ S, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => map_one _⟩
  | insert a S ha ih =>
    obtain ⟨k, h1, h2⟩ := ih
    have s1 : mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F a) (extH σ J (sgV a) (sgV_mul a) (γ a)) = γ a :=
      mapH_extH_self σ J _ _ _ (fun y => Pi.single_eq_same a y) _
    have s2 : ∀ w, w ≠ a →
        mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (extH σ J (sgV a) (sgV_mul a) (γ a)) = 1 :=
      fun w hw => mapH_extH_zero σ J _ _ _ (fun y => Pi.single_eq_of_ne hw y) _
    refine ⟨extH σ J (sgV a) (sgV_mul a) (γ a) * k, fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [s1, h2 _ ha, mul_one]
      · rw [s2 v (fun e => ha (e ▸ hv)), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, s2 v hv.1, h2 v hv.2, one_mul]

theorem exists_of_finite (γ : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (h : {v | γ v ≠ 1}.Finite) :
    ∃ k : HA (Af F) σ J, ∀ v, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = γ v := by
  obtain ⟨k, h1, h2⟩ := exists_on_finset σ J γ h.toFinset
  refine ⟨k, fun v => ?_⟩
  by_cases hv : v ∈ h.toFinset
  · exact h1 v hv
  · rw [h2 v hv]
    simpa [eq_comm] using hv

end Gen

theorem exists_finite_adelic : ∀ (D : D7) (V : HSp D) (γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram), {v | γ v ≠ 1}.Finite → ∃ k ∈ GfC V, ∀ v : HeightOneSpectrum (𝓞 D.host.F), (finMat D.sp.cm.sig V.gram k).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) = (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1 := by
  intro D V γ h
  obtain ⟨k, hk⟩ := exists_of_finite D.sp.cm.sig V.gram γ h
  refine ⟨ofFin D.sp.cm V k, ?_, fun v => ?_⟩
  · exact congrArg (HA.mat _ _ _) (projInf_ofFin D.sp.cm V k)
  · have e : finMat D.sp.cm.sig V.gram (ofFin D.sp.cm V k) = (HA.mat _ _ _ k).1 :=
      congrArg (fun x => (HA.mat _ _ _ x).1) (projFin_ofFin D.sp.cm V k)
    rw [e, ← hk v]
    rfl

end GlobalTheory.LocalUnitaryGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOtherHalfPeriod
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HalfPeriod

theorem half_comb_not_mem (w₁ w₂ : ℂ) (hind : LinearIndependent ℝ ![w₁, w₂]) (a b : ℤ)
    (hab : ¬ (2 ∣ a ∧ 2 ∣ b)) :
    ((a : ℂ) * w₁ + (b : ℂ) * w₂) / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
  intro h
  rw [AddSubgroup.mem_closure_pair] at h
  obtain ⟨m, n, hmn⟩ := h
  rw [LinearIndependent.pair_iff] at hind
  have key : ((a - 2 * m : ℤ) : ℝ) • w₁ + ((b - 2 * n : ℤ) : ℝ) • w₂ = 0 := by
    rw [zsmul_eq_mul, zsmul_eq_mul] at hmn
    simp only [Complex.real_smul]
    push_cast
    linear_combination (-2 : ℂ) * hmn
  obtain ⟨h1, h2⟩ := hind _ _ key
  have h1' : a - 2 * m = 0 := by exact_mod_cast h1
  have h2' : b - 2 * n = 0 := by exact_mod_cast h2
  exact hab ⟨⟨m, by omega⟩, ⟨n, by omega⟩⟩

theorem exists_other_half_period : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ,
    2 * P ∈ Λ → P ∉ Λ → ∃ P' : ℂ, 2 * P' ∈ Λ ∧ P' ∉ Λ ∧ P - P' ∉ Λ := by
  rintro Λ ⟨w₁, w₂, hind, rfl⟩ P _ _
  have hw₁ : w₁ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) :=
    AddSubgroup.subset_closure (by simp)
  have hw₂ : w₂ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) :=
    AddSubgroup.subset_closure (by simp)
  have n₁ : w₁ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 1 0 (by decide)
    simpa using this
  have n₂ : w₂ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 0 1 (by decide)
    simpa using this
  have n₃ : (w₁ - w₂) / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 1 (-1) (by decide)
    convert this using 2
    push_cast; ring
  by_cases hP : P - w₁ / 2 ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)
  · refine ⟨w₂ / 2, by rw [mul_div_cancel₀ _ two_ne_zero]; exact hw₂, n₂, ?_⟩
    intro h
    apply n₃
    have := AddSubgroup.sub_mem _ h hP
    convert this using 1
    ring
  · exact ⟨w₁ / 2, by rw [mul_div_cancel₀ _ two_ne_zero]; exact hw₁, n₁, hP⟩

end GlobalTheory.HalfPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil


set_option maxHeartbeats 1000000 in
theorem exists_weil_of_vacuum (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (N N' : ℕ)
    (e0 : VC D N N' → ℂ) (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (h0 : e0 ≠ 0) (χ : HeckeU D N) (χ' : HeckeU D N') :
    ∃ W : WeilO D cc δ N N' e0, W.chV = χ ∧ W.chV' = χ' ∧ W.ep = 1 ∧ W.ep' = 1 := by
  have hg : admG1 D := (_root_.GlobalTheory.InducedType.induced_type D).1
  obtain ⟨w, γ, WA, hM⟩ := GlobalTheory.T.exists_adelicWeilRepresentationModel D hg cc δ hc N N'
  obtain ⟨hT, hfix, hspan⟩ := _root_.GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span D hg cc δ hc N N' w γ WA hM e0 he h0
  obtain ⟨lam, hlam, hsq⟩ := _root_.GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨c', hc1', hc2'⟩ := _root_.GlobalTheory.SplitCharacter.exists_split_character D N χ N'
  obtain ⟨c, hc1, hc2⟩ := _root_.GlobalTheory.SplitCharacter.exists_split_character D N' χ' N
  have hidx := _root_.GlobalTheory.FinWeil.idx_map_actA D hg cc δ hc N N'
  have hM' := hM
  obtain ⟨hH, hSD, hinv, hrat, hcont⟩ := hM'
  obtain ⟨Om, hOm1, hOm2⟩ := GlobalTheory.T.exists_weil_representation_heisenberg hH lam hlam _ hSD ⟨e0, hT⟩ (fun h => h0 (congrArg Subtype.val h)) hfix hspan
    (actA D N N') hinv (fun u => (hidx u.1 u.2).1)
  let O : GA D N → GA D N' → (VC D N N' → ℂ) → (VC D N N' → ℂ) := fun g g' F =>
    if h : F ∈ TTs D (tor0 D cc δ) N N' then
      ((((c' g' * c g : ℂˣ) : ℂ) • Om (g, g') ⟨F, h⟩ : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) else 0
  have hO : ∀ g g' (F : TTs D (tor0 D cc δ) N N'), O g g' F =
      ((((c' g' * c g : ℂˣ) : ℂ) • Om (g, g') F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := fun g g' F => dif_pos F.2
  refine ⟨{ nz := h0, chV := χ, chV' := χ', ep := 1, ep' := 1, ep_pm := ⟨Or.inl rfl, Or.inl rfl⟩, Om := O,
            maps := ?_, add := ?_, smul := ?_, one := ?_, mul := ?_, lift := ?_, inert := ?_, split := ?_ }, rfl, rfl, rfl, rfl⟩
  · intro g g' F hF
    rw [hO g g' ⟨F, hF⟩]
    exact Subtype.property _
  · intro g g' F hF F' hF'
    have := hO g g' (⟨F, hF⟩ + ⟨F', hF'⟩)
    rw [map_add (f := _), smul_add, Submodule.coe_add, Submodule.coe_add, ← hO, ← hO] at this
    exact this
  · intro g g' a F hF
    have := hO g g' (a • ⟨F, hF⟩)
    rw [map_smul, smul_comm, Submodule.coe_smul, Submodule.coe_smul a, ← hO] at this
    exact this
  · intro F hF
    rw [hO 1 1 ⟨F, hF⟩, map_one, map_one, mul_one, Units.val_one, one_smul, Prod.mk_one_one, map_one]
    rfl
  · intro g₁ g₂ g₁' g₂' F hF
    rw [hO _ _ ⟨F, hF⟩, hO g₂ g₂' ⟨F, hF⟩, hO, map_smul, smul_smul, ← Prod.mk_mul_mk, map_mul Om, map_mul, map_mul,
      ← Units.val_mul, mul_mul_mul_comm]
    rfl
  · intro g g' z F hF
    obtain ⟨m, hm, h⟩ := hcont (actA D N N' (g, g') (z.map (inc D))) (Om (g, g') ⟨F, hF⟩)
    refine ⟨m, hm, fun z' hz' => ?_⟩
    choose a ha1 ha2 using hz'
    have h1 : z'.map (inc D) = actA D N N' (g, g') (z.map (inc D)) + m • (Matrix.of a : XA D N N') := by
      rw [← sub_eq_iff_eq_add']
      ext i j
      rw [actA_apply, ha2 i j, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    have h2 := hrat z ⟨F, hF⟩
    rw [← h2, hO, hO g g' ⟨F, hF⟩, ← hrat, map_smul, hOm1, h1, h (Matrix.of a) ha1]
  · intro k k' hk hk' hs hs'
    have h3 := (GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ (hOm2 (k, k')).1).2.2 ((hidx k k').2.2 hk hk')
    rw [hO k k' ⟨e0, hT⟩, hc1 k hs, hc1' k' hs', mul_one, Units.val_one, one_smul, (hOm2 (k, k')).2, normOp, h3.1,
      h3.2 _ hfix, map_one, inv_one, one_smul]
  · intro g g' x x' L₁ L₁' hs hs' hx h1 h1' hL hL'
    have h3 := _root_.GlobalTheory.FinWeil.iop_eq_sumOp D hg cc δ hc N N' w γ WA hM g g' L₁ L₁' hL hL' (hOm2 (g, g')).1 ⟨e0, hT⟩ hfix
    have h4 := hsq _ (hidx g g').1 fun q hq hi => (hidx g g').2.1 q hq (hs q hq hi) (hs' q hq hi)
    rw [hO g g' ⟨e0, hT⟩, hc2 g x (fun q hq hi => (hx q hq hi).1) h1, hc2' g' x' (fun q hq hi => (hx q hq hi).2) h1',
      (hOm2 (g, g')).2, normOp, h4, Submodule.coe_smul, Submodule.coe_smul, ← h3, zpow_one, zpow_one]
    rfl

theorem exists_weil : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even N → Even N' → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ (χ : HeckeU D N) (χ' : HeckeU D N'), ∃ W : WeilO D cc δ N N' e0, W.chV = χ ∧ W.chV' = χ' ∧ W.ep = 1 ∧ W.ep' = 1 :=
  fun D cc δ hc N N' _ _ e0 he h0 χ χ' => exists_weil_of_vacuum D cc δ hc N N' e0 he h0 χ χ'

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lam_ballU_le_ofReal_pow : ∀ (p q : ℕ) (lam : Measure (lieU p q)), IsOmegaLeb lam → ∀ r : ℝ, 0 < r → lam (ballU p q r) ≤ ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) := by
  first | exact @GlobalTheory.CartanInt.LamBall.lam_ballU_le | exact GlobalTheory.CartanInt.LamBall.lam_ballU_le | (intros; apply GlobalTheory.CartanInt.LamBall.lam_ballU_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralExpNegMulSumNormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_exp_neg_mul_sum_norm_matrix : ∀ (p q : ℕ) (b : ℝ), 0 < b → ∫⁻ B : Fin p → Fin q → ℂ, ENNReal.ofReal (Real.exp (-(b * ∑ i, ∑ j, ‖B i j‖))) = ENNReal.ofReal ((2 * Real.pi / b ^ 2) ^ (p * q)) := by
  first | exact @GlobalTheory.CartanInt.lintegral_exp_neg_mul_sum_norm | exact GlobalTheory.CartanInt.lintegral_exp_neg_mul_sum_norm | (intros; apply GlobalTheory.CartanInt.lintegral_exp_neg_mul_sum_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPadicModelAbscissaLeOneOfTorsionCoprime
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TorsionAbscissa

theorem norm_xAt_le_of_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ (N : ℕ) (v : ℂ), 0 < N → Nat.Coprime N p → (N : ℂ) * v ∈ g.abelian₂ → v ∉ g.abelian₂ → ‖GlobalTheory.EvenTheta.xAt g v‖ ≤ 1 := by
  intro D p _ cc δ g hg N v hN hcop hNv hv
  exact norm_xAt_le D p cc δ g hg v ⟨hv, N, hN, hcop, hNv⟩

end GlobalTheory.TorsionAbscissa
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubAbscissaEqOneOfUnitDiscrIntegralChords
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar

variable {p : ℕ} [Fact p.Prime]

theorem norm_le_one_of_quad {a c m : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (h : ‖m ^ 2 + a * m - c‖ ≤ 1) : ‖m‖ ≤ 1 := by
  by_contra hm
  push_neg at hm
  have e : m ^ 2 = (m ^ 2 + a * m - c) + (-(a * m) + c) := by ring
  have hb : ‖m ^ 2‖ ≤ ‖m‖ := by
    rw [e]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (h.trans hm.le) ?_)
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (hc.trans hm.le))
    rw [norm_neg, norm_mul]
    calc ‖a‖ * ‖m‖ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ = ‖m‖ := one_mul _
  rw [norm_pow, sq] at hb
  have : 1 * ‖m‖ < ‖m‖ * ‖m‖ := mul_lt_mul_of_pos_right hm (by linarith)
  linarith

theorem norm_sub_x_eq_one : ∀ {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x₁ y₁ x₂ y₂ m m' : ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.Δ‖ = 1 → W.toAffine.Equation x₁ y₁ → W.toAffine.Equation x₂ y₂ → ‖x₁‖ ≤ 1 → ‖x₂‖ ≤ 1 → x₁ ≠ x₂ → m * (x₁ - x₂) = y₁ - y₂ → m' * (x₁ - x₂) = y₁ - W.toAffine.negY x₂ y₂ → ‖m ^ 2 + W.a₁ * m - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖m' ^ 2 + W.a₁ * m' - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖x₁ - x₂‖ = 1 := by
  intro p _ W x₁ y₁ x₂ y₂ m m' h1 h2 hΔ he1 he2 hx1 hx2 hne hm hm' hq hq'
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hle : ‖x₁ - x₂‖ ≤ 1 := by
    rw [sub_eq_add_neg]; exact it_add hx1 (by rwa [norm_neg])
  refine le_antisymm hle (not_lt.mp fun hs => ?_)
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2
  have c12 : ‖W.a₂ + x₁ + x₂‖ ≤ 1 := it_add (it_add h2 hx1) hx2
  have mb : ‖m‖ ≤ 1 := norm_le_one_of_quad h1 c12
    (by rwa [show m ^ 2 + W.a₁ * m - (W.a₂ + x₁ + x₂) = m ^ 2 + W.a₁ * m - W.a₂ - x₁ - x₂ by ring])
  have mb' : ‖m'‖ ≤ 1 := norm_le_one_of_quad h1 c12
    (by rwa [show m' ^ 2 + W.a₁ * m' - (W.a₂ + x₁ + x₂) = m' ^ 2 + W.a₁ * m' - W.a₂ - x₁ - x₂ by ring])
  have s1 : ‖y₁ - y₂‖ < 1 := by rw [← hm, mul_comm]; exact sm_mul' hs mb
  have s2 : ‖y₁ + y₂ + W.a₁ * x₂ + W.a₃‖ < 1 := by
    have e : y₁ + y₂ + W.a₁ * x₂ + W.a₃ = m' * (x₁ - x₂) := by
      rw [hm']; simp only [WeierstrassCurve.Affine.negY]; ring
    rw [e, mul_comm]; exact sm_mul' hs mb'
  have s3 : ‖W.a₁ * (x₁ - x₂)‖ < 1 := sm_mul h1 hs
  have hy : ‖2 * y₁ + W.a₁ * x₁ + W.a₃‖ < 1 := by
    rw [show 2 * y₁ + W.a₁ * x₁ + W.a₃ =
      (y₁ - y₂) + (y₁ + y₂ + W.a₁ * x₂ + W.a₃) + W.a₁ * (x₁ - x₂) by ring]
    exact sm_add (sm_add s1 s2) s3
  have s4 : ‖y₁ + y₂ + W.a₁ * x₁ + W.a₃‖ < 1 := by
    rw [show y₁ + y₂ + W.a₁ * x₁ + W.a₃ = (y₁ + y₂ + W.a₁ * x₂ + W.a₃) + W.a₁ * (x₁ - x₂) by ring]
    exact sm_add s2 s3
  have e1 := he1
  have e2 := he2
  rw [WeierstrassCurve.Affine.equation_iff] at e1 e2
  have hN : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂ =
      m * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) := by
    apply mul_right_cancel₀ hd
    have hsub : (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) = (x₁ - x₂) *
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂) := by
      linear_combination e1 - e2
    linear_combination -hsub - (y₁ + y₂ + W.a₁ * x₁ + W.a₃) * hm
  have hN' : ‖x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂‖ < 1 := by
    rw [hN]; exact sm_mul mb s4
  have hx' : ‖3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁‖ < 1 := by
    rw [show 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ =
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂) -
        ((x₂ - x₁) * (x₂ + 2 * x₁ + W.a₂) + W.a₁ * (y₁ - y₂)) by ring]
    refine sm_sub hN' (sm_add ?_ (sm_mul h1 s1))
    exact sm_mul' (by rw [← norm_neg, neg_sub]; exact hs) (it_add (it_add hx2 (it_mul n2 hx1)) h2)
  have hc := disc_small W x₁ y₁ h1 h2 hx1 he1 hy hx'
  rw [hΔ] at hc
  exact lt_irrefl _ hc

end GlobalTheory.ThetaPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormTangentDenominatorEqOneOfUnitDiscrDouble
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaPar

theorem padicComplex_norm_le_max_norm_add_norm {p : ℕ} [Fact p.Prime] {a b : ℂ_[p]} :
    ‖a‖ ≤ max ‖a + b‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max (a + b) (-b)
  simpa using this

theorem unit_of_double_integral_sub {p : ℕ} [Fact p.Prime] (a b : ℂ_[p]) :
    ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max a (-b)
  simpa [sub_eq_add_neg] using this

theorem unit_of_double_integral {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x y m : ℂ_[p])
    (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1)
    (hΔ : ‖W.Δ‖ = 1) (he : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1)
    (_hη : 2 * y + W.a₁ * x + W.a₃ ≠ 0)
    (hm : m * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hm2 : ‖m ^ 2 + W.a₁ * m - W.a₂ - 2 * x‖ ≤ 1) :
    ‖2 * y + W.a₁ * x + W.a₃‖ = 1 := by
  have he' := he
  rw [WeierstrassCurve.Affine.equation_iff] at he'
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2

  have hy : ‖y‖ ≤ 1 := by
    by_contra hy
    push_neg at hy
    have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 := by
      refine it_add (it_add (it_add ?_ (it_mul h2 ?_)) (it_mul h4 hx)) h6
      · rw [show x ^ 3 = x * x * x by ring]; exact it_mul (it_mul hx hx) hx
      · rw [sq]; exact it_mul hx hx
    have hS : ‖(W.a₁ * x + W.a₃) * y‖ ≤ ‖y‖ := by
      rw [norm_mul]
      calc ‖W.a₁ * x + W.a₃‖ * ‖y‖ ≤ 1 * ‖y‖ :=
            mul_le_mul_of_nonneg_right (it_add (it_mul h1 hx) h3) (norm_nonneg _)
        _ = ‖y‖ := one_mul _
    have hyy : ‖y‖ < ‖y ^ 2‖ := by
      rw [norm_pow, sq]; nlinarith
    have key := padicComplex_norm_le_max_norm_add_norm (a := y ^ 2) (b := (W.a₁ * x + W.a₃) * y)
    have hsum : y ^ 2 + (W.a₁ * x + W.a₃) * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
      linear_combination he'
    rw [hsum] at key
    have : ‖y ^ 2‖ ≤ 1 := by
      rcases le_max_iff.mp key with h | h
      · exact h.trans hR
      · exact absurd (h.trans hS) (not_le.mpr hyy)
    linarith
  have hηle : ‖2 * y + W.a₁ * x + W.a₃‖ ≤ 1 :=
    it_add (it_add (it_mul n2 hy) (it_mul h1 hx)) h3
  refine le_antisymm hηle (not_lt.mp fun hlt => ?_)

  have hmi : ‖m‖ ≤ 1 := by
    by_contra hmg
    push_neg at hmg
    have hT : ‖W.a₁ * m - W.a₂ - 2 * x‖ ≤ ‖m‖ := by
      have hm1 : (1 : ℝ) ≤ ‖m‖ := hmg.le
      refine le_trans (unit_of_double_integral_sub _ _) (max_le ?_ ?_)
      · refine le_trans (unit_of_double_integral_sub _ _) (max_le ?_ (h2.trans hm1))
        rw [norm_mul]
        calc ‖W.a₁‖ * ‖m‖ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = ‖m‖ := one_mul _
      · exact (it_mul n2 hx).trans hm1
    have hmm : ‖m‖ < ‖m ^ 2‖ := by rw [norm_pow, sq]; nlinarith
    have key := padicComplex_norm_le_max_norm_add_norm (a := m ^ 2) (b := W.a₁ * m - W.a₂ - 2 * x)
    rw [show m ^ 2 + (W.a₁ * m - W.a₂ - 2 * x) = m ^ 2 + W.a₁ * m - W.a₂ - 2 * x by ring] at key
    have : ‖m ^ 2‖ ≤ 1 := by
      rcases le_max_iff.mp key with h | h
      · exact h.trans hm2
      · exact absurd (h.trans hT) (not_le.mpr hmm)
    nlinarith [norm_nonneg m, show ‖m ^ 2‖ = ‖m‖ * ‖m‖ by rw [norm_pow, sq]]
  have hsmall : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ < 1 := by
    rw [← hm]; exact sm_mul hmi hlt
  have := disc_small W x y h1 h2 hx he hlt hsmall
  linarith

end GlobalTheory.ThetaPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarMulSqEqProdKernelQuotientsStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStar_mul_sq_eq_prod_kernel_quotients : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (β : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ ∧ β * Q i ∈ Λ) ∧ ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := by
  first | exact @GlobalTheory.EvenTheta.MulLat.sg_mul_sq | exact GlobalTheory.EvenTheta.MulLat.sg_mul_sq | (intros; apply GlobalTheory.EvenTheta.MulLat.sg_mul_sq <;> assumption)
end

