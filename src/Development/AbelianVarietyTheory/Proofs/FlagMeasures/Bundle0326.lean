module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0152
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0317
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0318
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVolMt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0320
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLevelCharacterMatchAtTypePrime
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Match

theorem diag_lift : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (d : Fin n → (kv F v)ˣ), ∃ D : GL (Fin n) (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∀ b, x b ∈ v.adicCompletionIntegers F) ↔ ∀ b, ((D : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ x) b ∈ v.adicCompletionIntegers F) ∧ ∀ M : Matrix (Fin n) (Fin n) (v.adicCompletion F), redM F v (((D⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * M * (D : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = diagonal (fun i => ((d i)⁻¹ : (kv F v)ˣ).1) * redM F v M * diagonal (fun i => ((d i : (kv F v)ˣ) : kv F v)) := by
  intro F _ _ v n d
  have hs := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers F)
  choose u hu using fun i => hs ((d i : (kv F v)ˣ) : kv F v)
  have hunit : ∀ i, IsUnit (u i) := fun i =>
    isUnit_of_map_unit (IsLocalRing.residue (v.adicCompletionIntegers F)) (u i) (by rw [hu i]; exact (d i).isUnit)
  let w : Fin n → (v.adicCompletionIntegers F)ˣ := fun i => (hunit i).unit
  let e : Fin n → (v.adicCompletion F)ˣ := fun i => Units.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).toMonoidHom (w i)
  have he : ∀ i, ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := fun i => (w i : v.adicCompletionIntegers F).2
  have he' : ∀ i, (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := fun i => (((w i)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  have hw : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers F) ((w i : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = ((d i : (kv F v)ˣ) : kv F v) := fun i => hu i
  have hw' : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers F) (((w i)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = (((d i)⁻¹ : (kv F v)ˣ) : kv F v) := by
    intro i
    have h1 := congrArg Units.val (map_inv (Units.map (IsLocalRing.residue (v.adicCompletionIntegers F)).toMonoidHom) (w i))
    have h2 : Units.map (IsLocalRing.residue (v.adicCompletionIntegers F)).toMonoidHom (w i) = d i := Units.ext (hw i)
    rw [h2] at h1
    exact h1
  let D : GL (Fin n) (v.adicCompletion F) :=
    ⟨diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F)),
      diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)),
      by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩
  refine ⟨D, fun x => ?_, fun M => ?_⟩
  · change _ ↔ ∀ b, (diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *ᵥ x) b ∈ _
    simp only [mulVec_diagonal]
    refine ⟨fun h b => mul_mem (he b) (h b), fun h b => ?_⟩
    have := mul_mem (he' b) (h b)
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  · change redM F v (diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * M *
      diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) = _
    ext a b
    have key : (diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * M *
        diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) a b =
        ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      simp only [diagonal_mul, mul_diagonal]
    simp only [diagonal_mul, mul_diagonal, redM]
    by_cases hM : M a b ∈ v.adicCompletionIntegers F
    · have hP : ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
        mul_mem (mul_mem (he' a) hM) (he b)
      rw [dite_eq_left (key ▸ hP), dite_eq_left hM, ← hw' a, ← hw b, ← map_mul, ← map_mul]
      congr 1
    · have hP : ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∉ v.adicCompletionIntegers F := by
        intro hP
        apply hM
        have := mul_mem (mul_mem (he a) hP) (he' b)
        have e1 : ((e a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * (((e b)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = M a b := by
          simp [mul_assoc]
        rwa [e1] at this
      rw [dite_eq_right (key ▸ hP), dite_eq_right hM]; simp

end GlobalTheory.St.G.Match

namespace GlobalTheory.St.G.Match

theorem nat_prime_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hpv : (p : 𝓞 F) ∈ v.asIdeal) : (q : 𝓞 F) ∉ v.asIdeal := by
  intro hqv
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : (a : 𝓞 F) * (p : 𝓞 F) + (b : 𝓞 F) * (q : 𝓞 F) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) hab
    push_cast at this; exact this
  rw [← h1]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hpv) (v.asIdeal.mul_mem_left _ hqv)

end GlobalTheory.St.G.Match

namespace GlobalTheory.St.G

theorem gmatch_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → ∀ (Fr : AdFrame cm.sig J (hat F S.Lb) (gp 0 * gp 1) k) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), ∃ κ ∈ levelVL cm.sig J v S.Lb, ∀ y ∈ levelVL cm.sig J v S.Lb, (Fr.LocK S.Lb v y ↔ κ⁻¹ * y * κ ∈ S.Uloc v) ∧ (Fr.LocK S.Lb v y → Fr.locChi v y = (lamJ (G.psi0 i v hv) (G.chiB i v hv) a t 0 sk (redM F v (G.mat i v hv (Gl.fr i v hv) (κ⁻¹ * y * κ))))⁻¹) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl Fr i v hv
  subst a sk fc
  have hTv : (T : 𝓞 F) ∉ v.asIdeal := fun h =>
    GlobalTheory.St.G.Match.nat_prime_not_mem v (gp i) T (hgp i) hT (fun e => hTg i e.symm) hv h
  have hTL := GlobalTheory.St.G.stepLevel_tLat F E n cm.sig J T f _ S
  have hSD := _root_.GlobalTheory.St.G.selfDualAt_of_tLat F E cm n J hJ hdet T f S.Lb hTL v hTv
  have hLat : IsLat S.Lb := ⟨S.Lb_fin, S.Lb_span⟩
  obtain ⟨fr', ψ', hψ', hfr', hK⟩ := _root_.GlobalTheory.St.G.frame_local_basis_unitriangular F E cm n J hJ hdet k t gp G S.Lb Fr hk hgp hne hspl hLat i v hv hSD
  have hcard := ((_root_.GlobalTheory.St.G.SplitPrime.split_place F E cm (gp i) (hgp i) (hspl i)).2 v hv).1
  haveI : Finite (kv F v) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (hgp i).ne_zero)
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.St.G.Torus.torus_transitive (kv F v) n t (G.psi0 i v hv) ψ' (G.chiB i v hv) (fun _ => 1) (G.psi_zero_nontrivial_character i v hv) hψ'
  obtain ⟨D, hDint, hDred⟩ := GlobalTheory.St.G.Match.diag_lift F v n d
  obtain ⟨κ, hκ, -⟩ := (GlobalTheory.T.split_place_lattice_components F E cm n J hJ hdet v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv)).2.1
    (fr' * D * (Gl.fr i v hv)⁻¹)
  have hphi : bc (G.phi i v hv) κ.1 = fr' * D * (Gl.fr i v hv)⁻¹ := hκ
  have hlev : κ.1 ∈ levelVL cm.sig J v S.Lb := by
    refine _root_.GlobalTheory.St.G.mem_levelVL_of_first_components F E cm n J v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) S.Lb hSD κ.1 κ.2 ?_
    intro x
    refine (Gl.fr_lat i v hv x).trans ?_
    refine Iff.trans ?_ (hfr' _).symm
    rw [hDint]
    rw [hκ]
    simp only [Units.val_mul, mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨κ.1, hlev, fun y hy => ?_⟩
  have hyκ : κ.1⁻¹ * y * κ.1 ∈ levelVL cm.sig J v S.Lb := mul_mem (mul_mem (inv_mem hlev) hy) hlev
  have hg : (Gl.fr i v hv)⁻¹ * bc (G.phi i v hv) (κ.1⁻¹ * y * κ.1) * Gl.fr i v hv
      = D⁻¹ * (fr'⁻¹ * bc (G.phi i v hv) y * fr') * D := by
    rw [map_mul, map_mul, map_inv, hphi]; group
  have hred : redM F v (G.mat i v hv (Gl.fr i v hv) (κ.1⁻¹ * y * κ.1)) =
      diagonal (fun j => ((d j)⁻¹ : (kv F v)ˣ).1) * redM F v (G.mat i v hv fr' y) * diagonal (fun j => ((d j : (kv F v)ˣ) : kv F v)) := by
    rw [← hDred]
    unfold GLoc.mat
    rw [hg, Units.val_mul, Units.val_mul]
  obtain ⟨hK1, hK2⟩ := hK y hy
  refine ⟨?_, fun hy' => ?_⟩
  · rw [hK1, (hd _).1, ← hred, Gl.mem i v hv _ hyκ]
  · rw [hK2 hy', (hd _).2, hred]

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjGaugeMeasureEqInvDetSmul
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConjScale

open Topology Filter

theorem integral_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ) :
    ∫ t, φ (L *ᵥ t) = |L.det|⁻¹ * ∫ t, φ t := by
  have hc : Continuous (Matrix.toLin' L) := LinearMap.continuous_of_finiteDimensional _
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hL
  have h2 : ∫ t, φ t ∂(Measure.map (Matrix.toLin' L) volume) = ∫ t, φ (Matrix.toLin' L t) :=
    integral_map hc.measurable.aemeasurable hφ.aestronglyMeasurable
  rw [h, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul] at h2
  simpa using h2.symm

theorem hasCompactSupport_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : HasCompactSupport φ) : HasCompactSupport (fun t => φ (L *ᵥ t)) := by
  have hu : IsUnit L.det := isUnit_iff_ne_zero.2 hL
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (Matrix.toLinearEquiv' L (Matrix.invertibleOfIsUnitDet L hu)).toContinuousLinearEquiv
  exact hφ.comp_homeomorph e.toHomeomorph

theorem scalar_eq_inv_det {X : Type} [MeasurableSpace X] (μ : Measure X) (T : X → X) (hT : Measurable T)
    (h : X → ℝ) (hh : Measurable h) {d : ℕ} (t : X → Fin d → ℝ) (ht : Measurable t)
    (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0) (c : NNReal) (hc : μ.map T = (c : ENNReal) • μ)
    (hTt : ∀ᵐ g ∂μ, t (T g) = L *ᵥ t g) (C : ℝ) (hC : 1 ≤ C) (h1 : ∀ g, h (T g) ≤ C * h g)
    (h2 : ∀ g, h g ≤ C * h (T g)) (ρ : ℝ) (hρ : 0 < ρ) (hfin : μ {g | h g < ρ} ≠ ⊤)
    (hlim : ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ ρ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | h g < r₁}, φ (fun i => t g i / r) ∂μ)
        (𝓝[>] 0) (𝓝 (∫ x, φ x))) :
    (c : ℝ) = |L.det|⁻¹ := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  let b : ContDiffBump (0 : Fin d → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : (Fin d → ℝ) → ℝ := b
  have hφc : Continuous φ := b.continuous
  have hφs : HasCompactSupport φ := b.hasCompactSupport
  have hφp : 0 < ∫ x, φ x := b.integral_pos
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => b.nonneg
  have hφ1 : ∀ x, φ x ≤ 1 := fun x => b.le_one
  let ψ : (Fin d → ℝ) → ℝ := fun x => φ (L *ᵥ x)
  have hψc : Continuous ψ := hφc.comp (continuous_const.matrix_mulVec continuous_id)
  have hψs : HasCompactSupport ψ := hasCompactSupport_comp_mulVec L hL φ hφs
  have hψi : ∫ x, ψ x = |L.det|⁻¹ * ∫ x, φ x := integral_comp_mulVec L hL φ hφc
  have hr1 : 0 < ρ / C := div_pos hρ hC0
  have hr1' : ρ / C ≤ ρ := div_le_self hρ.le hC
  have hr2 : 0 < ρ / C / C := div_pos hr1 hC0
  have hr2' : ρ / C / C ≤ ρ := (div_le_self hr1.le hC).trans hr1'
  have hB1 : MeasurableSet {g | h g < ρ / C} := measurableSet_lt hh measurable_const
  have hs1 : {g | h g < ρ / C / C} ⊆ T ⁻¹' {g | h g < ρ / C} := by
    intro g hg
    have hg : h g < ρ / C / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h1 g
    show h (T g) < ρ / C
    linarith
  have hs2 : T ⁻¹' {g | h g < ρ / C} ⊆ {g | h g < ρ} := by
    intro g hg
    have hg : h (T g) < ρ / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h2 g
    show h g < ρ
    linarith
  have hm : ∀ r : ℝ, Measurable (fun g => (fun i => t g i / r : Fin d → ℝ)) := fun r =>
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp ht).div_const r
  have hint : ∀ r : ℝ, IntegrableOn (fun g => ψ (fun i => t g i / r)) {g | h g < ρ} μ := by
    intro r
    refine Measure.integrableOn_of_bounded (M := 1) hfin (hψc.measurable.comp (hm r)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun g => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]
    exact hφ1 _
  have key : ∀ r : ℝ, (c : ℝ) * ∫ g in {g | h g < ρ / C}, φ (fun i => t g i / r) ∂μ
      = ∫ g in T ⁻¹' {g | h g < ρ / C}, ψ (fun i => t g i / r) ∂μ := by
    intro r
    have e1 := setIntegral_map (μ := μ) (g := T) (f := fun g => φ (fun i => t g i / r)) hB1
      (hφc.measurable.comp (hm r)).aestronglyMeasurable hT.aemeasurable
    rw [hc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul] at e1
    rw [e1]
    refine integral_congr_ae (ae_restrict_of_ae (hTt.mono fun g hg => ?_))
    have e2 : ∀ y : Fin d → ℝ, (fun i => y i / r) = r⁻¹ • y := fun y => by
      ext i; simp [div_eq_inv_mul]
    show φ (fun i => t (T g) i / r) = φ (L *ᵥ fun i => t g i / r)
    rw [e2, e2, hg, Matrix.mulVec_smul]
  have l1 := (hlim _ hr1 hr1' φ hφc hφs).const_mul (c : ℝ)
  have l2 := hlim _ hr2 hr2' ψ hψc hψs
  have l3 := hlim _ hρ le_rfl ψ hψc hψs
  have a1 : ∫ x, ψ x ≤ c * ∫ x, φ x := by
    refine le_of_tendsto_of_tendsto l2 l1 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set ((hint r).mono_set hs2) (Eventually.of_forall fun g => hφ0 _) (Filter.Eventually.of_forall hs1)
  have a2 : c * ∫ x, φ x ≤ ∫ x, ψ x := by
    refine le_of_tendsto_of_tendsto l1 l3 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set (hint r) (Eventually.of_forall fun g => hφ0 _) (Filter.Eventually.of_forall hs2)
  exact mul_right_cancel₀ hφp.ne' ((le_antisymm a2 a1).trans hψi)

theorem hs_conj_le {n : ℕ} {ε : Fin n → Bool} (m g : Formalism.REAL.UJ ε) :
    Formalism.REAL.hs (uMat (m * g * m⁻¹) - 1) ≤
      Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) * Formalism.REAL.hs (uMat g - 1) := by
  have a : uMat (m * g * m⁻¹) = uMat m * uMat g * uMat m⁻¹ := rfl
  have b : uMat m * uMat m⁻¹ = 1 := by
    have : uMat m * uMat m⁻¹ = uMat (m * m⁻¹) := rfl
    rw [this, mul_inv_cancel]; rfl
  have e : uMat (m * g * m⁻¹) - 1 = uMat m * (uMat g - 1) * uMat m⁻¹ := by
    rw [a, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, b]
  rw [e]
  refine (Formalism.REAL.frobenius_mul_le _ _).trans ?_
  rw [mul_right_comm]
  exact mul_le_mul_of_nonneg_right (Formalism.REAL.frobenius_mul_le _ _) (Formalism.REAL.frobenius_nonneg _)

theorem map_conj_eq_inv_det_smul (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E))
    (hS : ∀ g, g ∈ S ↔ uMat g - 1 ∈ A) (hcl : IsClosed (S : Set (Formalism.REAL.UJ ε)))
    (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ)
    (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ) (hm : ∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S)
    (hmL : ∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) (hL : L.det ≠ 0) :
    μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  have hSe : (S : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := Set.ext hS
  obtain ⟨-, hK, -, r₀, hr₀, hlim⟩ := GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hE hsp μ (hSe ▸ hμ)
  obtain ⟨h1, h2, h3⟩ := hμ
  have hp : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := Metric.measure_ball_pos _ _ one_pos
  have hf : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) < ⊤ := measure_ball_lt_top
  obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ :=
    (((h3.eventually (lt_mem_nhds hp)).and (h3.eventually (gt_mem_nhds hf))).and self_mem_nhdsWithin).exists
  have hr : 0 < r := hr
  have hcu : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((hcu.sub continuous_const).matrix_elem i j).norm).pow 2
  have hne : μ ≠ 0 := by
    rintro rfl
    simp at hr1
  have hfin : μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hr2
    exact lt_irrefl _ hr2
  obtain ⟨c, hcμ⟩ := _root_.GlobalTheory.ConjScalesMeasure.map_conj_eq_smul n ε S μ hcl h1 h2 hK hne m hm
  have hC0 : 0 ≤ Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) :=
    mul_nonneg (Formalism.REAL.frobenius_nonneg _) (Formalism.REAL.frobenius_nonneg _)
  have hT : Continuous (fun u : Formalism.REAL.UJ ε => m * u * m⁻¹) := by fun_prop
  have ht : Continuous (fun (g : Formalism.REAL.UJ ε) (i : Fin d) => (((uMat g - 1) * (E i)ᴴ).trace).re) :=
    continuous_pi fun i => Complex.continuous_re.comp
      (((hcu.sub continuous_const).matrix_mul continuous_const).matrix_trace)
  have key := scalar_eq_inv_det μ (fun u => m * u * m⁻¹) hT.measurable _ hc.measurable _ ht.measurable L hL c hcμ
    ?_ (Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) + 1) (by linarith) ?_ ?_ (min r₀ (r ^ 2))
    (lt_min hr₀ (by positivity)) ?_ (fun r₁ a b => hlim r₁ a (b.trans (min_le_left _ _)))
  · rw [hcμ, ← key, ENNReal.ofReal_coe_nnreal]
  · have : ∀ᵐ g ∂μ, g ∈ (S : Set (Formalism.REAL.UJ ε)) := h1
    filter_upwards [this] with g hg
    exact _root_.GlobalTheory.UnitaryCoords.coords_conj n ε A d E hE hsp g m L ((hS g).1 hg) ((hS _).1 (S.inv_mem hg)) hmL
  · intro g
    have := hs_conj_le m g
    have := Formalism.REAL.frobenius_nonneg (uMat g - 1)
    linarith
  · intro g
    have h4 := hs_conj_le m⁻¹ (m * g * m⁻¹)
    have e : m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ = g := by group
    rw [e, inv_inv] at h4
    have := Formalism.REAL.frobenius_nonneg (uMat (m * g * m⁻¹) - 1)
    linarith
  · refine ne_top_of_le_ne_top hfin (measure_mono fun g hg => ?_)
    have hg : Formalism.REAL.hs (uMat g - 1) < min r₀ (r ^ 2) := hg
    exact Real.sqrt_le_iff.2 ⟨hr.le, (hg.trans_le (min_le_right _ _)).le⟩

end GlobalTheory.GaugeConjScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeBetweenFrameAndComplementPartsStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitLattice_between_frameAndComplementParts : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ N : ℕ, 0 < N ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')) := by
  first
  | exact @GlobalTheory.FrameProj.lattice_between_parts
  | exact GlobalTheory.FrameProj.lattice_between_parts
  | intros
    apply GlobalTheory.FrameProj.lattice_between_parts
    all_goals first
      | assumption
      | haveI : Submodule.IsFullLattice _ _ := by assumption
        infer_instance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsScalarInUnipotentRadicalDoubleCosetStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_isScalar_in_unipotentRadical_doubleCoset : ∀ (D : D7) {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T'), Submodule.IsLattice D.host.E Λ → F.zt = F.fl.z → F'.zt = F'.fl.z → F''.zt = F''.fl.z → ∀ n ∈ NRat F, ∀ m ∈ NRat F', (∀ a, frame F'' a = (n * m) (frame F' a)) → IsScalar Λ F F' F'' (n * m) := by
  first | exact @GlobalTheory.SnFam.CvScal.pair_scalar | exact GlobalTheory.SnFam.CvScal.pair_scalar | (intros; apply GlobalTheory.SnFam.CvScal.pair_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalMatrixRepresentsAdelicPointInFrameStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_matrix_represents_adelic_point_in_frame : ∀ (D : D7) (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsAdeleIso X ιA → ∀ (h : X.B.I.Gf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), X.B.I.fmat h = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), y.1.1 = (y₀.map X.ιE).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) → RepF X wt ιA h y := by
  first | exact @GlobalTheory.St.repF_of_rational | exact GlobalTheory.St.repF_of_rational | (intros; apply GlobalTheory.St.repF_of_rational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalStabiliserPointFromUnitaryFixingFrameStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u), ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∧ ∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
  first | exact @GlobalTheory.GamRat.gam_rat | exact GlobalTheory.GamRat.gam_rat | (intros; apply GlobalTheory.GamRat.gam_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingMemRationalStabiliserStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_fixing_mem_rationalStabiliser : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ₀ : GL (Fin X.B.I.n) X.B.I.E), γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ γ : Gam X u, (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
  first | exact @GlobalTheory.St.rat_unitary_fixing_mem_gam | exact GlobalTheory.St.rat_unitary_fixing_mem_gam | (intros; apply GlobalTheory.St.rat_unitary_fixing_mem_gam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocalStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (ν : Measure X.B.I.Ginf), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) → IsQuotMeasS X.B.I (Measure.pi μl) ν → (∀ v, ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v), ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (s * x)) (X.Wloc u' v ((γ v)⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v x) (X.Wloc u' v ((γ v)⁻¹ * x))) → hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vpi u); Formalism.L2.SG.TermOp.OO ν Set.univ (X.Wu u) (X.Wu u') γ) = ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (γ v)) := by
  first | exact @GlobalTheory.OrbQuotProd.oo_quot | exact GlobalTheory.OrbQuotProd.oo_quot | (intros; apply GlobalTheory.OrbQuotProd.oo_quot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasure
section
noncomputable section

namespace GlobalTheory.GaugeKExists

theorem gaugeK : PI.RhsWLim.W.GaugeK := by
  intro k r _
  exact ⟨Formalism.L2.SG.Pf.GV.nu0 k r, Formalism.L2.SG.Pf.GV.gauge_measure_is_gauge⟩

end GlobalTheory.GaugeKExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ d d' : LocNG.Datum P, LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ P.Hp = S.Hp ∧ (P.PrimeTo → S.Hp = 1) ∧ ∀ (R : LocNG.Reps P) (d : LocNG.Datum P), LocNG.amp R d (LocNG.BBne (H := H)) = S.amp (c.dat d) (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧ LocNG.amp R d (fun t => ¬ LocNG.BBne (H := H) t) = S.amp (c.dat d) (S.BBzero (c.dat d)) := by
  first | exact @GlobalTheory.HL.WCoordTerms.terms_orbits_heights_amps | exact GlobalTheory.HL.WCoordTerms.terms_orbits_heights_amps | (intros; apply GlobalTheory.HL.WCoordTerms.terms_orbits_heights_amps <;> assumption)
end

