module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRootSubOneLengthLeTameValue
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.LocalRingCardinality.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscCocycleFrobeniusEquation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.CocycleFrob

theorem σA_frob {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff l g, WittVector.map_coeff, WittVector.map_coeff,
    GlobalTheory.RingIface.sigA_coeff l g, frobenius_def, frobenius_def, map_pow]

theorem cancel_left {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    (Y X₁ X₂ : Matrix n n R) (c : R) (hc : c ≠ 0) (hY : Y.det ≠ 0) (h : c • (Y * X₁) = c • (Y * X₂)) :
    X₁ = X₂ := by
  have h1 : Y * X₁ = Y * X₂ := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this
  have h2 := congrArg (fun Z => Y.adjugate * Z) h1
  simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h2
  ext i j
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hY this

theorem frob_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev) → (Y.map bk.iA).det ≠ 0 → ∀ (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (w : (Ainf l)ˣ), Per.σA g (bk.ev bk.E) = bk.ev bk.E * w → ∀ (P : Matrix (Fin d) (Fin d) (Ainf l)), P.map WittVector.frobenius = P → ∀ (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA) → bk.iS bk.E ^ (2 * N) • e = (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA := by
  intro l _ K bk τ hτ d M N Y A A' hAA hφ hdet g G Φ _ hΦ w hw P hP e he
  obtain ⟨-, -, -, h0, h1, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  obtain ⟨-, -, -, hστ⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have ht' : bk.iA (Per.σA g τ) ≠ 0 := by
    rw [← map_zero bk.iA]
    intro h
    have h2 := hστ g
    rw [hinj h, map_zero] at h2
    exact not_isUnit_zero h2
  have hE : bk.iA (bk.ev bk.E) ≠ 0 := by
    rw [← map_zero bk.iA]
    intro h
    exact bk.E_ne_zero (bk.ev_injective ((hinj h).trans (map_zero _).symm))
  have hu : bk.iA (w : Ainf l) ≠ 0 := fun h => by
    have := congrArg bk.iA w.mul_inv
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this

  have hΦA : ∀ x, Φ (bk.iA x) = bk.iA (WittVector.frobenius x) := hΦ.ext
  have hσE : ∀ k : ℕ, bk.iA (Per.σA g (bk.ev bk.E ^ k)) = (bk.iA (bk.ev bk.E) * bk.iA w) ^ k := fun k => by
    rw [map_pow, hw, map_pow, map_mul]

  have hφ1 : bk.iA (bk.ev bk.E) ^ N • (Y.map WittVector.frobenius).map bk.iA =
      bk.iA (bk.ev bk.E) ^ M • (Y.map bk.iA * (A.map bk.ev).map bk.iA) := by
    have := congrArg (fun X => X.map bk.iA) hφ
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_mul, map_pow] at this
    exact this

  have hφ2 : (bk.iA (bk.ev bk.E) * bk.iA w) ^ N • ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA =
      (bk.iA (bk.ev bk.E) * bk.iA w) ^ M • ((Y.map (Per.σA g)).map bk.iA * ((A.map bk.ev).map (Per.σA g)).map bk.iA) := by
    have := congrArg (fun X => (X.map (Per.σA g)).map bk.iA) hφ
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_smul' _ _ _ (map_mul (Per.σA g)),
      Matrix.map_mul] at this
    rw [hσE, hσE] at this
    have hc : ((Y.map WittVector.frobenius).map (Per.σA g)) = ((Y.map (Per.σA g)).map WittVector.frobenius) := by
      exact Matrix.ext fun i j => σA_frob g (Y i j)
    rw [hc] at this
    exact this

  have he1 : (bk.iA (bk.ev bk.E) * bk.iA w * bk.iA (Per.σA g τ)) ^ M • ((Y.map WittVector.frobenius).map bk.iA * e.map Φ) =
      (bk.iA (bk.ev bk.E) * bk.iA τ) ^ M • (P.map bk.iA * ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA) := by
    have := congrArg (fun X => X.map Φ) he
    simp only [Matrix.map_smul' _ _ _ (map_mul Φ), Matrix.map_mul, map_pow, hΦA] at this
    have m1 : ∀ Z : Matrix (Fin d) (Fin d) (Ainf l), (Z.map bk.iA).map Φ = (Z.map WittVector.frobenius).map bk.iA :=
      fun Z => Matrix.ext fun i j => hΦA (Z i j)
    rw [m1, m1, m1, hP, ← σA_frob, hτ.1, map_mul, hw, map_mul, map_mul, map_mul] at this
    exact this
  have hA2 : ((A.map bk.ev).map (Per.σA g)).map bk.iA * ((A'.map bk.ev).map (Per.σA g)).map bk.iA =
      (bk.iA (bk.ev bk.E) * bk.iA w) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have := congrArg (fun X => ((X.map bk.ev).map (Per.σA g)).map bk.iA) hAA
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_smul' _ _ _ (map_mul (Per.σA g)),
      Matrix.map_smul' _ _ _ (map_mul bk.ev), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [map_pow bk.ev, hσE] at this
    exact this
  have hv : bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) * bk.iA w = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hiS : bk.iS bk.E = bk.iA (bk.ev bk.E) := rfl
  rw [hiS, Matrix.map_smul' _ _ _ (map_mul bk.iA), map_pow]
  generalize (Y.map WittVector.frobenius).map bk.iA = ΦY at hφ1 he1
  generalize ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA = ΦGY at hφ2 he1
  generalize (Y.map (Per.σA g)).map bk.iA = GY at hφ2 he
  generalize Y.map bk.iA = YY at hφ1 he hdet
  generalize (A.map bk.ev).map bk.iA = AA at hφ1 ⊢
  generalize ((A.map bk.ev).map (Per.σA g)).map bk.iA = GA at hφ2 hA2
  generalize ((A'.map bk.ev).map (Per.σA g)).map bk.iA = GA' at hA2 ⊢
  generalize P.map bk.iA = PP at he he1
  generalize e.map Φ = Φe at he1 ⊢
  generalize bk.iA (bk.ev bk.E) = E' at *
  generalize bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) = v at *
  generalize bk.iA (w : Ainf l) = u at *
  generalize bk.iA (Per.σA g τ) = t' at *
  generalize bk.iA τ = t at *
  have key : (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (u ^ N • (AA * Φe))) =
      (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (e * GA)) :=
    calc (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (u ^ N • (AA * Φe)))
        = (u ^ N * (E' * u * t') ^ M) • ((E' ^ M • (YY * AA)) * Φe) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (u ^ N * (E' * u * t') ^ M) • ((E' ^ N • ΦY) * Φe) := by rw [hφ1]
      _ = (E' * u) ^ N • ((E' * u * t') ^ M • (ΦY * Φe)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' * u) ^ N • ((E' * t) ^ M • (PP * ΦGY)) := by rw [he1]
      _ = (E' * t) ^ M • (PP * ((E' * u) ^ N • ΦGY)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' * t) ^ M • (PP * ((E' * u) ^ M • (GY * GA))) := by rw [hφ2]
      _ = (E' ^ M * (E' * u) ^ M) • ((t ^ M • (PP * GY)) * GA) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' ^ M * (E' * u) ^ M) • ((t' ^ M • (YY * e)) * GA) := by rw [he]
      _ = (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (e * GA)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
  have hu' : u ≠ 0 := fun h => by rw [h, mul_zero] at hv; exact zero_ne_one hv
  have hc : E' ^ (2 * M) * u ^ M * t' ^ M ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hE) (pow_ne_zero _ hu')) (pow_ne_zero _ ht')
  have hX := cancel_left YY _ _ _ hc hdet key
  calc E' ^ (2 * N) • e = (v ^ (2 * N) * (E' * u) ^ (2 * N)) • e := by
        congr 1
        rw [show v ^ (2 * N) * (E' * u) ^ (2 * N) = E' ^ (2 * N) * (v * u) ^ (2 * N) by ring, hv, one_pow, mul_one]
    _ = v ^ (2 * N) • (e * ((E' * u) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)))) := by
        rw [Matrix.mul_smul, Matrix.mul_one, smul_smul]
    _ = v ^ (2 * N) • ((e * GA) * GA') := by rw [← hA2, Matrix.mul_assoc]
    _ = v ^ (2 * N) • ((u ^ N • (AA * Φe)) * GA') := by rw [hX]
    _ = (v ^ N • AA) * Φe * GA' := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
        congr 1
        rw [show v ^ (2 * N) * u ^ N = v ^ N * (v * u) ^ N by ring, hv, one_pow, mul_one]

end GlobalTheory.BSP.CocycleFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscExistsConstAddXMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSer

variable (l : ℕ) {W : Type} [CommRing W] (ρ : ℝ≥0)

def shiftX (s : W⟦X⟧) : W⟦X⟧ := PowerSeries.mk fun n => coeff (n + 1) s

theorem coeff_shiftX (s : W⟦X⟧) (n : ℕ) : coeff n (shiftX s) = coeff (n + 1) s := coeff_mk _ _

theorem X_mul_shiftX (s : W⟦X⟧) : X * shiftX s = s - C (coeff 0 s) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_shiftX, map_sub, coeff_C]; simp

theorem eq_zero_of_X_mul_eq_zero {t : W⟦X⟧} (h : X * t = 0) : t = 0 := by
  ext n
  have := congrArg (coeff (n + 1)) h
  rwa [coeff_succ_X_mul, map_zero] at this

theorem exists_rep (y : PreDisc l (X : W⟦X⟧) ρ) : ∃ (c : ℕ) (s : W⟦X⟧),
    y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  exact ⟨c, s, by rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]⟩

theorem aPre_rep (n c : ℕ) (s : W⟦X⟧) :
    aPre l ρ n (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) s *
      IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
      algebraMap W (PreDisc l (0 : W) 1) (coeff n s) *
        IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c := by
  rw [aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]

theorem eq_zero_of_X_mul (z : PreDisc l (X : W⟦X⟧) ρ)
    (h : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * z = 0) : z = 0 := by
  obtain ⟨c, t, rfl⟩ := exists_rep l ρ z
  have hu : IsUnit (IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧)) :=
    IsUnit.of_mul_eq_one_right (algebraMap _ _ (l : W⟦X⟧)) (IsLocalization.Away.mul_invSelf _)
  rw [← mul_assoc, ← map_mul] at h
  have h2 : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X * t) = 0 := (hu.pow c).mul_left_eq_zero.1 h
  obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (l : W⟦X⟧)) _ _).1 h2
  obtain ⟨k, rfl⟩ := hm
  have h3 : (l : W⟦X⟧) ^ k * t = 0 :=
    eq_zero_of_X_mul_eq_zero (by rw [mul_left_comm]; exact hm')
  have h4 : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) t = 0 := by
    have h5 := congrArg (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ)) h3
    rw [map_mul, map_zero] at h5
    rw [map_pow] at h5
    exact ((IsLocalization.Away.algebraMap_isUnit (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧)).pow k).mul_right_eq_zero.1 h5
  rw [h4, zero_mul]

abbrev c0 (y : PreDisc l (X : W⟦X⟧) ρ) : PreDisc l (X : W⟦X⟧) ρ :=
  preMap l (0 : W) 1 (X : W⟦X⟧) ρ C (aPre l ρ 0 y)

theorem X_mul_rep (c : ℕ) (s : W⟦X⟧) :
    algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * (algebraMap _ _ (shiftX s) *
      IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
    algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c -
      c0 l ρ (algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) := by
  rw [c0, aPre_rep, map_mul, preMap_alg, map_pow, preMap_inv, ← mul_assoc, ← map_mul, X_mul_shiftX, map_sub,
    sub_mul]

def dFun (y : PreDisc l (X : W⟦X⟧) ρ) : PreDisc l (X : W⟦X⟧) ρ :=
  algebraMap _ _ (shiftX (exists_rep l ρ y).choose_spec.choose) *
    IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ (exists_rep l ρ y).choose

theorem X_mul_dFun (y : PreDisc l (X : W⟦X⟧) ρ) :
    algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * dFun l ρ y = y - c0 l ρ y := by
  have hy := (exists_rep l ρ y).choose_spec.choose_spec
  rw [dFun, X_mul_rep, ← hy]

theorem dFun_eq (y z : PreDisc l (X : W⟦X⟧) ρ)
    (h : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * z = y - c0 l ρ y) : dFun l ρ y = z :=
  sub_eq_zero.1 (eq_zero_of_X_mul l ρ _ (by rw [mul_sub, X_mul_dFun, h, sub_self]))

theorem dFun_rep (c : ℕ) (s : W⟦X⟧) :
    dFun l ρ (algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
      algebraMap _ _ (shiftX s) * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c :=
  dFun_eq l ρ _ _ (X_mul_rep l ρ c s)

def DPre : PreDisc l (X : W⟦X⟧) ρ →+ PreDisc l (X : W⟦X⟧) ρ :=
  AddMonoidHom.mk' (dFun l ρ) fun y z => dFun_eq l ρ _ _ (by
    rw [mul_add, X_mul_dFun, X_mul_dFun, c0, c0, c0, map_add (f := _), map_add (f := _)]; abel)

theorem DPre_apply (y : PreDisc l (X : W⟦X⟧) ρ) : DPre l ρ y = dFun l ρ y := rfl

theorem aPre_DPre (n : ℕ) (y : PreDisc l (X : W⟦X⟧) ρ) : aPre l ρ n (DPre l ρ y) = aPre l ρ (n + 1) y := by
  obtain ⟨c, s, rfl⟩ := exists_rep l ρ y
  rw [DPre_apply, dFun_rep, aPre_rep, aPre_rep, coeff_shiftX]

theorem norm_DPre_le [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (y : PreDisc l (X : W⟦X⟧) ρ) :
    ‖DPre l ρ y‖ ≤ (ρ : ℝ)⁻¹ * ‖y‖ := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hρ : (0 : ℝ) < ρ := by exact_mod_cast hρ0
  refine norm_le_of_aPre l ρ hρ0 hρ1 _ _ (by positivity) fun n => ?_
  rw [aPre_DPre, inv_mul_eq_div, le_div_iff₀ hρ, mul_assoc, ← pow_succ]
  exact norm_aPre_le l ρ hl hρ1.le y (n + 1)

theorem continuous_DPre [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Continuous (DPre l ρ (W := W)) :=
  AddMonoidHomClass.continuous_of_bound _ _ (norm_DPre_le l ρ hρ0 hρ1)

theorem exists_const_add_X_mul [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (κ : Disc l (0 : W) 1 →+* Disc l (X : W⟦X⟧) ρ) (hκ : IsDiscMap (l := _) (u := _) (ρ := _) (C : W →+* W⟦X⟧) κ)
    (x : Disc l (X : W⟦X⟧) ρ) :
    ∃ (c : Disc l (0 : W) 1) (x₁ : Disc l (X : W⟦X⟧) ρ), x = κ c + toDisc l (X : W⟦X⟧) ρ X * x₁ := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let A0 := (aPre l ρ 0 (W := W)).completion (continuous_aPre l ρ hl hρ0 hρ1.le 0)
  let D := (DPre l ρ (W := W)).completion (continuous_DPre l ρ hρ0 hρ1)
  have hA : ∀ y, A0 (ofPre l (X : W⟦X⟧) ρ y) = ofPre l (0 : W) 1 (aPre l ρ 0 y) := fun y =>
    AddMonoidHom.completion_coe _ _ y
  have hD : ∀ y, D (ofPre l (X : W⟦X⟧) ρ y) = ofPre l (X : W⟦X⟧) ρ (DPre l ρ y) := fun y =>
    AddMonoidHom.completion_coe _ _ y
  have hκc : Continuous κ :=
    AddMonoidHomClass.continuous_of_bound _ 1 fun y => (hκ.norm_le y).trans (one_mul _).ge
  have e : κ.comp (ofPre l (0 : W) 1) = (ofPre l (X : W⟦X⟧) ρ).comp (preMap l (0 : W) 1 (X : W⟦X⟧) ρ C) :=
    IsLocalization.ringHom_ext (Submonoid.powers (l : W)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply]; rw [preMap_alg]; exact hκ.ext a)
  refine ⟨A0 x, D x, ?_⟩
  refine (denseRange_ofPre l (X : W⟦X⟧) ρ).induction_on x
    (isClosed_eq continuous_id ((hκc.comp (AddMonoidHom.continuous_completion _ _)).add
      (continuous_const.mul (AddMonoidHom.continuous_completion _ _)))) fun y => ?_
  rw [hA, hD, show κ (ofPre l (0 : W) 1 (aPre l ρ 0 y)) = _ from RingHom.congr_fun e _, RingHom.comp_apply,
    show toDisc l (X : W⟦X⟧) ρ X = ofPre l (X : W⟦X⟧) ρ (algebraMap _ _ X) from rfl, ← map_mul, ← map_add,
    DPre_apply, X_mul_dFun]
  congr 1
  abel

end GlobalTheory.BSP.DiscSer

namespace GlobalTheory.BSP

theorem exists_const_add_X_mul_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∀ (κ : Disc l (0 : Wq l bk.a) 1 →+* bk.DS ρ), IsDiscMap (l := _) (u := _) (ρ := _) (C : Wq l bk.a →+* bk.S) κ →
    ∀ x : bk.DS ρ, ∃ (c : Disc l (0 : Wq l bk.a) 1) (x₁ : bk.DS ρ), x = κ c + toDisc l (X : bk.S) ρ X * x₁ :=
  fun l _ _ _ ρ hρ0 hρ1 κ hκ x => DiscSer.exists_const_add_X_mul l ρ hρ0 hρ1 κ hκ x

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPartCOfPartAPartBFiniteLevel
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKFinLevel

theorem bkC_of_bkA_bkB : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, bkACore (P.PD K) → bkBCore (P.PD K) → Formalism.MainNotions.LocalSituation.bkC (P.PD K) := by
  intro hT _ l _ P _ _ K hA hB LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hDR hd ϖ hϖ r hI hI'
  show (∀ c ∈ quotientCocycles LA _ hI, (c ∈ HfQ (P.PD K) LA _ hI ↔ ∀ c' ∈ HfQ (P.PD K) LA' _ hI',
      CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c'))) ∧
    (∀ c' ∈ quotientCocycles LA' _ hI', (c' ∈ HfQ (P.PD K) LA' _ hI' ↔ ∀ c ∈ HfQ (P.PD K) LA _ hI,
      CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c')))
  have orth := GlobalTheory.T.blochKato_reductions_orthogonal_mod_pow l P K hA LL O hO L1 hL1 A A' LA LA' m hDR hd ϖ r hI hI'

  have hfz : ∀ s ∈ HfQ (P.PD K) LA _ hI, s ∈ quotientCocycles LA _ hI := by
    intro s hs
    obtain ⟨a, -, has⟩ := (GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction l P K LL O hO A LA ϖ r hI s).1 hs
    rw [has]
    exact GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles l P K LL O hO A LA ϖ hϖ r hI a

  have clause2 : ∀ c' ∈ quotientCocycles LA' _ hI', (∀ c ∈ HfQ (P.PD K) LA _ hI,
      CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c')) → c' ∈ HfQ (P.PD K) LA' _ hI' := by
    intro c' hc' horth
    apply GlobalTheory.T.blochKato_quotient_of_divisible_image_mem l P K LL O hO A' LA' ϖ hϖ r hI' c'
    have hZ := GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles l P K LL O hO A' LA' ϖ r hI' c' hc'
    refine ((hB LL O hO L1 hL1 A A' LA LA' m hDR hd).1 _ hZ).2 ?_
    intro d hdf
    have hdT : d ∈ latticeCocycles LA := hdf.1
    rw [GlobalTheory.T.cup_divisible_image_coboundary_iff_finite_level l P K LL O hO L1 hL1 A A' LA LA' m hd ϖ r ⟨d, hdT⟩ c']
    exact horth _ ((GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction l P K LL O hO A LA ϖ r hI _).2 ⟨⟨d, hdT⟩, hdf.2, rfl⟩)
  refine ⟨fun c hc => ⟨fun h c' hc' => orth c h c' hc', fun h => ?_⟩,
    fun c' hc' => ⟨fun h c hc => orth c hc c' h, clause2 c' hc'⟩⟩

  let S : Submodule O (↥(GK K) → A.V ⧸ LA.T) :=
    (HfQ (P.PD K) LA _ hI).map ((GlobalTheory.BKFinLevel.ioL LA ϖ r).compLeft ↥(GK K)) ⊔ BD LA
  have hS1 : BD LA ≤ S := le_sup_right
  have hS2 : S ≤ divisibleCocycles LA := by
    refine sup_le ?_ (GlobalTheory.T.lattice_divisible_coboundaries_le_locConst_cocycles' l P K LL O hO A LA)
    rintro _ ⟨s, hs, rfl⟩
    exact GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles l P K LL O hO A LA ϖ r hI s (hfz s hs)
  have hflip : IsDualLat1 (P.PD K) LA' LA m.flip := by
    obtain ⟨⟨hDom, hDVR, hFr⟩, -, -, htr, -⟩ := id hO
    exact Formalism.MainNotions.BlochKatoDuality.Br.isDualLat1_flip (P.PD K) hd
  have hC := GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles l P K LL O hO A LA ϖ r hI c hc
  have key := GlobalTheory.T.lattice_dual_cyclotomic hT l P K LL O hO L1 hL1 A' A LA' LA m.flip hflip S hS1 hS2 _ hC (by
    intro d hdZ hdS
    rw [← GlobalTheory.T.finite_level_cup_swap_coboundary_iff l P K LL O hO L1 hL1 A A' LA LA' m hd ϖ r hI c hc ⟨d, hdZ⟩]
    apply h
    apply clause2 _ (GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles l P K LL O hO A' LA' ϖ hϖ r hI' ⟨d, hdZ⟩)
    intro s hs
    rw [GlobalTheory.T.finite_level_cup_swap_coboundary_iff l P K LL O hO L1 hL1 A A' LA LA' m hd ϖ r hI s (hfz s hs) ⟨d, hdZ⟩]
    exact hdS _ (Submodule.mem_sup_left ⟨s, hs, rfl⟩))
  obtain ⟨y, ⟨a, ha, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1 key
  have hdiff : (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r ((c - a) g)) ∈ HfD (P.PD K) LA := by
    have : (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r ((c - a) g)) = z := by
      funext g
      have := congrFun hyz g
      simp only [Pi.sub_apply, map_sub, LinearMap.compLeft_apply, Function.comp_apply,
        Pi.add_apply] at this ⊢
      rw [← this]; abel
    rw [this]
    exact Submodule.mem_sup_right hz
  have := GlobalTheory.T.blochKato_quotient_of_divisible_image_mem l P K LL O hO A LA ϖ hϖ r hI _ hdiff
  simpa using (HfQ (P.PD K) LA _ hI).add_mem this ha

end GlobalTheory.BKFinLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPoles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem pre_bounded_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Pre bk N d ρ), ∃ Y Y' : Matrix (Fin d) (Fin d) (Ainf l), Y.map (inclW l) = inclW l τ ^ N • F.T ∧ Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ K bk τ hτ N d ρ F
  classical
  obtain ⟨hU, -⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have hφt : frobW l (inclW l τ) = bk.evW bk.E * inclW l τ := by
    rw [frobW_inclW, hτ.1, map_mul]; rfl
  have he : IsUnit (bk.evW bk.E) := by
    have h := hU.map (frobW l)
    rw [hφt] at h
    exact isUnit_of_mul_isUnit_left h
  have hdet : IsUnit F.T.det := (Matrix.isUnit_iff_isUnit_det _).1 F.unit
  have hTTi : F.T * F.T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hTiT : F.T⁻¹ * F.T = 1 := Matrix.nonsing_inv_mul _ hdet
  have hmapmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l) :=
    fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)
  have h1 : F.T⁻¹.map (frobW l) * F.T.map (frobW l) = 1 := by
    rw [← hmapmul, hTiT]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hAA : F.A.map bk.evW * F.A'.map bk.evW = bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul, F.A_mul]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp

  have hφTi : bk.evW bk.E ^ N • F.T⁻¹.map (frobW l) = F.A'.map bk.evW * F.T⁻¹ := by
    have k1 : (bk.evW bk.E ^ N • F.T.map (frobW l)) * F.A'.map bk.evW * F.T⁻¹ =
        bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
      rw [F.φ, Matrix.mul_assoc F.T, hAA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hTTi]
    have k2 := congrArg (fun M => F.T⁻¹.map (frobW l) * M) k1
    simp only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_one] at k2
    have k3 : bk.evW bk.E ^ N • (bk.evW bk.E ^ N • F.T⁻¹.map (frobW l)) =
        bk.evW bk.E ^ N • (F.A'.map bk.evW * F.T⁻¹) := by
      rw [smul_smul, ← pow_add, show N + N = 2 * N by ring, ← k2]
    exact (he.pow N).smul_left_cancel.1 k3
  have hY : ∀ i j, ∃ a : Ainf l, inclW l τ ^ N * F.T i j = inclW l a := by
    intro i
    refine GlobalTheory.HeightInt.frob_row_integral l (Fin d) (fun j => inclW l τ ^ N * F.T i j)
      (fun k j => bk.ev (F.A k j)) ?_
    intro j
    have e1 := congrFun (congrFun F.φ i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e1
    rw [map_mul, map_pow, hφt, mul_pow, mul_comm (bk.evW bk.E ^ N), mul_assoc, e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc]; rfl
  have hY' : ∀ i j, ∃ a : Ainf l, inclW l τ ^ N * F.T⁻¹ i j = inclW l a := by
    intro i j
    refine GlobalTheory.HeightInt.frob_row_integral l (Fin d) (fun k => inclW l τ ^ N * F.T⁻¹ k j)
      (fun k i => bk.ev (F.A' i k)) ?_ i
    intro i
    have e1 := congrFun (congrFun hφTi i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e1
    rw [map_mul, map_pow, hφt, mul_pow, mul_comm (bk.evW bk.E ^ N), mul_assoc, e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (bk.evW (F.A' i k)), mul_assoc]; rfl
  choose Y hYe using hY
  choose Y' hY'e using hY'
  refine ⟨Matrix.of Y, Matrix.of Y', ?_, ?_⟩
  · ext i j
    simp [Matrix.smul_apply, hYe]
  · refine Matrix.ext fun i j => ?_
    apply inclW_injective
    have e2 := congrFun (congrFun hTTi i) j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at e2 ⊢
    simp only [← hYe, ← hY'e]
    calc ∑ k, inclW l τ ^ N * F.T i k * (inclW l τ ^ N * F.T⁻¹ k j)
        = inclW l τ ^ (2 * N) * ∑ k, F.T i k * F.T⁻¹ k j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
      _ = _ := by rw [e2]; split_ifs <;> simp [map_pow]

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRootSubOneLengthLeTameValueStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductorRoot_sub_one_length_le_tameValue : ∀ (D : D7) (C : NChoice D), NChTie D C → ∀ i : D.nd.Loc, ∀ v ∈ D.nd.Q i, ((lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) ≤ BlochKatoReduction.Gen.tameVal (D.ntw.l (C.twI (D.nd.w i))) (KillingConditions.psiW C (D.nd.w i)) (D.nd.plOm.1 v) := by
  first | exact @GlobalTheory.CondTieChoice.conductor_le_tameVal | exact GlobalTheory.CondTieChoice.conductor_le_tameVal | (intros; apply GlobalTheory.CondTieChoice.conductor_le_tameVal <;> assumption)
end

