module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0728
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0714
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotValuationNatCastLtOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionSmoothRightInvariant
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.InvParts

theorem L_bridge : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := GlobalTheory.T.isUnit_block_det_of_conj_lower

theorem L_top : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := GlobalTheory.T.exists_nhds_one_conjLowerUnipotent_schurBlocks_small

theorem L_row : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := GlobalTheory.T.lastRow_finite_mem_compact_on_support

theorem L_col : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := GlobalTheory.T.firstColumn_inv_finite_mem_compact_on_support

theorem L_supSc : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := GlobalTheory.T.schurComplement_mem_adelicGLSupportedAtFinitePlaces

end GlobalTheory.SchurExt.InvParts

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem psi_sFin_of_mem {z : Af E} (hz : z ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : psi (sFin E z) = 1 := by
  have h := GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles (K := E) (y := sFin E z)
    (GroundTheory.Global.mem_invDifferentAdeles.mpr (GroundTheory.Global.mem_finiteInvDifferent_of_mem_integralFiniteAdeles hz))
  have h0 : (sFin E z).1 = 0 := rfl
  rw [psi, h, h0]
  simp

theorem psi_add (a b : Ad E) : psi (a + b) = psi a * psi b := by
  simp only [psi, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem supS_mul {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {x y : GA E a}
    (hx : x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (hy : y ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) : x * y ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  intro w hw
  rw [map_mul, hx w hw, hy w hw, mul_one]

theorem supS_inv {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {x : GA E a}
    (hx : x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) : x⁻¹ ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  intro w hw
  rw [map_inv, hx w hw, inv_one]

theorem finGL_mem_supS {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {k : GL (Fin a) (Af E)}
    (hk : finGL E a k ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∉ S) :
    Matrix.GeneralLinearGroup.map (pLoc E w) k = 1 := by
  have h := hk w hw
  rw [← h]
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pLoc E w (k i j) = pLoc E w (pFin E ((finGL E a k : GA E a) i j))
  congr 1
  exact (congrArg (fun y : GL (Fin a) (Af E) => (y : Matrix (Fin a) (Fin a) (Af E)) i j) (pFin_finGL (E := E) k)).symm

end GlobalTheory.SchurExt


open GlobalTheory.SchurExt.InvParts in
theorem GlobalTheory.SchurExt.schurF_mul_finGL_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ U : Subgroup (GL (Fin (r + 1)) (Af E)), IsOpen (U : Set (GL (Fin (r + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b₁ (g * finGL E (r + 1) u) = b₁ g) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
  intro E _ _ _ m r S β b₁ χ ⟨Uβ, hUβo, hUβ⟩ hβC ⟨Ub, hUbo, hUb⟩ hbC
  obtain ⟨Krow, hKr, hKrow⟩ := L_row E m S β hβC
  obtain ⟨Kcol, hKc, hKcol⟩ := L_col E r b₁ hbC
  obtain ⟨W₀, hW₀, hW⟩ := L_top E m r S Uβ Ub hUβo hUbo Krow Kcol hKr hKc
  have fwd : ∀ k ∈ W₀, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S →
      ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ x ≠ 0 →
        schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
    intro k hk hkS x hx hF
    classical
    have hD : IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
      by_contra hD
      exact hF (by rw [schurF, ite_eq_right hD])
    rw [schurF, ite_eq_left hD] at hF
    have hβ0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hF))
    have hβ0' := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hF))
    have hb0 := right_ne_zero_of_mul (left_ne_zero_of_mul hF)
    have hχ0 := right_ne_zero_of_mul hF
    have hYint : ∀ i j, pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
      by_contra hY
      exact hχ0 (by rw [chiF, ite_eq_right hY, mul_zero])
    obtain ⟨hdu, hdU, hsU, hyI, hX⟩ := hW k hk (finGL_mem_supS hkS)
      ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (fun i j => hYint i j)
    obtain ⟨hSc, hD', eD, eSc, eYi, eYf, eX⟩ := L_bridge E m r x k hD hdu
    have hrow := hKrow _ (L_supSc E m r S x hx hD) hβ0'
    have hcol := hKcol _ hb0
    rw [coe_mkGL hSc] at hrow
    rw [Matrix.coe_units_inv, coe_mkGL hD] at hcol
    have hz := hX _ hrow _ hcol
    have hchi : chiF χ (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
        Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) =
        chiF χ (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) := by
      have h1 : (fun i j => pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
          Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) =
          fun i j => pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) :=
        funext fun i => funext fun j => eYi i j
      have h2 : ∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
          Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E :=
        fun i j => by rw [eYf]; exact add_mem (hYint i j) (hyI i j)
      rw [chiF, chiF, h1, ite_eq_left h2, ite_eq_left hYint]
    rw [schurF, ite_eq_left hD', eD, eSc, hUb _ hdU, hUβ _ hsU, hchi, eX, psi_add, psi_sFin_of_mem hz, mul_one, schurF, ite_eq_left hD]
  open scoped Pointwise in
  exact by
    refine ⟨W₀ ∩ W₀⁻¹, Filter.inter_mem hW₀ (inv_mem_nhds_one _ hW₀), ?_⟩
    intro k hk hkS x hx
    by_cases h0 : schurF β b₁ χ x = 0
    · by_cases h1 : schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = 0
      · rw [h0, h1]
      · have h2 := fwd k⁻¹ hk.2 (by rw [map_inv]; exact supS_inv hkS) _ (supS_mul hx hkS) h1
        rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at h2
        exact absurd (h2.symm.trans h0) h1
    · exact fwd k hk.1 hkS x hx h0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceComponentUnitaryAdelicDetermined
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCompat

theorem compAt_eq_zero_of_proj_eq_zero {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (z : AL L) (hp : s.proj z = 0) (hq : s.proj (conjAL L z) = 0) : compAt L s.v z = 0 := by
  obtain ⟨e, hne⟩ : ∃ e : L, e ≠ IsCMField.complexConj L e := by
    by_contra hcon
    push Not at hcon
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext fun x => (hcon x).symm)
  have hli : LinearIndependent (maximalRealSubfield L) ![(1 : L), e] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    have h' := congrArg (IsCMField.complexConj L) h
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'
    have hd : algebraMap (maximalRealSubfield L) L t * (e - IsCMField.complexConj L e) = 0 := by
      linear_combination h - h'
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hd with h0 | h0
      · simpa using h0
      · exact absurd (sub_eq_zero.1 h0) hne
    subst ht
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank (maximalRealSubfield L) L := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L]; simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = e := by simp [b]
  obtain ⟨A, B, hAB⟩ := GlobalTheory.tensor_exists_decomp b z
  rw [hb0, hb1] at hAB
  have h1 : s.proj z = A s.v + s.i e * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]
    rfl
  have h2 : s.proj (ReciprocityTheory.Aut.conjAL L z) =
      A s.v + s.i (IsCMField.complexConj L e) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  have hu : s.i e - s.i (IsCMField.complexConj L e) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hne (s.i.toRingHom.injective h)
  have hBv : B s.v = 0 := by
    have hm : (s.i e - s.i (IsCMField.complexConj L e)) * B s.v =
        s.proj z - s.proj (ReciprocityTheory.Aut.conjAL L z) := by
      rw [h1, h2]; ring
    rw [hp, hq, sub_zero] at hm
    exact (mul_eq_zero.1 hm).resolve_left hu
  have hAv : A s.v = 0 := by
    rw [hp, hBv, mul_zero, add_zero] at h1
    exact h1.symm
  rw [hAB]
  have hA' : evalAt L s.v A = 0 := by rw [← hAv]; rfl
  have hB' : evalAt L s.v B = 0 := by rw [← hBv]; rfl
  simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul, hA', hB']

theorem compAt_map_eq_of_loc_eq : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    (x y : GAf L n), s.loc n x = s.loc n y →
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) =
        (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) := by
  intro L _ _ _ n s x y h
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply]
  rw [← sub_eq_zero, ← map_sub]
  apply compAt_eq_zero_of_proj_eq_zero s
  · rw [map_sub, GlobalTheory.SplitLocEq.proj_entry, GlobalTheory.SplitLocEq.proj_entry, h, sub_self]
  · rw [map_sub, map_sub, GlobalTheory.SplitLocEq.conj_entry, GlobalTheory.SplitLocEq.conj_entry, GlobalTheory.SplitLocEq.proj_entry,
      GlobalTheory.SplitLocEq.proj_entry, map_inv, map_inv, h, sub_self]

end GlobalTheory.SplitCompat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumAdelicReadingEqOfTwoBaseChangeDecompsOnCover
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverBCRead

theorem evR_sum_eq {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ)
    (hσ : C.σ₂.comp C.inc = σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {m m' : ℕ} (x : Fin m → C.c'.F)
    (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j)
    (hf : ∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n)
    (hBC : IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs)
    (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) :
    (∑ b, C.σ₂ (C.d.eF (x b)) * toC (evR (T.Q.Xo j) T.Q.c (f b) y)) =
      ∑ i, C.σ₂ (C.d.eF (as i)) * toC (evR (T.Q.Xo j) T.Q.c (fs i) y) := by
  letI : Algebra C.c'.F (CAt σ) := (C.σ₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)).toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle (CAt σ) := by
    intro c0
    show C.σ₂ (C.d.eF (incF T.Q.c C.c' C.hle c0)) = σ c0
    exact RingHom.congr_fun hσ c0
  have h1 := hBC (CAt σ) hA (FrPt.ext C.hle hA y)
  rw [Formalism.L2.Pj.evR_sum_smul] at h1
  simp only [GlobalTheory.FieldBCModel.evR_rulBC C.hle (hf _).1 hA, FrPt.res_ext] at h1
  exact h1

theorem phiJ_sum_eq_of_isBC : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.σ₂.comp C.inc = σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m m' : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs → ∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b) = ∑ i, C.σ₂ (C.d.eF (as i)) • T.phiJ j σ a (fs i) := by
  intro D T j σ C hσ a n m m' x f as fs hf hBC
  have key : (∑ b, C.σ₂ (C.d.eF (x b)) • rdU (T.U j σ) (f b) : FDSec (T.U j σ).X) =
      ∑ i, C.σ₂ (C.d.eF (as i)) • rdU (T.U j σ) (fs i) := by
    funext k z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : z ∈ ((T.U j σ).X k).dom
    · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]
      exact evR_sum_eq T j σ C hσ a n x f as fs hf hBC ((T.U j σ).un k ⟨z, h⟩)
    · simp [rdU, dif_neg h]
  let L : FDSec (T.U j σ).X →ₗ[ℂ] (GA D (T.V j σ) → ℂ) := (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ))
  have e : ∀ g : T.R j, T.phiJ j σ a g = L (rdU (T.U j σ) g) := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, ← map_smul, ← map_sum, key]

end GlobalTheory.CoverBCRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FieldTransport

section General
variable {G H : Type} [Group G] [Group H]

def compEquiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {τ : Representation ℂ H W} (φ : ρ.Equiv τ) (f : G →* H) :
    Representation.Equiv (ρ.comp f : Representation ℂ G V) (τ.comp f : Representation ℂ G W) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    have := congrArg (fun L => L v) (φ.toIntertwiningMap.isIntertwining' (f g))
    simpa using this

def compCompEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : H →* G)
    (g : G →* H) (h : ∀ x, f (g x) = x) : Representation.Equiv ((ρ.comp f).comp g : Representation ℂ G V) ρ :=
  .mk (LinearEquiv.refl ℂ V) fun x => LinearMap.ext fun v => by simp [h]

variable [TopologicalSpace G] [TopologicalSpace H]

def pullRep (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f) (σ : IrrRep H) : IrrRep G :=
  ⟨σ.V, σ.ρ.comp f, fun v => (σ.smooth v).preimage hf,
    GlobalTheory.JacFactor.isIrreducible_comp_surj σ.ρ f hs σ.irr⟩

end General

section GLmap
variable {R S : Type} [CommRing R] [CommRing S]

abbrev mapGL (e : R ≃+* S) (n : ℕ) : GL (Fin n) R →* GL (Fin n) S := GeneralLinearGroup.map e.toRingHom

theorem mapGL_symm_mapGL (e : R ≃+* S) (n : ℕ) (g : GL (Fin n) R) : mapGL e.symm n (mapGL e n g) = g := by
  ext a b; simp [mapGL]

theorem mapGL_mapGL_symm (e : R ≃+* S) (n : ℕ) (g : GL (Fin n) S) : mapGL e n (mapGL e.symm n g) = g := by
  ext a b; simp [mapGL]

theorem mapGL_surjective (e : R ≃+* S) (n : ℕ) : Function.Surjective (mapGL e n) :=
  fun g => ⟨_, mapGL_mapGL_symm e n g⟩

theorem continuous_mapGL [TopologicalSpace R] [TopologicalSpace S] (e : R ≃+* S) (he : Continuous e) (n : ℕ) :
    Continuous (mapGL e n) :=
  Units.continuous_map (continuous_id.matrix_map he)

end GLmap
end GlobalTheory.FieldTransport

namespace GlobalTheory.FieldTransport

section Fields
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

def transportFun (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL (k := k)) : IrrGL (k := k') :=
  ⟨x.1, (pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1) (mapGL_surjective i.symm x.1) x.2.rep).cl⟩

theorem transportFun_left (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) (x : IrrGL (k := k)) :
    transportFun i.symm (by simpa using hi) (transportFun i hi' x) = x := by
  refine congrArg (Sigma.mk x.1) ((IrrRep.cl_eq_iff.2 ?_).trans x.2.cl_rep)
  obtain ⟨ψ⟩ := IrrRep.nonempty_equiv_rep
    (pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1) (mapGL_surjective i.symm x.1) x.2.rep)
  exact ⟨(compEquiv ψ (mapGL i.symm.symm x.1)).trans
    (compCompEquiv x.2.rep.ρ (mapGL i.symm x.1) (mapGL i.symm.symm x.1) fun g => mapGL_symm_mapGL i x.1 g)⟩

theorem repRel_iff (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL (k := k)) (x' : IrrGL (k := k')) :
    RepRel i x x' ↔ transportFun i hi' x = x' := by
  constructor
  · rintro ⟨n, π, π', e, rfl, rfl, he⟩
    refine congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 ?_)
    obtain ⟨ψ⟩ := IrrRep.nonempty_equiv_rep π
    refine ⟨(compEquiv ψ (mapGL i.symm n)).trans (.mk e fun g => LinearMap.ext fun v => ?_)⟩
    have := he (mapGL i.symm n g) v
    rw [show GeneralLinearGroup.map i.toRingHom (mapGL i.symm n g) = g from mapGL_mapGL_symm i n g] at this
    simpa using this
  · rintro rfl
    refine ⟨x.1, x.2.rep, pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1)
      (mapGL_surjective i.symm x.1) x.2.rep, LinearEquiv.refl ℂ _,
      congrArg (Sigma.mk x.1) x.2.cl_rep.symm, rfl, fun g v => ?_⟩
    show x.2.rep.ρ g v = x.2.rep.ρ (mapGL i.symm x.1 (mapGL i x.1 g)) v
    rw [mapGL_symm_mapGL]

theorem exists_transport (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) :
    ∃ T : IrrGL (k := k) ≃ IrrGL (k := k'), (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  have hi2 : Continuous i.symm.symm := by simpa using hi
  refine ⟨⟨transportFun i hi', transportFun i.symm hi2, fun x => transportFun_left i hi hi' x, fun y => ?_⟩,
    repRel_iff i hi', fun x => rfl⟩
  have := transportFun_left i.symm hi' hi2 y
  simpa using this

end Fields
end GlobalTheory.FieldTransport


open GlobalTheory.FieldTransport in
theorem GlobalTheory.transport_irrGL_bijective : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∃ T : IrrGL (k := k) ≃ IrrGL (k := k'), (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  exact exists_transport i hi (_root_.GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation k k' i hi).1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistAllPowersOfGaloisCohomologyClassField
section
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.Published

namespace GlobalTheory.TwExportTop

theorem twistAllPowers_of_galoisCohomology_classField :
    Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), LocalSituation.Conclusion5 D → BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D) → BlochKatoReduction.adm2 D → BlochKatoReduction.adm8 D → AllGood D.nexp → D.nexp.sig_all → BlochKatoReduction.adm9 D N0 → BlochKatoReduction.adm10 D → GlobalTheory.UnivChar.IsUnivChar D.nexp → OffRange D → ThURel D.nexp → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → IntegralHeckeForms.admT4 D.nexp E → TypeKept E → UnivSup D E → SupG D → SupFull D → SupHk D → CommG D → HkComm D → HkSS D → ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i := by
  intro hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW hRC D E N0 h5 h1 h2 h8 hGood hSig h9 h10 hUniv hOff hRel
    hL3 hT4 hT hU hG hFull hHk hComm hHC hSS
  exact GlobalTheory.TwExportSup.twistTheorem_allPowers_of_selmer_supLattice D E N0
    (_root_.GlobalTheory.SelFun.oneMatrix_of_galoisCohomology hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 D D.nd D.ntw (BlochKatoReduction.bk0 D))
    (_root_.GlobalTheory.ResSel.residual_bound_of_parts hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW D D.nd D.ntw (BlochKatoReduction.bk0 D))
    (_root_.GlobalTheory.StepTwo.Dyadic.bound_mod_two_of_hypothesis hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 D D.nd D.ntw (BlochKatoReduction.bk0 D))
    ⟨h1, h2, (GlobalTheory.BlochKato₂.duality_dim_of_localTheorem D h5).1, h4, h9, h10⟩
    (GlobalTheory.UnivChar.delUTie_of_isUnivChar D.nexp (GlobalTheory.AdmChars.exists_admissible_family D.ntw hRC) hUniv)
    hRel hHC hOff hGood h8 hG hFull hHk hU hT hComm hT4 hL3 hSig hSS

end GlobalTheory.TwExportTop
end

