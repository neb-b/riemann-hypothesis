module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0850
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0861
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0860
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0849

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCell
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEul

theorem detPow_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n 0 g = 1 := by
  intro E _ _ _ n g
  simp [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, GlobalTheory.Mem.Chr.CharModel.absHom_val]

theorem pInf_lastRow_tl_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ))
    (g : GA E (m + 1)),
    (fun i => pInf E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l * g) i)) = fun i => pInf E (GlobalTheory.ZEul.lastRow g i) := by
  intro E _ _ _ m ϖ l g
  funext i
  have h := congrArg (fun M : GL (Fin (m + 1)) (Cinf E) => (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) i)
    (show Matrix.GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl (m + 1) ϖ l * g) =
      Matrix.GeneralLinearGroup.map (pInf E) g by rw [map_mul, GlobalTheory.CellDec.tl, pInf_finGL, one_mul])
  exact h

theorem uInt_cell_eval : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (b : GA E (m + 1) → ℂ) (α α' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ) (φ φ' : GA E (m + 1) → ℂ)
      (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ' g) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ' (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l w)) →
    ∀ x : ℝ, ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
      GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧ GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧
      ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x v) *
            GlobalTheory.ZEul.uInt φ φ Φ N 0 g * (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) := by
  intro E _ _ _ m S hψ ϖ hϖ b α α' φ φ' N J Φ hJ hint hS hloc hΦ hNφ hNφ' hKφ hKφ' hWφ hWφ' x g hg
  have hWp : ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ p = b p ∧ GlobalTheory.JSW.whit φ' p = b p := by
    intro p hp
    have h0 : GlobalTheory.JSW.tl ϖ (0 : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)) = 1 := by simp [GlobalTheory.JSW.tl]
    have e1 := hWφ 0 (by simp) p hp
    have e2 := hWφ' 0 (by simp) p hp
    rw [h0, mul_one] at e1 e2
    simp only [Finsupp.support_zero, Finset.prod_empty, mul_one] at e1 e2
    exact ⟨e1, e2⟩
  have hnorm : ∀ u : GA E (m + 1), ‖GlobalTheory.JSW.psiN u‖ = 1 := fun u => Circle.norm_coe _
  have hcc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z z' : ℂ, c * z * conj (c * z') = z * conj z' := by
    intro c hc z z'
    rw [map_mul]
    have : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
    calc c * z * (conj c * conj z') = (c * conj c) * (z * conj z') := by ring
      _ = _ := by rw [this, one_mul]
  have hzero : ∀ F F' : GA E (m + 1) → ℂ, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0 → GlobalTheory.ZEul.uInt F F' Φ N 0 g = 0 := by
    intro F F' h
    rcases h with h | h <;> simp only [GlobalTheory.ZEul.uInt, h, mul_zero, zero_mul]
  have hdec : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J,
        g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = u * p * finGL E (m + 1) κ ∧
        GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ∧
        GlobalTheory.ZEul.uInt φ φ Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ∧
        GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) := by
    intro h1 h2
    obtain ⟨u, hu, p, hp, κ, hκ, he⟩ := GlobalTheory.T.mirabolicCell_decomposition_lastRow E m S J hJ N hS Φ hΦ g hg h1 h2
    have k1 : GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN u * b p := by rw [he, hKφ κ hκ, hNφ u hu, (hWp p hp).1]
    have k2 : GlobalTheory.JSW.whit φ' (g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN u * b p := by rw [he, hKφ' κ hκ, hNφ' u hu, (hWp p hp).2]
    refine ⟨u, hu, p, hp, κ, hκ, he, ?_, ?_, ?_⟩ <;>
      simp only [GlobalTheory.ZEul.uInt, k1, k2, hcc _ (hnorm u), GlobalTheory.ZEul.detPow_zero, Complex.ofReal_one, mul_one]
  have h12 : GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧
      GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g := by
    by_cases h0 : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0
    · rw [hzero _ _ h0, hzero _ _ h0, hzero _ _ h0]; exact ⟨rfl, rfl⟩
    push_neg at h0
    obtain ⟨-, -, p, -, -, -, -, e1, e2, e3⟩ := hdec h0.1 h0.2
    rw [e1, e2, e3]; exact ⟨rfl, rfl⟩
  refine ⟨h12.1, h12.2, fun l => ?_⟩

  have hyt := GlobalTheory.ZEul.pInf_lastRow_tl_mul E m ϖ l.1 g
  obtain ⟨hind1, hind2⟩ := GlobalTheory.T.lastRowCongruenceIndicator_diagonalUniformizer_mul E m S ϖ hϖ N hint hloc l g hg
  have hdt := _root_.GlobalTheory.CellEvalDet.detPow_tl_mul E (m + 1) ϖ hϖ l.1 x g
  have hL : GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
      GlobalTheory.JSW.whit φ (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
        infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) *
      conj (GlobalTheory.JSW.whit φ' (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
        infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))) *
      Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) *
      (GlobalTheory.RSJ.detPow E (m + 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) : ℂ) := by
    simp only [GlobalTheory.ZEul.uInt]; rw [hyt]
  rw [hL]
  have hprod0 : ∀ w ∈ l.1.support, GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
      (fun i => (α' w i : ℂ)) x (l.1 w) = 0 →
      (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (α' w i : ℂ)) x v) = 0 :=
    fun w hw h => Finset.prod_eq_zero hw h
  by_cases hz : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0
  · have hIt : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0 := by
      rcases hz with h | h
      · exact Or.inl h
      · right
        by_cases hl : ∀ w, 0 ≤ l.1 w (Fin.last m)
        · rw [hind1 hl, h]
        · push_neg at hl; exact hind2 hl
    rw [hzero φ φ hz]
    rcases hIt with h | h <;> simp [h]
  push_neg at hz
  by_cases hlast : ∀ w, 0 ≤ l.1 w (Fin.last m)
  swap
  · push_neg at hlast
    obtain ⟨w, hw⟩ := hlast
    have hws : w ∈ l.1.support := by
      rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at hw; simp at hw
    rw [hind2 ⟨w, hw⟩, hprod0 w hws ?_]
    · simp
    · rw [GlobalTheory.ZEul.rsTerm, if_neg]; rintro ⟨h1, -⟩; exact absurd (h1 (Fin.last m)) (not_le.2 hw)
  rw [hind1 hlast]
  obtain ⟨u, hu, p, hp, κ, hκ, he, -, e0, -⟩ := hdec hz.1 hz.2
  rw [e0]
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l.1 with ht
  have hcomm : p * t = t * p := _root_.GlobalTheory.CellDec.TlComm.tl_commute_of_one_off E (m + 1) S ϖ l p hp.1
  have hu' : t * u * t⁻¹ ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) :=
    (GlobalTheory.SmGL.mem_unipB (Ad E)).1 (GlobalTheory.CellDec.tl_conj_mem ϖ l.1 ((GlobalTheory.SmGL.mem_unipB (Ad E)).2 hu))
  have hσ : t * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) =
      (t * u * t⁻¹) * (p * t) * finGL E (m + 1) κ := by
    rw [mul_assoc t g, he, hcomm]; group
  have hW : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, F (u * g) = GlobalTheory.JSW.psiN u * F g) →
      (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, F (g * finGL E (m + 1) κ) = F g) →
      F (t * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN (t * u * t⁻¹) * F (p * t) := by
    intro F hN hK; rw [hσ, hK κ hκ, hN _ hu']
  rw [hW _ hNφ hKφ, hW _ hNφ' hKφ', hcc _ (hnorm _)]
  by_cases hanti : ∀ w, Antitone (l.1 w)
  swap
  · push_neg at hanti
    obtain ⟨w, hw⟩ := hanti
    have hw0 : l.1 w ≠ 0 := by rintro h0; rw [h0] at hw; exact hw antitone_const
    have hwS : w ∉ S := fun h => hw0 (l.2 w h)
    have hws : w ∈ l.1.support := Finsupp.mem_support_iff.2 hw0
    rw [GlobalTheory.T.whittaker_diagonalUniformizer_eq_zero_of_not_antitone E m S J w hwS (hψ w hwS) ϖ (hϖ w) (GlobalTheory.JSW.whit φ) hNφ hKφ l.1 hw p (hp.1 w hwS), hprod0 w hws ?_]
    · simp
    · rw [GlobalTheory.ZEul.rsTerm, if_neg]; rintro ⟨-, h2⟩; exact hw h2
  have hnn : ∀ w i, 0 ≤ l.1 w i := fun w i => le_trans (hlast w) (hanti w (Fin.le_last i))
  obtain ⟨l', hl'app⟩ : ∃ l' : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), ∀ w, l' w = fun i => (l.1 w i).toNat :=
    ⟨Finsupp.mapRange (fun v i => (v i).toNat) (funext fun _ => rfl) l.1, fun w => Finsupp.mapRange_apply⟩
  have hl' : ∀ w i, ((l' w i : ℕ) : ℤ) = l.1 w i := fun w i => by
    rw [hl'app]; exact Int.toNat_of_nonneg (hnn w i)
  have hsupp : l'.support = l.1.support := by
    ext w
    simp only [Finsupp.mem_support_iff, ne_eq]
    constructor
    · intro h h0; apply h; rw [hl'app, h0]; rfl
    · intro h h0; apply h; funext i; have := hl' w i; rw [h0] at this; simpa using this.symm
  have htl : t = GlobalTheory.JSW.tl ϖ l' := GlobalTheory.T.adelicDiagonalUniformizer_eq_prod_localDiagonal E (m + 1) ϖ l.1 l' hl'
  have hsS : ∀ w ∈ l'.support, w ∉ S := fun w hw hS' => by
    rw [hsupp, Finsupp.mem_support_iff] at hw; exact hw (l.2 w hS')
  rw [hdt, htl, hWφ l' hsS p hp, hWφ' l' hsS p hp, hsupp]
  have key : ((GlobalTheory.CellDec.dinv (m + 1) l.1 : ℝ) : ℂ) *
      ((∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l' w)) *
        conj (∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l' w))) *
      (((∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-x * ∑ i, (l.1 w i : ℝ))) : ℝ) : ℂ) =
      l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (α' w i : ℂ)) x v := by
    rw [map_prod, ← Finset.prod_mul_distrib, GlobalTheory.CellDec.dinv, Complex.ofReal_prod, Complex.ofReal_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finsupp.prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hq : 0 < qV E w := Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    rw [hl'app]
    exact GlobalTheory.T.rankinSelbergLocalTerm_eq_sphericalWhittaker_product (qV E w) hq (m + 1) _ _ x (l.1 w) (hnn w) (hanti w)
  rw [← key]
  simp only [map_mul, Complex.ofReal_mul]
  ring

end GlobalTheory.ZEul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSetInertiaPowerTrivialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_set_inertia_power_trivial : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A), IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∃ m : ℕ, ((m : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  first | exact @GlobalTheory.TwistPullTame.good_pull_tame | exact GlobalTheory.TwistPullTame.good_pull_tame | (intros; apply GlobalTheory.TwistPullTame.good_pull_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableHopfOrderSubgroupTranslation
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

namespace GlobalTheory.RSnm

open GroundTheory.Automorphic.FourierWhittaker (partialCoeff_self partialCoeff_of_lt stepCoeff
  colGL_eq_blockGL whittaker_eq_partialCoeff continuous_partialCoeff)

theorem partialCoeff_partialCoeff_comp_blockGL {E : Type} [Field E] [NumberField E] {a n : ℕ}
    (han : a ≤ n) (φ : GA E n → ℂ) :
    ∀ (d j : ℕ), j + d = a → ∀ h : GA E a,
      partialCoeff (fun h : GA E a => partialCoeff φ a (blockGL han h)) j h =
        partialCoeff φ j (blockGL han h) := by
  intro d
  induction d with
  | zero =>
    intro j hj h
    obtain rfl : j = a := by omega
    rw [partialCoeff_self]
  | succ d ih =>
    intro j hj h
    have hja : j < a := by omega
    rw [partialCoeff_of_lt _ hja, partialCoeff_of_lt φ (hja.trans_le han)]
    unfold stepCoeff
    congr 1
    funext x
    rw [ih (j + 1) (by omega), map_mul, ← colGL_eq_blockGL hja han]

theorem whit_partialCoeff_comp_blockGL : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → ∀ h : GA E (m + 1),
    GlobalTheory.JSW.whit (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) h =
      GlobalTheory.JSW.whit φ (blockGL (by omega : m + 1 ≤ k + 1) h) := by
  intro E _ _ k m hmk φ hφ h
  have hb : m + 1 ≤ k + 1 := by omega
  have hQ : Continuous fun h : GA E (m + 1) => partialCoeff φ (m + 1) (blockGL hb h) :=
    (continuous_partialCoeff hφ (m + 1)).comp (GlobalTheory.RSnm.continuous_blockGL hb)
  unfold GlobalTheory.JSW.whit
  rw [whittaker_eq_partialCoeff hQ (Nat.succ_pos m), whittaker_eq_partialCoeff hφ (Nat.succ_pos k)]
  exact partialCoeff_partialCoeff_comp_blockGL hb φ m 1 (by omega) h

end GlobalTheory.RSnm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuperDiagBlockGL
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
noncomputable section

namespace GlobalTheory.RSnmUnfProps

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

theorem superDiag_blockGL {R : Type} [CommRing R] {j n : ℕ} (hj : j ≤ n) (g : GL (Fin j) R) :
    GlobalTheory.Whittaker.superDiag (blockGL hj g) = GlobalTheory.Whittaker.superDiag g := by
  unfold GlobalTheory.Whittaker.superDiag
  simp only [Finset.sum_filter]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
  · intro i hi
    have hij : ¬ (i : ℕ) < j := fun h => hi ⟨⟨i, h⟩, rfl⟩
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · rw [coe_blockGL, blockMat_apply, dite_eq_right hij, if_neg]
      intro h; rw [h] at hb; omega
    · rfl
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro b hb
      have hbj : ¬ (b : ℕ) < j := fun h => hb ⟨⟨b, h⟩, rfl⟩
      split_ifs
      · rw [coe_blockGL, blockMat_apply, dite_eq_left (by simp), dite_eq_right hbj]
      · rfl
    · intro b
      simp only [Fin.coe_castLE]
      split_ifs
      · rw [coe_blockGL, blockMat_apply, dite_eq_left (by simp), dite_eq_left (by simp)]
        rfl
      · rfl

variable {E : Type} [Field E] [NumberField E]

theorem psiN_blockGL {j n : ℕ} (hj : j ≤ n) (g : GA E j) :
    GlobalTheory.JSW.psiN (blockGL hj g : GA E n) = GlobalTheory.JSW.psiN g := by
  unfold GlobalTheory.JSW.psiN
  rw [superDiag_blockGL]

theorem norm_psiN {a : ℕ} (u : GA E a) : ‖GlobalTheory.JSW.psiN u‖ = 1 := by
  simp [GlobalTheory.JSW.psiN, Circle.norm_coe]

theorem blockGL_mem_NA {j n : ℕ} (hj : j ≤ n) {u : GA E j} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := j)) :
    (blockGL hj u : GA E n) ∈ GlobalTheory.JSW.NA (E := E) (a := n) := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · rw [coe_blockGL, blockMat_apply]
    split_ifs with ha hb hc
    · exact h1 _ _ (by rw [Fin.lt_def] at hik ⊢; exact hik)
    · rfl
    · exact absurd hik (by rw [hc]; exact lt_irrefl _)
    · rfl
  · rw [coe_blockGL, blockMat_apply]
    split_ifs with ha hb
    · exact h2 _
    · rfl
    · exact absurd rfl hb

theorem detAbs_unip {a : ℕ} {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) : GlobalTheory.RSnm.detAbs u = 1 := by
  have hd : Matrix.GeneralLinearGroup.det u = 1 := Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu)
  rw [GlobalTheory.RSnm.detAbs, hd, map_one]; rfl

end GlobalTheory.RSnmUnfProps


open GroundTheory.Automorphic.FourierWhittaker (blockGL) in
theorem GlobalTheory.RSnmUnfProps.uIntNM_props : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (F : (Fin (m + 1) → Ad E) → ℂ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) →
    Continuous (fun g : GA E (m + 1) => GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)) ∧
    Continuous (fun g : GA E (m + 1) => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)) ∧
    (∀ x : ℝ, Measurable (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x)) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g : GA E (m + 1),
      ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (u * g))‖ = ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ ∧
      ‖GlobalTheory.JSW.whit φ' (u * g)‖ = ‖GlobalTheory.JSW.whit φ' g‖ ∧
      GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g ∧ GlobalTheory.RSnm.detAbs (u * g) = GlobalTheory.RSnm.detAbs g ∧
      ∀ x : ℝ, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (u * g) = GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g) ∧
    ∀ (x : ℝ) (g : GA E (m + 1)), ‖GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g‖ ≤
      (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) +
        ‖GlobalTheory.JSW.whit φ' g‖ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ x) / 2 := by
  intro E _ _ _ m r S φ φ' F hW hW' hl hl' hF
  have hmn : m + 1 ≤ m + r + 1 + 1 := by omega
  have cW : Continuous (fun g : GA E (m + 1) => GlobalTheory.JSW.whit φ (blockGL hmn g)) :=
    hW.comp (GlobalTheory.RSnm.continuous_blockGL hmn)
  have cF : Continuous (fun g : GA E (m + 1) => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)) :=
    hF.comp GlobalTheory.ZUnfTheta.continuous_lastRow
  have cD : ∀ y : ℂ, Continuous (fun g : GA E (m + 1) => ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ y) := fun y =>
    (Complex.continuous_ofReal.comp GlobalTheory.RSnm.continuous_detAbs).cpow continuous_const
      fun h => Complex.ofReal_mem_slitPlane.2 (GlobalTheory.RSnm.detAbs_pos h)
  have hwu : ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g : GA E (m + 1),
      GlobalTheory.JSW.whit φ (blockGL hmn (u * g)) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ (blockGL hmn g) := by
    intro u hu g
    have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    rw [map_mul, hl _ (GlobalTheory.RSnmUnfProps.blockGL_mem_NA hmn hu'), GlobalTheory.RSnmUnfProps.psiN_blockGL]
  refine ⟨cW, cF, fun x => ?_, fun u hu g => ?_, fun x g => ?_⟩
  · unfold GlobalTheory.RSnmUnf.uIntNM
    exact (((cW.mul (Complex.continuous_conj.comp hW')).mul cF).mul (cD _)).measurable
  · have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    have hlr := GlobalTheory.ZEulProps.lastRow_unip hu g
    have hd : GlobalTheory.RSnm.detAbs (u * g) = GlobalTheory.RSnm.detAbs g := by
      rw [GlobalTheory.RSnm.detAbs_mul, GlobalTheory.RSnmUnfProps.detAbs_unip hu, one_mul]
    refine ⟨?_, ?_, hlr, hd, fun x => ?_⟩
    · rw [hwu u hu g, norm_mul, GlobalTheory.RSnmUnfProps.norm_psiN, one_mul]
    · rw [hl' u hu' g, norm_mul, GlobalTheory.RSnmUnfProps.norm_psiN, one_mul]
    · unfold GlobalTheory.RSnmUnf.uIntNM
      rw [hwu u hu g, hl' u hu' g, hlr, hd, map_mul]
      have h1 := GlobalTheory.ZEulProps.psiN_mul_conj u
      linear_combination (GlobalTheory.JSW.whit φ (blockGL hmn g) * conj (GlobalTheory.JSW.whit φ' g) *
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g) *
        ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2)) * h1

  · have hdp := GlobalTheory.RSnm.detAbs_pos g
    have hre : ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2).re = (x - ((r : ℝ) + 1)) / 2 + x / 2 := by
      push_cast
      simp only [Complex.sub_re, Complex.div_re, Complex.add_re, Complex.ofReal_re, Complex.natCast_re,
        Complex.one_re, Complex.natCast_im, Complex.one_im, Complex.add_im, Complex.ofReal_im]
      norm_num
      ring
    unfold GlobalTheory.RSnmUnf.uIntNM
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hdp, hre,
      Real.rpow_add hdp]
    have hA : GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) = (GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdp.le]; norm_num
    have hB : GlobalTheory.RSnm.detAbs g ^ x = (GlobalTheory.RSnm.detAbs g ^ (x / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdp.le]; norm_num
    rw [hA, hB]
    set a := ‖GlobalTheory.JSW.whit φ (blockGL hmn g)‖
    set b := ‖GlobalTheory.JSW.whit φ' g‖
    set c := ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖
    set α := GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2)
    set β := GlobalTheory.RSnm.detAbs g ^ (x / 2)
    have hc : 0 ≤ c := norm_nonneg _
    nlinarith [mul_nonneg hc (sq_nonneg (a * α - b * β))]
end
end

