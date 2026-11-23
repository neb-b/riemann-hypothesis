module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0895
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0874
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0884
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0893
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0888
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescentStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
open GlobalTheory.SupDescent in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.cuspForm_integral_lattice_unramified_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (c' : Coeff l) (hle : c.F ≤ c'.F) (la' : HeightOneSpectrum (𝓞 c'.F)), (∀ x : c.F, vLa la' (incF c c' hle x) = vLa la x) → CuspBC hle U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n) → ∀ f' ∈ cusp Xo c' (unfBC hle U) a n, BddAll Xo c' la' 1 f' → ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, la'.valuation c'.F (as i) ≤ 1) ∧ (∀ i, fs i ∈ supSet Xo c la (cusp Xo c U a n)) ∧ IsBC hle f' as fs := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hgood c' hle la' hv hBC a n hD _ f' hf' hb
  obtain ⟨m, as, fs, hfs, hIs⟩ := hBC a n f' hf'
  choose κ hκ0 hκ using fun i => _root_.GlobalTheory.CuspBound.exists_bddAll_cusp E H Dw l Xo c r U hU la p hp hpl hgood a n (fs i) hD (hfs i)
  let : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  have := liesOver (K := c.F) (K' := c'.F) hv
  obtain ⟨d, b, hb1, hb2⟩ := exists_residue_basis (la := la) (la' := la')
  choose x ρ hρ hx using fun i => exists_approx (K := c.F) (K' := c'.F) hv hb2 (as i) (hκ0 i)
  let F : Fin d → Rul Xo c := fun j => ∑ i, x i j • fs i
  have hF : ∀ j, F j ∈ cusp Xo c U a n := fun j => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfs i)
  have hG : ∀ i, κ i • fs i ∈ supSet Xo c la (cusp Xo c U a n) := fun i =>
    ⟨Submodule.smul_mem _ _ (hfs i), (GlobalTheory.GoodPtsModel.bddAll_iff_smul _ _).1 (hκ i)⟩
  have key : ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S),
      evR Xo c' f' y = ∑ j, algebraMap c'.F S (b j) * evR Xo c (F j) (y.res hle h) +
        ∑ i, algebraMap c'.F S (ρ i) * evR Xo c (κ i • fs i) (y.res hle h) := by
    intro S _ _ _ h y
    have h' : ∀ t : c.F, algebraMap c'.F S (algebraMap c.F c'.F t) = algebraMap c.F S t := h
    have hs : ∀ i, evR Xo c (κ i • fs i) (y.res hle h) = algebraMap c.F S (κ i) * evR Xo c (fs i) (y.res hle h) :=
      fun i => evalAt_smul _ _ _ _ _
    rw [hIs S h y]
    simp only [F, evR_sum, hs, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i]
    simp only [map_add (f := _), map_sum, map_mul, h', add_mul, Finset.sum_mul, mul_assoc]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨d + m, Fin.append (fun j => (b j : c'.F)) ρ, Fin.append F fun i => κ i • fs i, fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact la'.valuation_le_one (b j)
    · rw [Fin.append_right]; exact hρ j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    swap
    · rw [Fin.append_right]; exact hG j
    rw [Fin.append_left]
    refine ⟨hF j, fun T io e ho y hy => ?_⟩
    rw [map_one, one_mul]
    refine inV_of_forall_emb (K := c.F) (K' := c'.F) hb1 hy ho (fun j => evI y (F j)) ?_ j
    intro T' i e' σ e'' he' hi hT' hσ ho'
    obtain ⟨y₁, φ, hφ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i e' he' hi
    obtain ⟨y₂, hy₂⟩ := exists_intFr_ext hle (io := i.comp io) σ hσ y₁
    have hi' : ∀ t : T.Fr, vV T'.V (i t) = (e' : ℤ) * vV T.V t := fun t => by
      by_cases h : t = 0
      · subst h; simp [vV]
      · exact hi t h
    have h1 := hb T' σ e'' ho' y₂ hT'
    rw [map_one, one_mul] at h1
    have h2 : InV T' (∑ k, σ (ρ k) * evI y₁ (κ k • fs k)) := Subring.sum_mem _ fun k _ => by
      have h3 := (hG k).2 T' _ _ (ho.bc i he' hi') y₁ hT'
      rw [map_one, one_mul] at h3
      exact Subring.mul_mem _ ((GlobalTheory.GoodPtsModel.inV_iff_val T' _).2
        ((val_le_one_iff ho' _).2 (hρ k))) h3
    have h4 : ∀ j, i (evI y (F j)) = evI y₁ (F j) := fun j => by
      let := io.toAlgebra
      let := (i.comp io).toAlgebra
      exact (DFunLike.congr_fun hφ _).symm.trans
        (GlobalTheory.FlagTan.evR_frMap (cusp_le_sec Xo c U a n (hF j)).1 hmap).symm
    have h5 : evI y₂ f' = ∑ j, σ (b j) * evI y₁ (F j) + ∑ k, σ (ρ k) * evI y₁ (κ k • fs k) := by
      let := (i.comp io).toAlgebra
      let := σ.toAlgebra
      have := key T'.Fr hσ y₂.1
      rw [hy₂] at this
      exact this
    simp only [h4]
    rw [eq_sub_of_add_eq h5.symm]
    exact Subring.sub_mem _ h1 h2
  · intro S _ _ _ h y
    rw [key S h y, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactLocalConditionDataAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exactLocalConditionData_at_place : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i), tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i →
    D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d →
    (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool)
      (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ),
        ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      ∃ (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)) (_ : Irreducible lam)
        (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
        (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
        (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
        (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
        SetC HW r ρ π C hA lam θ h w' η typ U := by
  first | exact @GlobalTheory.UseLocInst.exists_setC | exact GlobalTheory.UseLocInst.exists_setC | (intros; apply GlobalTheory.UseLocInst.exists_setC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorInerStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.admSS i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → ResSpan i ρ π → π ∈ D.nd.Z i → (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) → D.R.t + 1 < D.nd.l i → ∃ S : IdempotentChoiceData D.nd i, IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S := by
  first | exact @GlobalTheory.UseFive.objects_globalStep_gen | exact GlobalTheory.UseFive.objects_globalStep_gen | (intros; apply GlobalTheory.UseFive.objects_globalStep_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatchedWhittakerVectorsShintaniRelations
section
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.Tx.exists_unipotentInvariant_compactlySupported_weight : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (x₀ : GA E (m + 1)),
    ∃ κ : GA E (m + 1) → ℝ, Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h, κ h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart (fun h => (κ h : ℂ)) g) (invSet E (m + 1))) ∧ 0 < κ x₀ := by
  first
  | exact @GlobalTheory.KappaCut.exists_kappa
  | exact GlobalTheory.KappaCut.exists_kappa
  | (intros; apply GlobalTheory.KappaCut.exists_kappa <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.Tx.contDiffOn_chart_globalWhittakerCoefficient : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g, ContDiffOn ℝ ∞ (chart (GlobalTheory.JSW.whit φ.1) g) (invSet E a) := by
  first | (exact @GlobalTheory.JSW.WhitSmooth.whit_contDiffOn) | (exact GlobalTheory.JSW.WhitSmooth.whit_contDiffOn) | (intros; apply GlobalTheory.JSW.WhitSmooth.whit_contDiffOn  <;> assumption)
end

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

namespace GlobalTheory.JSW.MatchedVec

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mem_mspanR_of_mem (π : CuspSub E a) {φ : Sm E a} (hφ : φ ∈ π.V) : φ.1 ∈ GlobalTheory.JSW.mspanR π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ hφ

def stab (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | finRep E a k φ = φ}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_level (φ : Sm E a) (hφ : IsAutForm φ) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧
      ∀ u ∈ U, ∀ g, φ.1 (g * finGL E a u) = φ.1 g :=
  ⟨stab φ, hφ.level, fun u hu g => congrArg (fun ψ : Sm E a => ψ.1 g) (show finRep E a u φ = φ from hu)⟩

theorem chart_mul (f f' : GA E a → ℂ) (g : GA E a) (x : Lie E a) :
    chart (fun h => f h * f' h) g x = chart f g x * chart f' g x := by
  unfold chart
  split_ifs <;> simp

end GlobalTheory.JSW.MatchedVec


open GlobalTheory.JSW.MatchedVec in
theorem GlobalTheory.JSW.MatchedVec.matched_vectors : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ),
    (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) →
    (∀ w ∉ S, HasSatGL w (π'.locRep w) (Finset.univ.val.map (β w))) →
    ∃ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
                       (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) ∧
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
        GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
          (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) ∧
      Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      ∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0 := by
  intro E _ _ _ m r S hcond π π' hπu hπ'u α β hα hβ
  obtain ⟨φ', hφ'V, hφ'K, x₀, hx₀S, hx₀⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E m S hcond π' β hβ
  obtain ⟨φ₀, hφ₀V, hφ₀K, x₁, hx₁S, hx₁⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E (m + r + 1) S hcond π α hα
  obtain ⟨κ, hκc, hκ0, hκN, ⟨C, hC, hκC⟩, ⟨Uκ, hUκo, hUκ⟩, hκsm, hκx₀⟩ := GlobalTheory.Tx.exists_unipotentInvariant_compactlySupported_weight E m x₀
  have haut' : IsAutForm φ' := (π'.cusp φ' hφ'V).1
  obtain ⟨U', hU'o, hU'⟩ := exists_level φ' haut'
  have hWN : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ'.1 (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ'.1 g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul haut'.continuous (fun γ g => haut'.left γ g) hu g
  have hWU : ∀ u ∈ U', ∀ g, GlobalTheory.JSW.whit φ'.1 (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit φ'.1 g := by
    intro u hu g
    rw [← GlobalTheory.JSW.KirSemi.whit_rt]
    congr 1
    funext y
    exact hU' u hu y
  have hWsm := GlobalTheory.Tx.contDiffOn_chart_globalWhittakerCoefficient E (m + 1) φ' haut'
  set βf : GA E (m + 1) → ℂ := fun h => (κ h : ℂ) * GlobalTheory.JSW.whit φ'.1 h with hβf
  have hβN : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, βf (u * g) = GlobalTheory.JSW.psiN u * βf g := by
    intro u hu g
    simp only [hβf, hκN u hu g, hWN u hu g]
    ring
  have hβC : ∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, βf h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C := by
    refine ⟨C, hC, fun h _ hne => hκC h ?_⟩
    intro h0
    apply hne
    simp [hβf, h0]
  have hβU : ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, βf (g * finGL E (m + 1) u) = βf g := by
    refine ⟨Uκ ⊓ U', hUκo.inter hU'o, fun u hu g => ?_⟩
    simp only [hβf, hUκ u hu.1 g, hWU u hu.2 g]
  have hβsm : ∀ g, ContDiffOn ℝ ∞ (chart βf g) (invSet E (m + 1)) := by
    intro g
    have e : chart βf g = fun x => chart (fun h => (κ h : ℂ)) g x * chart (GlobalTheory.JSW.whit φ'.1) g x :=
      funext fun x => chart_mul _ _ g x
    rw [e]
    exact (hκsm g).mul (hWsm g)
  obtain ⟨b, hbN, hbC, hbU, hbsm, hbblk⟩ := GlobalTheory.T.exists_whittaker_bump_extension_schur_complement E m r S βf hβN hβC hβU hβsm
  obtain ⟨F, hFspan, hFb, hFU, hFinv, hFeig⟩ :=
    GlobalTheory.T.kirillov_semilocal_smooth_bump E (m + r + 1) S b hbN hbC hbU hbsm π φ₀ hφ₀V ⟨x₁, hx₁S, hx₁⟩
  refine ⟨F, φ'.1, κ, hFspan, mem_mspanR_of_mem π' hφ'V, hFU, ?_, ⟨U', hU'o, hU'⟩, ?_, ?_, ?_, ?_,
    hκc, hκ0, hκN, ⟨C, hC, fun h _ hne => hκC h hne⟩, ⟨Uκ, hUκo, hUκ⟩, ⟨x₀, hx₀S, hκx₀, hx₀⟩⟩
  · intro w hw k hk g
    refine hFinv _ (pInf_finGL _) ?_ ?_ g
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [GlobalTheory.JSW.BumpShintani.map_comp_eq, pFin_finGL]
      exact pLoc_locGL_of_ne hne _
    · intro g'
      exact congrArg (fun ψ : Sm E (m + r + 1 + 1) => ψ.1 g') (hφ₀K w hw k hk)
  · intro w hw k hk g
    exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 g) (hφ'K w hw k hk)
  · intro ϖ hϖ l hl h hh
    exact GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + 1) S hcond π' β hβ φ' hφ'V hφ'K ϖ hϖ l hl h hh
  · intro ϖ hϖ l hl h hh
    set l' : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + r + 1 + 1) → ℕ) :=
      l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero with hl'
    have hsupp : l'.support = l.support := by
      ext w
      simp only [hl', Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq]
      constructor
      · intro h1 h2
        apply h1
        rw [h2, GlobalTheory.RSnmUnf.padNat_zero]
      · intro h1 h2
        apply h1
        funext i
        have := congrFun h2 ⟨i, by omega⟩
        simpa [GlobalTheory.RSnmUnf.padNat, i.2] using this
    have hl's : ∀ w ∈ l'.support, w ∉ S := fun w hw => hl w (hsupp ▸ hw)
    have hC := GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + r + 1 + 1) S hcond π α hα φ₀ hφ₀V hφ₀K ϖ hϖ l' hl's
    have hS : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l') = 1 :=
      fun w hw => GlobalTheory.JSW.BumpShintani.loc_tl ϖ l' w (fun h => hl's w h hw)
    have hmir := GlobalTheory.T.blockGL_supported_mem_mirabolic_supported E m r S h hh
    rw [map_mul, GlobalTheory.T.blockEmbeddingGL_torus_element_zero_padded E m r ϖ l, hFeig _ _ (GlobalTheory.JSW.BumpShintani.pInf_tl ϖ l') hS hC _ hmir.1, hsupp]
    rfl
  · intro h hh
    clear hβsm hβU hβC hβN hWsm hWU hWN hFeig hFinv
    exact (hFb _ (GlobalTheory.T.blockGL_supported_mem_mirabolic_supported E m r S h hh)).trans (hbblk h hh)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

open scoped ComplexOrder Topology
noncomputable section
namespace GlobalTheory.SmoothVac
variable {D : D7}

theorem comm_compAt_one (W : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (s : Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    s * compAt θ τ (Formalism.L2.Theta.mt W 1) = compAt θ τ (Formalism.L2.Theta.mt W 1) * s := by
  have h1 : Formalism.L2.Theta.mt W 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1, compAt, Matrix.map_one _ (by simp) (by simp), Matrix.one_mul, Matrix.mul_one]

theorem isCartanInv_one (V : HSp D) (hV : V.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) 1 := by
  have : gramAt D V τ = 1 := by rw [gramAt, hV, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

theorem exists_ne_zero_of_isVacO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT LS LT f) : ∃ w, f w ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have := hn p hp
  have h0 : f = 0 := funext h
  rw [h0] at this
  simp [nrm2] at this

theorem finCong_of_mul_left {a b : ℕ} {V : HSp D} {k : GA D V} (h : GlobalTheory.Member.FinCong V (a * b) k) :
    GlobalTheory.Member.FinCong V a k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h z hz
  exact ⟨b • y, nsmul_mem hy b, by rw [e, mul_smul]⟩

theorem finCong_of_mul_right {a b : ℕ} {V : HSp D} {k : GA D V} (h : GlobalTheory.Member.FinCong V (a * b) k) :
    GlobalTheory.Member.FinCong V b k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h z hz
  exact ⟨a • y, nsmul_mem hy a, by rw [e, mul_comm, mul_smul]⟩

theorem isOpen_comap_St (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    IsOpen (((Formalism.L2.DIV.St β).comap ((Formalism.UG.bc (Lev.swapAE D)).comp (Bridge.Gf V).subtype) :
      Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ_mat β ∅ (continuous_subtype_val (p := fun x => x ∈ Bridge.Gf V)) rfl]
    with x hh
  exact hh.1


set_option maxHeartbeats 1000000 in
theorem isOpen_map_levelGroup (V : HSp D) {N : ℕ} (hN : 0 < N) :
    IsOpen (((GlobalTheory.Member.PrincLevel.levelGroup V N).map (finHom V).rangeRestrict : Subgroup (Bridge.Gf V)) :
      Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨hop, -, -⟩ := GlobalTheory.Member.latHat_open_and_continuous D V
  have hc : Continuous fun x : Bridge.Gf V => ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :
      Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    Units.continuous_val.comp continuous_subtype_val
  obtain ⟨S, hS⟩ := h3.restrictScalars (R := ℤ)
  have hLS : (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ⊆
      (AddSubgroup.closure (S : Set (Fin V.rank → D.host.E)) : AddSubgroup (Fin V.rank → D.host.E)) := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (S : Set (Fin V.rank → D.host.E)) := by rw [hS]; exact hx
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    exact hx'
  have hU : (⋂ x ∈ S, {k : Bridge.Gf V | ∃ y ∈ latHat V,
      ((k : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :
        Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ GlobalTheory.AdLat.fv D.host.F x -
        GlobalTheory.AdLat.fv D.host.F x = N • y}) ∈ 𝓝 (1 : Bridge.Gf V) := by
    refine (Filter.biInter_finset_mem S).2 fun x _ => ?_
    have hcx := GlobalTheory.Member.PrincLevel.continuous_mulVec_sub hc (GlobalTheory.AdLat.fv D.host.F x)
    refine ((hop N hN).preimage hcx).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hU fun x hx => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hx
  obtain ⟨g, hg⟩ := x.2
  refine ⟨GlobalTheory.LevelNbhd.finPartG V g, ⟨GlobalTheory.LevelNbhd.finPartG_mem_GfC V g, ?_⟩, ?_⟩
  · unfold GlobalTheory.Member.FinCong
    rw [GlobalTheory.LevelNbhd.finHom_finPartG, hg]
    rw [h1] at hx ⊢
    exact GlobalTheory.Member.PrincLevel.cong_of_gen _ _ hLS _ N fun s hs => hx s hs
  · exact Subtype.ext (by rw [MonoidHom.coe_rangeRestrict, GlobalTheory.LevelNbhd.finHom_finPartG, hg])

theorem om_pow_eq {V W : HSp D} (ω : PairRep V W) (k : GA D V) (f : WO V W → ℂ) (c : ℂ) (hc : ω (k, 1) f = c • f) :
    ∀ m : ℕ, ω (k ^ m, 1) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, Prod.mk_one_one, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    have e : ((k ^ (m + 1), (1 : GA D W)) : GA D V × GA D W) = (k ^ m, 1) * (k, 1) := by
      rw [pow_succ, Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

end GlobalTheory.SmoothVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocycStatement
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ) (f : Br.G D.nbr i w hw → (Fin 1 → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 1),
    f ∈ divisibleCocycles (latC C (locOC C (chiRatO D.nd i c))) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧
      ∀ g, iotaC ↥C.LL.1 lam a (z' g) = f g := by
  first | exact @GlobalTheory.UseLoc.Cases.liftC_main | exact GlobalTheory.UseLoc.Cases.liftC_main | (intros; apply GlobalTheory.UseLoc.Cases.liftC_main <;> assumption)
end

