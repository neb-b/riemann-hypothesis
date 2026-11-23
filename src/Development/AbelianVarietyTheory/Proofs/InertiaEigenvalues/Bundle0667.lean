module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.SatakeDualWeyl.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
public import ReciprocityTheory.ResidueCardinality.ArtinOntoB
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0070
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0662
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharac
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorPowEqSum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem htOp_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (C : Core l) (ξ : Ainf l) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (σ : GQ l) (z : ℂ_[l]) (H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), U * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) → IsHT C ξ (fun g => (r g).val.map σ) z u → ∀ n : ℕ, u ^ n = ∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x) := by
  intro l _ K C ξ a d ρ r b e hR σ z H U u hU hu
  have hσz : ∀ c : ℤ_[l], σ (zOm l c) = zOm l c := fun c => by simp [zOm]
  have hθo : ∀ w : Om l, Per.θD l (C.o w) = algebraMap (Om l) ℂ_[l] w := fun w => C.o_sec.th w

  let S : Set (Om l) := Set.range fun t : Fin d × Fin a × Fin a => σ (b t.1 t.2.1 t.2.2)
  haveI : Finite S := (Set.finite_range _).to_subtype
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let K' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] S, hfd⟩
  have hfix : ∀ g : GQ l, g ∈ GK K' → ∀ i m k, g (σ (b i m k)) = σ (b i m k) := by
    intro g hg i m k
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg _
      (IntermediateField.subset_adjoin _ _ ⟨(i, m, k), rfl⟩)
  let B : Fin a → Matrix (Fin a) (Fin d) ℂ_[l] := fun k m i => algebraMap (Om l) ℂ_[l] (σ (b i m k))
  have hVu : IsUnit (H.V.map (Per.θD l)) := H.unit.map (Per.θD l).mapMatrix
  have col : ∀ k, u * B k * H.V.map (Per.θD l) = B k * U * H.V.map (Per.θD l) := by

    intro k
    ext m j
    let y : Fin a → Per.BdRp l := fun m => ∑ i, C.o (σ (b i m k)) * H.V i j
    let x : Fin a → Per.BdR l := fun m => ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * H.Q i j
    have hy : ∀ m, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * x m = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * y m) := by
      intro m
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [x, y, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hq := H.Q_eq i j
      calc algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * (algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * H.Q i j)
          = algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * H.Q i j) := by ring
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * H.V i j) := by rw [hq]
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * (C.o (σ (b i m k)) * H.V i j)) := by simp only [map_mul, map_pow]; ring
    have hx : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
        ((r g).val.map σ).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) *ᵥ (fun i => Per.σD (g : GQ l) (x i)) = x := by
      intro g hg
      funext m'
      have hσD : ∀ m, Per.σD (g : GQ l) (x m) = ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * Per.σD (g : GQ l) (H.Q i j) := by
        intro m
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [x, map_sum, map_mul, PrimeEx.sigD_o, hfix _ hg]
      have e1 : ∀ i, ∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) =
          ∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k))) := by
        intro i
        have h1 := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) => algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (M m' k)))) (hR.equi g i)
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [Matrix.mul_apply, Matrix.sum_apply, map_sum, map_mul, hσz] using h1
      have e2 : ∀ s, ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * Per.σD (g : GQ l) (H.Q i j) = H.Q s j := by
        intro s
        have h1 := congrFun (congrFun (H.inv g g.2) s) j
        simpa [Matrix.mul_apply] using h1
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.comp_apply, hσD]
      calc ∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * Per.σD (g : GQ l) (H.Q i j)
          = ∑ i, (∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k)))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            exact Finset.sum_comm
        _ = ∑ i, (∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k)))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [e1]
        _ = ∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k))) * ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
        _ = x m' := by simp only [e2, x]
    have h := hu K' (H.p j) H.q x y hx hy
    have hθy : (fun m => Per.θD l (y m)) = fun m => (B k * H.V.map (Per.θD l)) m j := by
      funext m'
      simp only [y, Matrix.mul_apply, Matrix.map_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hθo]
    rw [hθy] at h
    have h2 := congrFun h m
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
    rw [Matrix.mul_assoc u, Matrix.mul_assoc (B k), hU, ← Matrix.mul_assoc (B k), Matrix.mul_diagonal, Matrix.mul_apply, h2, mul_comm]
  have comm : ∀ k, u * B k = B k * U := by
    intro k
    have hd : IsUnit (H.V.map (Per.θD l)).det := (Matrix.isUnit_iff_isUnit_det _).1 hVu
    calc u * B k = u * B k * H.V.map (Per.θD l) * (H.V.map (Per.θD l))⁻¹ := by
          rw [Matrix.mul_assoc (u * B k), Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      _ = B k * U * H.V.map (Per.θD l) * (H.V.map (Per.θD l))⁻¹ := by rw [col k]
      _ = B k * U := by rw [Matrix.mul_assoc (B k * U), Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have key : ∀ x : Fin d → ℂ_[l], u * (∑ i, x i • (b i).map fun w => algebraMap (Om l) ℂ_[l] (σ w)) =
      ∑ i, (U *ᵥ x) i • (b i).map fun w => algebraMap (Om l) ℂ_[l] (σ w) := by
    intro x
    ext m k
    have h := congrFun (congrArg (· *ᵥ x) (comm k)) m
    simp only [← Matrix.mulVec_mulVec] at h
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, B] at h
    refine (Finset.sum_congr rfl fun x1 _ => ?_).trans (h.trans (Finset.sum_congr rfl fun c _ => ?_))
    · congr 1
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    · simp only [Matrix.mulVec, dotProduct]
      exact mul_comm _ _
  have one : ∑ i, (fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map (fun w => algebraMap (Om l) ℂ_[l] (σ w)) = 1 := by
    ext m k
    have h := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) => algebraMap (Om l) ℂ_[l] (σ (M m k))) hR.one
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hσz] at h
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [h]
    by_cases hmk : m = k <;> simp [Matrix.one_apply, hmk]
  intro n
  induction n with
  | zero => simpa using one.symm
  | succ n ih => rw [pow_succ', ih, key, Matrix.mulVec_mulVec, ← pow_succ']

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertPlaceLatticeIndexSumBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.InertIdx

theorem indexSum_inert : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(4 : ℝ)) := by
  classical
  intro D W n hn v f hf ⟨w, hw⟩ C hC hdist
  obtain ⟨ε, hε, rfl⟩ := hf
  have hP := GlobalTheory.HeckeRowsCompare.isPrimeIdem_of_inert (P := w) hw hε
  have hc := GlobalTheory.LabChar.fixed_of_tie hP
  obtain ⟨ϖ, σ, q, π, hU, -, hCh, hV⟩ := GlobalTheory.InertLoc.exists_chart hc hP
  obtain ⟨β, ι, hFr, hGC⟩ := hV W
  obtain ⟨hσσ, hσv, -, -, ⟨x0, hx0, hx0v⟩, -, -⟩ := hU
  let K := GlobalTheory.InertLoc.LP D w
  let O := w.adicCompletionIntegers D.host.E

  have hσO : ∀ x : O, σ (x : K) ∈ O := fun x => by
    show Valued.v (σ (x : K)) ≤ 1
    rw [hσv]; exact x.2
  let cO : O ≃+* O :=
    { toFun := fun x => ⟨σ x, hσO x⟩, invFun := fun x => ⟨σ x, hσO x⟩,
      left_inv := fun x => Subtype.ext (hσσ x), right_inv := fun x => Subtype.ext (hσσ x),
      map_mul' := fun x y => Subtype.ext (map_mul σ _ _), map_add' := fun x y => Subtype.ext (map_add σ _ _) }
  let cK : K ≃+* K :=
    { toFun := σ, invFun := σ, left_inv := hσσ, right_inv := hσσ, map_mul' := map_mul σ, map_add' := map_add σ }

  let H : GA D W → Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) K) := fun g =>
    if hg : SuppF W (algebraMap (AF D.host.F) (AE D) ε) g then (hGC.2.2.1 g hg).choose else 1
  have hH : ∀ g ∈ C, ι (H g) = g := fun g hg => by
    simp only [H, dif_pos (hC g hg).1]
    exact (hGC.2.2.1 g (hC g hg).1).choose_spec
  have hinj : Set.InjOn (fun g => ((H g : GL (Fin W.rank) K))) C := fun g hg g' hg' e => by
    rw [← hH g hg, ← hH g' hg', Subtype.ext e]
  have hsum := Finset.sum_image (f := fun x : GL (Fin W.rank) K =>
      ((((Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map (((x : Matrix (Fin W.rank) (Fin W.rank) K)).mulVecLin.restrictScalars O)).toAddSubgroup.relIndex
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2)) hinj
  have hterm : ∀ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = ((((Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((((H g : GL (Fin W.rank) K) : Matrix (Fin W.rank) (Fin W.rank) K)).mulVecLin.restrictScalars O)).toAddSubgroup.relIndex
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) := fun g hg => by
    conv_lhs => rw [← hH g hg]
    rw [_root_.GlobalTheory.InertLatIndex.latIndex_chart_eq D W v ε hε w σ π β ι hCh hFr hGC (H g)]
  rw [Finset.sum_congr rfl hterm, ← hsum]

  have hcard : Nat.card (IsLocalRing.ResidueField O) = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, ← GlobalTheory.LFun.InertChart.absNorm_eq
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (by
      have := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
      exact this))
  have hunit : IsUnit (cO ⟨x0, hx0⟩ - ⟨x0, hx0⟩) := by
    have hne : σ x0 - x0 ≠ 0 := fun e => by rw [e, map_zero] at hx0v; exact zero_ne_one hx0v
    refine isUnit_iff_exists_inv.2 ⟨⟨(σ x0 - x0)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · show Valued.v ((σ x0 - x0)⁻¹) ≤ 1
      rw [map_inv₀, hx0v, inv_one]
    · exact mul_inv_cancel₀ hne
  have hunitary : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      ((x : Matrix (Fin W.rank) (Fin W.rank) K).map cK)ᵀ * (1 : Matrix (Fin W.rank) (Fin W.rank) O).map (algebraMap O K) *
        (x : Matrix (Fin W.rank) (Fin W.rank) K) = (1 : Matrix (Fin W.rank) (Fin W.rank) O).map (algebraMap O K) := by
    intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (H g).2
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h1
  have hnontriv : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) ≠
        Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank))) := by
    intro x hx he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (_root_.GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint K O W.rank _).1 he
    have h2 := (hGC.2.2.2 (H g)).2 h1
    rw [hH g hg] at h2
    exact (hC g hg).2 h2
  have hdist' : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))), ∀ x' ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x' : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) →
      x = x' := by
    intro x hx x' hx' he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hx'
    have hm : (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map
        (((((H g)⁻¹ * H g' : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) K)) : GL (Fin W.rank) K) : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
        Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank))) := by
      have hcomp : ∀ (a b : GL (Fin W.rank) K), ((((a * b : GL (Fin W.rank) K)) : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
          ((a : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O).comp ((b : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) := by
        intro a b
        ext y : 1
        simp [Matrix.mulVec_mulVec]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcomp, Submodule.map_comp, ← he, ← Submodule.map_comp, ← hcomp, inv_mul_cancel]
      ext y
      simp
    have h1 := (_root_.GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint K O W.rank _).1 hm
    have h2 := (hGC.2.2.2 _).2 h1
    rw [map_mul, map_inv, hH g hg, hH g' hg'] at h2
    rw [hdist g hg g' hg' h2]
  have key := GlobalTheory.HermNbr.selfDual_sum_le O K cO cK (fun x => Subtype.ext (hσσ x)) (fun x => rfl)
    ⟨⟨x0, hx0⟩, hunit⟩ W.rank n 1 (by simp) (by simp) hn
    (C.image fun g => ((H g : GL (Fin W.rank) K))) hunitary hnontriv hdist'
  refine key.trans (le_of_eq ?_)
  rw [hcard]
  have hv0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_nonneg _
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hv0]
  norm_num

end GlobalTheory.InertIdx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinitesimalCharacterInduced
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.SpehInfChar GlobalTheory.BlockCap GlobalTheory.Published

namespace GlobalTheory.NormIndCap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem tensorSp_update {c : ℕ} {n : Fin c → ℕ} (V : ∀ i, Submodule ℂ (Sm E (n i))) (i : Fin c)
    (m : ∀ j, GA E (n j)) {F : (∀ j, GA E (n j)) → ℂ} (hF : F ∈ tensorSp V) :
    ∃ θ ∈ V i, ∀ y, F (Function.update m i y) = θ.1 y := by
  classical
  let L : ((∀ j, GA E (n j)) → ℂ) →ₗ[ℂ] (GA E (n i) → ℂ) :=
    { toFun := fun F y => F (Function.update m i y), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hle : tensorSp V ≤ ((V i).map (Sm E (n i)).subtype).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, rfl⟩
    refine ⟨(∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) • (φ i).1, (V i).smul_mem _ (φ i).2, ?_⟩
    funext y
    change (∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) * (φ i).1.1 y =
      ∏ j, (φ j).1.1 (Function.update m i y j)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  obtain ⟨θ, hθ, e⟩ := hle hF
  exact ⟨θ, hθ, fun y => (congrFun e y).symm⟩

theorem qdet_block_levi {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i)))
    (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ) (hM : HasInfCharGL (V i) τ M) (u : ℂ) (ψ : Sm E N)
    (hψ : (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorSp V) (m : ∀ j, GA E (n j)) :
    (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) =
      (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) := by
  obtain ⟨θ, hθ, hθe⟩ := tensorSp_update V i m hψ
  have hR : restrLin (stdBlocks n h) m i ψ = θ := Subtype.ext (funext fun y => hθe y)
  have key := LinearMap.congr_fun (qdet_intertwine (restrLin (stdBlocks n h) m i) _ (Eop τ)
    (restrLin_Eop (stdBlocks n h) m i τ) (u + ((n i : ℂ) - 1) / 2)) ψ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hR] at key
  have k2 := congrArg (fun φ : Sm E (n i) => φ.1 (m i)) key
  have hc : Formalism.REAL.qdet (Eop τ) (u + ((n i : ℂ) - 1) / 2) θ = (M.map (u + ·)).prod • θ := hM.2 u θ hθ
  have hm : Function.update m i (m i) = m := Function.update_eq_self i m
  simp only [hc] at k2
  have k3 : (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) (Function.update m i (m i))) =
      (M.map (u + ·)).prod * θ.1 (m i) := k2
  rw [hm, ← hθe, hm] at k3
  exact k3

theorem hasInfCharGL_map_mulChi {a : ℕ} {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (χ : HChar E) :
    HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map]; exact h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

end GlobalTheory.NormIndCap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfInnerEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.UpInj

theorem ops_exist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), TransLaws R i → ∃ B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H), (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) ∧ (∀ γ, ‖B γ‖ ≤ 1) ∧ B 1 = 1 ∧ ∀ γ k, k ∈ GlobalTheory.UpInj.KR R i → B (γ * k) = B γ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hTL
  choose B hBn hBp using fun γ : GfC (Wc D i) => hTL.2.2.1 γ γ.2
  refine ⟨B, fun γ x y => hBp γ x y, hBn, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    rw [← hBp 1 x y, ContinuousLinearMap.one_apply]
    exact hTL.2.2.2.2.2 x y
  · intro γ k hk
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    rw [← hBp, ← hBp]
    have := hTL.2.2.2.1 γ γ.2 1 (Subgroup.one_mem _) k (Subgroup.mem_subgroupOf.1 hk) x y
    rwa [one_mul] at this

theorem coef_mult_small : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T), FinMult R i t → LocSmall R i t → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ v (g h : GfC (Wc D i)), GlobalTheory.UpInj.cf (Wc D i) v g = 1 → GlobalTheory.UpInj.cf (Wc D i) v h = h → coef R i t μ 𝓕 ((g * h : GfC (Wc D i)) : GA D (Wc D i)) = coef R i t μ 𝓕 g * coef R i t μ 𝓕 h) ∧ ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (GfC (Wc D i))), (∀ g ∈ C, GlobalTheory.UpInj.cf (Wc D i) v g = g ∧ g ∉ GlobalTheory.UpInj.KR R i) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ GlobalTheory.UpInj.KR R i → g = g') → ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ ≤ s v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hFM hLS μ 𝓕 hμ
  refine ⟨fun v g h hg hh => ?_, ?_⟩
  · exact hFM μ 𝓕 hμ v _ (GlobalTheory.UpInj.isFinIdem_fE v) g g.2 (GlobalTheory.UpInj.trivAt_of_cf_eq_one _ v g hg) h
      ((GlobalTheory.UpInj.cf_eq_self_iff _ v h).1 hh)
  · obtain ⟨s, hs, hs1, hsb⟩ := hLS μ 𝓕 hμ
    refine ⟨s, hs, hs1, fun v C hC hCd => ?_⟩
    have := hsb v _ (GlobalTheory.UpInj.isFinIdem_fE v) (C.map (Function.Embedding.subtype _)) ?_ ?_
    · simpa [Finset.sum_map] using this
    · intro g hg
      obtain ⟨g, hgC, rfl⟩ := Finset.mem_map.1 hg
      exact ⟨(GlobalTheory.UpInj.cf_eq_self_iff _ v g).1 (hC g hgC).1, fun h => (hC g hgC).2 (Subgroup.mem_subgroupOf.2 h)⟩
    · intro g hg g' hg' hgg
      obtain ⟨g, hgC, rfl⟩ := Finset.mem_map.1 hg
      obtain ⟨g', hgC', rfl⟩ := Finset.mem_map.1 hg'
      refine congrArg _ (hCd g hgC g' hgC' (Subgroup.mem_subgroupOf.2 ?_))
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hgg


set_option maxHeartbeats 1000000 in
theorem coef_biinv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, LevFix R i t → VecNe R i t → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ g k k', k ∈ levW R i → k' ∈ levW R i → coef R i t μ 𝓕 (k * g * k') = coef R i t μ 𝓕 g) ∧ coef R i t μ 𝓕 1 = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF hVN μ 𝓕 hμ
  have hv : ∀ k ∈ levW R i, R.ωP i t (1, k) (R.vP i t) = R.vP i t := fun k hk => by
    have := hLF k hk 1
    rwa [GlobalTheory.RawLift.Model.pureTensor_one] at this
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [GlobalTheory.RawLift.Model.pureTensor_one] at this
  have hW := hL.thP.ωP i t
  refine ⟨fun g k k' hk hk' => ?_, GlobalTheory.RawLift.Model.coef_one R i t hVN μ 𝓕 hμ⟩
  rw [GlobalTheory.RawLift.Model.coef_mul_lev R i t hLF μ 𝓕 _ _ hk']
  unfold coef
  congr 1
  have e : R.ωP i t (1, k * g) = R.ωP i t (1, k) * R.ωP i t (1, g) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply]
  calc thetaIP μ 𝓕 (R.ωP i t (1, k) (R.ωP i t (1, g) (R.vP i t))) (R.vP i t)
      = thetaIP μ 𝓕 (R.ωP i t (1, k) (R.ωP i t (1, g) (R.vP i t))) (R.ωP i t (1, k) (R.vP i t)) := by rw [hv k hk]
    _ = thetaIP μ 𝓕 (R.ωP i t (1, g) (R.vP i t)) (R.vP i t) :=
      GlobalTheory.WeilPairing.thetaInner_weilRep D R.ψ _ _ _ _ (R.ωP i t) μ 𝓕 hW hμ (1, k) _ _ (hW.om_pres _ _ hth) hth

theorem injective_of_inner_eq {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (L : H →ₗ[ℂ] E) (W : H →L[ℂ] H) (a0 : ℝ) (ha0 : 0 < a0)
    (key : ∀ x y, ⟪L x, L y⟫_ℂ = (a0 : ℂ) * ⟪x, W y⟫_ℂ) (hW : Function.Injective W) : Function.Injective L := by
  have ha0' : (a0 : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have sym : ∀ x y, ⟪x, W y⟫_ℂ = ⟪W x, y⟫_ℂ := by
    intro x y
    have h2 : (a0 : ℂ) * ⟪x, W y⟫_ℂ = (a0 : ℂ) * ⟪W x, y⟫_ℂ := by
      rw [← key, ← inner_conj_symm, key, map_mul, Complex.conj_ofReal, inner_conj_symm]
    exact mul_left_cancel₀ ha0' h2
  intro x x' hxx'
  have hz : L (x - x') = 0 := by rw [map_sub, hxx', sub_self]
  have h3 := key (x - x') (W (x - x'))
  rw [hz, inner_zero_left] at h3
  have h4 : ⟪x - x', W (W (x - x'))⟫_ℂ = 0 := (mul_eq_zero.1 h3.symm).resolve_left ha0'
  rw [sym] at h4
  have hWz : W (x - x') = 0 := inner_self_eq_zero.1 h4
  exact sub_eq_zero.1 (hW (hWz.trans (map_zero W).symm))

set_option maxHeartbeats 4000000 in
theorem upInj_holds : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FinSum R i t → FinMult R i t → LevFix R i t → VecNe R i t → LocSmall R i t → LevProd R i → TransLaws R i → UpInj R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t hFS hFM hLF hVN hLS _ hTL
  classical
  obtain ⟨⟨p, hp⟩, -⟩ := (hL.thP.vP i t).1.2.norm
  obtain ⟨hinv, h1⟩ := coef_biinv D G Pl0 T A Ks R F hL i t hLF hVN p.1 p.2 hp
  obtain ⟨hmul, s, hs, hs1, hsm⟩ := coef_mult_small D G Pl0 T A Ks R i t hFM hLS p.1 p.2 hp
  obtain ⟨B, hB, hBn, hB1, hBK⟩ := ops_exist D G Pl0 T A Ks R i hTL
  obtain ⟨hrep, hhk⟩ := _root_.GlobalTheory.UpInj.heckeReps D G Pl0 T A Ks R i hTL B hB
  let a : GfC (Wc D i) → ℂ := fun g => coef R i t p.1 p.2 g
  have hmem := GlobalTheory.UpInj.kr_mem_iff R i
  have hfin := GlobalTheory.UpInj.kr_finite R i
  have hidem : ∀ v g, GlobalTheory.UpInj.cf (Wc D i) v (GlobalTheory.UpInj.cf (Wc D i) v g) = GlobalTheory.UpInj.cf (Wc D i) v g :=
    fun v g => GlobalTheory.UpInj.cf_cf (Wc D i) v g
  have horth : ∀ v w g, v ≠ w → GlobalTheory.UpInj.cf (Wc D i) w (GlobalTheory.UpInj.cf (Wc D i) v g) = 1 :=
    fun v w g h => GlobalTheory.UpInj.cf_orth (Wc D i) h g
  obtain ⟨e, he⟩ := _root_.GlobalTheory.quotient_equiv_restrictedFamilies _ (GlobalTheory.UpInj.KR R i) _ (GlobalTheory.UpInj.cf (Wc D i)) hmem hfin hidem horth
  have ha_bi : ∀ g k k', k ∈ GlobalTheory.UpInj.KR R i → k' ∈ GlobalTheory.UpInj.KR R i → a (k * g * k') = a g := by
    intro g k k' hk hk'
    exact hinv g k k' (Subgroup.mem_subgroupOf.1 hk) (Subgroup.mem_subgroupOf.1 hk')
  have ha_right : ∀ g k, k ∈ GlobalTheory.UpInj.KR R i → a (g * k) = a g := by
    intro g k hk
    have := ha_bi g 1 k (Subgroup.one_mem _) hk
    rwa [one_mul] at this
  have hfac := _root_.GlobalTheory.finprod_components_of_rightInvariant_mul _ _ _ _ a hmem hfin hidem horth ha_right h1 hmul
  have hloc := fun v => _root_.GlobalTheory.UpInj.localSum_hasSum _ (GlobalTheory.UpInj.KR R i) (GlobalTheory.UpInj.cf (Wc D i) v) _ a B (s v) (hidem v) ha_bi hBK hBn
    (hsm v) (hrep v) (hhk v)
  obtain ⟨W, hWi, hW⟩ := _root_.GlobalTheory.hasSum_inner_quotient_eulerProduct_injective _ (GlobalTheory.UpInj.KR R i) _ (GlobalTheory.UpInj.cf (Wc D i)) _ a B s e he hmem hidem horth ha_right h1 hfac
    hBn hB1 hBK hs hs1 hsm hloc
  intro th hth
  obtain ⟨a0, ha0, hsum⟩ := hFS th hth p.1 p.2 hp
  have ha0' : (a0 : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have key : ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ = (a0 : ℂ) * ⟪x, W y⟫_ℂ := by
    intro x y
    have h2 := (hW x y).mul_left (a0 : ℂ)
    have e : (fun q : GfC (Wc D i) ⧸ GlobalTheory.UpInj.KR R i => (a0 : ℂ) * (a (Quotient.out q) * ⟪x, B (Quotient.out q) y⟫_ℂ)) =
        fun q => (a0 : ℂ) * (coef R i t p.1 p.2 (Quotient.out q : GfC (Wc D i)) *
          trPair R i (Quotient.out q : GfC (Wc D i)) x y) := by
      funext q; rw [hB]
    rw [e] at h2
    exact (hsum x y).unique h2
  exact injective_of_inner_eq _ W a0 ha0 key hWi

end GlobalTheory.UpInj

end
end

