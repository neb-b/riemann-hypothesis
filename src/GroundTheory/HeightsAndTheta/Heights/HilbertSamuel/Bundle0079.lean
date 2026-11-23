module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0069

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridge
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Res

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem psi0_null (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 :=
  volume_projection_zeroSet_null R Ψ hP hΨ j

theorem ram_null (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 :=
  ram_null' R Ψ hP hΨ j

theorem brBad_null (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0 := by
  have h3 : brBad R Ψ ⊆ {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
      {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0} := by
    rintro x ((h | h) | ⟨k, hk, hn⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · by_cases h0 : Ψ (segre (R.lift x x)) 0 = 0
      · exact Or.inl (Or.inr h0)
      · refine Or.inr ⟨h0, k, hk, ?_⟩
        by_contra hd
        exact hn ⟨analyticAt_brQ R Ψ x k hk h0, hd⟩
  refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono h3)) ?_
  simp only [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (measure_union_null (R.null j) (psi0_null R Ψ hP hΨ j))
    (ram_null R Ψ hP hΨ j)

theorem potOf_isPotential (R : AnRes P J e) (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) :=
  isPotential_potOf R hL

theorem brIntegrable (R : AnRes P J e) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) :=
  brIntegrable_of logAbsLocInt R L A s hL hA hs

theorem brQ_image_null (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
  brQ_image_null_of R Ψ (brBad_null R Ψ hP hΨ)

theorem brFibreSum_ae (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w =
      ∑ᶠ x ∈ brQ R Ψ ⁻¹' {y} \ brBad R Ψ,
        logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x := by
  have hN : volume ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
    measure_union_null (projB_null Ψ hP hΨ R.homog R.nondeg) (brQ_image_null R Ψ hP hΨ)
  have hNae : ∀ᵐ y, y ∉ ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) :=
    ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hN)
  filter_upwards [hNae, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hy1 : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y := fun h => hyN (Or.inl h)
  have hfib : ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y = brW R Ψ '' (brQ R Ψ ⁻¹' {y} \ brBad R Ψ) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, -, hx0, hxq, rfl⟩ := exists_of_mem_fibre R Ψ hw hy1
      exact ⟨x, ⟨hxq, fun hbad => hyN (Or.inr ⟨x, ⟨hbad, hx0⟩, hxq⟩)⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
      rwa [show brQ R Ψ x = y from hx.1] at this
  rw [hfib, finsum_mem_image ((brW_injOn R Ψ).mono (by exact fun x hx => show _ ∧ _ from
    ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩))]
  refine finsum_mem_congr rfl fun x hx => ?_
  obtain ⟨γ, hγ, hval⟩ := exists_sheet_brW R Ψ L A s hP hL hs x hx.2
  rw [show brQ R Ψ x = y from hx.1] at hγ hval
  unfold sheetDensity
  rw [dite_eq_left ⟨γ, hγ⟩]
  exact (hind _ _ _ (Exists.choose_spec (⟨γ, hγ⟩ : ∃ γ, IsSheet P Ψ y (brW R Ψ x) γ)) hγ).trans hval

end Res

theorem bridge {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e : ℕ}
    (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    ptsIntegralAt P Ψ (pot L) (logNorm A s) =
      mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  rw [pushForward_null R.A (fun j => potOf R (L j)) (fun j => potOf_isPotential R (L j) (hL j))
    (brQ R Ψ) (brBad R Ψ) (brBad_null R Ψ hP hΨ) (brGood R Ψ) (brFib_finite R Ψ hP hΨ) _
    (brIntegrable R L A s hP hL hA hs)]
  exact integral_congr_ae (brFibreSum_ae R Ψ L A s hP hΨ hL hA hs)

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsSmallOfArVolPPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeWithoutBigness

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem tensor_constLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (z : (Σ k, ι k) → ℂ) :
    (A.tensor (constLine c)).h z = A.h z * Real.exp (-c) := rfl

theorem tensor_constLine_a (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) : (A.tensor (constLine c)).a = A.a := by
  show A.a + (constLine (ι := ι) c).a = A.a
  simp [constLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]

theorem isSmoothHerm_twist {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (c : ℝ) :
    IsSmoothHerm (A.tensor (constLine c)) := by
  unfold IsSmoothHerm
  have : (A.tensor (constLine c)).h = fun z => A.h z * Real.exp (-c) := rfl
  rw [this]
  exact hA.mul contDiffOn_const

theorem leviForm_twist (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (w : (Σ k, ι k) → ℂ) :
    leviForm (fun z => Real.log ((A.tensor (constLine c)).h z)) z w =
      leviForm (fun z => Real.log (A.h z)) z w := by
  have hev : (fun z => Real.log ((A.tensor (constLine c)).h z)) =ᶠ[𝓝 z]
      (fun z => Real.log (A.h z) + (-c)) := by
    filter_upwards [isOpen_blockNonzero.mem_nhds hz] with z' hz'
    rw [tensor_constLine_h, Real.log_mul (A.pos z' hz').ne' (Real.exp_pos _).ne', Real.log_exp]
  have h2 : fderiv ℝ (fderiv ℝ (fun z => Real.log ((A.tensor (constLine c)).h z))) z =
      fderiv ℝ (fderiv ℝ (fun z => Real.log (A.h z))) z := by
    rw [hev.fderiv.fderiv_eq]
    congr 1
    funext z'
    exact fderiv_add_const _
  unfold leviForm
  rw [h2]

theorem isSemipositiveRel_twist {P0 P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (h : IsSemipositiveRel P0 P A) (c : ℝ) : IsSemipositiveRel P0 P (A.tensor (constLine c)) := by
  refine ⟨isSmoothHerm_twist h.1 c, fun z hz w hw => ?_⟩
  rw [leviForm_twist A c hz.1 w]
  exact h.2 z hz w hw

theorem isConjInvariantH_twist {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : IsConjInvariantH A) (c : ℝ) :
    IsConjInvariantH (A.tensor (constLine c)) := by
  intro z
  rw [tensor_constLine_h, tensor_constLine_h, h z]

theorem nefOnFibres_twist {P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : NefOnFibres P A.a) (c : ℝ) :
    NefOnFibres P (A.tensor (constLine c)).a := by
  rw [tensor_constLine_a]
  exact h

theorem exists_small_section_of_arithmeticVolume_pos {Ω : Type} [Field Ω] {Q : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω}
    {D : ℕ} (h : 0 < arVolP Q La 1 D) : ∃ τ, 1 ≤ τ ∧ ∃ s ∈ La τ, s ≠ 0 ∧ Q τ s := by
  by_contra hne
  push Not at hne
  have hzero : ∀ k : ℕ, smallSectionCount Q La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hsub : Subsingleton {s : La (1 * k) // Q (1 * k) (s : Ω)} := by
        constructor
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        have ha0 : (a : Ω) = 0 := by
          by_contra h0
          exact hne (1 * k) (by omega) a a.2 h0 ha
        have hb0 : (b : Ω) = 0 := by
          by_contra h0
          exact hne (1 * k) (by omega) b b.2 h0 hb
        exact Subtype.ext (Subtype.ext (ha0.trans hb0.symm))
      have hcard : Nat.card {s : La (1 * k) // Q (1 * k) (s : Ω)} ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr hsub
      have hlog : smallSectionCount Q La (1 * k) = 0 := by
        unfold smallSectionCount
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h | h <;> rw [h] <;> simp
      rw [hlog, zero_div]
  have : arVolP Q La 1 D = 0 := by
    unfold arVolP
    simp only [hzero]
    exact limsup_const 0
  linarith

theorem exists_gt_of_lt {N e' g T : ℝ} (hN : 0 < N) (h : N * e' * g < T) :
    ∃ e'', e' < e'' ∧ N * e'' * g < T := by
  by_cases hg : g ≤ 0
  · refine ⟨e' + 1, by linarith, ?_⟩
    have h1 : N * (e' + 1) * g = N * e' * g + N * g := by ring
    have h2 : N * g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN.le hg
    linarith
  · push Not at hg
    have hd : 0 < (T - N * e' * g) / (2 * N * g) := div_pos (by linarith) (by positivity)
    refine ⟨e' + (T - N * e' * g) / (2 * N * g), by linarith, ?_⟩
    have h1 : N * (e' + (T - N * e' * g) / (2 * N * g)) * g = N * e' * g + (T - N * e' * g) / 2 := by
      field_simp
    rw [h1]
    linarith

end LatticeWithoutBigness


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.H1VanishGeneratedOfLocalizedSubsingleton
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Trivial

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]


omit [Fintype K] [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] in
theorem loc_subsingleton_of_kill {T : Submonoid (MRingOver S ι)} {u : MRingOver S ι} (hu : u ∈ T)
    (hk : ∀ y : M, u • y = 0) : Subsingleton (LocalizedModule T M) := by
  have h0 : ∀ x : LocalizedModule T M, x = 0 := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h y s =>
      rw [← LocalizedModule.zero_mk s]
      refine LocalizedModule.mk_eq.mpr ⟨⟨u, hu⟩, ?_⟩
      simp only [Submonoid.smul_def, smul_zero]
      rw [smul_comm, hk, smul_zero]
  exact ⟨fun a b => by rw [h0 a, h0 b]⟩

theorem h1_vanish_generated_of_localized_subsingleton
    (h : ∀ (n : ℕ) (I : KH.Cell K ι n), Subsingleton (LocalizedModule (KH.cellMon S I.1) M))
    (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    Subsingleton (KH.cechHc ι 𝓜 d 1) ∧ GeneratedMod S ι 𝓜 d := by
  have : Subsingleton (KH.CechC S ι M 1) := ⟨fun f g => funext fun I => (h 1 I).elim _ _⟩
  refine ⟨⟨fun x y => ?_⟩, fun I x _ => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]
  · refine ⟨1, 0, 0, Fin.elim0, Fin.elim0, Submonoid.one_mem _, isMultiHomog_one_zero, fun j => j.elim0,
      fun j => j.elim0, ?_⟩
    rw [one_smul, Fin.sum_univ_zero]
    exact (h 0 I).elim _ _


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem isMGraded_punit : KH.IsMGraded S ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) := by
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (fun _ => disjoint_bot_left)
    (Subsingleton.elim _ _), fun _ _ _ _ _ _ => (Submodule.mem_bot _).2 (Subsingleton.elim _ _)⟩

end Trivial

theorem H1GenerationDevissage.proof (hPF : KH.PrimeFiltStatement) (hSES : KH.CechSESStatement)
    (hGQ : GradedSubquot.Statement) (hGS : GenSESStep.Statement) : H1GenerationDevissage.Statement := by
  intro S _ K _ _ ι _ _ V N hS hP M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩ := hPF S K ι M 𝓜 hS hfin hgr
  let G : ℕ → Set M := fun j => m '' {l | (l : ℕ) < j}
  let F : ℕ → Submodule (MRingOver S ι) M := fun j => Submodule.span _ (G j)
  have hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c' := by
    rintro j _ ⟨l, -, rfl⟩
    exact ⟨c l, hm l⟩
  have hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)
  have hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j)) := fun j =>
    (hGQ S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1
  have key : ∀ j ≤ r, ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      Subsingleton (KH.cechHc ι (subGrading 𝓜 (F j)) (e + n • N) 1) ∧
        GeneratedMod S ι (subGrading 𝓜 (F j)) (e + n • N) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hF0 : F 0 = ⊥ := by simp [F, G]
      refine ⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton
        (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun y => ?_) _ _⟩
      rw [one_smul]
      have hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M) := by
        rw [← hF0]
        exact y.2
      exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot _).1 hy)
    | succ j ih =>
      intro hj
      obtain ⟨c₀, hc₀⟩ := ih (Nat.le_of_succ_le hj)
      let l : Fin r := ⟨j, hj⟩
      let L : Submodule (MRingOver S ι) (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hq := (hGQ S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1)) (hFmono (Nat.le_succ j))).2
      have hcolj : ∀ p : MRingOver S ι, p • m l ∈ F j ↔ p ∈ 𝔭 l := fun p => hcol l p
      have hkill : ∀ p ∈ 𝔭 l, ∀ y ∈ F (j + 1), p • y ∈ F j := by
        intro p hp y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨l', hl', rfl⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h
          · exact (F j).smul_mem p (Submodule.subset_span ⟨l', h, rfl⟩)
          · rw [show l' = l from Fin.ext h]
            exact (hcolj p).2 hp
        | zero => rw [smul_zero]; exact (F j).zero_mem
        | add x y _ _ hx hy => rw [smul_add]; exact (F j).add_mem hx hy
        | smul a x _ hx => rw [smul_comm]; exact (F j).smul_mem a hx
      have hann : 𝔭 l ≤ Module.annihilator (MRingOver S ι) (F (j + 1) ⧸ L) := by
        intro p hp
        rw [Module.mem_annihilator]
        intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective L q
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        show ((p • y : F (j + 1)) : M) ∈ F j
        rw [Submodule.coe_smul]
        exact hkill p hp y y.2
      have hfinQ : Module.Finite (MRingOver S ι) (F (j + 1) ⧸ L) := by
        have : Module.Finite (MRingOver S ι) (F (j + 1)) :=
          Module.Finite.iff_fg.2 (Submodule.fg_span ((Set.toFinite _).image m))
        infer_instance
      obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n →
          Subsingleton (KH.cechHc ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) 1) ∧
            GeneratedMod S ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) := by
        by_cases hrel : IsMultiProjPrime (𝔭 l)
        · exact hP (𝔭 l) hrel (hV.trans (h𝔭 l).2.2) (F (j + 1) ⧸ L) _ hfinQ hq hann e
        · have hirr : ¬ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (𝔭 l) := fun h => hrel ⟨(h𝔭 l).1, (h𝔭 l).2.1, h⟩
          simp only [ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, not_forall, not_exists, not_not] at hirr
          obtain ⟨k, hk⟩ := hirr
          refine ⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton (fun _ I => ?_) _ _⟩
          obtain ⟨i, hi⟩ := I.2.1 k
          exact loc_subsingleton_of_kill (Submonoid.subset_closure ⟨k, i, hi, rfl⟩)
            (Module.mem_annihilator.1 (hann (hk i)))
      refine ⟨max c₀ c₂, fun n hn => ?_⟩
      have h0 := hc₀ n (le_of_max_le_left hn)
      have h2 := hc₂ n (le_of_max_le_right hn)
      let g := Submodule.inclusion (hFmono (Nat.le_succ j))
      have hex : LinearMap.range g = LinearMap.ker L.mkQ := by
        rw [Submodule.range_inclusion, Submodule.ker_mkQ]
      have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g := fun _ _ hx => hx
      have hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L)
          L.mkQ := fun _ _ hx => Submodule.mem_map_of_mem hx
      have H := hSES S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex (e + n • N) 1
      exact ⟨H.1 h0.1 h2.1, hGS S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex _ h0.1 h0.2 h2.2⟩
  have hFr : F r = ⊤ := by
    rw [← hspan]
    simp [F, G]
  obtain ⟨c₁, hc₁⟩ := key r le_rfl
  refine ⟨c₁, fun n hn => ?_⟩
  obtain ⟨h1, hgen⟩ := hc₁ n hn
  let g := (F r).subtype
  have hex : LinearMap.range g = LinearMap.ker (0 : M →ₗ[MRingOver S ι] PUnit) := by
    rw [Submodule.range_subtype, hFr, LinearMap.ker_zero]
  have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F r)) 𝓜 g := fun _ _ hx => hx
  have hhG : KH.IsMGradedMap S ι 𝓜 (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) 0 :=
    fun _ _ _ => Submodule.zero_mem _
  have hU := h1_vanish_generated_of_localized_subsingleton (M := PUnit) (S := S) (ι := ι)
    (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun _ => Subsingleton.elim _ _)
    (fun _ => ⊥) (e + n • N)
  have H := hSES S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG
    (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex (e + n • N) 1
  exact ⟨H.1 h1 hU.1, hGS S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG
    (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex _ h1 hgen hU.2⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphChangeOfModel
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GraphChangeOfModel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} {ι₂ : K₂ → Type}

theorem exists_form_not_mem {P : Ideal (MRing ι)} {d : ℕ} {g : (Σ k, ι₂ k) → MRing ι} (hP : IsArithVar P d)
    (hBP : IsBasePtFree P g) : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P := by
  intro k₂
  by_contra hall
  push Not at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  choose i hi using hrel
  obtain ⟨N, hN⟩ := hBP k₂ i
  have hle : Ideal.span (Set.range fun j : ι₂ k₂ => g ⟨k₂, j⟩) ≤ P :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle] at hN
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp (hprime.mem_of_pow_mem N hN)
  exact hi k hk

end GraphChangeOfModel


open GraphChangeOfModel IndefiniteRowSideFullHecke.Inter in
theorem GraphChangeOfModel.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hIso : IsomInvariance.Statement) (hGI : GraphIsometricForms.Statement) : GraphChangeOfModel.Statement := by
  intro I hI K _ ι _ K₂ _ ι₂ _ P d g δ G J L L₁ hP hg hBP hImg hJ hL hL₁ ha hh
  obtain ⟨hΓ, himg, hdeg⟩ := hGr K ι K₂ ι₂ P d g δ hP hg (exists_form_not_mem hP hBP)
  obtain ⟨G'⟩ := hGF K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV _ d isBlockMap_inl hΓ
  obtain ⟨J', hJ', -⟩ := hEU G'.Φ _ (fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂))
  have e1 := hAI3 I hI K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV _ d G' J' L₁
    (fun j => pullHerm isBlockMap_inl (L₁ j)) isBlockMap_inl hΓ (by rw [himg]; exact hP) hJ' hL₁
    (fun j => isPullHerm_pullHerm _ _)
  have e2 := hAI3 I hI K₂ ι₂ (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inr inrV _ d G J L
    (fun j => pullHerm isBlockMap_inr (L j)) isBlockMap_inr hΓ hImg hJ hL
    (fun j => isPullHerm_pullHerm _ _)
  have e3 := hIso (K ⊕ K₂) (Sum.elim ι ι₂) (I (K ⊕ K₂) (Sum.elim ι ι₂)) (hI _ _) _ d
    (fun j => pullHerm isBlockMap_inl (L₁ j)) (fun j => pullHerm isBlockMap_inr (L j)) hΓ
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inl (isPullHerm_pullHerm _ _) (hL₁ j))
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inr (isPullHerm_pullHerm _ _) (hL j))
    (fun j => hGI K ι K₂ ι₂ P d g δ (L₁ j) (L j) _ _ hP hg hBP (ha j) (hh j) (isPullHerm_pullHerm _ _)
      (isPullHerm_pullHerm _ _))
  rw [hdeg G' J' hJ', himg] at e1
  rw [← e2, ← e3, e1]
  simp

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

