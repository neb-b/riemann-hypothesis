module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0403
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0419
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0171
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0407
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationIndep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.ChernMass

theorem chernInt_eq_of_presents (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ)
    (r' : L'.ι → Y.Fnˣ) (hL : Presents Δ L r) (hL' : Presents Δ L' r')
    (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) L')
    (hφ : φ.IsCInf) (hψ : ψ.IsCInf) :
    φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  obtain ⟨ψ₀, hψ₀, hmass⟩ := _root_.GlobalTheory.CompanionTheory.ChernTransport.transport Y Δ L L' r r' hL hL' φ hφ
  rw [← hmass]
  exact _root_.GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_isCInf Y L' ψ₀ ψ hψ₀ hψ

end GlobalTheory.CompanionTheory.ChernMass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralRandomSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem measurable_gW (d : ℕ) (α : Type) [Fintype α] : Measurable (gW d α) := by
  unfold gW
  fun_prop

theorem encard_iUnion_fin {X : Type} {m : ℕ} (B : Fin m → Set X)
    (h : Pairwise (Function.onFun Disjoint B)) :
    (((⋃ t, B t).encard : ℕ∞) : ℝ≥0∞) = ∑ t, (((B t).encard : ℕ∞) : ℝ≥0∞) := by
  classical
  have key : ∀ s : Finset (Fin m), (((⋃ t ∈ s, B t).encard : ℕ∞) : ℝ≥0∞) =
      ∑ t ∈ s, (((B t).encard : ℕ∞) : ℝ≥0∞) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq, ENat.toENNReal_add,
        ih]
      exact Set.disjoint_iUnion₂_right.2 fun t ht => h (fun e => ha (e ▸ ht))
  simpa using key Finset.univ

theorem crofton : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∃ μ : Measure (Fin Y.dim → Fin n → ℂ), IsProbabilityMeasure μ ∧ μ ≪ volume ∧ (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ∫ C, (({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℝ) ∂μ := by
  intro Y Δ L r hL n b hb _
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  set φ := Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp) with hφdef
  have hφ : φ.IsCInf := Weight.isCInf_fsBasis hL b hb _ _
  have hneg : φ.chernPart Y.dim (-1) = 0 :=
    Weight.chernPart_neg_eq_zero hφ (Weight.semiPosReg_fsBasis hL b hb _ _)
  have hint := GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ
  have hfin : φ.chernPart Y.dim 1 Set.univ ≠ ⊤ := by
    have h1 := hint.1
    rw [IntegrableOn, Measure.restrict_univ, integrable_const_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 one_ne_zero
    · exact ((isFiniteMeasure_iff _).1 (by simpa using h1)).ne

  let ι := AlgChart Y.str (RingHom.id ℂ) Y.dim × L.ι × Fin n
  let S : ι → Set (CxPts Y.str (RingHom.id ℂ)) := fun t => t.1.e.source ∩
    (ptsIn Y.str (RingHom.id ℂ) (L.U t.2.1) ∩ ptsIn Y.str (RingHom.id ℂ) (nonzeroLocus (b t.2.2)))
  have hSo : ∀ t, IsOpen (S t) := fun t =>
    t.1.e.open_source.inter ((isOpen_ptsIn _).inter (isOpen_ptsIn _))
  have hSc : (⋃ t, S t) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := RingHom.id ℂ) y
    obtain ⟨j, hj⟩ := exists_mem_ptsIn hb y
    exact Set.mem_iUnion.2 ⟨⟨c, pick hL y, j⟩, hc, mem_pick hL y, hj⟩
  obtain ⟨m, l, A, hdis, hun, hsub, hσ⟩ := _root_.GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition _ ι S hSo hSc
  set G : ℝ≥0∞ := ENNReal.ofReal (Real.pi ^ (Y.dim * n)) with hG
  have hGpos : G ≠ 0 := by
    rw [hG, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hGtop : G ≠ ⊤ := ENNReal.ofReal_ne_top
  let Z : (Fin Y.dim → Fin n → ℂ) → Set (CxPts Y.str (RingHom.id ℂ)) := fun C =>
    {y | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
      ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}
  let P : Fin m → (Fin Y.dim → Fin n → ℂ) → Set (CxPts Y.str (RingHom.id ℂ)) := fun t C =>
    {y | y ∈ A t ∧ ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
      ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}
  have hpiece : ∀ t, Measurable (fun C => (((P t C).encard : ℕ∞) : ℝ≥0∞)) ∧
      ∫⁻ C, gW Y.dim (Fin n) C * (((P t C).encard : ℕ∞) : ℝ≥0∞) =
        G * φ.chernPart Y.dim 1 (A t) := fun t =>
    _root_.GlobalTheory.CompanionTheory.FSCrofton.crofton_chart Y L hL n b hb (l t).1 (l t).2.1 (l t).2.2 (A t)
      (fun y hy => (hsub t hy).1) (fun y hy => (hsub t hy).2.1)
      (fun y hy => (secVal_ne_zero_iff _ (hsub t hy).2.1).2 (hsub t hy).2.2) (hσ t)
  have hZ : ∀ C, (((Z C).encard : ℕ∞) : ℝ≥0∞) = ∑ t, (((P t C).encard : ℕ∞) : ℝ≥0∞) := by
    intro C
    rw [← encard_iUnion_fin]
    · congr 2
      ext y
      simp only [Set.mem_iUnion, P, Z, Set.mem_ofPred_eq]
      constructor
      · intro h
        obtain ⟨t, ht⟩ := Set.mem_iUnion.1 (hun ▸ Set.mem_univ y)
        exact ⟨t, ht, h⟩
      · rintro ⟨t, -, h⟩
        exact h
    · intro s t hst
      exact (hdis hst).mono (fun y hy => hy.1) (fun y hy => hy.1)
  have hNm : Measurable fun C => (((Z C).encard : ℕ∞) : ℝ≥0∞) := by
    simp only [hZ]
    exact Finset.measurable_fun_sum _ fun t _ => (hpiece t).1
  have hAm : ∀ t, MeasurableSet (A t) := fun t => by
    obtain ⟨K, hK, e⟩ := hσ t
    rw [← e]
    exact MeasurableSet.iUnion fun i => (hK i).measurableSet
  have hmass : φ.chernPart Y.dim 1 Set.univ = ∑ t, φ.chernPart Y.dim 1 (A t) := by
    rw [← hun, measure_iUnion hdis hAm, tsum_fintype]
  have hgm := measurable_gW Y.dim (Fin n)
  have hsum : ∫⁻ C, gW Y.dim (Fin n) C * (((Z C).encard : ℕ∞) : ℝ≥0∞) =
      G * φ.chernPart Y.dim 1 Set.univ := by
    simp only [hZ, Finset.mul_sum]
    rw [lintegral_finsetSum Finset.univ (f := fun t C => gW Y.dim (Fin n) C *
      (((P t C).encard : ℕ∞) : ℝ≥0∞)) fun t _ => hgm.mul (hpiece t).1, hmass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => (hpiece t).2
  let μ : Measure (Fin Y.dim → Fin n → ℂ) := G⁻¹ • volume.withDensity (gW Y.dim (Fin n))
  have hlin : ∀ f : (Fin Y.dim → Fin n → ℂ) → ℝ≥0∞, Measurable f →
      ∫⁻ C, f C ∂μ = G⁻¹ * ∫⁻ C, gW Y.dim (Fin n) C * f C := by
    intro f hf
    rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hgm hf]
    rfl
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have h1 := hlin (fun _ => 1) measurable_const
    simp only [lintegral_one, mul_one] at h1
    rw [h1, _root_.GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW, Fintype.card_fin]
    exact ENNReal.inv_mul_cancel hGpos hGtop
  have hN : ∫⁻ C, (((Z C).encard : ℕ∞) : ℝ≥0∞) ∂μ = φ.chernPart Y.dim 1 Set.univ := by
    rw [hlin _ hNm, hsum, ← mul_assoc, ENNReal.inv_mul_cancel hGpos hGtop, one_mul]
  refine ⟨μ, hprob, ?_, ?_⟩
  · exact (withDensity_absolutelyContinuous _ _).smul_left _
  · have hcast : ∀ C, ((Z C).ncard : ℝ) = ((((Z C).encard : ℕ∞) : ℝ≥0∞)).toReal := by
      intro C
      rw [Set.ncard]
      cases h : (Z C).encard with
      | top => simp
      | coe a => simp
    have hae : ∀ᵐ C ∂μ, (((Z C).encard : ℕ∞) : ℝ≥0∞) < ⊤ :=
      ae_lt_top hNm (by rw [hN]; exact hfin)
    have e := integral_toReal hNm.aemeasurable hae
    rw [hN] at e
    simp only [Z] at hcast e
    simp only [hcast]
    rw [e, Weight.chernInt, hneg]
    simp [Measure.real]
end GlobalTheory.CompanionTheory.FSCrofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellRightStable
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

variable {k : Type} [Field k]

theorem sEmb_mul_row (n : ℕ) (m : Mir k n) (q : Mir k (n + 1)) (j : Fin (n + 1 + 1)) :
    (((sEmb (k := k) n m * q : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)
        (Fin.castSucc (Fin.last n)) j =
      ((q : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) (Fin.castSucc (Fin.last n)) j := by
  have hm : ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) =
      GlobalTheory.BZMir.eLast k n :=
    (GlobalTheory.BZMir.mem_Mir_iff k (m : GL (Fin (n + 1)) k)).1 m.2
  have hm' : ∀ x, ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) x =
      GlobalTheory.BZMir.eLast k n x := fun x => congrFun hm x
  have he : (((GlobalTheory.CompanionTheory.BZPhiPG.sEmb (k := k) n m : GlobalTheory.BZMir.Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) :
      Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      GlobalTheory.BZMir.glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    rfl
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [he, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc, Fin.lastCases_last, hm', zero_mul,
    add_zero, GlobalTheory.BZMir.eLast]
  simp [Pi.single_apply]

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

theorem GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) :
    ∀ p ∈ Cl (k := k) i t, ∀ m, p * sO k i t m ∈ Cl (k := k) i t := by
  intro p hp m
  have key : ∀ j, (((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sO k i t m⁻¹ * p⁻¹ : GlobalTheory.BZMir.Mir k (i + 1 + t + 1)) :
      GL (Fin (i + 1 + t + 1 + 1)) k) : Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k)
        (Fin.castSucc (Fin.last (i + 1 + t))) j =
      (((p⁻¹ : GlobalTheory.BZMir.Mir k (i + 1 + t + 1)) : GL (Fin (i + 1 + t + 1 + 1)) k) :
        Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k) (Fin.castSucc (Fin.last (i + 1 + t))) j :=
    fun j => GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sEmb_mul_row (i + 1 + t)
      (GlobalTheory.CompanionTheory.BZPhiPG.castM k (by omega) m⁻¹) p⁻¹ j
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_setOf_eq] at hp ⊢
  intro c
  rw [_root_.mul_inv_rev, ← map_inv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sO k i t) m]
  exact (key _).trans (hp c)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedPointsCountComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
namespace GlobalTheory.CompanionTheory.KoszulCount

theorem cxPts_eq_of_pt_eq {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {y y' : CxPts p (RingHom.id ℂ)}
    (h : y.1 (closedPoint ℂ) = y'.1 (closedPoint ℂ)) : y = y' := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := y.1 (closedPoint ℂ)) (U := ⊤) trivial
  have hy : y ∈ ptsIn p (RingHom.id ℂ) U := mem_ptsIn.2 hx
  have hy' : y' ∈ ptsIn p (RingHom.id ℂ) U := mem_ptsIn.2 (h ▸ hx)
  have hv : ∀ g : Γ(X, U), ev p (RingHom.id ℂ) U g y = 0 → ev p (RingHom.id ℂ) U g y' = 0 := by
    intro g hg
    by_contra hne
    have h₁ := (mem_ptsIn_basicOpen hy' g).2 hne
    have h₂ : y ∈ ptsIn p (RingHom.id ℂ) (X.basicOpen g) := mem_ptsIn.2 (h ▸ mem_ptsIn.1 h₁)
    exact (mem_ptsIn_basicOpen hy g).1 h₂ hg
  refine Subtype.ext (GlobalTheory.Points.ext_of_valR hU hy hy' fun f => ?_)
  have e₀ : ev p (RingHom.id ℂ) U
      (f - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (ev p (RingHom.id ℂ) U f y)) y = 0 := by
    rw [ev_eq hy, map_sub, ← ev_eq hy, ← ev_eq hy, ev_algX hy]
    simp
  have e₁ := hv _ e₀
  rw [ev_eq hy', map_sub, ← ev_eq hy', ← ev_eq hy', ev_algX hy'] at e₁
  exact (sub_eq_zero.1 e₁).symm

theorem exists_cxPts_pt_eq {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    ∃ y : CxPts p (RingHom.id ℂ), y.1 (closedPoint ℂ) = x := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨⟨y, -, hs⟩, -⟩ :=
    GlobalTheory.SpecialisationPts.nonempty_and_isPreconnected X p inferInstance U hU x hxU
  exact ⟨y, (hs.mem_closed hx rfl : _ ∈ ({x} : Set X))⟩

theorem ncard_cxPts_over_closed : ∀ (Y : Var ℂ) (Z : Set Y.X), (∀ x ∈ Z, IsClosed ({x} : Set Y.X)) → ({y : CxPts Y.str (RingHom.id ℂ) | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z}).ncard = Z.ncard := by
  intro Y Z hZ
  have : LocallyOfFiniteType Y.str := inferInstance
  have him : (fun y : CxPts Y.str (RingHom.id ℂ) => y.1 (closedPoint ℂ)) ''
      {y : CxPts Y.str (RingHom.id ℂ) | y.1 (closedPoint ℂ) ∈ Z} = Z := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := exists_cxPts_pt_eq Y.str (hZ x hx)
      exact ⟨y, hx, rfl⟩
  conv_rhs => rw [← him]
  exact (Set.InjOn.ncard_image fun _ _ _ _ h => cxPts_eq_of_pt_eq h).symm

end GlobalTheory.CompanionTheory.KoszulCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantUnipotentActionTrivial
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem qC_sigX_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : HPG k (i + 1) (t + 1)) (h1 : (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1)) (h2 : (pgProj k (i + 1) (t + 1) u).2 = 1) (w : τ.V ⊗[ℂ] σ.V), qC τ σ (sigX τ σ u w) = qC τ σ w := by
  intro k _ _ _ _ i t τ σ u h1 h2 w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a b =>
    have hd : ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (pgProj k (i + 1) (t + 1) u).1 : ℂˣ) : ℂ) = 1 := by
      have := GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_unip (k := k) (i + 1) (((t + 1 : ℕ) : ℝ) / 2) ⟨_, h1⟩
      simpa using congrArg Units.val this
    have ha : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).1 a = τ.ρ (pgProj k (i + 1) (t + 1) u).1 a := by
      refine (twist_apply τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) _ a).trans ?_
      rw [hd, one_smul]
    have hρ : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).2 = 1 := by
      rw [h2, map_one]
    have hb : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).2 b = b :=
      LinearMap.congr_fun hρ b
    have e : sigX τ σ u (a ⊗ₜ[ℂ] b) = (τ.ρ (pgProj k (i + 1) (t + 1) u).1 a) ⊗ₜ[ℂ] b :=
      (extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (pgProj k (i + 1) (t + 1) u) a b).trans (congrArg₂ (fun x y => TensorProduct.tmul ℂ x y) ha hb)
    have hq : (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (pgProj k (i + 1) (t + 1) u).1 a) =
        (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      unfold twKer
      apply Submodule.subset_span
      exact ⟨⟨_, h1⟩, a, by simp⟩
    rw [e]
    exact congrArg (fun x => TensorProduct.tmul ℂ x b) hq

end GlobalTheory.CompanionTheory.BZPhiPG
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantUnipotentCharacterTrivial
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem qO_extTensor_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : MirUin k (i + 1)) (hu : mirChar k ψ i u = 1) (v : τ.V ⊗[ℂ] σ.V),
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1) v) = qO τ σ ψ v := by
  intro k _ _ _ _ i t ψ τ σ u hu v
  let L : (τ.V ⊗[ℂ] σ.V) →ₗ[ℂ] (τ.V ⊗[ℂ] σ.V) :=
    extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1)
  have hd : ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (u : Mir k (i + 1)) : ℂˣ) : ℂ) = 1 := by
    have := GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_unip (k := k) (i + 1) (((t + 1 : ℕ) : ℝ) / 2) u
    simpa using congrArg Units.val this
  have ha : ∀ a : τ.V, (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (u : Mir k (i + 1)) a = τ.ρ (u : Mir k (i + 1)) a := by
    intro a
    refine (twist_apply τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) _ a).trans ?_
    rw [hd, one_smul]
  have hρ : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 = 1 := map_one _
  have hb : ∀ b : σ.V, (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 b = b := fun b => LinearMap.congr_fun hρ b
  have e : ∀ (a : τ.V) (b : σ.V), L (a ⊗ₜ[ℂ] b) = (τ.ρ (u : Mir k (i + 1)) a) ⊗ₜ[ℂ] b := fun a b =>
    (extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
      ((u : Mir k (i + 1)), 1) a b).trans (congrArg₂ (fun x y => TensorProduct.tmul ℂ x y) (ha a) (hb b))
  have hq : ∀ a : τ.V, (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ (τ.ρ (u : Mir k (i + 1)) a) =
      (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ a := by
    intro a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    unfold twKer
    apply Submodule.subset_span
    exact ⟨u, a, by simp [hu]⟩
  have key : ∀ w : τ.V ⊗[ℂ] σ.V, qO τ σ ψ (L w) = qO τ σ ψ w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b =>
      rw [e]
      exact congrArg (fun x => TensorProduct.tmul ℂ x b) (hq a)
  exact key v

end GlobalTheory.CompanionTheory.BZPhiPG
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactArchimedeanEntriesBoundedStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_archimedean_entries_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J)), IsCompact C → ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ C, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n), ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.CFin.archMat_entries_bounded_of_isCompact | exact GlobalTheory.CompanionTheory.CFin.archMat_entries_bounded_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.CFin.archMat_entries_bounded_of_isCompact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactPartDiagonalMap
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.CptDiag

theorem isCompact_closure_zpowers_image {G G' : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    [T2Space G'] (φ : G →* G') (hφ : Continuous φ) (t : G)
    (ht : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (φ t) : Set G')) := by
  have hK : IsCompact (φ '' closure (Subgroup.zpowers t : Set G)) := ht.image hφ
  refine hK.of_isClosed_subset isClosed_closure ?_
  refine closure_minimal ?_ hK.isClosed
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), map_zpow φ t k⟩

theorem cptPart_diag : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (Z : Subgroup H), cptPart (Z.map ((MonoidHom.id H).prod (MonoidHom.id H))) = (cptPart Z).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  intro H _ _ _ _ Z
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨hu, hc⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    have := isCompact_closure_zpowers_image (MonoidHom.fst H H) continuous_fst _ hc
    simpa using this
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    have hcont : Continuous ((MonoidHom.id H).prod (MonoidHom.id H)) := by
      show Continuous fun x : H => (x, x)
      exact continuous_id.prodMk continuous_id
    exact ⟨Subgroup.mem_map_of_mem _ ht, isCompact_closure_zpowers_image _ hcont t hc⟩

end GlobalTheory.CompanionTheory.CptDiag
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousShiftedOrbitMap
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem continuous_castM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a = b) : Continuous (castM k h) := by
  subst h
  exact continuous_id

theorem continuous_sO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ), Continuous (sO k i t) := by
  intro k _ _ _ _ i t
  exact (GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.continuous_sEmb k ((i + 1) + t)).comp (continuous_castM k _)

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedBallIndicatorStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_induced_ball_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E), IsSmooth ρ → ∀ (s : kˣ) (e : E), ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k, restr ρ b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr | exact GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr | (intros; apply GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr <;> assumption)
end

