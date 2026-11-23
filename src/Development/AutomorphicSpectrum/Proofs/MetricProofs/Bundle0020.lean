module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.LeviForms.MixedIntegralInclusionExclusion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvDensOfOpen
section
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

private theorem fderiv2_add_lemma {D : ℕ} {g₁ g₂ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)}
    {y : Fin D → ℂ} (hU : IsOpen U) (hy : y ∈ U) (h₁ : ContDiffOn ℝ 2 g₁ U) (h₂ : ContDiffOn ℝ 2 g₂ U) :
    fderiv ℝ (fderiv ℝ (fun z => g₁ z + g₂ z)) y = fderiv ℝ (fderiv ℝ g₁) y + fderiv ℝ (fderiv ℝ g₂) y := by
  have hev : fderiv ℝ (fun z => g₁ z + g₂ z) =ᶠ[𝓝 y] fun z => fderiv ℝ g₁ z + fderiv ℝ g₂ z := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact fderiv_add ((h₁.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
      ((h₂.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  rw [hev.fderiv_eq]
  exact fderiv_add
    (((h₁.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (((h₂.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

private theorem hessL_add_lemma_2 {D : ℕ} (H₁ H₂ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    hessL (H₁ + H₂) = hessL H₁ + hessL H₂ := by
  funext i k
  simp only [hessL, ContinuousLinearMap.add_apply, Pi.add_apply]
  push_cast
  ring

theorem conv_dens_of_open {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (V : Set X) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ)
    (phT : Fin e → ℝ → X → ℝ) (hB : IsOpen V) (hΘ : IsPotential A Θ)
    (hth : ∀ i, IsPotential A (th i)) (hph : ∀ i, A.SmoothOn V (ph i))
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ i, A.Smooth (phT i t))
    (hC2 : ∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V, IsCompact K' →
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT i t ∘ (A.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph i ∘ (A.chart j).symm))) (nhdsWithin 0 (Set.Ioi 0)) K')
    (j : Fin A.n) (K : Set (Fin e → ℂ))
    (hK : K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V) (hKc : IsCompact K) :
    TendstoUniformlyOn (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
      (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j) (nhdsWithin 0 (Set.Ioi 0)) K := by
  classical
  have hS : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) :=
    (A.chart j).isOpen_inter_preimage_symm hB
  let a : Fin e → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k y =>
    hessC (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y
  let b : (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun y =>
    hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y
  let q : Fin e → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k y =>
    hessL (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) y)
  let p : Fin e → ℝ → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k t y =>
    hessL (fderiv ℝ (fderiv ℝ (phT k t ∘ (A.chart j).symm)) y)

  have hsplit : ∀ (k : Fin e) (u : X → ℝ) (W : Set (Fin e → ℂ)) (y : Fin e → ℂ), IsOpen W → y ∈ W →
      y ∈ (A.chart j).target → ContDiffOn ℝ 2 (u ∘ (A.chart j).symm) W →
      hessC (fun y' => (th k + LocPot.ofFun u + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
        a k y + hessL (fderiv ℝ (fderiv ℝ (u ∘ (A.chart j).symm)) y) + b y := by
    intro k u W y hW hyW hyt hu
    have h1 : ContDiffOn ℝ 2 (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) :=
      contDiffOn_infty.1 ((hth k).1 ((A.chart j).symm y) j) 2
    have h3 : ContDiffOn ℝ 2 (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y'))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y)) :=
      contDiffOn_infty.1 (hΘ.1 ((A.chart j).symm y) j) 2
    have o1 := (A.chart j).isOpen_inter_preimage_symm ((th k).isOpen_U ((A.chart j).symm y))
    have o3 := (A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U ((A.chart j).symm y))
    have oU := (o1.inter hW).inter o3
    have mU : y ∈ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) ∩ W ∩
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y)) :=
      ⟨⟨⟨hyt, (th k).mem_U _⟩, hyW⟩, ⟨hyt, Θ.mem_U _⟩⟩
    have hu' : ContDiffOn ℝ 2 (fun y' => u ((A.chart j).symm y')) W := hu
    have e12 : ContDiffOn ℝ 2 (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
        u ((A.chart j).symm y'))
        (((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) ∩ W ∩
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y))) :=
      (h1.mono (Set.inter_subset_left.trans Set.inter_subset_left)).add
        (hu'.mono (Set.inter_subset_left.trans Set.inter_subset_right))
    show hessL (fderiv ℝ (fderiv ℝ (fun y' => ((th k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
      u ((A.chart j).symm y')) + Θ.φ ((A.chart j).symm y) ((A.chart j).symm y'))) y) = _
    rw [fderiv2_add_lemma oU mU e12 (h3.mono Set.inter_subset_right),
      fderiv2_add_lemma oU mU (h1.mono (Set.inter_subset_left.trans Set.inter_subset_left))
        (hu'.mono (Set.inter_subset_left.trans Set.inter_subset_right)),
      hessL_add_lemma_2, hessL_add_lemma_2]
    rfl

  have hq0 : ∀ k, ContinuousOn (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) := fun k =>
    ((contDiffOn_infty.1 (hph k j) 2).fderiv_of_isOpen hS (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
      hS (by norm_num)
  have hq_cont : ∀ k, ContinuousOn (q k) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) := fun k =>
    continuous_hessL.comp_continuousOn (hq0 k)
  have hpq : ∀ k, TendstoUniformlyOn (p k) (q k) (nhdsWithin 0 (Set.Ioi 0)) K := by
    intro k
    have hbdd : Bornology.IsBounded (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) '' K) :=
      (hKc.image_of_continuousOn ((hq0 k).mono hK)).isBounded
    exact tendstoUniformlyOn_comp_continuous hessL continuous_hessL _ _ hbdd (hC2 k j K hK hKc)
  have hW : TendstoUniformlyOn (fun t y => fun k => a k y + p k t y + b y)
      (fun y k => a k y + q k y + b y) (nhdsWithin 0 (Set.Ioi 0)) K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hk : ∀ k, ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ y ∈ K, dist (q k y) (p k t y) < ε :=
      fun k => Metric.tendstoUniformlyOn_iff.1 (hpq k) ε hε
    filter_upwards [Filter.eventually_all.2 hk] with t ht y hy
    rw [dist_pi_lt_iff hε]
    intro k
    rw [dist_add_right, dist_add_left]
    exact ht k y hy
  have hWc : ContinuousOn (fun y k => a k y + q k y + b y) K := by
    refine continuousOn_pi.2 fun k => ?_
    have ha : ContinuousOn (a k) (A.chart j).target := hessC_base_continuousOn A (th k) (hth k) j
    have hb : ContinuousOn b (A.chart j).target := hessC_base_continuousOn A Θ hΘ j
    exact ((ha.mono fun z hz => (hK hz).1).add ((hq_cont k).mono hK)).add (hb.mono fun z hz => (hK hz).1)
  have hG : Continuous (fun w : Fin e → Fin e → Fin e → ℂ =>
      (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => w k).re) := by
    simp only [mdisc]
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    refine continuous_const.mul (continuous_finsetSum _ fun S _ => continuous_const.mul ?_)
    exact Continuous.matrix_det (continuous_finsetSum _ fun k _ => continuous_apply k)
  have hmain := tendstoUniformlyOn_comp_continuous _ hG _ _
    (hKc.image_of_continuousOn hWc).isBounded hW
  refine (hmain.congr ?_).congr_right ?_
  · filter_upwards [hT] with t ht y hy
    have hfun : (fun k => a k y + p k t y + b y) = fun k => hessC
        (fun y' => (th k + LocPot.ofFun (phT k t) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
      funext fun k => (hsplit k (phT k t) _ y ((A.chart j).isOpen_inter_preimage_symm isOpen_univ)
        ⟨(hK hy).1, trivial⟩ (hK hy).1 (contDiffOn_infty.1 (ht k j) 2)).symm
    show (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => (fun k => a k y + p k t y + b y) k).re = _
    rw [hfun]
    rfl
  · intro y hy
    have hfun : (fun k => a k y + q k y + b y) = fun k => hessC
        (fun y' => (th k + LocPot.ofFun (ph k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
      funext fun k => (hsplit k (ph k) _ y hS (hK hy) (hK hy).1 (contDiffOn_infty.1 (hph k j) 2)).symm
    show (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => (fun k => a k y + q k y + b y) k).re = _
    rw [hfun]
    rfl

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LineIsomorphismDefectFunction
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem defect_exists_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (A B : HermLine ι) (f g : MRing ι), IsMultiProjPrime P → IsLineIso P A.a B.a f g → IsSmoothHerm A → IsSmoothHerm B → ∃ w : ((Σ k, ι k) → ℂ) → ℝ, IsDefectOn P (mcPts P) f g A B w ∧ (∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z') ∧ R.A.Smooth (fun x => w (R.lift x x)) :=
  @PositivityTheory.UnitarySelfGeneration.i_defect

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem hessC_finset_sum_mul {D : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ∀ a, ContDiffAt ℝ 2 (f a) z) :
    hessC (fun y => ∑ a ∈ s, c a * f a y) z = ∑ a ∈ s, (c a : ℂ) • hessC (f a) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using st_hessC_eq_zero (f := fun _ => (0 : ℝ)) (y := z) 0 (Eventually.of_forall fun _ => rfl)
  | insert a s ha ih =>
    have h1 : ContDiffAt ℝ 2 (fun y => c a * f a y) z := contDiffAt_const.mul (hf a)
    have h2 : ContDiffAt ℝ 2 (fun y => ∑ b ∈ s, c b * f b y) z :=
      ContDiffAt.sum fun b _ => contDiffAt_const.mul (hf b)
    simp only [Finset.sum_insert ha]
    rw [hessC_add' _ _ z h1 h2, ih, hessC_const_mul']

theorem mdisc_sum_smul {D : ℕ} {σ : Type*} [Fintype σ] (H : σ → Matrix (Fin D) (Fin D) ℂ)
    (c : Fin D → σ → ℂ) :
    mdisc (fun i => ∑ a, c i a • H a) =
      ∑ w : Fin D → σ, (∏ i, c i (w i)) * mdisc (fun i => H (w i)) := by
  classical
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hM, M.map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [M.map_smul_univ, RingHom.id_apply, smul_eq_mul]

theorem locDens_sumPot_expand {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {σ : Type} [Fintype σ] (P : σ → LocPot X) (c : Fin e → σ → ℝ) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hC : ∀ a, IsTwiceDifferentiableAt A (P a) ((A.chart j).symm y)) :
    locDens A (fun i => sumPot (c i) P) j y =
      ∑ w : Fin e → σ, (∏ i, c i (w i)) * locDens A (fun i => P (w i)) j y := by
  classical
  have hf : ∀ a, ContDiffAt ℝ 2
      (fun y' => (P a).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro a
    have := hC a j ((A.chart j).map_target hy)
    rwa [(A.chart j).right_inv hy] at this
  have hH : ∀ i, hessC (fun y' => (sumPot (c i) P).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      ∑ a, ((c i a : ℝ) : ℂ) •
        hessC (fun y' => (P a).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := fun i =>
    hessC_finset_sum_mul Finset.univ (c i) _ y hf
  simp only [locDens, maDens, hH]
  rw [mdisc_sum_smul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Complex.ofReal_prod, Complex.re_ofReal_mul]
  ring

theorem mInt_sumPot_expand (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (σ : Type) [Fintype σ] (U : Set X) (P : σ → LocPot X)
    (c : Fin e → σ → ℝ) (g : X → ℝ) (hN : IsNull A Uᶜ)
    (hC : ∀ a, ∀ x ∈ U, IsTwiceDifferentiableAt A (P a) x)
    (hI : ∀ w : Fin e → σ, MIntegrable A (fun i => P (w i)) g) :
    MIntegrable A (fun i => sumPot (c i) P) g ∧
      mInt A (fun i => sumPot (c i) P) g =
        ∑ w : Fin e → σ, (∏ i, c i (w i)) * mInt A (fun i => P (w i)) g := by
  classical
  have key : ∀ j, ∀ᵐ y, y ∈ (A.chart j).target →
      locDens A (fun i => sumPot (c i) P) j y =
        ∑ w : Fin e → σ, (∏ i, c i (w i)) * locDens A (fun i => P (w i)) j y := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN j)] with y hy hyt
    have hU : (A.chart j).symm y ∈ U := by
      by_contra h
      exact hy ⟨hyt, h⟩
    exact locDens_sumPot_expand A P c j hyt fun a => hC a _ hU
  refine ⟨fun j K hK hKc => ?_, ?_⟩
  · have h1 : IntegrableOn (fun y => ∑ w : Fin e → σ, (∏ i, c i (w i)) *
        (g ((A.chart j).symm y) * locDens A (fun i => P (w i)) j y)) K :=
      integrable_finsetSum _ fun w _ => (hI w j K hK hKc).const_mul _
    refine Integrable.congr h1 ?_
    filter_upwards [ae_restrict_of_ae (key j), ae_restrict_mem hKc.measurableSet] with y hy hyK
    rw [hy (hK hyK), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  · have h : Nonempty (ChartPartition A) := existsPartition A
    simp only [mInt, dif_pos h, integralWith]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hw : ∀ w : Fin e → σ, IntegrableOn (fun y => (∏ i, c i (w i)) *
        (h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
          locDens A (fun i => P (w i)) j y)) (A.chart j).target := fun w =>
      (integrableOn_weight A h.some _ g (hI w) j).const_mul _
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ fun w _ => hw w]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (key j),
      ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy hyt
    rw [hy hyt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionNormIsomorphicLines
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LineDefect

open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

section Alg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem map_aeval_int {σ R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') (a : σ → R)
    (s : MvPolynomial σ ℤ) : ψ (aeval a s) = aeval (fun p => ψ (a p)) s := by
  have := MvPolynomial.comp_aeval_apply (R := ℤ) a ψ.toIntAlgHom s
  simpa using this

theorem aeval_eq_eval₂ {σ R : Type} [CommRing R] [Algebra ℤ R] (a : σ → R) (s : MvPolynomial σ ℤ) :
    aeval a s = eval₂ (Int.castRingHom R) a s := by
  rw [aeval_def]
  congr 1
  exact Subsingleton.elim _ _

theorem prod_cross {F : Type} [Field F] (x : K → F) (hx : ∀ k, x k ≠ 0) {a b : K → ℤ} {α γ : K → ℕ}
    (hd : ∀ k, (α k : ℤ) - γ k = a k - b k) :
    (∏ k, x k ^ a k) * ∏ k, x k ^ γ k = (∏ k, x k ^ b k) * ∏ k, x k ^ α k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hx k), ← zpow_add₀ (hx k)]
  congr 1
  linarith [hd k]

variable {Ω : Type} [Field Ω]

theorem cone_of_form {R : Type} [CommRing R] (b : (Σ k, ι k) → R) {s : MRing ι} {d : K → ℕ}
    (hs : IsMultiHomog s d) :
    aeval (fun p => (MvPolynomial.X p.1 : MvPolynomial K R) * MvPolynomial.C (b p)) s =
      (∏ k, MvPolynomial.X k ^ d k) * MvPolynomial.C (aeval b s) := by
  have h := aeval_blockScale hs (fun k => (MvPolynomial.X k : MvPolynomial K R)) fun p => MvPolynomial.C (b p)
  rw [map_aeval_int MvPolynomial.C b s]
  simp only [aeval_eq_eval₂] at h ⊢
  exact h

theorem aeval_ne_zero_of_form {y : (Σ k, ι k) → Ω} {s : MRing ι} {d : K → ℕ} (hs : IsMultiHomog s d)
    (h : s ∉ mCoordIdeal y) : aeval y s ≠ 0 := by
  intro h0
  refine h ?_
  change mConeMap y s = 0
  have e : mConeMap y s = aeval (fun p => (MvPolynomial.X p.1 : MvPolynomial K Ω) * MvPolynomial.C (y p)) s := by
    simp only [mConeMap, mul_comm]
  rw [e, cone_of_form y hs, h0, map_zero, mul_zero]

variable (S : Subring Ω) (φ : S →+* ℂ) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : (Σ k, ι k) → ℂ)
  (r : (Σ k, ι k) → S)

def coneS : MRing ι →ₐ[ℤ] MvPolynomial K S :=
  aeval fun p => MvPolynomial.X p.1 * MvPolynomial.C (r p)

def evS : MvPolynomial K S →+* ℂ := eval₂Hom φ fun k => w ⟨k, c k⟩

variable {S φ y c w r}

theorem coneS_eq_zero (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hr : ∀ p, (r p : Ω) * y ⟨p.1, c p.1⟩ = y p) {s : MRing ι}
    (hs : s ∈ mCoordIdeal y) : coneS S r s = 0 := by
  have hJ : Function.Injective (MvPolynomial.map (σ := K) S.subtype) :=
    MvPolynomial.map_injective _ Subtype.val_injective
  refine hJ ?_
  rw [map_zero]
  let Res : MvPolynomial K Ω →+* MvPolynomial K Ω :=
    eval₂Hom MvPolynomial.C fun k => MvPolynomial.C (y ⟨k, c k⟩)⁻¹ * MvPolynomial.X k
  have e : (MvPolynomial.map (σ := K) S.subtype).comp (coneS S r).toRingHom = Res.comp (mConeMap y).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) fun p => ?_
    have h1 : ((r p : S) : Ω) = y p * (y ⟨p.1, c p.1⟩)⁻¹ := by
      rw [← hr p, mul_inv_cancel_right₀ (hy p.1)]
    simp [coneS, mConeMap, Res, h1]
    ring
  have h0 : mConeMap y s = 0 := hs
  have := RingHom.congr_fun e s
  simpa [h0] using this

theorem evS_coneS (hw : ∀ p, w ⟨p.1, c p.1⟩ * φ (r p) = w p) (s : MRing ι) :
    evS S φ c w (coneS S r s) = evC w s := by
  have e : (evS S φ c w).comp (coneS S r).toRingHom =
      (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) fun p => ?_
    simp [coneS, evS, hw p]
  exact RingHom.congr_fun e s

theorem core (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hr : ∀ p, (r p : Ω) * y ⟨p.1, c p.1⟩ = y p)
    (hw : ∀ p, w ⟨p.1, c p.1⟩ * φ (r p) = w p) {f g u v : MRing ι} {α γ : K → ℕ} (hf : IsMultiHomog f α)
    (hg : IsMultiHomog g γ) (hG : aeval r g ≠ 0) (huv : u * f - v * g ∈ mCoordIdeal y) {s₁ s₂ : S}
    (hs : s₂ * aeval r f = s₁ * aeval r g) :
    evC w u * φ s₁ * ∏ k, w ⟨k, c k⟩ ^ α k = evC w v * φ s₂ * ∏ k, w ⟨k, c k⟩ ^ γ k := by
  have h0 := coneS_eq_zero hy hr huv
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h0
  have hcf : coneS S r f = (∏ k, MvPolynomial.X k ^ α k) * MvPolynomial.C (aeval r f) := cone_of_form r hf
  have hcg : coneS S r g = (∏ k, MvPolynomial.X k ^ γ k) * MvPolynomial.C (aeval r g) := cone_of_form r hg
  have hCG : (MvPolynomial.C (aeval r g) : MvPolynomial K S) ≠ 0 := by
    exact (map_ne_zero_iff (MvPolynomial.C : S →+* MvPolynomial K S) (MvPolynomial.C_injective K S)).2 hG
  have hcs : (MvPolynomial.C s₂ : MvPolynomial K S) * MvPolynomial.C (aeval r f) =
      MvPolynomial.C s₁ * MvPolynomial.C (aeval r g) := by
    rw [← map_mul, ← map_mul, hs]
  have key : coneS S r u * MvPolynomial.C s₁ * (∏ k, MvPolynomial.X k ^ α k) =
      coneS S r v * MvPolynomial.C s₂ * ∏ k, MvPolynomial.X k ^ γ k := by
    refine mul_left_cancel₀ hCG ?_
    rw [hcf, hcg] at h0
    linear_combination (MvPolynomial.C s₂) * h0 - (coneS S r u * ∏ k, MvPolynomial.X k ^ α k) * hcs
  have := congrArg (evS S φ c w) key
  rw [map_mul, map_mul, map_mul, map_mul, evS_coneS hw, evS_coneS hw] at this
  simpa [evS, map_prod] using this

end Alg

theorem norm_mul_h_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A B : HermLine ι) (e₀ ρ t : Ω) (f g u v : MRing ι) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, ι k) → ℂ) (ν : ℝ), IsCptGen ξ → CoordsAt ξ y z w → e₀ ≠ 0 → IsLineIso (mCoordIdeal y) A.a B.a f g → aeval y f = ρ * aeval y g → SecNorm ξ y A e₀ z w t ν → SecNorm ξ y B (ρ * e₀) z w t ν → 0 < ν → u * f - v * g ∈ mCoordIdeal y → evC w u ≠ 0 → ‖evC w v‖ * B.h w = ‖evC w u‖ * A.h w := by
  intro X Ω _ ξ K _ ι _ y A B e₀ ρ t f g u v z w ν hξ hw he hiso hρ hA hB hν huv _
  obtain ⟨⟨α, γ, hf, hg, hd⟩, hfP, hgP, -⟩ := hiso
  obtain ⟨c, hc⟩ := hA.exists_chart
  have hz := hA.specializes
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ ℂ z hz hξ
  obtain ⟨a₁, ha₁, e₁⟩ := hA.2.2 c hc
  obtain ⟨a₂, ha₂, e₂⟩ := hB.2.2 c hc
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  choose q hq hq' using fun p : Σ k, ι k => (hw.2 p.1 (c p.1) (IsUnit.mk0 _ (hc p.1))).2 p.2
  choose m hm using fun p => (hφ _ _).1 (hq p)
  obtain ⟨m₁, hm₁⟩ := (hφ _ _).1 ha₁
  obtain ⟨m₂, hm₂⟩ := (hφ _ _).1 ha₂
  set r : (Σ k, ι k) → regAt ξ ⟨centre z, hz⟩ := fun p => ⟨_, m p⟩ with hrdef
  have hr : ∀ p, (r p : Ω) * y ⟨p.1, c p.1⟩ = y p := fun p => div_mul_cancel₀ _ (hy p.1)
  have hwr : ∀ p, w ⟨p.1, c p.1⟩ * φ (r p) = w p := fun p => by
    rw [hm p, mul_comm]
    exact (hq' p).symm
  have hyf : aeval y f ≠ 0 := aeval_ne_zero_of_form hf hfP
  have hyg : aeval y g ≠ 0 := aeval_ne_zero_of_form hg hgP
  have hρ0 : ρ ≠ 0 := fun h => hyf (by rw [hρ, h, zero_mul])
  have hscale : ∀ {s : MRing ι} {d : K → ℕ}, IsMultiHomog s d →
      aeval y s = (∏ k, y ⟨k, c k⟩ ^ d k) * (aeval r s : regAt ξ ⟨centre z, hz⟩) := by
    intro s d hs
    have h1 := aeval_blockScale hs (fun k => y ⟨k, c k⟩) fun p => (r p : Ω)
    have e : (fun p : Σ k, ι k => y ⟨p.1, c p.1⟩ * (r p : Ω)) = y :=
      funext fun p => (mul_comm _ _).trans (hr p)
    rw [e] at h1
    rw [h1]
    congr 1
    exact (map_aeval_int (regAt ξ ⟨centre z, hz⟩).subtype r s).symm
  have hF := hscale hf
  have hG := hscale hg
  have hQα : (∏ k, y ⟨k, c k⟩ ^ α k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have hQγ : (∏ k, y ⟨k, c k⟩ ^ γ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have hPA : (∏ k, y ⟨k, c k⟩ ^ A.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hPB : (∏ k, y ⟨k, c k⟩ ^ B.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hP := prod_cross (fun k => y ⟨k, c k⟩) hy hd
  have hGne : aeval r g ≠ 0 := fun h => hyg (by rw [hG, h]; simp)
  have hs : (⟨_, m₂⟩ : regAt ξ ⟨centre z, hz⟩) * aeval r f = ⟨_, m₁⟩ * aeval r g := by
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul]
    change t / ((∏ k, y ⟨k, c k⟩ ^ B.a k) * (ρ * e₀)) * _ = t / ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀) * _
    have hFG := hρ
    rw [hF, hG] at hFG
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero hPB (mul_ne_zero hρ0 he))
      (mul_ne_zero hPA he)]
    have key : ((aeval r f : regAt ξ ⟨centre z, hz⟩) : Ω) * (∏ k, y ⟨k, c k⟩ ^ A.a k) =
        ((aeval r g : regAt ξ ⟨centre z, hz⟩) : Ω) * (∏ k, y ⟨k, c k⟩ ^ B.a k) * ρ :=
      mul_right_cancel₀ hQγ (by
        linear_combination ((aeval r f : regAt ξ ⟨centre z, hz⟩) : Ω) * hP + (∏ k, y ⟨k, c k⟩ ^ B.a k) * hFG)
    linear_combination (t * e₀) * key
  have hcore := core (φ := φ) hy hr hwr hf hg hGne huv hs
  rw [hm₁, hm₂] at hcore
  have hn := congrArg norm hcore
  simp only [norm_mul, norm_prod, norm_pow] at hn
  have hNγ : (∏ k, ‖w ⟨k, c k⟩‖ ^ γ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  have hN := prod_cross (fun k => ‖w ⟨k, c k⟩‖) (fun k => norm_ne_zero_iff.2 (hc k)) hd
  refine mul_right_cancel₀ hNγ (mul_left_cancel₀ hν.ne' ?_)
  linear_combination (‖evC w v‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ γ k) * e₂ - (‖evC w u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ γ k) * e₁ -
    (∏ k, ‖w ⟨k, c k⟩‖ ^ B.a k) * hn - (‖evC w u‖ * ‖a₁‖) * hN

end GlobalTheory.CompanionTheory.Ar.LineDefect
end
end

