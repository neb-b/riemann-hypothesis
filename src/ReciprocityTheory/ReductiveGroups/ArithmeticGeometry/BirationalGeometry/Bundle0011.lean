module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeD
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

def brQ (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    Fin e → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

def brBad (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def brW (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

variable (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem brGood : ∀ x ∉ brBad R Ψ, ∀ j, x ∈ (R.A.chart j).source →
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr ⟨j, hj, h⟩)

theorem notMemB_of_notMem_brBad {x : R.X} (hx : x ∉ brBad R Ψ) : R.lift x x ∉ mcPts J := fun h => hx (Or.inl (Or.inl h))

theorem projection_zero_ne_of_notMem_bridgeBadSet {x : R.X} (hx : x ∉ brBad R Ψ) :
    Ψ (segre (R.lift x x)) 0 ≠ 0 := fun h => hx (Or.inl (Or.inr h))

theorem brW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : R.X}
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) : brW R Ψ x ∈ fibre P Ψ (brQ R Ψ x) := by
  classical
  have hz0 : R.lift x x ∈ mcPts P := R.mem x x (R.mem_U x)
  let k0 : K := hK.some
  let cc : K → ℂ := fun k => if k = k0 then (Ψ (segre (R.lift x x)) 0)⁻¹ else 1
  have hcc : ∀ k, cc k ≠ 0 := by
    intro k
    simp only [cc]
    split_ifs
    · exact inv_ne_zero h0
    · exact one_ne_zero
  have horb : SameOrbit (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) (R.lift x x) := ⟨cc, hcc, rfl⟩
  have hprod : ∏ k, cc k = (Ψ (segre (R.lift x x)) 0)⁻¹ := by simp [cc]
  have hseg : segre (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) = brW R Ψ x := by
    rw [segre_smul, hprod]
    rfl
  refine ⟨fun p => cc p.1 * R.lift x x p, mem_mcPts_of_sameOrbit hPh horb hz0, hseg, ?_⟩
  show Ψ ((Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)) = Fin.cons 1 (brQ R Ψ x)
  rw [map_smul]
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [inv_mul_cancel₀ h0]
  · simp [brQ, div_eq_inv_mul]

theorem brW_injOn : Set.InjOn (brW R Ψ) {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0} := by
  intro x hx x' hx' h
  have hz' := (R.mem x' x' (R.mem_U x')).1
  apply R.inj x x' hx.1
  apply sameOrbit_of_segre hz' (Ψ (segre (R.lift x x)) 0 * (Ψ (segre (R.lift x' x')) 0)⁻¹)
    (mul_ne_zero hx.2 (inv_ne_zero hx'.2))
  have h' : (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) =
      (Ψ (segre (R.lift x' x')) 0)⁻¹ • segre (R.lift x' x') := h
  rw [mul_smul, ← h', smul_smul, mul_inv_cancel₀ hx.2, one_smul]

theorem brFib_finite (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} \ brBad R Ψ).Finite := by
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  refine Set.Finite.of_injOn (f := brW R Ψ) (t := fibre P Ψ y) ?_ ?_ (fibreFinite K ι P e Ψ hP hΨ y)
  · intro x hx
    have h0 := projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2
    have hq : brQ R Ψ x = y := hx.1
    rw [← hq]
    exact brW_mem_fibre R Ψ hP.1 hPh h0
  · intro x hx x' hx' h
    exact brW_injOn R Ψ ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩
      ⟨notMemB_of_notMem_brBad R Ψ hx'.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx'.2⟩ h

theorem exists_of_mem_fibre {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y)
    (hy : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ brQ R Ψ x = y ∧ brW R Ψ x = w := by
  obtain ⟨z, hz, hzw, hΨw⟩ := hw
  have hzJ : z ∉ mcPts J := by
    intro hzJ
    refine hy ⟨z, hz, hzJ, ?_⟩
    rw [hzw]
    exact hΨw
  obtain ⟨x, hx⟩ := R.surj z hz hzJ
  obtain ⟨cc, hcc, hlift⟩ := hx
  have hμ : ∏ k, cc k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hcc k
  have hseg : segre (R.lift x x) = (∏ k, cc k) • w := by
    rw [hlift, segre_smul, hzw]
  have hΨl : Ψ (segre (R.lift x x)) = (∏ k, cc k) • Fin.cons 1 y := by
    rw [hseg, map_smul, hΨw]
  have h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, cc k := by
    rw [hΨl]
    simp
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hzJ
    refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (cc k)⁻¹, fun k => inv_ne_zero (hcc k), ?_⟩ h
    funext p
    rw [hlift]
    exact (inv_mul_cancel_left₀ (hcc p.1) (z p)).symm
  · rw [h0]
    exact hμ
  · funext i
    simp only [brQ, hΨl]
    simp [hμ]
  · show (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) = w
    rw [h0, hseg, smul_smul, inv_mul_cancel₀ hμ, one_smul]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeH
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def goodT (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (j : Fin A.n) : Set (Fin e → ℂ) :=
  {u | u ∈ (A.chart j).target ∧ AnalyticAt ℂ (q ∘ (A.chart j).symm) u ∧
    LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0}

theorem isOpen_goodT (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (j : Fin A.n) :
    IsOpen (goodT A q j) := by
  rw [isOpen_iff_mem_nhds]
  rintro u ⟨hut, han, hdet⟩
  have h1 : ∀ᶠ v in 𝓝 u, v ∈ (A.chart j).target := (A.chart j).open_target.mem_nhds hut
  have h2 : ∀ᶠ v in 𝓝 u, AnalyticAt ℂ (q ∘ (A.chart j).symm) v := han.eventually_analyticAt
  have hc : ContinuousAt (fun v => ContinuousLinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) v)) u :=
    ContinuousLinearMap.continuous_det.continuousAt.comp han.fderiv.continuousAt
  have h3 : ∀ᶠ v in 𝓝 u, ContinuousLinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) v) ≠ 0 :=
    hc.eventually_ne hdet
  filter_upwards [h1, h2, h3] with v a b c
  exact ⟨a, b, c⟩

theorem target_diff_goodT_subset (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (j : Fin A.n) :
    (A.chart j).target \ goodT A q j ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' S := by
  rintro u ⟨hut, hug⟩
  refine ⟨hut, ?_⟩
  by_contra hS
  apply hug
  have hx := (A.chart j).map_target hut
  have hr : (A.chart j) ((A.chart j).symm u) = u := (A.chart j).right_inv hut
  obtain ⟨h1, h2⟩ := hq _ hS j hx
  rw [hr] at h1 h2
  exact ⟨hut, h1, h2⟩

theorem integrableOn_chart [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Pt : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) *
      locDens A Φ j u) (A.chart j).target := by
  have hχc : ContinuousOn (fun u => Pt.χ j ((A.chart j).symm u)) (A.chart j).target := by
    have := ((Pt.smooth j) j).continuousOn
    simpa [Function.comp_def] using this
  have hKc : IsCompact ((A.chart j) '' tsupport (Pt.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart j).continuousOn.mono (Pt.tsupport_subset j))
  have hKt : (A.chart j) '' tsupport (Pt.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (Pt.tsupport_subset j hx)
  have hI := hg j _ hKt hKc
  have hI2 : IntegrableOn (fun u => Pt.χ j ((A.chart j).symm u) *
      (g ((A.chart j).symm u) * locDens A Φ j u)) ((A.chart j) '' tsupport (Pt.χ j)) := by
    first
      | exact hI.continuousOn_mul (hχc.mono hKt) hKc
      | exact IntegrableOn.continuousOn_mul (hχc.mono hKt) hI hKc
  simp only [mul_assoc]
  refine hI2.of_forall_diff_eq_zero (A.chart j).open_target.measurableSet ?_
  rintro u ⟨hut, huK⟩
  have hn : (A.chart j).symm u ∉ tsupport (Pt.χ j) := fun h =>
    huK ⟨_, h, (A.chart j).right_inv hut⟩
  have h0 : Pt.χ j ((A.chart j).symm u) = 0 := by
    first
      | exact image_eq_zero_of_nmem_tsupport hn
      | exact image_eq_zero_of_notMem_tsupport hn
  rw [h0, zero_mul]

theorem goodT_fibre_eq (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) :
    goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y} =
      (A.chart j) '' ((A.chart j).source ∩ (q ⁻¹' {y} \ S)) := by
  ext u
  constructor
  · rintro ⟨hu, hy'⟩
    have hx := (A.chart j).map_target hu.1
    have hxS : (A.chart j).symm u ∉ S := fun hS => hy ⟨u, ⟨hu, hS⟩, hy'⟩
    exact ⟨(A.chart j).symm u, ⟨hx, hy', hxS⟩, (A.chart j).right_inv hu.1⟩
  · rintro ⟨x, ⟨hx, hqx, hxS⟩, rfl⟩
    have hl : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
    obtain ⟨h1, h2⟩ := hq x hxS j hx
    refine ⟨⟨(A.chart j).map_source hx, h1, h2⟩, ?_⟩
    show q ((A.chart j).symm (A.chart j x)) ∈ ({y} : Set (Fin e → ℂ))
    rw [hl]
    exact hqx

theorem fib_term (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (Pt : ChartPartition A) (g : X → ℝ) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source)
    (hxS : x ∉ S) :
    Pt.χ j ((A.chart j).symm (A.chart j x)) * g ((A.chart j).symm (A.chart j x)) *
        locDens A Φ j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
      Pt.χ j x * (g x * pushDens A Φ q x) := by
  have hxc : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hl : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
  have hut : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hx
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart (chartIdx A x)).source :=
    ⟨hut, by
      show (A.chart j).symm (A.chart j x) ∈ (A.chart (chartIdx A x)).source
      rw [hl]
      exact hxc⟩
  have hD := locDensChart A Φ hΦ j (chartIdx A x) (A.chart j x) hut hmem.2
  rw [hl] at hD
  have hTan : AnalyticAt ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :=
    A.holo j (chartIdx A x) _ hmem
  have hTu : (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) = A.chart (chartIdx A x) x := by
    simp [hl]
  obtain ⟨hqc, -⟩ := hq x hxS (chartIdx A x) hxc
  obtain ⟨-, hdj⟩ := hq x hxS j hx
  have heq : (q ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j x)]
      (q ∘ (A.chart (chartIdx A x)).symm) ∘ (A.chart (chartIdx A x) ∘ (A.chart j).symm) := by
    have hopen : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart (chartIdx A x)).source ∈
        𝓝 (A.chart j x) :=
      ((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
        (A.chart (chartIdx A x)).open_source).mem_nhds hmem
    filter_upwards [hopen] with y hy
    simp only [Function.comp_apply]
    rw [(A.chart (chartIdx A x)).left_inv hy.2]
  have hfd : fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) =
      (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x)).comp
        (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x)) := by
    rw [heq.fderiv_eq, fderiv_comp _ (by rw [hTu]; exact hqc.differentiableAt)
      hTan.differentiableAt, hTu]
  have hdet : LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
    rw [hfd]
    exact LinearMap.det_comp _ _
  have hT0 : ‖LinearMap.det (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    rw [hdet, h, mul_zero] at hdj
    exact hdj rfl
  have hQ0 : ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    rw [hdet, h, zero_mul] at hdj
    exact hdj rfl
  rw [hl, jacN, pushDens, hD, hdet, norm_mul, mul_pow]
  field_simp

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeP
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}


set_option maxHeartbeats 1600000 in
theorem exists_monic_rel (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (P : Ideal (MRing ι)) (hPh : IsMultiHomogIdeal P) (hΨ : IsGoodProj P Ψ)
    (F : MvPolynomial ((k : K) → ι k) ℂ) :
    ∃ (n : ℕ) (c : ℕ → MvPolynomial (Fin (e + 1)) ℂ), c n = 1 ∧
      ∀ z ∈ mcPts P, ∑ i ∈ Finset.range (n + 1),
        eval (Ψ (segre z)) (c i) * eval (segre z) F ^ i = 0 := by
  classical
  have hrel := fun i => segre_rel hPh Ψ hΨ i
  choose r hr G hG hrelz using hrel
  let R := MvPolynomial (Fin (e + 1)) ℂ
  let Z := ↥(mcPts P)
  let φw : MvPolynomial ((k : K) → ι k) ℂ →+* (Z → ℂ) :=
    Pi.ringHom fun z : Z => MvPolynomial.eval (segre z.1)
  let φy : R →+* (Z → ℂ) := Pi.ringHom fun z : Z => MvPolynomial.eval (Ψ (segre z.1))
  letI : Algebra R (Z → ℂ) := φy.toAlgebra
  have hsmul : ∀ (c : R) (x : Z → ℂ), c • x = φy c * x := fun c x => Algebra.smul_def c x
  let T : Finset (((k : K) → ι k) →₀ ℕ) :=
    (Fintype.piFinset fun i => Finset.range (r i)).image Finsupp.equivFunOnFinite.symm
  have memT : ∀ s : ((k : K) → ι k) →₀ ℕ, (∀ i, s i < r i) → s ∈ T := fun s hs =>
    Finset.mem_image.2 ⟨⇑s, Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (hs i),
      Finsupp.equivFunOnFinite_symm_coe s⟩
  let N : Submodule R (Z → ℂ) :=
    Submodule.span R (↑(T.image fun s => φw (monomial s 1)) : Set (Z → ℂ))
  have hC : ∀ (a : ℂ) (x : Z → ℂ), x ∈ N → φw (C a) * x ∈ N := by
    intro a x hx
    have e1 : φw (C a) = φy (C a) := by
      funext z
      show MvPolynomial.eval (segre z.1) (C a) = MvPolynomial.eval (Ψ (segre z.1)) (C a)
      rw [eval_C, eval_C]
    rw [e1, ← hsmul]
    exact N.smul_mem _ hx
  have hY : ∀ (j : Fin (e + 1)) (x : Z → ℂ), x ∈ N → φy (X j) * x ∈ N := by
    intro j x hx
    rw [← hsmul]
    exact N.smul_mem _ hx
  have key : ∀ d, ∀ f : MvPolynomial ((k : K) → ι k) ℂ, f.totalDegree ≤ d → φw f ∈ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro f hf
      set_option synthInstance.maxHeartbeats 100000 in
        rw [f.as_sum, map_sum]
      refine N.sum_mem fun s hs => ?_
      rw [show monomial s (AddMonoidAlgebra.coeff f s) = C (AddMonoidAlgebra.coeff f s) * monomial s 1 by
        rw [C_mul_monomial, mul_one], map_mul]
      apply hC
      have hsdeg : (s.sum fun _ e => e) ≤ d := (le_totalDegree hs).trans hf
      by_cases hall : ∀ i, s i < r i
      · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (memT s hall)))
      · push_neg at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨s', hsplit⟩ : ∃ s', s = s' + Finsupp.single i (r i) :=
          ⟨s - Finsupp.single i (r i), (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hi)).symm⟩
        have hdeg : (s.sum fun _ e => e) = (s'.sum fun _ e => e) + r i := by
          rw [hsplit, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl]
        have hXr : φw (X i ^ r i) = ∑ j, φy (X j) * φw (G i j) := by
          funext z
          rw [Finset.sum_apply]
          show MvPolynomial.eval (segre z.1) (X i ^ r i) =
            ∑ j, MvPolynomial.eval (Ψ (segre z.1)) (X j) * MvPolynomial.eval (segre z.1) (G i j)
          simp only [map_pow, eval_X]
          exact hrelz i z.1 z.2
        have hri := hr i
        rw [hsplit, monomial_add_single, map_mul, hXr, Finset.mul_sum]
        refine N.sum_mem fun j _ => ?_
        rw [mul_left_comm, ← map_mul φw]
        apply hY
        apply ih ((s.sum fun _ e => e) - 1) (by omega)
        calc (monomial s' 1 * G i j).totalDegree
            ≤ (monomial s' (1 : ℂ)).totalDegree + (G i j).totalDegree := totalDegree_mul _ _
          _ ≤ (s'.sum fun _ e => e) + (r i - 1) := by
            rw [totalDegree_monomial _ one_ne_zero]
            exact Nat.add_le_add_left (hG i j) _
          _ ≤ (s.sum fun _ e => e) - 1 := by omega
  have hFG : (Subalgebra.toSubmodule (Algebra.adjoin R (Set.range φw))).FG := by
    have e2 : Subalgebra.toSubmodule (Algebra.adjoin R (Set.range φw)) = N := by
      apply le_antisymm
      · rw [Algebra.adjoin_eq_span, Submodule.span_le]
        intro x hx
        let Mw : Submonoid (Z → ℂ) :=
          { carrier := Set.range φw
            mul_mem' := by
              rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
              exact ⟨a * b, map_mul _ _ _⟩
            one_mem' := ⟨1, map_one _⟩ }
        have hx' : x ∈ Mw := (Submonoid.closure_le.2 (fun y hy => hy)) hx
        obtain ⟨f, rfl⟩ := hx'
        exact key _ f le_rfl
      · rw [Submodule.span_le]
        intro x hx
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact Algebra.subset_adjoin ⟨_, rfl⟩
    rw [e2]
    exact ⟨_, rfl⟩
  have hint : IsIntegral R (φw F) :=
    IsIntegral.of_mem_of_fg (Algebra.adjoin R (Set.range φw)) hFG (φw F)
      (Algebra.subset_adjoin ⟨F, rfl⟩)
  obtain ⟨p, hpm, hp⟩ := hint
  refine ⟨p.natDegree, p.coeff, hpm.coeff_natDegree, fun z hz => ?_⟩
  have h := congrFun hp ⟨z, hz⟩
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_apply] at h
  exact h

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem divSupp_one (P : Ideal (MRing ι)) : divSupp P 1 = ∅ := by
  ext W
  simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hW
  have hp := hW.1
  have htop : (⊤ : Ideal (MRing ι)) ≤ W := by
    have h2 := hp.2
    rwa [Ideal.span_singleton_one, sup_top_eq] at h2
  exact fun _ => hp.1.ne_top (top_le_iff.1 htop)

theorem logNorm_ofWeight_one (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (z : (Σ k, ι k) → ℂ) :
    logNorm (HermLine.ofWeight u hu) 1 z = u z := by
  simp [logNorm, HermLine.ofWeight, Real.exp_neg, Real.log_exp]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
  intro m hm k
  rw [MvPolynomial.support_one] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  simp

theorem metricChange : MetricChangeStatement := by
  intro K _ ι _ I hI P n L A u hu hP hL hA hsm
  have hB : IsSmoothHerm (HermLine.ofWeight u hu) := by
    show ContDiffOn ℝ _ (fun z => Real.exp (-u z)) _
    exact hsm.neg.exp
  have h1 : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hlog : logNorm (HermLine.ofWeight u hu) 1 = u := funext (logNorm_ofWeight_one u hu)
  have hrec : recR I P L (HermLine.ofWeight u hu) 1 = -ptsIntegral P (pot L) u := by
    unfold recR
    rw [divSupp_one]
    simp only [finsum_mem_empty, zero_sub, arInt, hlog]
    rfl
  rw [hI.2.1 P n L A _ hP hL hA hB,
    hI.2.2 P n L _ 1 (fun _ => 0) hP hL hB (fun _ => rfl) isMultiHomog_one h1, hrec]
  ring

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterExt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def PtsLocalStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g g' : ((Σ k, ι k) → ℂ) → ℝ),
    (∀ j, ∀ z ∈ mcPts P, φ j z = φ' j z) → (∀ z ∈ mcPts P, g z = g' z) →
    ptsIntegralAt P Ψ φ g = ptsIntegralAt P Ψ φ' g' ∧ ptsIntegral P φ g = ptsIntegral P φ' g'

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

