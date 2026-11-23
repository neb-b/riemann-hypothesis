module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Positivity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section

variable {K : Type u} [Fintype K] {ι : K → Type v} [∀ k, Fintype (ι k)] {F : Type w} [Field F]

theorem exists_isChart_of_isProjVarF {V : Ideal (MRingOver F ι)} {n : ℕ} (hV : IsProjVarF V n) :
    ∃ i, IsChart V i :=
  ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩

theorem ratDiv_one_eq_mapRange (V : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    ratDiv V f 1 = Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f) := by
  simp [ratDiv, divCycle_one]

theorem cycEval_ratDiv_one_nonneg (J : Ideal (MRingOver F ι) → ℤ) (V : Ideal (MRingOver F ι))
    (f : MRingOver F ι) (h : ∀ W ∈ divSupp V f, 0 ≤ J W) : 0 ≤ cycEval J (ratDiv V f 1) := by
  rw [ratDiv_one_eq_mapRange, cycEval, Finsupp.sum_mapRange_index (by simp), Finsupp.sum]
  exact Finset.sum_nonneg fun W hW => mul_nonneg (Nat.cast_nonneg _)
    (h W (mem_divSupp_of_divCycle_ne_zero (Finsupp.mem_support_iff.mp hW)))

theorem cycEval_ratDiv_one_pos (J : Ideal (MRingOver F ι) → ℤ) (V : Ideal (MRingOver F ι))
    (f : MRingOver F ι) (hne : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f ≠ 0) (h : ∀ W ∈ divSupp V f, 0 < J W) :
    0 < cycEval J (ratDiv V f 1) := by
  rw [ratDiv_one_eq_mapRange, cycEval, Finsupp.sum_mapRange_index (by simp), Finsupp.sum]
  refine Finset.sum_pos (fun W hW => mul_pos ?_ ?_) (Finsupp.support_nonempty_iff.mpr hne)
  · exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hW)
  · exact h W (mem_divSupp_of_divCycle_ne_zero (Finsupp.mem_support_iff.mp hW))

theorem ptDeg_pos {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) {i : ∀ k, ι k}
    (hi : IsChart V i) : 0 < ptDeg V i := by
  have := chart_finite hV hi
  have : Nontrivial (MRingOver F ι ⧸ chartIdeal V i) := ⟨(chart_isField hV hi).exists_pair_ne⟩
  exact Module.finrank_pos

theorem nonneg_of_isFieldIntersection {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)), IsProjVarF V n →
      ∀ L : Fin n → K → ℤ, (∀ j k, 0 ≤ L j k) → 0 ≤ I V n L := by
  intro n
  induction n with
  | zero =>
    intro V hV L _
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    rw [hI.1 V L i hV hi]
    exact Nat.cast_nonneg _
  | succ n ih =>
    intro V hV L hL
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    have hf := isMultiHomog_coordProd (F := F) i (fun k => (L (Fin.last n) k).toNat)
    have hfV := coordProd_not_mem hV.1.1 i hi (fun k => (L (Fin.last n) k).toNat)
    have hsec : IsRatSection V (L (Fin.last n))
        (∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ (L (Fin.last n) k).toNat) 1 :=
      ⟨_, 0, hf, isMultiHomog_one, hfV,
        fun h => hV.1.1.ne_top ((Ideal.eq_top_iff_one V).mpr h),
        fun k => by simp [Int.toNat_of_nonneg (hL _ k)]⟩
    rw [← Fin.snoc_init_self (α := fun _ => K → ℤ) L, hI.2 V n (Fin.init L) _ _ 1 hV hsec]
    exact cycEval_ratDiv_one_nonneg _ _ _ fun W hW =>
      ih W (isProjVarF_of_mem_divSupp hV hf hfV hW) _ fun j k => hL _ k


omit [Fintype K] in
theorem const_one_eq_snoc (n : ℕ) :
    (fun _ _ => (1 : ℤ) : Fin (n + 1) → K → ℤ) =
      Fin.snoc (α := fun _ => K → ℤ) (fun _ _ => 1) (fun _ => 1) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

theorem segre_pos_of_isFieldIntersection (hS : SegreDivisor.Statement.{u, v, w})
    {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)), IsProjVarF V n → 0 < I V n (fun _ _ => 1) := by
  intro n
  induction n with
  | zero =>
    intro V hV
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    rw [hI.1 V _ i hV hi]
    exact_mod_cast ptDeg_pos hV hi
  | succ n ih =>
    intro V hV
    obtain ⟨f, hf, hfV, hne⟩ := hS K ι F V n hV
    have hsec : IsRatSection V (fun _ => 1) f 1 :=
      ⟨_, 0, hf, isMultiHomog_one, hfV,
        fun h => hV.1.1.ne_top ((Ideal.eq_top_iff_one V).mpr h), fun k => by simp⟩
    rw [const_one_eq_snoc, hI.2 V n _ _ f 1 hV hsec]
    exact cycEval_ratDiv_one_pos _ _ _ hne fun W hW =>
      ih W (isProjVarF_of_mem_divSupp hV hf hfV hW)

end

theorem Positivity.of_found (hS : SegreDivisor.Statement.{u, v, w}) {K : Type u} [Fintype K]
    (F : Type w) [Field F] (ι : K → Type v) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.PositivityStatement F ι :=
  fun _ hI V n hV =>
    ⟨fun L hL => nonneg_of_isFieldIntersection hI n V hV L hL,
      segre_pos_of_isFieldIntersection hS hI n V hV⟩

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

namespace PtsSumMeasurable

theorem measurable_maDensity {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) :
    Measurable (maDensity φ) := by
  set M : ((Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) → Matrix (Fin D) (Fin D) ℂ := fun H i j =>
    ((H (Pi.single i 1) (Pi.single j 1) +
        H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
      Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1) -
        H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ))) / 4 with hMdef
  have hM : Continuous M := continuous_pi fun i => continuous_pi fun j => by
    simp only [hMdef]
    set_option synthInstance.maxHeartbeats 200000 in
      fun_prop
  have hdisc : Continuous fun B : Fin D → Matrix (Fin D) (Fin D) ℂ => (mixedDisc B).re := by
    unfold mixedDisc
    exact Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun S _ =>
      continuous_const.mul (Continuous.matrix_det (continuous_finsetSum _ fun k _ =>
        continuous_apply k))))
  have heq : maDensity φ = fun z => (D.factorial : ℝ) * (2 / Real.pi) ^ D *
      (mixedDisc fun k => M (fderiv ℝ (fderiv ℝ (φ k)) z)).re := rfl
  rw [heq]
  exact measurable_const.mul ((hdisc.comp (continuous_pi fun k => hM.comp (continuous_apply k))).measurable.comp
    (Measurable.of_eval fun k => measurable_fderiv ℝ _))

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem exists_lift_family {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).Finite) :
    ∃ (B : ℕ → Set (Fin e → ℂ)) (γ : ℕ → (Fin e → ℂ) → (Σ k, ι k) → ℂ),
      (∀ m, IsOpen (B m)) ∧
      (∀ m, ∀ y ∈ B m, DifferentiableAt ℂ (γ m) y ∧ γ m y ∈ mcPts P ∧
        Ψ (segre (γ m y)) = Fin.cons 1 y) ∧
      ∀ y w γ', IsSheet P Ψ y w γ' → ∃ m, y ∈ B m ∧ segre (γ m y) = w := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  have hρ : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  let Bl : D × ℕ → Set (Fin e → ℂ) := fun p => ball (p.1 : Fin e → ℂ) (1 / (p.2 + 1))
  have : Countable D := hDc.to_subtype
  have : ∀ p : D × ℕ, Countable (secSet P Ψ (Bl p)) := fun p =>
    (secSet_finite osgood hfin (p.1 : Fin e → ℂ) (hρ p.2)).countable.to_subtype
  let T := Σ p : D × ℕ, secSet P Ψ (Bl p)
  let Lift : T → ((Fin e → ℂ) → (Σ k, ι k) → ℂ) → Prop := fun t γ =>
    ∀ y ∈ Bl t.1, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧
      segre (γ y) = (t.2 : (Fin e → ℂ) → ((k : K) → ι k) → ℂ) y
  let Bo : Option T → Set (Fin e → ℂ) := fun o =>
    o.elim ∅ fun t => if ∃ γ, Lift t γ then Bl t.1 else ∅
  let γo : Option T → (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun o =>
    o.elim (fun _ _ => 0) fun t => if h : ∃ γ, Lift t γ then h.choose else fun _ _ => 0
  obtain ⟨f, hf⟩ := exists_surjective_nat (Option T)
  have hBsome : ∀ t : T, Bo (some t) = if ∃ γ, Lift t γ then Bl t.1 else ∅ := fun t => rfl
  have hγsome : ∀ t : T, (h : ∃ γ, Lift t γ) → γo (some t) = h.choose := fun t h => by
    show (if h : ∃ γ, Lift t γ then h.choose else fun _ _ => 0) = _
    rw [dite_eq_left h]
  have hBo : ∀ o, IsOpen (Bo o) := by
    rintro (_ | t)
    · exact isOpen_empty
    · rw [hBsome]
      split_ifs
      · exact isOpen_ball
      · exact isOpen_empty
  have hlift : ∀ o, ∀ y ∈ Bo o, DifferentiableAt ℂ (γo o) y ∧ γo o y ∈ mcPts P ∧
      Ψ (segre (γo o y)) = Fin.cons 1 y := by
    rintro (_ | t) y hy
    · exact absurd hy (Set.notMem_empty y)
    · rw [hBsome] at hy
      split_ifs at hy with h
      · rw [hγsome t h]
        obtain ⟨h1, h2, h3⟩ := h.choose_spec y hy
        refine ⟨h1, h2, ?_⟩
        obtain ⟨-, -, hfib⟩ := t.2.2
        obtain ⟨z, -, -, hΨ⟩ := hfib y hy
        rw [h3, hΨ]
      · exact absurd hy (Set.notMem_empty y)
  refine ⟨fun m => Bo (f m), fun m => γo (f m), fun m => hBo (f m), fun m => hlift (f m),
    fun y w γ' hγ' => ?_⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hγ'.2
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨d, hdy, hdD⟩ := Metric.dense_iff.mp hDd y _ (hρ n)
    let p : D × ℕ := (⟨d, hdD⟩, n)
    have hyB : y ∈ Bl p := by
      show y ∈ ball d (1 / ((n : ℝ) + 1))
      rw [mem_ball, dist_comm]
      exact hdy
    have hBsub : Bl p ⊆ ball y ε := by
      intro y' hy'
      have hy'' : dist y' d < 1 / ((n : ℝ) + 1) := hy'
      rw [mem_ball] at hdy ⊢
      calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
        _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_lt_add hy'' hdy
        _ < ε := by linarith
    have hG := mem_secSet_of_sheet (P := P) (Ψ := Ψ) (B := Bl p) (γ := γ') fun y' hy' =>
      hball y' (hBsub hy')
    let t : T := ⟨p, _, hG⟩
    have hL : ∃ γ, Lift t γ := ⟨γ', fun y' hy' => ⟨(hball y' (hBsub hy')).1,
      (hball y' (hBsub hy')).2.1, by simp only [t]; rw [Set.indicator_of_mem hy']⟩⟩
    obtain ⟨m, hm⟩ := hf (some t)
    refine ⟨m, ?_, ?_⟩
    · show y ∈ Bo (f m)
      rw [hm, hBsome, if_pos hL]
      exact hyB
    · show segre (γo (f m) y) = w
      rw [hm, hγsome t hL, (hL.choose_spec y hyB).2.2]
      simp only [t]
      rw [Set.indicator_of_mem hyB, hγ'.1]

end PtsSumMeasurable

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableWeightA
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem PtsSumMeasurableWeight.aestronglyMeasurable_fibreSum_of_lifts
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (F : ℝ → ℝ)
    (hF : Measurable F) (hF0 : F 0 = 0) (hfin : ∀ y, (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).Finite)
    (B : ℕ → Set (Fin e → ℂ)) (γ : ℕ → (Fin e → ℂ) → (Σ k, ι k) → ℂ) (hBo : ∀ m, IsOpen (B m))
    (hlift : ∀ m, ∀ y ∈ B m, DifferentiableAt ℂ (γ m) y ∧ γ m y ∈ mcPts P ∧
      Ψ (segre (γ m y)) = Fin.cons 1 y)
    (hcov : ∀ y w γ', IsSheet P Ψ y w γ' → ∃ m, y ∈ B m ∧ segre (γ m y) = w)
    (dens : ℕ → (Fin e → ℂ) → ℝ) (hdm : ∀ m, Measurable (dens m))
    (hdens : ∀ m, ∀ y ∈ B m, dens m y = g (γ m y) * maDensity (fun j y' => φ j (γ m y')) y)
    (hind : ∀ᵐ y, ∀ w γ₁ γ₂, IsSheet P Ψ y w γ₁ → IsSheet P Ψ y w γ₂ →
      g (γ₁ y) * maDensity (fun j y' => φ j (γ₁ y')) y =
        g (γ₂ y) * maDensity (fun j y' => φ j (γ₂ y')) y) :
    AEStronglyMeasurable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, F (sheetDensity P Ψ φ g y w)) volume := by
  classical
  have hsheet : ∀ m, ∀ y ∈ B m, IsSheet P Ψ y (segre (γ m y)) (γ m) := fun m y hy =>
    ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _

  set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m =>
    (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef
  have hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y) := fun m y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hσm : ∀ m, Measurable (σ m) := fun m =>
    (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet

  set S : ℕ → Set (Fin e → ℂ) := fun m =>
    {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hSdef
  have hSm : ∀ m, MeasurableSet (S m) := by
    intro m
    have : S m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ := by
      ext y
      simp [hSdef, imp_iff_not_or]
    rw [this]
    exact (hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ =>
      ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)
  set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (S m).indicator (fun y => F (dens m y)) with hfdef
  have hfm : ∀ m, Measurable (f m) := fun m => (hF.comp (hdm m)).indicator (hSm m)
  have hf0 : ∀ m y, y ∉ S m → f m y = 0 := fun m y hm => by
    simp only [hfdef]
    exact Set.indicator_of_notMem hm _
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y)
    (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_
  filter_upwards [hind] with y hy

  have hterm : ∀ m, y ∈ S m → f m y = F (sheetDensity P Ψ φ g y (σ m y)) := by
    intro m hm
    have hsh := hsheet m y hm.1
    rw [← hσB m y hm.1] at hsh
    have hex : ∃ γ', IsSheet P Ψ y (σ m y) γ' := ⟨_, hsh⟩
    have hfv : f m y = F (dens m y) := by
      simp only [hfdef]
      exact Set.indicator_of_mem hm _
    rw [hfv, hdens m y hm.1]
    unfold sheetDensity
    rw [dite_eq_left hex]
    exact congrArg F (hy _ _ _ hex.choose_spec hsh).symm
  have hmemF : ∀ m, y ∈ S m → σ m y ∈ (hfin y).toFinset := by
    intro m hm
    rw [Set.Finite.mem_toFinset, hσB m y hm.1]
    exact ⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩
  have hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y := by
    intro m
    rw [Finset.sum_ite_eq]
    by_cases hm : y ∈ S m
    · rw [if_pos (hmemF m hm)]
    · split_ifs
      · rfl
      · rw [hf0 m y hm]
  have hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop,
      F (sheetDensity P Ψ φ g y w) = ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0 := by
    intro w _
    by_cases hex : ∃ γ', IsSheet P Ψ y w γ'
    · obtain ⟨γ', hγ'⟩ := hex
      have hP' : ∃ m, y ∈ B m ∧ σ m y = w := by
        obtain ⟨m, hm, hmw⟩ := hcov y w γ' hγ'
        exact ⟨m, hm, (hσB m y hm).trans hmw⟩
      obtain ⟨hm1B, hm1w⟩ := Nat.find_spec hP'
      have hm1S : y ∈ S (Nat.find hP') :=
        ⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩
      filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN
      rw [Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w,
        hterm _ hm1S, hm1w]
      intro m _ hne
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · exfalso
          have hle : Nat.find hP' ≤ m := Nat.find_min' hP' ⟨hmS.1, hmw⟩
          exact hmS.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩
        · exact hf0 m y hmS
      · rfl
    · have h0 : sheetDensity P Ψ φ g y w = 0 := by
        unfold sheetDensity
        rw [dite_eq_right hex]
      refine Eventually.of_forall fun N => ?_
      rw [h0, hF0]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · have hsh := hsheet m y hmS.1
          rw [← hσB m y hmS.1, hmw] at hsh
          exact absurd ⟨_, hsh⟩ hex
        · exact hf0 m y hmS
      · rfl
  have hsum : ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, F (sheetDensity P Ψ φ g y w) =
      ∑ w ∈ (hfin y).toFinset, F (sheetDensity P Ψ φ g y w) :=
    finsum_mem_eq_finite_toFinset_sum _ (hfin y)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => hfy m

end GroundTheory.Heights₂.Heights
end
end

