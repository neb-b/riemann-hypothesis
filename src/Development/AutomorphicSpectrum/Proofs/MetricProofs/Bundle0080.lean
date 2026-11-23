module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0033
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0012
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0076
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothMetricsNonnegDensity
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxTwist

theorem isSheet_bot_of_isSetSheet {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {S : Set ((Σ k, ι k) → ℂ)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hS : ∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (hγ : IsSetSheet S Ψ y w γ) : IsSheet ⊥ Ψ y w γ := by
  refine ⟨hγ.1, hγ.2.mono fun y' hy' => ⟨hy'.1, ⟨hS _ hy'.2.1, fun f hf => ?_⟩, hy'.2.2⟩⟩
  rw [Ideal.mem_bot.1 hf]
  simp

theorem exists_dominating_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
    ∃ N : Fin e → HermLine ι, (∀ j, IsSmoothHerm (N j)) ∧
      ∀ (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
        (∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) →
        (∀ (g : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z, 0 ≤ g z) → 0 ≤ setSheetDensity S Ψ (pot N) g y w) ∧
        ∀ (g g' : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z ∈ S, |g z| ≤ g' z) →
          |setSheetDensity S Ψ (pot L) g y w| ≤ 3 ^ e * setSheetDensity S Ψ (pot N) g' y w := by
  intro K _ ι _ e L hL
  classical
  choose T hTs hTp hLTp using fun j =>
    GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.proof GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.proof K ι (L j) (hL j)
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j => isSmoothHerm_tensor (hL j) (hTs j)
  refine ⟨fun j => ((L j).tensor (T j)).tensor (T j), fun j => isSmoothHerm_tensor (hLT j) (hTs j), ?_⟩
  intro S Ψ hS
  have hab : ∀ {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ},
      IsSetSheet S Ψ y w γ → |maDensity (fun j y' => pot L j (γ y')) y| ≤
        3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y :=
    fun hγ => GroundTheory.Heights₂.Heights.Inter.PointsAbsIntegrable.abs_maDensity_le hL hTs hTp hLTp
      (isSheet_bot_of_isSetSheet hS hγ)
  have hnn : ∀ {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ},
      IsSetSheet S Ψ y w γ →
        0 ≤ maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y :=
    fun hγ => nonneg_of_mul_nonneg_right ((abs_nonneg _).trans (hab hγ)) (by positivity)
  refine ⟨fun g y w hg => ?_, fun g g' y w hgg => ?_⟩
  · unfold setSheetDensity
    split_ifs with hγ
    · exact mul_nonneg (hg _) (hnn hγ.choose_spec)
    · exact le_rfl
  · unfold setSheetDensity
    by_cases hγ : ∃ γ, IsSetSheet S Ψ y w γ
    · rw [dite_eq_left hγ, dite_eq_left hγ]
      have hs := hγ.choose_spec
      have hmem : hγ.choose y ∈ S := hs.2.self_of_nhds.2.1
      have hg := hgg _ hmem
      rw [abs_mul]
      calc |g (hγ.choose y)| * |maDensity (fun j y' => pot L j (hγ.choose y')) y|
          ≤ g' (hγ.choose y) * (3 ^ e * maDensity
              (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (hγ.choose y')) y) :=
            mul_le_mul hg (hab hs) (abs_nonneg _) ((abs_nonneg _).trans hg)
        _ = 3 ^ e * (g' (hγ.choose y) * maDensity
              (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (hγ.choose y')) y) := by ring
    · rw [dite_eq_right hγ, dite_eq_right hγ]
      simp

end GlobalTheory.CompanionTheory.Ar.Pub.CxTwist
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def proj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k × ι k) → ℂ :=
  fun q => z ⟨q.1, q.2.1⟩ * starRingEnd ℂ (z ⟨q.1, q.2.2⟩) / ((∑ i, ‖z ⟨q.1, i⟩‖ ^ 2 : ℝ) : ℂ)

def Pts (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Set ((Σ k, ι k × ι k) → ℂ) :=
  proj '' conePts P

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

def rep (x : Pts P) : (Σ k, ι k) → ℂ := x.2.choose

theorem rep_mem (x : Pts P) : rep x ∈ conePts P := x.2.choose_spec.1

theorem proj_rep (x : Pts P) : proj (rep x) = x.1 := x.2.choose_spec.2


variable (P) in
def src (p : (k : K) → ι k) : Set (Pts P) := {x | ∀ k, rep x ⟨k, p k⟩ ≠ 0}


variable (P) in
def coord (p : (k : K) → ι k) (x : Pts P) : Fin (Fintype.card (Σ k, ι k)) → ℂ :=
  renPt (affCoord p (rep x))


variable (P) in
def ideal (p : (k : K) → ι k) : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  (chartIdeal P p).map (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)


open Classical in
def lift (p : (k : K) → ι k) (q : Σ k, ι k) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  if q.2 = p q.1 then 1 else X (Fintype.equivFin (Σ k, ι k) q)


variable (P) in
def bd (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  ((chartIdeal (P ⊔ D) p).map (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)).radical

theorem finite_minimalPrimes (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : I.minimalPrimes.Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing _ I


variable (P) in
def rc (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : ℕ := (finite_minimalPrimes (P ⊔ D)).toFinset.card


variable (P) in
def compIdeal (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  ((finite_minimalPrimes (P ⊔ D)).toFinset.equivFin.symm k).1


variable (P) in
def comp (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) : Set (Pts P) :=
  {x | ∀ f ∈ compIdeal P D k, eval (rep x) f = 0}

def ordAlong (Q P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (f : MvPolynomial (Σ k, ι k) ℂ) : ℕ :=
  sSup {m : ℕ | ∃ s ∉ Q, s * f ∈ Q ^ m ⊔ P}

theorem compIdeal_mem (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) :
    compIdeal P D k ∈ (P ⊔ D).minimalPrimes := by
  exact (Set.Finite.mem_toFinset _).1 ((finite_minimalPrimes (P ⊔ D)).toFinset.equivFin.symm k).2

theorem eval_lift (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) (q : Σ k, ι k) :
    eval (coord P p x) (lift p q) = affCoord p (rep x) q := by
  classical
  unfold lift
  split_ifs with h
  · obtain ⟨k, i⟩ := q
    simp only at h
    subst h
    simp [affCoord, hx k]
  · simp [coord, renPt]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FixedMemberBase
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem epsT_small (C : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → |epsT C t| ≤ 1 / 2 ∧ C * epsT C t ≤ 1 := by
  have hL : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop := by
      first | exact tendsto_inv_nhdsGT_zero | exact tendsto_inv_zero_atTop
    exact (Real.tendsto_log_atTop.comp hinv).congr fun t => by simp [one_div]
  have hq : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have he : Tendsto (fun t => epsT C t) (𝓝[>] 0) (𝓝 0) := by
    have h := (hq.comp hL).const_mul C
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    simp only [Function.comp, epsT]
    ring
  have ha : ∀ᶠ t in 𝓝[>] (0:ℝ), |epsT C t| < 1 / 2 := by
    have h := he.abs
    rw [abs_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  have hb : ∀ᶠ t in 𝓝[>] (0:ℝ), C * epsT C t < 1 := by
    have h := he.const_mul C
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨u, hu, hsub⟩ : ∃ u ∈ Set.Ioi (0:ℝ), Set.Ioc 0 u ⊆ {t | |epsT C t| < 1 / 2 ∧ C * epsT C t < 1} := by
    first | exact mem_nhdsGT_iff_exists_Ioc_subset.mp (ha.and hb) | exact mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.mp (ha.and hb)
  refine ⟨u, hu, fun t ht htu => ?_⟩
  obtain ⟨h1, h2⟩ := hsub ⟨ht, htu⟩
  exact ⟨h1.le, h2.le⟩

private theorem contDiffAt_comp_chart_symm_of_smoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (U : Set X) (f : X → ℝ) (hU : IsOpen U) (hf : A.SmoothOn U f) (j : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ U) :
    ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hU
  refine ((hf j).contDiffAt (hopen.mem_nhds ⟨hy, hyU⟩)).of_le ?_
  first | exact_mod_cast (le_top : ((2 : ℕ∞)) ≤ ⊤) | simp | decide

private theorem levi_add_mul {ι : Type} [Fintype ι] (F G : (ι → ℂ) → ℝ) (y w : ι → ℂ) (k : ℝ)
    (hF : ContDiffAt ℝ 2 F y) (hG : ContDiffAt ℝ 2 G y) :
    levi (fun z => F z + k * G z) y w = levi F y w + k * levi G y w := by
  have hF1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ F z :=
    (hF.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ G z :=
    (hG.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hD : (fderiv ℝ fun z => F z + k * G z) =ᶠ[𝓝 y] fun z => fderiv ℝ F z + k • fderiv ℝ G z := by
    filter_upwards [hF1, hG1] with z hz1 hz2
    exact (hz1.hasFDerivAt.add (hz2.hasFDerivAt.const_mul k)).fderiv
  have hF2 : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG2 : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ fun z => F z + k * G z) y =
      fderiv ℝ (fderiv ℝ F) y + k • fderiv ℝ (fderiv ℝ G) y := by
    rw [hD.fderiv_eq]
    exact (hF2.hasFDerivAt.add (hG2.hasFDerivAt.const_smul k)).fderiv
  unfold levi
  rw [h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem levi_split {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ th : LocPot X)
    (u : X → ℝ) (hΘ : IsPotential A Θ) (hth : IsPotential A th) (hu : A.Smooth u) (ε c : ℝ) (x : X)
    (j : Fin A.n) (y : Fin e → ℂ) (hy : y ∈ (A.chart j).target)
    (h1 : (A.chart j).symm y ∈ th.U x) (h2 : (A.chart j).symm y ∈ Θ.U x) (w : Fin e → ℂ) :
    levi (fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
        c * Θ.φ x ((A.chart j).symm z)) y w =
      levi ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y w +
        (c - ε) * levi (Θ.φ x ∘ (A.chart j).symm) y w := by
  have hthC := contDiffAt_comp_chart_symm_of_smoothOn A (th.U x) (th.φ x) (th.isOpen_U x) (hth.1 x) j y hy h1
  have hΘC := contDiffAt_comp_chart_symm_of_smoothOn A (Θ.U x) (Θ.φ x) (Θ.isOpen_U x) (hΘ.1 x) j y hy h2
  have huC := contDiffAt_comp_chart_symm_of_smoothOn A Set.univ u isOpen_univ hu j y hy trivial
  have hPC : ContDiffAt ℝ 2 ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y :=
    (hthC.add huC).add (contDiffAt_const.mul hΘC)
  rw [← levi_add_mul _ _ y w (c - ε) hPC hΘC]
  congr 1
  funext z
  show _ = th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) + ε * Θ.φ x ((A.chart j).symm z) +
    (c - ε) * Θ.φ x ((A.chart j).symm z)
  ring

private theorem levi_sub_const' {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (a : ℝ) (y w : ι → ℂ) :
    levi (fun z => g z - a) y w = levi g y w := by
  have h : fderiv ℝ (fun z => g z - a) = fderiv ℝ g := by
    funext z
    by_cases hg : DifferentiableAt ℝ g z
    · exact (hg.hasFDerivAt.sub_const a).fderiv
    · have hg' : ¬ DifferentiableAt ℝ (fun z => g z - a) z := fun h => hg (by simpa using h.add_const a)
      rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hg']
  unfold levi
  rw [h]

private theorem levi_zero' {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (y : ι → ℂ) : levi g y 0 = 0 := by
  unfold levi
  simp

theorem isPsh_of_le {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (ε c a : ℝ) (hεc : ε ≤ c)
    (hP : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) (Q : LocPot X)
    (hU : ∀ x, Q.U x ⊆ th.U x ∩ Θ.U x)
    (hφ : ∀ x z, Q.φ x z = th.φ x z + u z + c * Θ.φ x z - a) : IsPsh A Q := by
  intro x j y hy w
  obtain ⟨hyt, hyQ⟩ := hy
  have hsub := hU x hyQ
  have hfun : Q.φ x ∘ (A.chart j).symm = fun z => (th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z)) - a := by
    funext z
    simp only [Function.comp_apply, hφ]
  rw [hfun, levi_sub_const' (fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z)) a y w,
    levi_split A Θ th u hΘ hth hu ε c x j y hyt hsub.1 hsub.2 w]
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (th + LocPot.ofFun u + Θ.rsmul ε).U x := by
    refine ⟨hyt, ?_⟩
    show (A.chart j).symm y ∈ th.U x ∩ Set.univ ∩ Θ.U x
    exact ⟨⟨hsub.1, trivial⟩, hsub.2⟩
  have hPs := hP x j y hmem w
  rcases eq_or_ne w 0 with rfl | hw
  · simp [levi_zero']
  · have hΘp := hpos x j y ⟨hyt, hsub.2⟩ w hw
    have hce : 0 ≤ c - ε := sub_nonneg.mpr hεc
    nlinarith

theorem isPosPot_of_lt {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (ε c : ℝ) (hεc : ε < c)
    (hP : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) (Q : LocPot X)
    (hU : ∀ x, Q.U x ⊆ th.U x ∩ Θ.U x)
    (hφ : ∀ x z, Q.φ x z = th.φ x z + u z + c * Θ.φ x z) : IsPosPot A Q := by
  intro x j y hy w hw
  obtain ⟨hyt, hyQ⟩ := hy
  have hsub := hU x hyQ
  have hfun : Q.φ x ∘ (A.chart j).symm = fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z) := by
    funext z
    simp only [Function.comp_apply, hφ]
  rw [hfun, levi_split A Θ th u hΘ hth hu ε c x j y hyt hsub.1 hsub.2 w]
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (th + LocPot.ofFun u + Θ.rsmul ε).U x := by
    refine ⟨hyt, ?_⟩
    show (A.chart j).symm y ∈ th.U x ∩ Set.univ ∩ Θ.U x
    exact ⟨⟨hsub.1, trivial⟩, hsub.2⟩
  have hPs := hP x j y hmem w
  have hΘp := hpos x j y ⟨hyt, hsub.2⟩ w hw
  have hce : 0 < c - ε := sub_pos.mpr hεc
  nlinarith

private theorem isPotential_add' {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q) : IsPotential A (P + Q) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · show ContDiffOn ℝ _ (fun z => P.φ x ((A.chart j).symm z) + Q.φ x ((A.chart j).symm z))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x))
    exact ((hP.1 x j).mono fun z (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x)) =>
      ⟨hz.1, hz.2.1⟩).add ((hQ.1 x j).mono fun z
        (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x)) => ⟨hz.1, hz.2.2⟩)
  · obtain ⟨⟨hPx, hQx⟩, hPx', hQx'⟩ := hy
    obtain ⟨W1, hW1o, hyW1, G1, hG1, hd1⟩ := hP.2 x x' y ⟨hPx, hPx'⟩
    obtain ⟨W2, hW2o, hyW2, G2, hG2, hd2⟩ := hQ.2 x x' y ⟨hQx, hQx'⟩
    refine ⟨W1 ∩ W2, hW1o.inter hW2o, ⟨hyW1, hyW2⟩, fun z => G1 z + G2 z, fun j => ?_, fun z hz => ?_⟩
    · exact ((hG1 j).mono fun z (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W1 ∩ W2)) =>
        ⟨hz.1, hz.2.1⟩).add ((hG2 j).mono fun z
          (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W1 ∩ W2)) => ⟨hz.1, hz.2.2⟩)
    · obtain ⟨⟨⟨hz1, hz2⟩, hzPx, hzQx⟩, hzPx', hzQx'⟩ := hz
      have e1 := hd1 z ⟨⟨hz1, hzPx⟩, hzPx'⟩
      have e2 := hd2 z ⟨⟨hz2, hzQx⟩, hzQx'⟩
      show P.φ x z + Q.φ x z - (P.φ x' z + Q.φ x' z) = (G1 z + G2 z).re
      rw [Complex.add_re, ← e1, ← e2]
      ring

theorem fixedMember_base : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ), IsPotential A Θ → IsPosPot A Θ → (∀ y, logNormSec L s y ≤ 0) → IsSingWeight A L s th ph C₅ → IsRegFamily A Θ L s th ph phT C t₀ → ∃ t₂ : ℝ, 0 < t₂ ∧ t₂ ≤ t₀ ∧ ∀ t₁, 0 < t₁ → t₁ ≤ t₂ → IsPotential A (th + LocPot.ofFun (phT t₁) + Θ) ∧ IsPsh A (th + LocPot.ofFun (phT t₁) + Θ + Θ.rsmul (-(1 / 2))) ∧ IsPosPot A (th + LocPot.ofFun (phT t₁) + Θ) ∧ ∀ t, 0 < t → t ≤ t₁ → A.Smooth (fun y => phT t y - phT t₁ y - C * epsT C t₁) ∧ IsPsh A (th + LocPot.ofFun (phT t₁) + Θ + LocPot.ofFun (fun y => phT t y - phT t₁ y - C * epsT C t₁)) ∧ (∀ y, phT t y - phT t₁ y - C * epsT C t₁ ≤ 0) ∧ ∀ y ∉ bdry s, -(|C₅| + |C| + 1) * Real.log (rW L s y) ≤ phT t y - phT t₁ y - C * epsT C t₁ := by
  intro e X _ A Θ L s th ph phT C₅ C t₀ hΘ hpos hlog hSW hRF
  obtain ⟨a, ha, hab⟩ := epsT_small C
  obtain ⟨ht0, -, hR⟩ := hRF
  obtain ⟨hthP, -, -, hSW4⟩ := hSW
  refine ⟨min t₀ a, lt_min ht0 ha, min_le_left _ _, fun t₁ ht₁ ht₁2 => ?_⟩
  have ht₁0 : t₁ ≤ t₀ := ht₁2.trans (min_le_left _ _)
  have ht₁a : t₁ ≤ a := ht₁2.trans (min_le_right _ _)
  obtain ⟨hsm1, hC1, -, -, hpsh1, -, -, -⟩ := hR t₁ ht₁ ht₁0
  obtain ⟨he1, he1'⟩ := hab t₁ ht₁ ht₁a
  have hepsle : epsT C t₁ ≤ 1 / 2 := (le_abs_self _).trans he1
  refine ⟨isPotential_add' A _ _ (isPotential_add' A _ _ hthP (isPotential_ofFun A _ hsm1)) hΘ,
    ?_, ?_, fun t ht htt₁ => ?_⟩
  · exact isPsh_of_le A Θ th (phT t₁) hΘ hpos hthP hsm1 (epsT C t₁) (1 / 2) 0 hepsle hpsh1 _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x ∩ Θ.U x) => ⟨hz.1.1.1, hz.1.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z + -(1 / 2) * Θ.φ x z = th.φ x z + phT t₁ z + 1 / 2 * Θ.φ x z - 0
        ring)
  · exact isPosPot_of_lt A Θ th (phT t₁) hΘ hpos hthP hsm1 (epsT C t₁) 1 (by linarith) hpsh1 _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x) => ⟨hz.1.1, hz.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z = th.φ x z + phT t₁ z + 1 * Θ.φ x z
        ring)
  have htt0 : t ≤ t₀ := htt₁.trans ht₁0
  obtain ⟨hsm, -, hph, -, hpsh, -, -, hmono⟩ := hR t ht htt0
  obtain ⟨he, -⟩ := hab t ht (htt₁.trans ht₁a)
  have hepsle' : epsT C t ≤ 1 := by linarith [le_abs_self (epsT C t)]
  refine ⟨fun j => ((hsm j).sub (hsm1 j)).sub contDiffOn_const, ?_, fun y => ?_, fun y hy => ?_⟩
  · exact isPsh_of_le A Θ th (phT t) hΘ hpos hthP hsm (epsT C t) 1 (C * epsT C t₁) hepsle' hpsh _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x ∩ Set.univ) => ⟨hz.1.1.1, hz.1.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z + (phT t z - phT t₁ z - C * epsT C t₁) =
          th.φ x z + phT t z + 1 * Θ.φ x z - C * epsT C t₁
        ring)
  · have h := hmono t₁ htt₁ ht₁0 y
    linarith
  · have h1 := hph y hy
    have h2 := (hSW4 y hy).1
    have h3 := hC1 y
    have hr : Real.exp 1 ≤ rW L s y := by
      have := hlog y
      unfold rW
      linarith
    have hL : 1 ≤ Real.log (rW L s y) := by
      have h := Real.log_le_log (Real.exp_pos 1) hr
      rwa [Real.log_exp] at h
    have k1 : 0 ≤ (|C₅| - C₅) * Real.log (rW L s y) :=
      mul_nonneg (sub_nonneg.mpr (le_abs_self C₅)) (by linarith)
    have k2 : 0 ≤ (|C| + 1) * (Real.log (rW L s y) - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hL)
    have k3 := le_abs_self C
    nlinarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolution
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hcase hblk hca hcb RW q hq h0 h1 L' v cst hnorm U G ΦY ΦW hU hC
  have hC' := fun m => (isFibreChart_iff FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)).1 (hC m)
  choose l H bp hD using hC'
  refine ⟨fun m => alphaOf BM (l m) (H m) (bp m), fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_xi_potential K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_base_member K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb k₀ hblk RW q h0 h1 _ hnorm (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoordinateTieTransfer
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.FlagTie

theorem flagCoord_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ X'), CoordTie ℤ ξ' (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → CoordTie ℤ ξ' (flagCoord ((k : K₀) → J₀ k) (seg x₀) φ (cc 𝔐 bW bO)) :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_tie

end GlobalTheory.CompanionTheory.Ar.FlagTie
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeight
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flagHeight_holds : FlagHeight := PositivityTheory.Xgp.t_top_flh

end GlobalTheory.CompanionTheory.Ar.PB
end

