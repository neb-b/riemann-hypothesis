module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0030

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)

namespace GoodChartDim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segreCone (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, x = fun a => segre z (σ a)}

theorem segreCone_smul {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) :
    ∀ c ∈ segreCone P σ, ∀ a : ℂ, a ≠ 0 → a • c ∈ segreCone P σ := by
  rintro _ ⟨z, hz, rfl⟩ a ha
  obtain ⟨z', hz', hseg⟩ := GoodChartZeroSet.exists_segre_smul P hP.2.1.2.1 hz ha
    (fun h => absurd hP.1 (not_nonempty_iff.2 h))
  exact ⟨z', hz', funext fun b => by simp [hseg]⟩


open Classical in
def psiCoeffs {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Fin m → ℂ :=
  fun a => Ψ (fun i' => if σ a = i' then (1 : ℂ) else 0) 0

theorem projChartSet_eq (P : Ideal (MRing ι)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    projChartSet P σ Ψ = {x | x ∈ segreCone P σ ∧ eval x (linForm (psiCoeffs σ Ψ)) = 1} := by
  have hl : ∀ z : (Σ k, ι k) → ℂ,
      eval (fun a => segre z (σ a)) (linForm (psiCoeffs σ Ψ)) = Ψ (segre z) 0 := fun z => by
    rw [show linForm (psiCoeffs σ Ψ) = GoodChartZeroSet.linForm σ Ψ from rfl, GoodChartZeroSet.eval_linForm]
    simp
  ext x
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, (hl z).trans h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, (hl z).symm.trans h1, rfl⟩

theorem linForm_single' {m : ℕ} (a : Fin m) : linForm (Pi.single a (1 : ℂ)) = X a := by
  classical
  simp [linForm, Pi.single_apply]


omit [∀ k, Fintype (ι k)] in
theorem segreChartSet_eq (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (a : Fin m) :
    segreChartSet P σ (σ a) = {x | x ∈ segreCone P σ ∧ eval x (linForm (Pi.single a (1 : ℂ))) = 1} := by
  ext x
  simp only [segreChartSet, segreCone, Set.mem_ofPred_eq, linForm_single', eval_X]
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, h1, rfl⟩

theorem linForm_sub_one_not_mem {m : ℕ} {V : Ideal (MvPolynomial (Fin m) ℂ)} (hV : IsHomogIdeal V) (hne : V ≠ ⊤)
    (t : Fin m → ℂ) : linForm t - 1 ∉ V := by
  intro h
  have h0 := hV _ h 0
  rw [homogeneousComponent_zero] at h0
  have hc : AddMonoidAlgebra.coeff (linForm t - 1) 0 = -1 := by
    simp [linForm, coeff_sum, coeff_C_mul, coeff_X]
  rw [hc] at h0
  exact hne (Ideal.eq_top_of_isUnit_mem _ h0 (by simp))

theorem exists_X_not_mem {m : ℕ} {W : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ} (h : linForm t ∉ W) :
    ∃ a, X a ∉ W := by
  by_contra hall
  push Not at hall
  exact h (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hall a))

theorem le_of_homog_le_sup {m : ℕ} {V W : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ} (hV : IsHomogIdeal V)
    (hW : W.IsPrime) (hWh : IsHomogIdeal W) (ht : linForm t ∉ W) (hle : V ≤ W ⊔ Ideal.span {linForm t - 1}) :
    V ≤ W := by
  intro f hf
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ => ChartDehomog.proof ℂ m W t _ d hW hWh ht
    (homogeneousComponent_isHomogeneous d f) (hle (hV f hf d))

theorem eq_of_add_one_eq {x : WithBot ℕ∞} {e : ℕ} (h : x + 1 = (e : WithBot ℕ∞) + 1) : x = e := by
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← Nat.cast_succ] at h
    exact absurd h (WithBot.bot_ne_natCast _)
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) = ((e + 1 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_inj, top_add] at h'
      exact absurd h' (by exact_mod_cast (ENat.top_ne_natCast (e + 1)))
    | coe x =>
      have h' : ((x + 1 : ℕ) : WithBot ℕ∞) = ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h'' : x + 1 = e + 1 := by exact_mod_cast h'
      exact_mod_cast (show x = e by omega)

end GoodChartDim

open GoodChartDim

theorem GoodChartDim.proof (h₁ : ConeVanishingHomog.Statement) (h₂ : ConeSliceIdeal.Statement)
    (h₃ : ChartDehomogPrime.Statement) : GoodChartDim.Statement := by
  classical
  intro K _ ι _ P e m σ Ψ hP J hJ
  have hC := segreCone_smul hP σ
  set t := psiCoeffs σ Ψ
  have hS : projChartSet P σ Ψ = {x | x ∈ segreCone P σ ∧ eval x (linForm t) = 1} := projChartSet_eq P σ Ψ
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : projChartIdeal P σ Ψ ≤ J := hJ.1.2
  set H := vanishingIdeal ℂ (segreCone P σ)
  have hH : IsHomogIdeal H := h₁ m _ hC
  have hHI : H ≤ projChartIdeal P σ Ψ := by
    rw [projChartIdeal, hS]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  have hℓ1 : linForm t - 1 ∈ projChartIdeal P σ Ψ := by
    rw [projChartIdeal, hS, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]

  obtain ⟨W, hW, hℓW, hWJ, hWcore⟩ := ChartHomogenise.proof ℂ m J t hJp (hIJ hℓ1)
  have hHW : H ≤ W := hWcore H hH (hHI.trans hIJ)
  obtain ⟨a, ha⟩ := exists_X_not_mem hℓW
  set u : Fin m → ℂ := Pi.single a 1
  have huW : linForm u ∉ W := by rw [linForm_single']; exact ha
  have hT : segreChartSet P σ (σ a) = {x | x ∈ segreCone P σ ∧ eval x (linForm u) = 1} :=
    segreChartSet_eq P σ a

  have := h₃ ℂ m W u hW huW
  have hTJ' : segreChartIdeal P σ (σ a) ≤ W ⊔ Ideal.span {linForm u - 1} := by
    rw [segreChartIdeal, hT]; exact h₂ m _ u W hC hHW
  obtain ⟨Q₀, hQ₀, hQ₀J'⟩ := Ideal.exists_minimalPrimes_le hTJ'
  have hdimQ₀ := SegreChartDim.proof K ι P e m σ (σ a) hP Q₀ (mem_segreChartComponents.2 hQ₀)
  have hu1 : linForm u - 1 ∈ segreChartIdeal P σ (σ a) := by
    rw [segreChartIdeal, hT, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]
  have hHT : H ≤ segreChartIdeal P σ (σ a) := by
    rw [segreChartIdeal, hT]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  obtain ⟨V, hV, huV, hVQ₀, hVcore⟩ := ChartHomogenise.proof ℂ m Q₀ u hQ₀.1.1 (hQ₀.1.2 hu1)
  have hHV : H ≤ V := hVcore H hH (hHT.trans hQ₀.1.2)
  have hVW : V ≤ W := le_of_homog_le_sup hV.isHomog hW.isPrime hW.isHomog huW
    ((le_sup_left.trans hVQ₀.le).trans hQ₀J')

  have hIV : projChartIdeal P σ Ψ ≤ V ⊔ Ideal.span {linForm t - 1} := by
    rw [projChartIdeal, hS]; exact h₂ m _ t V hC hHV
  have hVJ : V ⊔ Ideal.span {linForm t - 1} ≤ J :=
    sup_le (hVW.trans (le_sup_left.trans hWJ.le)) ((Ideal.span_singleton_le_iff_mem _).2 (hIJ hℓ1))
  have hJmin : J ∈ (V ⊔ Ideal.span {linForm t - 1}).minimalPrimes :=
    ⟨⟨hJp, hVJ⟩, fun Z hZ hZJ => hJ.2 ⟨hZ.1, hIV.trans hZ.2⟩ hZJ⟩
  have hQ₀min : Q₀ ∈ (V ⊔ Ideal.span {linForm u - 1}).minimalPrimes := by
    have := hQ₀.1.1
    rw [hVQ₀, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have d₁ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V J (linForm t - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top t) hJmin
  have d₂ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V Q₀ (linForm u - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top u) hQ₀min
  rw [← d₂, hdimQ₀] at d₁
  exact eq_of_add_one_eq d₁

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralSegreChartProj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (ptsIntegralAt)
open ComplexSets

theorem PtsIntegralSegreChartProj.proof (hFin : SegreChartProjFinite.Statement)
    (hZero : SegreChartZeroSet.Statement) (hAbs : SegreChartAbsIntegrable.Statement)
    (hSum : PtsSegreChartFibreSum.Statement) : PtsIntegralSegreChartProj.Statement := by
  intro K _ _ ι _ P e m σ i L g Ψ G Φ hP hL hg hΨ hΨ0 hgerm
  set A := chartProjMatrix σ Ψ
  set G' := chartWeight σ i g with hG'
  set Φ' := chartPot σ i L
  have hcoordS : ∀ x ∈ segreChartSet P σ i, x (σ.symm i) = 1 := by
    rintro _ ⟨z, -, hzi, rfl⟩
    simpa using hzi
  have hchart : ∀ J ∈ segreChartComponents P σ i, zeroSet J ⊆ segreChartSet P σ i := by
    intro J hJ x hx
    rw [← hZero K ι P m σ i hP.2.1.2.1]
    exact fun q hq => hx q ((mem_segreChartComponents.1 hJ).1.2 hq)
  have hprime : ∀ J ∈ segreChartComponents P σ i, J.IsPrime := fun J hJ =>
    (mem_segreChartComponents.1 hJ).1.1
  have hdim : ∀ J ∈ segreChartComponents P σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) := fun J hJ =>
    SegreChartDim.proof K ι P (e + 1) m σ i hP J hJ
  have hfin : ∀ J ∈ segreChartComponents P σ i, IsFiniteProjection J A :=
    hFin K ι P (e + 1) m σ i Ψ hP hΨ hΨ0
  have hmeas : Measurable G' := measurable_chartWeight σ i hg
  have hsm : ∀ J ∈ segreChartComponents P σ i, ∀ k, SmoothNear (zeroSet J) (Φ' k) := fun J hJ =>
    smoothNear_chartPot σ i hL fun x hx => chart_coord_eq_one hJ hx
  have habs : ∀ J ∈ segreChartComponents P σ i, Integrable (chartAbsDens J A G' Φ') := fun J hJ =>
    hAbs K ι P (e + 1) m σ i L g hP hL hg J hJ A (hfin J hJ)
  have hint : ∀ J ∈ segreChartComponents P σ i, Integrable (chartDens J A G' Φ') := by
    intro J hJ
    refine (habs J hJ).mono' (SheetSumMeasurable.full m (e + 1) J A G' Φ' (hprime J hJ) (hdim J hJ)
      (hfin J hJ) hmeas (hsm J hJ)).1.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens sheetSum
    refine (abs_finsum_mem_le_finsum_mem_abs _ _).trans (le_of_eq (finsum_mem_congr rfl fun x _ => ?_))
    split_ifs <;> simp

  have hcong : ∀ J ∈ segreChartComponents P σ i, ∀ A₁ : Matrix (Fin (e + 1)) (Fin m) ℂ,
      chartDens J A₁ G Φ = chartDens J A₁ G' Φ' := by
    intro J hJ A₁
    funext y
    unfold chartDens sheetSum
    refine finsum_mem_congr rfl fun x hx => ?_
    have hxS : x ∈ segreChartSet P σ i := hchart J hJ hx.1
    split_ifs with h
    · obtain ⟨U, hU, hyU, hdiff, hsx, -, -⟩ := h.choose_spec
      have hy : A₁ *ᵥ x = y := hx.2
      have hG : G x = G' x := by
        rw [hG', chartWeight_of_coord g (hcoordS x hxS)]
        exact (hgerm x hxS).1.eq_of_nhds
      have hcont : Tendsto h.choose (𝓝 y) (𝓝 x) := by
        have := (hdiff.continuousOn.continuousAt (hU.mem_nhds hyU)).tendsto
        rwa [hsx, hy] at this
      beta_reduce
      rw [hG]
      congr 1
      exact ReciprocityTheory.AnForm.M.maDens_congr_eventuallyEq fun k => ((hgerm x hxS).2 k).comp_tendsto hcont
    · rfl

  have hvar : ∀ J ∈ segreChartComponents P σ i, varInt J (e + 1) G Φ = ∫ y, chartDens J A G' Φ' y := by
    intro J hJ
    have hex : ∃ A₁ : Matrix (Fin (e + 1)) (Fin m) ℂ, IsFiniteProjection J A₁ := ⟨A, hfin J hJ⟩
    rw [varInt, dite_eq_left hex, chartInt, hcong J hJ]
    exact (IntegralIndep.full m (e + 1) J A hex.choose G' Φ' (hprime J hJ) (hdim J hJ) (hfin J hJ)
      hex.choose_spec hmeas (hsm J hJ) (habs J hJ)).2.symm
  rw [Finset.sum_congr rfl hvar, ← integral_finsetSum _ hint]
  unfold ptsIntegralAt
  refine integral_congr_ae ?_
  filter_upwards [hSum K ι P (e + 1) m σ i L g Ψ hP hL hg hΨ hΨ0] with y hy
  exact hy

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartProjFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix

theorem homogeneousComponent_mem_leadIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  · rw [homogeneousComponent_eq_zero (n := r) (φ := f) h]
    exact zero_mem _

theorem eval_linPoly_eq_mulVec {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem SegreChartProjFinite.pow_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hΨ0 : ∀ w, Ψ w 0 = w i)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := segre_rel hP.2.1.2.1 Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine (mem_segreChartComponents.1 hJ).1.2 ?_
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hzi, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hΨ0, hzi, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, Gx, map_sub, map_add (f := _), map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
      eval_linPoly_eq_mulVec, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, map_sub, map_add (f := _), map_sum, hX, h0, zero_add,
      homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

theorem SegreChartProjFinite.proof : SegreChartProjFinite.Statement := by
  intro K _ ι _ P e m σ i Ψ hP hΨ hΨ0 J hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := SegreChartProjFinite.pow_mem hP hΨ hΨ0 hJ a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨FiniteProjHomInjective.proof m e J _ (mem_segreChartComponents.1 hJ).1.1
    (SegreChartDim.proof K ι P e m σ i hP J hJ) hfin, hfin⟩

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def CurveVertPointChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        (curvePtIdeal y W).IsMaximal ∧
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ curvePtIdeal y W ∧
          (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) ∧
        ∀ (e : K → ℕ) (g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
          (g ∈ W ↔ ∃ a b : curveRing y, a ∈ curvePtIdeal y W ∧ b ∉ curvePtIdeal y W ∧
            (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k)

def CurveVertPointInj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      Set.InjOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)

def CurveVertPointSurj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ m : Ideal (curveRing y), m.IsMaximal →
        locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0 →
          ∃ W ∈ divSupp (mCoordIdeal y) s, curvePtIdeal y W = m

def CurveVertPointMultChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        ∀ a b : curveRing y, b ∉ curvePtIdeal y W →
          (b : Ω) * aeval y s = a * ∏ k, y ⟨k, c k⟩ ^ d k →
            multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
              locLen (curvePtIdeal y W) (curveRing y ⧸ Ideal.span {a})

def CurveSectionQuotLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ (m : Ideal (curveRing y)) (c : ∀ k, ι k), m.IsPrime → (∀ k, y ⟨k, c k⟩ ≠ 0) →
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) →
        ∀ a b : curveRing y, b ∉ m → (b : Ω) * aeval y s = a * ∏ k, y ⟨k, c k⟩ ^ d k →
          locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) =
            locLen m (curveRing y ⧸ Ideal.span {a})

end

end GroundTheory.Heights₂.Heights.Targets
end

