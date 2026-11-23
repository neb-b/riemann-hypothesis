module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithIntersectionSystem

theorem multilin_of_isFamily {I : AllFam} (hI : I.IsFamily) : IsMultilinFam I := by
  intro K _ ι _ P n L j A B hP hL hA hB
  cases n with
  | zero => exact j.elim0
  | succ m =>
    obtain ⟨hsym, hadd, -⟩ := hI K ι
    have e : ∀ X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm X →
        I K ι P (m + 1) (Function.update L j X) =
          I K ι P (m + 1)
            (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
      intro X hX
      rw [← GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.update_comp_swap]
      exact (hsym P (m + 1) _ _ hP
        (GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.smooth_update hL j hX)).symm
    rw [e _ (isSmoothHerm_tensor hA hB), e A hA, e B hB]
    exact hadd P m _ A B hP (fun i => hL _) hA hB

theorem of_found (hE : GroundTheory.Heights₂.Heights.Inter.ThmIExists.Statement) (hPF : PFCoordStatement)
    (hCM : ContractMixedStatement) : ArithIntersectionSystemStatement := by
  obtain ⟨I, hI⟩ := (hE : ExistsStatement)
  exact ⟨I, hI, multilin_of_isFamily hI, hPF I hI, hCM I hI⟩

end ArithIntersectionSystem

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

namespace BaseChangeMin

variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

section GD

attribute [local instance] MvPolynomial.algebraMvPolynomial



end GD

theorem ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro a
  obtain ⟨Z, hZ, hZa⟩ :=
    Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2)
  have : Z.IsPrime := hZ.1.1
  let z : PrimeSpectrum.zeroLocus (R := R) (I : Set R) :=
    ⟨⟨Z, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hZ.1.2⟩
  have hza : z ≤ a := hZa
  let e : Set.Ici z ↪o PrimeSpectrum.zeroLocus (R := R) (Z : Set R) :=
    OrderEmbedding.ofMapLEIff
      (fun x => ⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (show Z ≤ x.1.1.asIdeal from x.2)⟩)
      fun _ _ => Iff.rfl
  calc ((Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight z : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.coheight_anti hza)
    _ = Order.krullDim (Set.Ici z) := Order.coheight_eq_krullDim_Ici z
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) (Z : Set R)) :=
        Order.krullDim_le_of_orderEmbedding e
    _ = ringKrullDim (R ⧸ Z) := (ringKrullDim_quotient Z).symm
    _ ≤ N := h Z hZ

end BaseChangeMin

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.IsMultiHomogPlaneCoordinate
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def normSq (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) ^ 2

def regLog (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (ε : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (normSq A s z + ε) / 2

omit [∀ k, Fintype (ι k)] in
theorem normSq_nonneg (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : 0 ≤ normSq A s z :=
  sq_nonneg _

theorem normSq_smul {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    normSq A s (fun p => c p.1 * z p) = normSq A s z := by
  unfold normSq
  rw [eval_smul_of_isMultiHomog hs c z, A.smul c z hc, norm_mul, norm_prod]
  have hC : (∏ k, ‖c k‖ ^ A.a k) = ∏ k, ‖c k ^ a k‖ := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ha k, norm_pow, zpow_natCast]
  rw [hC, mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ =>
    norm_ne_zero_iff.mpr (pow_ne_zero _ (hc k)))]

def regLine (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  HermLine.ofWeight (fun z => -regLog A s ε z) fun c z hc => by
    simp only [regLog, normSq_smul ha hs c z hc]

theorem regLine_a (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : (regLine A s ε ha hs).a = 0 := rfl

theorem log_regLine (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : (fun z => Real.log ((regLine A s ε ha hs).h z)) = regLog A s ε := by
  funext z
  simp [regLine, HermLine.ofWeight, Real.log_exp]

theorem contDiff_evalC (s : MRing ι) :
    ContDiff ℝ ∞ (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) s)) := by
  induction s using MvPolynomial.induction_on with
  | C a => simpa only [map_C, eval_C] using contDiff_const
  | add p q hp hq => simpa only [map_add (f := _), eval_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, map_X, eval_mul, eval_X] using hp.mul (contDiff_apply ℝ (fun _ => ℂ) i)

theorem contDiffOn_regLog {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (s : MRing ι) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (regLog A s ε) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have hN : ContDiffOn ℝ ∞ (normSq A s) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have h1 := (((contDiff_norm_sq ℝ).comp (contDiff_evalC s)).contDiffOn (s := {z : (Σ k, ι k) → ℂ |
      ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})).div (hA.pow 2) fun z hz => pow_ne_zero _ (A.pos z hz).ne'
    exact h1.congr fun z _ => by simp only [normSq, div_pow]; rfl
  exact ((hN.add contDiffOn_const).log fun z _ =>
    (add_pos_of_nonneg_of_pos (normSq_nonneg A s z) hε).ne').div_const 2

theorem isSmoothHerm_regLine {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) {s : MRing ι} {ε : ℝ} (hε : 0 < ε)
    {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    IsSmoothHerm (regLine A s ε ha hs) :=
  Real.contDiff_exp.comp_contDiffOn (contDiffOn_regLog hA s hε).neg.neg

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartObjects
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing mcPts segre PBlk)

section Chart

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def segreChartSet (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def segreChartIdeal (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (segreChartSet P σ i)

def segreChartComponents (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Finset (Ideal (MvPolynomial (Fin m) ℂ)) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) ℂ)
    (segreChartIdeal P σ i)).toFinset

omit [∀ k, Fintype (ι k)] in
theorem mem_segreChartComponents {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} :
    J ∈ segreChartComponents P σ i ↔ J ∈ (segreChartIdeal P σ i).minimalPrimes :=
  Set.Finite.mem_toFinset _


omit [∀ k, Fintype (ι k)] in
theorem chart_coord_eq_one {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i)
    {x : Fin m → ℂ} (hx : x ∈ ComplexSets.zeroSet J) : x (σ.symm i) = 1 := by
  have hle : segreChartIdeal P σ i ≤ J := (mem_segreChartComponents.1 hJ).1.2
  have hmem : (MvPolynomial.X (σ.symm i) - 1 : MvPolynomial (Fin m) ℂ) ∈ segreChartIdeal P σ i := by
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, -, hzi, rfl⟩
    simp [hzi]
  have h := hx _ (hle hmem)
  simp only [map_sub, MvPolynomial.eval_X, map_one] at h
  exact sub_eq_zero.1 h

end Chart

section Lift

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ) :
    (Σ k, ι k) → ℂ :=
  fun p => x (σ.symm (Function.update i p.1 p.2))

theorem contDiff_chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) {n : WithTop ℕ∞} :
    ContDiff ℝ n (chartLift σ i) :=
  contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (σ.symm (Function.update i p.1 p.2))


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartLift_blockNonzero {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) : ∀ k, ∃ j, chartLift σ i x ⟨k, j⟩ ≠ 0 :=
  fun k => ⟨i k, by simp [chartLift, hx]⟩


omit [∀ k, Fintype (ι k)] in
theorem chartLift_segre_apply {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) (k : K) (j : ι k) :
    chartLift σ i (fun a => segre z (σ a)) ⟨k, j⟩ = z ⟨k, j⟩ * (z ⟨k, i k⟩)⁻¹ := by
  have hne : z ⟨k, i k⟩ ≠ 0 := fun h0 => by
    have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hz] at this
    exact one_ne_zero this
  have hupd : (fun k' => z ⟨k', Function.update i k j k'⟩) =
      Function.update (fun k' => z ⟨k', i k'⟩) k (z ⟨k, j⟩) := by
    funext k'
    by_cases h : k' = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  have hprod : segre z (Function.update i k j) = z ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i k'⟩ := by
    simp only [segre]
    rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hall : z ⟨k, i k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i k'⟩ = 1 := by
    rw [Finset.mul_prod_erase _ (fun k' => z ⟨k', i k'⟩) (Finset.mem_univ k)]
    exact hz
  simp only [chartLift, Equiv.apply_symm_apply]
  rw [hprod]
  field_simp
  linear_combination z ⟨k, j⟩ * hall

theorem segre_chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) :
    segre (chartLift σ i (fun a => segre z (σ a))) = segre z := by
  funext i'
  show ∏ k, chartLift σ i (fun a => segre z (σ a)) ⟨k, i' k⟩ = ∏ k, z ⟨k, i' k⟩
  simp only [chartLift_segre_apply σ i z hz, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have : ∏ k, z ⟨k, i k⟩ = 1 := hz
  rw [this, inv_one, mul_one]

end Lift

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsBilinear
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot PBlk oneLine
  isSmoothHerm_oneLine)

def PtsBilinear.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (T : Type) [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ)
    (v : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ t, IsDegZeroSmooth (u t)) →
    IsDegZeroSmooth v →
    ptsIntegral P (Fin.cons v (pot L)) (fun z => ∑ t, u t z) =
        ∑ t, ptsIntegral P (Fin.cons v (pot L)) (u t) ∧
      ptsIntegral P (Fin.cons (fun z => ∑ t, u t z) (pot L)) v =
        ∑ t, ptsIntegral P (Fin.cons (u t) (pot L)) v

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChart
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre PBlk oneLine
  isSmoothHerm_oneLine)

def SegreChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (u v : ((Σ k, ι k) → ℂ) → ℝ)
    (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth u → IsDegZeroSmooth v →
    0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → u z = 0) →
      ∃ (m : ℕ) (Js : Finset (Ideal (MvPolynomial (Fin m) ℂ))) (U V : (Fin m → ℂ) → ℝ)
        (Φ : Fin n → (Fin m → ℂ) → ℝ),
        (∀ J ∈ Js, J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (n + 1 : ℕ) ∧
          SmoothNear (ComplexSets.zeroSet J) U ∧ SmoothNear (ComplexSets.zeroSet J) V ∧
          ∀ j, SmoothNear (ComplexSets.zeroSet J) (Φ j)) ∧
        HasCompactSupport U ∧
        ptsIntegral P (Fin.cons v (pot L)) u = ∑ J ∈ Js, varInt J (n + 1) U (Matrix.vecCons V Φ) ∧
        ptsIntegral P (Fin.cons u (pot L)) v = ∑ J ∈ Js, varInt J (n + 1) V (Matrix.vecCons U Φ)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreCoordGoodProj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre PBlk)

def SegreCoordGoodProj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (i : (k : K) → ι k),
    IsArithVar P (e + 1) → (∃ z ∈ mcPts P, segre z i ≠ 0) →
      ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ ∧ ∀ w, Ψ w 0 = w i

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegrePartition
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (segre PBlk)

def SegrePartition.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)],
    (∀ k, Nonempty (ι k)) →
      ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ((k : K) → ι k) → ((Σ k, ι k) → ℂ) → ℝ,
        (∀ i, IsDegZeroSmooth (ρ i)) ∧ (∀ z, ∑ i, ρ i z = 1) ∧
          ∀ i z, ‖segre z i‖ < δ * ‖segre z‖ → ρ i z = 0

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsAmpleCountAlongMultiplesAmple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def AmpleCountAlongMultiples.StatementAmple : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    KH.AmpleV ℚ (KH.genIdeal y) N.a →
    (∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • N.a - fun _ => 1)) →
    (∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (GroundTheory.Heights₂.Heights.HilbertSamuel.fibreIdeal ℓ y) N.a) →
    ∀ ε : ℝ, 0 < ε → ∃ b : ℕ, 1 ≤ b ∧ ∀ᶠ k : ℕ in atTop,
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε) *
          (((b * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y N) (chartLat y N.a) (b * k)

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftCountAlongMultiples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftCountAlongMultiples.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem) (a : ℕ) (ι' : Type) [Fintype ι'] (x' : ι' → Ω),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    1 ≤ a → (∀ j, x' j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) x' →
    Birational (fun p : Σ _ : Unit, ι' => x' p.2) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ((a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε) *
          ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y N) (chartLat y N.a) (a * k)

end

end GroundTheory.Heights₂.Heights.Targets
end

