module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def killBlocks (S : Set K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval fun p => if p.1 ∈ S then 0 else X p


open Classical in
theorem killBlocks_X (S : Set K) (p : Σ k, ι k) :
    killBlocks S (X p : MRing ι) = if p.1 ∈ S then 0 else X p := by
  rw [killBlocks, aeval_X]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_monomial_of_forall (S : Set K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ)
    (h : ∀ p ∈ m.support, p.1 ∉ S) : killBlocks S (monomial m c : MRing ι) = monomial m c := by
  rw [killBlocks, aeval_monomial, monomial_eq, algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun p hp => ?_
  rw [if_neg (h p hp)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_monomial_of_mem (S : Set K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (p : Σ k, ι k)
    (hp : p ∈ m.support) (hS : p.1 ∈ S) : killBlocks S (monomial m c : MRing ι) = 0 := by
  rw [killBlocks, aeval_monomial, Finsupp.prod]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hp ?_)
  rw [if_pos hS, zero_pow (Finsupp.mem_support_iff.mp hp)]

theorem killBlocks_of_isMultiHomog (S : Set K) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    killBlocks S f = f ∨ killBlocks S f = 0 := by
  by_cases ha : ∀ k ∈ S, a k = 0
  · left
    set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => killBlocks_monomial_of_forall S m _ ?_
    rintro ⟨k, i⟩ hp hkS
    have h1 := hf m hm k
    rw [ha k hkS] at h1
    have h2 : m ⟨k, i⟩ ≤ ∑ j, m ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => m ⟨k, j⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Finsupp.mem_support_iff.mp hp (by omega)
  · right
    push Not at ha
    obtain ⟨k, hkS, hak⟩ := ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    have h1 := hf m hm k
    obtain ⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by
      by_contra h0
      push Not at h0
      have : ∑ j, m ⟨k, j⟩ = 0 := Finset.sum_eq_zero fun j _ => h0 j
      omega
    exact killBlocks_monomial_of_mem S m _ ⟨k, i⟩ (Finsupp.mem_support_iff.mpr hi) hkS

theorem le_comap_killBlocks {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (S : Set K) :
    P ≤ P.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hP
  refine Ideal.span_le.mpr fun f hf => ?_
  obtain ⟨a, ha⟩ := hT f hf
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases killBlocks_of_isMultiHomog S ha with h | h <;> rw [h]
  · exact Ideal.subset_span hf
  · exact Ideal.zero_mem _


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_comp {S S' : Set K} (h : S ⊆ S') :
    (killBlocks S').comp (killBlocks S) = (killBlocks S' : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  simp only [AlgHom.comp_apply, killBlocks, aeval_X]
  by_cases hp : p.1 ∈ S
  · simp [hp, h hp]
  · simp [hp, killBlocks, aeval_X]

theorem comap_killBlocks_mono {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {S S' : Set K}
    (h : S ⊆ S') : P.comap (killBlocks S) ≤ P.comap (killBlocks S') := by
  intro f hf
  rw [Ideal.mem_comap] at hf ⊢
  have e : killBlocks S' f = killBlocks S' (killBlocks S f) := by
    rw [← AlgHom.comp_apply, killBlocks_comp h]
  rw [e]
  exact le_comap_killBlocks hP S' hf

theorem arithVarZero : ReciprocityTheory.ChartRestriction.G.AI.I2.ArithVarZeroStatement := by
  intro K _ ι _ P hP
  obtain ⟨_, ⟨hPp, hPh, hPr⟩, hhor, hdim⟩ := hP
  have := hPp
  set m := Fintype.card K with hm
  let e : K ≃ Fin m := Fintype.equivFin K
  let S : ℕ → Set K := fun n => {k | (e k : ℕ) < n}
  let Q : ℕ → Ideal (MRing ι) := fun n => P.comap (killBlocks (S n))
  let Q2 : Ideal (MRing ι) :=
    RingHom.ker ((Int.castRingHom (ZMod 2)).comp (constantCoeff : MRing ι →+* ℤ))
  have hQp : ∀ n, (Q n).IsPrime := fun n => Ideal.IsPrime.comap _
  have hQ2p : Q2.IsPrime := RingHom.ker_isPrime _
  have hstep : ∀ n, n < m → Q n < Q (n + 1) := by
    intro n hn
    obtain ⟨i, hi⟩ := hPr (e.symm ⟨n, hn⟩)
    refine SetLike.lt_iff_le_and_exists.mpr
      ⟨comap_killBlocks_mono hPh fun k hk => Nat.lt_succ_of_lt hk, X ⟨e.symm ⟨n, hn⟩, i⟩, ?_, ?_⟩
    · show killBlocks _ _ ∈ P
      rw [killBlocks_X, if_pos (by simp [S])]
      exact P.zero_mem
    · intro h2
      change killBlocks _ _ ∈ P at h2
      rw [killBlocks_X, if_neg (by simp [S])] at h2
      exact hi h2
  have hall : ∀ f : MRing ι, killBlocks (S m) f = C (constantCoeff f) := by
    intro f
    have : killBlocks (S m) = aeval (0 : (Σ k, ι k) → MRing ι) := by
      refine MvPolynomial.algHom_ext fun p => ?_
      rw [killBlocks_X, if_pos (by simp [S]), aeval_X]
      rfl
    rw [this, aeval_zero, algebraMap_eq]
  have hQm : ∀ f, f ∈ Q m ↔ constantCoeff f = 0 := by
    intro f
    change killBlocks (S m) f ∈ P ↔ _
    rw [hall]
    change constantCoeff f ∈ P.comap (C : ℤ →+* MRing ι) ↔ _
    rw [hhor, Ideal.mem_bot]
  have hstep2 : Q m < Q2 := by
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun f hf => ?_, C 2, ?_, fun h2 => ?_⟩
    · rw [RingHom.mem_ker, RingHom.comp_apply, (hQm f).mp hf, map_zero]
    · rw [RingHom.mem_ker, RingHom.comp_apply, constantCoeff_C]
      rfl
    · have := (hQm _).mp h2
      rw [constantCoeff_C] at this
      norm_num at this
  let T : ℕ → Ideal (MRing ι) := fun n => if n ≤ m then Q n else Q2
  have hTp : ∀ n, (T n).IsPrime := by
    intro n
    dsimp only [T]
    split_ifs
    exacts [hQp n, hQ2p]
  have hPT : ∀ n, P ≤ T n := by
    intro n
    dsimp only [T]
    split_ifs
    · exact le_comap_killBlocks hPh _
    · exact (le_comap_killBlocks hPh _).trans hstep2.le
  have hTlt : ∀ n, n ≤ m → T n < T (n + 1) := by
    intro n hn
    dsimp only [T]
    rw [if_pos hn]
    rcases hn.lt_or_eq with h | h
    · rw [if_pos (Nat.succ_le_of_lt h)]
      exact hstep n h
    · rw [if_neg (by omega), h]
      exact hstep2
  let g : Fin (m + 2) → PrimeSpectrum.zeroLocus (R := MRing ι) (P : Set (MRing ι)) :=
    fun j => ⟨⟨T j, hTp j⟩, hPT j⟩
  have hg : StrictMono g := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    exact hTlt i (Nat.lt_succ_iff.mp i.isLt)
  have hlen := Order.LTSeries.length_le_krullDim (LTSeries.mk (m + 1) g hg)
  rw [← ringKrullDim_quotient, hdim] at hlen
  have h3 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 + m : ℕ) : WithBot ℕ∞) := hlen
  have h4 : m + 1 ≤ 0 + m := by exact_mod_cast h3
  omega

end GroundTheory.Heights₂.Heights.Inter

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem pointFormRank_holds.exists_surj_coords {σ : Type*} {n : ℕ} (ℓ : σ → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ x, (∀ s, ℓ s x = 0) → x = 0) :
    ∀ m, m ≤ n → ∃ q : Fin m → σ, Function.Surjective (fun x : Fin n → ℂ => fun j => ℓ (q j) x) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨Fin.elim0, fun t => ⟨0, funext fun j => j.elim0⟩⟩
  | succ m ih =>
    intro hm
    obtain ⟨q, hq⟩ := ih (by omega)
    let Φ : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi fun j => ℓ (q j)
    have hrank := LinearMap.finrank_range_add_finrank_ker Φ
    have hle : Module.finrank ℂ (LinearMap.range Φ) ≤ m := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    have hpos : 0 < Module.finrank ℂ (LinearMap.ker Φ) := by
      rw [Module.finrank_fin_fun] at hrank; omega
    obtain ⟨⟨x, hxk⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hΦx : ∀ j, ℓ (q j) x = 0 := fun j => congr_fun (LinearMap.mem_ker.mp hxk) j
    obtain ⟨s, hs⟩ : ∃ s, ℓ s x ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (hℓ x h)
    refine ⟨Fin.snoc q s, fun t => ?_⟩
    obtain ⟨x0, hx0'⟩ := hq (Fin.init t)
    refine ⟨x0 + ((t (Fin.last m) - ℓ s x0) / ℓ s x) • x, funext fun j => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, map_add (f := _), map_smul, smul_eq_mul]
      rw [div_mul_cancel₀ _ hs]
      ring
    · simp only [Fin.snoc_castSucc, map_add (f := _), map_smul, hΦx, smul_eq_mul, mul_zero, add_zero]
      exact congr_fun hx0' j

theorem pointFormRank_holds.eq_zero_of_eventually_eval {d : ℕ} (f : MvPolynomial (Fin d) ℂ) (a : Fin d → ℂ)
    (h : ∀ᶠ z in 𝓝 a, eval z f = 0) : f = 0 := by
  have han : AnalyticOnNhd ℂ (fun z => eval z f) Set.univ := AnalyticOnNhd.eval_mvPolynomial f
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
  exact MvPolynomial.funext fun z => by simpa using h0 (Set.mem_univ z)

theorem pointFormRank_holds.proof (hA : RatioAlgDep.Statement) : pointFormRank_holds.Statement := by
  intro K _ ι _ Q d n F y hQ hdn hF hev
  classical
  have hy : F y ∈ mcPts Q := hev.self_of_nhds
  choose c hc using hy.1
  have hcomp : ∀ p, AnalyticAt ℂ (fun y' => F y' p) y := analyticAt_pi_iff.mp hF
  have hDy : ∀ p : Σ k, ι k, F y ⟨p.1, c p.1⟩ ≠ 0 := fun p => hc p.1
  set r : (Σ k, ι k) → (Fin n → ℂ) → ℂ := fun p y' => F y' p / F y' ⟨p.1, c p.1⟩ with hr_def
  have hr : ∀ p, AnalyticAt ℂ (r p) y := fun p => (hcomp p).div (hcomp _) (hDy p)
  have hnear : ∀ᶠ y' in 𝓝 y, ∀ k, F y' ⟨k, c k⟩ ≠ 0 :=
    Filter.eventually_all.mpr fun k => (hcomp ⟨k, c k⟩).continuousAt.eventually_ne (hc k)
  set F' := fderiv ℂ F y with hF'_def
  have hF' : HasFDerivAt F F' y := hF.differentiableAt.hasFDerivAt
  set ℓ : (Σ k, ι k) → (Fin n → ℂ) →L[ℂ] ℂ := fun p => fderiv ℂ (r p) y with hℓ_def
  have hℓ : ∀ p, HasFDerivAt (r p) (ℓ p) y := fun p => (hr p).differentiableAt.hasFDerivAt
  have hprod : ∀ p, HasFDerivAt (fun y' => r p y' * F y' ⟨p.1, c p.1⟩)
      (r p y • (ContinuousLinearMap.proj ⟨p.1, c p.1⟩).comp F' + F y ⟨p.1, c p.1⟩ • ℓ p) y :=
    fun p => (hℓ p).mul (hasFDerivAt_pi'.mp hF' _)
  have heq : ∀ p, (fun y' => F y' p) =ᶠ[𝓝 y] fun y' => r p y' * F y' ⟨p.1, c p.1⟩ :=
    fun p => hnear.mono fun y' hy' => (div_mul_cancel₀ _ (hy' p.1)).symm
  have hderiv : ∀ p, (ContinuousLinearMap.proj p).comp F' =
      r p y • (ContinuousLinearMap.proj ⟨p.1, c p.1⟩).comp F' + F y ⟨p.1, c p.1⟩ • ℓ p :=
    fun p => (hasFDerivAt_pi'.mp hF' p).unique ((hprod p).congr_of_eventuallyEq (heq p))
  by_contra hno
  push Not at hno
  have hinj : ∀ x, (∀ p, ℓ p x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    refine hno x hx0 (fun k => F' x ⟨k, c k⟩ / F y ⟨k, c k⟩) ?_
    funext p
    have h1 := congrArg (fun L => L x) (hderiv p)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, FunLike.coe_add, Pi.add_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hx p, mul_zero, add_zero] at h1
    rw [h1, bsmul, hr_def]
    ring
  obtain ⟨q, hq⟩ := pointFormRank_holds.exists_surj_coords (fun p => (ℓ p).toLinearMap)
    (fun x hx => hinj x (by simpa using hx)) d hdn
  have hg : HasStrictFDerivAt (fun y' j => r (q j) y') (ContinuousLinearMap.pi fun j => ℓ (q j)) y :=
    hasStrictFDerivAt_pi.mpr fun j => (hr (q j)).hasStrictFDerivAt
  have hrange : (ContinuousLinearMap.pi fun j => ℓ (q j) : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)).range = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun t => ?_
    obtain ⟨x, hx⟩ := hq t
    exact ⟨x, hx⟩
  have hmap := hg.map_nhds_eq_of_surj hrange
  obtain ⟨f, hf0, hfz⟩ := hA K ι Q d c q hQ
  have hev' : ∀ᶠ y' in 𝓝 y, eval (fun j => r (q j) y') (map (Int.castRingHom ℂ) f) = 0 := by
    filter_upwards [hev, hnear] with y' hy' hy'c
    exact hfz (F y') hy'.2 hy'c
  have hz : ∀ᶠ z in 𝓝 ((fun y' j => r (q j) y') y), eval z (map (Int.castRingHom ℂ) f) = 0 := by
    rw [← hmap]
    exact Filter.eventually_map.mpr hev'
  have h0 := pointFormRank_holds.eq_zero_of_eventually_eval _ _ hz
  exact hf0 (MvPolynomial.map_injective _ (Int.castRingHom ℂ).injective_int (h0.trans (map_zero _).symm))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Gen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_comp_X {σ A B : Type} [CommRing A] [CommRing B] {_ : Algebra ℤ B}
    (φ : MvPolynomial σ ℤ →+* A) (e : A →+* B) (f : MvPolynomial σ ℤ) :
    aeval (fun q => e (φ (X q))) f = e (φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (eq_intCast (algebraMap ℤ B) a).trans (eq_intCast ((e.comp φ).comp C) a).symm
  | add p q hp hq => rw [map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p q hp => rw [map_mul, hp, aeval_X, map_mul, map_mul]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_genPt (P : Ideal (MRing ι)) {_ : Algebra ℤ (FnField P)} (f : MRing ι) :
    aeval (genPt P) f = algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f) :=
  aeval_comp_X (Ideal.Quotient.mk P) (algebraMap (MRing ι ⧸ P) (FnField P)) f


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ker_algebraMap_comp_mk (P : Ideal (MRing ι)) :
    RingHom.ker ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) = P := by
  rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (MRing ι ⧸ P) (FnField P)), Ideal.mk_ker]

end Gen

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

def pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) : Fin (a + 1) → Fin n :=
  fun c => if h : (c : ℕ) < a then ⟨c, by have := a.2; omega⟩ else b

def pivotMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) : R :=
  (M.submatrix (Fin.castLE (by have := a.2; omega)) (pivotCols a b)).det

def leadMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) : R :=
  pivotMinor M a (Fin.castLE (Nat.sub_le n 1) a)

def pivotMatrix {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun r b => if h : (r : ℕ) < n - 1 then pivotMinor M ⟨r, h⟩ b else 0

theorem pivotCols_strictMono {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    StrictMono (pivotCols a b) := by
  intro c d hcd
  have hcd' : (c : ℕ) < d := hcd
  simp only [pivotCols]
  split_ifs with h1 h2 h2
  · exact Fin.mk_lt_mk.mpr hcd'
  · exact Fin.mk_lt_mk.mpr (by omega)
  · omega
  · omega

theorem card_image_pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    (Finset.univ.image (pivotCols a b)).card = a + 1 := by
  rw [Finset.card_image_of_injective _ (pivotCols_strictMono a b hab).injective, Finset.card_univ, Fintype.card_fin]

theorem pivotMinor_eq_flagMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hab : (a : ℕ) ≤ b) :
    pivotMinor M a b = flagMinor M a ⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩ := by
  unfold pivotMinor flagMinor
  congr 2
  exact (Finset.orderEmbOfFin_unique (card_image_pivotCols a b hab) (fun c => Finset.mem_image_of_mem _ (Finset.mem_univ c))
    (pivotCols_strictMono a b hab))

theorem pivotMinor_eq_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hba : (b : ℕ) < a) : pivotMinor M a b = 0 := by
  unfold pivotMinor
  refine Matrix.det_zero_of_column_eq (i := ⟨b, by omega⟩) (j := Fin.last a) (fun h => by
    have := congrArg Fin.val h; simp at this; omega) fun k => ?_
  simp [pivotCols, hba]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem regularityLocalDimension_holds.proof (hF : LocRingFrac.Statement) (hL : LocRingLocal.Statement) (hN : LocRingNoeth.Statement)
    (hPw : LocRingPow.Statement) : regularityLocalDimension_holds.Statement := by
  intro K _ ι _ P s a W hP hs hsP hW
  have hPp : P.IsPrime := hP.2.1.1
  have := hPp
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨hloc, hunit⟩ := hL K ι P W hPp hWp hPW
  have hnoeth := hN K ι P W hPp hWp hPW hW.2
  have := hloc
  have := hnoeth
  refine ⟨hloc, hnoeth, ?_⟩
  choose c hc using hW.2
  have ht : IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) a := AvoidRing.isMultiHomog_coordProd c a
  have htW : (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) ∉ W := AvoidRing.coordProd_not_mem hWp c hc a
  have htP : Ideal.Quotient.mk P (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => htW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  set xF := IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ⟨_, htP⟩ with hxF
  have hxmem : xF ∈ locRing P W := Subring.subset_closure ⟨s, _, a, htP, htW, hs, ht, rfl⟩
  have hxt : xF * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))
      (Ideal.Quotient.mk P (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) :=
    IsLocalization.mk'_spec _ _ _
  set x : locRing P W := ⟨xF, hxmem⟩
  have hx0 : x ≠ 0 := by
    intro h
    have h' : xF = 0 := congrArg Subtype.val h
    rw [h', zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hxt
    exact hsP hxt
  have hxu : ¬ IsUnit x := fun h => (hunit x s _ a hs ht htW hxt).mp h hsW
  have hmin : IsLocalRing.maximalIdeal (locRing P W) ∈ (Ideal.span {x}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hxu⟩, fun q hq _ y hy => ?_⟩
    obtain ⟨u, v, b, hu, hv, hvW, hyuv⟩ := hF K ι P W hPp hWp hPW y y.2
    have huW : u ∈ W := by
      by_contra h
      exact hy ((hunit y u v b hu hv hvW hyuv).mpr h)
    obtain ⟨n, z, hz, hyz⟩ :=
      hPw K ι P s _ a W xF u v b y hPp hP.2.1.2.1 hs hsP hW ht htW hxt hu hv huW hvW hyuv
    have e : y ^ n = x * ⟨z, hz⟩ := Subtype.ext (by simpa using hyz)
    have hq1 := hq.1
    exact hq1.mem_of_pow_mem n (e ▸ q.mul_mem_right _ (hq.2 (Ideal.mem_span_singleton_self x)))
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have h2 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx0) hxu
  have h3 := Ideal.height_mono hmin.1.2
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, le_antisymm h1 (h2 ▸ h3)]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherTail
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def pointForm_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d n : ℕ)
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (g : ((Σ k', ι' k') → ℂ) → ℝ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') d → d < n + 1 →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    ptsIntegral P' (fun j z => Real.log ((L' j).h z)) g = 0

end GroundTheory.Heights₂.Heights.Inter
end
end

