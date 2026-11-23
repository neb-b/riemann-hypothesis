module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

namespace EuclideanSections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact mul_mem (hs c hc) (ht c hc)

theorem isBoundedH_mono {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {s : Ω}
    {c c' : ℝ} (hs : GroundTheory.Heights₂.Heights.HilbertSamuel.IsBoundedH P y A τ c s) (hc : c ≤ c') : GroundTheory.Heights₂.Heights.HilbertSamuel.IsBoundedH P y A τ c' s := by
  intro dg dh g h z hg hh hd he hz
  refine (hs dg dh g h z hg hh hd he hz).trans ?_
  have h0 : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (norm_nonneg (eval z (map (Int.castRingHom ℂ) h)))) h0

theorem eventually_shift_le (D m : ℕ) (b E δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n ≤ N → N ≤ n + m →
      b * ((N : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) + E * ((N : ℝ) + 1) ^ D ≤
        (b + δ) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF0 : 0 < F := by positivity
  have hlin : ∀ c : ℝ, (fun n : ℕ => (n : ℝ) + c) ~[atTop] fun n : ℕ => (n : ℝ) := fun c =>
    IsEquivalent.refl.add_isLittleO ((isLittleO_const_id_atTop c).comp_tendsto tendsto_natCast_atTop_atTop)
  have hu : (fun n : ℕ => ((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := (hlin m).pow (D + 1)
  have hv : (fun n : ℕ => ((n : ℝ) + (m + 1)) ^ D) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
    ((hlin (m + 1)).pow D).isBigO.trans_isLittleO
      ((isLittleO_pow_pow_atTop_of_lt (Nat.lt_succ_self D)).comp_tendsto tendsto_natCast_atTop_atTop)
  set c₁ := δ / (2 * (|b| + 1)) with hc₁
  set c₂ := δ / (2 * F * (|E| + 1)) with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hc₂0 : 0 < c₂ := by positivity
  have hbc : |b| * c₁ ≤ δ / 2 := by
    rw [hc₁, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg b]
  have hEc : F * (|E| * c₂) ≤ δ / 2 := by
    rw [hc₂, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg E]
  filter_upwards [hu.def hc₁0, hv.def hc₂0] with n h1 h2
  intro N hnN hNn
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hN1 : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hN2 : (N : ℝ) ≤ n + m := by exact_mod_cast hNn
  have hw : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1) := by positivity
  have hpow : (N : ℝ) ^ (D + 1) ≤ ((n : ℝ) + m) ^ (D + 1) := pow_le_pow_left₀ (by positivity) hN2 _
  have hpow' : (n : ℝ) ^ (D + 1) ≤ (N : ℝ) ^ (D + 1) := pow_le_pow_left₀ hn0 hN1 _
  have hv' : ((N : ℝ) + 1) ^ D ≤ ((n : ℝ) + (m + 1)) ^ D := pow_le_pow_left₀ (by positivity) (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg (by linarith)] at h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg (by positivity)] at h2
  have hb : b * (N : ℝ) ^ (D + 1) ≤
      b * (n : ℝ) ^ (D + 1) + |b| * (((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) := by
    rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg hb]; nlinarith
    · nlinarith [abs_nonneg b, mul_le_mul_of_nonpos_left hpow' hb]
  have hE : E * ((N : ℝ) + 1) ^ D ≤ |E| * ((n : ℝ) + (m + 1)) ^ D :=
    (mul_le_mul_of_nonneg_right (le_abs_self E) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hv' (abs_nonneg E))
  have hb2 : |b| * (((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) ≤ δ / 2 * (n : ℝ) ^ (D + 1) :=
    (mul_le_mul_of_nonneg_left h1 (abs_nonneg b)).trans
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hbc hw)
  have hE2 : |E| * F * ((n : ℝ) + (m + 1)) ^ D ≤ δ / 2 * (n : ℝ) ^ (D + 1) := by
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg E) hF0.le)
    nlinarith [mul_le_mul_of_nonneg_right hEc hw]
  have key : b * (N : ℝ) ^ (D + 1) + F * (E * ((N : ℝ) + 1) ^ D) ≤ (b + δ) * (n : ℝ) ^ (D + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hE hF0.le]
  rw [show b * ((N : ℝ) ^ (D + 1) / F) + E * ((N : ℝ) + 1) ^ D =
      (b * (N : ℝ) ^ (D + 1) + F * (E * ((N : ℝ) + 1) ^ D)) / F by field_simp, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right key hF0.le

end EuclideanSections


open EuclideanSections in
theorem EuclideanSections.proof (hP : EuclideanSectionsPower.Statement) (hS : SmallSectionsNonzero.Statement)
    (hL : SublatticeDegree.Statement) (hG : SuccessiveMinimaSpan.Statement) : EuclideanSections.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hconj
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hcon, ⟨Cr, hr⟩, m, hm, hdeg⟩ :=
    hP K ι Ω y D A P0 II hD hII har hb hA hconj
  obtain ⟨C, hC⟩ := hG K ι Ω y D A P0 hD har hb hA
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, ⟨Cr, hr⟩, fun ε hε => ?_⟩
  set C₁ := max C 1 with hC₁
  have hC₁1 : (1 : ℝ) ≤ C₁ := le_max_right _ _
  have hlog : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁1
  set I := II K ι (mCoordIdeal y) (D + 1) (fun _ => A) with hI
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (hdeg (ε / 2) (half_pos hε))
  filter_upwards [eventually_shift_le D m (I + ε / 2) (Cr * Real.log C₁) (ε / 2) (half_pos hε),
    eventually_ge_atTop (m * Q)] with n hn hnQ
  intro _ _
  have hqQ : Q ≤ n / m + 1 := Nat.le_succ_of_le ((Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact hnQ))
  have hnN : n ≤ m * (n / m + 1) := (Nat.lt_mul_div_succ n hm).le
  have hNn : m * (n / m + 1) ≤ n + m := by
    have := Nat.mul_div_le n m
    rw [mul_add, mul_one]
    omega
  suffices main : ∀ N : ℕ, n ≤ N → N ≤ n + m →
      -Real.log (ZLattice.covolume (imageLattice (φ N))) ≤
        (I + ε / 2) * ((N : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) →
      -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
        (I + ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) from
    main _ hnN hNn (hQ (n / m + 1) hqQ)
  intro N hnN hNn h1
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnN
  obtain ⟨t, ht, ht0, hts⟩ := hS K ι Ω y D A P0 har hb hA j

  let ψ : chartLat y A.a n →+ chartLat y A.a (n + j) :=
    { toFun := fun s => ⟨(s : Ω) * t, mul_mem_chartLat s.2 ht⟩
      map_zero' := by ext; simp
      map_add' := fun s s' => by ext; simp [add_mul] }
  have hψ : Function.Injective ψ := fun s s' h =>
    Subtype.ext (mul_right_cancel₀ ht0 (congrArg Subtype.val h))
  have hψn : ∀ s, ‖φ (n + j) (ψ s)‖ ≤ ‖φ n s‖ := fun s => hcon n j s ⟨t, ht⟩ (ψ s) hts rfl

  have hclos : AddSubgroup.closure
      {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)} = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro x
    have hx : (x : Ω) ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a (n + j) ∧ IsBoundedH (mCoordIdeal y) y A (n + j) C s} := by
      rw [hC (n + j)]; exact x.2
    have key : ∀ z (hz : z ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a (n + j) ∧ IsBoundedH (mCoordIdeal y) y A (n + j) C s}),
        ∃ hz' : z ∈ chartLat y A.a (n + j), (⟨z, hz'⟩ : chartLat y A.a (n + j)) ∈ AddSubgroup.closure
          {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)} := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz => exact ⟨hz.1, AddSubgroup.subset_closure (isBoundedH_mono hz.2 (le_max_left _ _))⟩
      | zero => exact ⟨zero_mem _, zero_mem _⟩
      | add z w _ _ hz hw =>
        obtain ⟨hz', hz''⟩ := hz
        obtain ⟨hw', hw''⟩ := hw
        exact ⟨add_mem hz' hw', add_mem hz'' hw''⟩
      | neg z _ hz =>
        obtain ⟨hz', hz''⟩ := hz
        exact ⟨neg_mem hz', neg_mem hz''⟩
    obtain ⟨_, hx'⟩ := key x hx
    exact hx'
  have hbound : ∀ s ∈ {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)},
      ‖φ (n + j) s‖ ≤ C₁ := fun s hs => hsup (n + j) C₁ s (by linarith) hs
  have h2 := hL (chartLat y A.a (n + j)) (chartLat y A.a n) (r (n + j)) (r n) (φ (n + j)) (φ n) ψ _ C₁
    (hinj _) (hinj _) hψ hψn hclos hbound hC₁1
  have h3 : (r (n + j) : ℝ) * Real.log C₁ ≤ Cr * Real.log C₁ * (((n + j : ℕ) : ℝ) + 1) ^ D := by
    have := mul_le_mul_of_nonneg_right (hr (n + j)) hlog
    linarith
  have h4 := hn (n + j) (Nat.le_add_right n j) hNn
  have h5 : I + ε / 2 + ε / 2 = I + ε := by ring
  rw [h5] at h4
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegAmple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace GenDegAmple

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem hilbFn_nonneg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (m : K → ℤ) : 0 ≤ hilbFn q m := by
  unfold hilbFn
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem eventualValue_nonneg {K : Type} [Fintype K] (f : (K → ℤ) → ℤ) (hf : ∀ m, 0 ≤ f m) :
    0 ≤ eventualValue f := by
  unfold eventualValue
  split_ifs with h
  · obtain ⟨m, hm⟩ := h.choose_spec.exists
    rw [← hm]
    exact hf m
  · exact le_rfl

theorem unit_nonneg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (e : ℕ) : ∀ q : Ideal (MRing ι F), NumbersDVR.IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ r : Fin e → K, 0 ≤ intNum F q (fun j => unitDeg (r j)) := by
  induction e with
  | zero =>
    intro q _ _ r
    unfold intNum mixedDiff
    rw [List.ofFn_zero, List.foldr_nil]
    exact eventualValue_nonneg _ (hilbFn_nonneg q)
  | succ e ih =>
    intro q hq hd r
    obtain ⟨i, hX⟩ := hq.relevant (r 0)
    have hd' : ringKrullDim (MRing ι F ⧸ q) = ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := hd
    have hsplit : (fun j : Fin (e + 1) => unitDeg (r j)) =
        Matrix.vecCons (unitDeg (r 0)) (fun j : Fin e => unitDeg (r j.succ)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    rw [hsplit, IntersectionRecursion.proof F K ι q e hq hd' (r 0) i hX]
    refine finsum_nonneg fun W => ?_
    split_ifs with h
    · exact mul_nonneg (Int.natCast_nonneg _) (ih W h.1 h.2.2 _)
    · exact le_rfl

end GenDegAmple

theorem GenDegAmple.proof (hVar : GenericFibreVar.Statement) (hPos : MultiDegreePositive.Statement) :
    GenDegAmple.Statement := by
  intro K _ ι _ Ω _ y D d hV hd
  classical
  have hPV := hVar K ι Ω y D hV
  have hP := (Bridge.isMultiProjPrime_iff _).mpr hPV.1
  have hrel : FieldNumbers.relDim (KH.genIdeal y) = D := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hPV.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  set f := intNumMultilinear (KH.genIdeal y) D hP.multiHomog hP.relevant hrel with hf
  have hg : ∀ b, genDeg (mCoordIdeal y) D b = f (fun _ => b) := fun b => by
    rw [hf, intNumMultilinear_apply, genDeg]
    congr
  have hN : ∀ r : Fin D → K, 0 ≤ f (fun j => unitDeg (r j)) := fun r => by
    rw [hf, intNumMultilinear_apply]
    exact GenDegAmple.unit_nonneg D _ hP hPV.2 r
  have hH : 0 < f (fun _ => fun _ => (1 : ℤ)) := by
    rw [hf, intNumMultilinear_apply]
    exact hPos ℚ K ι _ D hP hPV.2
  have hsum : ∀ b : K → ℤ, (fun _ : Fin D => b) = fun _ => ∑ k, b k • unitDeg k := fun b => by
    funext _ k'
    simp [unitDeg, Finset.sum_apply, Pi.single_apply]
  have expand : ∀ b : K → ℤ,
      f (fun _ => b) = ∑ r : Fin D → K, (∏ j, b (r j)) * f (fun j => unitDeg (r j)) := fun b => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum b, f.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [f.map_smul_univ (fun j => b (r j)) (fun j => unitDeg (r j)), smul_eq_mul]
    simp only [RingHom.id_apply]
  rw [hg, expand d]
  have hH' := hH
  rw [expand (fun _ => (1 : ℤ))] at hH'
  simp only [Finset.prod_const_one, one_mul] at hH'
  refine lt_of_lt_of_le hH' (Finset.sum_le_sum fun r _ => ?_)
  have hp : (1 : ℤ) ≤ ∏ j, d (r j) := by
    calc (1 : ℤ) = ∏ _j : Fin D, (1 : ℤ) := Finset.prod_const_one.symm
      _ ≤ ∏ j, d (r j) := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun j _ => hd (r j))
  exact le_mul_of_one_le_left (hN r) hp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneSectionBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Mul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLatQ (b : K → ℤ) {t : Ω} (ht : t ∈ chartLatQ y (b - 1) 1) :
    (∏ k, y ⟨k, c k⟩) * t ∈ chartLatQ y b 1 := by
  intro c' hc'
  have h := ht c' hc'
  have hk : ∀ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) =
      y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k)) / y ⟨k, c' k⟩ := by
    intro k
    rw [eq_div_iff (hc' k), ← zpow_add_one₀ (hc' k)]
    congr 1
    simp only [Pi.sub_apply, Pi.one_apply]
    ring
  have heq : (∏ k, y ⟨k, c k⟩) * t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) =
      (t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) := by
    simp only [hk, Finset.prod_div_distrib]
    ring
  rw [heq]
  refine Subalgebra.mul_mem _ h (Subalgebra.prod_mem _ fun k _ => ?_)
  exact Algebra.subset_adjoin ⟨⟨k, c k⟩, rfl⟩

theorem finrank_chartLatQ_le (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) :
    Module.finrank ℚ (chartLatQ y b 1) ≤
      Module.finrank ℚ (chartLatQ y (b - 1) 1) + Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) := by
  by_cases hfin : FiniteDimensional ℚ (chartLatQ y b 1)
  swap
  · rw [Module.finrank_of_not_finite hfin]; exact Nat.zero_le _
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  let φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b :=
    { toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, mul_mem_chartLatQ b t.2⟩,
        Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩
      map_add' := fun s t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_add, mul_add]
      map_smul' := fun r t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }
  have hinj : Function.Injective φ := fun s t h => by
    have h' := congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h
    exact Subtype.ext (mul_left_cancel₀ hm0 h')
  have hsurj : Function.Surjective φ := by
    rintro ⟨⟨s, hsV⟩, hs⟩
    obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hs)
    exact ⟨⟨t, ht⟩, Subtype.ext (Subtype.ext hts)⟩
  have hφ := (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  rw [← Submodule.finrank_quotient_add_finrank (chartDivSec y c b), ← hφ, add_comm]

end Mul

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem nefOnGenericDeg_of_semipos (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) {P P0 : Ideal (MRing ι)} {M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hP0 : P0 ≤ P) (hs : IsSemipositiveRel P0 P M) : NefOnGenericDeg P M.a := by
  classical
  intro W hW hPW
  have h1 : 0 ≤ geomDeg W M 1 := hN K ι P P0 M hP0 hs W hW hPW
  have h2 := hD K ι W 1 (fun _ => M) hW (fun _ => hs.1)
  have h3 : geomDeg W M 1 = (genDeg W 1 M.a : ℝ) := by
    rw [geomDeg, genDeg]
    convert h2 using 2
    rfl
  exact_mod_cast h3 ▸ h1

theorem continuousOn_zcomb_fsH {M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hM : IsSmoothHerm M) (k : ℤ) :
    ContinuousOn (HermLine.zcomb M (fsH ι) k (-1)).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have hH : ContinuousOn (fsH ι).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) 1).continuousOn
  exact (hM.continuousOn.zpow₀ k fun z hz => Or.inl (M.pos z hz).ne').mul
    (hH.zpow₀ (-1) fun z hz => Or.inl ((fsH ι).pos z hz).ne')

theorem KodairaSection.proof (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) (hK : KodairaGeneric.Statement)
    (hC : ChartDenominator.Statement) (hS : SectionSupBound.Statement) : KodairaSection.Statement := by
  intro K _ ι _ Ω _ _ y D M P0 hD1 har hb hM
  obtain ⟨k, e, hk, he0, heQ⟩ :=
    hK K ι Ω y D M.a hD1 har hb (nefOnGenericDeg_of_semipos hN hD hM.normalForm_baseLattice_le_dualSpan_sup_line hM.semipos) hM.big
  obtain ⟨n, hn, hne⟩ := hC K ι Ω y _ 1 e heQ
  have ha : (HermLine.zcomb M (fsH ι) k (-1)).a = (k : ℤ) • M.a - 1 := by
    funext i
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics]
    ring
  obtain ⟨C, hC0, hB⟩ := hS K ι Ω y (HermLine.zcomb M (fsH ι) k (-1)) 1 ((n : Ω) * e)
    (continuousOn_zcomb_fsH hM.semipos.1 k) (by rw [ha]; exact hne)
  exact ⟨k, (n : Ω) * e, C, hk, hC0, mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) he0, hne, hB⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionToProjectiveBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem ReductionToProjectiveBlock.proof (hRP : ReductionToProjective.Statement)
    (hMC : BlockMetricChange.Statement) (hIm : BlockImageDatum.Statement) (hTop : BlockImageTop.Statement)
    (hGD : BlockImageGenDeg.Statement) : ReductionToProjectiveBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  obtain ⟨d₀, r, M, N, d', hy, hk, hB, hmet, hchi⟩ := hIm D K ι Ω d

  have h1 := hMC D K ι Ω I d d₀ hI hy hk

  have h2 := (hRP D Ω (Fin r) I d' hI).2

  have hdeg : d₀.A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ := hk ▸ d₀.deg
  have htop : I K ι (mCoordIdeal d₀.y) (D + 1) (fun _ => d₀.A) = top I d'.x d'.m D := by
    rw [hy]
    exact hTop D K ι Ω (Fin r) I d.y d.k₀ d₀.A M N d'.x d'.m hI d.arith d.birat d'.arith hB hdeg
      d₀.semipos.1 d'.smooth hmet

  have hg : genDeg (ι := GlobalTheory (Fin r)) (coordIdeal ℤ d'.x) D 1 = genDeg (mCoordIdeal d.y) D d.A.a := by
    rw [d.deg]
    exact hGD D K ι Ω (Fin r) d.y d.k₀ M N d'.x d.arith d.birat hB
  rw [hg] at h2
  refine (h2.sub h1).congr_left fun n => ?_
  simp only [hsDefect, hchi n, htop]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricTransportSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def MetricTransportSmooth.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)),
    IsInvMat B → IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) → IsSmoothMetric m'

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

