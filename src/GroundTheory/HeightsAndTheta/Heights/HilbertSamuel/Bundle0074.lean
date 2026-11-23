module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockArith
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PowerBlockArith

variable {K : Type} [Fintype K] {ι : K → Type}

theorem blockFnField_addBlock {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {a : K → ℤ} {m N : ℕ}
    {v : Fin N → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hv : ∀ j, v j ∈ chartLat y a m) :
    blockFnField (addBlock y v) = blockFnField y := by
  have hZ : ∀ s ∈ chartRingZ y c, s ∈ blockFnField y := by
    intro s hs
    have : chartRingZ y c ≤ (blockFnField y).toSubalgebra.restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin ℚ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
    exact this hs
  apply le_antisymm
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨⟨_ | k, i⟩, ⟨_ | k', i'⟩, hpq, rfl⟩
    · have hP0 : (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have e : addBlock y v ⟨none, i⟩ / addBlock y v ⟨none, i'⟩ =
          (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) / (v i' * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) := by
        rw [mul_div_mul_right _ _ hP0]
        rfl
      rw [e]
      exact div_mem (hZ _ (hv i c hc)) (hZ _ (hv i' c hc))
    · exact absurd hpq (by simp)
    · exact absurd hpq (by simp)
    · obtain rfl : k = k' := Option.some_injective _ hpq
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _
      ⟨(⟨some p.1, p.2⟩ : Σ k, addIdx ι N k), (⟨some q.1, (hpq ▸ q.2 : ι q.1)⟩ : Σ k, addIdx ι N k),
        by simp [hpq], by cases p; cases q; simp at hpq; subst hpq; rfl⟩

end PowerBlockArith


open PowerBlockArith in
theorem PowerBlockArith.proof (hF : CoordArithOfFnField.Statement) : PowerBlockArith.Statement := by
  intro K _ ι _ Ω _ _ y D a m N v hy hv hgen

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0]
  choose c hc using hnz

  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    obtain ⟨u, -, hu⟩ := hgen c hc
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hu
  exact hF K ι (Option K) (addIdx ι N) Ω y (addBlock y v) (D + 1) ⟨none⟩
    (fun k => by
      cases k with
      | none => exact ⟨j₀, hj₀⟩
      | some k => exact ⟨c k, hc k⟩)
    (blockFnField_addBlock c hc hv).symm hy

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockDatum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

noncomputable section

namespace PowerBlockDatum

theorem exists_coord_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := hV.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem isMultiHomogIdeal_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) :=
  ⟨{1}, fun f hf => ⟨fun _ => 0, by
    rw [Set.mem_singleton_iff.mp hf]
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp⟩, Ideal.span_singleton_one.symm⟩

end PowerBlockDatum


open PowerBlockDatum in
theorem PowerBlockDatum.proof (hE : ResExistsStatement) (hV : ResVolume.Statement)
    (hVer : PowerBlockVeronese.Statement) (hBir : PowerHeightsirational.Statement)
    (hAr : PowerBlockArith.Statement) (hMet : PowerBlockMetric.Statement)
    (hMeas : PowerBlockMeasure.Statement) : PowerBlockDatum.Statement := by
  intro K _ _ ι _ Ω _ _ y D A P0 hD hArith hBiry hSG hConj
  obtain ⟨q, w, hw, hgen, -⟩ := hSG.gen
  obtain ⟨m₁, hm₁⟩ := hVer K ι Ω y A.a q w (exists_coord_ne_zero hArith) hw hgen
  obtain ⟨m₂, hm₂⟩ := hBir K ι Ω y D A.a q w hD hArith hBiry hw hgen hSG.deg_pos
  obtain ⟨N, v, hspan, hgenv, hver⟩ := hm₁ (max (max m₁ m₂) 1) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hbir := hm₂ (max (max m₁ m₂) 1) (le_trans (le_max_right _ _) (le_max_left _ _)) N v hspan
  have hv : ∀ j, v j ∈ chartLat y A.a (max (max m₁ m₂) 1) := fun j =>
    hspan ▸ AddSubgroup.subset_closure (Set.mem_range_self j)
  have hArv := hAr K ι Ω y D A.a _ N v hArith hv hgenv
  obtain ⟨B, P0', hBa, hBconj, hP0', hBsemi, hrel⟩ :=
    hMet K ι Ω y A P0 _ N v hSG.normalForm_baseLattice_le_dualSpan_sup_line hSG.semipos hConj hv hgenv
  obtain ⟨J', -, -, -, ⟨R'⟩⟩ := hE (Option K) (addIdx ι N) (mCoordIdeal (addBlock y v)) ⊤ D hArv
    isMultiHomogIdeal_top (fun h => hArv.2.1.1.ne_top (top_le_iff.mp h))
  let _ : MeasurableSpace R'.toAnRes.X := borel _
  have _ : BorelSpace R'.toAnRes.X := ⟨rfl⟩
  obtain ⟨dV, hdV⟩ := hV (Option K) (addIdx ι N) _ _ D R'.toAnRes hArv
  obtain ⟨μ, hμp, hμn, hμd, hμ⟩ :=
    hMeas K ι Ω y A _ N D v B J' R'.toAnRes dV hSG.semipos.1 hBsemi.1 hBa hdV hv hgenv hrel
  let d : HSMBlockDatum D (Option K) (addIdx ι N) Ω :=
    { y := addBlock y v, k₀ := none, A := B, P0 := P0', J := J', R := R'.toAnRes, meas := borel _,
      borel := ⟨rfl⟩, dV := dV, one_le := hD, arith := hArv, birat := hbir, deg := hBa, conjInv := hBconj,
      normalForm_baseLattice_le_dualSpan_sup_line := hP0', semipos := hBsemi, vol := hdV }
  exact ⟨max (max m₁ m₂) 1, N, v, d, μ, le_max_right _ _, rfl, rfl, hv, hgenv, hrel,
    eventually_atTop.2 ⟨1, fun n hn => hver n hn⟩, hμp, hμn, hμd, fun q f hf => hμ q f hf⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PowerBlockTop

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def tensorPowH (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι
  | 0 => A
  | n + 1 => (tensorPowH A n).tensor A

omit [∀ k, Fintype (ι k)] in
theorem tensorPowH_a (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n : ℕ) : (tensorPowH A n).a = fun k => ((n + 1 : ℕ) : ℤ) * A.a k := by
  induction n with
  | zero => funext k; simp [tensorPowH]
  | succ n ih =>
    funext k
    show (tensorPowH A n).a k + A.a k = _
    rw [ih]
    push_cast
    ring

omit [∀ k, Fintype (ι k)] in
theorem tensorPowH_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n : ℕ) (z : (Σ k, ι k) → ℂ) : (tensorPowH A n).h z = A.h z ^ (n + 1) := by
  induction n with
  | zero => simp [tensorPowH]
  | succ n ih =>
    show (tensorPowH A n).h z * A.h z = _
    rw [ih, pow_succ _ (n + 1)]

theorem isSmoothHerm_tensorPowH {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (n : ℕ) : IsSmoothHerm (tensorPowH A n) := by
  induction n with
  | zero => exact hA
  | succ n ih => exact isSmoothHerm_tensor ih hA

theorem update_tensorPowH {I : AllFam} (hI : I.IsFamily) {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n)
    {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (j : Fin n) {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A)
    (t : ℕ) :
    I K ι P n (Function.update L j (tensorPowH A t)) = ((t + 1 : ℕ) : ℝ) * I K ι P n (Function.update L j A) := by
  induction t with
  | zero => simp [tensorPowH]
  | succ t ih =>
    have h := GroundTheory.Heights₂.Heights.Targets.ArithIntersectionSystem.multilin_of_isFamily hI K ι P n L j
      (tensorPowH A t) A hP hL (isSmoothHerm_tensorPowH hA t) hA
    show I K ι P n (Function.update L j ((tensorPowH A t).tensor A)) = _
    rw [h, ih]
    push_cast
    ring

theorem const_tensorPowH {I : AllFam} (hI : I.IsFamily) {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n)
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (t : ℕ) :
    I K ι P n (fun _ => tensorPowH A t) = ((t + 1 : ℕ) : ℝ) ^ n * I K ι P n (fun _ => A) := by
  classical
  let Lr : ℕ → Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun r i => if (i : ℕ) < r then tensorPowH A t else A
  have hLr : ∀ r j, IsSmoothHerm (Lr r j) := fun r j => by
    simp only [Lr]
    split_ifs
    · exact isSmoothHerm_tensorPowH hA t
    · exact hA
  have step : ∀ r, r ≤ n → I K ι P n (Lr r) = ((t + 1 : ℕ) : ℝ) ^ r * I K ι P n (Lr 0) := by
    intro r
    induction r with
    | zero => intro _; simp
    | succ r ih =>
      intro hr
      let j : Fin n := ⟨r, hr⟩
      have e1 : Lr (r + 1) = Function.update (Lr r) j (tensorPowH A t) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [Lr, j]
        · have : (i : ℕ) ≠ r := fun h => hi (Fin.ext h)
          rw [Function.update_of_ne hi]
          simp only [Lr]
          congr 1
          exact propext ⟨fun h => by omega, fun h => by omega⟩
      have e2 : Lr r = Function.update (Lr r) j A := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [Lr, j]
        · rw [Function.update_of_ne hi]
      rw [e1, update_tensorPowH hI hP (hLr r) j hA t, ← e2, ih (by omega), pow_succ]
      ring
  have hn := step n le_rfl
  have e3 : Lr n = fun _ => tensorPowH A t := by funext i; simp [Lr, i.2]
  have e4 : Lr 0 = fun _ => A := by funext i; simp [Lr]
  rw [e3, e4] at hn
  exact hn


omit [∀ k, Fintype (ι k)] in
theorem blockFnField_addBlock {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω}
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {m N : ℕ} {v : Fin N → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hv : ∀ j, v j ∈ chartLat y A.a m) : blockFnField (addBlock y v) = blockFnField y := by
  have hZ : ∀ s ∈ chartRingZ y c, s ∈ blockFnField y := by
    intro s hs
    have : chartRingZ y c ≤ (blockFnField y).toSubalgebra.restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin ℚ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
    exact this hs
  apply le_antisymm
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨⟨_ | k, i⟩, ⟨_ | k', i'⟩, hpq, rfl⟩
    · have hP0 : (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have e : addBlock y v ⟨none, i⟩ / addBlock y v ⟨none, i'⟩ =
          (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) / (v i' * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) := by
        rw [mul_div_mul_right _ _ hP0]
        rfl
      rw [e]
      exact div_mem (hZ _ (hv i c hc)) (hZ _ (hv i' c hc))
    · exact absurd hpq (by simp)
    · exact absurd hpq (by simp)
    · obtain rfl : k = k' := Option.some_injective _ hpq
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _ ⟨oldV N p, oldV N q, by simp [oldV, hpq], rfl⟩

end PowerBlockTop


open PowerBlockTop in
theorem PowerBlockTop.proof (hPF : PFCoordStatement) (hIso : IsomInvariance.Statement)
    (hAB : AddBlockIsometric.Statement) : PowerBlockTop.Statement := by
  classical
  intro K _ _ ι _ Ω _ _ y D A m N v B I hI hy hA hm hv hgen hBa hBs hmet

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0]
  choose c hc using hnz

  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    obtain ⟨u, -, hu⟩ := hgen c hc
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hu
  have hFn := blockFnField_addBlock c hc hv
  have hbm := isBlockMap_oldV (ι := ι) N
  have hyv : IsArithVar (mCoordIdeal (addBlock y v)) (D + 1) :=
    CoordArithOfFnField.proof K ι (Option K) (addIdx ι N) Ω y (addBlock y v) (D + 1) ⟨none⟩
      (fun k => by
        cases k with
        | none => exact ⟨j₀, hj₀⟩
        | some k => exact ⟨c k, hc k⟩) hFn.symm hy
  have hcomp : addBlock y v ∘ oldV N = y := rfl
  have himg : imageZ (oldV N) (mCoordIdeal (addBlock y v)) = mCoordIdeal y := by
    rw [GroundTheory.Heights₂.Heights.Targets.ImageCoord.proof K ι (Option K) (addIdx ι N) some (oldV N) Ω (addBlock y v) hbm,
      hcomp]
  have hAm : IsSmoothHerm (tensorPowH A (m - 1)) := isSmoothHerm_tensorPowH hA _
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hpull := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hbm (tensorPowH A (m - 1))

  have hPFe := hPF I hI K ι (Option K) (addIdx ι N) some (oldV N) Ω (addBlock y v) (D + 1)
    (fun _ => tensorPowH A (m - 1)) (fun _ => GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.pullHerm hbm (tensorPowH A (m - 1)))
    hbm hyv (by rw [himg]; exact hy) (fun _ => hAm) (fun _ => hpull)
  rw [IntermediateField.relfinrank_eq_one_iff.mpr (by rw [hcomp, hFn]), Nat.cast_one, one_mul, himg] at hPFe

  have hiso : ∀ _ : Fin (D + 1), IsIsometricOn (mCoordIdeal (addBlock y v)) B
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.pullHerm hbm (tensorPowH A (m - 1))) := fun _ =>
    hAB K ι Ω y D A m N v B _ hy hm hv hgen hBa
      (by
        show pullDeg some (tensorPowH A (m - 1)).a = _
        rw [tensorPowH_a, hm'])
      (fun z => by
        show (tensorPowH A (m - 1)).h (fun p => z (oldV N p)) = _
        rw [tensorPowH_h, hm']
        rfl) hmet
  have e1 := hIso (Option K) (addIdx ι N) (I (Option K) (addIdx ι N)) (hI _ _) (mCoordIdeal (addBlock y v)) (D + 1)
    (fun _ => B) (fun _ => GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.pullHerm hbm (tensorPowH A (m - 1))) hyv (fun _ => hBs)
    (fun _ => GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hbm hpull hAm) hiso
  rw [e1, hPFe, const_tensorPowH hI hy hA, hm']

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelChartPoly

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

theorem chartMonomial_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ e k ∈ relSecM R y e := by
  classical
  have h := monomial_mem_relSecM R y (b := e) (fun q : Σ k, ι k => if q.2 = c q.1 then e q.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [pow_ite]

theorem coord_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) [DecidableEq K] :
    y p ∈ relSecM R y (Pi.single p.1 1) := by
  have h := chartMonomial_mem R y (Function.update c p.1 p.2) (Pi.single p.1 1)
  convert h using 1
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem generator_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) :
    y p / y ⟨p.1, c p.1⟩ * ∏ k, y ⟨k, c k⟩ ∈ relSecM R y (fun _ => 1) := by
  classical
  by_cases h0 : y ⟨p.1, c p.1⟩ = 0
  · simp [h0]
  have hW : ∏ k, y ⟨k, c k⟩ = (∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k) *
      ∏ k, y ⟨k, c k⟩ ^ (if k = p.1 then 0 else 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add]
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  have h1 : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
    rw [Finset.prod_eq_single p.1]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hmem := mul_mem_relSecM R y (coord_mem R y c p)
    (chartMonomial_mem R y c (fun k => if k = p.1 then 0 else 1))
  have hb : (Pi.single p.1 1 + fun k => if k = p.1 then 0 else 1 : K → ℕ) = fun _ => 1 := by
    funext k
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  rw [hb] at hmem
  rw [hW, h1, ← mul_assoc, div_mul_cancel₀ _ h0]
  exact hmem

end RelChartPoly

theorem RelChartPoly.proof : RelChartPoly.Statement := by
  intro K _ ι _ Ω _ R y c σ hσ
  have hW : ∀ M : ℕ, (∏ k, y ⟨k, c k⟩) ^ M ∈ relSecM R y (fun _ => M) := by
    intro M
    rw [← Finset.prod_pow]
    exact RelChartPoly.chartMonomial_mem R y c (fun _ => M)
  have hmul : ∀ {a b : ℕ} {x x' : Ω}, x ∈ relSecM R y (fun _ => a) → x' ∈ relSecM R y (fun _ => b) →
      x * x' ∈ relSecM R y (fun _ => a + b) := fun hx hx' => mul_mem_relSecM R y hx hx'
  induction hσ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨1, by simpa using RelChartPoly.generator_mem R y c p⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ r ?_
    simpa using hW 0
  | add x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    rw [add_mul]
    refine add_mem ?_ ?_
    · have := hmul hN (hW M)
      convert this using 1
      ring
    · have := hmul hM (hW N)
      rw [add_comm N M]
      convert this using 1
      ring
  | mul x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    have := hmul hN hM
    convert this using 1
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNefGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedNefGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    NefOnGenericDeg (mCoordIdeal y) a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

