module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.TailBound
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorRatioRegularOfMatrixIdentity
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

private theorem det_mul_eq_sum_prod_det_submatrix {Ω : Type} [Field Ω] {n r : ℕ}
    (B : Matrix (Fin r) (Fin n) Ω) (C : Matrix (Fin n) (Fin r) Ω) :
    (B * C).det = ∑ p : Fin r → Fin n, (∏ i, B i (p i)) * (C.submatrix p id).det := by
  have hsub : ∀ p : Fin r → Fin n, (C.submatrix p id).det =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : Ω) * ∏ i, C (p i) (σ i) := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [← Matrix.det_transpose, Matrix.transpose_mul, Matrix.det_apply']
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum, hsub]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

private theorem det_submatrix_mul_det_eq_pow_mul {Ω : Type} [Field Ω] {n r : ℕ}
    (A C : Matrix (Fin n) (Fin r) Ω) (T : Matrix (Fin r) (Fin r) Ω) (a : Ω) (hAT : A * T = a • C)
    (J : Fin r → Fin n) :
    (A.submatrix J id).det * T.det = a ^ r * (C.submatrix J id).det := by
  have h1 : A.submatrix J id * T = a • C.submatrix J id := by
    ext i j
    have h := congrFun (congrFun hAT (J i)) j
    simpa [Matrix.mul_apply] using h
  rw [← Matrix.det_mul, h1, Matrix.det_smul, Fintype.card_fin]

theorem minor_isUnit_of_leftInverse : ∀ {Ω : Type} [Field Ω] {n r : ℕ} (R : Subring Ω) (A C : Matrix (Fin n) (Fin r) Ω)
    (B : Matrix (Fin r) (Fin n) Ω) (T : Matrix (Fin r) (Fin r) Ω) (a : Ω) (hAT : A * T = a • C) (ha : a ≠ 0)
    (hT : T.det ≠ 0) (hBC : B * C = 1) (hC : ∀ j l, C j l ∈ R) (hB : ∀ l j, B l j ∈ R) (J₀ : Fin r → Fin n)
    (hz : (A.submatrix J₀ id).det ≠ 0)
    (hr : ∀ J : Fin r → Fin n, (A.submatrix J id).det / (A.submatrix J₀ id).det ∈ R),
    (C.submatrix J₀ id).det ≠ 0 ∧ (C.submatrix J₀ id).det ∈ R ∧ (C.submatrix J₀ id).det⁻¹ ∈ R ∧
      (A.submatrix J₀ id).det * T.det = a ^ r * (C.submatrix J₀ id).det := by
  intro Ω _ n r R A C B T a hAT ha hT hBC hC hB J₀ hz hr
  have hrel : ∀ J : Fin r → Fin n,
      (A.submatrix J id).det * T.det = a ^ r * (C.submatrix J id).det :=
    det_submatrix_mul_det_eq_pow_mul A C T a hAT
  have har : a ^ r ≠ 0 := pow_ne_zero r ha
  have hC0 : (C.submatrix J₀ id).det ≠ 0 := by
    intro h0
    have h := hrel J₀
    rw [h0, mul_zero] at h
    exact mul_ne_zero hz hT h
  have hCR : (C.submatrix J₀ id).det ∈ R := by
    let M : Matrix (Fin r) (Fin r) R := Matrix.of fun i j => ⟨C (J₀ i) j, hC _ _⟩
    have hM : R.subtype.mapMatrix M = C.submatrix J₀ id := by
      ext i j
      rfl
    rw [← hM, ← RingHom.map_det]
    exact SetLike.coe_mem M.det
  have hratio : ∀ J : Fin r → Fin n, (C.submatrix J id).det =
      (C.submatrix J₀ id).det * ((A.submatrix J id).det / (A.submatrix J₀ id).det) := by
    intro J
    apply mul_left_cancel₀ har
    rw [← hrel J, show a ^ r * ((C.submatrix J₀ id).det *
        ((A.submatrix J id).det / (A.submatrix J₀ id).det)) =
        (a ^ r * (C.submatrix J₀ id).det) * ((A.submatrix J id).det / (A.submatrix J₀ id).det) by ring,
      ← hrel J₀]
    field_simp
  have hs := det_mul_eq_sum_prod_det_submatrix B C
  rw [hBC, Matrix.det_one] at hs
  have hs2 : (C.submatrix J₀ id).det * ∑ p : Fin r → Fin n,
      (∏ i, B i (p i)) * ((A.submatrix p id).det / (A.submatrix J₀ id).det) = 1 := by
    refine Eq.trans ?_ hs.symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hratio p]
    ring
  refine ⟨hC0, hCR, ?_, hrel J₀⟩
  rw [inv_eq_of_mul_eq_one_right hs2]
  exact sum_mem fun p _ => mul_mem (prod_mem fun i _ => hB _ _) (hr p)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyUniformBound
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.AnalyticLimit

theorem tailLogBound_of_φ_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Yo : Set X) (r : X → ℝ) {Φ Ψ : Fin e → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ) (CE : ℝ)
    (H : TailLogBound A Yo r Φ CE) : TailLogBound A Yo r Ψ CE := by
  have hd : ∀ j y, ReciprocityTheory.AnForm.M.locDens A Φ j y = ReciprocityTheory.AnForm.M.locDens A Ψ j y := by
    intro j y
    simp only [ReciprocityTheory.AnForm.M.locDens, h]
  have hM : ∀ g, ReciprocityTheory.AnForm.M.MIntegrable A Φ g ↔ ReciprocityTheory.AnForm.M.MIntegrable A Ψ g := by
    intro g
    simp only [ReciprocityTheory.AnForm.M.MIntegrable, hd]
  have hI : ∀ g, ReciprocityTheory.AnForm.M.mInt A Φ g = ReciprocityTheory.AnForm.M.mInt A Ψ g := by
    intro g
    simp only [ReciprocityTheory.AnForm.M.mInt, ReciprocityTheory.AnForm.M.integralWith, hd]
  intro R₀ hR
  rw [← hM, ← hI]
  exact H R₀ hR

theorem tailLogProducts : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → ∀ (P : Fin e → LocPot X) (C : ℝ), (∀ i, IsPotential A (P i)) → ∃ CE : ℝ, ∀ f : Fin e → X → ℝ, (∀ i, A.Smooth (f i)) → (∀ i, IsPsh A (P i + LocPot.ofFun (f i))) → (∀ i, ∀ x ∈ R.Yo, |f i x| ≤ C + C * Real.log (R.r x)) → (∀ i, ∀ x ∈ R.Yo, f i x ≤ C) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => P i + LocPot.ofFun (f i)) CE := by
  intro e X _ _ _ A R Θ hΘ hΘp P C hP
  have hSmooth : ListTailLogSmooth.Statement :=
    ListTailLogSmooth.proof
      (GroundTheory.Heights₂.Heights.ForSecondHalf.ListTailLog.of_lemmaETailMass lemmaETailMass)
  let R₁ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.RegChartData.ofRegular R Θ hΘ hΘp
  let R' := regChartShift R₁
  have hconst : A.Smooth (fun _ : X => C) := fun j => contDiffOn_const
  let th : Fin e → LocPot X := fun i => P i + LocPot.ofFun (fun _ => C)
  have hth : ∀ i, IsPotential A (th i) := fun i =>
    isPotentialAdd A _ _ (hP i) (isPotential_ofFun A _ hconst)
  obtain ⟨Om, hOm⟩ := BoundingKaehler.full e A ⟨Θ, hΘ, hΘp⟩ e th hth
  obtain ⟨CE, hCE⟩ := hSmooth A R' Om (3 * |C|)
  refine ⟨CE, fun f hf hpsh habs hle => ?_⟩
  let u : Fin e → X → ℝ := fun i x => f i x - C
  have hu : ∀ i, A.Smooth (u i) := fun i j => (hf i j).sub contDiffOn_const
  have hφ : ∀ i, (potForm (th i) (u i)).φ = (P i + LocPot.ofFun (f i)).φ := by
    intro i
    funext x y
    show (P i).φ x y + C + (f i y - C) = (P i).φ x y + f i y
    ring
  have hnn : ∀ i, FormNonneg A R.Yo (P i + LocPot.ofFun (f i)) := fun i x k y hy w =>
    hpsh i x k y ⟨hy.1, hy.2.2⟩ w
  have hform : ∀ i, IsSmoothPotForm A R'.Yo R'.r Om (3 * |C|) (th i) (u i) := by
    intro i
    refine ⟨⟨hth i, (hOm i).1, (hOm i).2, ?_, ?_, ?_, ?_, Or.inl (hu i)⟩, hu i⟩
    · exact fun j => (hu i j).mono fun y hy => ⟨hy.1, trivial⟩
    · intro x hx
      have := hle i x hx
      show f i x - C ≤ 0
      linarith
    · intro x hx
      have hx' : x ∈ R.Yo := hx
      have h1 : 1 ≤ R.r x := R.one_le_r x hx'
      have he : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have hL : Real.log (R.r x) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
        Real.log_le_log (by linarith) (by linarith)
      have hL1 : 1 ≤ Real.log (R.r x + (Real.exp 1 - 1)) := by
        have h2 : Real.log (Real.exp 1) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
          Real.log_le_log (Real.exp_pos 1) (by linarith)
        rwa [Real.log_exp] at h2
      have hL0 := Real.log_nonneg h1
      have hf' : -(C + C * Real.log (R.r x)) ≤ f i x := by
        have := (neg_abs_le (f i x))
        linarith [habs i x hx']
      have hc1 : C * Real.log (R.r x) ≤ |C| * Real.log (R.r x + (Real.exp 1 - 1)) :=
        mul_le_mul (le_abs_self C) hL hL0 (abs_nonneg C)
      have hc2 : |C| ≤ |C| * Real.log (R.r x + (Real.exp 1 - 1)) :=
        le_mul_of_one_le_right (abs_nonneg _) hL1
      have hc3 := le_abs_self C
      show -(3 * |C| * Real.log (R.r x + (Real.exp 1 - 1))) ≤ f i x - C
      linarith
    · intro x k y hy w
      have := hnn i x k y ⟨hy.1, hy.2.1, hy.2.2.1⟩ w
      rw [hφ i]
      exact this
  have hB := hCE th u hform
  have hpot : ∀ i, IsPotential A (P i + LocPot.ofFun (f i)) := fun i =>
    isPotentialAdd A _ _ (hP i) (isPotential_ofFun A _ (hf i))
  have hB' : TailLogBound A R.Yo R'.r (fun i => P i + LocPot.ofFun (f i)) CE :=
    tailLogBound_of_φ_eq A _ _ hφ CE hB
  exact tailLogBound_of_le (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.isOpen_Yo_regular R)
    (regChartData_continuousOn_r R₁) (r' := R'.r)
    (fun x _ => by
      show R.r x ≤ R.r x + (Real.exp 1 - 1)
      linarith [Real.add_one_le_exp (1 : ℝ)])
    hpot hnn hB'

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NefPolarization
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.NefPolProof

theorem exists_ne_zero_of_relevant {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : IsRelevant (mCoordIdeal y)) :
    ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro k
  obtain ⟨i, hi⟩ := h k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem fin_one_const {α : Type} (a : α) : (fun _ : Fin 1 => a) = ![a] := by
  funext j
  fin_cases j
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.NefPolProof

namespace GlobalTheory.CompanionTheory.Ar.PB


open GlobalTheory.CompanionTheory.Ar.PB.NefPolProof in
theorem nefPol : NefPol := by
  intro hIn D σ _ S Fl hFl K _ ι _ Ω _ _ y Re hJ hBir I hI n hn
  have hK : Nonempty K := Re.arith.1
  have hRe := _root_.GlobalTheory.CompanionTheory.Ar.PB.re_pot hIn.resExists K ι D σ S (mCoordIdeal y) Re
  have hsm : IsSmoothHerm (combLine Re.ref n) := (hRe.2.2.2 n).1
  have hnef : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.NefOnF I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) (combLine Re.ref n).a := by
    intro W hW hle
    obtain ⟨hW', hWmap⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.PB.varieties_over_rat_arith_contract K ι 1).1 W hK hW
    have hPW : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) :=
      (Ideal.le_comap_map).trans (Ideal.comap_mono hle)
    have h0 := _root_.GlobalTheory.CompanionTheory.Ar.PB.nonneg_degree_horizontal_curve hIn K ι D σ S (mCoordIdeal y) Re Fl hFl hJ n hn _ hW' hPW
    have h1 := _root_.GlobalTheory.CompanionTheory.Ar.PB.curvatureIntegral_eq_genericIntersection hIn K ι I hI 1 (W.comap (MvPolynomial.map (Int.castRingHom ℚ)))
      (fun _ => combLine Re.ref n) hW' (fun _ => hsm)
    rw [hWmap] at h1
    have h2 : (0 : ℝ) ≤ (I W 1 fun _ => (combLine Re.ref n).a : ℤ) := by
      rw [← h1]; exact h0
    rw [← fin_one_const]
    exact_mod_cast h2
  refine ⟨hnef, ?_⟩
  intro hpos β dβ _ _
  have hdeg := (hRe.2.2.2 n).2
  have hgp : 0 < geomDeg (mCoordIdeal y) (combLine Re.ref n) D := by
    rw [hdeg]
    exact mul_pos (by exact_mod_cast Re.deg_pos) hpos
  have h1 := _root_.GlobalTheory.CompanionTheory.Ar.PB.curvatureIntegral_eq_genericIntersection hIn K ι I hI D (mCoordIdeal y) (fun _ => combLine Re.ref n) Re.arith (fun _ => hsm)
  have hI0 : 0 < I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) D (fun _ => (combLine Re.ref n).a) := by
    have : (0 : ℝ) < (I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) D (fun _ => (combLine Re.ref n).a) : ℤ) := by
      rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal, ← h1]; exact hgp
    exact_mod_cast this
  have hsec := hIn.siuZ K ι Ω y D (combLine Re.ref n).a I hI Re.arith hBir hnef hI0
  exact _root_.GlobalTheory.CompanionTheory.Ar.PB.section_sub_degree K ι Ω y (combLine Re.ref n).a dβ
    (exists_ne_zero_of_relevant y Re.arith.2.1.2.2) hsec

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProdXbPowEqXcOfPow
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} {K₀ : Type} {J₀ : K₀ → Type}

theorem eq_baseFull (k' : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀)) {s : Ψ ⊕ Ψ} {a : Fin (rk Ψ p q s)}
    (hk : k'.1 = .inr ⟨s, a⟩) (h : 0 < rk Ψ p q s) : k' = baseFull K₀ s h := by
  have hfull : (a : ℕ) + 1 = rk Ψ p q s :=
    BasePt.step_full K₀ ⟨s, a⟩ (by rw [← hk]; exact k'.2)
  apply Subtype.ext
  rw [hk]
  have e : a = ⟨rk Ψ p q s - 1, by omega⟩ := Fin.ext (by show (a : ℕ) = rk Ψ p q s - 1; omega)
  rw [e]
  rfl

theorem xb_of_step [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)]
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    (k' : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀)) {s : Ψ ⊕ Ψ} {a : Fin (rk Ψ p q s)} (hk : k'.1 = .inr ⟨s, a⟩) :
    xb A x₀ ⟨k', c k'⟩ = zOf A c s := by
  have h : 0 < rk Ψ p q s := by have := a.2; omega
  obtain rfl := eq_baseFull k' hk h
  exact xb_rowsOf A x₀ c s h

theorem zOf_of_rk_eq_zero (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    {s : Ψ ⊕ Ψ} (h : rk Ψ p q s = 0) : zOf A c s = 1 := by
  haveI : IsEmpty (Fin (rk Ψ p q s)) := by rw [h]; infer_instance
  exact Matrix.det_isEmpty


open Classical in
def stepFac (z : Ω) (s : Ψ ⊕ Ψ) : K₀ ⊕ StepIx Ψ p q → Ω :=
  Sum.elim (fun _ => 1) fun t => if t.1 = s then z else 1

theorem prod_stepFac [Fintype Ψ] [Fintype K₀] (z : Ω) (s : Ψ ⊕ Ψ) (hz : rk Ψ p q s = 0 → z = 1) :
    ∏ k' : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀), stepFac z s k'.1 = z := by
  classical
  by_cases h : 0 < rk Ψ p q s
  · rw [Finset.prod_eq_single (baseFull K₀ s h)]
    · simp [stepFac, baseFull, fullT]
    · rintro ⟨k | ⟨s', a⟩, hk⟩ _ hb
      · simp [stepFac]
      · by_cases e : s' = s
        · subst e
          exact absurd (eq_baseFull _ rfl h) hb
        · simp [stepFac, e]
    · simp
  · rw [hz (by omega)]
    refine Finset.prod_eq_one ?_
    rintro ⟨k | ⟨s', a⟩, hk⟩ _
    · simp [stepFac]
    · by_cases e : s' = s
      · subst e
        have := a.2
        omega
      · simp [stepFac, e]

theorem prod_xb_zpow_bF {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type}
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    (r : Ψ × Fin (p + q)) :
    ∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k' =
      xcOf x₀ c ^ (rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1)) *
        (if p ≤ (r.2 : ℕ) + 1 then (zOf A c (.inl r.1))⁻¹ else 1) *
        (if (r.2 : ℕ) + 1 = p + q then (zOf A c (.inr r.1))⁻¹ else 1) := by
  classical
  set N := rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1) with hN
  set zW : Ω := if p ≤ (r.2 : ℕ) + 1 then (zOf A c (.inl r.1))⁻¹ else 1 with hzW
  set zO : Ω := if (r.2 : ℕ) + 1 = p + q then (zOf A c (.inr r.1))⁻¹ else 1 with hzO
  have hW : rk Ψ p q (.inl r.1) = 0 → zW = 1 := fun h => by
    rw [hzW, zOf_of_rk_eq_zero A c h]
    simp
  have hO : rk Ψ p q (.inr r.1) = 0 → zO = 1 := fun h => by
    rw [hzO, zOf_of_rk_eq_zero A c h]
    simp
  let g : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀) → Ω := fun k' =>
    Sum.elim (fun _ => xb A x₀ ⟨k', c k'⟩ ^ N) (fun _ => 1) k'.1
  have hg : ∏ k', g k' = xcOf x₀ c ^ N := by
    rw [xcOf, ← Finset.prod_pow]
    refine (Fintype.prod_of_injective (baseInl (Ψ := Ψ) (p := p) (q := q)) ?_ _ _ ?_ ?_).symm
    · intro a b e
      exact Sum.inl.inj (congrArg Subtype.val e)
    · rintro ⟨k | t, hk⟩ hi
      · exact absurd ⟨k, rfl⟩ hi
      · rfl
    · intro k
      rfl
  have hpt : ∀ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k' =
      g k' * stepFac zW (.inl r.1) k'.1 * stepFac zO (.inr r.1) k'.1 := by
    rintro ⟨k | ⟨s, a⟩, hk⟩
    · have e : bF m r (⟨.inl k, hk⟩ : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀)) = (N : ℤ) := rfl
      rw [e, zpow_natCast]
      simp [g, stepFac]
    · have hx := xb_of_step A x₀ c ⟨.inr ⟨s, a⟩, hk⟩ (s := s) (a := a) rfl
      have hf : (a : ℕ) + 1 = rk Ψ p q s := BasePt.step_full K₀ ⟨s, a⟩ hk
      rw [hx]
      rcases s with τ | τ
      · by_cases e : τ = r.1
        · subst e
          have hf' : (a : ℕ) + 1 = p := hf
          by_cases hc : p ≤ (r.2 : ℕ) + 1
          · simp [bF, twist, g, stepFac, hf', hc, hzW]
          · simp [bF, twist, g, stepFac, hf', hc, hzW]
        · simp [bF, twist, g, stepFac, e]
      · by_cases e : τ = r.1
        · subst e
          have hf' : (a : ℕ) + 1 = q := hf
          by_cases hc : (r.2 : ℕ) + 1 = p + q
          · simp [bF, twist, g, stepFac, hf', hc, hzO]
          · simp [bF, twist, g, stepFac, hf', hc, hzO]
        · simp [bF, twist, g, stepFac, e]
  rw [Finset.prod_congr rfl fun k' _ => hpt k', Finset.prod_mul_distrib, Finset.prod_mul_distrib, hg,
    prod_stepFac zW _ hW, prod_stepFac zO _ hO]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionLocalChartPolynomial
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem proj_diag_ne_zero_iff (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    SncRes.proj z ⟨k, (i, i)⟩ ≠ 0 ↔ z ⟨k, i⟩ ≠ 0 := by
  simp only [SncRes.proj]
  constructor
  · intro h h0
    apply h
    simp [h0]
  · intro h
    have hn : (0 : ℝ) < ‖z ⟨k, i⟩‖ := norm_pos_iff.2 h
    have hpos : (0 : ℝ) < ∑ j, ‖z ⟨k, j⟩‖ ^ 2 := by
      refine lt_of_lt_of_le (pow_pos hn 2) ?_
      exact Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have hden : ((∑ j, ‖z ⟨k, j⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact div_ne_zero (mul_ne_zero h ((map_ne_zero _).2 h)) hden

theorem isOpen_alt_bis (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    IsOpen (SncRes.src P p) := by
  have h : SncRes.src P p = ⋂ k, {x : SncRes.Pts P | x.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
    ext x
    simp only [SncRes.src, Set.mem_ofPred_eq, Set.mem_iInter]
    refine forall_congr' fun k => ?_
    rw [← SncRes.proj_rep x]
    exact (proj_diag_ne_zero_iff _ k (p k)).symm
  rw [h]
  refine isOpen_iInter_of_finite fun k => ?_
  have hc : Continuous fun x : SncRes.Pts P => x.1 ⟨k, (p k, p k)⟩ :=
    (continuous_apply _).comp continuous_subtype_val
  exact isOpen_ne_fun hc continuous_const

theorem chart_coord_ratio : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ p' : (k : K) → ι k, (∀ k, eval (SncRes.coord P p x) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O, (∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ∧ eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q ≠ 0 ∧ ∀ l, SncRes.coord P p y l * eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q = eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) (F l) := by
  intro K _ ι _ P _ p x hx p' hp'
  classical
  have key : ∀ y ∈ SncRes.src P p,
      ((∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ↔ y ∈ SncRes.src P p') := by
    intro y hy
    simp only [SncRes.eval_lift p y hy, ReciprocityTheory.AnForm.R.affCoord]
    constructor
    · intro h k h0
      exact h k (by simp [h0])
    · intro h k
      exact div_ne_zero (h k) (hy k)
  refine ⟨SncRes.src P p ∩ SncRes.src P p', (isOpen_alt_bis P p).inter (isOpen_alt_bis P p'),
    ⟨hx, (key x hx).1 hp'⟩, Set.inter_subset_left, ∏ k, X ⟨k, p k⟩,
    fun l => X ((Fintype.equivFin (Σ k, ι k)).symm l) *
      ∏ k ∈ Finset.univ.erase ((Fintype.equivFin (Σ k, ι k)).symm l).1, X ⟨k, p k⟩, ?_⟩
  rintro y ⟨hy, hy'⟩
  have hw : (fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) =
      ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) := funext (SncRes.eval_lift p y hy)
  simp only [hw]
  have hone : ∀ k, ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p k⟩ = 1 := fun k => by
    simp [ReciprocityTheory.AnForm.R.affCoord, hy k]
  have hne : ∀ k, ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p' k⟩ ≠ 0 := fun k =>
    div_ne_zero (hy' k) (hy k)
  have ha : ∀ k, ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩ ≠ 0 := by
    intro k
    have : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩ =
        1 / ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p' k⟩ := by
      rw [← hone k]; rfl
    rw [this]
    exact div_ne_zero one_ne_zero (hne k)
  refine ⟨(key y hy).2 hy', ?_, fun l => ?_⟩
  · rw [map_prod]
    simp only [eval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => ha k
  · set q := (Fintype.equivFin (Σ k, ι k)).symm l with hq
    have hcoord : SncRes.coord P p y l = ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) q := rfl
    rw [map_mul, map_prod, map_prod, hcoord]
    simp only [eval_X]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k => ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩)
      (Finset.mem_univ q.1), ← mul_assoc]
    congr 1
    have h1 : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨q.1, p q.1⟩ =
        1 / ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨q.1, p' q.1⟩ := by
      rw [← hone q.1]; rfl
    have h2 : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) q =
        ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) q /
          ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨q.1, p' q.1⟩ := rfl
    rw [h1, h2, mul_one_div]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv
end
end

