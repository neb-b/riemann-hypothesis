module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatios
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
public import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterion
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

section Fields

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {G : Type} [Field G] [CharZero G]


omit [∀ k, Fintype (ι k)] in
theorem prod_div_mem (y : (Σ k, ι k) → G) (u v : ∀ k, ι k) :
    (∏ k, y ⟨k, u k⟩) / (∏ k, y ⟨k, v k⟩) ∈ blockFnField y := by
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, u k⟩, ⟨k, v k⟩, rfl, rfl⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem blockFnField_eq_top [Algebra ℤ G] (y : (Σ k, ι k) → G) {κ : Type} (f : κ → G) (c₀ : κ)
    (hsub : ∀ j, f j / f c₀ ∈ blockFnField y)
    (hgen : ∀ a : G, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀), h ≠ 0 ∧ a = g / h) :
    blockFnField y = ⊤ := by
  have hle : ∀ g ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀), g ∈ blockFnField y := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hsub j
    | algebraMap r => rw [eq_intCast]; exact intCast_mem (blockFnField y) r
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  rw [eq_top_iff]
  intro a _
  obtain ⟨g, hg, h, hh, -, rfl⟩ := hgen a
  exact div_mem (hle g hg) (hle h hh)

theorem trdeg_top : Algebra.trdeg ℤ (⊤ : IntermediateField ℚ G) = Algebra.trdeg ℤ G := by
  have e : (⊤ : IntermediateField ℚ G) ≃ₐ[ℤ] G := (IntermediateField.topEquiv (F := ℚ) (E := G)).restrictScalars ℤ
  exact e.trdeg_eq

end Fields

section Gen

variable (Ω : Type) [Field Ω] [CharZero Ω] {S : Type} (r : S → ℕ)

theorem trdeg_genField [inst : Algebra ℤ (GenField Ω r)] :
    Algebra.trdeg ℤ (GenField Ω r) = Algebra.trdeg ℤ Ω + Cardinal.mk (GenIx r) := by
  obtain rfl : inst = OreLocalization.instAlgebra := Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic (MvPolynomial (GenIx r) Ω) (GenField Ω r) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (GenIx r) Ω))
  haveI : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr
    (by simpa using (Int.cast_injective (α := Ω)))
  have h1 := trdeg_add_eq ℤ Ω (A := GenField Ω r)
  have h2 := trdeg_add_eq Ω (MvPolynomial (GenIx r) Ω) (A := GenField Ω r)
  rw [trdeg_eq_zero (R := MvPolynomial (GenIx r) Ω) (A := GenField Ω r), add_zero, MvPolynomial.trdeg_of_isDomain] at h2
  rw [← h1, ← h2, Cardinal.lift_id]

end Gen

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {G : Type} [Field G] [CharZero G]

theorem isArithVar_of_trdeg [Nonempty K] (y : (Σ k, ι k) → G) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : ℕ)
    (htr : Algebra.trdeg ℤ (blockFnField y) = e) : IsArithVar (mCoordIdeal y) (e + 1) := by
  refine ⟨‹_›, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y c hc⟩, horizontal y, ?_⟩
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.ringKrullDim_coord y c hc, htr, map_add (f := _), Cardinal.toENat_nat, Cardinal.toENat_nat]
  have h4 : (e : ℕ∞) + (Fintype.card K : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by
    push_cast
    ring
  rw [h4]
  rfl

theorem trdeg_of_isArithVar (x : (Σ k, ι k) → G) (d : ℕ) (hx : IsArithVar (mCoordIdeal x) (d + 1)) :
    ∃ c : ∀ k, ι k, (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ Algebra.trdeg ℤ (blockFnField x) = d := by
  obtain ⟨-, ⟨-, -, hrel⟩, -, hdim⟩ := hx
  have hne : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X, h0, map_zero, zero_mul]
  choose c hc using hne
  refine ⟨c, hc, ?_⟩
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.ringKrullDim_coord x c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField x) + (Fintype.card K : Cardinal)).toENat + 1 =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_injective hdim
  rw [map_add (f := _), Cardinal.toENat_nat] at h1
  have h3 : (Algebra.trdeg ℤ (blockFnField x)).toENat + ((Fintype.card K + 1 : ℕ) : ℕ∞) =
      (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
    push_cast at h1 ⊢
    rw [← add_assoc, h1]
    ring
  have h2 : (Algebra.trdeg ℤ (blockFnField x)).toENat = (d : ℕ∞) :=
    WithTop.add_right_cancel (ENat.coe_ne_top _) h3
  exact Cardinal.toENat_eq_natCast.mp h2

end Dim

section Main

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ}

theorem mk_genIx : Cardinal.mk (GenIx (rk Ψ p q)) = ((Fintype.card Ψ * (p.choose 2 + q.choose 2) : ℕ) : Cardinal) := by
  show Cardinal.mk (Σ s : Ψ ⊕ Ψ, {lk : Fin (rk Ψ p q s) × Fin (rk Ψ p q s) // lk.2 < lk.1}) = _
  rw [Cardinal.mk_fintype, Fintype.card_sigma]
  simp only [FlagTrdeg.card_below_diagonal]
  rw [Fintype.sum_sum_type]
  simp [rk, Nat.choose_two_right]
  ring

variable {Ω : Type} [Field Ω] [CharZero Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {n : Ψ ⊕ Ψ → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (rk Ψ p q s) → E)
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω)

abbrev vals (s : Ψ ⊕ Ψ) : Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω := Matrix.of fun j l => φ s j (c s l)

def chartOf (j : FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q)) : ∀ k, idx (p := p) (q := q) J₀ n k
  | .inl k => j.1 k
  | .inr t => j.2 t

theorem flagCoord_eq_prod (j : FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q)) :
    flagCoord _ (seg x₀) φ c j = ∏ k, yv (vals φ c) x₀ ⟨k, chartOf j k⟩ := by
  rw [Fintype.prod_sum_type]
  simp only [flagCoord, yv, chartOf, seg, map_prod]
  rfl

theorem isArithVar_yv (hB : ∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * vals φ c s = 1)
    (hgen : ∀ c₀, seg x₀ c₀ ≠ 0 → ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => seg x₀ j / seg x₀ c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => seg x₀ j / seg x₀ c₀), h ≠ 0 ∧ a = g / h)
    (d : ℕ) (hx : IsArithVar (mCoordIdeal x₀) (d + 1)) :
    IsArithVar (mCoordIdeal (yv (vals φ c) x₀)) (d + Fintype.card Ψ * (p.choose 2 + q.choose 2) + 1) := by
  classical
  obtain ⟨c₀, hc₀, htr⟩ := trdeg_of_isArithVar x₀ d hx
  have hs : seg x₀ c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc₀ k
  obtain ⟨J, hJ, hfrac⟩ := CoordGen.flagCoord_generate Ω E (Ψ ⊕ Ψ) (rk Ψ p q) n _ (seg x₀) φ c c₀ hs (hgen c₀ hs) hB
  haveI : CharZero (GenField Ω (rk Ψ p q)) :=
    charZero_of_injective_algebraMap (algebraMap Ω (GenField Ω (rk Ψ p q))).injective
  have hy : ∀ k, yv (vals φ c) x₀ ⟨k, chartOf J k⟩ ≠ 0 := by
    rw [flagCoord_eq_prod] at hJ
    exact fun k => Finset.prod_ne_zero_iff.1 hJ k (Finset.mem_univ k)
  have htop := blockFnField_eq_top (yv (vals φ c) x₀) (flagCoord _ (seg x₀) φ c) J
    (fun j => by rw [flagCoord_eq_prod, flagCoord_eq_prod]; exact prod_div_mem _ _ _) hfrac
  have htop0 := blockFnField_eq_top x₀ (seg x₀) c₀ (fun j => prod_div_mem x₀ _ _) (hgen c₀ hs)
  haveI : Nonempty (K₀ ⊕ StepIx Ψ p q) := ⟨.inl hx.1.some⟩
  refine isArithVar_of_trdeg _ (chartOf J) hy _ ?_
  rw [htop, trdeg_top, trdeg_genField, ← trdeg_top (G := Ω), ← htop0, htr, mk_genIx]
  push_cast
  rfl

end Main

theorem isArithVar_flagModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d hF hx
  exact isArithVar_yv φ (cc 𝔐 bW bO) x₀ hF.2.2.2
    (fun c₀ hc₀ => FracChart.exists_eq_div_adjoin 𝔐.X Ω 𝔐.ξ _ (seg x₀) c₀ 𝔐.tie hc₀) d hx

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberTelescoping
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def positionPerm {n : ℕ} (m : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' m).symm

theorem positionPerm_last {n : ℕ} (m : Fin (n + 1)) : positionPerm m (Fin.last n) = m := by
  simp [positionPerm]

theorem positionPerm_castSucc {n : ℕ} (m : Fin (n + 1)) (j : Fin n) :
    positionPerm m (Fin.castSucc j) = m.succAbove j := by
  simp [positionPerm]

def word {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) : Fin (n + 1) → HermLine ι :=
  fun j => if (j : ℕ) < m then a else if (j : ℕ) < k then a₀ else A'

theorem word_comp_low {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) (hm : m < n + 1) (hk : m < k) :
    word (n := n) a a₀ A' k m ∘ positionPerm ⟨m, hm⟩ = Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀ := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [word, positionPerm_last, hk]
  | cast i =>
    simp only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]
      simp [h]
    · rw [Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]
      have h1 : ¬ (i : ℕ) + 1 < m := by omega
      have h2 : ¬ (i : ℕ) < m := by omega
      simp [h1, h2]

theorem word_comp_high {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) (hm : m < n + 1) :
    word (n := n) a a₀ A' k (m + 1) ∘ positionPerm ⟨m, hm⟩ = Fin.snoc (mixWord (n := n) a a₀ A' k m) a := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [word, positionPerm_last]
  | cast i =>
    simp only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]
      have h1 : (i : ℕ) < m + 1 := by omega
      simp [h, h1]
    · rw [Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]
      have h1 : ¬ (i : ℕ) + 1 < m + 1 := by omega
      have h2 : ¬ (i : ℕ) < m := by omega
      simp [h1, h2]

theorem forall_snoc {n : ℕ} {p : HermLine ι → Prop} {L : Fin n → HermLine ι} {x : HermLine ι}
    (hL : ∀ j, p (L j)) (hx : p x) : ∀ j, p ((Fin.snoc L x : Fin (n + 1) → HermLine ι) j) := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa using hx
  | cast i => simpa using hL i

theorem cone_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    (∀ k, ∃ i, (fun p : Σ k, ι k => c p.1 * z p) ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨i, right_ne_zero_of_mul hi⟩
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem logRatio_smul {a a₀ : HermLine ι} (hd : a.a = a₀.a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (hc : ∀ k, c k ≠ 0) : logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z := by
  have hcone := cone_smul c z hc
  unfold logRatio
  by_cases h : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [if_pos (hcone.mpr h), if_pos h, a.smul c z hc, a₀.smul c z hc, hd]
    have hprod : (∏ k, ‖c k‖ ^ a₀.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [Real.log_mul hprod (a₀.pos z h).ne', Real.log_mul hprod (a.pos z h).ne']
    ring
  · rw [if_neg (fun h' => h (hcone.mp h')), if_neg h]

theorem logRatio_smooth {a a₀ : HermLine ι} (ha : IsSmoothHerm a) (ha₀ : IsSmoothHerm a₀) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.SmoothFn (logRatio a a₀) := by
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha₀
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  refine ((h0.log fun z hz => (a₀.pos z hz).ne').sub (h1.log fun z hz => (a.pos z hz).ne')).congr ?_
  intro z hz
  have hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz
  simp only [logRatio, if_pos hz']

theorem tensor_logRatio_h {a a₀ : HermLine ι}
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu)).h z = a.h z := by
  have h0 := a₀.pos z hz
  have h1 := a.pos z hz
  show a₀.h z * Real.exp (-logRatio a a₀ z) = a.h z
  rw [logRatio, if_pos hz, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h0,
    ← mul_div_assoc, mul_div_right_comm, div_self h0.ne', one_mul]

theorem word_step (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k m : ℕ)
    (hP : IsArithVar P (n + 1)) (ha : IsSmoothHerm a) (ha₀ : IsSmoothHerm a₀) (hA' : IsSmoothHerm A')
    (hd : a.a = a₀.a) (hk : k ≤ n + 1) (hm : m < k) :
    I P (n + 1) (word a a₀ A' k (m + 1)) - I P (n + 1) (word a a₀ A' k m) =
      -ptsIntegral P (pot (mixWord (n := n) a a₀ A' k m)) (logRatio a a₀) := by
  have hu : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z := fun c z hc => logRatio_smul hd c z hc
  have hMs : ∀ j, IsSmoothHerm (mixWord (n := n) a a₀ A' k m j) := fun j => by
    simp only [mixWord]
    split_ifs <;> assumption
  have hWs : ∀ r (j : Fin (n + 1)), IsSmoothHerm (word (n := n) a a₀ A' k r j) := fun r j => by
    simp only [word]
    split_ifs <;> assumption
  have hmn : m < n + 1 := lt_of_lt_of_le hm hk
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha₀
  have hlr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := logRatio_smooth ha ha₀
  have hT : IsSmoothHerm (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu)) := by
    show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => a₀.h z * Real.exp (-logRatio a a₀ z))
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
    exact h0.mul hlr.neg.exp
  have e1 : I P (n + 1) (word (n := n) a a₀ A' k (m + 1)) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) := by
    rw [← word_comp_high a a₀ A' k m hmn, hI.1 P (n + 1) _ _ hP (hWs (m + 1))]
  have e0 : I P (n + 1) (word (n := n) a a₀ A' k m) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀) := by
    rw [← word_comp_low a a₀ A' k m hmn hm, hI.1 P (n + 1) _ _ hP (hWs m)]
  have e2 : I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m)
        (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu))) := by
    refine metricLocal K ι I hI P (n + 1) _ _ hP (forall_snoc (p := IsSmoothHerm) hMs ha)
      (forall_snoc (p := IsSmoothHerm) hMs hT) ?_ ?_
    · intro j
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        show a.a = a₀.a + 0
        rw [add_zero, hd]
      | cast i => simp only [Fin.snoc_castSucc]
    · intro j z hz
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact (tensor_logRatio_h hu z hz.1).symm
      | cast i => simp only [Fin.snoc_castSucc]
  have e3 := metricChange K ι I hI P n (mixWord (n := n) a a₀ A' k m) a₀ (logRatio a a₀) hu hP hMs ha₀
    (logRatio_smooth ha ha₀)
  rw [e1, e0, e2, e3]
  ring

theorem positionTelescope : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k : ℕ), IsArithVar P (n + 1) →
      IsSmoothHerm a → IsSmoothHerm a₀ → IsSmoothHerm A' → a.a = a₀.a → k ≤ n + 1 →
      I P (n + 1) (fun j => if (j : ℕ) < k then a else A') -
          I P (n + 1) (fun j => if (j : ℕ) < k then a₀ else A') =
        -∑ i ∈ Finset.range k, ptsIntegral P (pot (mixWord (n := n) a a₀ A' k i)) (logRatio a a₀) := by
  intro K _ ι _ I hI P n a a₀ A' k hP ha ha₀ hA' hd hk
  have h1 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a else A') = word (n := n) a a₀ A' k k := by
    funext j
    by_cases h : (j : ℕ) < k <;> simp [word, h]
  have h0 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a₀ else A') = word (n := n) a a₀ A' k 0 := by
    funext j
    simp [word]
  have hs := Finset.sum_range_sub (fun r => I P (n + 1) (word (n := n) a a₀ A' k r)) k
  rw [h1, h0, ← hs, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact word_step I hI P n a a₀ A' k i hP ha ha₀ hA' hd hk (Finset.mem_range.mp hi)

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.HoloLift

variable {e : ℕ} {V : Set (Fin e → ℂ)}

def inclChart (hV : IsOpen V) [Nonempty V] : OpenPartialHomeomorph V (Fin e → ℂ) :=
  hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

theorem inclChart_source (hV : IsOpen V) [Nonempty V] : (inclChart hV).source = Set.univ := by
  simp [inclChart]

theorem inclChart_target (hV : IsOpen V) [Nonempty V] : (inclChart hV).target = V := by
  simp [inclChart]

theorem inclChart_apply (hV : IsOpen V) [Nonempty V] (y : V) : inclChart hV y = y := by
  simp [inclChart]

theorem val_inclChart_symm (hV : IsOpen V) [Nonempty V] {w : Fin e → ℂ} (hw : w ∈ V) :
    (((inclChart hV).symm w : V) : Fin e → ℂ) = w := by
  have h := (inclChart hV).right_inv (x := w) (by rw [inclChart_target]; exact hw)
  rwa [inclChart_apply] at h

theorem eventually_val_inclChart_symm (hV : IsOpen V) [Nonempty V] {w : Fin e → ℂ} (hw : w ∈ V) :
    ∀ᶠ w' in 𝓝 w, (((inclChart hV).symm w' : V) : Fin e → ℂ) = w' := by
  filter_upwards [hV.mem_nhds hw] with w' hw' using val_inclChart_symm hV hw'

def inclAtlas (hV : IsOpen V) [Nonempty V] : FinHolAtlas e V where
  n := 1
  chart _ := inclChart hV
  cover x := ⟨0, by rw [inclChart_source]; trivial⟩
  holo j k := by
    rintro w ⟨hw, -⟩
    rw [inclChart_target] at hw
    refine analyticAt_id.congr ?_
    filter_upwards [eventually_val_inclChart_symm hV hw] with w' hw'
    simp only [Function.comp, inclChart_apply, hw', id]

end GlobalTheory.CompanionTheory.Ar.PB.HoloLift


open GlobalTheory.CompanionTheory.Ar.PB.HoloLift in
theorem GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D e : ℕ) (R : AnLogRes P J D), J = ⊤ → ∀ (V : Set (Fin e → ℂ)) (μ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (g : (Fin e → ℂ) → R.X), IsOpen V → (∀ q, AnalyticOnNhd ℂ (fun u => μ u q) V) → (∀ u ∈ V, SameOrbit (R.lift (g u) (g u)) (μ u)) → ContinuousOn g V ∧ ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ g) (V ∩ g ⁻¹' (R.A.chart k).source) := by
  intro K _ ι _ P J D e R hJ V μ g hV hμ hg
  subst hJ
  rcases V.eq_empty_or_nonempty with rfl | hne
  · refine ⟨continuousOn_empty _, fun k w hw => ?_⟩
    exact absurd hw.1 (Set.notMem_empty w)
  haveI : Nonempty V := hne.to_subtype
  let B : FinHolAtlas e V := inclAtlas hV
  let Vf : V → Set V := fun _ => Set.univ
  let μf : V → V → (Σ k, ι k) → ℂ := fun _ u => μ u
  let h : V → R.X := fun y => g y
  have hVo : ∀ y, IsOpen (Vf y) := fun _ => isOpen_univ
  have hVm : ∀ y, y ∈ Vf y := fun _ => Set.mem_univ _
  have hμf : ∀ y q, B.HoloOn (Vf y) fun u => μf y u q := by
    rintro y q j w ⟨hw, -⟩
    have hw' : w ∈ V := by simpa [B, inclAtlas, inclChart_target] using hw
    refine (hμ q w hw').congr ?_
    filter_upwards [eventually_val_inclChart_symm hV hw'] with w' h'
    simp only [Function.comp, μf, B, inclAtlas, h']
  have hc : ∀ y y', ∀ u ∈ Vf y ∩ Vf y', SameOrbit (μf y u) (μf y' u) := fun _ _ u _ =>
    Proj.orbit_trans (Proj.orbit_symm (hg u u.2)) (hg u u.2)
  have hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μf y y) := fun y => hg y y.2
  have hnz : ∀ y k, ∃ i, μf y y ⟨k, i⟩ ≠ 0 := fun y k => by
    obtain ⟨i, hi⟩ := (R.mem (h y) (h y) (R.mem_U _)).1 k
    exact ⟨i, Proj.orbit_ne (hh y) hi⟩
  have hcont : Continuous h := CovMap.continuous_of_orbit_of_ne R B hVo hVm hμf hnz hc hh
  refine ⟨continuousOn_iff_continuous_restrict.2 hcont, fun k w hw => ?_⟩
  have hA := Proj.analytic_of_orbit R B hVo hVm hμf hc hh hcont (0 : Fin 1) k
  have hmem : w ∈ (B.chart (0 : Fin 1)).target ∩
      (B.chart (0 : Fin 1)).symm ⁻¹' (h ⁻¹' (R.A.chart k).source) := by
    refine ⟨by simpa [B, inclAtlas, inclChart_target] using hw.1, ?_⟩
    have e1 := val_inclChart_symm hV hw.1
    show g (((inclChart hV).symm w : V) : Fin e → ℂ) ∈ (R.A.chart k).source
    rw [e1]
    exact hw.2
  refine (hA w hmem).congr ?_
  filter_upwards [eventually_val_inclChart_symm hV hw.1] with w' h'
  show R.A.chart k (g (((inclChart hV).symm w' : V) : Fin e → ℂ)) = R.A.chart k (g w')
  rw [h']
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshDoublePositivePotential
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos

theorem isPsh_add_zero_add (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    IsPsh A (Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ) := by
  unfold ReciprocityTheory.AnForm.M.IsPsh
  intro x j y hy w
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
  have hfun : ((Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ).φ x ∘ (A.chart j).symm) =
      fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show Θ.φ x _ + 0 + Θ.φ x _ = (2 : ℝ) • Θ.φ x _
    rw [smul_eq_mul]
    ring
  have hlevi : ∀ z v, ReciprocityTheory.AnForm.levi (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) z v =
      2 * ReciprocityTheory.AnForm.levi (Θ.φ x ∘ (A.chart j).symm) z v := by
    intro z v
    unfold ReciprocityTheory.AnForm.levi
    have h1 : fderiv ℝ (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) =
        (2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm) := fderiv_const_smul_field (2 : ℝ)
    have h2 : fderiv ℝ ((2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) =
        (2 : ℝ) • fderiv ℝ (fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) := fderiv_const_smul_field (2 : ℝ)
    rw [h1, h2]
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfun, hlevi]
  by_cases hw : w = 0
  · subst hw
    simp [ReciprocityTheory.AnForm.levi]
  · exact mul_nonneg (by norm_num) (hpos x j y hy' w hw).le

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos
end

