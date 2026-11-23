module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.BasicNotions Formalism.MainNotions

section Mean

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

theorem htI2et_of_pt (d : Data K ι Ω WT A)
    (hpt : ∀ sg, Real.log (d.supN sg (d.n1 • d.wde) d.et) / d.i ≤ d.Pet) : d.HeightIntegralEstimateTrivialPlace := by
  unfold Data.HeightIntegralEstimateTrivialPlace meanK
  have hN : (0 : ℝ) < (Fintype.card (K →+* ℂ) : ℝ) := by
    first
    | exact_mod_cast Fintype.card_pos
    | (haveI : Nonempty (K →+* ℂ) := ⟨(IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom⟩
       exact_mod_cast Fintype.card_pos)
  rw [div_right_comm, Finset.sum_div, div_le_iff₀ hN]
  calc ∑ sg, (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) sg / (d.i : ℝ)
      ≤ ∑ _sg : K →+* ℂ, d.Pet := Finset.sum_le_sum (fun sg _ => hpt sg)
    _ = d.Pet * (Fintype.card (K →+* ℂ) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end Mean

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def recNrm {σ : c.F →+* ℂ} {rU : ℕ} (U : Unf Xo c σ rU) (xR : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c)
    (k : U.Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ rU) : ℝ :=
  lieFac Dw xR a * (U.X k).pnorm (laU U a n k) (rdU U f k) x

def I2AtFramePoints {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul Xo c)
    (uL : WtR E) (th tableLineDegreeFive DF cc : ℝ) : Prop :=
  ∀ σ, GoodEmb c σ → ∀ (k : (U σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU), x ∈ ((U σ).X k).dom →
    -Real.log (Real.sqrt (∑ j, recNrm (U σ) xR uL.1 uL.2 (wR j) k x ^ 2)) ≤
      tableLineDegreeFive * DF + cc * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x

def NrmTieU (h : GenFrEx Xo c) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul Xo c) (uL : WtR E)
    (etR : Rul Xo c) (uet : WtR E) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ σ, GoodEmb c σ ∧ ∃ (k : (U σ).Comp)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU), x ∈ ((U σ).X k).dom ∧
    (∀ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P = recNrm (U σ) xR uL.1 uL.2 (wR j) k x) ∧
    nrmC fn (yP Z) (wtZ uet.1 uet.2) (valC h uet.1 uet.2 etR Z) P ≤ recNrm (U σ) xR uet.1 uet.2 etR k x

variable [Fintype (Comp Xo c)]

theorem supN_dataOf_nonneg (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ) (sg : c.F →+* ℂ) (G : WTZ E) (x : ∀ Z : Comp Xo c, AC Z) :
    0 ≤ (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).supN sg G x := by
  unfold Data.supN
  apply Real.iSup_nonneg
  intro p
  unfold dataOf nrmC
  dsimp only
  first
  | positivity
  | exact (rfl : (0 : ℕ) = 0)

theorem htI2be_of (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR th : ℝ)
    (hi : 0 < i) (hcc : 0 ≤ cc) (hfn : FnNe Xo c fn) (het : NZAt h etR)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (htie : NrmTieU h fn yP U xR wR uL etR uet) (hI2 : I2AtFramePoints U xR wR uL th tableLineDegreeFive DF cc)
    (harch : ∀ σ, GoodEmb c σ → ∀ (k : (U σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU),
      x ∈ ((U σ).X k).dom → recNrm (U σ) xR uet.1 uet.2 etR k x ≤
        Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x - tableLineDegreeTwo))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralBoundEstimate := by
  intro Z P
  obtain ⟨σ, hσ, k, x, hx, hw, he⟩ := htie Z P
  have h1 := hI2 σ hσ k x hx
  have h2 := harch σ hσ k x hx
  show -Real.log (Real.sqrt (∑ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P ^ 2)) ≤
    tableLineDegreeFive * DF + cc / (i : ℝ) * (-Real.log (nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P)) +
      cc * tableLineDegreeTwo
  have hbe : (∑ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P ^ 2) =
      ∑ j, recNrm (U σ) xR uL.1 uL.2 (wR j) k x ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [hw j]
  rw [hbe]
  have hm := valC_mem h uet.1 uet.2 etR Z
  rw [huet] at hm
  have hpos : 0 < nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P :=
    nrmC_pos fn (yP Z) hfn P hm (valC_ne_zero (het Z))
  have he' : nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P ≤
      recNrm (U σ) xR uet.1 uet.2 etR k x := by
    rw [← huet]; exact he
  have hlog := Real.log_le_log hpos (he'.trans h2)
  rw [Real.log_exp] at hlog
  set e := Real.log (nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P)
  set φ := ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x
  have hi' : (0 : ℝ) < i := Nat.cast_pos.2 hi
  have h3 : φ - tableLineDegreeTwo ≤ -e / i := by
    rw [le_div_iff₀ hi']; nlinarith
  have key : cc * φ ≤ cc / (i : ℝ) * (-e) + cc * tableLineDegreeTwo :=
    calc cc * φ = cc * (φ - tableLineDegreeTwo) + cc * tableLineDegreeTwo := by ring
      _ ≤ cc * (-e / i) + cc * tableLineDegreeTwo := by gcongr
      _ = cc / (i : ℝ) * (-e) + cc * tableLineDegreeTwo := by ring
  linarith

end Gen

section Rec

variable {D : D7} {T : Top D} (hL : LawsP T)

variable (j : ℕ) [IsCMField D.host.E] [Fintype (Comp (T.Q.Xo j) T.Q.c)]

end Rec

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.TieInst
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def wRat (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : Fin G.N) :
    ↥(Frac0 (xplus X E hM) la G.w) :=
  ⟨frac (xplus X E hM) la G.w 1 (emb (xplus X E hM) la G.N (X.inc wL (G.w k))),
    Algebra.subset_adjoin (frac_mem_Hfr (xplus X E hM) la G.w (by
      rw [add_zero_weight_one_eq]; exact emb_mem_Vw (xplus X E hM) la G.N wL (G.w k)))⟩

def GenericSectionMinimumIntegral (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) →
    IsReduced (OsK (xplus X E hM) la G.w) → ∀ ζ : PtsG G la, (∀ k, 0 ≤ ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k))) ∧
    ∃ k, ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k)) = 0

lemma nval_nonneg_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : 0 ≤ nval T.V e z ↔ 0 ≤ nval T.V 1 z := by
  by_cases hz : z = 0
  · simp [hz, nval_zero]
  · rw [nval_of_ne hz, nval_of_ne hz, EReal.coe_nonneg, EReal.coe_nonneg]
    have : (0 : ℝ) < e := by exact_mod_cast he
    constructor
    · intro h; simpa using (div_nonneg_iff.1 h).elim (fun h' => h'.1) (fun h' => absurd h'.2 (not_le.2 this))
    · intro h; exact div_nonneg (by simpa using h) this.le

lemma nval_eq_zero_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : nval T.V e z = 0 ↔ nval T.V 1 z = 0 := by
  by_cases hz : z = 0
  · simp [hz, nval_zero]
  · rw [nval_of_ne hz, nval_of_ne hz]
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    simp [div_eq_zero_iff, this]

theorem depthAtSec_of {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (S : Scal B)
    (hspan : SpanW (xplus X E hM) G.w S) (h0 : GenericSectionMinimumIntegral G la)
    (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hred : IsReduced (OsK (xplus X E hM) la G.w)) (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ))
    (ζ : PtsG G la) :
    (xplus X E hM).depth S.sW wL la (.inr (y ζ)) =
      nval (hs ζ).T.V (ep (unifO (xplus X E hM) la G.N) ζ) ((hs ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)) := by
  set h := hs ζ with hh
  have hb : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) ≠ 0 := h.s0.ne_zero
  have he := h.ep_pos

  have hwk : ∀ k, E.vAt' la (y ζ) (X.inc wL (G.w k)) =
      nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)) +
        nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k : Lw (xplus X E hM) la G.w)) := by
    intro k
    rw [h.hv, ← nval_mul]
    congr 1
    show _ = _ * h.lift (frac (xplus X E hM) la G.w 1 _)
    rw [h.lift_frac, pow_one, mul_comm, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  have hord : ∀ k, nval h.T.V 1 (h.lift (wRat G la k : Lw (xplus X E hM) la G.w)) =
      toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k))) :=
    fun k => (h.ord (wRat G la k)).symm
  obtain ⟨hint, k0, hk0⟩ := h0 hfd hred ζ
  have hnn : ∀ k, 0 ≤ nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k : Lw _ la G.w)) := by
    intro k
    rw [nval_nonneg_iff he, hord]
    have := hint k
    generalize ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k)) = o at this ⊢
    cases o with
    | top => simp [toE]
    | coe n => simp only [toE]; exact_mod_cast (WithTop.coe_nonneg.1 this)
  have hz0 : nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k0 : Lw _ la G.w)) = 0 := by
    rw [nval_eq_zero_iff he, hord, hk0]
    show toE ((0 : ℤ) : WithTop ℤ) = 0
    simp [toE]
  apply le_antisymm
  · refine (iInf₂_le (G.w k0) (by rw [← hspan]; exact Submodule.subset_span ⟨k0, rfl⟩)).trans_eq ?_
    show E.vAt' la (y ζ) (X.inc wL (G.w k0)) = _
    rw [hwk, hz0, add_zero]
  · refine le_iInf₂ fun F hF => ?_
    rw [← hspan] at hF
    show _ ≤ E.vAt' la (y ζ) (X.inc wL F)
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [hwk]
      exact le_add_of_nonneg_right (hnn k)
    | zero => rw [map_zero, E.vAt'_zero]; exact le_top
    | add x z _ _ hx hz =>
      rw [map_add (f := _)]
      exact (le_min hx hz).trans (E.vAt'_add la _ _ _)
    | smul a x _ hx =>
      by_cases ha : ((a : 𝓞 B.KO) : B.KO) = 0
      · have : a = 0 := by exact_mod_cast ha
        rw [this, zero_smul, map_zero, E.vAt'_zero]; exact le_top
      · rw [← algebraMap_smul B.KO a x, map_smul, E.vAt'_smul la _ _ _ ha]
        exact le_add_of_nonneg_of_le (by exact_mod_cast vAdd_int_nonneg la ha) hx

end Formalism.L2.Pj
end
end

