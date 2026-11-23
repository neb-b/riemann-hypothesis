module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0156
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddGen
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.CutMP.JA.BStar Formalism.QuantumDeterminants
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def orderZeroDifferentialOperator (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (c ca : Coef S v)
    (hadj : ∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')) :
    B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) :=
  [⟨c, ca, [], fun X hX => by simp at hX, hadj⟩]

variable {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {c ca : Coef S v}
  {hadj : ∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')}

theorem order_zero_operator_apply (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    B.opApply (orderZeroDifferentialOperator S v c ca hadj) J = fun g => c g (J g) := by
  funext g
  simp only [B.opApply, orderZeroDifferentialOperator, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  first
    | rfl
    | simp [B.Rw]

theorem order_zero_operator_adjoint (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    B.opAdj (orderZeroDifferentialOperator S v c ca hadj) J = fun g => ca g (J g) := by
  funext g
  first
    | (simp [B.opAdj, orderZeroDifferentialOperator]; done)
    | (simp [B.opAdj, orderZeroDifferentialOperator]; rfl)
    | rfl

theorem order_zero_operator_order : B.opOrder (orderZeroDifferentialOperator S v c ca hadj) = 0 := by
  first
    | rfl
    | simp [B.opOrder, orderZeroDifferentialOperator]

end gen

section eqv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))} {v : Fin S.f}

theorem eqv_left {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {n : B.Mat S.G.k S.G.r} (hn : n ∈ Nset S.G.k S.G.r) (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (n * g) X = c g X := by
  have hp : (T v).base.inSS ((Matrix.of.symm 1, Matrix.of.symm n⁻¹), (Matrix.of.symm 1, Matrix.of.symm 1)) :=
    ⟨by simpa only [Equiv.apply_symm_apply] using P.BigCellZetaMinors.one_uw (T v).base.z, by simpa only [Equiv.apply_symm_apply] using WeylGroupFacts.mem_n_inv hn,
      by simpa only [Equiv.apply_symm_apply] using P.BigCellZetaMinors.one_uw (T v).base.z', by simpa only [Equiv.apply_symm_apply] using WeylGroupFacts.mem_n_one⟩
  have h := he _ hp g hg X
  have hu : IsUnit n.det := WeylGroupFacts.isUnit_of_uh hn.1
  simp only [Equiv.apply_symm_apply, inv_one, (T v).base.π_rep.1, (T v).base.π'_rep.1, B.sgs,
    Matrix.nonsing_inv_nonsing_inv n hu, Matrix.one_mul, Matrix.mul_one] at h
  simpa [ContinuousLinearMap.one_def] using h.symm

theorem eqv_right {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {n : B.Mat S.G.k S.G.r} (hn : n ∈ Nset S.G.k S.G.r) (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (g * n) X = c g X := by
  have hp : (T v).base.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm n)) :=
    ⟨by simpa only [Equiv.apply_symm_apply] using P.BigCellZetaMinors.one_uw (T v).base.z, by simpa only [Equiv.apply_symm_apply] using WeylGroupFacts.mem_n_one,
      by simpa only [Equiv.apply_symm_apply] using P.BigCellZetaMinors.one_uw (T v).base.z', by simpa only [Equiv.apply_symm_apply] using hn⟩
  have h := he _ hp g hg X
  simp only [Equiv.apply_symm_apply, inv_one, (T v).base.π_rep.1, (T v).base.π'_rep.1, B.sgs,
    Matrix.one_mul, Matrix.mul_one] at h
  simpa [ContinuousLinearMap.one_def] using h.symm

theorem eqv_uw {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {h h' : B.Mat S.G.k S.G.r} (hh : h ∈ UWset S.G.k S.G.r (T v).base.z) (hh' : h' ∈ UWset S.G.k S.G.r (T v).base.z')
    (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (h * g * h') (((T v).base.π h).comp (X.comp ((T v).base.π' h'))) =
      ((T v).base.π h).comp ((c g X).comp ((T v).base.π' h')) := by
  have hp : (T v).base.inSS ((Matrix.of.symm h, Matrix.of.symm 1), (Matrix.of.symm h'⁻¹, Matrix.of.symm 1)) :=
    ⟨by simpa only [Equiv.apply_symm_apply] using hh, by simpa only [Equiv.apply_symm_apply] using WeylGroupFacts.mem_n_one,
      by simpa only [Equiv.apply_symm_apply] using P.BigCellInversePair.uw_inv hh', by simpa only [Equiv.apply_symm_apply] using WeylGroupFacts.mem_n_one⟩
  have hg' : h * g * h' ∈ B.GV S.G.k S.G.r := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hh.1 hg) hh'.1
  have e := he _ hp (h * g * h') hg' X
  have hu' : IsUnit h'.det := WeylGroupFacts.isUnit_of_uh hh'.1
  have hs : B.sgs ((Matrix.of.symm h, Matrix.of.symm 1), (Matrix.of.symm h'⁻¹, Matrix.of.symm 1)) (h * g * h') = g := by
    simp only [B.sgs, Equiv.apply_symm_apply, inv_one, Matrix.mul_one]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hh.1), Matrix.one_mul]
  rw [hs] at e
  simpa only [Equiv.apply_symm_apply, Matrix.nonsing_inv_nonsing_inv h' hu'] using e

theorem equivariant_coefficient_preserves_forms {c : Coef S v} (hc : B.CkOn ⊤ (B.GPos (T v).base) c) (he : EqvC S T v c)
    {J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} (hJ : J ∈ smoothFormsPositiveCone S T v) :
    (fun g => c g (J g)) ∈ smoothFormsPositiveCone S T v := by
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U1, J', hU1, hg1, hJ', hJeq⟩ := hS g₀ hg₀
    obtain ⟨U2, c', hU2, hg2, hc', hceq⟩ := hc g₀ ⟨hg₀.1.1, hg₀.2.1⟩
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun g => ContinuousLinearMap.restrictScalarsL ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v))
          (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) ℝ ℝ (c' g)) (U1 ∩ U2) :=
      (ContinuousLinearMap.restrictScalarsL ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v))
          (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) ℝ ℝ).contDiff.comp_contDiffOn (hc'.mono Set.inter_subset_right)
    refine ⟨U1 ∩ U2, fun g => c' g (J' g), hU1.inter hU2, ⟨hg1, hg2⟩,
      h2.clm_apply (hJ'.mono Set.inter_subset_left), ?_⟩
    intro g hg hgl
    simp only
    rw [hJeq g hg.1 hgl, hceq g hg.2 hgl.1]
  · intro g hg n hn
    simp only
    rw [hL g hg n hn, ContinuousLinearMap.map_smul, eqv_left he hg.1.1 hn.1]
  · intro g hg n hn
    simp only
    rw [hR g hg n hn, ContinuousLinearMap.map_smul, eqv_right he hg.1.1 hn.1]
  · intro g hg h hh h' hh'
    simp only
    rw [hU g hg h hh h' hh', eqv_uw he hg.1.1 hh hh']

end eqv

section transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem trJ_of_fibMat (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hFr : IsFrame S T v e) (c : Coef S v)
    (V : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)
    (hV : FibMat S T v e c V) (b : A (D.parOf S v) (DQ (D.parOf S v)))
    (β : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → (DQ (D.parOf S v)).R)
    (hβ : ∀ ρ π, b ρ π = (DQ (D.parOf S v)).fnP (β ρ π) (cjD (D.parOf S v) (β ρ π)))
    (hβV : ∀ ρ π q, evD (D.parOf S v) q (β ρ π) = V ρ π q)
    (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hJ : J ∈ smoothFormsPositiveCone S T v) :
    actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (fun g => c g (J g)) := by
  funext ρ
  set X := actA (D.parOf S v) b (trJ S T v e J) ρ with hXdef
  have hsm : ∀ π (q : Qp (D.parOf S v).r (D.parOf S v).TT), evQ (D.parOf S v) (trJ S T v e J π) q =
      ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) := fun π q =>
    congrFun (En.toSm_val_of_mem (D.parOf S v) (En.trace_smoothness E Wp Wq S T v hPl e hFr J hJ π)) q
  have hw : (fun q : Qp (D.parOf S v).r (D.parOf S v).TT =>
      ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (c (B.gq (T v).base q.1) (J (B.gq (T v).base q.1))))) =
      (X : Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) := by
    funext q
    have hX := actA_fm_apply (D.parOf S v) hβ (trJ S T v e J) ρ q
    change _ = evQ (D.parOf S v) X q
    rw [hX]
    simp only [hsm, hβV]
    have hfib := En.fibre_membership_holds E Wp Wq S T v hPl J hJ q.1 q.2
    have hspan := (hFr.2 q.1.2 q.2.2).2.2 _ hfib
    have hcJ : c (B.gq (T v).base q.1) (J (B.gq (T v).base q.1)) =
        ∑ π, inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) •
          c (B.gq (T v).base q.1) (e π q.1.2) := by
      conv_lhs => rw [hspan]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [ContinuousLinearMap.map_smul]
    rw [hcJ, En.hsVec_sum_smul, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [inner_smul_right, hV q.1 q.2 ρ π]
    ring
  unfold trJ
  beta_reduce
  rw [hw]
  unfold MA.toSm
  rw [dite_eq_left X.2]

theorem real_to_bounded_holds : RealToBdd := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hPl e Cb c ca V b hFr hR hb
  obtain ⟨hadj, hc, hca, he, hea, hbc, hbca, hV⟩ := hR
  choose β hβ hβV using hb
  refine ⟨orderZeroDifferentialOperator S v c ca hadj, order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩
  · intro Tm hTm
    simp only [orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    exact ⟨hc, hca⟩
  · intro p hp f _ g hg
    rw [order_zero_operator_apply, order_zero_operator_apply]
    exact he p hp g hg.1 _
  · intro Tm hTm ε hε m
    simp only [orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    obtain ⟨C1, h1⟩ := hbc ε hε m
    obtain ⟨C2, h2⟩ := hbca ε hε m
    refine ⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · rw [order_zero_operator_apply]; exact equivariant_coefficient_preserves_forms hc he hJ
  · rw [order_zero_operator_adjoint]; exact equivariant_coefficient_preserves_forms hca hea hJ
  · rw [order_zero_operator_apply]
    exact trJ_of_fibMat S T v hPl e hFr c V hV b β hβ hβV J hJ

end transfer

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjPair
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hsVec_zero' {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] : B.hsVec (0 : W →L[ℂ] V) = 0 := by
  change Formalism.FourierDecayAlt.P.JFxI.hsVecL 0 = 0
  exact map_zero _

theorem group_action_pairing_holds : GAPair := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr X Y F F' hX hY hF hF' hae
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  set Qs := MA.Qset (D.parOf S v).r (D.parOf S v).TT with hQs
  have hQm : MeasurableSet Qs := (MA.Qset_open _ _).measurableSet
  set W : (Fin S.G.r → ℂ) × ℂ → ℝ := bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') with hWdef
  have hW0 : ∀ x, 0 ≤ W x := fun x => Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ x

  have hW : ∀ x ∈ Qs, W x = Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
    intro x hx
    have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
      rw [hTT]; exact le_of_lt hx.2
    rw [hWdef]
    unfold bcWeight
    rw [if_pos hle]
    unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
    rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
      have := l.isLt
      simp only [MA.Mdim]; omega
    have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
    have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
    rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
      pow_succ]
    field_simp

  have hval : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v), ∀ ρ,
      ((trJ S T v e J ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) =
        fun q => ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq Db q.1))) := fun J hJ ρ =>
    toSm_val_of_mem (D.parOf S v) (trace_smoothness E Wp Wq S T v hplace e hFr J hJ ρ)

  have hR : ∀ ρ, MA.ip0 (trJ S T v e X ρ) (trJ S T v e Y ρ) =
      ∫ x in Qs, ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x))))) := by
    intro ρ
    unfold MA.ip0
    rw [Formalism.FourierDecayAlt.P.MAx2.Adj.integral_base_measure]
    have hz : ∀ x, x ∉ Qs → ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
        MA.ext (r := (D.parOf S v).r) (TT := (D.parOf S v).TT)
          (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT =>
            ((trJ S T v e X ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q *
            conj (((trJ S T v e Y ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
              MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q)) x = 0 := by
      intro x hx
      rw [Formalism.FourierDecayAlt.P.MAx2.Adj.ext_out _ hx, mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine setIntegral_congr_fun hQm fun x hx => ?_
    simp only [MA.ext, hval X hX, hval Y hY]
    rw [dite_eq_left (show x ∈ MA.Qset S.G.r (D.parOf S v).TT from hx)]
    rw [hW x hx, map_mul, Complex.conj_ofReal]
    have hw := wq_pos (k := S.G.k) hx
    have hs : ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) *
        ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) = ((MA.wq S.G.k x (D.parOf S v).TT : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw.le]
    push_cast
    linear_combination ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))) * hs

  have hcont : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v),
      ContinuousOn (fun x => B.hsVec (J (B.gq Db x))) Qs := fun J hJ =>
    hsVec_contDiff.continuous.comp_continuousOn (jgq_contDiffOn S T v hplace hJ).continuousOn
  have heC : ∀ ρ, ContinuousOn (fun x : MA.E S.G.r => B.hsVec (e ρ x.2)) Qs := fun ρ =>
    hsVec_contDiff.continuous.comp_continuousOn
      ((hFr.1 ρ).continuousOn.comp continuous_snd.continuousOn fun x hx => hx.2)

  have hXc : ContinuousOn (fun x => X (B.gq Db x)) Qs := (jgq_contDiffOn S T v hplace hX).continuousOn
  set O : Set ((Fin S.G.r → ℂ) × ℂ) := Qs ∩ (fun x => X (B.gq Db x)) ⁻¹' {0}ᶜ with hO
  have hOo : IsOpen O := hXc.isOpen_inter_preimage (MA.Qset_open _ _) isOpen_compl_singleton
  have hOm : MeasurableSet O := hOo.measurableSet
  have hOQ : O ⊆ Qs := Set.inter_subset_left

  obtain ⟨-, -, -, ⟨C, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db
    (B.AB S.G.k S.G.r) le_rfl
  have h54 : ∀ G : GFn S v, B.InCC (B.AB S.G.k S.G.r) 5 G → ∃ c, B.CCle (B.AB S.G.k S.G.r) 4 G c := by
    rintro G ⟨c, hck, hb⟩
    exact ⟨c, Formalism.FourierDecayAlt.P.B5.ckOn_mono (by norm_num) hck, fun u w hu hw hl g hg => hb u w hu hw (by omega) g hg⟩
  obtain ⟨c₁, hc₁⟩ := h54 F hF
  obtain ⟨c₂, hc₂⟩ := h54 F' hF'
  obtain ⟨hN, hN', -⟩ := hB1 F F' c₁ c₂ hF hF' hc₁ hc₂
  unfold B.normSq jNormSq at hN hN'

  have hU : ∀ (Z G : GFn S v), Z ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) →
      (∫⁻ p, ENNReal.ofReal (W p * ‖B.hsVec (B.JF Db G (B.gq Db p))‖ ^ 2)) ≠ ⊤ →
      (∀ᵐ x ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)), x ∈ O → Z (B.gq Db x) = B.JF Db G (B.gq Db x)) →
      IntegrableOn (fun x => W x * ‖B.hsVec (Z (B.gq Db x))‖ ^ 2) O := by
    intro Z G hZ hNG hZG
    refine ⟨((Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _).aestronglyMeasurable).mul
      ((((hcont Z hZ).mono hOQ).norm.pow 2).aestronglyMeasurable hOm), ?_⟩
    refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => mul_nonneg (hW0 x) (sq_nonneg _))).2 ?_
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hNG)
    calc ∫⁻ x in O, ENNReal.ofReal (W x * ‖B.hsVec (Z (B.gq Db x))‖ ^ 2)
        = ∫⁻ x in O, ENNReal.ofReal (W x * ‖B.hsVec (B.JF Db G (B.gq Db x))‖ ^ 2) := by
          refine setLIntegral_congr_fun_ae hOm ?_
          filter_upwards [hZG] with x hx hxO
          rw [hx hxO]
      _ ≤ ∫⁻ x, ENNReal.ofReal (W x * ‖B.hsVec (B.JF Db G (B.gq Db x))‖ ^ 2) := setLIntegral_le_lintegral O _
  have hUX := hU X F hX hN (by filter_upwards [hae] with x hx hxO; exact (hx (hOQ hxO)).1)
  have hUY := hU Y F' hY hN' (by filter_upwards [hae] with x hx hxO; exact (hx (hOQ hxO)).2 hxO.2)
  have hInt : ∀ ρ, IntegrableOn (fun x => ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))))) O := by
    intro ρ
    refine Integrable.mono' (hUX.add hUY) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)).aestronglyMeasurable).mul
        (((((heC ρ).inner (hcont X hX)).mul ((heC ρ).inner (hcont Y hY)).star).mono hOQ).aestronglyMeasurable hOm)
    · refine ae_restrict_of_forall_mem hOm fun x hxO => ?_
      have hx := hOQ hxO
      have he1 : ‖B.hsVec (e ρ x.2)‖ ≤ 1 := by
        have h1 : inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (e ρ x.2)) = (1 : ℂ) := by
          simpa using (hFr.2 x.2 hx.2).2.1 ρ ρ
        rw [inner_self_eq_norm_sq_to_K] at h1
        have h2' : ((‖B.hsVec (e ρ x.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
          rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
        have h2 : ‖B.hsVec (e ρ x.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
        nlinarith [norm_nonneg (B.hsVec (e ρ x.2))]
      have ha : ∀ J : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J (B.gq Db x)))‖ ≤ ‖B.hsVec (J (B.gq Db x))‖ := fun J =>
        (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (J (B.gq Db x)))])
      have hn1 := ha X
      have hn2 := ha Y
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 x), RCLike.norm_conj]
      have hp : ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x)))‖ *
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))‖ ≤
            ‖B.hsVec (X (B.gq Db x))‖ ^ 2 + ‖B.hsVec (Y (B.gq Db x))‖ ^ 2 := by
        nlinarith [norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x)))),
          norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))),
          norm_nonneg (B.hsVec (X (B.gq Db x))), norm_nonneg (B.hsVec (Y (B.gq Db x))),
          sq_nonneg (‖B.hsVec (X (B.gq Db x))‖ - ‖B.hsVec (Y (B.gq Db x))‖)]
      calc W x * (‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x)))‖ *
            ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))‖)
          ≤ W x * (‖B.hsVec (X (B.gq Db x))‖ ^ 2 + ‖B.hsVec (Y (B.gq Db x))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hp (hW0 x)
        _ = W x * ‖B.hsVec (X (B.gq Db x))‖ ^ 2 + W x * ‖B.hsVec (Y (B.gq Db x))‖ ^ 2 := by ring

  have hQO : ∀ ρ, (∫ x in Qs, ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))))) =
      ∫ x in O, ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x))))) := by
    intro ρ
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQm hOQ fun x hx => ?_
    have hX0 : X (B.gq Db x) = 0 := by
      by_contra h
      exact hx.2 ⟨hx.1, h⟩
    rw [hX0, hsVec_zero', inner_zero_right, zero_mul, mul_zero]

  unfold MA.ipA
  simp_rw [hR]
  rw [Finset.sum_congr rfl fun ρ _ => hQO ρ]
  rw [← integral_finsetSum _ (fun ρ _ => hInt ρ)]
  unfold B.beta betaBig
  have hae2 : ∀ᵐ x ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)), x ∉ O →
      ((W x : ℝ) : ℂ) * inner ℂ (B.hsVec (B.JF Db F' (bigCell S.G.k S.G.r x.1 (Db.μsec x.2))))
        (B.hsVec (B.JF Db F (bigCell S.G.k S.G.r x.1 (Db.μsec x.2)))) = 0 := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero Db, hae] with x hx hxe hxO
    by_cases hxQ : x ∈ Qs
    · have hX0 : X (B.gq Db x) = 0 := by
        by_contra h
        exact hxO ⟨hxQ, h⟩
      have hJ0 : B.JF Db F (B.gq Db x) = 0 := by rw [← (hxe hxQ).1]; exact hX0
      change ((W x : ℝ) : ℂ) * inner ℂ (B.hsVec (B.JF Db F' (B.gq Db x))) (B.hsVec (B.JF Db F (B.gq Db x))) = 0
      rw [hJ0, hsVec_zero', inner_zero_right, mul_zero]
    · rcases hx with hx | hx
      · exfalso
        apply hxQ
        refine ⟨hx.1, ?_⟩
        have h2 := hx.2
        rw [hTT] at h2
        exact h2
      · rw [show W x = 0 from hx]; simp
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hae2]
  refine setIntegral_congr_ae hOm ?_
  filter_upwards [hae] with x hxe hxO
  rw [← Finset.mul_sum]
  congr 1
  have hXF := (hxe (hOQ hxO)).1
  have hYF := (hxe (hOQ hxO)).2 hxO.2
  have hXf := (hFr.2 x.2 (hOQ hxO).2).2.2 (X (B.gq Db x)) (fibre_membership_holds E Wp Wq S T v hplace X hX x (hOQ hxO))
  rw [← parseval (fun ρ => e ρ x.2) (X (B.gq Db x)) (Y (B.gq Db x)) hXf, hXF, hYF]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA.GA
end

