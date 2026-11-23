module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0133
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0167
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0165
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0157
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0156
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0166
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0109
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSAdj

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastVCastV
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def PointStepT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (c : ℂ) (hh : D.IsLocPt h j) (hc : D.IsLocPt (h ++ [(1, c)]) (j + 1)),
    KB.CptCoef p.T.base F → ∀ γ ∈ B.GV P.k (P.r - (j + 1)),
    KB.slv p.T F (j + 1) hj [] _ hc.2 (fun a => a.elim0) γ =
      ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
        (psi P.k (P.r - j) (p.T.bs j).z cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1) *
            star (psi P.k (P.r - j) (p.T.bs j).z' cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2))) •
          KB.slv p.T F j (by omega) [] h hh.2 (fun a => a.elim0)
            ((rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1)⁻¹ *
              mc (by omega : P.r - (j + 1) + 1 = P.r - j) c γ * rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2)
        ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1))))

theorem asm_castV_castV {k a b d : ℕ} (h1 : a = b) (h2 : b = d) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
  subst h1; subst h2; rfl

theorem castM_castM' {k a b d : ℕ} (h1 : a = b) (h2 : b = d) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by
  subst h1; subst h2; rfl

theorem sliceStep_of (hJ : JFStep) (hP : PointStepT) : KB.SliceStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h c hh hc hF γ hγ hΩ
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  have hc0 : c ≠ 0 := (hc.1 (1, c) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hT := p.hT
  have key := hJ P.k (P.r - (j + 1)) (P.r - j) e Wp Wq (p.T.bs j) (p.T.bs (j + 1))
    (by rw [levTower_bs_z_eq_castV_liftVec p.T j hj, asm_castV_castV])
    (by rw [levTower_bs_z'_eq_castV_liftVec p.T j hj, asm_castV_castV])
    (fun y => by rw [tower_π p.T j hj, lev1, castM_castM'])
    (fun y => by rw [tower_π' p.T j hj, lev1, castM_castM'])
    (hT j (by omega)).1 (hT j (by omega)).2.1 (hT (j + 1) hj).1 (hT (j + 1) hj).2.1
    (hT j (by omega)).2.2 (hT (j + 1) hj).2.2
    (KB.slv p.T F j (by omega) [] h hh.2 fun a => a.elim0)
    (KB.slv p.T F (j + 1) hj [] _ hc.2 fun a => a.elim0) c hc0
    (Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j (by omega) [] h hh hF _)
    (fun γ' hγ' => hP Wp Wq P p F j hj h c hh hc hF γ' hγ') γ hγ hΩ
  rw [key, mc, castM_castM']

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BoundedOperatorsSquareIntegrable
section
open Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem bounded_operators_square_integrable : BoundedOperatorsSquareIntegrable := by
  intro P L hTT hL b hb u hu π
  have hLaw : (MA.DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT.le
  have hPW : ∃ C, Formalism.FourierDecayAlt.P.MAx3.I4.PW b C := by
    induction hb using Submonoid.closure_induction with
    | mem x hx => exact Formalism.FourierDecayAlt.P.MAx3.I4.PW_gen hTT hL hLaw hx
    | one => exact ⟨1, Formalism.FourierDecayAlt.P.MAx3.I4.PW_one⟩
    | mul x y _ _ h1 h2 =>
      obtain ⟨C1, h1⟩ := h1
      obtain ⟨C2, h2⟩ := h2
      exact ⟨_, Formalism.FourierDecayAlt.P.MAx3.I4.PW_mul h1 h2⟩
  obtain ⟨C, hC0, Mx, hMb, hMe⟩ := hPW
  have hmeas := jd_evQ_meas P (MA.actA P b u π)
  have hL2u : ∀ π', MemLp (MA.evQ P (u π')) 2 (MA.mu0 P.r P.TT) := fun π' =>
    (memLp_two_iff_integrable_sq_norm (jd_evQ_meas P (u π'))).2 (hu π')
  have hs : MemLp (fun q => ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT) :=
    memLp_finsetSum _ fun π' _ => (hL2u π').norm
  have hg : MemLp (fun q => C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT) := hs.const_mul C
  refine (memLp_two_iff_integrable_sq_norm hmeas).1 (hg.of_le hmeas (Filter.Eventually.of_forall fun q => ?_))
  rw [hMe u q π]
  calc ‖∑ π', Mx q π π' * MA.evQ P (u π') q‖ ≤ ∑ π', ‖Mx q π π' * MA.evQ P (u π') q‖ := norm_sum_le _ _
    _ ≤ ∑ π', C * ‖MA.evQ P (u π') q‖ := Finset.sum_le_sum fun π' _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hMb q π π') (norm_nonneg _)
    _ = C * ∑ π', ‖MA.evQ P (u π') q‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖‖ := le_abs_self _

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBesselFold
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem foldCV_memB {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}
    (hcl : ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) (s : ℂ) :
    ∀ a : List C.Letter, foldCV k r s a J ∈ Q.FFl k r z z' π π' 0 Dm
  | [] => hJ
  | x :: a => hcl _ (foldCV_memB hcl hJ s a) x.2 s

theorem mem_level_zero_of_mem_group {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem JF_smul' {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (c : ℂ)
    (G : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) : B.JF D (c • G) g = c • B.JF D G g := by
  show ∫ p, JF.xiP D p • B.rho D p (c • G) g ∂D.μSS = c • ∫ p, JF.xiP D p • B.rho D p G g ∂D.μSS
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [B.rho, Pi.smul_apply, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [smul_comm]

theorem thr_budget (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀)
    (m : ℕ) (hm : m ≤ (2 * r + k + 1) * (N + 1)) :
    JF.TransportedAlt k r (A₀ - 2 * ((r : ℝ) + 1) * (((2 * r + k + 1) * (N + 1) : ℕ) : ℝ)) m := by
  unfold JF.TransportedAlt
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  set R : ℝ := (r : ℝ) + 1 with hRdef
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  have hMc : (((2 * r + k + 1) * (N + 1) : ℕ) : ℝ) = n * ((N : ℝ) + 1) := by rw [hn]; push_cast; ring
  have hmr : (m : ℝ) ≤ n * ((N : ℝ) + 1) := by rw [← hMc]; exact_mod_cast hm
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; linarith
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hR1 : (1 : ℝ) ≤ R := by rw [hRdef]; linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have h4 : R ≤ R ^ 4 := by
    have : (1 : ℝ) ≤ R ^ 3 := one_le_pow₀ hR1
    calc R = R * 1 := by ring
      _ ≤ R * R ^ 3 := by gcongr
      _ = R ^ 4 := by ring
  set P : ℝ := (N : ℝ) * n ^ 2 + n ^ 3 with hP
  have hP0 : 0 ≤ P := by positivity
  have hA' : 100 * R * P ≤ A₀ := le_trans (by gcongr) hA
  have hnn : n ≤ n ^ 2 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ n by linarith) hn0
    calc n = n * 1 := by ring
      _ ≤ n * n := this
      _ = n ^ 2 := by ring
  have hn23 : 3 * n ^ 2 ≤ n ^ 3 := by
    have := mul_le_mul_of_nonneg_right hn3 (sq_nonneg n)
    calc 3 * n ^ 2 ≤ n * n ^ 2 := this
      _ = n ^ 3 := by ring
  have hn1 : 3 * n ≤ n ^ 2 := by
    have := mul_le_mul_of_nonneg_right hn3 hn0
    calc 3 * n ≤ n * n := this
      _ = n ^ 2 := by ring
  have i1 : 8 * (n * (N : ℝ)) ≤ 100 * ((N : ℝ) * n ^ 2) := by
    have := mul_le_mul_of_nonneg_right hnn hN0
    nlinarith
  have i2 : 8 * n + 9 * n ^ 2 < 100 * n ^ 3 := by nlinarith
  have inner : 8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2 < 100 * P := by rw [hP]; nlinarith
  have key : R * (8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2) < R * (100 * P) := mul_lt_mul_of_pos_left inner hR0
  have hrm : 6 * (r : ℝ) * (m : ℝ) ≤ 6 * R * (n * ((N : ℝ) + 1)) := by
    have h6 : 6 * (r : ℝ) ≤ 6 * R := by rw [hRdef]; linarith
    calc 6 * (r : ℝ) * (m : ℝ) ≤ 6 * R * (m : ℝ) := by gcongr
      _ ≤ 6 * R * (n * ((N : ℝ) + 1)) := by gcongr
  rw [hcast, hMc, lt_div_iff₀ (by positivity)]
  have e1 : R * (100 * P) = 100 * R * P := by ring
  have e2 : R * (8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2) =
      2 * R * (n * ((N : ℝ) + 1)) + 6 * R * (n * ((N : ℝ) + 1)) + n ^ 2 * (9 * R) := by ring
  rw [e1, e2] at key
  linarith

theorem besselFoldBuilt_of (hC : CVInCC) : BesselFoldBuilt := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v hcl ε hε hJF
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨hcut, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, _⟩ := hv v
  set Db := (T v).base with hDb
  set s : ℂ := M.sgn (D.parOf S v) (S.l + 1) with hs
  set F := D.cutF Db χ (f v) ε with hF
  set n : ℕ := 2 * S.G.r + S.G.k + 1 with hn
  set N : ℕ := S.Ntop with hN
  set A : ℝ := A₀ - 2 * ((S.G.r : ℝ) + 1) * ((n * (N + 1) : ℕ) : ℝ) with hAdef
  have hThr : ∀ m, m ≤ n * (N + 1) → JF.TransportedAlt S.G.k S.G.r A m := fun m hm =>
    thr_budget S.G.k S.G.r N A₀ hk2 hA m hm
  have hFcc : B.InCC A (n * (N + 1)) F :=
    Formalism.FourierDecayAlt.P.PBE.cutF_inCC Db hcut hCC hε A (n * (N + 1)) (by rw [hAdef]; linarith)

  have hreg : ∀ a : List C.Letter, a.length ≤ N →
      B.InCC A (n * (N + 1 - a.length)) (foldCV S.G.k S.G.r s a F) := by
    intro a
    induction a with
    | nil => intro _; simp only [List.length_nil, Nat.sub_zero]; exact hFcc
    | cons x a ih =>
      intro hl
      simp only [List.length_cons] at hl
      have h1 := ih (by omega)
      have e : n * (N + 1 - a.length) = n * (N + 1 - (a.length + 1)) + (2 * S.G.r + S.G.k + 1) := by
        rw [← hn, ← Nat.mul_succ]; congr 1; omega
      rw [e] at h1
      have h2 := hC S.G.k S.G.r _ A _ _ (x.2 : ℂ) s h1
      simp only [List.length_cons]
      exact h2
  have hOp : IsOpen (Q.OmPlus S.G.k S.G.r Db.z Db.z') := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus _ _
  intro a
  induction a with
  | nil => intro _ g _; rfl
  | cons x a ih =>
    intro hl g hg
    simp only [List.length_cons] at hl
    have ih' := ih (by omega)
    set H := foldCV S.G.k S.G.r s a F with hH
    set m : ℕ := n * (N + 1 - a.length) with hm
    have hHcc : B.InCC A m H := hreg a (by omega)
    have hnm : 2 * S.G.r + S.G.k + 1 ≤ m := by
      rw [hm, ← hn]; exact Nat.le_mul_of_pos_right n (by omega)
    have hmM : m ≤ n * (N + 1) := by rw [hm]; exact Nat.mul_le_mul_left n (by omega)
    have hThm := hThr m hmM
    have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) H :=
      Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast hnm) hHcc.choose_spec.1

    have hswap : B.JF Db (Q.CV S.G.k S.G.r (x.2 : ℂ) H) g = Q.CV S.G.k S.G.r (x.2 : ℂ) (B.JF Db H) g := by
      rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A m H (x.2 : ℂ) hnm hThm hHcc g hg]
      show ∫ p, JF.xiP Db p • B.rho Db p (Q.CV S.G.k S.G.r (x.2 : ℂ) H) g ∂Db.μSS = _
      refine integral_congr_ae ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS Db] with p hp
      rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ Db (x.2 : ℂ) H p hp hCkn g hg.1]

    have hJHk : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (Q.OmPlus S.G.k S.G.r Db.z Db.z' ∩ B.GV S.G.k S.G.r)
        (B.JF Db H) := by
      intro g₀ hg₀
      obtain ⟨U, F', hU, hgU, hc, he⟩ :=
        (Formalism.FourierDecayAlt.P.jacquet_derivative_formula S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A m H hThm hHcc).1 g₀
          ⟨mem_level_zero_of_mem_group hg₀.2, hg₀.1⟩
      exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm), fun g hgU hgG => he g hgU (mem_level_zero_of_mem_group hgG)⟩
    have hfold : foldCV S.G.k S.G.r s a (B.JF Db F) ∈
        Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) := foldCV_memB hcl hJF s a
    have hfk : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (Q.OmPlus S.G.k S.G.r Db.z Db.z' ∩ B.GV S.G.k S.G.r)
        (foldCV S.G.k S.G.r s a (B.JF Db F)) := by
      intro g₀ hg₀
      obtain ⟨U, F', hU, hgU, hc, he⟩ := hfold.1 g₀
        ⟨mem_level_zero_of_mem_group hg₀.2, hg₀.1.2, fun b => hg₀.1.1 _ (by simp <;> omega)⟩
      exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast le_top), fun g hgU hgG => he g hgU (mem_level_zero_of_mem_group hgG)⟩
    have hloc := coefficient_vector_locality S.G.k S.G.r _ (Q.OmPlus S.G.k S.G.r Db.z Db.z') (B.JF Db H)
      (foldCV S.G.k S.G.r s a (B.JF Db F)) (x.2 : ℂ) hOp hJHk hfk
      (fun g' hg' => ih' g' ⟨hg'.2, hg'.1⟩) g ⟨hg.2, hg.1⟩
    show B.JF Db (s • Q.CV S.G.k S.G.r (x.2 : ℂ) H) g = (s • Q.CV S.G.k S.G.r (x.2 : ℂ) (foldCV S.G.k S.G.r s a (B.JF Db F))) g
    rw [JF_smul', hswap, hloc, Pi.smul_apply]

end Formalism.FourierDecayAlt.P.CutMP.En
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGradedRegFFM
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.CutMP.Gr

open NumberField

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section thr

end thr

section jf

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jf_mem_FFlM [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hT : JF.TransportedAlt k r A m) (hF : B.InCC A m F) :
    B.JF D F ∈ FFlM (m : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hN := Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem
    D.haarN.conc (fun n₀ h => D.haarN.left n₀ h)
  have hW := Formalism.FourierDecayAlt.P.bessel_words_of_domain Formalism.FourierDecayAlt.P.bessel_integral_domain
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 g₀ hg₀
    exact ⟨U, F', hU, hgU, hc, he⟩
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one D.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one D.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.QuantumDeterminants.bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem
      D.haarN.conc D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
      (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep g h hh h' hh'

end jf

end

end Formalism.FourierDecayAlt.P.CutMP.Gr
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRAsmPS
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

namespace Asm

def ggP (TT : ℝ) : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)

theorem gg_eval (TT : ℝ) (ζ : ℂ) : MvPolynomial.eval ![ζ, conj ζ, sig TT ζ] (ggP TT) = gg TT ζ := by
  simp only [ggP, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, gg]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.mul_conj]
  push_cast
  ring

theorem PS.congr {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → g ζ = f ζ) :
    PS TT g := by
  obtain ⟨m, p, hp⟩ := hf
  exact ⟨m, p, fun ζ hζ => by rw [h ζ hζ]; exact hp ζ hζ⟩

theorem PS.const (TT : ℝ) (a : ℂ) : PS TT (fun _ => a) :=
  ⟨0, MvPolynomial.C a, fun ζ _ => by simp⟩

theorem PS.mul {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ * g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨m', p', hp'⟩ := hg
  refine ⟨m + m', p * p', fun ζ hζ => ?_⟩
  rw [map_mul, ← hp ζ hζ, ← hp' ζ hζ]
  ring

theorem PS.add {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ + g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨m', p', hp'⟩ := hg
  refine ⟨m + m', p * ggP TT ^ m' + p' * ggP TT ^ m, fun ζ hζ => ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, gg_eval, ← hp ζ hζ, ← hp' ζ hζ]
  ring

theorem PS.sum {TT : ℝ} {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (h : ∀ i ∈ s, PS TT (f i)) :
    PS TT (fun ζ => ∑ i ∈ s, f i ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact PS.congr (PS.const TT 0) fun ζ _ => by simp
  | insert a s ha ih =>
    exact PS.congr (PS.add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
      fun ζ _ => by rw [Finset.sum_insert ha]

theorem PSV.apply {TT : ℝ} {V : Type*} [AddCommGroup V] [Module ℂ V] {f : ℂ → V} (hf : PSV TT f)
    (L : V →ₗ[ℂ] ℂ) : PS TT (fun ζ => L (f ζ)) := by
  obtain ⟨n, a, v, ha, hf⟩ := hf
  refine PS.congr (PS.sum Finset.univ (fun i ζ => a i ζ * L (v i)) fun i _ => PS.mul (ha i) (PS.const TT _))
    fun ζ hζ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf ζ hζ, map_sum]
  simp only [map_smul, smul_eq_mul]

end Asm

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASectionCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SARadSec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
      ∀ U : M.Ty P → MA.SmQ P.r P.TT, ∃ Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ q : MA.Qp P.r P.TT,
        Φ q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
          (((Real.sqrt (MA.wq P.k q.1 P.TT))⁻¹ : ℝ) : ℂ) • ∑ ρ, (U ρ : MA.Qp P.r P.TT → ℂ) q • e ρ q.1.2

def SADescend : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → ∀ Φ ∈ Q.RadSp k r z z' π π',
      ∃ D₀ : Set (Q.Mx k r), Q.IsDom k r z z' 0 D₀ ∧ ∃ K ∈ Q.FFl k r z z' π π' 0 D₀,
        ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), 0 < Q.GGl k r z z' g →
          Q.wCell k r (Fin.last r) c * g ∈ D₀ ∧ K (Q.wCell k r (Fin.last r) c * g) = Φ c g

def SACover : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    ∀ g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r z z', ∃ n ∈ Q.Nlev k r 0, ∃ n' ∈ Q.Nlev k r 0, ∃ c ∈ OmX r,
      ∃ g₁ ∈ Q.Glev k r (Fin.last r), 0 < Q.GGl k r z z' g₁ ∧ g = n * (Q.wCell k r (Fin.last r) c * g₁) * n'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymDefs
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

def Xuv (k r : ℕ) (u v : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  vecMulVec u (star (Hpk k r *ᵥ v)) - vecMulVec v (star (Hpk k r *ᵥ u))

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTSS
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTSS_of_adj_radT : GTSSAdjPt → GTCLRadT → GTSS := fun hA hR =>
  gTSS_of_cut (gTSSLocal_of_radT hR) hA SSC.second_shift_constant SSPh.second_shift_phase_holds

theorem gTSS_of_adj : GTSSAdjPt → GTSS := fun hA => gTSS_of_adj_radT hA radial_torus_local_holds

theorem second_shift_gauge_holds : GTSS := gTSS_of_adj second_shift_adjoint_pointwise

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

