module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0216
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0096
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0141
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPContPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpNormPiLe
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AestronglyMeasurableGermIntegrand
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0219
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0184

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCoreAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core

noncomputable section

theorem theta_gauge_constancy_holds : ThtGaugeConstOfCore := by
  intro hA hPt hTh hE hPR hGL hDU
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ v e hH hk l hl Bw Bw' hBw hBw'
  obtain ⟨hB, hFr, hGa, hQQ⟩ := hH
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v)
    (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' hPl
  obtain ⟨d, hd1, hd2, hd3, hd4⟩ := Formalism.FourierDecayAlt.P.normal_form_actual (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v)
    (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' hPl X
  have hAct : ActHyp (D.parOf S v) (T v).base X d := ⟨hPl, hd1, hd2, hd3, hd4⟩
  obtain ⟨SS, hSS⟩ := hPt (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct l hl
  obtain ⟨Pr, hPr⟩ := hPR (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl hk
  obtain ⟨θ, hθ⟩ := hTh (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct l hl SS hSS Pr hPr
    Bw Bw' hBw hBw'
  have hFrB : Gauge.IsFrameB (D.parOf S v) (T v).base e := hFr
  have hGQ : GQQ (D.parOf S v) (T v).base e := hQQ
  have hSSF := hA (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct e hFrB hGQ
  refine ⟨θ, fun ζ hζ π ρ hup => ?_⟩
  have hent := hE (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct e hFrB hSSF l hl SS hSS ζ hζ π ρ
  rw [if_pos hup] at hent
  obtain ⟨hP1, hH1, -, -⟩ := hDU Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v ζ hζ
  set n0 := SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ with hn0
  have hN0 : PRho.nrmW S.G.k S.G.r (T v).base.z n0 = 1 := by
    unfold PRho.nrmW; rw [hP1, hH1]; simp
  obtain ⟨-, -, hrest⟩ := hPr
  have hpos : 0 < PRho.nrmW S.G.k S.G.r (T v).base.z n0 := by rw [hN0]; norm_num

  have hfix : ∀ τ y, Pr τ n0 (e τ ζ y) = e τ ζ y := by
    intro τ y
    refine ((hrest n0 hpos).2.2.2 τ (e τ ζ y)).2 ?_
    intro Fr hFrm w
    rw [hP1] at hFrm
    exact hGL Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk ζ hζ τ Fr hFrm w y
  have hfixc : ∀ τ, (Pr τ n0).comp (e τ ζ) = e τ ζ := fun τ => by ext y; exact hfix τ y
  have hsa := (hrest n0 hpos).2.1 ρ
  have hfib : e π ζ ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' ζ :=
    ((hFrB.2 ζ hζ).1 π)
  set B0 : Wq (S.pl v) →L[ℂ] Wp (S.pl v) := tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    Bw Bw' n0 (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
    (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) (e π ζ) with hB0
  have key : (Pr ρ n0).comp (SS ζ (e π ζ)) = θ π • (Pr ρ n0).comp B0 :=
    hθ ζ hζ π ρ hup (e π ζ) hfib (hfixc π)

  have hmove : ∀ Y : Wq (S.pl v) →L[ℂ] Wp (S.pl v),
      inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp Y)) = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Y) := by
    intro Y
    have h1 := hsInner_lmul (Pr ρ n0) hsa Y (e ρ ζ)
    simp only [B.hsInner, lmul_apply] at h1
    rw [hfixc ρ] at h1
    exact h1
  have hsm : ∀ (c : ℂ) (A : Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A
    unfold B.hsVec
    ext i
    simp
  calc θ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec B0)
      = θ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp B0)) := by rw [hmove]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (θ π • (Pr ρ n0).comp B0)) := by rw [hsm, inner_smul_right]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp (SS ζ (e π ζ)))) := by rw [key]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (SS ζ (e π ζ))) := hmove _
    _ = _ := hent

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMContPf
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

namespace ContPfM

section ring

variable {R : Type*} [Ring R] (a c d : ℕ → R)

def Mi (i : ℕ) : Matrix (Fin 2) (Fin 2) R := !![a i, d i; -c i, 0]

def prodM (lo n : ℕ) : Matrix (Fin 2) (Fin 2) R := ((List.range n).map fun j => Mi a c d (lo + j)).prod

def bus : ℕ → R × R
  | 0 => (1, 0)
  | i + 1 => ((bus i).1 * a i - (bus i).2 * c i, (bus i).1 * d i)

def tds (r : ℕ) : ℕ → Fin 2 → R
  | 0, b => if b = 0 then 1 else 0
  | 1, b => if 1 ≤ r then (if b = 0 then a (r - 1) else d (r - 1)) else 0
  | m + 2, b => if m + 2 ≤ r then a (r - (m + 2)) * tds r (m + 1) b - c (r - (m + 1)) * d (r - (m + 2)) * tds r m b else 0

variable {a c d}

theorem prodM_succ_left (lo n : ℕ) : prodM a c d lo (n + 1) = Mi a c d lo * prodM a c d (lo + 1) n := by
  unfold prodM
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  congr 2
  exact List.map_congr_left (fun j _ => by
    show Mi a c d (lo + (j + 1)) = Mi a c d (lo + 1 + j)
    congr 1
    omega)

theorem prodM_succ_right (lo n : ℕ) : prodM a c d lo (n + 1) = prodM a c d lo n * Mi a c d (lo + n) := by
  unfold prodM
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

theorem bus_eq : ∀ i, (bus a c d i).1 = prodM a c d 0 i 0 0 ∧ (bus a c d i).2 = prodM a c d 0 i 0 1 := by
  intro i
  induction i with
  | zero => simp [bus, prodM]
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [prodM_succ_right]
    simp only [bus, h1, h2, Matrix.mul_apply, Fin.sum_univ_two, Mi, zero_add]
    simp [sub_eq_add_neg]

theorem tds_eq (hcd : ∀ i, Commute (c (i + 1)) (d i)) (r : ℕ) :
    ∀ m, m ≤ r → ∀ b, tds a c d r m b = prodM a c d (r - m) m 0 b
  | 0, _, b => by fin_cases b <;> simp [tds, prodM]
  | 1, hm, b => by
    rw [prodM_succ_left]
    fin_cases b <;> simp [tds, hm, prodM, Mi]
  | m + 2, hm, b => by
    have ih1 := tds_eq hcd r (m + 1) (by omega) b
    have ih0 := tds_eq hcd r m (by omega) b
    have e1 : r - (m + 2) + 1 = r - (m + 1) := by omega
    have e2 : r - (m + 1) + 1 = r - m := by omega
    show (if m + 2 ≤ r then a (r - (m + 2)) * tds a c d r (m + 1) b -
        c (r - (m + 1)) * d (r - (m + 2)) * tds a c d r m b else 0) = _
    have hL : prodM a c d (r - (m + 1)) (m + 1) = Mi a c d (r - (m + 1)) * prodM a c d (r - m) m := by
      rw [prodM_succ_left, e2]
    have hR : prodM a c d (r - (m + 2)) (m + 2) =
        Mi a c d (r - (m + 2)) * (Mi a c d (r - (m + 1)) * prodM a c d (r - m) m) := by
      rw [prodM_succ_left, e1, hL]
    rw [if_pos hm, ih1, ih0, hL, hR]
    have hc := (hcd (r - (m + 2))).eq
    rw [e1] at hc
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Mi]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, zero_mul, add_zero, neg_mul]
    simp only [hc, mul_neg, mul_assoc, sub_eq_add_neg]

theorem tds_bus (hcd : ∀ i, Commute (c (i + 1)) (d i)) (r : ℕ) :
    tds a c d r r 0 = (bus a c d r).1 ∧ tds a c d r r 1 = (bus a c d r).2 := by
  rw [tds_eq hcd r r le_rfl, tds_eq hcd r r le_rfl, (bus_eq r).1, (bus_eq r).2, Nat.sub_self]
  exact ⟨rfl, rfl⟩

end ring

section ops

open ContPf

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]


variable (X) in
def aSv (Y : ℂ) (i : ℕ) : Module.End ℂ (WSm r X) := algebraMap ℂ _ Y - eS X i 3

theorem cp_vABs (Y : ℂ) : ∀ i, i ≤ r → ∀ f : WSm r X,
    (Q.vABs r Y i).1 (f : (Fin r → ℂ) → X) = (((bus (aSv X Y) (eS X · 4) (eS X · 5) i).1 f : WSm r X) : (Fin r → ℂ) → X) ∧
      (Q.vABs r Y i).2 (f : (Fin r → ℂ) → X) = (((bus (aSv X Y) (eS X · 4) (eS X · 5) i).2 f : WSm r X) : (Fin r → ℂ) → X)
  | 0, _, f => ⟨rfl, rfl⟩
  | i + 1, hi, f => by
    have hir : i < r := by omega
    have ih := cp_vABs Y i (by omega)
    simp only [Q.vABs, dif_pos hir, bus]
    refine ⟨?_, ?_⟩
    · have e1 : Y • (f : (Fin r → ℂ) → X) - pbOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) =
          ((aSv X Y i f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [aSv, eS, dif_pos hir]
        rfl
      have e2 : cbOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) = ((eS X i 4 f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [eS, dif_pos hir]
        rfl
      rw [e1, e2, (ih _).1, (ih _).2]
      rfl
    · have e3 : cbiOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) = ((eS X i 5 f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [eS, dif_pos hir]
        rfl
      rw [e3, (ih _).1]
      rfl

theorem cp_tdUv (Y : ℂ) (b : Fin 2) : ∀ m, ∀ f : WSm r X,
    tdUv r Y m b (f : (Fin r → ℂ) → X) = ((tds (aSv X Y) (eS X · 4) (eS X · 5) r m b f : WSm r X) : (Fin r → ℂ) → X)
  | 0, f => by
    fin_cases b <;> simp [tdUv, tds]
  | 1, f => by
    by_cases h1 : 1 ≤ r
    · have hr : r - 1 < r := by omega
      fin_cases b
      · simp only [tdUv, tds, dif_pos h1, if_pos h1, Fin.zero_eta, if_true, aSv, eS, dif_pos hr]
        rfl
      · simp only [tdUv, tds, dif_pos h1, if_pos h1, Fin.mk_one, one_ne_zero, if_false, eS, dif_pos hr]
        rfl
    · simp only [tdUv, tds, dif_neg h1, if_neg h1]
      rfl
  | m + 2, f => by
    by_cases h2 : m + 2 ≤ r
    · have ih1 := cp_tdUv Y b (m + 1) f
      have ih0 := cp_tdUv Y b m f
      have hr2 : r - (m + 2) < r := by omega
      have hr1 : r - (m + 1) < r := by omega
      simp only [tdUv, tds, dif_pos h2, if_pos h2]
      rw [ih1, ih0]
      simp only [aSv, eS, dif_pos hr2, dif_pos hr1]
      rfl
    · simp only [tdUv, tds, dif_neg h2, if_neg h2]
      rfl

end ops

section loc

open ContPf

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem loc_pbOp (l : Fin r) : Loc (X := X) (pbOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h.eventuallyEq_nhds] with y hy
  simp only [pbOp, wirtBar, hy.fderiv_eq]

theorem loc_cbOp (l : Fin r) : Loc (X := X) (cbOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h] with y hy
  simp only [cbOp, hy]

theorem loc_cbiOp (l : Fin r) : Loc (X := X) (cbiOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h] with y hy
  simp only [cbiOp, hy]

theorem loc_tdUv (Y : ℂ) (b : Fin 2) : ∀ m, Loc (tdUv (X := X) r Y m b)
  | 0 => by
    unfold tdUv
    split_ifs
    · exact loc_id
    · exact loc_zero
  | 1 => by
    unfold tdUv
    split_ifs
    · exact loc_sub (loc_smul Y loc_id) (loc_pbOp _)
    · exact loc_cbiOp _
    · exact loc_zero
  | m + 2 => by
    have ih1 := loc_tdUv Y b (m + 1)
    have ih0 := loc_tdUv Y b m
    unfold tdUv
    split_ifs
    · exact loc_sub (loc_sub (loc_smul Y ih1) (loc_comp (loc_pbOp _) ih1))
        (loc_comp (loc_cbOp _) (loc_comp (loc_cbiOp _) ih0))
    · exact loc_zero

theorem loc_vABs (Y : ℂ) : ∀ i, Loc (X := X) (Q.vABs r Y i).1 ∧ Loc (X := X) (Q.vABs r Y i).2 := by
  intro i
  induction i with
  | zero => exact ⟨loc_id, loc_zero⟩
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    by_cases hi : i < r
    · simp only [Q.vABs, dif_pos hi]
      exact ⟨loc_sub (loc_comp h1 (loc_sub (loc_smul Y loc_id) (loc_pbOp _))) (loc_comp h2 (loc_cbOp _)),
        loc_comp h1 (loc_cbiOp _)⟩
    · simp only [Q.vABs, dif_neg hi]
      exact ⟨h1, h2⟩

end loc

end ContPfM

open ContPf ContPfM in
theorem mirror_residue_continuity : JDRvCont := by
  intro X _ _ r Y O hO hOm f hf c hc b
  obtain ⟨f', hf'm, hf'e⟩ := cp_cutoff O hO hOm f hf c hc
  have e1 : tdUv r Y r b f c = tdUv r Y r b f' c := ((loc_tdUv Y b r) f f' c hf'e.symm).eq_of_nhds
  have ev := loc_vABs (X := X) (r := r) Y r
  have h3 := cp_tdUv Y b r ⟨f', hf'm⟩
  have h4 := cp_vABs Y r le_rfl ⟨f', hf'm⟩
  have h5 := tds_bus (a := aSv (r := r) X Y) (c := (eS X · 4)) (d := (eS X · 5))
    (fun i => eS_comm (i + 1) i (by omega) 4 5) r
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · have e2 : (Q.vABs r Y r).1 f c = (Q.vABs r Y r).1 f' c := (ev.1 f f' c hf'e.symm).eq_of_nhds
    simp only [Q.cmp, if_true]
    rw [e1, e2]
    change tdUv r Y r 0 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c =
      (Q.vABs r Y r).1 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c
    rw [h3, h4.1, h5.1]
  · have e2 : (Q.vABs r Y r).2 f c = (Q.vABs r Y r).2 f' c := (ev.2 f f' c hf'e.symm).eq_of_nhds
    simp only [Q.cmp, show ¬ ((1 : Fin 2) = 0) by decide, if_false]
    rw [e1, e2]
    change tdUv r Y r 1 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c =
      (Q.vABs r Y r).2 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c
    rw [h3, h4.2, h5.2]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section pt

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem rn_zero : U.Rn k p ρ 0 = 1 := by
  have h1 : U.skewOf (0 : (G.UT p → ℂ) × (Fin p → ℝ)) = 0 := by
    unfold U.skewOf; ext a b; simp [G.strictUpper]
  unfold U.Rn
  rw [← Formalism.FourierDecayAlt.P.Ux3.block3_one]
  simp only [Prod.fst_zero, Prod.snd_zero, h1]
  congr 1 <;> ext <;> simp

theorem upper_zero : G.upper (0 : G.UT p → ℂ) = 1 := by
  unfold G.upper G.strictUpper; ext a b; simp

theorem rcAct_one_zero : rcAct (1 : B.Mat k ρ) (0 : U.RC k p ρ) = 0 := by
  unfold rcAct; ext <;> simp

theorem sxL_mem (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) :
    sxL Bj σ x ∈ Sset k (p + ρ) (liftVec k p ρ Bj.z) := by
  by_cases hx : GoodL Bj σ x
  · rw [sxL, if_pos hx]
    exact left_factor_mem k p ρ Bj.z (-x.2.1) (lhOf σ x.2.2.2) (Matrix.of x.1.1) (Matrix.of x.1.2) Bj.z_mem
      (lh_lower σ _) hx.1 hx.2
  · rw [sxL, if_neg hx]
    refine ⟨1, (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k (p + ρ) _).one_mem, 1,
      (Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)).one_mem, by simp⟩

theorem goodL_pt (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (g : B.Mat k ρ) (hg : g ∈ B.GV k ρ) (x : XL k p ρ σ) (hx : GoodL Bj σ x) :
    sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g ∈ B.GV k (p + ρ) ∧
      U.DjU k p ρ (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g) ≠ 0 := by
  set ξ0 : U.Xi k p 0 ρ σ := ((x.2.1, 0), (x.2.2.1, (x.2.2.2, 0))) with hξ0
  have uh : IsUnit (Matrix.of x.1.1 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z).unit _ hx.1
  have uν : IsUnit (Matrix.of x.1.2 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).unit _ hx.2
  have hH1 : (1 : B.Mat k ρ)ᴴ * Hpk k ρ * 1 = Hpk k ρ := by simp
  have e := gamma_xi_split k p ρ σ d ξ0 (fun a => a.elim0) (Matrix.of x.1.1) (Matrix.of x.1.2) 1 1 g uh uν hH1
  simp only [hξ0, Formalism.FourierDecayAlt.P.PBM.embG_one, upper_zero, Formalism.FourierDecayAlt.P.PBM.muP_one, rcAct_one_zero, rn_zero,
    Matrix.mul_one] at e
  have hx' : sxL Bj σ x = U.Rn k p ρ (-x.2.1) * U.muP k p ρ (lhOf σ x.2.2.2)ᴴ⁻¹ *
      U.embG k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹) := if_pos hx
  have cG := Formalism.FourierDecayAlt.P.unitary_group_closed k ρ
  have hγ : (Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹ * g ∈ B.GV k ρ :=
    cG.mul_mem _ (cG.mul_mem _ (cG.inv_mem _ hx.1.1) _ (cG.inv_mem _ hx.2.1)) _ hg
  rw [hx', ← e]
  have hZ : G.detM (fun a : Fin 0 => a.elim0 : G.Mat 0) ≠ 0 := by rw [detM_zero]; exact one_ne_zero
  refine ⟨Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ0 _ hZ hγ, ?_⟩
  intro h0
  have h1 := Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice σ d ξ0 (fun a : Fin 0 => a.elim0)
    ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹ * g)
  rw [detM_zero, mul_one] at h1
  exact Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd (h1.symm.trans h0)

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem core_lf (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun x => ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g))) (muL Bj σ) ∧
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ x, ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) ∂(muL Bj σ) :=
  core_main gamma_xi_split psi_right_equivariant psi_right_action_comm psi_measure_preserving right_measure_preserving hp σ d hd Bj B0 hz' hπ' hW'
    hW0' hNj hN0 g hg H hHc R hR (fl_aesm Bj σ d hd H hHc g hg.1)
    (aestronglyMeasurable_germ_integrand gamma_xi_split Bj B0 hz' hπ' σ d hd H hHc g hg.1)
    (fun x hx => Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.krI_aesm B0 H hHc _ (goodL_pt Bj σ d hd g hg.1 x hx).1
      (goodL_pt Bj σ d hd g hg.1 x hx).2)
    (fun γ hγ => slice_int_cont σ d hd H hHc _ _ γ hγ)

end pt

theorem left_fubini_reduced_form : CoreLF := by
  intro k p m n e hp σ d hd Wp Wq _ _ _ _ _ _ Bj B0 hz hz' hπ' hW' hW0' hNj hN0
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz hz'
  refine ⟨XL k p m σ, inferInstance, muL Bj σ, ellL Bj σ, sxL Bj σ, fun x => hz ▸ sxL_mem Bj σ x, ?_⟩
  intro g hg H hHc hRb
  obtain ⟨R, hR⟩ := hRb
  have hπ'' : ∀ y : B.Mat k m, Bj.π' y = B0.π' (U.embG k p m y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hset : {x | x ∈ B.GV k (p + m) ∧ Dmin k (p + m) B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} =
      {x | x ∈ B.GV k (p + m) ∧ U.DjU k p m x ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Formalism.FourierDecayAlt.P.hat_z_minimum_degree k p m B0.z B0.z' x]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + m) ∧ U.DjU k p m x ≠ 0} := hset ▸ hHc
  have h := core_lf hp σ d hd Bj B0 hz'.symm hπ'' hW' hW0' hNj hN0 g hg H hHc' R hR
  have hF : D.castF (rfl : p + m = p + m) H = H := funext fun y => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hV : ∀ v : Fin (2 * (p + m) + k + 1) → ℂ, D.castV (rfl : p + m = p + m).symm v = v :=
    fun v => Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl v
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, hF, hV, ← hz, ← hz']
  exact h

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas

namespace Formalism.FourierDecayAlt.P

theorem left_fubini_normalized_tower : LeftFubiniLemmas.LeftFubini := LeftFubiniReduction.leftFubini_of_core LeftFubiniLemmas.left_fubini_reduced_form

end Formalism.FourierDecayAlt.P
end
end

