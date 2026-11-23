module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0053
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Function.L2Space
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0025

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def GermOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq),
    (∀ (U : Set (B.Mat k r)) (f f' : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U →
      (∀ x ∈ U, x ∈ B.GV k r → f x = f' x) → ∀ g ∈ U, g ∈ B.GV k r →
        B.opApply Θ f g = B.opApply Θ f' g ∧ B.opAdj Θ f g = B.opAdj Θ f' g) ∧
    (∀ (c : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r),
      B.opApply Θ (c • f) g = c • B.opApply Θ f g ∧ B.opAdj Θ (c • f) g = c • B.opAdj Θ f g)

def ExtLoc : Prop :=
  ∀ (k r : ℕ) (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E'] (O : Set (B.Mat k r)) (J : B.Mat k r → E'),
    IsOpen O → Q.SmoothLev k r 0 O J → ∀ g₀ ∈ B.GV k r, g₀ ∈ O →
      ∃ (f : B.Mat k r → E') (U : Set (B.Mat k r)), B.CkOn ⊤ (B.GV k r) f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧
        IsOpen U ∧ g₀ ∈ U ∧ ∀ x ∈ U, x ∈ B.GV k r → f x = J x

def SmoothOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (O : Set (B.Mat k r)), IsOpen O → (∀ g ∈ O, g ∈ B.GV k r → g ∈ B.GPos D) →
    B.SmoothCoef (B.GPos D) Θ → ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → tsupport f ⊆ O →
      Q.SmoothLev k r 0 O (B.opApply Θ f) ∧ Q.SmoothLev k r 0 O (B.opAdj Θ f)

def AdjComm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ∀ g ∈ B.GPos D, B.opAdj Θ (B.rho D p f) g = B.rho D p (B.opAdj Θ f) g

def EquivOps : Prop :=
  ExtLoc →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (O : Set (B.Mat k r)) (P : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsDom k r D.z D.z' 0 O →
    (∀ (U : Set (B.Mat k r)) (f f' : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U →
      (∀ x ∈ U, x ∈ B.GV k r → f x = f' x) → ∀ g ∈ U, g ∈ B.GV k r → P f g = P f' g) →
    (∀ (c : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → P (c • f) g = c • P f g) →
    (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → tsupport f ⊆ O → Q.SmoothLev k r 0 O (P f)) →
    (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → tsupport f ⊆ O →
      ∀ p, D.inSS p → ∀ g ∈ O, g ∈ B.GV k r → P (B.rho D p f) g = B.rho D p (P f) g) →
    ∀ J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 O, P J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 O

def OmPDom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f),
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) ∧
      ∀ g ∈ OmP S T v, g ∈ B.GV S.G.k S.G.r → g ∈ B.GPos (T v).base

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAIsAdj
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

section IsAdjProof

variable (P : M.Par)

def adjSub : Subalgebra ℂ (DQ P).Pr where
  carrier := {a | IsAdj a}
  mul_mem' {a b} ha hb := ((Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.1 a b ha hb).2
  add_mem' {a b} ha hb := ((Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.1 a b ha hb).1
  algebraMap_mem' z := by
    have h := (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.2.1 z 1 (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).1
    rw [Algebra.algebraMap_eq_smul_one]
    exact h

theorem adjSub_star {a : (DQ P).Pr} (ha : a ∈ adjSub P) : star a ∈ adjSub P :=
  (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.2.2 a ha

theorem gen_adj (hτ : 0 ≤ P.TT) {w : (DQ P).Pr} (hw : w ∈ (DQ P).gens P.TT) : w ∈ adjSub P :=
  Formalism.FourierDecayAlt.P.adjoint_generators P.r P.TT hτ w hw

abbrev MSa : Subalgebra ℂ (A P (DQ P)) := Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (adjSub P) (M.Ty P)

theorem sc_memMS (hτ : 0 ≤ P.TT) {w : (DQ P).Pr} (hw : w ∈ (DQ P).gens P.TT) : sc P (DQ P) w ∈ MSa P :=
  Formalism.FourierDecayAlt.P.MAx2.Jet.scalar_mem _ _ (gen_adj P hτ hw)

theorem star_memMS {a : A P (DQ P)} (ha : a ∈ MSa P) : star a ∈ MSa P := fun i j => by
  rw [Matrix.star_apply]; exact adjSub_star P (ha j i)

variable {P}

section Lv

variable (hτ : 0 ≤ P.TT) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hτ hL

theorem lv_p (l : Fin P.r) : L.p l ∈ MSa P := by
  rw [hL.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_pb (l : Fin P.r) : L.pb l ∈ MSa P := by
  rw [hL.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_c (l : Fin P.r) : L.c l ∈ MSa P := by
  rw [hL.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_ci (l : Fin P.r) : L.ci l ∈ MSa P := by
  rw [hL.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_cb (l : Fin P.r) : L.cb l ∈ MSa P := by
  rw [hL.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_cbi (l : Fin P.r) : L.cbi l ∈ MSa P := by
  rw [hL.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem zeta_mem_self_adjoint : L.ζ ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zi : L.ζi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zb : L.ζb ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zbi : L.ζbi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_gg : L.GG ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_ggi : L.GGi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_nab : L.nab ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => add_mem (gen_adj P hτ (by simp [DAlg.gens]))
    (Subalgebra.smul_mem _ (mul_mem (gen_adj P hτ (by simp [DAlg.gens])) (gen_adj P hτ (by simp [DAlg.gens]))) _)
theorem lv_nabs : L.nabs ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => add_mem (neg_mem (gen_adj P hτ (by simp [DAlg.gens])))
    (Subalgebra.smul_mem _ (mul_mem (gen_adj P hτ (by simp [DAlg.gens])) (gen_adj P hτ (by simp [DAlg.gens]))) _)

theorem lv_Dr : L.Dr ∈ MSa P := by
  unfold LevelData.Dr
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_c hτ hL l
theorem lv_Drb : L.Drb ∈ MSa P := by
  unfold LevelData.Drb
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_cb hτ hL l
theorem lv_Dri : L.Dri ∈ MSa P := by
  unfold LevelData.Dri
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_ci hτ hL l
theorem lv_Drbi : L.Drbi ∈ MSa P := by
  unfold LevelData.Drbi
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_cbi hτ hL l

theorem lv_Tprod (Y : ℂ) : L.Tprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (MSa P) (Fin 2) := by
  unfold LevelData.Tprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (Subalgebra.algebraMap_mem _ _) (lv_p hτ hL l)
  · exact neg_mem (lv_c hτ hL l)
  · exact lv_ci hτ hL l
  · exact zero_mem _

theorem lv_Tvprod (Y : ℂ) : L.Tvprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (MSa P) (Fin 2) := by
  unfold LevelData.Tvprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tvl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact sub_mem (Subalgebra.algebraMap_mem _ _) (lv_pb hτ hL l)
  · exact neg_mem (lv_cb hτ hL l)
  · exact lv_cbi hτ hL l
  · exact zero_mem _

theorem lv_hat {X : A P (DQ P)} (hX : X ∈ hatSet P L) : X ∈ MSa P := by
  have hl0 : ∀ Y, L.l0 Y ∈ MSa P := fun Y => by
    unfold LevelData.l0
    exact sub_mem (neg_mem (lv_nab hτ hL)) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (lv_zb hτ hL) (lv_ggi hτ hL)))
  have hm0 : ∀ Y, L.m0 Y ∈ MSa P := fun Y => by
    unfold LevelData.m0
    exact sub_mem (neg_mem (lv_nabs hτ hL)) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (zeta_mem_self_adjoint hτ hL) (lv_ggi hτ hL)))
  rcases hX with ((⟨Y, rfl⟩ | ⟨Y, rfl⟩) | ⟨Y, rfl⟩) | ⟨Y, rfl⟩
  · exact mul_mem (lv_Dr hτ hL) (lv_Tprod hτ hL Y 0 0)
  · exact mul_mem (mul_mem (lv_Drb hτ hL) (lv_gg hτ hL))
      (add_mem (mul_mem (hl0 Y) (lv_Tprod hτ hL Y 0 0)) (lv_Tprod hτ hL Y 1 0))
  · exact mul_mem (lv_Drb hτ hL) (lv_Tvprod hτ hL Y 0 0)
  · exact mul_mem (mul_mem (lv_Dr hτ hL) (lv_gg hτ hL))
      (add_mem (mul_mem (hm0 Y) (lv_Tvprod hτ hL Y 0 0)) (lv_Tvprod hτ hL Y 1 0))

theorem lv_SS (i : ℕ) : SS P (DQ P) i ∈ MSa P := fun a b => by
  simp only [SS, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact zero_mem _

theorem lv_kap (g : M.Ty P → ℂ) : kap P (DQ P) g ∈ MSa P := by
  have : kap P (DQ P) g = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (g π) := rfl
  rw [this]
  exact Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => Subalgebra.algebraMap_mem _ _

theorem lv_bdd {b : A P (DQ P)} (hb : b ∈ bddSet P L) : b ∈ MSa P := by
  have hD : L.D ∈ MSa P := mul_mem (lv_Dr hτ hL) (zeta_mem_self_adjoint hτ hL)
  have hDi : L.Di ∈ MSa P := mul_mem (lv_zi hτ hL) (lv_Dri hτ hL)
  have hDb : L.Db ∈ MSa P := mul_mem (lv_Drb hτ hL) (lv_zb hτ hL)
  have hDbi : L.Dbi ∈ MSa P := mul_mem (lv_zbi hτ hL) (lv_Drbi hτ hL)
  have hS : ∀ i, L.Drb * L.Dri * SS P (DQ P) i ∈ MSa P := fun i =>
    mul_mem (mul_mem (lv_Drb hτ hL) (lv_Dri hτ hL)) (lv_SS hτ hL i)
  rcases hb with ((h4 | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h4
    rcases h4 with rfl | rfl | rfl | rfl
    · exact lv_zi hτ hL
    · exact lv_zbi hτ hL
    · exact mul_mem hD hDbi
    · exact mul_mem hDb hDi
  · exact lv_kap hτ hL g
  · exact hS i
  · exact star_memMS P (hS i)

end Lv

theorem transfer_is_adjoint_holds : JAIsAdj := by
  intro P L hτ hL a ha
  have hsub : Submonoid.closure (hatSet P L ∪ bddSet P L) ≤ (MSa P).toSubmonoid :=
    Submonoid.closure_le.2 fun x hx => by
      rcases hx with hx | hx
      · exact lv_hat (le_of_lt hτ) hL hx
      · exact lv_bdd (le_of_lt hτ) hL hx
  intro π π'
  exact hsub ha π π'

end IsAdjProof

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatNodes
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem hat_nodes_decay_holds : JDHatNodes := by
  intro P
  classical
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = 1 + ∑ π : M.Ty P, ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i| := ⟨_, rfl⟩
  refine ⟨fun j => Mb + ((j : ℕ) : ℝ), fun a b h => ?_, fun j π => ?_⟩
  · dsimp only at h
    have h' : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := add_left_cancel h
    exact Fin.ext (by exact_mod_cast h')
  · unfold M.xC
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have hle : |M.rho P π i| ≤ ∑ π' : M.Ty P, ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π' i'| := by
      calc |M.rho P π i| ≤ ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i'| :=
            Finset.single_le_sum (f := fun i' => |M.rho P π i'|) (fun _ _ => abs_nonneg _) hi
        _ ≤ _ := Finset.single_le_sum (f := fun π' => ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π' i'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ π)
    have hpos : 0 < Mb + ((j : ℕ) : ℝ) + M.rho P π i := by
      have h1 := neg_abs_le (M.rho P π i)
      have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hc : (((Mb + ((j : ℕ) : ℝ) : ℝ) : ℂ) + ((M.rho P π i : ℝ) : ℂ)) =
        ((Mb + ((j : ℕ) : ℝ) + M.rho P π i : ℝ) : ℂ) := by push_cast; ring
    rw [hc]
    exact Complex.ofReal_ne_zero.2 (ne_of_gt hpos)

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def PolyOp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq) : Prop :=
  ∀ Tm ∈ Θ, Tm.word.length ≤ o ∧ ∃ P : B.Mat k r → ℂ, U.IsPolyDeg κ P ∧
    (∀ g, Tm.coef g = P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) ∧
    ∀ g, Tm.coefAdj g = star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)

def JDPolyOK : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq),
    PolyOp o κ Θ → (∀ UU : Set (B.Mat k r), B.SmoothCoef UU Θ) ∧ (∀ d : ℝ, (κ : ℝ) ≤ d → GlobCoef Θ d) ∧
      B.opOrder Θ ≤ o

def JDCapA : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℂ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (L.Ahat y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (L.Ahatv y) (trJ S T v e J)

def JDCapR : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℝ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (RhM (D.parOf S v) L y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (RhvM (D.parOf S v) L y) (trJ S T v e J)

theorem hatOK_of_poly (hP : JDPolyOK) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cc : ℝ} (hCc : 1 ≤ Cc) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))} {v : Fin S.f}
    {Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    (hΘ : PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ)
    (hc : B.Commutes (T v).base (B.GPos (T v).base) Θ) : HatOK Cc S T v Θ := by
  obtain ⟨hs, hg, ho⟩ := hP S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) _ _ Θ hΘ
  have hn : (0 : ℝ) ≤ nDim S.G.k S.G.r := by unfold nDim; positivity
  have hr : (0 : ℝ) ≤ (S.G.r : ℝ) + 1 := by positivity
  refine ⟨hs _, hc, hg _ ?_, ?_⟩
  · have e1 : (((S.G.r + 1) * (2 * S.G.r + S.G.k + 1) : ℕ) : ℝ) = ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r := by
      unfold nDim; push_cast; ring
    rw [e1, mul_assoc]
    exact le_mul_of_one_le_left (mul_nonneg hr hn) hCc
  · have e2 : ((B.opOrder Θ : ℕ) : ℝ) ≤ nDim S.G.k S.G.r := by
      unfold nDim; exact_mod_cast ho
    exact e2.trans (le_mul_of_one_le_left hn hCc)

theorem jDOpA_of_parts (hP : JDPolyOK) (hC : JDCapA) : JDOpA := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  obtain ⟨Θ, Θv, hΘ, hΘv, hc, hcv, h⟩ := hC Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  exact ⟨Θ, Θv, hatOK_of_poly hP hCc hΘ hc, hatOK_of_poly hP hCc hΘv hcv, h⟩

theorem jDOpR_of_parts (hP : JDPolyOK) (hC : JDCapR) : JDOpR := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  obtain ⟨Θ, Θv, hΘ, hΘv, hc, hcv, h⟩ := hC Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  exact ⟨Θ, Θv, hatOK_of_poly hP hCc hΘ hc, hatOK_of_poly hP hCc hΘv hcv, h⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRealisation
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section L2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def gramL {ι : Type} (μ : Measure ℂ) (F G : ι × ℂ → ℂ → H) (p q : ι × ℂ) : ℂ :=
  ∫ D, ⟪F p D, G q D⟫_ℂ ∂μ

theorem inner_toLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ D, ⟪f D, g D⟫_ℂ ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with D h1 h2
  rw [h1, h2]

theorem integrable_inner_of_memLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun D => ⟪f D, g D⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with D h1 h2
  rw [h1, h2]

theorem blockPSD_gramL {ι : Type} (μ : Measure ℂ) (Y : Finset ι) (U A : ι × ℂ → ℂ → H)
    (memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (U (h, x)) 2 μ)
    (memA : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (A (h, x)) 2 μ) (Xs : Finset ℂ) (hXs : ∀ x ∈ Xs, x ≠ 0) :
    KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (gramL μ U U) (gramL μ U A) (gramL μ A A) := by
  have hmem : ∀ p ∈ Y ×ˢ Xs, MemLp (U p) 2 μ ∧ MemLp (A p) 2 μ := by
    intro p hp
    rw [Finset.mem_product] at hp
    have hx := hXs _ hp.2
    exact ⟨memU _ hp.1 _ hx, memA _ hp.1 _ hx⟩
  let v : {x // x ∈ (Y ×ˢ Xs).disjSum (Y ×ˢ Xs)} → Lp H 2 μ := fun x =>
    Sum.elim (fun p => if hp : MemLp (U p) 2 μ then hp.toLp (U p) else 0)
      (fun q => if hq : MemLp (A q) 2 μ then hq.toLp (A q) else 0) x.1
  unfold KB.BlockPSD TB.PSDOn
  open scoped ComplexOrder in
  refine (congrArg Matrix.PosSemidef ?_).mpr (Matrix.posSemidef_gram ℂ v)
  ext i j
  obtain ⟨x, hx⟩ := i
  obtain ⟨y, hy⟩ := j
  rcases x with p | q <;> rcases y with p' | q'
  · have h1 := (hmem p (Finset.inl_mem_disjSum.mp hx)).1
    have h2 := (hmem p' (Finset.inl_mem_disjSum.mp hy)).1
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, dif_pos h1, dif_pos h2, inner_toLp h1 h2, gramL]
  · have h1 := (hmem p (Finset.inl_mem_disjSum.mp hx)).1
    have h2 := (hmem q' (Finset.inr_mem_disjSum.mp hy)).2
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, Sum.elim_inr, dif_pos h1, dif_pos h2,
      inner_toLp h1 h2, gramL]
  · have h1 := (hmem q (Finset.inr_mem_disjSum.mp hx)).2
    have h2 := (hmem p' (Finset.inl_mem_disjSum.mp hy)).1
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, Sum.elim_inr, dif_pos h1, dif_pos h2, gramL]
    rw [← inner_conj_symm, inner_toLp h2 h1]
  · have h1 := (hmem q (Finset.inr_mem_disjSum.mp hx)).2
    have h2 := (hmem q' (Finset.inr_mem_disjSum.mp hy)).2
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inr, dif_pos h1, dif_pos h2, inner_toLp h1 h2, gramL]

end L2

end

end Formalism.FourierDecayAlt.P.PBK
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.QRadialDecompositionOfPieces
section
theorem Formalism.FourierDecayAlt.P.q_radial_decomposition_of_pieces : Formalism.FourierDecayAlt.Q.RadialDecompositionOfParts :=
  radial_decomposition_of_parts
end

