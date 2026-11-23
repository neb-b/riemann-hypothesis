module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0178
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVstep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0125
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroOfTrace
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_zero_of_trace {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (u v : Fin (2 * r + k + 1) → ℂ)
    (h1 : (Matrix.trace (ζ * Xuv k r u v)).re = 0)
    (h2 : (Matrix.trace (ζ * Xuv k r u (Complex.I • v))).re = 0) :
    herm (Hpk k r) (ζ *ᵥ u) v = 0 := by
  rw [trace_xuv] at h1 h2
  have hs : ∀ w, herm (Hpk k r) (ζ *ᵥ w) u = -star (herm (Hpk k r) (ζ *ᵥ u) w) := by
    intro w
    rw [herm_skew hζ, herm_swap w]
  rw [hs] at h1 h2
  rw [herm_smul_right] at h2
  set A := herm (Hpk k r) (ζ *ᵥ u) v
  simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
  constructor <;> linarith

theorem herm_bvec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    herm (Hpk k r) x (bvec i) = (Hpk k r *ᵥ x) i := by
  rw [herm_eq, Finset.sum_eq_single i]
  · simp [bvec]
  · intro j _ hj; simp [bvec, hj]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem herm_e (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) x (bvec (eI k r b)) = x (esI k r b) := by
  rw [herm_bvec, hpk_mulVec, if_pos (Or.inl (by simp [eI]))]
  rfl

theorem herm_es (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) x (bvec (esI k r b)) = x (eI k r b) := by
  rw [herm_bvec, hpk_mulVec, if_pos (Or.inr (by simp [esI]; omega))]
  congr 1
  apply Fin.ext
  simp [eI, esI]
  omega

theorem herm_w (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    herm (Hpk k r) x (bvec i) = if i.val = r + k then -x i else x i := by
  rw [herm_bvec, hpk_mulVec, if_neg (by omega)]

theorem inWb_sub {u v : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (hv : inWb k r v) : inWb k r (u - v) := by
  intro i hi; simp [hu i hi, hv i hi]

theorem inWb_smul (c : ℂ) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) : inWb k r (c • u) := by
  intro i hi; simp [hu i hi]

def sg (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_mulVec_wb {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ u) i = sg (k := k) (r := r) i * u i := by
  rw [hpk_mulVec, sg]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, hu i h, hu ⟨2 * r + k - i.val, by omega⟩ (by simp; omega), mul_zero]
  · rw [if_neg h]
    split_ifs <;> ring

def KI (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩

theorem herm_wb {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u y = ∑ i ∈ Finset.univ.erase (KI k r), star (y i) * u i - star (y (KI k r)) * u (KI k r) := by
  rw [herm_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (KI k r))]
  have hK : sg (k := k) (r := r) (KI k r) = -1 := by simp [sg, KI]
  rw [hpk_mulVec_wb hu, hK]
  have : ∀ i ∈ Finset.univ.erase (KI k r), star (y i) * (Hpk k r *ᵥ u) i = star (y i) * u i := by
    intro i hi
    rw [hpk_mulVec_wb hu]
    have : i.val ≠ r + k := fun e => (Finset.mem_erase.1 hi).1 (Fin.ext (by simp [KI, e]))
    simp [sg, this]
  rw [Finset.sum_congr rfl this]
  ring

theorem re_star_mul_self (a : ℂ) : (star a * a).re = ‖a‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem wb_definite {z w : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hw : inWb k r w) (hwz : herm (Hpk k r) w z = 0) (hww : (herm (Hpk k r) w w).re ≤ 0) : w = 0 := by
  set S := Finset.univ.erase (KI k r)
  set K := KI k r
  have e2 : (herm (Hpk k r) w w).re = ∑ i ∈ S, ‖w i‖ ^ 2 - ‖w K‖ ^ 2 := by
    rw [herm_wb hw, Complex.sub_re, Complex.re_sum, re_star_mul_self]
    simp only [re_star_mul_self]
    rfl
  have eT : Tz k r z = ‖z K‖ ^ 2 - ∑ i ∈ S, ‖z i‖ ^ 2 := by
    rw [Tz, herm_wb hz, Complex.sub_re, Complex.re_sum, re_star_mul_self]
    simp only [re_star_mul_self]
    ring
  rw [herm_wb hw, sub_eq_zero] at hwz
  have hn : ‖z K‖ * ‖w K‖ ≤ ∑ i ∈ S, ‖z i‖ * ‖w i‖ := by
    calc ‖z K‖ * ‖w K‖ = ‖star (z K) * w K‖ := by rw [norm_mul, norm_star]
      _ = ‖∑ i ∈ S, star (z i) * w i‖ := by rw [hwz]
      _ ≤ ∑ i ∈ S, ‖star (z i) * w i‖ := norm_sum_le _ _
      _ = ∑ i ∈ S, ‖z i‖ * ‖w i‖ := by simp only [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖z i‖) (fun i => ‖w i‖)
  set P := ∑ i ∈ S, ‖w i‖ ^ 2
  set Q := ∑ i ∈ S, ‖z i‖ ^ 2
  set m := ∑ i ∈ S, ‖z i‖ * ‖w i‖
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => by positivity)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => by positivity)
  have ha : 0 ≤ ‖w K‖ := norm_nonneg _
  have hc : 0 ≤ ‖z K‖ := norm_nonneg _
  have h1 : P ≤ ‖w K‖ ^ 2 := by linarith
  have h2 : Q < ‖z K‖ ^ 2 := by linarith
  have h3 : (‖z K‖ * ‖w K‖) ^ 2 ≤ m ^ 2 := by
    have : 0 ≤ ‖z K‖ * ‖w K‖ := by positivity
    exact pow_le_pow_left₀ this hn 2
  have h4 : (‖z K‖ * ‖w K‖) ^ 2 ≤ Q * ‖w K‖ ^ 2 := by
    calc (‖z K‖ * ‖w K‖) ^ 2 ≤ m ^ 2 := h3
      _ ≤ Q * P := hcs
      _ ≤ Q * ‖w K‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hQ
  have h5 : ‖w K‖ ^ 2 * (‖z K‖ ^ 2 - Q) ≤ 0 := by nlinarith
  have h6 : ‖w K‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < ‖w K‖ ^ 2 * (‖z K‖ ^ 2 - Q) := mul_pos hcon (by linarith)
    linarith
  have hwK : w K = 0 := by
    have : ‖w K‖ = 0 := by nlinarith
    exact norm_eq_zero.1 this
  have hP0 : P = 0 := le_antisymm (by nlinarith) hP
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hP0
  funext i
  by_cases hi : i = K
  · rw [hi, hwK]; rfl
  · have := hall i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
    rw [this]; rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableOfDecay4
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

def FormOne : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (X : Q.ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (μ : Measure (Formalism.QuantumDeterminants.Mt (JC.parLev P0 j).k (JC.parLev P0 j).r))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π')) (JC.parLev P0 j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π'))) (l0 : ℕ),
    P5.IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 →
    KB.ZetaNorm (T.bs j) μ →
    ∀ (w : List C.Letter) (F F' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ Φ' : Wd.Ix (Fin w.length) →
        Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (ε : ℝ),
      0 < ε → (∀ a, JC.NiceCoef (T.bs j) ε (F a)) → (∀ a, JC.NiceCoef (T.bs j) ε (F' a)) →
      (∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F a)) y.1 y.2) →
      (∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ' a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F' a)) y.1 y.2) →
      D.formLev T (M.sgn P0 l0) j w F F' = P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ' 0

def ZetaNormExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq), ∃ μ : Measure (Mt k r), KB.ZetaNorm Bs μ

theorem integrable_of_decay4 {φ : ℂ → ℂ} (hφ : Continuous φ) {C : ℝ}
    (hC : ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) : Integrable φ := by
  have hd : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(4 : ℝ))) volume := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]; norm_num
  refine Integrable.mono' (hd.const_mul C) hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have e : (1 + ‖t‖) ^ (-4 : ℤ) = (1 + ‖t‖) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_intCast]; norm_num
  rw [← e]; exact hC t

theorem nice_common {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {S : Type} [Fintype S] (Bs : B.RealPlaceData k ρ Wp Wq)
    {x : S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : ∀ a, KB.CptCoef Bs (x a)) :
    ∃ ε, 0 < ε ∧ ∀ a, JC.NiceCoef Bs ε (x a) := by
  classical
  choose R hR using fun a => (h a).2.1
  choose εf hεf0 hεf using fun a => (h a).2.2
  let Sε : Finset ℝ := insert 1 (Finset.univ.image εf)
  have hne : Sε.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨Sε.min' hne, ?_, fun a => ⟨(h a).1, fun A m => ?_, fun g hg hg0 => ?_⟩⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      exact hεf0 a
  · refine Formalism.FourierDecayAlt.P.JFxG.cptInCC_G (h a).1 (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k ρ (R a)) (fun g hg hgC => ?_) A m
    by_contra h0
    exact hgC (hR a g hg h0)
  · exact le_trans (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a))))
      (hεf a g hg hg0)

end Formalism.FourierDecayAlt.P.PBO
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def GEqs (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : B.Mat k r → E) : Prop :=
  Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') J ∧
  (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Formalism.REAL.RdV X J g = c • J g) ∧
  (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.LdV X J g = c • J g) ∧
  (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs → ∀ w : ℂ, ∃ c : ℂ,
    ∀ g ∈ JF.Om k r z z', Q.capLft k r Bs w J g = c • J g) ∧
  (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z'] Bs → ∀ w : ℂ, ∃ c : ℂ,
    ∀ g ∈ JF.Om k r z z', Q.capR k r Bs w J g = c • J g) ∧
  (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.CV k r (Y : ℂ) J g = c • J g)

def NDiff : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (m : ℕ∞) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    J ∈ Gr.FFlM m k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Formalism.REAL.RdV X J g = c • J g) ∧
    (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Q.LdV X J g = c • J g)

def UCap : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (u u' : ℕ → ℝ) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' →
    J ∈ Gr.FFlM ((2 * r + k + 1 : ℕ) : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [D.z] Bs → ∀ w : ℂ, ∃ c : ℂ,
      ∀ g ∈ JF.Om k r D.z D.z', Q.capLft k r Bs w J g = c • J g) ∧
    (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [D.z'] Bs → ∀ w : ℂ, ∃ c : ℂ,
      ∀ g ∈ JF.Om k r D.z D.z', Q.capR k r Bs w J g = c • J g)

def GEqsPost : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : B.Mat k r → E) (ℓ : E →L[ℂ] ℂ), GEqs k r z z' J → GEqs k r z z' (fun g => ℓ (J g))

def SmoothOfCoeffs : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (Dm : Set (B.Mat k r))
    (J : B.Mat k r → E), (∀ ℓ : E →L[ℂ] ℂ, Q.SmoothLev k r 0 Dm (fun g => ℓ (J g))) → Q.SmoothLev k r 0 Dm J

def GChart : Prop :=
  ∀ (k r : ℕ), ∃ d : ℕ, ∀ g₀ ∈ B.GV k r, ∃ (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)),
    IsOpen O ∧ IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ κ O ∧ ContDiffOn ℝ ∞ Φ U ∧
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) ∧ (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g)

def ChartEqs : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsOpen O → IsOpen U → ContDiffOn ℝ ∞ κ O → ContDiffOn ℝ ∞ Φ U →
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) → (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g) →
    (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') → GEqs k r z z' u →
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → SOp d),
      (∀ j i w, ContDiffOn ℝ ∞ ((P j).a i w) O) ∧ (∀ j, (P j).ord ≤ 2 * r + k + 1) ∧
      ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
      (∀ j, ∀ x ∈ O, (P j).app (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → (∀ j, (P j).symb x ξ = 0) →
        ∃ Ξ : B.Mat k r, B.inLie k r Ξ ∧ Ξ ≠ 0 ∧ IsNilpotent Ξ ∧
          (∀ X ∈ JfS.lieOf (UWset k r z) ∪ JfS.lieOf (Nset k r), (Matrix.trace (Ξ * X)).re = 0) ∧
          (∀ X ∈ JfS.lieOf (UWset k r z') ∪ JfS.lieOf (Nset k r),
            (Matrix.trace (Ξ * (κ x * X * (κ x)⁻¹))).re = 0)

def ClassToWeak : Prop :=
  ∀ (d N : ℕ) (P : SOp d) (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ),
    IsOpen U → (∀ i w, ContDiffOn ℝ ∞ (P.a i w) U) → P.ord ≤ N → ContDiffOn ℝ (N : WithTop ℕ∞) u U →
    (∀ x ∈ U, P.app u x = 0) →
    ∀ φ : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x, u x * P.tr φ x = 0

def LieSsetSplit : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ X ∈ JfS.lieOf (Sset k r z), ∃ A ∈ JfS.lieOf (UWset k r z), ∃ Bn ∈ JfS.lieOf (Nset k r), X = A + Bn

def GRegScalar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → GEqs k r z z' u →
    Q.SmoothLev k r 0 (Q.OmPlus k r z z') u

theorem gRegJ_of (hN : NDiff) (hU : UCap) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hS : GRegScalar) : GRegJ := by
  intro k r Wp Wq _ _ _ _ _ _ D u u' J hT hT' hF hCV
  have hG : GEqs k r D.z D.z' J := by
    obtain ⟨hn1, hn2⟩ := hN k r Wp Wq D _ J hF
    obtain ⟨hu1, hu2⟩ := hU k r Wp Wq D u u' J hT hT' hF
    refine ⟨?_, hn1, hn2, hu1, hu2, hCV⟩
    intro g₀ hg₀
    obtain ⟨U, F, hUo, hgU, hFc, hJF⟩ := hF.1 g₀ hg₀
    exact ⟨U, F, hUo, hgU, by simpa [Gr.smM] using hFc, hJF⟩
  exact hC k r (Wq →L[ℂ] Wp) _ J (fun ℓ =>
    hS k r D.z D.z' _ D.k_pos D.z_mem D.z'_mem D.T_pos D.T'_pos (hP k r D.z D.z' _ J ℓ hG))

theorem gRegScalar_of (hK : GChart) (hE : ChartEqs) (hW : ClassToWeak) (hR : EllRegW) (hSym : JfS.SymbolNil)
    (hL : LieSsetSplit) : GRegScalar := by
  intro k r z z' u hk hz hz' hT hT' hG g₀ hg₀
  obtain ⟨d, hd⟩ := hK k r
  have hg₀G : g₀ ∈ B.GV k r := hg₀.1.1
  obtain ⟨O, U, κ, Φ, hO, hU, hg₀U, hκ, hΦ, hκO, hΦU⟩ := hd g₀ hg₀G
  have hO' : IsOpen (O ∩ κ ⁻¹' Q.OmPlus k r z z') :=
    hκ.continuousOn.isOpen_inter_preimage hO (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z')
  have hU' : IsOpen (U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z')) :=
    hΦ.continuousOn.isOpen_inter_preimage hU hO'
  have hΦg₀ : Φ g₀ ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z' := by
    obtain ⟨h1, h2⟩ := hΦU g₀ hg₀U hg₀G
    refine ⟨h1, ?_⟩
    show κ (Φ g₀) ∈ Q.OmPlus k r z z'
    rw [h2]; exact hg₀.2
  have hκO' : ∀ x ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z',
      κ x ∈ B.GV k r ∧ κ x ∈ U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z') ∧ Φ (κ x) = x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hκO x hx.1
    refine ⟨h1, ⟨h2, ?_⟩, h3⟩
    show Φ (κ x) ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z'
    rw [h3]; exact hx
  have hΦU' : ∀ g ∈ U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z'), g ∈ B.GV k r →
      Φ g ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z' ∧ κ (Φ g) = g :=
    fun g hg hgG => ⟨hg.2, (hΦU g hg.1 hgG).2⟩
  obtain ⟨ι, hι, P, hPc, hPo, huc, hPu, hsym⟩ := hE k r z z' d _ _ κ Φ u hk hz hz' hT hT' hO' hU'
    (hκ.mono Set.inter_subset_left) (hΦ.mono Set.inter_subset_left) hκO' hΦU' (fun x hx => hx.2) hG
  have := hι
  have hsm : ContDiffOn ℝ ∞ (fun x => u (κ x)) (O ∩ κ ⁻¹' Q.OmPlus k r z z') := by
    refine hR d ι P _ _ hO' hPc huc.continuousOn
      (fun j φ hφ hφc hφs => hW d _ (P j) _ _ hO' (hPc j) (hPo j) huc (hPu j) φ hφ hφc hφs) ?_
    intro x hx ξ hξ
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨Ξ, hΞ, hΞ0, hnil, hl, hr⟩ := hsym x hx ξ hξ hall
    apply hΞ0
    have hxG := (hκO' x hx).1
    have hxOm : κ x ∈ Q.OmPlus k r z z' := hx.2
    refine hSym k r z z' hk hz hz' hT hT' (κ x) hxG ⟨hxOm.2, fun a => hxOm.1 ⟨(a : ℕ) + 1, by omega⟩ a.isLt⟩
      Ξ hΞ hnil ?_ ?_
    · intro X hX
      obtain ⟨A, hA, Bn, hB, rfl⟩ := hL k r z hz hT X hX
      simp only [mul_add, Matrix.trace_add, Complex.add_re]
      rw [hl A (Or.inl hA), hl Bn (Or.inr hB), add_zero]
    · intro X hX
      obtain ⟨A, hA, Bn, hB, rfl⟩ := hL k r z' hz' hT' X hX
      simp only [mul_add, add_mul, Matrix.trace_add, Complex.add_re]
      rw [hr A (Or.inl hA), hr Bn (Or.inr hB), add_zero]
  refine ⟨U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z'), fun g => u (κ (Φ g)), hU', ⟨hg₀U, hΦg₀⟩, ?_, ?_⟩
  · exact hsm.comp (hΦ.mono Set.inter_subset_left) (fun g hg => hg.2)
  · intro g hg hgG
    show u g = u (κ (Φ g))
    rw [(hΦU g hg.1 hgG.1).2]

theorem jfSmoothBuilt_of_leaves (hN : NDiff) (hU : UCap) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hK : GChart)
    (hE : ChartEqs) (hW : ClassToWeak) (hR : EllRegW) (hSym : JfS.SymbolNil) (hL : LieSsetSplit) :
    JfSmoothBuilt :=
  transfer_smooth_of_regularity (gRegJ_of hN hU hP hC (gRegScalar_of hK hE hW hR hSym hL))

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniOfCore
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniReduction

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem leftFubini_of_core (hC : LeftFubiniLemmas.CoreLF) : LeftFubiniLemmas.LeftFubini := by
  intro k r Wp Wq _ _ _ _ _ _ T hT j hj hj1 a ha
  obtain ⟨hab, rfl⟩ := ha
  have e : D.ptSize a + (r - D.ptSize a) = r := by omega
  have hd : ∀ q, D.ptDiag a q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne a hab q q.2
  obtain ⟨X, hX, μ, ℓ, sx, hsx, hmain⟩ := hC k (D.ptSize a) (r - D.ptSize a) r e hj1 (D.ptPerm a) (D.ptDiag a) hd
    Wp Wq (T.bs (D.ptSize a)) T.base (T.z_lev _ hj) (T.z'_lev _ hj) (T.π'_lev _ hj) (hT _ hj).2.1
    (Formalism.FourierDecayAlt.P.PBM.tower_haarW' T hT _ hj e) (hT _ hj).2.2 (hT 0 (Nat.zero_le r)).2.2
  refine ⟨X, hX, μ, ℓ, sx, hsx, fun g hg H hH hR => ?_⟩
  have hx : ∀ (h1 : D.ptSize a ≤ r) (h2 : r - D.ptSize a = r - D.ptSize a),
      LeftFubiniLemmas.levelZeroPointOver a h1 (D.castM h2 g) = D.castM e (U.mMap k (D.ptSize a) (r - D.ptSize a)
        (U.hMat (D.ptPerm a) (D.ptDiag a)) g) := by
    intro h1 h2
    unfold LeftFubiniLemmas.levelZeroPointOver
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hs : ∀ h2 : r - D.ptSize a = r - D.ptSize a,
      D.castF h2 (D.sliceAt k r T.base.z T.base.z' H a) =
        U.PhiFun (s := 0) k (r - D.ptSize a) (D.ptPerm a) (D.ptDiag a) (D.castV e.symm T.base.z)
          (D.castV e.symm T.base.z') (D.castF e H) (fun a => a.elim0) := by
    intro h2
    funext y
    unfold D.castF
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, D.sliceAt, dite_eq_left hj]
    rfl
  simp only [hx, hs]
  exact hmain g hg H hH hR

end Formalism.FourierDecayAlt.P.LeftFubiniReduction
end
end

