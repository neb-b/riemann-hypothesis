module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def GlobCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d : ℝ) : Prop :=
  ∀ Tm ∈ Θ, B.CkOn ⊤ (B.GV k r) Tm.coef ∧ B.CkOn ⊤ (B.GV k r) Tm.coefAdj ∧
    ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r,
        ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ d ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ d

def nDim (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

def bddHat (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  {x | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ X ∈ MA.hatSet P L, x = b * X}

def JDHatBdd : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 ≤ P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ X ∈ MA.hatSet P L, ∀ b ∈ Submonoid.closure (MA.bddSet P L), X * b ∈ Submodule.span ℂ (bddHat P L)

def JDHatOp : Prop :=
  ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
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
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ X ∈ MA.hatSet (D.parOf S v) L,
        ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
          (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ B.SmoothCoef (B.GPos (T v).base) t.2 ∧
            B.Commutes (T v).base (B.GPos (T v).base) t.2 ∧
            GlobCoef t.2 (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder t.2 : ℝ) ≤ Cc * nDim S.G.k S.G.r) ∧
          ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
            MA.actA (D.parOf S v) X (trJ S T v e J) =
              (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

def JDJComm : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (d A : ℝ), 0 ≤ d →
      B.SmoothCoef (B.GPos (T v).base) Θ → B.Commutes (T v).base (B.GPos (T v).base) Θ → GlobCoef Θ d →
      Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d ≤ A →
      ∀ F : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        (∀ m : ℕ, B.InCC A m F) → B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        B.JF (T v).base (B.opApply Θ F) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧
          ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            B.opApply Θ (B.JF (T v).base F) (B.gq (T v).base x) = B.JF (T v).base (B.opApply Θ F) (B.gq (T v).base x)

def JDCCLower : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d A : ℝ),
    0 ≤ d → GlobCoef Θ d → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → (∀ m : ℕ, B.InCC A m F) →
      B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧ ∀ m : ℕ, B.InCC (A - d) m (B.opApply Θ F)

def TransferSquareIntegrable : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ A : ℝ, Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r ≤ A →
      ∀ F : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        (∀ m : ℕ, B.InCC A m F) → B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        ∀ π, MeasureTheory.Integrable
          (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF (T v).base F) π) q‖ ^ 2) (MA.mu0 (D.parOf S v).r (D.parOf S v).TT)

def BoundedOperatorsSquareIntegrable : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), ∀ u : M.Ty P → MA.SmQ P.r P.TT,
      (∀ π, MeasureTheory.Integrable (fun q => ‖MA.evQ P (u π) q‖ ^ 2) (MA.mu0 P.r P.TT)) →
      ∀ π, MeasureTheory.Integrable (fun q => ‖MA.evQ P (MA.actA P b u π) q‖ ^ 2) (MA.mu0 P.r P.TT)

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLam
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

section cfg

variable (c : Sz.Cfg)

theorem cfg_v_sub (i : ℕ) : c.v i - c.v (i + 1) = 4 * c.Del := by
  simp only [Sz.Cfg.v]
  push_cast
  ring

theorem cfg_v_ge_vlast (hok : c.Ok) (i : ℕ) (hi : i + 1 ≤ c.k) : c.vlast ≤ c.v i := by
  have hD := hok.hDel
  have hi' : (i : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hi
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith

theorem cfg_v_lt (hok : c.Ok) {i j : ℕ} (hij : i < j) : c.v j < c.v i := by
  have hD := hok.hDel
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith

theorem cfg_b_lt (hok : c.Ok) : ∀ {j j' : ℕ}, 1 ≤ j → j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j j' hj hjj' hj'm
  induction j' with
  | zero => omega
  | succ n ih =>
    have hg := hok.hgap n (by omega) (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjj' with h | h
    · have := ih h (by omega)
      linarith
    · subst h
      linarith

theorem cfg_b_ge_one (hok : c.Ok) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.lt_or_ge 1 j with h | h
  · have := cfg_b_lt c hok (le_refl 1) h hjm
    linarith [hok.hb1]
  · have e : j = 1 := by omega
    subst e
    exact hok.hb1

theorem cfg_interlaces (r : ℕ) (hm : c.m = 2 * r + 2) (hk : 2 ≤ c.k) (hok : c.Ok) (de : ℕ → ℝ)
    (hde : ∀ i, de i = 0 ∨ de i = 1) :
    C7.LamInterlaces c.k r (c.u de) (fun s : Fin (c.k + 2 * r + 1) => c.lam ((s : ℕ) + 1)) := by
  have hk4 := hok.hk
  have hD := hok.hDel
  have hv0 := hok.hv0
  have hb1 := hok.hb1
  have ha := hok.ha
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk4
  have hlamv : ∀ s : ℕ, s < c.k → c.lam s = c.v s := fun s hs => by
    rw [Sz.Cfg.lam, if_pos hs]
  have hlamb : ∀ s : ℕ, ¬ s < c.k → c.lam s = -c.b (s + 1 - c.k) := fun s hs => by
    rw [Sz.Cfg.lam, if_neg hs]
  have hu1 : c.u de 1 = c.a := by rw [Sz.Cfg.u, if_pos rfl]
  have huk : c.u de c.k = c.ulast := by rw [Sz.Cfg.u, if_neg (by omega), if_pos rfl]
  have hum : ∀ j : ℕ, j ≠ 1 → j ≠ c.k → c.u de j = c.v (j - 1) - 1 / 2 - de (j - 1) * c.Del :=
    fun j h1 h2 => by rw [Sz.Cfg.u, if_neg h1, if_neg h2]
  have hde0 : ∀ j, 0 ≤ de j * c.Del ∧ de j * c.Del ≤ c.Del := fun j => by
    rcases hde j with h | h <;> simp [h] <;> linarith
  have hul : c.ulast = if c.top then -c.bp else c.vlast - 1 / 2 := rfl
  have hvk : c.v (c.k - 1) = c.vlast := by
    simp only [Sz.Cfg.v]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  refine ⟨?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · intro s t hst
    have hst' : (s : ℕ) < t := hst
    have ht := t.isLt
    show c.lam ((t : ℕ) + 1) < c.lam ((s : ℕ) + 1)
    by_cases h1 : (t : ℕ) + 1 < c.k
    · rw [hlamv _ h1, hlamv _ (by omega)]
      exact cfg_v_lt c hok (by omega)
    · rw [hlamb _ h1]
      by_cases h2 : (s : ℕ) + 1 < c.k
      · rw [hlamv _ h2]
        have := cfg_b_ge_one c hok (j := (t : ℕ) + 1 + 1 - c.k) (by omega) (by omega)
        have := cfg_v_ge_vlast c hok ((s : ℕ) + 1) (by omega)
        linarith
      · rw [hlamb _ h2]
        have := cfg_b_lt c hok (j := (s : ℕ) + 1 + 1 - c.k) (j' := (t : ℕ) + 1 + 1 - c.k)
          (by omega) (by omega) (by omega)
        linarith
  · show c.lam ((i : ℕ) + 1) < c.u de ((i : ℕ) + 1)
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0, zero_add, hlamv 1 (by omega), hu1]
      have : 0 < 4 * (c.k : ℝ) * c.Del := by
        have := mul_le_mul hkR hD zero_le_one (by linarith)
        linarith
      linarith
    · by_cases h2 : (i : ℕ) + 1 < c.k
      · rw [hlamv _ h2, hum _ (by omega) (by omega), Nat.add_sub_cancel]
        have := cfg_v_sub c (i : ℕ)
        have := hde0 (i : ℕ)
        linarith
      · have e : (i : ℕ) + 1 = c.k := by omega
        rw [hlamb _ h2, e, Nat.add_sub_cancel_left, huk, hul]
        split_ifs with htp
        · have := (hok.htop htp).2
          linarith
        · linarith
  · show c.u de ((i : ℕ) + 2) < c.lam ((i : ℕ) + 1)
    rw [hlamv _ (by omega)]
    by_cases h2 : (i : ℕ) + 2 = c.k
    · have e : (i : ℕ) + 1 = c.k - 1 := by omega
      rw [h2, huk, hul, e, hvk]
      split_ifs with htp
      · have := (hok.htop htp).1
        linarith
      · linarith
    · have e : (i : ℕ) + 2 - 1 = (i : ℕ) + 1 := by omega
      rw [hum _ (by omega) h2, e]
      have := hde0 ((i : ℕ) + 1)
      linarith

end cfg

theorem eigenvalue_configuration_interlaces : LamCfgInterlaces := by
  intro E _ _ _ Wp Wq _ _ _ _ S hk hok hw hw' v
  exact ⟨cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de hw.1,
    cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de' hw'.1⟩

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DiscreteSeriesFormOneReduction
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

end Formalism.FourierDecayAlt.P.DDSmoothness

namespace Formalism.FourierDecayAlt.P

theorem discrete_series_form_one_reduction : Formalism.FourierDecayAlt.ThreeDimData.DDFormOneOfSteps := DDSmoothness.discrete_form_one_side

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedFrameProperty
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x7

theorem fixed_frame_property : C2.FixFrame := by
  intro k r z hz
  ext g
  constructor
  · rintro ⟨hgV, hfix⟩
    have hS : g ∈ Sset k r z := by
      rw [← standard_flag_property k r z hz]
      exact ⟨hgV, fun a => by simp [hfix a]⟩
    refine ⟨hS, uMap_eq hz g 1 fun b => ?_⟩
    simp [Matrix.one_apply, hfix b]
  · rintro ⟨hS, hU⟩
    have hS' := hS
    rw [← standard_flag_property k r z hz] at hS'
    refine ⟨hS'.1, fun a => ?_⟩
    rw [((unipotent_map_frame k r z hz).1 g hS).1 a, hU]
    simp [Matrix.one_apply]

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianXiVector
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace HermitianXiVector

open C2x5 FlagSpanVanishing

variable {k r : ℕ}

lemma herm_add_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b w : Fin n → ℂ) :
    herm H (a + b) w = herm H a w + herm H b w := by
  simp only [herm, mulVec_add, dotProduct_add]

lemma herm_smul_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (a w : Fin n → ℂ) :
    herm H (s • a) w = s * herm H a w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma herm_add_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v a b : Fin n → ℂ) :
    herm H v (a + b) = herm H v a + herm H v b := by
  simp only [herm, star_add, add_dotProduct]

lemma herm_smul_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (v a : Fin n → ℂ) :
    herm H v (s • a) = conj s * herm H v a := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]
  try rfl

lemma herm_neg_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a w : Fin n → ℂ) :
    herm H (-a) w = -herm H a w := by
  simp only [herm, mulVec_neg, dotProduct_neg]

lemma herm_X_left (v u : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0)
    (hu : ∀ i : Fin (2 * r + k + 1), r + k < i.val → u i = 0) : herm (Hpk k r) v u = 0 := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : r + k < i.val
  · rw [hu i hi, star_zero, zero_mul]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    by_cases hj : r ≤ j.val
    · rw [hv j hj, mul_zero]
    · rw [show Hpk k r i j = 0 by
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega), zero_mul]

lemma herm_X_right (v u : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0)
    (hu : ∀ i : Fin (2 * r + k + 1), r + k < i.val → u i = 0) : herm (Hpk k r) u v = 0 := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : r ≤ i.val
  · rw [hv i hi, star_zero, zero_mul]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    by_cases hj : r + k < j.val
    · rw [hu j hj, mul_zero]
    · rw [show Hpk k r i j = 0 by
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega), zero_mul]

lemma xiV_X (ξ : Fin r → ℂ) : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → C2.xiV k r ξ i = 0 := by
  intro i hi
  unfold C2.xiV
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

lemma xiV_apply_last_block_zero (ξ : Fin r → ℂ) : ∀ i : Fin (2 * r + k + 1), r + k < i.val → C2.xiV k r ξ i = 0 := by
  intro i hi
  unfold C2.xiV
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

lemma vmv_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (a b y : Fin n → ℂ) :
    vecMulVec a (star (H *ᵥ b)) *ᵥ y = herm H y b • a := by
  have hH' : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    rwa [conjTranspose_apply] at this
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, herm, Pi.star_apply, star_sum, star_mul', hH', Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

private lemma hpk_conjTranspose_self (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | (simp; done) | (exfalso; omega)

lemma nEich_apply (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    C2.nEich k r z ξ *ᵥ y = y + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • (-(herm (Hpk k r) y z) • C2.xiV k r ξ +
      herm (Hpk k r) y (C2.xiV k r ξ) • z + ((1 / 2 : ℂ) * herm (Hpk k r) y (C2.xiV k r ξ)) • C2.xiV k r ξ) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := hpk_conjTranspose_self k r
  first
  | simp only [C2.nEich, add_mulVec, one_mulVec, smul_mulVec, neg_mulVec, vmv_apply _ hH, neg_smul, smul_smul]
  | simp only [C2.nEich, add_mulVec, one_mulVec, Matrix.smul_mulVec_assoc, neg_mulVec, vmv_apply _ hH, neg_smul, smul_smul]

end HermitianXiVector

namespace HermitianXiVector

open C2x5 FlagSpanVanishing

variable {k r : ℕ}

lemma herm_neg_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v a : Fin n → ℂ) :
    herm H v (-a) = -herm H v a := by
  simp only [herm, star_neg, neg_dotProduct]

lemma herm_basis {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    herm H (A *ᵥ Pi.single j 1) (A *ᵥ Pi.single i 1) = (Aᴴ * H * A) i j := by
  have e1 : herm H (A *ᵥ Pi.single j 1) (A *ᵥ Pi.single i 1) =
      herm (Aᴴ * H * A) (Pi.single j 1) (Pi.single i 1) := by
    simp only [herm, star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]
  rw [e1]
  simp [herm, dotProduct, mulVec, Pi.single_apply]

lemma uh_of_herm {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ y y', herm H (A *ᵥ y) (A *ᵥ y') = herm H y y') : A ∈ UH H := by
  show Aᴴ * H * A = H
  ext i j
  have h1 := h (Pi.single j 1) (Pi.single i 1)
  rw [herm_basis] at h1
  rw [h1]
  simp [herm, dotProduct, mulVec, Pi.single_apply]

lemma nEich_herm {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) (y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (C2.nEich k r z ξ *ᵥ y) (C2.nEich k r z ξ *ᵥ y') = herm (Hpk k r) y y' := by
  have hH := GBasic.Hpk_herm k r
  have hxx : herm (Hpk k r) (C2.xiV k r ξ) (C2.xiV k r ξ) = 0 :=
    herm_X_left _ _ (xiV_X ξ) (xiV_apply_last_block_zero ξ)
  have hxz : herm (Hpk k r) (C2.xiV k r ξ) z = 0 :=
    herm_X_left _ z (xiV_X ξ) (fun i hi => hz.1 i (Or.inr hi))
  have hzx : herm (Hpk k r) z (C2.xiV k r ξ) = 0 :=
    herm_X_right _ z (xiV_X ξ) (fun i hi => hz.1 i (Or.inr hi))
  have hzz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by rw [hzz_real]; push_cast; ring
  have hxy : herm (Hpk k r) (C2.xiV k r ξ) y' = conj (herm (Hpk k r) y' (C2.xiV k r ξ)) := ggHerm_swap _ hH _ _
  have hzy : herm (Hpk k r) z y' = conj (herm (Hpk k r) y' z) := ggHerm_swap _ hH _ _
  have hT : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz.2.ne'
  have hcc : conj ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) := by
    rw [map_div₀, map_one, Complex.conj_ofReal]
  rw [nEich_apply, nEich_apply]
  simp only [herm_add_l, herm_add_r, herm_smul_l, herm_smul_r, herm_neg_l, herm_neg_r, hxx, hxz, hzx, hzz,
    hxy, hzy, hcc, map_neg, map_mul, map_div₀, map_one, map_ofNat]
  set c : ℂ := (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) with hc
  have hcT : c * ((Tz k r z : ℝ) : ℂ) = 1 := by rw [hc]; field_simp
  linear_combination (-(c * herm (Hpk k r) y (C2.xiV k r ξ) * conj (herm (Hpk k r) y' (C2.xiV k r ξ)))) * hcT

lemma nEich_col {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) :
    WeylGroupFacts.col k r (C2.nEich k r z ξ) := by
  intro i j hj hij
  have e : (C2.nEich k r z ξ *ᵥ bvec j) i = C2.nEich k r z ξ i j := by rw [mulVec_bvec]
  rw [← e, nEich_apply]
  have hjx : herm (Hpk k r) (bvec j) (C2.xiV k r ξ) = 0 :=
    herm_X_right (C2.xiV k r ξ) (bvec j) (xiV_X ξ) (fun p hp => by
      simp only [bvec, Pi.single_apply]; rw [if_neg (fun e => by rw [e] at hp; omega)])
  rw [hjx]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, Pi.neg_apply, zero_mul, mul_zero,
    add_zero]
  by_cases hir : r ≤ i.val
  · rw [xiV_X ξ i hir]; simp
  · have hjr : j.val < r := by omega
    have hjz : herm (Hpk k r) (Pi.single j 1) z = 0 :=
      herm_X_left (Pi.single j 1) z (fun p hp => by
        simp only [Pi.single_apply]; rw [if_neg (fun e => by rw [e] at hp; omega)])
        (fun p hp => hz.1 p (Or.inr hp))
    rw [hjz]; simp

lemma nEich_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) :
    C2.nEich k r z ξ ∈ Nset k r := by
  rw [WeylGroupFacts.nset_iff]
  exact ⟨uh_of_herm _ _ (nEich_herm hz ξ), nEich_col hz ξ⟩

end HermitianXiVector

end Formalism.FourierDecayAlt.P
end

