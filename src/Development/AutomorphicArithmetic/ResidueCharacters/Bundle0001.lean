module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomicAlt
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

def sN (l N : ℕ) : ℕ := max 1 (N.factorization l)

def lamN (l N h : ℕ) : ℕ := sN l N + Nat.log l (2 * h) + Nat.log l N + 1

def eL (l N h : ℕ) : ℕ := 32 * (2 * h * sN l N + 1) + lamN l N h

def c0L (l N h n : ℕ) : ℕ := 20 * (n + 1) * lamN l N h

def cBL (l N h n t : ℕ) : ℕ := 40 * (t + 1) * (n + 1) * lamN l N h

variable {l : ℕ} [Fact l.Prime]

structure Cyc (N : ℕ) (K LL : FinExt l) : Prop where
  lvl : l = 2 → 4 ∣ N
  pos : 0 < N
  le : K.1 ≤ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ Nat.lcm l N = 1}
  coef : ∀ x : Om l, x ^ Nat.lcm l N = 1 → x ∈ LL.1

variable (P : LocPrime l)

def LiftK : Prop := ∀ (N h : ℕ) (K LL : FinExt l), Cyc N K LL →
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L),
    IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → F.Onto →
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) → F.LiftF (P.PD K) (eL l N h)


set_option synthInstance.maxHeartbeats 400000 in
def InvariantsKilledOverCyclotomic : Prop := ∀ (N h n : ℕ) (K LL : FinExt l), Cyc N K LL →
  ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : Finset ℤ), U.card ≤ n → (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) →
    IsCrys (P.PD K) T.ρ → (∀ τ, JumpsInV (P.PD K) T.ρ τ (U : Set ℤ)) → (∀ τ, ¬ IsJumpV (P.PD K) T.ρ τ 0) →
    ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((l : ↥(OL LL)) ^ c0L l N h n) • x = 0

def TBK : Prop := ∀ (N h n t : ℕ) (K LL : FinExt l), Cyc N K LL → t ≤ h →
  ∀ (J : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Set ℤ) (U : Finset ℤ), U.card ≤ n → (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) →
    (∀ τ, J τ ⊆ (U : Set ℤ)) → TBAt (P.PD K) (O := ↥(OL LL)) (IK K) J t (cBL l N h n t)

end UpperTheory.N

end
end

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.NumBounds
section
open Formalism.MainNotions

namespace UpperTheory.N.Num

noncomputable def lam (l s : ℕ) (h : ℝ) : ℝ := (s : ℝ) + Real.logb l (2 * h) + 1

variable {l s : ℕ} {h : ℝ}

theorem logb_nonneg (hl : 2 ≤ l) (hh : 1 ≤ h) : 0 ≤ Real.logb l (2 * h) :=
  Real.logb_nonneg (by exact_mod_cast (by omega : 1 < l)) (by linarith)

theorem s_le_lam (hl : 2 ≤ l) (hh : 1 ≤ h) : (s : ℝ) + 1 ≤ lam l s h := by
  unfold lam
  linarith [logb_nonneg hl hh]

theorem one_le_lam (hl : 2 ≤ l) (hh : 1 ≤ h) : 1 ≤ lam l s h := by
  have := s_le_lam (s := s) hl hh
  have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  linarith

theorem natLog_le_logb (hl : 2 ≤ l) {n : ℕ} {y : ℝ} (hy : 1 ≤ y) (hn : (n : ℝ) ≤ y) :
    (Nat.log l n : ℝ) ≤ Real.logb l y := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [Nat.log_zero_right, Nat.cast_zero]
    exact Real.logb_nonneg hl' hy
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    exact (Real.natLog_le_logb n l).trans (Real.logb_le_logb_of_le hl' hn0 hn)

theorem natLog_le_lam (hl : 2 ≤ l) (hs : 1 ≤ s) (hh : 1 ≤ h) {n : ℕ} (hn : (n : ℝ) ≤ 8 * h) :
    (Nat.log l n : ℝ) ≤ lam l s h := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have h1 := natLog_le_logb hl (y := 4 * (2 * h)) (by linarith) (by linarith)
  rw [Real.logb_mul (by norm_num) (by linarith)] at h1
  have h2 : Real.logb l 4 ≤ 2 := by
    rw [Real.logb_le_iff_le_rpow hl1 (by norm_num)]
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have : (1 : ℝ) ≤ s := by exact_mod_cast hs
  unfold lam; linarith

theorem lam_le (hl : 2 ≤ l) (hs : 1 ≤ s) (hh : 1 ≤ h) : lam l s h ≤ 6 * h * s := by
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hlog2 := Real.log_two_gt_d9
  have hlogl : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl2
  have hx : 0 < 2 * h := by linarith
  have hlx : Real.log (2 * h) ≤ 2 * h - 1 := Real.log_le_sub_one_of_pos hx
  have hlx0 : 0 ≤ Real.log (2 * h) := Real.log_nonneg (by linarith)
  have hb : Real.logb l (2 * h) ≤ 3 * h := by
    unfold Real.logb
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  unfold lam
  nlinarith

end UpperTheory.N.Num
end

-- bundled from Development.AutomorphicArithmetic.ResidueCharacters.TwistDef
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

namespace UpperTheory.N.TwistK

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

def TBe (PD : PeriodData G Qp K₀ K B BdR) (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O]
    [Algebra O LL] (I : Subgroup G) : Prop :=
  ∀ (e : ℕ) (Ve : LocLat G Qp LL O), Module.finrank LL Ve.V = 1 →
    (∀ g x, Ve.ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) →
    (∀ n : ℕ, Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology Ve.L ⧸ divisibleFiniteCohomology PD Ve.L)
        (((PD.p : ℕ) : O) ^ n)) ≤ (((Module.finrank Qp K + 1) * n : ℕ) : ℕ∞) * lenOl PD (O := O)) ∧
    (0 < e → HfD PD Ve.L = BD Ve.L) ∧
    (e = 0 → ∀ c : G → Ve.V ⧸ Ve.L.T, c ∈ HfD PD Ve.L ↔
      (c ∈ divisibleCocycles Ve.L ∧ ∃ x, ∀ g ∈ I, c g = actD Ve.L g x - x))

end
end UpperTheory.N.TwistK

end
end

