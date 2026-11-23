module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalLevelRelIndexLiftLevelEqCard
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevIdx

open Formalism.IndefR.Lev (finE)

variable {D : D7} {T0 : Type} (C : LevCh D T0) (i : Fin D.R.m)

theorem mem_levG_datWp (P : LevelP C.Pg D.R.r ℂ) (κ : GA D (Wc D i)) :
    κ ∈ levG (Wc D i) (C.βW i) (C.datWp i P) ↔ κ ∈ GfC (Wc D i) ∧
      finE (Wc D i) κ ∈ parLev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i C.triv) ∧
      rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) κ) ∈ P.H := by
  rw [levG, Formalism.IndefR.Lev.mem_levA]
  refine and_congr_right fun _ => ?_
  exact Iff.rfl

def blkHom (P : LevelP C.Pg D.R.r ℂ) : levG (Wc D i) (C.βW i) (C.datWp i P) →* G0 C.Pg D.R.r where
  toFun κ := rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) κ.1)
  map_one' := by
    show rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) 1) = 1
    rw [map_one]; exact rTup_one
  map_mul' x y := by
    show rTup (C.βW i) (C.datWp i C.triv) (finE (Wc D i) (x.1 * y.1)) = _
    rw [map_mul]
    exact rTup_mul (hc := D.sp.cm) (J := (Wc D i).gram) ((mem_levG_datWp C i P _).1 x.2).2.1
      ((mem_levG_datWp C i P _).1 y.2).2.1

theorem ker_blkHom (P : LevelP C.Pg D.R.r ℂ) :
    (blkHom C i P).ker = (levG (Wc D i) (C.βW i) (C.datWp i C.triv)).subgroupOf
      (levG (Wc D i) (C.βW i) (C.datWp i P)) := by
  ext κ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_levG_datWp C i C.triv]
  obtain ⟨hG, hpar, -⟩ := (mem_levG_datWp C i P κ.1).1 κ.2
  constructor
  · intro h1
    exact ⟨hG, hpar, Subgroup.mem_bot.2 h1⟩
  · rintro ⟨-, -, hb⟩
    exact Subgroup.mem_bot.1 hb

theorem range_blkHom {μ0 : T0} (hC : C.Is μ0) (P : LevelP C.Pg D.R.r ℂ) : (blkHom C i P).range = P.H := by
  ext g
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨κ, rfl⟩
    exact ((mem_levG_datWp C i P κ.1).1 κ.2).2.2
  · intro hg
    obtain ⟨c, hB⟩ := hC.βW i
    have hsep := (GlobalTheory.StepLifts.places_apart C hC μ0).1
    obtain ⟨κ, hG, hpar, hred⟩ := GlobalTheory.ParahoricLift.liftsExist (Wc D i) (C.βW i) (C.datWp i C.triv) (C.ΛW i) _ hB
      (fun PP hPP PP' hPP' => hsep PP hPP PP' (hPP'.elim Or.inl fun h => absurd h (Finset.notMem_empty PP')))
      (Finset.disjoint_empty_right _) g
    have hmem : κ ∈ levG (Wc D i) (C.βW i) (C.datWp i P) := by
      refine (mem_levG_datWp C i P κ).2 ⟨hG, hpar, ?_⟩
      rw [hred]
      exact hg
    exact ⟨⟨κ, hmem⟩, hred⟩

theorem levidx : ∀ (D : D7) (T0 : Type) (C : LevCh D T0) (μ0 : T0), C.Is μ0 → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → C.Pg ⊆ Z → ∀ (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), levG (Wc D i) (C.βW i) (C.datWp i C.triv) ≤ levG (Wc D i) (C.βW i) (C.datWp i P) ∧ (levG (Wc D i) (C.βW i) (C.datWp i C.triv)).relIndex (levG (Wc D i) (C.βW i) (C.datWp i P)) = Nat.card P.H ∧ Nat.card P.H ≠ 0 := by
  intro D T0 C μ0 hC _ _ _ _ i P
  have hle : levG (Wc D i) (C.βW i) (C.datWp i C.triv) ≤ levG (Wc D i) (C.βW i) (C.datWp i P) := by
    intro κ hκ
    obtain ⟨h1, h2, h3⟩ := (mem_levG_datWp C i C.triv κ).1 hκ
    refine (mem_levG_datWp C i P κ).2 ⟨h1, h2, ?_⟩
    rw [Subgroup.mem_bot.1 h3]
    exact P.H.one_mem
  refine ⟨hle, ?_, Nat.card_pos.ne'⟩
  rw [Subgroup.relIndex, ← ker_blkHom C i P, Subgroup.index_ker, range_blkHom C i hC P]

end GlobalTheory.LevIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceStdParamIsParam
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

def realPlaceStdParam (p q : ℕ) : Ix p q → ℚ :=
  Sum.elim (fun i => -((i : ℕ) : ℚ)) (fun j => -(((p + j : ℕ)) : ℚ))

theorem realPlaceStdParam_int (p q : ℕ) (a : Ix p q) :
    ∃ k : ℤ, realPlaceStdParam p q a = k := by
  rcases a with i | j
  · exact ⟨-((i : ℕ) : ℤ), by simp [realPlaceStdParam]⟩
  · exact ⟨-((p + j : ℕ) : ℤ), by simp [realPlaceStdParam]⟩

theorem realPlaceStdParam_isParam (p q : ℕ) : IsParam (realPlaceStdParam p q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (i | j) (i' | j') h
    · simp only [realPlaceStdParam, Sum.elim_inl, neg_inj, Nat.cast_inj] at h
      exact congrArg Sum.inl (Fin.ext h)
    · simp only [realPlaceStdParam, Sum.elim_inl, Sum.elim_inr, neg_inj, Nat.cast_inj] at h
      have := i.2
      omega
    · simp only [realPlaceStdParam, Sum.elim_inl, Sum.elim_inr, neg_inj, Nat.cast_inj] at h
      have := i'.2
      omega
    · simp only [realPlaceStdParam, Sum.elim_inr, neg_inj, Nat.cast_inj] at h
      exact congrArg Sum.inr (Fin.ext (by omega))
  · rintro (i | j) (i' | j') h
    · have h' : (i : ℕ) < i' := h
      simp only [realPlaceStdParam, Sum.elim_inl, neg_lt_neg_iff, Nat.cast_lt]
      exact h'
    · exact absurd h (by simp [posC])
    · exact absurd h (by simp [posC])
    · have h' : (j : ℕ) < j' := h
      simp only [realPlaceStdParam, Sum.elim_inr, neg_lt_neg_iff, Nat.cast_lt]
      omega
  · intro a
    obtain ⟨k, hk⟩ := realPlaceStdParam_int p q a
    exact ⟨2 * k, by rw [hk]; push_cast; ring⟩
  · intro a b
    obtain ⟨k, hk⟩ := realPlaceStdParam_int p q a
    obtain ⟨l, hl⟩ := realPlaceStdParam_int p q b
    exact ⟨k - l, by rw [hk, hl]; push_cast; ring⟩

theorem exists_provA_of_forall_exists_hasParam :
    (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam →
      ∃ R : DSRep T, Formalism.L2.Theta.HasParam R lam) →
    ∃ X : ProvA, ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam →
      Formalism.L2.Theta.HasParam (X.ds p q lam) lam := by
  intro H
  classical
  let grp : ∀ p q : ℕ, GrpData p q := fun p q => Classical.choice (GlobalTheory.DetSqrtCover.nonempty_grpData p q)
  have key : ∀ (p q : ℕ) (lam : Ix p q → ℚ), ∃ R : DSRep (grp p q),
      IsParam lam → Formalism.L2.Theta.HasParam R lam := by
    intro p q lam
    by_cases h : IsParam lam
    · obtain ⟨R, hR⟩ := H p q (grp p q) lam h
      exact ⟨R, fun _ => hR⟩
    · obtain ⟨R, -⟩ := H p q (grp p q) _ (realPlaceStdParam_isParam p q)
      exact ⟨R, fun h' => absurd h' h⟩
  choose ds hds using key
  exact ⟨⟨grp, fun p q r s => Classical.choice (_root_.GlobalTheory.nonempty_fockData_of_covers p q r s _ _ _), ds⟩, hds⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsLinearlyOnMultiplicityValuesPosDef
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealAct

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

def ActsLin (θ : InfFam D) (M : DSModel V S) (k : GA D V) : Prop :=
  ∃ φ : Module.End ℂ (MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ),
    ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T)

theorem actsLin_one (M : DSModel V S) : ActsLin θ M 1 := by
  refine ⟨LinearMap.id, ?_⟩
  intro J χ T _ g
  rw [mul_one]
  rfl

theorem actsLin_mul {M : DSModel V S} {a b : GA D V} (ha : ActsLin θ M a) (hb : ActsLin θ M b) :
    ActsLin θ M (a * b) := by
  obtain ⟨φa, hφa⟩ := ha
  obtain ⟨φb, hφb⟩ := hb
  refine ⟨φb ∘ₗ φa, fun J χ T hT g => ?_⟩
  calc evAt M (g * (a * b)) T = evAt M ((g * a) * b) T := by rw [mul_assoc]
    _ = φb (evAt M (g * a) T) := hφb J χ T hT (g * a)
    _ = φb (φa (evAt M g T)) := by rw [hφa J χ T hT g]

theorem actsLin_atTau {M : DSModel V S} (hM : AllPlus M) (τ : D.what₂.Tau)
    {u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ActsLin θ M (atTau θ V τ u) := by
  classical
  have htop : M.sm τ = ⊤ := (AllPlus.finite_smooth_irreducible _ V S M hM τ).2.1
  let A : M.sm τ →ₗ[ℂ] M.sm τ :=
    (M.rep τ u).toLinearMap.restrict (fun x _ => by rw [htop]; exact Submodule.mem_top)
  let F : ∀ i, M.sm i →ₗ[ℂ] M.sm i := Function.update (fun i => (LinearMap.id : M.sm i →ₗ[ℂ] M.sm i)) τ A
  refine ⟨MultilinearMap.compLinearMapₗ F, ?_⟩
  intro J χ T hT g
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ θ V S M J χ T).1 hT
  ext v
  have hv : (fun i => F i (v i)) = Function.update v τ (A (v τ)) := by
    funext i
    by_cases h : i = τ
    · subst h
      simp [F]
    · simp [F, h]
  have hw : ((A (v τ) : M.sm τ) : M.H τ) = M.rep τ u (v τ) := rfl
  have key := congrFun (hmap.equiv τ u hu v (A (v τ)) hw) g
  rw [evAt_apply]
  simp only [MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply]
  rw [evAt_apply, hv, key]
  rfl

theorem real_acts : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∀ k ∈ GinfC V, ∃ φ : Module.End ℂ (MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T) := by
  intro D θ V S M hθ hM k hk
  classical
  obtain ⟨L, -, hLmul, -, hLarch, hLinv, hLat, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨a, hUa, hkL⟩ : ∃ a, a ∈ GlobalTheory.HolDict.UG (gramAt D V) ∧ L a = k := ⟨_, hLarch k, hLinv k hk⟩
  have haU : ∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := hUa
  have h1U : ∀ τ, (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    intro τ
    simp [Formalism.QuantumDeterminants.UH]
  have hL1 : L 1 = 1 := by
    have h := hLmul 1 (fun τ => h1U τ) 1 (fun τ => h1U τ)
    rw [mul_one] at h
    calc L 1 = (L 1)⁻¹ * (L 1 * L 1) := by group
      _ = (L 1)⁻¹ * L 1 := by rw [← h]
      _ = 1 := inv_mul_cancel _
  have hpart : ∀ s : Finset D.what₂.Tau,
      ActsLin θ M (L fun τ => if τ ∈ s then a τ else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun τ : D.what₂.Tau => if τ ∈ (∅ : Finset D.what₂.Tau) then a τ else 1) = 1 := by
        funext τ
        simp
      rw [he, hL1]
      exact actsLin_one M
    | insert x s hx ih =>
      have hs : (fun τ => if τ ∈ s then a τ else 1) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
        intro τ
        by_cases h : τ ∈ s
        · simpa [h] using haU τ
        · simpa [h] using h1U τ
      have hsing : Pi.mulSingle x (a x) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
        intro τ
        by_cases h : τ = x
        · subst h
          simpa using haU τ
        · simpa [Pi.mulSingle_apply, h] using h1U τ
      have hsplit : (fun τ => if τ ∈ insert x s then a τ else 1)
          = Pi.mulSingle x (a x) * fun τ => if τ ∈ s then a τ else 1 := by
        funext τ
        by_cases h : τ = x
        · subst h
          simp [hx]
        · simp [h, Pi.mulSingle_apply]
      rw [hsplit, hLmul _ hsing _ hs, ← hLat x (a x) (haU x)]
      exact actsLin_mul (actsLin_atTau hM x (haU x)) ih
  have hall : (fun τ => if τ ∈ (Finset.univ : Finset D.what₂.Tau) then a τ else 1) = a := by
    funext τ
    simp
  have := hpart Finset.univ
  rw [hall, hkL] at this
  exact this

end GlobalTheory.RealAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzGaussianFormReNeg
section
open MeasureTheory

namespace GlobalTheory

theorem schwartz_gaussian_form_re_neg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ) (hg : g ≠ 0)
    (hform : ∀ x, g x = g 0 * Complex.exp (M x x)) (v : V) (hv : v ≠ 0) : (M v v).re < 0 := by
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hg
    ext x
    rw [hform x, h0]; simp
  by_contra hre
  push_neg at hre
  obtain ⟨C, hC, hdec⟩ := g.decay 1 0
  have hgn : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set s : ℝ := (C + 1) / (‖v‖ * ‖g 0‖) with hs
  have hspos : 0 < s := by positivity
  have key := hdec (s • v)
  rw [norm_iteratedFDeriv_zero, pow_one, hform (s • v)] at key
  have hM : M (s • v) (s • v) = ((s ^ 2 : ℝ) : ℂ) * M v v := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [Complex.real_smul]; push_cast; ring
  rw [hM, norm_mul, Complex.norm_exp] at key
  have hexp : 1 ≤ Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re) := by
    apply Real.one_le_exp
    rw [Complex.re_ofReal_mul]
    positivity
  have hnorm : ‖s • v‖ = s * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
  rw [hnorm] at key
  have h1 : s * ‖v‖ * ‖g 0‖ = C + 1 := by
    rw [hs]; field_simp
  have h2 : s * ‖v‖ * ‖g 0‖ ≤ s * ‖v‖ * (‖g 0‖ * Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjIntegral

theorem mul_int {R : Type} [CommRing R] (S : Subring R) {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (i j : Fin n) : (A * B) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hB k j)

theorem conj_int {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (G Gi γ γi : Matrix (Fin n) (Fin n) R) (hG : ∀ i j, G i j ∈ S) (hGi : ∀ i j, Gi i j ∈ S) (hGG : Gi * G = 1)
    (hγ : γ * γi = 1) (hu : (γ.map σ)ᵀ * G * γ = G) (a : R) (ha : ∀ i j, (a • γ) i j ∈ S) :
    ∀ i j, (σ a • γi) i j ∈ S := by
  have e1 : γi = Gi * (γ.map σ)ᵀ * G := by
    calc γi = Gi * G * γi := by rw [hGG, Matrix.one_mul]
      _ = Gi * ((γ.map σ)ᵀ * G * γ) * γi := by rw [hu]
      _ = Gi * (γ.map σ)ᵀ * G * (γ * γi) := by simp only [Matrix.mul_assoc]
      _ = Gi * (γ.map σ)ᵀ * G := by rw [hγ, Matrix.mul_one]
  have e2 : σ a • γi = Gi * ((a • γ).map σ)ᵀ * G := by
    have : (a • γ).map σ = σ a • γ.map σ := by
      ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
    rw [this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, e1]
  have hc : ∀ i j, ((a • γ).map σ)ᵀ i j ∈ S := fun i j => hσ _ (ha j i)
  rw [e2]
  exact mul_int S (mul_int S hGi hc) hG

theorem conj_int_both {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (G Gi γ γi : Matrix (Fin n) (Fin n) R) (hG : ∀ i j, G i j ∈ S) (hGi : ∀ i j, Gi i j ∈ S) (hGG : Gi * G = 1)
    (hγ : γ * γi = 1) (hγ' : γi * γ = 1) (hu : (γ.map σ)ᵀ * G * γ = G) (a : R)
    (ha : ∀ i j, (a • γ) i j ∈ S) (ha' : ∀ i j, (a • γi) i j ∈ S) :
    (∀ i j, (σ a • γ) i j ∈ S) ∧ (∀ i j, (σ a • γi) i j ∈ S) := by
  have hu' : (γi.map σ)ᵀ * G * γi = G := by
    have h1 : (γi.map σ)ᵀ * (γ.map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hγ, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
    calc (γi.map σ)ᵀ * G * γi = (γi.map σ)ᵀ * ((γ.map σ)ᵀ * G * γ) * γi := by rw [hu]
      _ = ((γi.map σ)ᵀ * (γ.map σ)ᵀ) * G * (γ * γi) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, hγ, Matrix.one_mul, Matrix.mul_one]
  exact ⟨conj_int S σ hσ G Gi γi γ hG hGi hGG hγ' hu' a ha', conj_int S σ hσ G Gi γ γi hG hGi hGG hγ hu a ha⟩

theorem unit_conj {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (B Bi H J : Matrix (Fin n) (Fin n) R)
    (hB : Bi * B = 1) (hB' : B * Bi = 1) (hH : Formalism.UG.cT σ H * J * H = J) :
    ((Bi * H * B).map σ)ᵀ * (Formalism.UG.cT σ B * J * B) * (Bi * H * B) = Formalism.UG.cT σ B * J * B := by
  have hcT : ∀ A C : Matrix (Fin n) (Fin n) R, Formalism.UG.cT σ (A * C) = Formalism.UG.cT σ C * Formalism.UG.cT σ A := by
    intro A C; simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have e : Formalism.UG.cT σ Bi * Formalism.UG.cT σ B = 1 := by
    rw [← hcT, hB']
    simp only [Formalism.UG.cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  change Formalism.UG.cT σ (Bi * H * B) * _ * _ = _
  rw [hcT, hcT]
  calc Formalism.UG.cT σ B * (Formalism.UG.cT σ H * Formalism.UG.cT σ Bi) * (Formalism.UG.cT σ B * J * B) * (Bi * H * B)
      = Formalism.UG.cT σ B * (Formalism.UG.cT σ H * (Formalism.UG.cT σ Bi * Formalism.UG.cT σ B) * J * (B * Bi) * H) * B := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ B * J * B := by rw [e, hB', Matrix.mul_one, Matrix.mul_one, hH]

end GlobalTheory.ConjIntegral

namespace GlobalTheory.ConjIntegral


set_option maxHeartbeats 800000 in
theorem conj_smul_isIntM : ∀ {D : D7} (T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC T ΛT → IsFrame βT ΛT → ∀ (h : GL (Fin T.rank) (EAf D)), h ∈ UA D.sp.cm T.gram → ∀ (γ : GL (Fin T.rank) (EAf D)), γ = βT⁻¹ * h * βT → ∀ (a : AE D), IsIntM (toEAf D a • γ.1) → IsIntM (toEAf D a • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) → IsIntM (toEAf D (cA D a) • γ.1) ∧ IsIntM (toEAf D (cA D a) • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) := by
  intro D T ΛT βT hsd hβ h hh γ hγ a h1 h2
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D T ΛT hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) T.gram βT ΛT hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  have hσ : ∀ x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun _ hx => GlobalTheory.LevSplit.sigR_int hx
  have hGm : ∀ i j, (intGL D.host.F D.host.E T.rank G).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i j => (G.1 i j).2
  have hGi : ∀ i j, (intGL D.host.F D.host.E T.rank G⁻¹).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i j => ((G⁻¹).1 i j).2
  have hGG : (intGL D.host.F D.host.E T.rank G⁻¹).1 * (intGL D.host.F D.host.E T.rank G).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

  have hhu : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) h.1 * T.gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) * h.1 =
      T.gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) := hh
  have hγ1 : γ.1 = (βT⁻¹).1 * h.1 * βT.1 := by rw [hγ]; rfl
  have hu := unit_conj (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) βT.1 (βT⁻¹).1 h.1 _
    (Units.inv_mul βT) (Units.mul_inv βT) hhu
  rw [← hγ1, ← hG] at hu
  have key := conj_int_both _ _ hσ _ _ γ.1 (γ⁻¹).1 hGm hGi hGG (Units.mul_inv γ) (Units.inv_mul γ) hu (toEAf D a) h1 h2
  rw [GlobalTheory.AdelicLatMove.toEAf_cA a]
  exact key

end GlobalTheory.ConjIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalZetaKernelGLRightInvariantIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaGL

theorem kerGL_mul_right_KGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r N : ℕ) (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), KerGL w N z φ → ∀ g k : GL (Fin r) (w.adicCompletion E), k ∈ KGL w (n := r) → φ (g * k) = φ g := by
  intro E _ _ w r N z φ hφ g k hk
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
  have hm := mem_Ov_of_isUnifV hϖ
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w r ϖ hm hϖ g
  obtain ⟨t, ht⟩ : ∃ t : GL (Fin r) (w.adicCompletion E), t = k₁⁻¹ * g * k₂⁻¹ := ⟨_, rfl⟩
  have hg : g = k₁ * t * k₂ := by rw [ht]; group
  have htv : t.1 = Matrix.diagonal fun i => ϖ ^ a i := by
    calc t.1 = ((k₁⁻¹ : GL (Fin r) (w.adicCompletion E)).1 * k₁.1) * Formalism.UG.diagPow E w ϖ a *
          (k₂.1 * (k₂⁻¹ : GL (Fin r) (w.adicCompletion E)).1) := by
          rw [ht, Units.val_mul, Units.val_mul, e]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]; rfl
  rw [hg, mul_assoc (k₁ * t) k₂ k, hφ ϖ hϖ a t htv k₁ hk₁ (k₂ * k) (mul_mem hk₂ hk), hφ ϖ hϖ a t htv k₁ hk₁ k₂ hk₂]

end GlobalTheory.ZetaGL
end

