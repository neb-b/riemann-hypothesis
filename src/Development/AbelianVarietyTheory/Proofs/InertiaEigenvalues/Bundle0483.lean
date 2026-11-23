module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.DcrisExact

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]

theorem mapVB_eq_rTensor (f : V →ₗ[LL] W) (x : V ⊗[Qp] B) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x = (f.restrictScalars Qp).rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.MainNotions.RamifiedCoefficientChains.mapVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_Dcris' (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mapVB_act (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (x : V ⊗[Qp] B) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f (actVB PD ρ g x) =
      actVB PD σ g (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, Formalism.MainNotions.RamifiedCoefficientChains.mapVB, hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mapVB_mem_Dcris (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x ∈ Dcris PD σ := by
  rw [mem_Dcris'] at hx ⊢
  intro g
  rw [← mapVB_act PD ρ σ f hf, hx]

theorem ιV_mapVB (f : V →ₗ[LL] W) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := W) (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x) =
      AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV, Formalism.MainNotions.RamifiedCoefficientChains.mapVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_mem_FilV (f : V →ₗ[LL] W) (a : ℤ) {y : V ⊗[Qp] BdR}
    (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y ∈ FilV PD (LL := LL) (V := W) a := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨AlgebraTensorModule.map f (LinearMap.id : ↥((PD.Fil a).restrictScalars Qp) →ₗ[Qp] ↥((PD.Fil a).restrictScalars Qp)) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mapVB_mem_FilCris (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (a : ℤ) {x : V ⊗[Qp] B} (hx : x ∈ FilCris PD ρ a) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x ∈ FilCris PD σ a := by
  refine ⟨mapVB_mem_Dcris PD ρ σ f hf hx.1, ?_⟩
  show ιV PD (LL := LL) (V := W) (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x) ∈ FilV PD (LL := LL) (V := W) a
  rw [ιV_mapVB]
  exact map_mem_FilV PD f a hx.2

end Abstract

end GlobalTheory.Per.DcrisExact

namespace GlobalTheory.Per.DcrisExact

open GlobalTheory.Per.DcrisExact

theorem exactStrict (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict (P.PD K) ↥LL.1 := by
  intro hb V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hinj hsurj hex hc₀ hc₁ hc₂
  have hE : Function.Exact (ι.restrictScalars ℚ_[l]) (π.restrictScalars ℚ_[l]) := by
    rw [LinearMap.exact_iff]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, LinearMap.restrictScalars_apply]
    have := congrArg (fun S : Submodule ↥LL.1 V₁ => x ∈ S) hex
    simpa using this
  have hexT := rTensor_exact P.R.B (f := ι.restrictScalars ℚ_[l]) (g := π.restrictScalars ℚ_[l]) hE hsurj
  have hinjT : Function.Injective ((ι.restrictScalars ℚ_[l]).rTensor P.R.B) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hinj
  have hS := _root_.GlobalTheory.Per.CrisStrict.dcris_strict l P AI hT K LL hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _ hx
    apply hinjT
    rw [← mapVB_eq_rTensor, hx, map_zero]
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨mapVB_mem_Dcris _ ρ₀ ρ₁ ι hι hx, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, mapVB_eq_rTensor, mapVB_eq_rTensor,
        ← LinearMap.rTensor_comp_apply]
      have : (π.restrictScalars ℚ_[l]).comp (ι.restrictScalars ℚ_[l]) = 0 := by
        ext v
        exact hE.apply_apply_eq_zero v
      rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]
    · rintro y ⟨hy, hk⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, mapVB_eq_rTensor] at hk
      obtain ⟨x, hx⟩ := (hexT y).mp hk
      rw [← mapVB_eq_rTensor] at hx
      refine ⟨x, ?_, hx⟩
      have hy' := (mem_Dcris' _ ρ₁ y).1 hy
      rw [SetLike.mem_coe, mem_Dcris']
      intro g
      apply hinjT
      rw [← mapVB_eq_rTensor, ← mapVB_eq_rTensor, mapVB_act _ ρ₀ ρ₁ ι hι, hx, hy' g]
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact mapVB_mem_Dcris _ ρ₁ ρ₂ π hπ hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL V₁ ρ₁ V₂ ρ₂ π hπ).2
        hsurj hc₁).2 y hy
      exact ⟨x, hx, hxy⟩
  · intro a
    refine ⟨(hS V₁ ρ₁ V₂ ρ₂ π hπ).1 hsurj hc₁ a, ?_⟩
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, mapVB_mem_FilCris _ ρ₀ ρ₁ ι hι a hx⟩
    · rintro x ⟨hx, hf⟩
      exact (hS V₀ ρ₀ V₁ ρ₁ ι hι).2 hinj a x hx hf

end GlobalTheory.Per.DcrisExact

namespace GlobalTheory.Per.DcrisExact

theorem fontaine_dcris : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm11 D := by
  intro D l _ K LL
  refine ⟨exactStrict l (D.loc l) (D.locA l) (D.locT l) K LL, ?_, ?_⟩
  · intro V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hinj hsurj _ hc₁
    exact ⟨(GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) (D.locT l) K LL V₀ ρ₀ V₁ ρ₁ ι hι).1
        hinj hc₁,
      ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) (D.locT l) K LL V₁ ρ₁ V₂ ρ₂ π hπ).2
        hsurj hc₁).1⟩
  · intro hb V _ _ _ _ _ ρ hc
    exact GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.Per.DcrisExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEisensteinMemPrimeMulDividedPowerSeries
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem frobS_eis_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∃ B ∈ SdSet t K e, inclS t K (frobS l a (eis l a e)) = (l : ZMod a → K⟦X⟧) * B := by
  intro l hl a e _ _ O K _ _ _ _ _ _ _ _ _ t
  have hlp : l.Prime := hl.out
  have hl0 : (l : K) ≠ 0 := by
    have h : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
    rw [h]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hlp.ne_zero)
  have hle : l * e ≠ 0 := Nat.mul_ne_zero hlp.ne_zero (NeZero.ne e)
  have hf : frobS l a (eis l a e) = X ^ (l * e) + (l : (Wq l a)⟦X⟧) := by
    simp [eis, pow_mul]
  refine ⟨fun _ => 1 + C (l : K)⁻¹ * X ^ (l * e),
    ⟨fun n => if n = 0 then 1 else if n = l * e then (((l - 1).factorial : ℕ) : Wq l a) else 0, ?_, ?_⟩, ?_⟩
  · intro r
    rw [Filter.eventually_cofinite]
    refine (Set.finite_le_nat (l * e)).subset fun n hn => ?_
    by_contra h
    simp only [Set.mem_setOf_eq, not_le] at h
    apply hn
    simp only [show n ≠ 0 by omega, show n ≠ l * e by omega, if_false]
    exact dvd_zero _
  · intro τ n
    rw [map_add (f := _), coeff_one, coeff_C_mul, coeff_X_pow]
    by_cases h0 : n = 0
    · subst h0
      simp [hle.symm]
    · by_cases h1 : n = l * e
      · subst h1
        have hfac : (l : K)⁻¹ * (l.factorial : K) = ((l - 1).factorial : K) := by
          rw [← Nat.mul_factorial_pred hlp.ne_zero, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
        simp only [h0, hle, if_false, if_true, zero_add, mul_one, map_natCast]
        rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne e)), mul_comm, hfac]
      · simp [h0, h1]
  · funext τ
    ext n
    rw [inclS_apply, coeff_toAc, hf, Pi.mul_apply, Pi.natCast_apply, ← map_natCast (C : K →+* K⟦X⟧),
      coeff_C_mul, map_add (coeff n) (X ^ (l * e)) (l : (Wq l a)⟦X⟧), map_add (coeff n) (1 : K⟦X⟧), coeff_one, coeff_C_mul, coeff_X_pow, coeff_X_pow,
      ← map_natCast (C : Wq l a →+* (Wq l a)⟦X⟧), coeff_C]
    by_cases h0 : n = 0
    · subst h0
      simp [hle.symm]
    · by_cases h1 : n = l * e
      · subst h1
        simp [h0, hl0]
      · simp [h0, h1]

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusResidueSliceMemBoundedLeftDivisorSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.SliceLdiv

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem frobSlice_zero (l i : ℕ) : frobSlice l i (0 : K⟦X⟧) = 0 := by
  ext n; simp [coeff_frobSlice]

theorem frobSlice_sum {β : Type} (l i : ℕ) (s : Finset β) (g : β → K⟦X⟧) :
    frobSlice l i (∑ b ∈ s, g b) = ∑ b ∈ s, frobSlice l i (g b) := by
  ext n; simp [coeff_frobSlice, map_sum]

theorem frobSlice_mul_frob {l : ℕ} [Fact l.Prime] {i : ℕ} (hi : i < l) (z f : K⟦X⟧) :
    frobSlice l i (z * frob K l f) = frobSlice l i z * f := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_frobSlice, coeff_mul, coeff_mul]
  have hval : ∀ p q : ℕ, coeff (l * p + i) z * coeff q f =
      coeff (l * p + i) z * coeff (l * q) (frob K l f) := by
    intro p q
    rw [coeff_frob, if_pos (dvd_mul_right l q), Nat.mul_div_cancel_left q hl]
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (l * p.1 + i, l * p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hpq -
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hpq ⊢
    rw [← hpq, mul_add]; ring
  · rintro ⟨p, q⟩ - - ⟨p', q'⟩ - - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : p = p' := Nat.eq_of_mul_eq_mul_left hl (by omega)
    have h2' : q = q' := Nat.eq_of_mul_eq_mul_left hl h2
    rw [h1', h2']
  · rintro ⟨a, b⟩ hab hne
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [coeff_frob] at hne
    split_ifs at hne with hdvd
    · obtain ⟨q, rfl⟩ := hdvd
      have hq : q ≤ n := by
        by_contra hc
        have : l * (n + 1) ≤ l * q := Nat.mul_le_mul_left l (by omega)
        rw [mul_add, mul_one] at this
        omega
      have key : l * (n - q) + l * q = l * n := by rw [← mul_add, Nat.sub_add_cancel hq]
      have ha : a = l * (n - q) + i := by omega
      subst ha
      rw [Nat.mul_div_cancel_left q hl] at hne
      exact ⟨(n - q, q), by simp only [Finset.HasAntidiagonal.mem_antidiagonal]; omega,
        by simp only [coeff_frobSlice]; exact hne, rfl⟩
    · exact absurd (mul_zero _) hne
  · rintro ⟨p, q⟩ - -
    simp only [coeff_frobSlice]
    exact hval p q

theorem bdd_frobSlice (l i : ℕ) {z : K⟦X⟧} (hz : ∃ c : ℝ, ∀ n, ‖coeff n z‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (frobSlice l i z)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, fun n => by rw [coeff_frobSlice]; exact hc _⟩

theorem bdd_of_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c := ⟨1, hf⟩

theorem bdd_zero : ∃ c : ℝ, ∀ n, ‖coeff n (0 : K⟦X⟧)‖ ≤ c := ⟨0, fun n => by simp⟩

theorem bdd_sum {β : Type} (s : Finset β) (g : β → K⟦X⟧) (hg : ∀ b ∈ s, ∃ c : ℝ, ∀ n, ‖coeff n (g b)‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (∑ b ∈ s, g b)‖ ≤ c :=
  Finset.sum_induction g (fun f : K⟦X⟧ => ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c)
    (fun _ _ => Hom.bdd_add) bdd_zero hg

theorem bdd_matMul {μ ν ρ : Type} [Fintype ν] {M : Matrix μ ν K⟦X⟧} {N : Matrix ν ρ K⟦X⟧}
    (hM : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (M i j)‖ ≤ c) (hN : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (N i j)‖ ≤ c)
    (i : μ) (j : ρ) : ∃ c : ℝ, ∀ n, ‖coeff n ((M * N) i j)‖ ≤ c := by
  rw [Matrix.mul_apply]
  exact bdd_sum _ _ fun k _ => Hom.bdd_mul (hM i k) (hN k j)

theorem bdd_unif {μ ν : Type} [Finite μ] [Finite ν] {M : Matrix μ ν K⟦X⟧}
    (h : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (M i j)‖ ≤ c) : ∃ c : ℝ, ∀ i j n, ‖coeff n (M i j)‖ ≤ c := by
  choose c hc using h
  obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun p : μ × ν => c p.1 p.2)
  exact ⟨C, fun i j n => (hc i j n).trans (hC ⟨(i, j), rfl⟩)⟩

theorem exists_pow_E_mul_mem (l e : ℕ) {β : Type} [Finite β] (g : β → K⟦X⟧)
    (hg : ∀ b, g b ∈ invE l e (A O K)) : ∃ N : ℕ, ∀ b, E K l e ^ N * g b ∈ A O K := by
  have := Fintype.ofFinite β
  choose n hn using fun b => (mem_away.1 (hg b))
  refine ⟨Finset.univ.sup n, fun b => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ b))
  rw [hc, pow_add, mul_assoc]
  exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn b)

theorem frobSlice_mem_ldivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.ldivSet (τ - 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  obtain ⟨N₁, hN₁⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × ι × ι => P.mxInv p.1 p.2.1 p.2.2) (fun p => P.mxInv_mem _ _ _)
  obtain ⟨N₂, hN₂⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × κ × κ => Q.mx p.1 p.2.1 p.2.2) (fun p => Q.mx_mem _ _ _)
  refine ⟨N₁ + N₂, fun τ h hh i hi => ?_⟩
  obtain ⟨hhb, Y, ⟨cY, hcY⟩, hY⟩ := hh
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix ι κ K⟦X⟧,
      Z = (E K l e ^ N₁ • P.mxInv τ) * Y * (E K l e ^ N₂ • Q.mx τ) := ⟨_, rfl⟩
  have h1 : Y * Q.mx τ * (F.mat (τ - 1)).map (frob K l) = h • P.mx τ := by
    rw [Matrix.mul_assoc, ← F.comm, ← Matrix.mul_assoc, hY, Matrix.smul_mul, Matrix.one_mul]
  have hZF : Z * (F.mat (τ - 1)).map (frob K l) =
      (E K l e ^ (N₁ + N₂) * h) • (1 : Matrix ι ι K⟦X⟧) := by
    have : Z * (F.mat (τ - 1)).map (frob K l) =
        E K l e ^ N₁ • E K l e ^ N₂ • (P.mxInv τ * (Y * Q.mx τ * (F.mat (τ - 1)).map (frob K l))) := by
      simp only [hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      exact smul_comm _ _ _
    rw [this, h1, Matrix.mul_smul, P.mxInv_mul_mx]
    simp only [smul_smul, pow_add, mul_assoc]
  have hPb : ∀ r k, ∃ c : ℝ, ∀ n, ‖coeff n ((E K l e ^ N₁ • P.mxInv τ) r k)‖ ≤ c := fun r k =>
    bdd_of_mem_A (O := O) (by rw [Matrix.smul_apply, smul_eq_mul]; exact hN₁ (τ, r, k))
  have hQb : ∀ k c, ∃ c' : ℝ, ∀ n, ‖coeff n ((E K l e ^ N₂ • Q.mx τ) k c)‖ ≤ c' := fun k c =>
    bdd_of_mem_A (O := O) (by rw [Matrix.smul_apply, smul_eq_mul]; exact hN₂ (τ, k, c))
  have hYb : ∀ r k, ∃ c : ℝ, ∀ n, ‖coeff n (Y r k)‖ ≤ c := fun r k => ⟨cY, hcY r k⟩
  have hZb : ∀ r c, ∃ c' : ℝ, ∀ n, ‖coeff n (Z r c)‖ ≤ c' := fun r c => by
    rw [hZ]; exact bdd_matMul (bdd_matMul hPb hYb) hQb r c
  refine ⟨bdd_frobSlice l i (Hom.bdd_mul (bdd_of_mem_A (O := O) (pow_mem (E_mem l e (A O K)) _)) hhb),
    Z.map (frobSlice l i), bdd_unif fun r c => ?_, ?_⟩
  · rw [Matrix.map_apply]; exact bdd_frobSlice l i (hZb r c)
  · ext r c
    have hrc := congrFun (congrFun hZF r) c
    rw [Matrix.mul_apply] at hrc
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply] at hrc ⊢
    simp_rw [← frobSlice_mul_frob hi]
    rw [← frobSlice_sum, hrc, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      smul_eq_mul]
    split_ifs
    · rw [mul_one, mul_one]
    · rw [mul_zero, mul_zero, frobSlice_zero]

end GlobalTheory.BK.SliceLdiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPower
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

def galFq (g : GQ l) : Fq l a →+* Fq l a :=
  ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) fun x => by
    rw [mem_resSub, RingHom.comp_apply, ← map_pow]
    exact congrArg (Per.σF g) (mem_resSub.1 x.2)

theorem val_galFq (g : GQ l) (x : Fq l a) : Fq.val l a (galFq l a g x) = Per.σF g (Fq.val l a x) := rfl

theorem exists_pow_eq (φ : Fq l a →+* Fq l a) : ∃ m : ℕ, ∀ x, φ x = x ^ l ^ m := by
  first
  | exact @_root_.GlobalTheory.FrobeniusPower.main
  | exact _root_.GlobalTheory.FrobeniusPower.main
  | (apply _root_.GlobalTheory.FrobeniusPower.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrobeniusPower.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrobeniusPower.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrobeniusPower.main ..)
  | (intro h; exact _root_.GlobalTheory.FrobeniusPower.main h _ (fun _ => Iff.rfl))
  | exact _root_.GlobalTheory.FrobeniusPower.main ‹_› _ (fun _ => Iff.rfl)
  | (apply _root_.GlobalTheory.FrobeniusPower.main <;> first | assumption | exact fun _ => Iff.rfl)

theorem gal_wA_pow (g : GQ l) :
    ∃ s : ZMod a, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ s.val) w) := by
  obtain ⟨m, hm⟩ := exists_pow_eq l a (galFq l a g)
  refine ⟨(m : ZMod a), fun w => ?_⟩
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m (sigma_pow_eq_one l a)]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff]
  change Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ m) w).coeff n)
  rw [coeff_sigma_pow, ← hm, val_galFq]

end GlobalTheory.BKReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEisensteinEvalEqMulUnitCoeffDeRhamPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

variable {l : ℕ} [Fact l.Prime]

theorem ED_eq (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) :
    ED K t ϖ = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev 1 (eis l 1 e)) := by
  rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
  exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))

theorem σA_ev_eis_eq {e : ℕ} [NeZero e] (ϖ : PiSys l e) (g : GQ l) :
    ∃ u : Ainf l, IsUnit u ∧ Per.σA g (ϖ.ev 1 (eis l 1 e)) = ϖ.ev 1 (eis l 1 e) * u := by
  set d := ϖ.ev 1 (eis l 1 e) with hd
  have hdvd : ∀ h : GQ l, d ∣ Per.σA h d := fun h => by
    rw [← Ideal.mem_span_singleton, ϖ.span_ev_eis 1, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA, ϖ.theta_ev_eis 1, map_zero]
  obtain ⟨u, hu⟩ := hdvd g
  obtain ⟨u', hu'⟩ := hdvd g⁻¹
  by_cases hd0 : d = 0
  · refine ⟨1, isUnit_one, ?_⟩
    rw [hd0, map_zero, zero_mul]
  · refine ⟨u, ?_, hu⟩
    have h1 : d = d * (u * Per.σA g u') := by
      calc d = Per.σA g (Per.σA g⁻¹ d) := by rw [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one]
        _ = d * (u * Per.σA g u') := by rw [hu', map_mul, hu, mul_assoc]
    have h2 : u * Per.σA g u' = 1 := by
      have h3 : d * (u * Per.σA g u' - 1) = 0 := by rw [mul_sub, ← h1, mul_one, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hd0)
    exact IsUnit.of_mul_eq_one _ h2

end GlobalTheory.GalStep


open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.galOD_ED : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∃ v : OD l O, IsUnit v ∧ GlobalTheory.GalStep.galOD O g (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g _
  obtain ⟨u, hu, hσ⟩ := σA_ev_eis_eq ϖ g
  refine ⟨(1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l u, ?_, ?_⟩
  · exact hu.map ((Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O).comp (ainfToBdRp l))
  · rw [ED_eq a e O K t ϖ]
    change (1 : O) ⊗ₜ[ℤ_[l]] Per.σDp g (GlobalTheory.MemLoc.aDp l (ϖ.ev 1 (eis l 1 e))) = _
    rw [GlobalTheory.MemLoc.ActLaws.σDp_aDp, hσ, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisMatrixEqCrystalChangeOfBasisValueStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisMatrix_eq_crystal_changeOfBasis_value : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP), ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ (Cr : Obj l ↥(OL (ϖ.field a))) (eC : Cr.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj (ϖ.field a)) Cr), (∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x)) → ∀ (g : ↥(GK (ϖ.field a))) (ev : GlobalTheory.Prism.Hom PP Cr), ev.comp p₀ = h.comp (ϖ.toAinf a) → ev.comp p₁ = (h.comp (ainfHom (ϖ.field a) g)).comp (ϖ.toAinf a) → ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ i j, toOCr l O (Γ i j) = ∑ q, c i j q ⊗ₜ[ℤ_[l]] eC (ev.f (y i j q)) := by
  first | exact @GlobalTheory.CrysGalValue.main | exact GlobalTheory.CrysGalValue.main | (intros; apply GlobalTheory.CrysGalValue.main <;> assumption)
end

