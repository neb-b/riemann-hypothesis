module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
public import Development.AutomorphicSpectrum.Proofs.SemilocalMultiplicity.DsInfCharCap

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.EntriesZero
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.DerivativeAtIdentity

variable {n : ℕ}

private def dX {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → Module.End ℂ V) (X : Mat n) :
    Module.End ℂ V := ∑ a, ∑ b, X a b • F a b

private theorem dX_apply {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → Module.End ℂ V) (X : Mat n) (w : V) :
    dX F X w = ∑ a, ∑ b, X a b • F a b w := by
  simp [dX, LinearMap.sum_apply]

private theorem gam (X : Mat n) (hX : Xᴴ = -X) :
    ∃ γ : ℝ → UK n, (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) ∧ (∀ s h, γ (h + s) = γ h * γ s) ∧ γ 0 = 1 := by
  have hs : ∀ t : ℝ, ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := fun t => by
    simp [Matrix.conjTranspose_smul, hX]
  refine ⟨fun t => ⟨NormedSpace.exp ((t : ℂ) • X), ((skewExp n).1 _ (hs t))⟩, fun t => rfl, fun s h => ?_, ?_⟩
  · apply Subtype.ext
    show NormedSpace.exp (((h + s : ℝ) : ℂ) • X) = NormedSpace.exp ((h : ℂ) • X) * NormedSpace.exp ((s : ℂ) • X)
    rw [← Matrix.exp_add_of_commute]
    · congr 1
      push_cast
      rw [add_smul]
    · exact ((Commute.refl X).smul_left _).smul_right _
  · apply Subtype.ext
    show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
    simp

section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : UK n →* (V →ₗ[ℂ] V)}
  {F : Fin n → Fin n → Module.End ℂ V}

private theorem der0 (h : IsDerivK σ F) {X : Mat n} {γ : ℝ → UK n} (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X))
    (w : V) : HasDerivAt (fun t : ℝ => σ (γ t) w) (dX F X w) 0 := by
  obtain ⟨S, -, hw, -, -, hd⟩ := h.2 w
  rw [dX_apply]
  exact hd X γ hγ w hw

private theorem derS (h : IsDerivK σ F) {X : Mat n} {γ : ℝ → UK n} (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X))
    (hm : ∀ s h, γ (h + s) = γ h * γ s) (w : V) (s : ℝ) :
    HasDerivAt (fun t : ℝ => σ (γ t) w) (dX F X (σ (γ s) w)) s := by
  have h0 := der0 h hγ (σ (γ s) w)
  have h1 : HasDerivAt (fun t : ℝ => σ (γ (t - s)) (σ (γ s) w)) (dX F X (σ (γ s) w)) s := by
    have : HasDerivAt (fun t : ℝ => σ (γ t) (σ (γ s) w)) (dX F X (σ (γ s) w)) (s - s) := by
      simpa using h0
    exact HasDerivAt.comp_sub_const s s this
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show σ (γ t) w = σ (γ (t - s)) (σ (γ s) w)
  have := hm s (t - s)
  rw [sub_add_cancel] at this
  rw [this, map_mul]
  rfl

private theorem skw (h : IsDerivK σ F) {X : Mat n} {γ : ℝ → UK n} (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X))
    (h0 : γ 0 = 1) (u : V) : ⟪u, dX F X u⟫_ℂ + ⟪dX F X u, u⟫_ℂ = 0 := by
  have hu := der0 h hγ u
  have hi := hu.inner ℂ hu
  have hc : (fun t : ℝ => ⟪σ (γ t) u, σ (γ t) u⟫_ℂ) = fun _ => ⟪u, u⟫_ℂ := funext fun t => h.1 _ _ _
  have h1 : σ (γ 0) u = u := by rw [h0, map_one]; rfl
  rw [hc, h1] at hi
  exact hi.unique (hasDerivAt_const _ _)

private theorem zero_of (h : IsDerivK σ F) {X : Mat n} {γ : ℝ → UK n} (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X))
    (h0 : γ 0 = 1) (d : ℝ → V) (hd : ∀ s, HasDerivAt d (dX F X (d s)) s) (hz : d 0 = 0) (s : ℝ) : d s = 0 := by
  have hder : ∀ r, HasDerivAt (fun t : ℝ => ⟪d t, d t⟫_ℂ) 0 r := fun r => by
    have := (hd r).inner ℂ (hd r)
    rwa [skw h hγ h0] at this
  have hc := is_const_of_deriv_eq_zero (fun r => (hder r).differentiableAt) (fun r => (hder r).deriv) s 0
  simp only [hz, inner_zero_left] at hc
  exact inner_self_eq_zero.1 hc

end

end UpperTheory.RealTr.DerivativeAtIdentity

open UpperTheory.RealTr.DerivativeAtIdentity in
private theorem single_dX {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (D : Fin n → Fin n → V) (a b : Fin n) (z : ℂ) :
    ∑ c, ∑ d, (Matrix.single a b z : Mat n) c d • D c d = z • D a b := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro d _ hd
    simp [Matrix.single_apply, hd.symm]
  · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [Matrix.single_apply, hc.symm]
  · simp

open UpperTheory.RealTr.DerivativeAtIdentity in
private theorem entries_zero {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (D : Fin n → Fin n → V)
    (h : ∀ X : Mat n, Xᴴ = -X → ∑ c, ∑ d, X c d • D c d = 0) (a b : Fin n) : D a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_single])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Complex.star_def, Complex.conj_I, add_comm]
    ext c d
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.single_apply]
    split_ifs <;> simp [add_comm])
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    single_dX] at h1 h2
  have h3 : D a b + D b a = 0 := by
    have := congrArg (fun v => (-Complex.I) • v) h2
    simpa [smul_add, smul_smul] using this
  simp only [one_smul] at h1
  have h4 : (2 : ℂ) • D a b = 0 := by
    rw [two_smul]
    calc D a b + D a b = (D a b - D b a) + (D a b + D b a) := by abel
      _ = 0 := by rw [h1, h3, add_zero]
  exact (smul_eq_zero.1 h4).resolve_left two_ne_zero

open UpperTheory.RealTr.DerivativeAtIdentity in
theorem UpperTheory.RealTr.derAt :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : UK n →* (V →ₗ[ℂ] V)) (F : Fin n → Fin n → Module.End ℂ V), IsDerivK σ F →
      (∀ (μ θ : Wt n) (k : UK n) (v : V), k.1 = diagonal (fun a => Complex.exp (Complex.I * θ a)) → v ∈ wsp F μ → σ k v = evT θ (ex μ) • v) ∧
      ∀ (N : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] (σ' : UK n →* (N →ₗ[ℂ] N))
        (F' : Fin n → Fin n → Module.End ℂ N), IsDerivK σ' F' → ∀ t : N →ₗ[ℂ] V, (∀ k x, t (σ' k x) = σ k (t x)) ↔ t ∈ homL F' F := by
  intro n V _ _ σ F hF
  refine ⟨?_, ?_⟩
  · intro μ θ k v hk hv
    set X : Mat n := diagonal (fun a => Complex.I * (θ a : ℂ)) with hXd
    have hXs : Xᴴ = -X := by
      have hst : (star fun a => Complex.I * (θ a : ℂ)) = fun a => -(Complex.I * (θ a : ℂ)) := by
        ext a
        simp
      rw [hXd, Matrix.diagonal_conjTranspose, hst, ← Matrix.diagonal_neg]
    obtain ⟨γ, hγ, hm, h0⟩ := gam X hXs
    set c : ℂ := Complex.I * ∑ a, (θ a : ℂ) * (μ a : ℂ) with hc
    have hdv : dX F X v = c • v := by
      rw [dX_apply]
      have : ∀ a, ∑ b, X a b • F a b v = (Complex.I * (θ a : ℂ) * (μ a : ℂ)) • v := fun a => by
        rw [Finset.sum_eq_single a]
        · rw [hXd, Matrix.diagonal_apply_eq, hv a, smul_smul]
        · intro b _ hb
          simp [hXd, Matrix.diagonal_apply_ne _ hb.symm]
        · simp
      simp only [this, ← Finset.sum_smul, hc, Finset.mul_sum, mul_assoc]
    have hexp : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (c * t) • v) ((Complex.exp (c * s) * c) • v) s := fun s => by
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul c
      exact h1.cexp.smul_const v
    have hz := zero_of hF hγ h0 (fun s => σ (γ s) v - Complex.exp (c * s) • v)
      (fun s => by
        have := (derS hF hγ hm v s).fun_sub (hexp s)
        convert this using 1
        rw [map_sub, map_smul, hdv, smul_smul]) (by
        simp [h0]) 1
    have hg : γ 1 = k := by
      apply Subtype.ext
      rw [hγ, hk, hXd]
      simp [Matrix.exp_diagonal]
      intro i
      rw [Complex.exp_eq_exp_ℂ]
    have e := sub_eq_zero.1 hz
    rw [hg] at e
    rw [e]
    congr 1
    simp [evT, ex, hc]
  · intro N _ _ _ σ' F' hF' t
    let tc : N →L[ℝ] V := (LinearMap.toContinuousLinearMap t).restrictScalars ℝ
    have htc : ∀ x, tc x = t x := fun _ => rfl
    have hcomp : ∀ {X : Mat n} {γ : ℝ → UK n} (x : N) (s : ℝ) (y : N),
        HasDerivAt (fun r : ℝ => σ' (γ r) x) y s → HasDerivAt (fun r : ℝ => t (σ' (γ r) x)) (t y) s := fun x s y h =>
      tc.hasFDerivAt.comp_hasDerivAt s h
    constructor
    · intro hk a b x
      have := entries_zero (fun a b => t (F' a b x) - F a b (t x)) (fun X hX => by
        obtain ⟨γ, hγ, hm, h0⟩ := gam X hX
        have h1 := hcomp (X := X) x 0 _ (der0 hF' hγ x)
        simp only [hk] at h1
        have h2 := h1.unique (der0 hF hγ (t x))
        set_option synthInstance.maxHeartbeats 100000 in
          rw [dX_apply, dX_apply, map_sum] at h2
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul] at h2
        simp only [smul_sub, Finset.sum_sub_distrib]
        exact sub_eq_zero.2 h2) a b
      exact sub_eq_zero.1 this
    · intro ht k x
      obtain ⟨X, hX, hkX⟩ := (skewExp n).2 k
      obtain ⟨γ, hγ, hm, h0⟩ := gam X hX
      have hI : ∀ y : N, t (dX F' X y) = dX F X (t y) := fun y => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [dX_apply, dX_apply, map_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [ht a b y]
      have hz := zero_of hF hγ h0 (fun s => t (σ' (γ s) x) - σ (γ s) (t x))
        (fun s => by
          have := (hcomp (X := X) x s _ (derS hF' hγ hm x s)).fun_sub (derS hF hγ hm (t x) s)
          convert this using 1
          rw [map_sub, hI]) (by
          simp [h0]) 1
      have hg : γ 1 = k := by
        apply Subtype.ext
        rw [hγ, ← hkX]
        simp
      rw [hg] at hz
      exact sub_eq_zero.1 hz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Gelf2
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.gelf2 :
    ∀ (n : ℕ) (χ : Fin n → ℂ), GlobalTheory.Dec.gelfVal χ 2 = ∑ a, χ a ^ 2 - (nsq (rhoV n) : ℂ) := by
  intro n χ
  have hr : Formalism.QuantumDeterminants.rhoStd n = rhoV n := rfl
  rw [GlobalTheory.CasimirEigen.gelfVal_two_eq, hr, nsq]
  push_cast
  simp only [sq]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HomSurj
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem kspan_stb {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) :
    Stb F (Formalism.REAL.kSpan (fun _ => true) F x) := by
  intro a b y hy
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf] at hy ⊢
  intro S hS
  exact hS.2 a b rfl y (hy S hS)

private theorem proj_comm {n : ℕ} {N : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    {F : Fin n → Fin n → Module.End ℂ N} (hF : UF F) (S : Submodule ℂ N) [S.HasOrthogonalProjection]
    (hS : Stb F S) (a b : Fin n) (y : N) :
    S.starProjection (F a b y) = F a b (S.starProjection y) := by
  have hz : F a b (y - S.starProjection y) ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [← hF.unit b a w]
    exact Submodule.inner_right_of_mem_orthogonal (hS b a w hw)
      (Submodule.sub_starProjection_mem_orthogonal y)
  refine Submodule.eq_starProjection_of_mem_orthogonal' (hS a b _ (S.starProjection_apply_mem y)) hz ?_
  rw [← map_add (f := _), add_sub_cancel]

theorem UpperTheory.RealTr.homSurj :
    ∀ (n : ℕ) (N V : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (F : Fin n → Fin n → Module.End ℂ N) (K : Fin n → Fin n → Module.End ℂ V), UF F → UF K → LocF K → ∀ (ν : Wt n) (φ : hw F ν →ₗ[ℂ] hw K ν), ∃ t ∈ homL F K, (∀ x : hw F ν, t x = φ x) ∧ ∀ μ, μ ≠ ν → ∀ x ∈ hw F μ, t x = 0 := by
  intro n N V _ _ _ _ _ F K hF hK hL ν φ
  have hKR : Formalism.REAL.KRel (fun _ => true) F := Formalism.REAL.glRel_kRel _ F hF.gl
  have hKU : Formalism.REAL.KUnit (fun _ => true) F := fun a b _ => hF.unit a b
  obtain ⟨m, x, μ, hx, horth, hsup⟩ := Formalism.REAL.kDecomp N n (fun _ => true) F ⊤ inferInstance hKR hKU
    (fun a b _ y _ => trivial)
  obtain ⟨P, hP⟩ : ∃ P : Fin m → N →L[ℂ] N,
      ∀ i, P i = (Formalism.REAL.kSpan (fun _ => true) F (x i)).starProjection := ⟨_, fun _ => rfl⟩
  have hPmem : ∀ i y, P i y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) := by
    intro i y
    rw [hP]
    exact Submodule.starProjection_apply_mem _ y
  have hPself : ∀ i y, y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) → P i y = y := by
    intro i y hy
    rw [hP]
    exact Submodule.starProjection_eq_self_iff.mpr hy
  have hPorth : ∀ i j y, j ≠ i → y ∈ Formalism.REAL.kSpan (fun _ => true) F (x j) → P i y = 0 := by
    intro i j y hji hy
    rw [hP]
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (zero_mem _) (fun w hw => ?_)
    rw [sub_zero]
    exact horth j i hji y hy w hw
  have hcomm : ∀ i a b y, P i (F a b y) = F a b (P i y) := by
    intro i a b y
    rw [hP]
    exact proj_comm hF _ (kspan_stb F (x i)) a b y
  have hcomp : ∀ (μ' : Wt n) (y : N), KHighest (fun _ => true) F μ' y →
      ∀ i, KHighest (fun _ => true) F μ' (P i y) := by
    intro μ' y hy i
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← hcomm, hy.1 a, map_smul]
    · rw [← hcomm, hy.2 a b hab he, map_zero]
  have huniq : ∀ (μ' : Wt n) (y : N) i, KHighest (fun _ => true) F μ' y →
      y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) → y = 0 ∨ μ' = μ i ∧ ∃ c : ℂ, y = c • x i :=
    fun μ' y i hy hm => Formalism.REAL.kHiUniq N n _ F (μ i) μ' (x i) y hKR hKU (hx i).2.2 hm hy
  have hsum : ∀ y : N, y = ∑ i, P i y := by
    intro y
    have hy : y ∈ ⨆ i, Formalism.REAL.kSpan (fun _ => true) F (x i) := by
      rw [hsup]
      trivial
    refine Submodule.iSup_induction (motive := fun y => y = ∑ i, P i y) _ hy ?_ ?_ ?_
    · intro j z hz
      rw [Finset.sum_eq_single j (fun i _ hij => hPorth i j z (Ne.symm hij) hz)
        (fun h => absurd (Finset.mem_univ j) h), hPself j z hz]
    · simp
    · intro a b ha hb
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [← ha, ← hb]
  have hg : ∀ i, ∃ g : N →ₗ[ℂ] V, (∀ a b (y : N), g (F a b y) = K a b (g y)) ∧
      (μ i = ν → ∀ h : x i ∈ hw F ν, g (x i) = (φ ⟨x i, h⟩ : V)) ∧ (μ i ≠ ν → g = 0) := by
    intro i
    by_cases h : μ i = ν
    · have hxi : x i ∈ hw F ν := by
        rw [← h]
        exact (hx i).2.2
      obtain ⟨S, hSf, hvS, hSstb⟩ := hL (φ ⟨x i, hxi⟩ : V)
      obtain ⟨g, hg1, hg2⟩ := GlobalTheory.CompanionTheory.TransS.InfChar.hHWMap n (fun _ => true) N V F K ν (x i)
        (φ ⟨x i, hxi⟩ : V) S (fun a b c d _ _ => hF.gl a b c d) (fun a b _ => hF.unit a b)
        (fun a b c d _ _ => hK.gl a b c d) (fun a b _ => hK.unit a b) (hx i).2.1 hxi
        (φ ⟨x i, hxi⟩).2 hSf (fun a b _ => hSstb a b) hvS
      exact ⟨g, fun a b y => hg2 a b rfl y, fun _ _ => hg1, fun hne => absurd h hne⟩
    · exact ⟨0, fun a b y => by simp, fun h' => absurd h' h, fun _ => rfl⟩
  choose g hgL hgv hg0 using hg
  have happ : ∀ y, (∑ i, (g i).comp (P i : N →ₗ[ℂ] N)) y = ∑ i, g i (P i y) := by
    intro y
    simp [LinearMap.sum_apply]
  refine ⟨∑ i, (g i).comp (P i : N →ₗ[ℂ] N), ?_, ?_, ?_⟩
  · refine Submodule.sum_mem _ (fun i _ => ?_)
    show ∀ a b (y : N), (g i).comp (P i : N →ₗ[ℂ] N) (F a b y) = K a b ((g i).comp (P i : N →ₗ[ℂ] N) y)
    intro a b y
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hcomm i a b y]
    exact hgL i a b _
  · intro y
    have key : ∀ i, g i (P i y) = (φ ⟨P i y, hcomp ν y y.2 i⟩ : V) := by
      intro i
      rcases huniq ν (P i y) i (hcomp ν y y.2 i) (hPmem i y) with h0 | ⟨hμ, c, hc⟩
      · have e : (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν) = 0 := Subtype.ext h0
        rw [e, map_zero, Submodule.coe_zero, h0, map_zero]
      · have hxi : x i ∈ hw F ν := by
          rw [hμ]
          exact (hx i).2.2
        have e : (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν) = c • ⟨x i, hxi⟩ := Subtype.ext hc
        rw [e, map_smul, Submodule.coe_smul, hc, map_smul, hgv i hμ.symm hxi]
    have hs : (∑ i, (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν)) = y := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact (hsum y).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [happ, Finset.sum_congr rfl (fun i _ => key i), ← Submodule.coe_sum, ← map_sum, hs]
  · intro μ' hne y hy
    rw [happ]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases h : μ i = ν
    · rcases huniq μ' (P i y) i (hcomp μ' y hy i) (hPmem i y) with h0 | ⟨hμ, _⟩
      · rw [h0, map_zero]
      · exact absurd (hμ.trans h) hne
    · rw [hg0 i h, LinearMap.zero_apply]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnRel
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem tri {A : Type} [Ring A] (x y z p q : A) (h1 : y * z + z * y = p)
    (h2 : x * z + z * x = q) : x * y * z - z * (x * y) = x * p - q * y := by
  rw [← h1, ← h2]
  noncomm_ring

private theorem leib {A : Type} [Ring A] (X u v : A) :
    X * (u * v) - u * v * X = (X * u - u * X) * v + u * (X * v - v * X) := by
  noncomm_ring

private theorem spn_comm {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (hc : Clif c) (a b d e : Fin n) :
    spn c a b * c d e - c d e * spn c a b =
      (if b = d then c a e else 0) - (if e = a then c d b else 0) := by
  have hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t :=
    fun t r => (Algebra.commutes r t).symm
  have hsum : spn c a b * c d e - c d e * spn c a b =
      ∑ f, (c a f * c f b * c d e - c d e * (c a f * c f b)) := by
    unfold spn
    rw [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    split_ifs
    · rw [hs]
      abel
    · simp
  rw [hsum]
  have hterm : ∀ f, c a f * c f b * c d e - c d e * (c a f * c f b) =
      c a f * (if b = d ∧ f = e then 1 else 0) - (if f = d ∧ a = e then 1 else 0) * c f b := by
    intro f
    exact tri _ _ _ _ _ (hc f b d e) (hc a f d e)
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases hbd : b = d
    · simp [hbd]
    · simp [hbd]
  · by_cases hea : e = a
    · subst hea
      simp
    · have : ∀ f : Fin n, ¬ (f = d ∧ a = e) := fun f h => hea h.2.symm
      simp [this, hea]

theorem UpperTheory.RealTr.spnRel :
    ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A), Clif c → GlRel (spn c) ∧
      ∀ a b d e, spn c a b * c d e - c d e * spn c a b = (if b = d then c a e else 0) - (if e = a then c d b else 0) := by
  intro n A _ _ c hc
  refine ⟨?_, fun a b d e => spn_comm c hc a b d e⟩
  intro a b g h
  have hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t :=
    fun t r => (Algebra.commutes r t).symm
  have expand : ∀ X : A, X * spn c g h - spn c g h * X =
      ∑ f, (X * (c g f * c f h) - c g f * c f h * X) := by
    intro X
    unfold spn
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
    split_ifs
    · rw [hs]
      abel
    · simp
  rw [expand]
  simp_rw [leib, spn_comm c hc]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  unfold spn
  by_cases hbg : b = g <;> by_cases hha : h = a
  · subst hbg
    subst hha
    simp
  · simp [hbg, hha, Ne.symm hha]
  · simp [hbg, hha, Ne.symm hbg]
    abel
  · simp [hbg, hha, Ne.symm hbg, Ne.symm hha]
end
end

