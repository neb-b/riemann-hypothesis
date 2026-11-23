module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizontalModBreuilKisinOfEulerNoPole
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.HorizPole

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem X_pow_eq : (X : K⟦X⟧) ^ e = E K l e - l := by rw [E]; ring

theorem E_ne_zero : E K l e ≠ 0 := (isUnit_E (K := K) l e).ne_zero

theorem pow_mul_EN (j : ℕ) (f : K⟦X⟧) :
    E K l e ^ j * (E K l e * N K f) =
      E K l e * N K (E K l e ^ j * f) - (j : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * (E K l e ^ j * f) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, N_E]
  cases j with
  | zero => simp
  | succ j => simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]; push_cast; ring

theorem N_pow_mul (j : ℕ) (G : K⟦X⟧) :
    N K (E K l e ^ (j + 1) * G) =
      E K l e ^ (j + 1) * N K G + ((j + 1 : ℕ) : K⟦X⟧) * E K l e ^ j * ((e : K⟦X⟧) * X ^ e) * G := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, N_E]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]; push_cast; ring

theorem EN_xiExt (D : BKDat O K l e a ι η H) (w : Vec K a ι) :
    D.EN (D.xiExt w) = D.xiExt (fun τ i => E K l e * N K (w τ i)) := by
  rw [PhiMod.EN_apply, PhiMod.conn_xiExt]
  exact (D.xiExt_smul_tot (fun _ => E K l e) _).symm

theorem N_mem_Rpi {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) : N K f ∈ Rpi O K l e :=
  N_mem (derivative_mem_R l hf)

theorem C_mem_Rpi (c : K) : C c ∈ Rpi O K l e := HasK.C_mem c

theorem cast_ne (j : ℕ) : (((j + 1) * e * l : ℕ) : K) ≠ 0 :=
  natCast_ne_zero' l (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.succ_ne_zero j) (NeZero.ne e))
    (Fact.out : l.Prime).ne_zero)

theorem C_inv_mul (j : ℕ) : C ((((j + 1) * e * l : ℕ) : K))⁻¹ * (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (l : K⟦X⟧)) = 1 := by
  have h : (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (l : K⟦X⟧)) = C ((((j + 1) * e * l : ℕ) : K)) := by
    rw [map_natCast]; push_cast; ring
  rw [h, ← map_mul, inv_mul_cancel₀ (cast_ne j), map_one]

theorem neg_step (D : BKDat O K l e a ι η H) (p : ℕ) (v : Vec K a ι)
    (hv : ∀ τ i, E K l e ^ (p + 1) * D.xiExt.symm v τ i ∈ Rpi O K l e) (hN : D.EN v ∈ D.Man) :
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧
      ∀ τ i, E K l e ^ p * D.xiExt.symm v₁ τ i ∈ Rpi O K l e := by
  set c : K := (((p + 1) * e * l : ℕ) : K) with hc
  refine ⟨v - c⁻¹ • D.EN v, ?_, ?_, fun τ i => ?_⟩
  · rw [sub_sub_cancel]; exact D.Man.smul_mem _ hN
  · rw [map_sub, map_smul]; exact sub_mem hN (D.Man.smul_mem _ (D.EN_mem_Man hN))
  · obtain ⟨w, rfl⟩ := D.xiExt.surjective v
    have hco : D.xiExt.symm (D.xiExt w - c⁻¹ • D.EN (D.xiExt w)) τ i =
        w τ i - C c⁻¹ * (E K l e * N K (w τ i)) := by
      rw [EN_xiExt, ← map_smul, ← map_sub, LinearEquiv.symm_apply_apply]
      simp [smul_eq_C_mul]
    rw [hco]
    have hF := hv τ i
    rw [LinearEquiv.symm_apply_apply] at hF
    have h2 := pow_mul_EN (l := l) (e := e) (p + 1) (w τ i)
    have h1 := C_inv_mul (K := K) (l := l) (e := e) p
    have hX := X_pow_eq (K := K) (l := l) (e := e)
    have key : E K l e * (E K l e ^ p * (w τ i - C c⁻¹ * (E K l e * N K (w τ i)))) =
        E K l e * (C c⁻¹ * (((p + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (E K l e ^ (p + 1) * w τ i) -
          N K (E K l e ^ (p + 1) * w τ i))) := by
      rw [← mul_assoc, ← pow_succ']
      linear_combination (-C c⁻¹) * h2 + (C c⁻¹ * ((p + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (E K l e ^ (p + 1) * w τ i)) * hX + (-(E K l e ^ (p + 1) * w τ i)) * h1
    rw [mul_left_cancel₀ E_ne_zero key]
    exact mul_mem (C_mem_Rpi _) (sub_mem (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) hF)
      (N_mem_Rpi hF))

theorem neg_all (D : BKDat O K l e a ι η H) (p : ℕ) : ∀ (v : Vec K a ι),
    (∀ τ i, E K l e ^ p * D.xiExt.symm v τ i ∈ Rpi O K l e) → D.EN v ∈ D.Man →
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ ∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e := by
  induction p with
  | zero => exact fun v hv hN => ⟨v, by simp, hN, fun τ i => by simpa using hv τ i⟩
  | succ p ih =>
    intro v hv hN
    obtain ⟨v₁, h1, h2, h3⟩ := neg_step D p v hv hN
    obtain ⟨v₂, h4, h5, h6⟩ := ih v₁ h3 h2
    refine ⟨v₂, ?_, h5, h6⟩
    have := add_mem h1 h4
    rwa [sub_add_sub_cancel] at this

theorem pos_step (D : BKDat O K l e a ι η H) (j : ℕ) (v : Vec K a ι)
    (hv : ∀ τ i, D.xiExt.symm v τ i ∈ Rpi O K l e)
    (hG : ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v τ i) = E K l e ^ j * G)
    (hN : D.EN v ∈ D.Man) :
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ (∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e) ∧
      ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v₁ τ i) = E K l e ^ (j + 1) * G := by
  set c : K := (((j + 1) * e * l : ℕ) : K) with hc
  obtain ⟨w, rfl⟩ := D.xiExt.surjective v
  simp only [LinearEquiv.symm_apply_apply] at hv hG
  have hco : ∀ τ i, D.xiExt.symm (D.xiExt w + c⁻¹ • D.EN (D.xiExt w)) τ i =
      w τ i + c⁻¹ • (E K l e * N K (w τ i)) := fun τ i => by
    rw [EN_xiExt, ← map_smul, ← map_add (f := _), LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨D.xiExt w + c⁻¹ • D.EN (D.xiExt w), ?_, ?_, fun τ i => ?_, fun τ i => ?_⟩
  · rw [sub_add_cancel_left]; exact neg_mem (D.Man.smul_mem _ hN)
  · rw [map_add (f := _), map_smul]; exact add_mem hN (D.Man.smul_mem _ (D.EN_mem_Man hN))
  · rw [hco, smul_eq_C_mul]
    exact add_mem (hv τ i) (mul_mem (C_mem_Rpi _) (mul_mem (E_mem l e _) (N_mem_Rpi (hv τ i))))
  · obtain ⟨G, hGm, hGe⟩ := hG τ i
    rw [hco]
    refine ⟨C c⁻¹ * (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * G + N K G), mul_mem (C_mem_Rpi _)
      (add_mem (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) hGm) (N_mem_Rpi hGm)), ?_⟩
    have h3 := N_pow_mul (l := l) (e := e) j G
    have h1 := C_inv_mul (K := K) (l := l) (e := e) j
    have hX := X_pow_eq (K := K) (l := l) (e := e)
    rw [map_add (f := _), Derivation.map_smul, hGe, ← mul_assoc, ← pow_succ', h3, smul_eq_C_mul]
    linear_combination (C c⁻¹ * ((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * E K l e ^ j * G) * hX +
      (-(E K l e ^ j * G)) * h1

theorem pos_all (D : BKDat O K l e a ι η H) (j : ℕ) : ∀ (v : Vec K a ι),
    (∀ τ i, D.xiExt.symm v τ i ∈ Rpi O K l e) → D.EN v ∈ D.Man →
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ (∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e) ∧
      ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v₁ τ i) = E K l e ^ j * G := by
  induction j with
  | zero => exact fun v hv hN => ⟨v, by simp, hN, hv, fun τ i => ⟨_, N_mem_Rpi (hv τ i), by simp⟩⟩
  | succ j ih =>
    intro v hv hN
    obtain ⟨v₁, h1, h2, h3, h4⟩ := ih v hv hN
    obtain ⟨v₂, h5, h6, h7, h8⟩ := pos_step D j v₁ h3 h4 h2
    refine ⟨v₂, ?_, h6, h7, h8⟩
    have := add_mem h1 h5
    rwa [sub_add_sub_cancel] at this

theorem one_div_lt : 1 / ((e : ℝ) * l) < 1 / e := by
  have he : (0 : ℝ) < e := by exact_mod_cast NeZero.pos e
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact one_div_lt_one_div_of_lt he (by nlinarith)

theorem init (D : BKDat O K l e a ι η H) (n : ℕ) (v : Vec K a ι) (hv : v ∈ divE l e n D.Man) :
    ∀ τ i, E K l e ^ (n + H) * D.xiExt.symm v τ i ∈ Rpi O K l e := by
  have h1 : E K l e ^ (n + H) • v ∈ D.ext (Rpi O K l e) := by
    rw [add_comm, pow_add, mul_smul]
    exact D.smul_mem_ext_of_basis (fun i => D.lower _ (D.bas_mem_M i)) (A_le_Rpi l e) (D.mem_Man.1 hv)
  have h2 := (_root_.GlobalTheory.BK.xiExt_mem_Lk_iff O K l e a ι D.toPhiMod (1 / e) one_div_lt
    (E K l e ^ (n + H) • D.xiExt.symm v)).1 (by
      have := D.xiExt_smul_tot (fun _ => E K l e ^ (n + H)) (D.xiExt.symm v)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this ▸ h1)
  exact fun τ i => mem_tot.1 h2 τ i

theorem fin (D : BKDat O K l e a ι η H) (r : Vec K a ι) (hr : ∀ τ i, r τ i ∈ Rpi O K l e) :
    E K l e ^ η • D.xiExt r ∈ D.Man :=
  D.mem_Man.2 (D.smul_mem_Mext (A_le_Rpi l e)
    ((_root_.GlobalTheory.BK.xiExt_mem_Lk_iff O K l e a ι D.toPhiMod (1 / e) one_div_lt r).2 (mem_tot.2 fun τ i => hr τ i)))

theorem taylor (f : K⟦X⟧) (hf : f ∈ Rpi O K l e) (B : ℕ) :
    ∃ g ∈ invL l (A O K), ∃ r ∈ Rpi O K l e, f - g = E K l e ^ B * r := by
  obtain ⟨g, hg⟩ : ∃ g : invL l (A O K),
      Ideal.Quotient.mk _ g = AdicCompletion.evalₐ (idE O K l e) B (toHat O K l e ⟨f, hf⟩) :=
    Ideal.Quotient.mk_surjective _
  obtain ⟨r, hr, h⟩ := (evalₐ_toHat_eq_iff l e B ⟨f, hf⟩ g).1 hg.symm
  exact ⟨g, g.2, r, hr, h⟩

theorem eulerDerivation_eisensteinPow_final_bound {f g r G : K⟦X⟧} (m B : ℕ) (hB : m + 1 ≤ B) (hg : g ∈ invL l (A O K))
    (hr : r ∈ Rpi O K l e) (hG : G ∈ Rpi O K l e) (hf : N K f = E K l e ^ m * G)
    (hfg : f - g = E K l e ^ B * r) :
    ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K g = E K l e ^ m * h := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
  have hX := X_pow_eq (K := K) (l := l) (e := e)
  set h' := G - (E K l e ^ (d + 1) * N K r +
    ((m + d + 1 : ℕ) : K⟦X⟧) * E K l e ^ d * ((e : K⟦X⟧) * X ^ e) * r) with hh'
  have hgf : g = f - E K l e ^ (m + d + 1) * r := by rw [show m + d + 1 = m + 1 + d by omega, ← hfg]; ring
  have hN : N K g = E K l e ^ m * h' := by
    rw [hgf, map_sub, hf, N_pow_mul, hh']
    ring
  have hh'R : h' ∈ Rpi O K l e := sub_mem hG (add_mem (mul_mem (pow_mem (E_mem l e _) _) (N_mem_Rpi hr))
    (mul_mem (mul_mem (mul_mem (natCast_mem _ _) (pow_mem (E_mem l e _) _))
      (mul_mem (natCast_mem _ _) (pow_mem HasU.X_mem _))) hr))
  obtain ⟨k, hk⟩ : N K g ∈ invL l (A O K) := N_mem (derivative_mem_away _ (fun _ => derivative_mem_A) hg)
  have hk' : (l : K⟦X⟧) ^ k * N K g ∈ A O K := by simpa using hk
  refine ⟨(l : K⟦X⟧) ^ k * h', mem_A_of_E_pow_mul_mem l e m
    (mul_mem (pow_mem (natCast_mem _ _) _) hh'R) ?_, k, ?_⟩
  · rw [hN] at hk'; convert hk' using 1; ring
  · rw [hN]; ring

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (n : ℕ) (v : Vec K a ι), v ∈ divE l e n D.Man → D.EN v ∈ D.Man → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), v - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D n v hv hN m
  obtain ⟨v₁, h1, h2, h3⟩ := neg_all D (n + H) v (init D n v hv) hN
  obtain ⟨v₂, h4, -, h6, h7⟩ := pos_all D m v₁ h3 h2
  choose G hGm hGe using h7
  choose g hg r hr hfg using fun (τ : ZMod a) (i : ι) => taylor (D.xiExt.symm v₂ τ i) (h6 τ i) (m + 1 + η)
  refine ⟨g, mem_tot.2 fun τ i => hg τ i, ?_, fun τ i =>
    eulerDerivation_eisensteinPow_final_bound m (m + 1 + η) (by omega) (hg τ i) (hr τ i) (hGm τ i) (hGe τ i) (hfg τ i)⟩
  have e0 : D.xiExt.symm v₂ - g = (fun _ : ZMod a => E K l e ^ (m + 1 + η)) • r :=
    funext fun τ => funext fun i => by simpa using hfg τ i
  have e1 : v₂ - D.xiExt g = E K l e ^ (m + 1) • (E K l e ^ η • D.xiExt r) := by
    rw [smul_smul, ← pow_add]
    have := D.xiExt_smul_tot (fun _ : ZMod a => E K l e ^ (m + 1 + η)) r
    rw [← e0, map_sub, LinearEquiv.apply_symm_apply] at this
    exact this
  have e2 : v - D.xiExt g = (v - v₁) + (v₁ - v₂) + (v₂ - D.xiExt g) := by abel
  rw [e2, e1]
  exact add_mem (add_mem h1 h4) (D.smul_mem_Man (pow_mem (E_mem l e _) _) (fin D r hr))

end GlobalTheory.HorizPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisible
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.HatDescent

variable {l : ℕ} [Fact l.Prime]

theorem aDp_ev_eis_mul_eq_zero {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (y : Per.BdRp l)
    (hy : GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) * y = 0) : y = 0 := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
    rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hxi
  refine (GlobalTheory.MemLoc.filtration_eq_xi_pow l ε hE).2.1 y ?_
  rw [← hc, map_mul, mul_assoc, hy, mul_zero]

theorem eis_pow_dvd_of_aDp_mem {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (n : ℕ)
    (x : (Wq l a)⟦X⟧)
    (h : GlobalTheory.MemLoc.aDp l (ϖ.ev a x) ∈ Ideal.span {GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) ^ n}) :
    eis l a e ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    have h1 : Per.θ l (ϖ.ev a x) = 0 := by
      have h2 := congrArg (Per.θD l) hc
      rw [map_mul, map_pow, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1,
        (ϖ.theta_ev_eq_zero_iff a _).2 dvd_rfl] at h2
      exact Subtype.ext (h2.symm.trans (by simp))
    obtain ⟨x', rfl⟩ := (ϖ.theta_ev_eq_zero_iff a x).1 h1
    have h2 : GlobalTheory.MemLoc.aDp l (ϖ.ev a x') ∈
        Ideal.span {GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) ^ n} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨c, ?_⟩
      rw [← sub_eq_zero]
      apply aDp_ev_eis_mul_eq_zero (a := a) ϖ
      rw [map_mul, map_mul] at hc
      rw [mul_sub, ← hc]
      ring
    obtain ⟨z, hz⟩ := ih x' h2
    exact ⟨z, by rw [hz, pow_succ']; ring⟩

end GlobalTheory.BKReal.HatDescent

namespace GlobalTheory.BKReal.HatDescent

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

def crdB {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) : OD l O →ₗ[ℤ_[l]] Per.BdRp l :=
  TensorProduct.lid ℤ_[l] (Per.BdRp l) ∘ₗ (b.coord j).rTensor (Per.BdRp l)

theorem crdB_tmul {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) (o : O) (β : Per.BdRp l) :
    crdB b j (o ⊗ₜ β) = b.coord j o • β := rfl

theorem crdB_mul {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) (c : Per.BdRp l) (z : OD l O) :
    crdB b j (z * (1 ⊗ₜ c)) = crdB b j z * c := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o β =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, crdB_tmul, crdB_tmul, smul_mul_assoc]
  | add x y hx hy => rw [add_mul, map_add (f := _), map_add (f := _), hx, hy, add_mul]

theorem crdB_sum {J : Type} [Fintype J] [DecidableEq J] (b : Module.Basis J ℤ_[l] O) (j : J)
    (β : J → Per.BdRp l) : crdB b j (∑ k, b k ⊗ₜ β k) = β j := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single j (fun k _ hk => by
    rw [crdB_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [Finsupp.single_apply, hk])
    (by simp), crdB_tmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]

variable {a e : ℕ} [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem toAc_eis (t : Wq l a →ₐ[ℤ_[l]] O) : toAc t K (eis l a e) = fun _ => EIn l e (A O K) := by
  have hX : toAc t K X = fun _ => uIn (A O K) :=
    funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _))
  have hE : EIn l e (A O K) = uIn _ ^ e + (l : A O K) := Subtype.ext (by simp [E])
  rw [eis, map_add (f := _), map_pow, hX, map_natCast, hE]
  rfl

theorem exists_of_toOD_iTot_mem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (f : ZMod a → A O K)
    (h : toOD l O (ϖ.iTot t K f) ∈
      Ideal.span {((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) : OD l O) ^ n}) :
    ∃ g : ZMod a → A O K, f = (fun _ => EIn l e (A O K)) ^ n * g := by
  classical
  set b := Module.Free.chooseBasis ℤ_[l] O
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K b f
  have hT : toOD l O (ϖ.iTot t K (∑ j, b j • toAc t K (x j))) =
      ∑ j, b j ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (x j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, PiSys.iTot_toAc]
    refine Finset.sum_congr rfl fun j _ => ?_
    show b j • ((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (x j))) = _
    rw [smul_tmul', smul_eq_mul, mul_one]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have hx : ∀ j, eis l a e ^ n ∣ x j := fun j => by
    apply eis_pow_dvd_of_aDp_mem ϖ n
    rw [Ideal.mem_span_singleton']
    refine ⟨crdB b j z, ?_⟩
    have := congrArg (crdB b j) (hz.trans hT)
    rw [crdB_sum, Algebra.TensorProduct.tmul_pow, one_pow, crdB_mul] at this
    exact this
  choose y hy using hx
  refine ⟨∑ j, b j • toAc t K (y j), ?_⟩
  simp only [hy, map_mul, map_pow, toAc_eis, Finset.mul_sum, mul_smul_comm]

end GlobalTheory.BKReal.HatDescent

namespace GlobalTheory.BKReal.PiSys

open GlobalTheory.BKReal.HatDescent

theorem eq_Ehat_pow_mul_of_iD_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (x : ZMod a → Ahat O K l e),
    ϖ.iD t K x ∈ Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} →
      ∃ y : ZMod a → Ahat O K l e, x = (fun _ => Ehat O K l e) ^ n * y := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ n x hx
  have hd : ϖ.iD t K (fun _ => Ehat O K l e) =
      (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
    rw [iD, glue_const, Ehat, iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  choose g x' hg using fun τ => exists_eq_algebraMap_add_pow_mul (EIn l e (invL l (A O K))) n (x τ)
  have hsplit : x = (fun τ => ofAl O K l e (g τ)) + (fun _ => Ehat O K l e) ^ n * x' :=
    funext fun τ => hg τ
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (l : A O K)) (S := invL l (A O K)) g
  choose r hr using hm

  have h1 : ϖ.iD t K (fun τ => ofAl O K l e (g τ)) ∈
      Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} := by
    rw [hsplit, map_add (f := _), map_mul, map_pow] at hx
    exact (Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).1 hx
  have h2 : (fun τ => ofA O K l e (r τ)) =
      (fun _ => ofA O K l e ((l : A O K) ^ m)) * fun τ => ofAl O K l e (g τ) := by
    funext τ
    rw [Pi.mul_apply, ofA, RingHom.comp_apply, RingHom.comp_apply, hr τ, Algebra.smul_def, map_mul]
  have h3 : toOD l O (ϖ.iTot t K r) ∈
      Ideal.span {((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) : OD l O) ^ n} := by
    rw [← iD_ofA, h2, map_mul, ← hd]
    exact Ideal.mul_mem_left _ _ h1
  obtain ⟨h, hh⟩ := exists_of_toOD_iTot_mem t ϖ n r h3
  have hu : IsUnit (algebraMap (A O K) (invL l (A O K)) (l : A O K)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hEA : algebraMap (A O K) (invL l (A O K)) (EIn l e (A O K)) = EIn l e (invL l (A O K)) := rfl
  have hgτ : ∀ τ, g τ = EIn l e (invL l (A O K)) ^ n *
      (algebraMap (A O K) (invL l (A O K)) (h τ) * ↑(hu.unit⁻¹ ^ m)) := fun τ => by
    have h4 : algebraMap (A O K) (invL l (A O K)) (l : A O K) ^ m * g τ =
        EIn l e (invL l (A O K)) ^ n * algebraMap (A O K) (invL l (A O K)) (h τ) := by
      have h5 := (hr τ).symm
      rw [Algebra.smul_def, hh, Pi.mul_apply, Pi.pow_apply] at h5
      simp only [map_mul, map_pow, hEA] at h5
      exact h5
    have hone : (↑(hu.unit⁻¹ ^ m) : invL l (A O K)) * algebraMap (A O K) (invL l (A O K)) (l : A O K) ^ m = 1 := by
      rw [Units.val_pow_eq_pow_val, ← mul_pow, hu.val_inv_mul, one_pow]
    linear_combination (-(g τ)) * hone + (↑(hu.unit⁻¹ ^ m) : invL l (A O K)) * h4
  refine ⟨fun τ => ofAl O K l e (algebraMap (A O K) (invL l (A O K)) (h τ) * ↑(hu.unit⁻¹ ^ m)) + x' τ, ?_⟩
  funext τ
  rw [hg τ, Pi.mul_apply, Pi.pow_apply, hgτ τ, map_mul, map_pow, mul_add]
  rfl

end GlobalTheory.BKReal.PiSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.BlockCharpoly

open Polynomial

theorem exists_factor_of_idempotent {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K)
    (he : e * e = e) (hr : e.rank = t) :
    ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e := by
  classical
  set V := LinearMap.range e.mulVecLin with hV
  have hd : Module.finrank K V = t := hr
  let bs := Module.finBasisOfFinrankEq K V hd
  let P : (Fin n → K) →ₗ[K] V := e.mulVecLin.rangeRestrict
  let fa : (Fin t → K) →ₗ[K] (Fin n → K) := V.subtype ∘ₗ bs.equivFun.symm.toLinearMap
  let fb : (Fin n → K) →ₗ[K] (Fin t → K) := bs.equivFun.toLinearMap ∘ₗ P

  have hP : ∀ v : V, P v = v := by
    rintro ⟨v, w, rfl⟩
    apply Subtype.ext
    show e.mulVecLin (e.mulVecLin w) = e.mulVecLin w
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he]
  refine ⟨LinearMap.toMatrix' fa, LinearMap.toMatrix' fb, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [fa, fb, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, hP,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · rw [← LinearMap.toMatrix'_comp]
    have hc : fa ∘ₗ fb = Matrix.toLin' e := by
      refine LinearMap.ext fun x => ?_
      simp only [fa, fb, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        Submodule.coe_subtype, P, Matrix.toLin'_apply]
      rfl
    rw [hc, LinearMap.toMatrix'_toLin']

theorem blockPol_factor {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hba : b * a = 1) (M : Matrix (Fin n) (Fin n) K) :
    blockPol (a * b) (a * b * M * (a * b)) = (b * M * a).charpoly := by
  unfold blockPol
  set A := a.map (C : K →+* K[X]) with hA
  set B := b.map (C : K →+* K[X]) with hB
  have hBA : B * A = 1 := by
    rw [hA, hB, ← Matrix.map_mul, hba, Matrix.map_one _ C.map_zero C.map_one]

  have hmat : (X : K[X]) • (a * b).map (C : K →+* K[X]) - (a * b * M * (a * b)).map (C : K →+* K[X])
        + 1 - (a * b).map (C : K →+* K[X])
      = 1 + (A * ((X : K[X]) • (1 : Matrix (Fin t) (Fin t) K[X]) - B * M.map (C : K →+* K[X]) * A - 1)) * B := by
    simp only [Matrix.map_mul, ← hA, ← hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hmat, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hBA, Matrix.one_mul, add_sub_cancel]
  have hBMA : B * M.map (C : K →+* K[X]) * A = (b * M * a).map (C : K →+* K[X]) := by
    rw [hA, hB, Matrix.map_mul, Matrix.map_mul]
  rw [hBMA, Matrix.charpoly]
  congr 1
  ext i j
  simp only [Matrix.charmatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp

theorem blockPol_eq_charpoly {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K)
    (he : e * e = e) (hr : e.rank = t) :
    ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e ∧
      ∀ M : Matrix (Fin n) (Fin n) K, blockPol e (e * M * e) = (b * M * a).charpoly := by
  obtain ⟨a, b, hba, hab⟩ := exists_factor_of_idempotent e he hr
  refine ⟨a, b, hba, hab, fun M => ?_⟩
  subst hab
  exact blockPol_factor a b hba M

end GlobalTheory.BlockCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulCocycleValuesZeroOnSmallSubgroupStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_cocycle_values_zero_on_small_subgroup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), (∀ h ∈ L, bform (X := X) x.1 y.1 h = 0) → ∀ h ∈ L, ∀ h' ∈ L, ∀ a b, (X.l i : A) ^ nu X i * x.1 h a * y.1 h' b = 0 := by
  first | exact @GlobalTheory.NewPrime.FormVanish.two_mul_values_eq_zero | exact GlobalTheory.NewPrime.FormVanish.two_mul_values_eq_zero | (intros; apply GlobalTheory.NewPrime.FormVanish.two_mul_values_eq_zero <;> assumption)
end

