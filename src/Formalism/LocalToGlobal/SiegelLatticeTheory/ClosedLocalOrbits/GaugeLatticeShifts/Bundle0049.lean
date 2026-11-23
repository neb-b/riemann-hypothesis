module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemSteps
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

def MemIsomOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (g : GL (Fin X.B.I.n) X.B.I.E), g ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J →
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      ∀ y, X.crd (n y) = (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y

def MemFlagOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Z : Matrix (Kap X) (Kap X) X.B.I.E)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), InPat (lvk X) 1 Z → (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) →
    (∀ j, ∀ x ∈ Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Xflag (lf D (X.Fu u)) j) ∧
      ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u))), n x - x ∈ Xsp (lf D (X.Fu u))

def MemLatOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsFullLattice D.host.E Λ →
    ∃ d : ℕ, 1 ≤ d ∧ ∀ (Z : Matrix (Kap X) (Kap X) X.B.I.E) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
      InPat (lvk X) 1 Z → (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Z = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) →
      (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) → Formalism.HermitianLatticesTheory.gmap n Λ = Λ

def MemConjOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (M : GL (Fin X.B.I.n) X.B.I.E), M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J →
    (∀ Z : Matrix (Kap X) (Kap X) X.B.I.E, (↑M⁻¹ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * gE X Z *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) =
        gE X (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _))) ∧
    (∀ Z : Matrix (Kap X) (Kap X) X.B.I.E, Zᴴ * JB X = -(JB X * Z) →
      (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _))ᴴ * JB X =
        -(JB X * (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _)))) ∧
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (d : ℕ) (A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E)),
      ∃ A' : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E),
        Gr X (↑M⁻¹ : Matrix _ _ _) * (((c * d : ℕ) : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) *
          Gr X (M : Matrix _ _ _) = (d : X.B.I.E) • A'.map (fun a => (a : X.B.I.E))

def MemPtOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Z : Matrix (Kap X) (Kap X) X.B.I.E) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) →
    ∃ x : X.B.I.GA, RatLink X x n ∧ ∀ v, Mv X v x.1 = (cay (2 * D.R.rS + 2) Z).map (X.B.I.φ v)

theorem ratMem_of (h1 : MemIsomOf) (h2 : MemFlagOf) (h3 : MemLatOf) (h4 : MemConjOf) (h5 : MemPtOf) : RatMem := by
  intro D X Y u u' t M hM hlin
  obtain ⟨d1, hd1, H1⟩ := h3 D X t.lam ((Y.rowsOK u).1 t.lam t.mem).1.1
  obtain ⟨d2, hd2, H2⟩ := h3 D X t.lam' ((Y.rowsOK u').1 t.lam' t.mem').1.1
  obtain ⟨hc1, hsk, c, hc, hdiv⟩ := h4 D X M hM
  have crd_inj : ∀ a b : (VS D).V, X.crd a = X.crd b → a = b := fun a b h => by
    rw [← Formalism.L2.SG.Pf.Level.toV_crd X a, h, Formalism.L2.SG.Pf.Level.toV_crd]
  refine ⟨c * d2 * d1, Nat.one_le_iff_ne_zero.2 (by positivity), fun Z hZ hZ' hZs hA => ?_⟩
  obtain ⟨A, hA⟩ := hA
  obtain ⟨n, hni, hn⟩ := h1 D X (gGL X le_rfl hZ) (gGL_mem X le_rfl hZ hZs)
  have hn' : ∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y := hn
  have hZs' := hsk Z hZs
  obtain ⟨m, hmi, hm⟩ := h1 D X (gGL X le_rfl hZ') (gGL_mem X le_rfl hZ' hZs')
  have hm' : ∀ y, X.crd (m y) =
      gE X (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _)) *ᵥ X.crd y := hm
  have hinv : ∀ y, X.crd (t.lin⁻¹ y) = (↑M⁻¹ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := by
    intro y
    have e := hlin (t.lin⁻¹ y)
    have : t.lin (t.lin⁻¹ y) = y := by
      show (t.lin * t.lin⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    rw [this] at e
    rw [e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hconj : t.lin⁻¹ * n * t.lin = m := by
    apply LinearEquiv.ext
    intro y
    apply crd_inj
    show X.crd (t.lin⁻¹ (n (t.lin y))) = _
    rw [hinv, hn', hlin, hm', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc1]
  have e1 : Z = (d1 : X.B.I.E) • ((((c * d2 : ℕ) : 𝓞 X.B.I.E)) • A).map (fun a => (a : X.B.I.E)) := by
    rw [hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    push_cast
    ring
  have e2 : Z = ((c * d2 : ℕ) : X.B.I.E) • ((((d1 : ℕ) : 𝓞 X.B.I.E)) • A).map (fun a => (a : X.B.I.E)) := by
    rw [hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    push_cast
    ring
  obtain ⟨A', hA'⟩ := hdiv d2 ((((d1 : ℕ) : 𝓞 X.B.I.E)) • A)
  have hnN : n ∈ NLam t.lam (lf D (X.Fu u)) :=
    ⟨⟨hni, H1 Z n hZ ⟨_, e1⟩ hn'⟩, h2 D X u Z n hZ hn'⟩
  have hmN : t.lin⁻¹ * n * t.lin ∈ NLam t.lam' (lf D (X.Fu u')) := by
    rw [hconj]
    refine ⟨⟨hmi, H2 _ m hZ' ⟨A', ?_⟩ hm'⟩, h2 D X u' _ m hZ' hm'⟩
    rw [← hA', ← e2]
  obtain ⟨x, hx, hMv⟩ := h5 D X Z n hni hn'
  exact ⟨x.1, ⟨x, n, hx, rfl, hnN, hmN⟩, hMv⟩

end Formalism.L2.SG.TermOp.Vanish
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseCong
section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section Gen

variable {R : Type*} [CommRing R] (O : Subring R)

def cg_C {α β : Type*} (c : ℕ) (A : Matrix α β R) : Prop := ∀ i j, ∃ t ∈ O, A i j = (c : R) * t

def cg_D {α β : Type*} (m : ℕ) (A : Matrix α β R) : Prop := ∀ i j, (m : R) * A i j ∈ O

variable {O} {α β γ : Type*}

theorem cg_C_zero (c : ℕ) : cg_C O c (0 : Matrix α β R) := fun _ _ => ⟨0, zero_mem _, by simp⟩

theorem cg_C_add {c : ℕ} {A B : Matrix α β R} (hA : cg_C O c A) (hB : cg_C O c B) : cg_C O c (A + B) := by
  intro i j
  obtain ⟨s, hs, e1⟩ := hA i j
  obtain ⟨t, ht, e2⟩ := hB i j
  exact ⟨s + t, add_mem hs ht, by rw [Matrix.add_apply, e1, e2, mul_add]⟩

theorem cg_C_neg {c : ℕ} {A : Matrix α β R} (hA : cg_C O c A) : cg_C O c (-A) := by
  intro i j
  obtain ⟨s, hs, e1⟩ := hA i j
  exact ⟨-s, neg_mem hs, by rw [Matrix.neg_apply, e1, mul_neg]⟩

theorem cg_C_sub {c : ℕ} {A B : Matrix α β R} (hA : cg_C O c A) (hB : cg_C O c B) : cg_C O c (A - B) := by
  rw [sub_eq_add_neg]; exact cg_C_add hA (cg_C_neg hB)

theorem cg_C_sum {ι : Type*} {s : Finset ι} {c : ℕ} {A : ι → Matrix α β R} (h : ∀ k ∈ s, cg_C O c (A k)) :
    cg_C O c (∑ k ∈ s, A k) :=
  Finset.sum_induction _ (cg_C O c) (fun _ _ => cg_C_add) (cg_C_zero c) h

theorem cg_C_dvd {c k : ℕ} {A : Matrix α β R} (hA : cg_C O (c * k) A) : cg_C O c A := by
  intro i j
  obtain ⟨s, hs, e1⟩ := hA i j
  exact ⟨k * s, mul_mem (natCast_mem _ _) hs, by rw [e1]; push_cast; ring⟩

theorem cg_D_of_C {m k : ℕ} {A A' : Matrix α β R} (hA : cg_D O m A) (h : cg_C O k (A' - A)) :
    cg_D O m A' := by
  intro i j
  obtain ⟨s, hs, e1⟩ := h i j
  have e2 : A' i j = A i j + k * s := by rw [← e1, Matrix.sub_apply]; ring
  rw [e2, mul_add, ← mul_assoc]
  exact add_mem (hA i j) (mul_mem (mul_mem (natCast_mem _ m) (natCast_mem _ k)) hs)

theorem cg_D_mul_right {m : ℕ} (k : ℕ) {A : Matrix α β R} (hA : cg_D O m A) : cg_D O (m * k) A := by
  intro i j
  rw [Nat.cast_mul, mul_comm (m : R), mul_assoc]
  exact mul_mem (natCast_mem _ _) (hA i j)

theorem cg_D_mul_left {m : ℕ} (k : ℕ) {A : Matrix α β R} (hA : cg_D O m A) : cg_D O (k * m) A := by
  intro i j
  rw [Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (hA i j)

theorem cg_C_mul_left [Fintype β] {m c : ℕ} {P : Matrix α β R} {A : Matrix β γ R} (hP : cg_D O m P)
    (hA : cg_C O (c * m) A) : cg_C O c (P * A) := by
  choose t ht e using hA
  intro i j
  refine ⟨∑ k, ((m : R) * P i k) * t k j, sum_mem fun k _ => mul_mem (hP i k) (ht k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e k j]; push_cast; ring

theorem cg_C_mul_right [Fintype β] {m c : ℕ} {A : Matrix α β R} {Q : Matrix β γ R}
    (hA : cg_C O (c * m) A) (hQ : cg_D O m Q) : cg_C O c (A * Q) := by
  choose t ht e using hA
  intro i j
  refine ⟨∑ k, t i k * ((m : R) * Q k j), sum_mem fun k _ => mul_mem (ht i k) (hQ k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e i k]; push_cast; ring

theorem cg_D_mul [Fintype β] {m k : ℕ} {P : Matrix α β R} {Q : Matrix β γ R} (hP : cg_D O m P)
    (hQ : cg_D O k Q) : cg_D O (m * k) (P * Q) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun l _ => ?_
  rw [show ((m * k : ℕ) : R) * (P i l * Q l j) = ((m : R) * P i l) * ((k : R) * Q l j) by push_cast; ring]
  exact mul_mem (hP i l) (hQ l j)

theorem cg_D_pow [Fintype α] [DecidableEq α] {m : ℕ} {A : Matrix α α R} (hA : cg_D O m A) :
    ∀ j : ℕ, cg_D O (m ^ j) (A ^ j) := by
  intro j
  induction j with
  | zero =>
    intro i k
    rw [pow_zero, pow_zero, Nat.cast_one, one_mul, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact cg_D_mul ih hA

theorem cg_pow [Fintype α] [DecidableEq α] {m : ℕ} {A A' : Matrix α α R} (hA : cg_D O m A)
    (hA' : cg_D O m A') : ∀ (j c : ℕ), cg_C O (c * m ^ j) (A' - A) → cg_C O c (A' ^ j - A ^ j) := by
  intro j
  induction j with
  | zero => intro c _; simpa using cg_C_zero (O := O) (α := α) (β := α) c
  | succ j ih =>
    intro c h
    have e : A' ^ (j + 1) - A ^ (j + 1) = (A' ^ j - A ^ j) * A' + A ^ j * (A' - A) := by
      rw [pow_succ, pow_succ, Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e]
    refine cg_C_add (cg_C_mul_right (ih (c * m) ?_) hA') (cg_C_mul_left (cg_D_pow hA j) ?_)
    · rwa [show c * m * m ^ j = c * m ^ (j + 1) by ring]
    · exact cg_C_dvd (k := m) (by rwa [show c * m ^ j * m = c * m ^ (j + 1) by ring])

theorem cg_geo [Fintype α] [DecidableEq α] {m : ℕ} {A A' : Matrix α α R} (hA : cg_D O m A)
    (hA' : cg_D O m A') (N c : ℕ) (h : cg_C O (c * m ^ N) (A' - A)) : cg_C O c (geo N A' - geo N A) := by
  unfold geo
  rw [← Finset.sum_sub_distrib]
  refine cg_C_sum fun j hj => cg_pow hA hA' j c ?_
  have hj' : j ≤ N := (Finset.mem_range.1 hj).le
  refine cg_C_dvd (k := m ^ (N - j)) ?_
  rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj']

theorem cg_C_half [Invertible (2 : R)] {c : ℕ} {A : Matrix α β R} (h : cg_C O (2 * c) A) :
    cg_C O c ((⅟2 : R) • A) := by
  intro i j
  obtain ⟨t, ht, e⟩ := h i j
  refine ⟨t, ht, ?_⟩
  rw [Matrix.smul_apply, e, smul_eq_mul]
  push_cast
  linear_combination ((c : R) * t) * invOf_mul_self (2 : R)

theorem cg_D_half [Invertible (2 : R)] {m : ℕ} {A : Matrix α β R} (h : cg_D O m A) :
    cg_D O (2 * m) ((⅟2 : R) • A) := by
  intro i j
  have e : ((2 * m : ℕ) : R) * ((⅟2 : R) • A) i j = (m : R) * A i j := by
    rw [Matrix.smul_apply, smul_eq_mul]
    push_cast
    linear_combination ((m : R) * A i j) * invOf_mul_self (2 : R)
  rw [e]; exact h i j

theorem cg_cay [Fintype α] [DecidableEq α] [Invertible (2 : R)]
    (hden : ∀ A : Matrix α α R, ∃ m : ℕ, 1 ≤ m ∧ cg_D O m A) (N : ℕ) (Z : Matrix α α R) (c : ℕ)
    (hc : 1 ≤ c) :
    ∃ c' : ℕ, 1 ≤ c' ∧ ∀ Z' : Matrix α α R, cg_C O c' (Z' - Z) → cg_C O c (cay N Z' - cay N Z) := by
  obtain ⟨mZ, hmZ, hZ⟩ := hden Z
  obtain ⟨mG, hmG, hG⟩ := hden (geo N ((⅟2 : R) • Z))
  refine ⟨2 * (c * (mZ * mG) * (2 * mZ) ^ N), ?_, fun Z' h => ?_⟩
  · have h1 : 0 < (2 * mZ) ^ N := pow_pos (Nat.mul_pos two_pos hmZ) N
    exact Nat.mul_pos two_pos (Nat.mul_pos (Nat.mul_pos hc (Nat.mul_pos hmZ hmG)) h1)
  have hY : cg_D O (2 * mZ) ((⅟2 : R) • Z) := cg_D_half hZ
  have hYd : cg_C O (c * (mZ * mG) * (2 * mZ) ^ N) ((⅟2 : R) • Z' - (⅟2 : R) • Z) := by
    rw [← smul_sub]; exact cg_C_half h
  have hY' : cg_D O (2 * mZ) ((⅟2 : R) • Z') := cg_D_of_C hY hYd
  have hGd := cg_geo hY hY' N (c * (mZ * mG)) hYd
  have hZ0 : cg_D O (mZ * mG) Z := cg_D_mul_right mG hZ
  have hG0 : cg_D O (mZ * mG) (geo N ((⅟2 : R) • Z)) := cg_D_mul_left mZ hG
  have hG0' := cg_D_of_C hG0 hGd
  have e : cay N Z' - cay N Z = (Z' - Z) * geo N ((⅟2 : R) • Z') +
      Z * (geo N ((⅟2 : R) • Z') - geo N ((⅟2 : R) • Z)) := by
    unfold cay; simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [e]
  refine cg_C_add (cg_C_mul_right ?_ hG0') (cg_C_mul_left hZ0 hGd)
  exact cg_C_dvd (k := 2 * (2 * mZ) ^ N)
    (by rwa [show c * (mZ * mG) * (2 * (2 * mZ) ^ N) = 2 * (c * (mZ * mG) * (2 * mZ) ^ N) by ring])

end Gen

section Adelic

theorem cg_D_exists {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {α β : Type} [Fintype α] [Fintype β] (A : Matrix α β (E ⊗[F] Af F)) :
    ∃ m : ℕ, 1 ≤ m ∧ cg_D (IntAf F E) m A := by
  obtain ⟨m, hm, h⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.uniform_nat_mul (IntAf F E) (fun p : α × β => A p.1 p.2)
    (fun p => Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_IntAf _)
  exact ⟨m, hm, fun i j => h (i, j)⟩

end Adelic

theorem cayley_continuous : CayCont := by
  intro D X Z c hc
  exact cg_cay (O := IntAf X.B.I.F X.B.I.E) (fun A => cg_D_exists A) _ Z c hc

end Formalism.L2.SG.Pf.SlabNDensePf
end
end

