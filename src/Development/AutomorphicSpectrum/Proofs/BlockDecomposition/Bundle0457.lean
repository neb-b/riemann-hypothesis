module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0421
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0420
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCongruenceFactorization
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1

open GlobalTheory.SplitWeil ValuativeRel

section Core

variable {k : Type} [Field k]

def rowM (n : ℕ) (a : Fin (n + 1) → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  1 + Matrix.of fun r c => if r = Fin.last n then a c else 0

theorem rowM_apply (n : ℕ) (a : Fin (n + 1) → k) (r c : Fin (n + 1)) :
    rowM n a r c = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) r c + if r = Fin.last n then a c else 0 := rfl

theorem rowM_mul (n : ℕ) (a b : Fin (n + 1) → k) :
    rowM n a * rowM n b = rowM n (a + b + a (Fin.last n) • b) := by
  ext r c
  have e : rowM n a * rowM n b = 1 + (Matrix.of fun r c => if r = Fin.last n then a c else 0) +
      (Matrix.of fun r c => if r = Fin.last n then b c else 0) +
      (Matrix.of fun r c => if r = Fin.last n then a c else 0) *
        (Matrix.of fun r c => if r = Fin.last n then b c else 0) := by
    unfold rowM
    noncomm_ring
  rw [e]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, rowM_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hr : r = Fin.last n
  · subst hr
    simp [Finset.sum_ite_eq', ite_mul]
    ring
  · simp [hr]

def rowGL (n : ℕ) (a : Fin (n + 1) → k) (hu : 1 + a (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k where
  val := rowM n a
  inv := rowM n (-(1 + a (Fin.last n))⁻¹ • a)
  val_inv := by
    rw [rowM_mul]
    have : a + -(1 + a (Fin.last n))⁻¹ • a + a (Fin.last n) • -(1 + a (Fin.last n))⁻¹ • a = 0 := by
      ext c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      field_simp
      ring
    rw [this]
    ext r c
    simp [rowM_apply]
  inv_val := by
    rw [rowM_mul]
    have : -(1 + a (Fin.last n))⁻¹ • a + a + (-(1 + a (Fin.last n))⁻¹ • a) (Fin.last n) • a = 0 := by
      ext c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      field_simp
      ring
    rw [this]
    ext r c
    simp [rowM_apply]

theorem rowGL_inv_val (n : ℕ) (a : Fin (n + 1) → k) (hu : 1 + a (Fin.last n) ≠ 0) :
    (((rowGL n a hu)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      rowM n (-(1 + a (Fin.last n))⁻¹ • a) := rfl

end Core

section Core2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rowM_near (s : kˣ) (n : ℕ) (a : Fin (n + 1) → k) (ha : ∀ c, a c ∈ cball s) :
    GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s (rowM n a) := by
  intro r c
  rw [rowM_apply, add_sub_cancel_left]
  split_ifs
  · exact ha c
  · exact (ballSub s).zero_mem

theorem rowGL_mem (s : kˣ) (hs : valuation k (s : k) ≤ 1) (n : ℕ) (a : Fin (n + 1) → k)
    (hu : 1 + a (Fin.last n) ≠ 0) (hv : valuation k (1 + a (Fin.last n)) = 1) (ha : ∀ c, a c ∈ cball s) :
    rowGL n a hu ∈ congGL k s hs (n + 1) := by
  refine ⟨rowM_near s n a ha, ?_⟩
  rw [rowGL_inv_val]
  refine rowM_near s n _ fun c => ?_
  show valuation k ((-(1 + a (Fin.last n))⁻¹ • a) c) ≤ valuation k (s : k)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, Valuation.map_neg, map_inv₀, hv, inv_one, one_mul]
  exact ha c

theorem core (s : kˣ) (hs : valuation k (s : k) ≤ 1) (hs1 : valuation k (s : k) < 1) {n i : ℕ} (hi : i < n)
    (A B M : GL (Fin (n + 1)) k) (hM : M ∈ Mir k n) (hMAB : M = A * B) (hB : B ∈ congGL k s hs (n + 1))
    (hA : ∀ r c : Fin (n + 1), i < r.val → c.val ≤ i → (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) r c = 0) :
    ∃ a x : GL (Fin (n + 1)) k, a ∈ Mir k n ∧ x ∈ Mir k n ∧ x ∈ congGL k s hs (n + 1) ∧ M = a * x ∧
      ∀ r c : Fin (n + 1), i < r.val → c.val ≤ i → (a : Matrix (Fin (n + 1)) (Fin (n + 1)) k) r c = 0 := by
  classical
  set Bi : Matrix (Fin (n + 1)) (Fin (n + 1)) k := ((B⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) with hBi
  let a : Fin (n + 1) → k := fun c => Bi (Fin.last n) c - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) c
  have ha : ∀ c, a c ∈ cball s := fun c => hB.2 (Fin.last n) c
  have hv : valuation k (1 + a (Fin.last n)) = 1 :=
    Valuation.map_one_add_of_lt _ (lt_of_le_of_lt (ha _) hs1)
  have hu : 1 + a (Fin.last n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv

  have hAB : A = M * B⁻¹ := by rw [hMAB]; group
  have hlast : ∀ c, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) c = Bi (Fin.last n) c := by
    intro c
    have hl := (mem_Mir_iff k M).1 hM
    rw [hAB, Units.val_mul, Matrix.mul_apply, hl]
    simp [eLast, Pi.single_apply, hBi]
  have ha0 : ∀ c : Fin (n + 1), c.val ≤ i → a c = 0 := by
    intro c hc
    have h1 : Bi (Fin.last n) c = 0 := by
      rw [← hlast c]
      exact hA _ c (by simpa using hi) hc
    have h2 : Fin.last n ≠ c := by
      intro e
      rw [← e] at hc
      simp at hc
      omega
    simp [a, h1, Matrix.one_apply_ne h2]
  let R := rowGL n a hu
  have hRlast : ∀ c, (R : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) c = Bi (Fin.last n) c := by
    intro c
    show rowM n a _ _ = _
    rw [rowM_apply]
    simp [a]
  have hR : R ∈ congGL k s hs (n + 1) := rowGL_mem s hs n a hu hv ha
  have hx : R * B ∈ Mir k n := by
    rw [mem_Mir_iff]
    funext c
    have e : (Bi * (B : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = 1 := by
      rw [hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 := congrFun (congrFun e (Fin.last n)) c
    rw [Matrix.mul_apply] at e2
    rw [Units.val_mul, Matrix.mul_apply]
    simp only [hRlast]
    rw [e2]
    simp [eLast, Pi.single_apply, Matrix.one_apply, eq_comm]
  refine ⟨A * R⁻¹, R * B, ?_, hx, (congGL k s hs (n + 1)).mul_mem hR hB, ?_, ?_⟩
  · have : A * R⁻¹ = M * (R * B)⁻¹ := by rw [hMAB]; group
    rw [this]
    exact (Mir k n).mul_mem hM ((Mir k n).inv_mem hx)
  · rw [hMAB]; group
  · intro r c hr hc
    have e : ((R⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = rowM n (-(1 + a (Fin.last n))⁻¹ • a) := rfl
    have e1 : ∀ l, rowM n (-(1 + a (Fin.last n))⁻¹ • a) l c = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) l c := by
      intro l
      rw [rowM_apply]
      simp [ha0 c hc]
    rw [Units.val_mul, e, Matrix.mul_apply]
    simp only [e1]
    simp [Matrix.one_apply, hA r c hr hc]

end Core2

theorem near_block {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : kˣ) {n : ℕ} (g : Mir k n)
    (hg : NearOne s ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) :
    NearOne s ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro a b
  have h := hg (Fin.castSucc a) (Fin.castSucc b)
  have e : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (1 : Matrix (Fin n) (Fin n) k) a b := by
    simp [Matrix.one_apply]
  rw [e] at h
  exact h

theorem mirProj_mem_cong {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : kˣ) (hs : valuation k (s : k) ≤ 1) {n : ℕ} (g : Mir k n) (hg : g ∈ congM k s hs n) :
    mirabolicProjection k n g ∈ congGL k s hs n := by
  refine ⟨near_block s g hg.1, ?_⟩
  rw [← map_inv]
  exact near_block s g⁻¹ hg.2

theorem mirProj_sEmb {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (m : Mir k n) : mirabolicProjection k (n + 1) (sEmb k n m) = (m : GL (Fin (n + 1)) k) := by
  apply Units.ext
  ext a b
  show glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) = _
  simp [glEmbMat]

theorem mirProj_dEmb {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (d : Fin (t + 1) → k) : mirabolicProjection k ((i + 1) + t + 1) (dEmb k i t d) = 1 :=
  GlobalTheory.CompanionTheory.BZPhiPG.Grp.mirProj_eq_one_of_mem _ (Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩)

theorem mem_mirabolicParabolic_mul_cong : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (hs1 : ValuativeRel.valuation k (s : k) < 1)
    (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1))
    (κ : Mir k ((i + 1) + t + 1)) (hκ : κ ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1))
    (e : dEmb k i t d * sEmb k ((i + 1) + t) m = h * κ),
  ∃ a ∈ MirabolicParabolic k (i + 1) t, ∃ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t), m = a * x := by
  intro k _ _ _ _ i t s hs hs1 d m h hh κ hκ e
  have e1 := congrArg (mirabolicProjection k ((i + 1) + t + 1)) e
  rw [map_mul, map_mul, mirProj_dEmb, mirProj_sEmb, one_mul] at e1
  have hA : ∀ r c : Fin ((i + 1) + t + 1), i < r.val → c.val ≤ i →
      ((mirabolicProjection k ((i + 1) + t + 1) h : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) r c = 0 := by
    intro r c hr hc
    have := GlobalTheory.CompanionTheory.BZPhiPG.Grp.hpg_entry h hh (Fin.castSucc r) (by simpa using hr)
      (by have := r.isLt; simp; omega) ⟨c.val, by omega⟩
    exact this
  obtain ⟨a, x, ha, hx, hxc, hax, hent⟩ := core s hs hs1 (n := (i + 1) + t) (i := i) (by omega) _ _
    (m : GL (Fin ((i + 1) + t + 1)) k) m.2 e1 (mirProj_mem_cong s hs κ hκ) hA
  refine ⟨⟨a, ha⟩, (GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff k (i + 1) t _).2 ?_, ⟨x, hx⟩, hxc, Subtype.ext hax⟩
  intro b c
  apply hent
  · rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]
    omega
  · rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
    have := c.isLt
    omega

end GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFactorizationCharacterTrivial
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Conj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unip_cc (n : ℕ) (v : Fin n → k) (r c : Fin n) :
    (unip k n (Multiplicative.ofAdd v)).val (Fin.castSucc r) (Fin.castSucc c) = (1 : Matrix (Fin n) (Fin n) k) r c := by
  show (1 + colMat k n v) _ _ = _
  simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem unip_lc (n : ℕ) (v : Fin n → k) (c : Fin n) :
    (unip k n (Multiplicative.ofAdd v)).val (Fin.last n) (Fin.castSucc c) = 0 := by
  show (1 + colMat k n v) _ _ = _
  simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem unip_ll (n : ℕ) (v : Fin n → k) :
    (unip k n (Multiplicative.ofAdd v)).val (Fin.last n) (Fin.last n) = 1 := by
  show (1 + colMat k n v) _ _ = _
  simp [colMat]

theorem unip_mul_glEmb (n : ℕ) (g : GL (Fin n) k) (a b c : Fin n → k)
    (h : ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec a = b + c) :
    unip k n (Multiplicative.ofAdd a) * glEmb k n g =
      glEmb k n g * unip k n (Multiplicative.ofAdd b) * unip k n (Multiplicative.ofAdd c) := by
  rw [mul_assoc, ← map_mul, ← ofAdd_add, ← h, glEmb_mul_unip']
  simp only [toAdd_ofAdd]
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem castM_val {a b : ℕ} (h : a = b) (m : Mir k a) (x y : Fin (b + 1)) :
    ((castM k h m : Mir k b) : GL (Fin (b + 1)) k).val x y =
      (m : GL (Fin (a + 1)) k).val (Fin.cast (by omega) x) (Fin.cast (by omega) y) := by
  subst h
  rfl

def eps (i t : ℕ) : (Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) ≃ Fin ((i + 1) + t + 1) :=
  (ePG i (t + 1)).trans (finCongr (by omega))

theorem piPerm_eps (i t : ℕ) (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    piPerm i t (eps i t s) = eGP (i + 1) t s := by
  simp [piPerm, eps]

theorem blockIndex_true (i t : ℕ) (y : Fin (t + 1)) : eGP (i + 1) t ⟨true, y⟩ = Fin.natAdd (i + 1) y :=
  Fin.ext (by simp [eGP, two, stdSum])

theorem blockIndex_false (i t : ℕ) (a : Fin (i + 1)) : eGP (i + 1) t ⟨false, a⟩ = Fin.castAdd (t + 1) a :=
  Fin.ext (by simp [eGP, two, stdSum])

def gEl (i t : ℕ) (m : Mir k (i + (t + 1))) : GL (Fin ((i + 1) + t + 1)) k :=
  wGL k i t * ((castM k (by omega) m : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹

theorem gEl_inv (i t : ℕ) (m : Mir k (i + (t + 1))) : (gEl i t m)⁻¹ = gEl i t m⁻¹ := by
  simp [gEl, mul_assoc, map_inv]

theorem wGL_conj_mulVec (i t : ℕ) (M : GL (Fin ((i + 1) + t + 1)) k) (u : Fin ((i + 1) + t + 1) → k)
    (a : Fin ((i + 1) + t + 1)) :
    ((wGL k i t * M * (wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val.mulVec u) (piPerm i t a) =
      (M.val.mulVec (u ∘ piPerm i t)) a := by
  show ((Equiv.Perm.permMatrix k (piPerm i t)⁻¹ * M.val * Equiv.Perm.permMatrix k (piPerm i t)).mulVec u) (piPerm i t a) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec, Matrix.permMatrix_mulVec]
  simp [Function.comp]

theorem gEl_mulVec (i t : ℕ) (m : Mir k (i + (t + 1))) (u : Fin ((i + 1) + t + 1) → k)
    (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    ((gEl i t m).val.mulVec u) (eGP (i + 1) t s) =
      (∑ x : Fin (i + 1), (m : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) ⟨false, x⟩) *
        u (eGP (i + 1) t ⟨false, x⟩)) +
      ∑ y : Fin (t + 1), (m : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) ⟨true, y⟩) *
        u (eGP (i + 1) t ⟨true, y⟩) := by
  rw [← piPerm_eps, gEl, wGL_conj_mulVec]
  show (∑ b : Fin ((i + 1) + t + 1), (_ : k)) = _
  rw [← Equiv.sum_comp (eps i t), Fintype.sum_sigma, Fintype.sum_bool, add_comm]
  simp only [Function.comp, piPerm_eps]
  congr 1
  all_goals exact Finset.sum_congr rfl fun x _ => by rw [castM_val]; rfl

theorem ePG_true_ne_last (i t : ℕ) (y : Fin (t + 1)) : ePG i (t + 1) ⟨true, y⟩ ≠ Fin.last (i + (t + 1)) := by
  intro e
  have h1 := congrArg Fin.val e
  rw [Cells.ePG_true_val] at h1
  have := y.2
  simp only [Fin.val_last] at h1
  change y.1 < t + 1 at this
  omega

theorem ePG_false_castSucc' (i t : ℕ) (y : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc y⟩ = Fin.castSucc (Fin.castAdd (t + 1) y) :=
  Fin.ext (by simpa using Cells.ePG_false_val (i + 1) (t + 1) y)

theorem ePG_true' (i t : ℕ) (y : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, y⟩ = Fin.castSucc (Fin.natAdd (i + 1) y) :=
  Fin.ext (by simpa using Cells.ePG_true_val (i + 1) (t + 1) y)

abbrev uD (i t : ℕ) (d : Fin (t + 1) → k) : Fin ((i + 1) + t + 1) → k := @Fin.append (i + 1) (t + 1) k 0 d

theorem gEl_uD (i t : ℕ) (m : Mir k (i + (t + 1))) (d : Fin (t + 1) → k)
    (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    ((gEl i t m).val.mulVec (uD i t d)) (eGP (i + 1) t s) =
      ∑ y : Fin (t + 1), (m : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) ⟨true, y⟩) * d y := by
  rw [gEl_mulVec, Finset.sum_eq_zero, zero_add]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [blockIndex_true]
    congr 1
    exact Fin.append_right _ _ y
  · intro x _
    rw [blockIndex_false]
    have : uD i t d (Fin.castAdd (t + 1) x) = 0 := Fin.append_left _ _ x
    rw [this, mul_zero]

theorem vec_last (i t : ℕ) (m : Mir k (i + (t + 1))) (d : Fin (t + 1) → k) :
    ((gEl i t m).val.mulVec (uD i t d)) (Fin.castAdd (t + 1) (Fin.last i)) = 0 := by
  have h := gEl_uD i t m d ⟨false, Fin.last i⟩
  rw [blockIndex_false, ePG_false_last] at h
  refine h.trans (Finset.sum_eq_zero fun y _ => ?_)
  have hm := (mem_Mir_iff k (m : GL (Fin (i + (t + 1) + 1)) k)).1 m.2
  rw [hm]
  simp [eLast, Pi.single_apply, ePG_true_ne_last]

theorem vec_true (i t : ℕ) (h : HPG k i (t + 1)) (d : Fin (t + 1) → k) (y : Fin (t + 1)) :
    ((gEl i t (h : Mir k (i + (t + 1)))⁻¹).val.mulVec (uD i t d)) (Fin.natAdd (i + 1) y) =
      ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) y := by
  have h1 := gEl_uD i t (h : Mir k (i + (t + 1)))⁻¹ d ⟨true, y⟩
  rw [blockIndex_true] at h1
  refine h1.trans ?_
  have e : ((pgProj k i (t + 1) h).2)⁻¹ = (pgProj k i (t + 1) h⁻¹).2 := by
    rw [map_inv]; rfl
  rw [e]
  rfl

def cEl (i t : ℕ) (x : Fin (i + 1) → k) : Mir k ((i + 1) + (t + 1)) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append x (0 : Fin (t + 1) → k))), MirU_le_Mir k _ ⟨_, rfl⟩⟩

theorem cEl_mem (i t : ℕ) (x : Fin (i + 1) → k) : cEl i t x ∈ HPG k (i + 1) (t + 1) := by
  refine Cells.mem_HPG_of (I := i + 1) (T := t + 1) (cEl i t x) ?_ ?_
  · intro a b
    refine Cells.unip_castSucc_castSucc _ _ _ _ ?_
    intro e
    have := congrArg Fin.val e
    simp only at this
    omega
  · intro a
    refine (unip_apply_castSucc_last k _ _ _).trans ?_
    show Fin.append x (0 : Fin (t + 1) → k) (Fin.natAdd (i + 1) a) = 0
    simp

def uEl (i : ℕ) (x : Fin (i + 1) → k) : MirUin k (i + 1) :=
  ⟨⟨unip k (i + 1) (Multiplicative.ofAdd x), MirU_le_Mir k _ ⟨_, rfl⟩⟩, ⟨_, rfl⟩⟩

theorem pgProj_cEl (i t : ℕ) (x : Fin (i + 1) → k) :
    pgProj k (i + 1) (t + 1) ⟨cEl i t x, cEl_mem i t x⟩ = ((uEl i x : Mir k (i + 1)), 1) := by
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append x (0 : Fin (t + 1) → k)))).val
      (ePG (i + 1) (t + 1) ⟨false, a⟩) (ePG (i + 1) (t + 1) ⟨false, b⟩) =
      (unip k (i + 1) (Multiplicative.ofAdd x)).val a b
    induction a using Fin.lastCases with
    | last =>
      rw [ePG_false_last]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, unip_ll, unip_ll]
      | cast b => rw [ePG_false_castSucc', unip_lc, unip_lc]
    | cast a =>
      rw [ePG_false_castSucc']
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last, unip_apply_castSucc_last, unip_apply_castSucc_last]
        simp
      | cast b =>
        rw [ePG_false_castSucc', unip_cc, unip_cc]
        simp [Matrix.one_apply]
  · apply Units.ext
    ext a b
    show (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append x (0 : Fin (t + 1) → k)))).val
      (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) = (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) k) a b
    rw [ePG_true', ePG_true', unip_cc]
    simp [Matrix.one_apply]

theorem conj_eq_levi (i t : ℕ) (m : Mir k (i + (t + 1))) :
    wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) m) * (wEl k i t)⁻¹ = levi k _ (gEl i t m) := by
  rw [gEl, map_mul, map_mul, map_inv]
  rfl

theorem dEmb_conj :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (i t : ℕ) (h : HPG k i (t + 1)) (d : Fin (t + 1) → k),
  ∃ (c : HPG k (i + 1) (t + 1)) (u : MirUin k (i + 1)),
    pgProj k (i + 1) (t + 1) c = ((u : Mir k (i + 1)), 1) ∧ mirChar k ψ i u = 1 ∧
    dEmb k i t d * (wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹) =
      (wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹) * (c : Mir k ((i + 1) + (t + 1))) *
        dEmb k i t ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) := by
  intro k _ _ _ _ ψ i t h d
  let v : Fin ((i + 1) + t + 1) → k := (gEl i t (h : Mir k (i + (t + 1)))⁻¹).val.mulVec (uD i t d)
  let x : Fin (i + 1) → k := fun a => v (Fin.castAdd (t + 1) a)
  refine ⟨⟨cEl i t x, cEl_mem i t x⟩, uEl i x, pgProj_cEl i t x, ?_, ?_⟩
  · rw [mirChar_eq k ψ i (uEl i x) (Multiplicative.ofAdd x) rfl]
    have hx : x (Fin.last i) = 0 := vec_last i t _ d
    simp [hx]
  · rw [conj_eq_levi]
    apply Subtype.ext
    refine unip_mul_glEmb ((i + 1) + t + 1) (gEl i t (h : Mir k (i + (t + 1)))) _ _ _ ?_
    rw [gEl_inv]
    have key : ∀ z : Fin ((i + 1) + (t + 1)), v z = @Fin.append (i + 1) (t + 1) k x 0 z +
        @Fin.append (i + 1) (t + 1) k 0 ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) z := by
      intro z
      induction z using Fin.addCases with
      | left a => rw [Fin.append_left, Fin.append_left, Pi.zero_apply, add_zero]
      | right y =>
        rw [Fin.append_right, Fin.append_right, Pi.zero_apply, zero_add]
        exact vec_true i t h d y
    exact funext key

end GlobalTheory.CompanionTheory.BZPhiPG.Conj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VarietyStalkRegularDim
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem stalk_isRegularLocalRing_and_ringKrullDim_le :
    ∀ (Y : Var ℂ) (x : Y.X), IsRegularLocalRing (Y.X.presheaf.stalk x) ∧
      ringKrullDim (Y.X.presheaf.stalk x) ≤ Y.dim := by
  intro Y x
  have hsm : Smooth Y.str := SmoothOfRelativeDimension.smooth Y.dim Y.str
  haveI hAr : IsRegularRing (Y.X.presheaf.stalk x) :=
    ExtendRig.isRegularRing_stalk isRegularRing_of_smooth ℂ Y.str x
  refine ⟨IsRegularLocalRing.of_isRegularRing_of_isLocalRing _, ?_⟩
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens (Opens.mem_top x)
  have hdim : ringKrullDim Γ(Y.X, U) = Y.dim :=
    SmoothDim.ringKrullDim_affineOpen ℂ _ Y.str _ inferInstance U hU ⟨x, hx⟩
  letI : Algebra Γ(Y.X, U) (Y.X.presheaf.stalk x) := (Y.X.presheaf.germ U x hx).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  rw [← hdim, IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (Y.X.presheaf.stalk x)]
  exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

end GlobalTheory.CompanionTheory.KoszulCount
end

