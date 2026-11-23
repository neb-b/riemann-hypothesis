module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.UnipBLeColFixOne
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.QIterSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.DerCharBlkAtMirU
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mirU_apply {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) (a b : Fin (n + 1))
    (hab : ¬ ((b : ℕ) = n ∧ (a : ℕ) < n)) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b = if a = b then 1 else 0 := by
  obtain ⟨v, hv⟩ := (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k n u hu :
    ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv']
  show (1 + colMat k n v.toAdd) a b = _
  rw [Matrix.add_apply, Matrix.one_apply]
  have hc : colMat k n v.toAdd a b = 0 := by
    simp only [colMat]
    split_ifs with hb
    · have ha0 : ¬ (a : ℕ) < n := fun h' => hab ⟨by rw [hb, Fin.val_last], h'⟩
      have ha : a = Fin.last n := by
        ext
        have := a.isLt
        rw [Fin.val_last]
        omega
      rw [ha, Fin.lastCases_last]
    · rfl
  rw [hc, add_zero]

theorem blkAt_mirU_apply {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n) (hu : mirabolicProjection k n u = 1) (a b : Fin N)
    (hab : ¬ ((b : ℕ) = n ∧ (a : ℕ) < n)) :
    ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) a b =
      if a = b then 1 else 0 := by
  rw [blkAt_apply]
  by_cases ha : (a : ℕ) < n + 1
  · rw [dif_pos ha]
    by_cases hb : (b : ℕ) < n + 1
    · rw [dif_pos hb, mirU_apply u hu _ _ (by simpa using hab)]
      by_cases e : a = b
      · subst e
        simp
      · rw [if_neg e, if_neg]
        intro e'
        exact e (Fin.ext (by simpa using congrArg Fin.val e'))
    · rw [dif_neg hb, if_neg]
      intro e
      subst e
      exact hb ha
  · rw [dif_neg ha]

theorem blkAt_mirU_mem {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) ∈ derUnip k N n := by
  refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => ?_⟩
  · rw [Fin.lt_def] at hji
    rw [blkAt_mirU_apply h u hu i j (by omega), if_neg (fun e => by rw [e] at hji; omega)]
  · rw [blkAt_mirU_apply h u hu i i (by omega), if_pos rfl]
  · rw [blkAt_mirU_apply h u hu i j (by omega), Matrix.one_apply]

theorem derChar_blkAt_mirU (ψ : AddChar k Circle) {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n)
    (hu : mirabolicProjection k n u = 1) : derChar k ψ N n ⟨_, blkAt_mirU_mem h u hu⟩ = 1 := by
  rw [derChar_def]
  simp only [whitCharFrom, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  show ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
  rw [blkAt_mirU_apply h u hu _ _ (by omega), if_neg (fun e => by rw [e] at h1; omega)]

theorem blkAt_levi {n N : ℕ} (h : n + 1 ≤ N) (g : GL (Fin n) k) :
    blkAt k (n + 1) N h ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = blkAt k n N (by omega) g := by
  ext a b
  rw [blkAt_apply, blkAt_apply]
  have hl : ∀ (a' b' : Fin (n + 1)), (((levi k n g : Mir k n) : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) a' b' = glEmbMat k n (g : Matrix (Fin n) (Fin n) k) a' b' :=
    fun _ _ => rfl
  by_cases ha : (a : ℕ) < n
  · have ha' : (a : ℕ) < n + 1 := by omega
    rw [dif_pos ha', dif_pos ha]
    by_cases hb : (b : ℕ) < n
    · have hb' : (b : ℕ) < n + 1 := by omega
      rw [dif_pos hb', dif_pos hb, hl, glEmbMat_apply']
      simp only [ha, hb, dif_pos]
    · rw [dif_neg hb]
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true]
      · rw [dif_neg hb']
  · rw [dif_neg ha]
    by_cases ha' : (a : ℕ) < n + 1
    · rw [dif_pos ha']
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, dif_neg, not_false_eq_true]
        simp only [Fin.ext_iff]
      · rw [dif_neg hb']
        split_ifs with e <;> first | rfl | (simp only [Fin.ext_iff] at e; omega)
    · rw [dif_neg ha']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_mir {n : ℕ} (p : Mir k n) :
    Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det (mirabolicProjection k n p) := by
  have hl := (mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · rw [hl, Fin.succAbove_last]
    simp only [eLast, Pi.single_eq_same, mul_one, Fin.val_last]
    rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul]
    rfl
  · intro j _ hj
    rw [hl, eLast, Pi.single_eq_of_ne hj]
    simp
  · simp

theorem mir_act (ψ : AddChar k Circle) {n N : ℕ} (h : n + 1 ≤ N) {V D : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup D] [Module ℂ D] (π : Representation ℂ (GL (Fin N) k) V) (ρ' : Representation ℂ (GL (Fin n) k) D)
    (q : V →ₗ[ℂ] D) (hq1 : ∀ g v, q (π (blkAt k n N (by omega) g) v) = ρ' g (q v))
    (hq2 : twKer π (derUnip k N n) (derChar k ψ N n) ≤ LinearMap.ker q) (p : Mir k n) :
    (∀ v, q (π (blkAt k (n + 1) N h p) v) = ρ' (mirabolicProjection k n p) (q v)) ∧
      Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det (mirabolicProjection k n p) := by
  have hu1 : mirabolicProjection k n (p * (levi k n (mirabolicProjection k n p))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi, mul_inv_cancel]
  have hp : (p : GL (Fin (n + 1)) k) = ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k) *
      ((levi k n (mirabolicProjection k n p) : Mir k n) : GL (Fin (n + 1)) k) := by
    rw [← Subgroup.coe_mul, inv_mul_cancel_right]
  have hkill : ∀ w, q (π (blkAt k (n + 1) N h
      ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k)) w) = q w := by
    intro w
    rw [← sub_eq_zero, ← map_sub]
    apply hq2
    refine Submodule.subset_span ⟨⟨_, blkAt_mirU_mem h _ hu1⟩, w, ?_⟩
    rw [derChar_blkAt_mirU ψ h _ hu1]
    simp
  refine ⟨fun v => ?_, det_mir p⟩
  conv_lhs => rw [hp]
  rw [map_mul, map_mul, Module.End.mul_apply, hkill, blkAt_levi, hq1]

end PositivityTheory.RgUd.Form.U.Asm
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.IsLatticeStandardLattice
section
noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lat


variable (k) in
def lat0 (m : ℕ) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ valuation k ((1 : kˣ) : k)}
  add_mem' := fun {a b} ha hb i => by
    show valuation k (a i + b i) ≤ _
    exact ((valuation k).map_add _ _).trans (max_le (ha i) (hb i))
  zero_mem' := fun i => by simp
  neg_mem' := fun {a} ha i => by
    show valuation k (-(a i)) ≤ _
    rw [Valuation.map_neg]
    exact ha i

theorem coe_standard_lattice (m : ℕ) : (lat0 k m : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => cball (1 : kˣ) := by
  ext x
  simp only [Set.mem_univ_pi, cball, Set.mem_setOf_eq]
  exact Iff.rfl

theorem isLattice_standard_lattice (m : ℕ) : IsLat (lat0 k m) := by
  unfold IsLat
  rw [coe_standard_lattice]
  exact ⟨isCompact_univ_pi fun _ => isCompact_cball _, isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball _⟩

theorem isLat_sup {m : ℕ} {A₁ A₂ : AddSubgroup (Fin (m + 1) → k)} (h1 : IsLat A₁) (h2 : IsLat A₂) :
    IsLat (A₁ ⊔ A₂) := by
  unfold IsLat at *
  rw [AddSubgroup.add_normal]
  exact ⟨h1.1.add h2.1, h2.2.add_left⟩

end Lat

section Transport

variable {ψ : AddChar k Circle} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem kills_congr {a b : ℕ} (hab : a = b) {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : Kills ψ π a B) : Kills ψ π b B := by
  subst hab; exact h

theorem mirEq_congr {a b : ℕ} (hab : a = b) {ha : a + 1 ≤ N} {hb : b + 1 ≤ N} {s t : ℝ} (hst : s = t)
    {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : MirEq π a ha s B) : MirEq π b hb t B := by
  subst hab; subst hst; exact h

theorem lvl_congr {a b : ℕ} (hab : a = b) {ha : a + 2 ≤ N} {hb : b + 2 ≤ N} {s t : ℝ} (hst : s = t)
    {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : Lvl k ψ π a ha s B) : Lvl k ψ π b hb t B := by
  subst hab; subst hst; exact h

theorem isDens_smul {m : ℕ} {h : m + 2 ≤ N} {A₀ : AddSubgroup (Fin (m + 1) → k)} {B B' I C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hB : IsDens ψ h π A₀ B B') (hI : IsDens ψ h π A₀ I C) (c : ℂ) (hIc : ∀ v w, I v w = c * B v w) :
    ∀ v w, C v w = c * B' v w := by
  intro v w
  obtain ⟨A₁, hA₁, -, hB1⟩ := hB v w
  obtain ⟨A₂, hA₂, -, hI2⟩ := hI v w
  have hL := isLat_sup hA₁ hA₂
  rw [hI2 _ hL le_sup_right, hB1 _ hL le_sup_left, hIc]
  ring

end Transport

section Chain


open Classical in
def chain (hUD : UDens k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : ℕ → (V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  | 0 => B
  | d + 1 =>
    if h : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) then
      Classical.choose (hUD ψ hψc hψ1 (N - 2 - d) N (by obtain ⟨hN, -⟩ := h; omega) V π hs (d : ℝ)
        (chain hUD hψc hψ1 π hs B d) h.2
        (lat0 k (N - 2 - d)) (isLattice_standard_lattice _))
    else 0

variable (hUD : UDens k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ} {V : Type}
  [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

theorem chain_zero : chain hUD hψc hψ1 π hs B 0 = B := rfl

theorem chain_succ (d : ℕ) (hN : d + 2 ≤ N)
    (hL : Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d)) :
    IsDens ψ (by omega : N - 2 - d + 2 ≤ N) π (lat0 k (N - 2 - d)) (chain hUD hψc hψ1 π hs B d)
        (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      IsPsd (chain hUD hψc hψ1 π hs B (d + 1)) ∧ Kills ψ π (N - 2 - d + 1) (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      MirEq π (N - 2 - d) (by omega) ((d : ℝ) + 1) (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      (∀ v, chain hUD hψc hψ1 π hs B (d + 1) v v = 0 →
        v ∈ twKer π (derUnip k N (N - 2 - d + 1)) (lvlChar k ψ N (N - 2 - d + 1)) ⊔
          LinearMap.ker (chain hUD hψc hψ1 π hs B d)) := by
  have hh : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) := ⟨hN, hL⟩
  simp only [chain, dif_pos hh]
  exact Classical.choose_spec (hUD ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ)
    (chain hUD hψc hψ1 π hs B d) hL (lat0 k (N - 2 - d)) (isLattice_standard_lattice _))

theorem isPsd_of_inv (hB : IsInvForm π B) : IsPsd B := by
  obtain ⟨h1, h2, -⟩ := hB
  unfold IsPsd
  refine ⟨h1, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (h2 v hv).le

theorem chain_lvl (hB : IsInvForm π B) :
    ∀ d (hd : d + 2 ≤ N), Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) := by
  intro d
  induction d with
  | zero =>
    intro hd
    refine ⟨isPsd_of_inv π B hB, ?_, ?_⟩
    · refine kills_congr (a := N) (by omega) ?_
      intro v hv w
      rw [twKer_derUnip_self ψ π] at hv
      rw [(Submodule.mem_bot ℂ).1 hv]
      simp
    · intro p _ v w
      simp [chain_zero, hB.2.2]
  | succ d ih =>
    intro hd
    obtain ⟨-, h2, h3, h4, -⟩ := chain_succ hUD hψc hψ1 π hs B d (by omega) (ih (by omega))
    exact ⟨h2, kills_congr (by omega) h3, mirEq_congr (by omega) (by push_cast; ring) h4⟩

end Chain

end PositivityTheory.RgUd.Form.U.Asm
end
end

