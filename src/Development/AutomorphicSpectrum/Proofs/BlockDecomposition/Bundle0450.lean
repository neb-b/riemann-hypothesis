module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0420
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentOfProjectionZero
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem hecke_pow_kills_of_proj_eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J),
    PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → ∀ v : fixed π D.J, D.proj π (v : V) = 0 →
    ∃ j : ℕ, (U ^ j) v = 0 := by
  intro G _ _ _ D V _ _ π hπ t ht U hU v hv

  have hdom : ∀ r : ℕ, D.IsDom (t ^ r) := by
    intro r
    induction r with
    | zero => simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1
    | succ r ih =>
      rw [pow_succ]
      exact (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih ht.1

  have hecke : ∀ r : ℕ, PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w l _
      simp
    | succ r ih =>
      rw [pow_succ, pow_succ U]
      exact _root_.GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract G D V π hπ (t ^ r) t (hdom r) ht.1 _ _ ih hU

  have key : ∀ u ∈ twKer π D.N 1, ∃ R : ℕ, ∀ r ≥ R,
      ∀ l : Module.Dual ℂ V, (∀ x ∈ D.J, l ∘ₗ π x = l) → l (π ((t : G) ^ r) u) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, w, rfl⟩ := hu
      obtain ⟨R, hR⟩ := ht.2.1 (n : G) n.2
      refine ⟨R, fun r hr l hl => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
      have hmem : (t : G) ^ (R + j) * (n : G) * ((t : G) ^ (R + j))⁻¹ ∈ D.J ⊓ D.N := by
        have := (hdom j).1 _ hR
        convert this using 1
        simp only [Subgroup.coe_pow]
        rw [add_comm R j, pow_add]
        group
      have hx := hl _ hmem.1
      have hy := LinearMap.congr_fun hx (π ((t : G) ^ (R + j)) w)
      simp only [LinearMap.comp_apply] at hy
      have hz : π ((t : G) ^ (R + j) * (n : G) * ((t : G) ^ (R + j))⁻¹) (π ((t : G) ^ (R + j)) w)
          = π ((t : G) ^ (R + j)) (π (n : G) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hz] at hy
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hy, sub_self]
    | zero => exact ⟨0, fun r _ l _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, fun r hr l hl => ?_⟩
      rw [map_add (f := _), map_add (f := _), hA r (le_trans (le_max_left _ _) hr) l hl,
        hB r (le_trans (le_max_right _ _) hr) l hl, add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      refine ⟨A, fun r hr l hl => ?_⟩
      rw [map_smul, map_smul, hA r hr l hl, smul_zero]
  obtain ⟨R, hR⟩ := key _ ((Submodule.Quotient.mk_eq_zero _).1 hv)
  refine ⟨R, ?_⟩
  have h0 : (((U ^ R) v : fixed π D.J) : V) = 0 := by
    refine _root_.GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed G D.J D.isCompact_J V π hπ _ ((U ^ R) v).2 fun l hl => ?_
    rw [← hecke R v l hl, Subgroup.coe_pow]
    exact hR R le_rfl l hl
  exact Subtype.ext h0

end GlobalTheory.CompanionTheory.Cass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellDoubleCosetUniqueness
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Stab

section Perm

theorem piPerm_true_val (i t : ℕ) (x : Fin (t + 1)) (hx : i + x.val < (i + 1) + t + 1) :
    (piPerm i t ⟨i + x.val, hx⟩).val = i + 1 + x.val := by
  have h : (finCongr (by omega : i + 1 + t + 1 = i + (t + 1) + 1) ⟨i + x.val, hx⟩ :
      Fin (i + (t + 1) + 1)) = GlobalTheory.BZMir.Leib.ePG i (t + 1) ⟨true, x⟩ :=
    Fin.ext (by simp [GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]
  rw [h, Equiv.symm_apply_apply, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]

theorem piPerm_false_val (i t : ℕ) (y : Fin i) (hy : y.val < (i + 1) + t + 1) :
    (piPerm i t ⟨y.val, hy⟩).val = y.val := by
  have h : (finCongr (by omega : i + 1 + t + 1 = i + (t + 1) + 1) ⟨y.val, hy⟩ :
      Fin (i + (t + 1) + 1)) = GlobalTheory.BZMir.Leib.ePG i (t + 1) ⟨false, Fin.castSucc y⟩ :=
    Fin.ext (by simp [GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_false_val])
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]
  rw [h, Equiv.symm_apply_apply, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
  all_goals simp

end Perm

section Ent

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_symm_entry {a b : ℕ} (e : a = b) (r : Mir k b) (x y : ℕ) (hx : x < a + 1) (hy : y < a + 1)
    (hx' : x < b + 1) (hy' : y < b + 1) :
    (((castM k e).symm r : Mir k a) : GL (Fin (a + 1)) k).val ⟨x, hx⟩ ⟨y, hy⟩ =
      (r : GL (Fin (b + 1)) k).val ⟨x, hx'⟩ ⟨y, hy'⟩ := by
  subst e
  rfl

theorem mirProj_dEmb (i t : ℕ) (d : Fin (t + 1) → k) : mirabolicProjection k _ (dEmb k i t d) = 1 := by
  apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.mirProj_eq_one_of_mem
  exact Subgroup.mem_subgroupOf.mpr
    (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

theorem mirProj_wEl (i t : ℕ) : mirabolicProjection k _ (wEl k i t) = wGL k i t :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi _ _

theorem mirProj_sEmb (n : ℕ) (r : Mir k n) : mirabolicProjection k _ (sEmb k n r) = (r : GL (Fin (n + 1)) k) :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi _ _

theorem wGL_mul_apply (i t : ℕ) (M : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (a b : Fin ((i + 1) + t + 1)) :
    ((wGL k i t).val * M) (piPerm i t a) b = M a b := by
  show (Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t)⁻¹ * M) (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t a) b = M a b
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply]
  simp

theorem mul_wGL_apply (i t : ℕ) (M : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (a b : Fin ((i + 1) + t + 1)) :
    (M * (wGL k i t).val) a b = M a (piPerm i t b) := by
  show (M * Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t)⁻¹) a b = M a (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t b)
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply]
  simp [Equiv.Perm.inv_def]

theorem entry_eq (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k) (h : Mir k ((i + 1) + t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t)
    (x y : Fin ((i + 1) + t + 1)) :
    (r : GL (Fin ((i + 1) + t + 1)) k).val x y =
      (h : GL (Fin ((i + 1) + t + 1 + 1)) k).val (Fin.castSucc (piPerm i t x)) (Fin.castSucc (piPerm i t y)) := by
  have key := congrArg (GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t + 1)) e
  simp only [map_mul, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_dEmb, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_wEl,
    GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_sEmb, _root_.one_mul, _root_.mul_one] at key
  have key' := congrArg (fun g : GL (Fin ((i + 1) + t + 1)) k =>
    (g : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x) y) key
  simp only [Units.val_mul, GlobalTheory.CompanionTheory.BZPhiPG.Stab.wGL_mul_apply, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mul_wGL_apply] at key'
  exact key'

theorem entry_zero (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k) (h : Mir k ((i + 1) + t + 1))
    (hh : h ∈ HPG k (i + 1) (t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t)
    (x y : Fin ((i + 1) + t + 1)) (hx : i < (piPerm i t x).val) (hy : (piPerm i t y).val ≤ i) :
    (r : GL (Fin ((i + 1) + t + 1)) k).val x y = 0 := by
  rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_eq i t r d d' h e x y]
  have hc : (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ) < i + 1 := by omega
  have hz := GlobalTheory.CompanionTheory.BZPhiPG.Grp.hpg_entry h hh
    (Fin.castSucc (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x))
    (by rw [Fin.coe_castSucc]; exact hx)
    (by rw [Fin.coe_castSucc]; exact Nat.ne_of_lt (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x).isLt)
    ⟨(GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ), hc⟩
  have e₂ : (Fin.castLE (by omega) (⟨(GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ), hc⟩ : Fin (i + 1)) :
      Fin ((i + 1) + t + 1 + 1)) = Fin.castSucc (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y) := Fin.ext rfl
  rw [e₂] at hz
  exact hz

end Ent

theorem mem_of_double_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k), ∀ h ∈ HPG k (i + 1) (t + 1),
  dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t →
  ∃ h' ∈ HPG k i (t + 1), castM k (by omega) h' = r := by
  intro k _ _ _ _ i t r d d' h hh e
  have hab : i + (t + 1) = (i + 1) + t := by omega
  refine ⟨(GlobalTheory.CompanionTheory.BZPhiPG.castM k hab).symm r, ?_, MulEquiv.apply_symm_apply _ _⟩
  apply GlobalTheory.CompanionTheory.BZPhiPG.Cells.mem_HPG_of
  · intro x y
    have hxl := x.isLt
    have hyl := y.isLt
    refine (GlobalTheory.CompanionTheory.BZPhiPG.Stab.castM_symm_entry hab r (i + x.val) y.val (by omega) (by omega)
      (by omega) (by omega)).trans ?_
    exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_zero i t r d d' h hh e _ _
      (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_true_val]; omega) (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_false_val]; omega)
  · intro x
    have hxl := x.isLt
    have hcol : (Fin.last (i + (t + 1)) : Fin (i + (t + 1) + 1)) = ⟨(i + 1) + t, by omega⟩ :=
      Fin.ext (by rw [Fin.val_last, Fin.val_mk]; omega)
    rw [hcol]
    refine (GlobalTheory.CompanionTheory.BZPhiPG.Stab.castM_symm_entry hab r (i + x.val) ((i + 1) + t) (by omega) (by omega)
      (by omega) (by omega)).trans ?_
    exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_zero i t r d d' h hh e _ _
      (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_true_val]; omega) (GlobalTheory.CompanionTheory.BZPhiPG.Cells.piPerm_last_val i t).le

end GlobalTheory.CompanionTheory.BZPhiPG.Stab

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellParabolicNearIdentity
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rowD (i t : ℕ) (b : Fin (t + 1)) : Fin ((i + 1) + (t + 1) + 1) := Fin.castSucc (Fin.natAdd (i + 1) b)

theorem ePG_true_rowD (i t : ℕ) (b : Fin (t + 1)) : ePG (i + 1) (t + 1) ⟨true, b⟩ = rowD i t b :=
  Fin.ext (by simp [rowD, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])

def ent {n : ℕ} (a b : Fin (n + 1)) (p : Mir k n) : k :=
  ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b

theorem continuous_ent {n : ℕ} (a b : Fin (n + 1)) : Continuous (ent (k := k) a b) :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem a b

theorem ent_last_last {n : ℕ} (p : Mir k n) : ent (Fin.last n) (Fin.last n) p = 1 := by
  have hh := (mem_Mir_iff k _).1 p.2
  show ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1
  rw [hh]
  simp [eLast]

theorem colMat_mul_castSucc {n : ℕ} (v : Fin n → k) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (a : Fin n)
    (c : Fin (n + 1)) : (colMat k n v * A) (Fin.castSucc a) c = v a * A (Fin.last n) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp [colMat]
  · intro l _ hl
    simp [colMat, hl]
  · simp

theorem continuous_colMat_append (i t : ℕ) :
    Continuous fun d : Fin (t + 1) → k => colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := by
  refine continuous_matrix fun a b => ?_
  by_cases hb : b = Fin.last _
  · subst hb
    induction a using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast a =>
      induction a using Fin.addCases with
      | left a => simpa [colMat] using continuous_const
      | right a =>
        have e : ∀ d : Fin (t + 1) → k, colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
            (Fin.castSucc (Fin.natAdd (i + 1) a)) (Fin.last _) = d a := by
          intro d
          unfold colMat
          rw [if_pos rfl, Fin.lastCases_castSucc, Fin.append_right]
        exact (continuous_apply a).congr fun d => (e d).symm
  · simpa [colMat, hb] using continuous_const

theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_append i t)
  · exact continuous_const.sub (continuous_colMat_append i t)

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) 0) : Matrix _ _ k) = 1
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext a
    induction a using Fin.addCases <;> simp
  rw [this, colMat_zero, add_zero]

def delta (i t : ℕ) (u : Mir k ((i + 1) + (t + 1))) : Fin (t + 1) → k :=
  fun b => - ent (rowD i t b) (Fin.last _) u

theorem continuous_delta (i t : ℕ) : Continuous (delta (k := k) i t) :=
  continuous_pi fun b => (continuous_ent _ _).neg

theorem delta_one (i t : ℕ) : delta (k := k) i t 1 = 0 := by
  funext b
  have h0 : (1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _) = 0 :=
    Matrix.one_apply_ne (Fin.castSucc_ne_last _)
  show - ((1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _)) = 0
  rw [h0, neg_zero]

theorem eq_delta (i t : ℕ) (h u : Mir k ((i + 1) + (t + 1))) (hH : h ∈ HPG k (i + 1) (t + 1))
    (d : Fin (t + 1) → k) (e : h = dEmb k i t d * u) : d = delta i t u := by
  funext b
  have hp : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1)) := hH
  have hz := mem_parab_iff.1 hp true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_true_rowD, ePG_false_last] at hz
  have hv : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val =
      (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)) *
        ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val := by
    rw [e]; rfl
  have hz' : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val
      (rowD i t b) (Fin.last _) = 0 := hz
  rw [hv, add_mul, one_mul, Matrix.add_apply, rowD, colMat_mul_castSucc] at hz'
  have h1 : ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val (Fin.last _) (Fin.last _) = 1 :=
    ent_last_last u
  rw [h1, mul_one, Fin.append_right] at hz'
  show d b = - ent (rowD i t b) (Fin.last _) u
  exact eq_neg_of_add_eq_zero_right hz'

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

open Small in
theorem h_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (O : Set (Mir k ((i + 1) + t + 1))) (hO : O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1))),
    ∃ N ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) →
      ∀ (d : Fin (t + 1) → k) (x : Mir k ((i + 1) + t + 1)), x ∈ N →
        dEmb k i t d * wEl k i t = h * wEl k i t * x → h ∈ O := by
  intro k _ _ _ _ i t O hO
  let w : Mir k ((i + 1) + (t + 1)) := wEl k i t
  let f : Mir k ((i + 1) + (t + 1)) → Mir k ((i + 1) + (t + 1)) :=
    fun x => dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹)
  have hu : Continuous fun x : Mir k ((i + 1) + (t + 1)) => w * x⁻¹ * w⁻¹ :=
    (continuous_const.mul continuous_inv).mul continuous_const
  have hf : Continuous f :=
    ((continuous_dEmb i t).comp ((continuous_delta i t).comp hu)).mul hu
  have f1 : f 1 = 1 := by
    have e : w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹ = 1 := by group
    show dEmb k i t (delta i t (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹)) * (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹) = 1
    rw [e, delta_one, dEmb_zero, one_mul]
  refine ⟨f ⁻¹' O, hf.continuousAt.preimage_mem_nhds (by rw [f1]; exact hO), ?_⟩
  intro h hH d x hx e
  have e' : h = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by
    have e2 : dEmb k i t d * w = h * w * x := e
    calc h = (h * w * x) * x⁻¹ * w⁻¹ := by group
      _ = (dEmb k i t d * w) * x⁻¹ * w⁻¹ := by rw [e2]
      _ = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by group
  have hd := eq_delta i t h _ hH d e'
  have hfx : f x = h := by
    show dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹) = h
    rw [← hd, ← e']
  have : f x ∈ O := hx
  rwa [hfx] at this

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.DualQuot

theorem exists_subquotient_dual_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (S : IrrRep (GL (Fin n) k))
    (A' : Representation ℂ (GL (Fin n) k) V'), IsSmooth A' → ∀ B : S.V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ g w w', B (S.ρ g w) (A' g w') = ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B w w') → B ≠ 0 →
    ∃ Q : IrrRep (GL (Fin n) k), IsSubquotient Q.ρ A' ∧
      IrrGL.of Q.ρ Q.smooth Q.irr = (dualCl (IrrGL.of S.ρ S.smooth S.irr)).nu (s : ℂ) := by
  intro k _ _ _ _ n s V' _ _ S A' hA' B hB hB0
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hAd : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  have hχ : IsSmoothChar (absPow k (s : ℂ)) := isSmoothChar_absPow _
  have hχ' : IsSmoothChar (absPow k (-(s : ℂ))) := isSmoothChar_absPow _
  have hprod : ∀ g : GL (Fin n) k, ((detChar (Fin n) (absPow k (-(s : ℂ))) g : ℂˣ) : ℂ) *
      ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) = 1 := by
    intro g
    rw [absPow_neg, detChar_apply, detChar_apply, MonoidHom.inv_apply]
    simp
  have hT := isSmooth_twist hA' hχ'.detChar
  have hBT : ∀ g a b, B (S.ρ g a) (twist A' (detChar (Fin n) (absPow k (-(s : ℂ)))) g b) = B a b := by
    intro g a b
    rw [twist_apply, map_smul, hB, smul_eq_mul, ← mul_assoc, hprod, one_mul]
  let f := GlobalTheory.InvPairing.pairMap S.ρ hT B hBT
  have hc := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hAd S.ρ S.smooth S.irr
  have hsurj : Function.Surjective f := by
    let R : Subrepresentation (contra S.ρ) :=
      { toSubmodule := LinearMap.range f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          obtain ⟨w, rfl⟩ := hv
          refine ⟨twist A' (detChar (Fin n) (absPow k (-(s : ℂ)))) g w, ?_⟩
          have := LinearMap.congr_fun (f.isIntertwining' g) w
          simpa only [LinearMap.comp_apply] using this }
    rcases hc.eq_bot_or_eq_top R with hR | hR
    · exfalso
      refine hB0 (GlobalTheory.InvPairing.eq_zero_of_pairMap S.ρ hT B hBT fun b => ?_)
      have : f b ∈ R.toSubmodule := ⟨b, rfl⟩
      rw [hR] at this
      exact (Submodule.mem_bot ℂ).1 this
    · intro l
      have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩
  let F : A'.IntertwiningMap (twist (contra S.ρ) (detChar (Fin n) (absPow k (s : ℂ)))) :=
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun g => by
        refine LinearMap.ext fun w => ?_
        have h := LinearMap.congr_fun (f.isIntertwining' g) w
        simp only [LinearMap.comp_apply, twist_apply, map_smul] at h ⊢
        rw [← h, smul_smul, mul_comm, hprod, one_smul] }
  refine ⟨⟨_, twist (contra S.ρ) (detChar (Fin n) (absPow k (s : ℂ))),
    isSmooth_twist (isSmooth_contra _) hχ.detChar, isIrreducible_twist hc _⟩,
    IsSubquotient.of_surjective F hsurj, ?_⟩
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hAd, IrrGL.nu, IrrGL.tw_of]
  exact IrrGL.of_eq_of.2
    ⟨(twistEquiv (GlobalTheory.ContraRefl.contraEquiv (IrrGL.equivOf S.ρ S.smooth S.irr)) _).symm⟩

end GlobalTheory.CompanionTheory.DualQuot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueCardEqAbsNorm
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ResCardAbsNorm

theorem resCard_completion_eq_absNorm : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (resCard (w.adicCompletion E) : ℝ) = (Ideal.absNorm w.asIdeal : ℝ) := by
  intro E _ _ w
  exact_mod_cast GlobalTheory.LFun.SatBoundGL.resCard_completion w

end GlobalTheory.CompanionTheory.ResCardAbsNorm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPairStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_generic_of_jacquet_nu_pair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → GlobalTheory.BZSeg.NuPair k → GlobalTheory.BZSeg.LSegGeneric k := by
  first | exact @GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair | exact GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair | (intros; apply GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrderFgIdealProductStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_order_fg_ideal_product : ∀ {k R : Type} [Field k] [CommRing R] (O : ValuationSubring k) (φ : R ≃+* k × k) (𝔬 : Subring R), (∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) → ∀ I : Submodule 𝔬 R, I.FG → ∃ α β : k, ∀ r, r ∈ I ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal | exact GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal | (intros; apply GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal <;> assumption)
end

