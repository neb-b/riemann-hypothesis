module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0387
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemisimpleClassificationReal
section
open Finset
open CompanionTheory.D.LK (Pos)
open CompanionTheory.RgExh.U (adC)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

noncomputable section

namespace GlobalTheory.CompanionTheory.SemiClass

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annL_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    annL l x B = if l ∈ B then 0 else sgL l B • x (insert l B) := rfl

theorem creL_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creL l x B = if l ∈ B then sgL l B • x (B.erase l) else 0 := rfl

theorem sgL_erase (l : Lt n) (B : Finset (Lt n)) : sgL l (B.erase l) = sgL l B := by
  unfold sgL
  congr 2
  ext m
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hm⟩, hk⟩
    exact ⟨hm, hk⟩
  · rintro ⟨hm, hk⟩
    refine ⟨⟨?_, hm⟩, hk⟩
    rintro rfl
    exact lt_irrefl _ hk

theorem sgL_sq (l : Lt n) (B : Finset (Lt n)) : sgL l B * sgL l B = 1 := by
  unfold sgL; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem creL_annL (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creL l (annL l x) B = if l ∈ B then x B else 0 := by
  rw [creL_app]
  split_ifs with hB
  · rw [annL_app, if_neg (by simp), Finset.insert_erase hB, sgL_erase, smul_smul, sgL_sq, one_smul]
  · rfl

theorem mem_omU {lev : Fin n → ℕ} {l : Lt n} : l ∈ omU lev ↔ l.1 = false ∧ lev l.2.1.1 < lev l.2.1.2 := by
  simp [omU]

omit [Module ℂ V] in
theorem top_app (lev : Fin n → ℕ) (x : V) (B : Finset (Lt n)) :
    (Pi.single (omU lev) x : Cq n V) B = if B = omU lev then x else 0 := by
  rw [Pi.single_apply]

theorem top_smul (lev : Fin n → ℕ) (c : ℂ) (x : V) :
    (Pi.single (omU lev) (c • x) : Cq n V) = c • (Pi.single (omU lev) x : Cq n V) := by
  ext B
  simp only [Pi.smul_apply, top_app]
  split_ifs <;> simp

omit [Module ℂ V] in
theorem top_zero (lev : Fin n → ℕ) : (Pi.single (omU lev) (0 : V) : Cq n V) = 0 := by
  exact Pi.single_zero _

theorem liftL_top (lev : Fin n → ℕ) (T : Module.End ℂ V) (x : V) :
    (liftL n T : Module.End ℂ (Cq n V)) (Pi.single (omU lev) x) = Pi.single (omU lev) (T x) := by
  ext B
  simp only [liftL, LinearMap.compLeft_apply, Function.comp_apply, top_app]
  split_ifs <;> simp

theorem annL_top_of_notMem {lev : Fin n → ℕ} {l : Lt n} (x : V) (h : l ∉ omU lev) :
    annL l (Pi.single (omU lev) x : Cq n V) = 0 := by
  ext B
  rw [annL_app, top_app]
  split_ifs with h1 h2
  · rfl
  · exact absurd (by rw [← h2]; exact Finset.mem_insert_self l B) h
  · simp

theorem creL_annL_top_same {lev : Fin n → ℕ} {l : Lt n} (x : V) (h : l ∈ omU lev) :
    creL l (annL l (Pi.single (omU lev) x : Cq n V)) = Pi.single (omU lev) x := by
  ext B
  rw [creL_annL]
  split_ifs with hB
  · rfl
  · rw [top_app, if_neg (fun e => hB (by rw [e]; exact h))]

theorem creL_annL_top_ne {lev : Fin n → ℕ} {l m : Lt n} (x : V) (hm : m ∈ omU lev) (hne : m ≠ l) :
    creL m (annL l (Pi.single (omU lev) x : Cq n V)) = 0 := by
  ext B
  rw [creL_app]
  split_ifs with hB
  · rw [annL_app]
    split_ifs with hl
    · simp
    · rw [top_app, if_neg]
      · simp
      · intro e
        have hmem : m ∈ insert l (B.erase m) := by
          rw [e]
          exact hm
        simp [hne] at hmem
  · rfl

theorem mem_omU_of_adCL_ne {lev : Fin n → ℕ} {p q : Fin n} {l k : Lt n} (hpq : lev p = lev q)
    (hl : l ∈ omU lev) (h : adCL false p q l k ≠ 0) : k ∈ omU lev := by
  rw [mem_omU] at hl ⊢
  obtain ⟨hl1, hl2⟩ := hl
  have case1 : (q = l.2.1.1 ∧ k.1 = xor false l.1 ∧ k.2.1 = (p, l.2.1.2)) →
      k.1 = false ∧ lev k.2.1.1 < lev k.2.1.2 := by
    rintro ⟨e1, e2, e3⟩
    refine ⟨by simp [e2, hl1], ?_⟩
    calc lev k.2.1.1 = lev p := by rw [e3]
      _ = lev q := hpq
      _ = lev l.2.1.1 := by rw [e1]
      _ < lev l.2.1.2 := hl2
      _ = lev k.2.1.2 := by rw [e3]
  have case2 : (l.2.1.2 = p ∧ k.1 = xor false l.1 ∧ k.2.1 = (l.2.1.1, q)) →
      k.1 = false ∧ lev k.2.1.1 < lev k.2.1.2 := by
    rintro ⟨e1, e2, e3⟩
    refine ⟨by simp [e2, hl1], ?_⟩
    calc lev k.2.1.1 = lev l.2.1.1 := by rw [e3]
      _ < lev l.2.1.2 := hl2
      _ = lev p := by rw [e1]
      _ = lev q := hpq
      _ = lev k.2.1.2 := by rw [e3]
  unfold adCL at h
  split_ifs at h with c1 c2 c3
  · exact case1 c1
  · exact case1 c1
  · exact case2 c3
  · simp at h

theorem adCL_self (p q : Fin n) (i : Pos n) :
    adCL false p q ((false, i) : Lt n) (false, i) = adC p q i i := by
  simp [adCL, adC]

theorem adLL_top {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) (x : V) :
    adLL lev false p q (Pi.single (omU lev) x : Cq n V) =
      (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p q i i else 0) • (Pi.single (omU lev) x : Cq n V) := by
  have key : ∀ l k : Lt n, ((if inUU lev l then adCL false p q l k • (creL k * annL l) else 0 :
      Module.End ℂ (Cq n V)) (Pi.single (omU lev) x)) =
      if k = l then (if l ∈ omU lev then adCL false p q l l • (Pi.single (omU lev) x : Cq n V) else 0) else 0 := by
    intro l k
    by_cases hl : l ∈ omU lev
    · have hin : inUU lev l := (mem_omU.1 hl).2
      rw [if_pos hin, LinearMap.smul_apply, Module.End.mul_apply]
      by_cases hk : k = l
      · subst hk
        rw [creL_annL_top_same x hl, if_pos rfl, if_pos hl]
      · rw [if_neg hk]
        by_cases hkm : k ∈ omU lev
        · rw [creL_annL_top_ne x hkm hk, smul_zero]
        · have h0 : adCL false p q l k = 0 := by
            by_contra hne
            exact hkm (mem_omU_of_adCL_ne hpq hl hne)
          rw [h0, zero_smul]
    · have hr : (if k = l then (if l ∈ omU lev then adCL false p q l l • (Pi.single (omU lev) x : Cq n V) else 0)
          else 0) = 0 := by
        split_ifs <;> rfl
      rw [hr]
      split_ifs
      · rw [LinearMap.smul_apply, Module.End.mul_apply, annL_top_of_notMem x hl, map_zero, smul_zero]
      · rfl
  have hsum : (∑ l ∈ omU lev, adCL false p q l l) =
      ∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p q i i else 0 := by
    rw [omU, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
    simp [adCL_self]
  unfold adLL
  simp only [LinearMap.sum_apply, key, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← hsum, Finset.sum_smul, ← Finset.sum_filter]
  congr 1
  ext l
  simp

theorem leviFamilyOne_add_leviFamilyTwo (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a c : Fin n) :
    firstLeviFamily lev E1 E2 a c + secondLeviFamily lev E1 E2 a c = evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, a, c)) := by
  simp only [firstLeviFamily, secondLeviFamily, ← smul_add]
  rw [add_add_sub_cancel, ← two_smul ℂ, smul_smul]
  norm_num

end GlobalTheory.CompanionTheory.SemiClass

namespace GlobalTheory.CompanionTheory.SemiClass

open GlobalTheory.CompanionTheory.PairMult.TopK (K_act sum_diag adC_diag_ne)

theorem semiCls : SemiCls := by
  intro n lam _ lev hl V _ _ E1 E2 hA v hv a c hac
  rw [leviFamilyOne_add_leviFamilyTwo]
  unfold evLc
  rw [FreeAlgebra.lift_ι_apply]
  dsimp only
  rw [if_pos hac]
  simp only [Bool.false_eq_true, if_false, ite_false]
  rw [LinearMap.add_apply, liftL_top, adLL_top hac]
  have hk : kA E1 E2 a c v = kF E1 E2 a c v := rfl
  rw [hk, GlobalTheory.CompanionTheory.PairMult.TopK.K_act hl hA hv hac]
  by_cases h : a = c
  · subst h
    rw [if_pos (rfl : a = a), if_pos (rfl : a = a), GlobalTheory.CompanionTheory.PairMult.TopK.sum_diag hl.1, top_smul, ← add_smul]
    congr 1
    push_cast
    ring
  · rw [if_neg h, if_neg h, top_zero, zero_add]
    have h0 : (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC a c i i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [GlobalTheory.CompanionTheory.PairMult.TopK.adC_diag_ne h i]
      simp
    rw [h0, zero_smul]

end GlobalTheory.CompanionTheory.SemiClass
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearOrbitFinite
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.ShearOrbit

variable {k : Type} [Field k]

theorem shear_mul_inv (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    (1 + vecMulVec (eLast k n) b) * (1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (eLast k n) b) = 1 := by
  have hd : b ⬝ᵥ GlobalTheory.BZMir.eLast k n = b (Fin.last n) := by
    simp [GlobalTheory.BZMir.eLast, dotProduct_single]
  have hM : vecMulVec (GlobalTheory.BZMir.eLast k n) b * vecMulVec (GlobalTheory.BZMir.eLast k n) b =
      b (Fin.last n) • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    rw [vecMulVec_mul_vecMulVec, hd]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hc : (1 + b (Fin.last n))⁻¹ + (1 + b (Fin.last n))⁻¹ * b (Fin.last n) = 1 := by
    rw [← mul_one_add]
    exact inv_mul_cancel₀ hb
  rw [mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hM, smul_add, smul_smul, ← add_smul, hc,
    one_smul, add_sub_cancel_right]

theorem shearGL_val (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (eLast k n) b := by
  have h := GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_mul_inv n b hb
  have hu : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) :=
    ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩
  rw [GlobalTheory.CompanionTheory.MirPair.shearGL, dite_eq_left hu]
  exact hu.unit_spec

theorem shearGL_inv_val (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    (((shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (eLast k n) b :=
  Units.inv_eq_of_mul_eq_one_right (by rw [shearGL_val n b hb]; exact shear_mul_inv n b hb)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_add_ne_zero_of_mem_box (n : ℕ) {r : kˣ} (hr : valuation k (r : k) < 1) {b : Fin (n + 1) → k}
    (hb : b ∈ box (n + 1) r) : 1 + b (Fin.last n) ≠ 0 := by
  intro h
  have h1 : valuation k (b (Fin.last n)) ≤ valuation k (r : k) := hb (Fin.last n)
  have h2 : b (Fin.last n) = -1 := by linear_combination h
  rw [h2, Valuation.map_neg, map_one] at h1
  exact absurd hr (not_lt.mpr h1)

theorem continuous_shearGL (n : ℕ) {r : kˣ} (hr : valuation k (r : k) < 1) :
    Continuous fun b : (box (n + 1) r : Set (Fin (n + 1) → k)) => shearGL n b.1 := by
  have hne : ∀ b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)), 1 + b.1 (Fin.last n) ≠ 0 :=
    fun b => GlobalTheory.CompanionTheory.MirPair.ShearOrbit.one_add_ne_zero_of_mem_box n hr b.2
  have hv : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      vecMulVec (GlobalTheory.BZMir.eLast k n) b.1 :=
    continuous_matrix fun i j => by
      simp only [vecMulVec_apply]
      exact continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_const.add hv).congr fun b => (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shearGL_val n b.1 (hne b)).symm
  · have hinv : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
        (1 + b.1 (Fin.last n))⁻¹ :=
      (continuous_const.add ((continuous_apply _).comp continuous_subtype_val)).inv₀ hne
    exact (continuous_const.sub (hinv.smul hv)).congr fun b => (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shearGL_inv_val n b.1 (hne b)).symm


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_levi (m : ℕ) : Continuous (levi k m) := by
  have hmat : Continuous (GlobalTheory.BZMir.glEmbHom k m) := by
    apply continuous_matrix
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [GlobalTheory.BZMir.glEmbHom, GlobalTheory.BZMir.glEmbMat] <;>
      first
        | exact continuous_const
        | exact continuous_id.matrix_elem _ _
        | fun_prop
  have hGL : Continuous (GlobalTheory.BZMir.glEmb k m) := Continuous.units_map _ hmat
  exact continuous_induced_rng.2 hGL

theorem isOpen_orbit_fiber {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v w : V) :
    IsOpen {p : Mir k (n + 1) | T p v = w} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hS : IsOpen {g : GlobalTheory.BZMir.Mir k (n + 1) | T g v = v} := hT v
  have hcont : Continuous fun g : GlobalTheory.BZMir.Mir k (n + 1) => p⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GlobalTheory.BZMir.Mir k (n + 1) => p⁻¹ * g) ⁻¹' {g | T g v = v} ∈ 𝓝 p := by
    apply hcont.continuousAt.preimage_mem_nhds
    apply hS.mem_nhds
    simp
  filter_upwards [hmem] with g hg
  have hg' : T (p⁻¹ * g) v = v := hg
  have hsplit : T g = T p * T (p⁻¹ * g) := by
    rw [← map_mul, mul_inv_cancel_left]
  show T g v = w
  rw [hsplit, Module.End.mul_apply, hg']
  exact hp

theorem shear_orbit_finite {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v : V) (r : kˣ)
    (hr : valuation k (r : k) < 1) :
    ((fun b => T (levi k (n + 1) (shearGL n b)) v) '' (box (n + 1) r : Set (Fin (n + 1) → k))).Finite := by
  haveI : CompactSpace (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box (n + 1) r)
  have hc : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b.1) :=
    (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_levi (n + 1)).comp (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_shearGL n hr)
  have hlc : IsLocallyConstant fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      T (GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b.1)) v := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro w
    exact (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.isOpen_orbit_fiber T hT v w).preimage hc
  rw [Set.image_eq_range]
  exact hlc.range_finite

end GlobalTheory.CompanionTheory.MirPair.ShearOrbit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesBoxMembership
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.ShearLat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dotProduct_eLast {n : ℕ} (b : Fin (n + 1) → k) : b ⬝ᵥ eLast k n = b (Fin.last n) := by
  simp [eLast, dotProduct_single]

theorem isUnit_one_add {n : ℕ} (b : Fin (n + 1) → k) (h : 1 + b (Fin.last n) ≠ 0) :
    IsUnit (1 + vecMulVec (eLast k n) b) := by
  rw [Matrix.isUnit_iff_isUnit_det, vecMulVec_eq (ι := Unit),
    det_one_add_replicateCol_mul_replicateRow, dotProduct_eLast]
  exact h.isUnit

theorem shearGL_mulVec {n : ℕ} (b : Fin (n + 1) → k) (h : 1 + b (Fin.last n) ≠ 0)
    (x : Fin (n + 1) → k) :
    ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x =
      x + (b ⬝ᵥ x) • eLast k n := by
  have e : ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (eLast k n) b := by
    unfold shearGL
    rw [dite_eq_left (isUnit_one_add b h)]
    rfl
  rw [e, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem dotProduct_shear {n : ℕ} (b x : Fin (n + 1) → k) :
    b ⬝ᵥ (x + (b ⬝ᵥ x) • eLast k n) = (1 + b (Fin.last n)) * (b ⬝ᵥ x) := by
  rw [dotProduct_add, dotProduct_smul, dotProduct_eLast, smul_eq_mul]
  ring

theorem exists_bound {n : ℕ} (g : GL (Fin (n + 1)) k) :
    ∃ C : kˣ, 1 ≤ valuation k (C : k) ∧
      (∀ i, valuation k (((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i) ≤ valuation k (C : k)) ∧
      ∀ i j, valuation k (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j) ≤
        valuation k (C : k) := by
  let f : Option (Fin (n + 1) ⊕ Fin (n + 1) × Fin (n + 1)) → k := fun o =>
    match o with
    | none => 1
    | some (.inl i) => ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i
    | some (.inr p) => ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p.1 p.2
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun o => valuation k (f o)
  have h1 : 1 ≤ valuation k (f i₀) := by simpa [f] using hi₀ none
  have hne : f i₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact absurd h1 (by simp)
  exact ⟨Units.mk0 _ hne, h1, fun i => hi₀ (some (.inl i)), fun i j => hi₀ (some (.inr (i, j)))⟩

theorem mul_mem_cball {a u : k} {p C t : kˣ} (hp : valuation k (p : k) ≤ 1)
    (ha : a ∈ cball (p * C⁻¹ * t)) (hu : valuation k u ≤ valuation k (C : k)) : a * u ∈ cball t := by
  have ha' : valuation k a ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) := ha
  show valuation k (a * u) ≤ valuation k (t : k)
  calc valuation k (a * u) = valuation k a * valuation k u := map_mul _ _ _
    _ ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) * valuation k (C : k) := mul_le_mul' ha' hu
    _ = valuation k (p : k) * valuation k (t : k) := by
        rw [← map_mul, ← map_mul]
        congr 1
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
    _ ≤ valuation k (t : k) := mul_le_of_le_one_left' hp

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (g : GL (Fin (n + 1)) k), ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, ∀ (t : kˣ) (x : Fin (n + 1) → k), ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) ∈ box (n + 1) t ↔ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t) := by
  intro k _ _ _ _ n g
  obtain ⟨C, hC1, hu, hH⟩ := exists_bound g
  obtain ⟨p₀, hp0, hp1⟩ : ∃ p : k, p ≠ 0 ∧ valuation k p < 1 := Valuation.IsNontrivial.exists_lt_one
  obtain ⟨p, rfl⟩ : ∃ p : kˣ, (p : k) = p₀ := ⟨Units.mk0 _ hp0, rfl⟩
  have hCi : valuation k ((C⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_le_one_of_one_le₀ hC1
  have hr1 : valuation k ((p * C⁻¹ * C⁻¹ : kˣ) : k) < 1 := by
    simp only [Units.val_mul, map_mul]
    exact lt_of_le_of_lt ((mul_le_of_le_one_right' hCi).trans (mul_le_of_le_one_right' hCi)) hp1
  refine ⟨p * C⁻¹ * C⁻¹, hr1, fun b hb t x => ?_⟩
  have hlast : valuation k (b (Fin.last n)) < 1 := lt_of_le_of_lt (hb (Fin.last n)) hr1
  have hone : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hlast
  have hne : 1 + b (Fin.last n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hone
    exact zero_ne_one hone
  rw [shearGL_mulVec b hne x]
  have hGS : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (x + (b ⬝ᵥ x) • eLast k n) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x +
        (b ⬝ᵥ x) • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) := by
    rw [mulVec_add, mulVec_smul]
  have hd : ∀ z : Fin (n + 1) → k, b ⬝ᵥ z =
      (b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ⬝ᵥ
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z) := by
    intro z
    rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have hw : b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈
      box (n + 1) (p * C⁻¹) := by
    intro j
    change ∑ i, b i * ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j ∈ cball (p * C⁻¹)
    refine Finset.sum_induction _ (· ∈ cball (p * C⁻¹)) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
    have h1 : valuation k (b i) ≤ valuation k ((p * C⁻¹ * C⁻¹ : kˣ) : k) := hb i
    show valuation k (b i * _) ≤ valuation k ((p * C⁻¹ : kˣ) : k)
    rw [map_mul]
    refine (mul_le_mul' h1 (hH i j)).trans (le_of_eq ?_)
    rw [← map_mul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hdot : ∀ y ∈ box (n + 1) t,
      (b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ⬝ᵥ y ∈
        cball (p * C⁻¹ * t) := by
    intro y hy
    refine dotProduct_mem_cball (s := t) ?_ hy
    rwa [mul_inv_cancel_right]
  have hp : valuation k (p : k) ≤ 1 := hp1.le
  constructor
  · intro h i
    have h2 : (1 + b (Fin.last n)) * (b ⬝ᵥ x) ∈ cball (p * C⁻¹ * t) := by
      rw [← dotProduct_shear, hd (x + (b ⬝ᵥ x) • eLast k n)]
      exact hdot _ h
    have h3 : b ⬝ᵥ x ∈ cball (p * C⁻¹ * t) := by
      have h2' : valuation k ((1 + b (Fin.last n)) * (b ⬝ᵥ x)) ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) := h2
      rw [map_mul, hone, one_mul] at h2'
      exact h2'
    rw [hGS] at h
    have e : ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) i =
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x +
          (b ⬝ᵥ x) • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n)) i +
        -((b ⬝ᵥ x) * ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i) := by
      simp
    rw [e]
    exact add_mem_cball (h i) (neg_mem_cball (mul_mem_cball hp h3 (hu i)))
  · intro h i
    have h3 : b ⬝ᵥ x ∈ cball (p * C⁻¹ * t) := by
      rw [hd x]
      exact hdot _ h
    rw [hGS]
    exact add_mem_cball (h i) (mul_mem_cball hp h3 (hu i))

end GlobalTheory.CompanionTheory.MirPair.ShearLat
end

