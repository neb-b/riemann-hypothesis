module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInvLower
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0019
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProof
section
noncomputable section

namespace GlobalTheory.TypeAsm.NFEx

section Mat
variable {K : Type} [Field K] [StarRing K]


open Classical in
noncomputable def cb (b : K × ℕ) : Kˣ × ℕ+ :=
  if h : b.1 ≠ 0 ∧ 1 ≤ b.2 then (Units.mk0 (star b.1) (star_ne_zero.2 h.1), ⟨b.2, h.2⟩) else (1, 1)

theorem entry_cb (bs : List (K × ℕ)) (hb : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (a c : ℕ) :
    Formalism.MainNotions.S.Loc.ptEntryL (bs.map cb) a c = star (Formalism.MainNotions.S.ptEntry bs a c) := by
  induction bs generalizing a c with
  | nil => simp [Formalism.MainNotions.S.Loc.ptEntryL, Formalism.MainNotions.S.ptEntry]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have h := hb (t, s) (by simp)
    have ih' := ih (fun b hb' => hb b (by simp [hb']))
    simp only [List.map_cons, cb, dif_pos h, Formalism.MainNotions.S.Loc.ptEntryL, Formalism.MainNotions.S.ptEntry, PNat.mk_coe, Units.val_mk0]
    simp only [ih', apply_ite star, star_zero]
    exact if_congr Iff.rfl (if_congr Iff.rfl rfl rfl) (if_congr Iff.rfl rfl rfl)

theorem size_cb (bs : List (K × ℕ)) (hb : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) :
    ((bs.map cb).map (fun b => (b.2 : ℕ))).sum = (bs.map Prod.snd).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have h := hb b (by simp)
    have ih' := ih (fun b hb' => hb b (by simp [hb']))
    simp only [List.map_cons, List.sum_cons, cb, dif_pos h, PNat.mk_coe, ih']

end Mat
end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
section Mat2
variable {K : Type} [Field K] [StarRing K]

noncomputable def toPt {n : ℕ} (p : Formalism.MainNotions.S.Point K n) : Formalism.MainNotions.S.Loc.Pt K n where
  blocks := p.1.map cb
  size := (size_cb p.1 p.2.1).trans p.2.2

theorem toPt_mat {n : ℕ} (p : Formalism.MainNotions.S.Point K n) (a b : Fin n) :
    (toPt p).mat a b = star (Formalism.MainNotions.S.ptMat p a b) :=
  entry_cb p.1 p.2.1 a.val b.val

def sgnR (r : ℕ) {n : ℕ} (b : Fin n) : ℤˣ := (-1) ^ (r - b.val)

theorem decomp {n r : ℕ} (Z : Matrix (Fin n) (Fin n) K) (p : Formalism.MainNotions.S.Point K n)
    (h : Formalism.MainNotions.S.IsInCell (fun a b => (-1 : K) ^ (r - b.val) * Z a b) p) :
    ∃ A B : Matrix (Fin n) (Fin n) K, (∀ a b, a < b → A a b = 0 ∧ B b a = 0) ∧ (∀ a, A a a = 1 ∧ B a a = 1) ∧
      Z.map star = A * Matrix.of (fun a b => (toPt p).mat a b * (((sgnR r b : ℤˣ) : ℤ) : K)) * B := by
  obtain ⟨L, U, hL, hU, hZ⟩ := h
  set s : Fin n → K := fun b => (-1 : K) ^ (r - b.val) with hs_def
  have hs : ∀ b, s b * s b = 1 := fun b => by
    simp only [hs_def, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hss : ∀ b, star (s b) = s b := fun b => by simp [hs_def]
  have hsg : ∀ b : Fin n, (((sgnR r b : ℤˣ) : ℤ) : K) = s b := fun b => by
    simp [sgnR, hs_def]
  have hZ' : Z = L * Formalism.MainNotions.S.ptMat p * U * Matrix.diagonal s := by
    ext a b
    rw [Matrix.mul_diagonal, ← hZ]
    show Z a b = s b * Z a b * s b
    rw [mul_comm (s b), mul_assoc, hs, mul_one]
  have hD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hs]
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  have hDs : (Matrix.diagonal s).map star = Matrix.diagonal s := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hss]
    · simp [Matrix.diagonal_apply_ne _ hab]
  refine ⟨L.map star, Matrix.diagonal s * U.map star * Matrix.diagonal s, fun a b hab => ⟨?_, ?_⟩, fun a => ⟨?_, ?_⟩, ?_⟩
  · simp [(hL a b).1 hab]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [(hU b a).1 hab]
  · simp [(hL a a).2 rfl]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [(hU a a).2 rfl, hs]
  · have hP : Matrix.of (fun a b => (toPt p).mat a b * (((sgnR r b : ℤˣ) : ℤ) : K)) =
        (Formalism.MainNotions.S.ptMat p).map star * Matrix.diagonal s := by
      ext a b
      rw [Matrix.mul_diagonal, Matrix.of_apply, toPt_mat, hsg, Matrix.map_apply]
    have hmap : ∀ M N : Matrix (Fin n) (Fin n) K, (M * N).map star = M.map star * N.map star := fun M N =>
      (Matrix.map_mul (f := starRingEnd K) (L := M) (M := N))
    rw [hP, hZ', hmap, hmap, hmap, hDs]
    calc L.map star * (Formalism.MainNotions.S.ptMat p).map star * U.map star * Matrix.diagonal s
        = L.map star * (Formalism.MainNotions.S.ptMat p).map star * (Matrix.diagonal s * Matrix.diagonal s) * U.map star *
            Matrix.diagonal s := by rw [hD, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

end Mat2
end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt
  Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem zhat_eq {D : D7} {X : HidaSetting D} {Y : Full X} {u : D.what₂.Word} (t : GTu Y u)
    (j : ℕ) (hj : j ≤ D.R.rS + 1) :
    (Formalism.HermitianLatticeCounting.S6.Zhat (F0 X u) (Ft t)).submatrix (Fin.castLE hj) (Fin.castLE hj) =
      ((Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl).submatrix (Fin.castLE hj) (Fin.castLE hj)).map (star : D.host.E → D.host.E) := by
  refine Matrix.ext fun a b => ?_
  exact a_herm (S := VS D) ((F0 X u).e (Fin.castLE hj a)) ((Ft t).e (Fin.castLE hj b))

end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt
  Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nfExC (hHost : HostC) : NFExC := by
  intro D large₂ X Y u hStd t ht
  obtain ⟨hr, hG, -⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  have hjT := index_eq_normalForm t hN
  have hH := hHost D large₂ hStd
  obtain ⟨hrel, -⟩ := relRepC D X Y u u t hr hG
  have hTu := tie_Tu_pos D u
  have hj' : j ≤ D.R.rS + 1 := hj.trans (Nat.le_succ _)
  have geo := cell_geom D.host.F D.host.E (hS D) D.R.rS _ _ (lf D (X.Fu u)).fl (frq X t.rep).fl (tie_trace D.sp.cm)
    (tie_aniso D _ hTu (lf D (X.Fu u))) (tie_aniso D _ hTu (frq X t.rep)) hrel
  have hDG : Formalism.MainNotions.S.Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j ≠ 0 := by
    exact (nf_Dl (lf D (X.Fu u)).fl (frq X t.rep).fl
      (fixedFlag_level_ne_zero D u) (nf_T_ne D u) j hj').trans_ne (star_ne_zero.2 hN.2.2.1)
  obtain ⟨p, hp⟩ := cell_of_matRel cell_inv cell_sign cell_bruhat cell_mono cell_point hj'
    ((Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl).submatrix (Fin.castLE hj') (Fin.castLE hj'))
    (by rw [← tie_Dl_eq']; exact hDG) (geo j hj' (Or.inl ⟨hj, hDG⟩))
  obtain ⟨A, B, h0, h1, hZ⟩ := decomp _ p hp
  obtain ⟨N, hNj, -, hNT, hN𝔡, hF, hF'⟩ := GlobalTheory.DegCnt.RatNormal.exists_nf D.host.E (VS D).V (HV D) hH.1 D.R.rS
    (F0 X u) (Ft t) j hj c (Tu D u) (dI D) (toPt p) (fun b => sgnR D.R.rS b) A B hN rfl rfl
    (fun σ => nf_pos _ _ (p_posX D _ hTu _) σ) hH.2.2.2.2.2.2.2.1 hH.2.2.2.2.2.2.2.2.1 h0 h1
    (by rw [zhat_eq t j hj']; exact hZ)
  exact ⟨N, ⟨hN𝔡, hF, hF'⟩, hNj.trans hjT.symm, hNT⟩

end GlobalTheory.TypeAsm.NFEx

theorem GlobalTheory.TypeAsm.nfExC_holds : GlobalTheory.TypeAsm.NFExC := GlobalTheory.TypeAsm.NFEx.nfExC _root_.GlobalTheory.TypeAsm.hostC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMulEquivCongruenceTopologyAdelic
section
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.CongTop.Swap

section Abstract

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem bc_mem_UJ (φ : A →+* B) {σ : A →+* A} {τ : B →+* B} (h : ∀ x, φ (σ x) = τ (φ x))
    {J : Matrix n n A} {J' : Matrix n n B} (hJ : J.map φ = J') {g : GL n A} (hg : g ∈ Formalism.UG.UJ σ J) :
    Formalism.UG.bc φ g ∈ Formalism.UG.UJ τ J' := by
  have hg' : Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  have key : Formalism.UG.cT τ ((g : Matrix n n A).map φ) = (Formalism.UG.cT σ (g : Matrix n n A)).map φ := by
    unfold Formalism.UG.cT
    ext i j
    simp [h]
  subst hJ
  change Formalism.UG.cT τ ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ = J.map φ
  rw [key, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end Abstract

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (topTens)
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology

theorem mem_lamAf_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] Af F) :
    y ∈ lamAf (F := F) L ↔ (fun i => Algebra.TensorProduct.comm F E (Af F) (y i)) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  have hcc : ∀ z : E ⊗[F] Af F,
      Algebra.TensorProduct.comm F (Af F) E (Algebra.TensorProduct.comm F E (Af F) z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp [ha, hb]
  have key := GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf F E n L
    (fun i => Algebra.TensorProduct.comm F E (Af F) (y i))
  simp only [hcc] at key
  exact key.symm

private theorem tensorComm_sigR_eq_sigR_tensorComm (I : AutInst) (a : I.E ⊗[I.F] Af I.F) :
    Algebra.TensorProduct.comm I.F I.E (Af I.F) (Formalism.UG.sigR I.cm.sig (Af I.F) a) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig (Algebra.TensorProduct.comm I.F I.E (Af I.F) a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem J_map_inclE_comm (I : AutInst) :
    (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Af I.F) I.J := by
  ext i j
  simp [Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

private theorem tensorComm_mulVec_map_eq (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    (M.map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) *ᵥ
        (fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F) (v i)) =
      fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F) ((M *ᵥ v) i) := by
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

private theorem adLat_hat_eq_latHat (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {m : ℕ}
    (L : Set (Fin m → E)) : GlobalTheory.AdLat.hat F L = Formalism.MainNotions.StandardLattice.latHat F E L := by
  unfold GlobalTheory.AdLat.hat Formalism.MainNotions.StandardLattice.latHat
  congr 1

private theorem stabilizes_lamAf_iff (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    (∀ y, y ∈ lamAf (F := I.F) I.L ↔ M *ᵥ y ∈ lamAf (F := I.F) I.L) ↔
      GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E))
        (M.map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := by
  constructor
  · intro h z
    have h1 := h (fun i => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (z i))
    have e1 : (fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F)
        ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (z i))) = z :=
      funext fun i => AlgEquiv.apply_symm_apply _ _
    have e2 : M.map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) *ᵥ z =
        fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F)
          ((M *ᵥ fun i => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (z i)) i) := by
      rw [← tensorComm_mulVec_map_eq I M]
      congr 1
      exact e1.symm
    rw [mem_lamAf_iff, mem_lamAf_iff, e1, ← e2] at h1
    exact h1
  · intro h y
    rw [mem_lamAf_iff, mem_lamAf_iff, ← tensorComm_mulVec_map_eq I M]
    exact h _

theorem exists_continuousMulEquiv_adelic : ∀ (I : AutInst), ∃ e : I.Gf ≃ₜ* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J, (∀ x, ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J (e x) : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) = (I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) ∧ ∀ x, x ∈ I.Kset ↔ GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E)) ((I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := by
  intro I
  classical
  obtain ⟨hT2, -, -, -, hKo, ⟨K0, hK0⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hone : (1 : I.Gf) ∈ I.Kset := by
    have h1 : (1 : I.Gf) ∈ (K0 : Set I.Gf) := K0.one_mem
    rwa [hK0] at h1
  haveI : IsModuleTopology (Af I.F) (Af I.F ⊗[I.F] I.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af I.F ⊗[I.F] I.E) := IsModuleTopology.isTopologicalRing (Af I.F) _
  haveI : IsTopologicalGroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J) :=
    inferInstanceAs (IsTopologicalGroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J))
  obtain ⟨KH, hKH, hKHo, hKHc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab I.F I.E I.cm.sig I.n I.J I.L
    I.L_fg I.L_span
  let φ : I.E ⊗[I.F] Af I.F →+* Af I.F ⊗[I.F] I.E :=
    (Algebra.TensorProduct.comm I.F I.E (Af I.F)).toRingEquiv.toRingHom
  let ψ : Af I.F ⊗[I.F] I.E →+* I.E ⊗[I.F] Af I.F :=
    (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm.toRingEquiv.toRingHom
  have hψφ : ∀ a, ψ (φ a) = a := fun a => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm_apply_apply a
  have hφψ : ∀ b, φ (ψ b) = b := fun b => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).apply_symm_apply b
  have hsig : ∀ a, φ (Formalism.UG.sigR I.cm.sig (Af I.F) a) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig (φ a) := fun a => tensorComm_sigR_eq_sigR_tensorComm I a
  have hsig' : ∀ b, ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig b) =
      Formalism.UG.sigR I.cm.sig (Af I.F) (ψ b) := by
    intro b
    have h2 := congrArg ψ (hsig (ψ b))
    rw [hψφ, hφψ] at h2
    exact h2.symm
  have hJ : (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map φ = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Af I.F) I.J :=
    J_map_inclE_comm I
  have hJ' : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Af I.F) I.J).map ψ = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    rw [← hJ, Matrix.map_map]
    ext i j
    simp only [Matrix.map_apply, Function.comp_apply, hψφ]
  have hmem : ∀ x : I.Gf, Formalism.UG.bc φ (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J := fun x => bc_mem_UJ φ hsig hJ x.2
  have hmem' : ∀ h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J,
      Formalism.UG.bc ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h) ∈
        Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    fun h => bc_mem_UJ ψ hsig' hJ'
      (Subtype.property (p := fun g => g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J) h)
  have hl : ∀ g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F), Formalism.UG.bc ψ (Formalism.UG.bc φ g) = g := by
    intro g
    ext i j
    simp [Formalism.UG.bc, hψφ]
  have hr : ∀ g : GL (Fin I.n) (Af I.F ⊗[I.F] I.E), Formalism.UG.bc φ (Formalism.UG.bc ψ g) = g := by
    intro g
    ext i j
    simp [Formalism.UG.bc, hφψ]
  let e₀ : I.Gf ≃* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J :=
    { toFun := fun x => (⟨Formalism.UG.bc φ (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)), hmem x⟩ :
        ↥(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J))
      invFun := fun h => ⟨Formalism.UG.bc ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h), hmem' h⟩
      left_inv := fun x => Subtype.ext (hl (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)))
      right_inv := fun h => Subtype.ext (hr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h))
      map_mul' := fun x y => Subtype.ext (map_mul (Formalism.UG.bc φ) (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
        (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) }
  have hK : ∀ x : I.Gf, x ∈ I.Kset ↔ GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E))
      ((I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := fun x => stabilizes_lamAf_iff I (I.fmat x)
  have hKe : ∀ x : I.Gf, x ∈ I.Kset ↔ e₀ x ∈ KH := fun x => (hK x).trans (hKH (e₀ x)).symm
  have hmat : ∀ x : I.Gf, ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J (e₀ x) :
      GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) =
      (I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) := fun x => rfl
  have hcont_inv : Continuous (e₀.symm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J → I.Gf) := by
    apply continuous_of_continuousAt_one e₀.symm
    rw [ContinuousAt, Filter.tendsto_def]
    intro W hW
    simp only [map_one] at hW
    obtain ⟨g, hg1, hgW⟩ := I.topf_basis W hW
    have hN := GlobalTheory.Mem.Vol.StabGroup.congr_mem_nhds I.F I.E I.n I.L I.L_fg I.L_span g hg1
    have hmatc : Continuous (fun h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J =>
        ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
          Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E))) :=
      Units.continuous_val.comp continuous_subtype_val
    have h1 := hmatc.continuousAt (x := 1) |>.preimage_mem_nhds hN
    filter_upwards [h1, hKHo.mem_nhds KH.one_mem] with h hh hk
    apply hgW
    have hx : (I.fmat (e₀.symm h)).map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) =
        ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
          Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) := by
      rw [← hmat, MulEquiv.apply_symm_apply]
    refine ⟨(hK (e₀.symm h)).2 (hx ▸ (hKH h).1 hk), ?_⟩
    intro y hy
    have hy' := (mem_lamAf_iff I.L y).1 hy
    rw [← adLat_hat_eq_latHat] at hy'
    obtain ⟨w, hw, hwe⟩ := hh _ hy'
    refine ⟨fun i => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (w i), ?_, ?_⟩
    · rw [mem_lamAf_iff]
      have e1 : (fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F)
          ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (w i))) = w :=
        funext fun i => AlgEquiv.apply_symm_apply _ _
      rw [e1, ← adLat_hat_eq_latHat]
      exact hw
    · funext i
      apply (Algebra.TensorProduct.comm I.F I.E (Af I.F)).injective
      have e3 := congrFun hwe i
      beta_reduce at e3
      rw [← hx, tensorComm_mulVec_map_eq] at e3
      simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at e3
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, map_sub, smul_eq_mul,
        map_mul, map_natCast, AlgEquiv.apply_symm_apply, e3]
  have hcont : Continuous (e₀ : I.Gf → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J) := by
    apply continuous_of_continuousAt_one e₀
    rw [ContinuousAt, Filter.tendsto_def]
    intro V hV
    simp only [map_one] at hV
    obtain ⟨V', hV'V, hV'o, hV'1⟩ := mem_nhds_iff.1 hV
    have hC : IsCompact ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V') := hKHc.diff hV'o
    have hCi : IsClosed (e₀.symm '' ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V')) :=
      (hC.image hcont_inv).isClosed
    have hO : IsOpen (I.Kset ∩ (e₀.symm '' ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V'))ᶜ) :=
      hKo.inter hCi.isOpen_compl
    have h1O : (1 : I.Gf) ∈ I.Kset ∩ (e₀.symm '' ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V'))ᶜ := by
      refine ⟨hone, ?_⟩
      rintro ⟨c, ⟨-, hcV⟩, hc1⟩
      apply hcV
      have hc : c = 1 := by simpa using congrArg e₀ hc1
      rw [hc]
      exact hV'1
    refine Filter.mem_of_superset (hO.mem_nhds h1O) ?_
    rintro x ⟨hxK, hxC⟩
    show e₀ x ∈ V
    apply hV'V
    by_contra hxV
    exact hxC ⟨e₀ x, ⟨(hKe x).1 hxK, hxV⟩, e₀.symm_apply_apply x⟩
  exact ⟨{ toMulEquiv := e₀, continuous_toFun := hcont, continuous_invFun := hcont_inv },
    fun x => rfl, hK⟩

end GlobalTheory.CongTop.Swap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmulLocalWittFreeTupleGram
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalWittFree

theorem exists_smul_ratTup_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y := by
  intro F E _ _ _ _ _ σ hcm n J hJ v r P T hP y hy hgram

  obtain ⟨f, hf⟩ := _root_.GlobalTheory.FrameExtend.extend_frame F E σ hcm n J hJ v r P T hP y hy hgram

  have hdet := (GlobalTheory.FrameGram.std_frame_gram F E σ hcm n J hJ r P T hP).1

  obtain ⟨g, hg⟩ := GlobalTheory.LocalWittND.exists_smul_ratTup_eq F E σ hcm n J hJ v (r + 1 + r)
    (tupH P) hdet (Fin.append y f) hf
  refine ⟨g, funext fun i => ?_⟩

  have hF : (fun j => tupH P (Fin.castAdd r j)) = F0 P :=
    funext fun j => by simp [tupH, Fin.append_left]
  have h1 : (g • ratTup (F := F) (Fv F v) (tupH P)) (Fin.castAdd r i) =
      (g • ratTup (F := F) (Fv F v) (F0 P)) i := by
    rw [← hF]; rfl
  rw [← h1, hg, Fin.append_left]

end GlobalTheory.LocalWittFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnitaryFirstHermitianSpaceIsUnit
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.St.gramN_unitary_isUnit : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ g : GL (Fin (D.R.N 0)) D.host.E, (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE := by
  intro D X u wt hW y₀ hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, -, -, -, -, -, hM⟩ := GlobalTheory.St.qFrame_basis_gram D X u wt hW
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hG
  have hJ := X.B.I.J_det
  have hJJ : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ)
  have h1 : (Q.map (starRingEnd X.B.I.E))ᵀ * (Qi.map (starRingEnd X.B.I.E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ]; simp
  have hdetM : IsUnit (Matrix.fromBlocks G 0 0 G').det := by
    rw [← hM]
    apply Matrix.isUnit_det_of_right_inverse (B := Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ)
    calc (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q * (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ)
        = (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * (Q * Qi) * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (Q.map (starRingEnd X.B.I.E))ᵀ * (X.B.I.J * X.B.I.J⁻¹) * (Qi.map (starRingEnd X.B.I.E))ᵀ := by
          rw [hQQi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hJJ, Matrix.mul_one, h1]
  rw [Matrix.det_fromBlocks_zero₂₁] at hdetM
  have hGdet : G.det ≠ 0 := (isUnit_of_mul_isUnit_left hdetM).ne_zero
  have hy0 : y₀.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hy
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact hGdet this.symm
  have hd : (y₀.map X.ιE).det = X.ιE y₀.det := by
    simpa using (RingHom.map_det X.ιE.toRingHom y₀).symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (y₀.map X.ιE) ?_, rfl⟩
  rw [hd]; exact (map_ne_zero X.ιE).mpr hy0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OfClassification
section
namespace GlobalTheory.DiscreteSeriesConsequences

theorem of_classification : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Dec.LowKMultOne ∧ GlobalTheory.Dec.DSInfChar ∧
    GlobalTheory.Dec.DSExists ∧ GlobalTheory.Dec.DSUnique ∧ GlobalTheory.Published.DiscreteSeriesUpqExists := by
  intro h
  obtain ⟨hE, -, hU, hI, hM, -, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass (GlobalTheory.Published.discreteSeriesClassification_iff.1 h)
  exact ⟨hM, hI, hE, hU, GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE⟩

end GlobalTheory.DiscreteSeriesConsequences
end

