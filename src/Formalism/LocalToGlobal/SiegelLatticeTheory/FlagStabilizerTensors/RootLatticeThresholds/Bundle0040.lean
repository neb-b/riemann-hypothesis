module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0039
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiCondAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0054
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.LsSetresAvgW
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharB
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D)

theorem g_pos : 0 < X.B.g := by
  rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem divN_add (a b : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    divN X.B.I X.B.g (a + b) = divN X.B.I X.B.g a + divN X.B.I X.B.g b := by
  unfold divN; ring

theorem divN_g (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    divN X.B.I X.B.g ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * c) = c := by
  unfold divN
  have hg : ((X.B.g : ℕ) : X.B.I.F) ≠ 0 := Nat.cast_ne_zero.2 (g_pos X).ne'
  rw [← mul_assoc, ← map_natCast (algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)), ← map_mul,
    inv_mul_cancel₀ hg, map_one, one_mul]

theorem psi_modg (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) {d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hd : d ∈ IntAf X.B.I.F X.B.I.E) :
    X.psiEf (divN X.B.I X.B.g (c + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * d)) = X.psiEf (divN X.B.I X.B.g c) := by
  rw [divN_add, X.psiEf_add, divN_g, X.psiEf_int d hd, mul_one]

theorem divN_incl (y : X.B.I.E) : divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y) =
    Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((X.B.g : ℕ) : X.B.I.E)⁻¹ * y) := by
  unfold divN
  rw [Algebra.TensorProduct.algebraMap_apply, map_mul]
  congr 1
  show algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) ⊗ₜ[X.B.I.F] (1 : Af X.B.I.F) =
    Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((X.B.g : ℕ) : X.B.I.E)⁻¹)
  rw [map_inv₀, map_natCast]
  rfl

theorem psiEinf_star (y : X.B.I.E) : psiEinf X.B.I (star y) = psiEinf X.B.I y := by
  unfold psiEinf
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) y]
  congr 2
  simp only [starRingEnd_apply, star_star]
  ring

theorem psi_incl_star (y : X.B.I.E) :
    X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (star y)) =
      X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y) := by
  have h1 := X.psiEf_rat (star y)
  have h2 := X.psiEf_rat y
  rw [psiEinf_star] at h1
  have hne : psiEinf X.B.I y ≠ 0 := by intro h; rw [h, mul_zero] at h2; exact zero_ne_one h2
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

theorem psi_sig (ε : 𝓞 X.B.I.E) (m : ℕ) :
    X.psiEf (divN X.B.I X.B.g (iE X.B.I (sigO X.B.I ε) * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) =
      X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  have e : ∀ a : 𝓞 X.B.I.E, iE X.B.I a * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((a : X.B.I.E) * m) := by
    intro a; rw [map_mul, map_natCast]
  rw [e, e, divN_incl, divN_incl, sigO_coe]
  have : ((X.B.g : ℕ) : X.B.I.E)⁻¹ * (star (ε : X.B.I.E) * m) = star (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * m)) := by
    rw [star_mul, star_mul, star_inv₀, star_natCast, star_natCast]; ring
  rw [this, psi_incl_star]

variable {kv : Σ k : Fin 2, D.nd.PlG k}

theorem g_split_mul {k k' : Fin 2} (hk : k' ≠ k) :
    ((D.host.g k : ℕ) : 𝓞 X.B.I.E) * ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) = ((X.B.g : ℕ) : 𝓞 X.B.I.E) := by
  rw [g_eq_cast]
  fin_cases k <;> fin_cases k'
  · exact absurd rfl hk
  · rfl
  · exact mul_comm _ _
  · exact absurd rfl hk

theorem other_ne (k : Fin 2) : (1 - k) ≠ k := by fin_cases k <;> decide

theorem psi_period {ε : 𝓞 X.B.I.E} (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)}) (m q : ℕ) :
    X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * ((m + D.host.g kv.1 * q : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) =
      X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.1 hε
  have e : iE X.B.I ε * ((m + D.host.g kv.1 * q : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I δ * q) := by
    have hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
        iE X.B.I (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) * ((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)) := by
      rw [g_split_mul X (other_ne kv.1)]; simp [iE]
    rw [hg, ← hδ]
    simp only [iE, map_mul, map_natCast, Nat.cast_add, Nat.cast_mul]
    ring
  rw [e, psi_modg X _ (mul_mem (iE_int X.B.I δ) (natCast_mem _ q))]

def psiK (ε : 𝓞 X.B.I.E) (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)}) :
    AddChar (ZMod (D.host.g kv.1)) ℂ where
  toFun t := X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)))
  map_zero_eq_one' := by
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero]
    unfold divN; rw [mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  map_add_eq_mul' a b := by
    have : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
    have hval : a.val + b.val = (a + b).val + D.host.g kv.1 * ((a.val + b.val) / D.host.g kv.1) := by
      rw [ZMod.val_add]; exact (Nat.mod_add_div _ _).symm
    rw [← psi_period X hε (a + b).val ((a.val + b.val) / D.host.g kv.1), ← hval, Nat.cast_add, mul_add, divN_add,
      X.psiEf_add]

theorem psiK_apply (ε : 𝓞 X.B.I.E) (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)})
    (t : ZMod (D.host.g kv.1)) :
    psiK X ε hε t = X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := rfl

end Formalism.L2.SG.Pf.KppChar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PiWInvol
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

def piW : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
  ⟨ptPar w.1 b.val, lt_of_lt_of_eq (ptPar_lt w.1 b.val (by rw [w.2.2]; exact b.2)) w.2.2⟩

def blkW : Fin (D.R.rS + 1) → ℕ := fun i => blkOf w.1 i.val

theorem piW_invol (a : Fin (D.R.rS + 1)) : piW w (piW w a) = a := by
  apply Fin.ext
  show ptPar w.1 (ptPar w.1 a.val) = a.val
  exact ptPar_invol w.1 a.val (by rw [w.2.2]; exact a.2)

theorem piW_blk (a : Fin (D.R.rS + 1)) : blkW w (piW w a) = blkW w a := by
  show blkOf w.1 (ptPar w.1 a.val) = blkOf w.1 a.val
  exact blkOf_ptPar w.1 a.val (by rw [w.2.2]; exact a.2)

theorem piW_anti (a b : Fin (D.R.rS + 1)) (h : blkW w a = blkW w b) (hab : a < b) : piW w b < piW w a := by
  show ptPar w.1 b.val < ptPar w.1 a.val
  exact ptPar_anti w.1 a.val b.val (by rw [w.2.2]; exact b.2) hab h

def Fw (v : InfinitePlace X.B.I.F) : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ := frm X u D.host.rdE v

def Gw (v : InfinitePlace X.B.I.F) : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ :=
  fun b => uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v b

theorem hGG_w (v : InfinitePlace X.B.I.F) (a b : Fin (D.R.rS + 1)) :
    hJ (X.B.I.ε v) (Gw X u u' w v a) (Gw X u u' w v b) = lastDiag (-((Tw u' : ℝ) : ℂ)) a b := by
  show hJ (X.B.I.ε v) (uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v a)
    (uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v b) = _
  rw [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj, Matrix.mulVec_mulVec]
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by
    simp [uMat]
  rw [h1, Matrix.one_mulVec]
  exact gram_frm X v u' D.host.rdE a b

theorem hZ_w (hw : OkPt X u u' w) (v : InfinitePlace X.B.I.F) (c b : Fin (D.R.rS + 1)) :
    Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) c b ≠ 0 ↔ c = piW w b := by
  have hrep : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dite_eq_left hw.1]
    exact hw.1.choose_spec
  have hk : ∀ a : Fin (D.R.rS + 1), (((D.host.rdE : ℝ) : ℂ) ^ (D.R.rS - a.1))⁻¹ ≠ 0 := fun a =>
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast rdE_pos_c.ne'))
  have hZ : Zm (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) c b =
      (star ((((D.host.rdE : ℝ) : ℂ) ^ (D.R.rS - c.1))⁻¹) * (((D.host.rdE : ℝ) : ℂ) ^ (D.R.rS - b.1))⁻¹) *
        ZX X u u' 1 (gamW X u u' w) v c b := by
    simp only [Zm, Matrix.of_apply, Fw, Gw, ZX, Formalism.L2.SG.RealObj.Zhat, frm, famSc, hJ, Matrix.mulVec_smul, star_smul,
      Complex.ofReal_one, one_pow, inv_one, one_smul]
    simp [dotProduct_smul, smul_dotProduct]
    ring
  have h2 := congrFun (congrFun (hrep v) c) b
  simp only [Formalism.L2.SG.RealObj.ZhatO] at h2
  have h3 : ZX X u u' 1 (gamW X u u' w) v c b ≠ 0 ↔ Formalism.L2.SG.RealObj.ptC X v w c b ≠ 0 := by
    rw [← h2]
    simp
  have hb : b.val < (w.1.map Prod.snd).sum := by rw [w.2.2]; exact b.2
  rw [hZ, mul_ne_zero_iff, h3]
  simp only [Formalism.L2.SG.RealObj.ptC, Matrix.map_apply, Formalism.MainNotions.S.ptMat]
  rw [ptEntry_eq w.1 c.val b.val hb]
  simp only [ne_eq, map_eq_zero_iff _ (X.B.I.φ v).injective, EmbeddingLike.map_eq_zero_iff, ite_eq_right_iff,
    not_forall, exists_prop]
  constructor
  · rintro ⟨_, h, _⟩
    exact Fin.ext h
  · intro h
    exact ⟨mul_ne_zero (star_ne_zero.mpr (hk c)) (hk b), congrArg Fin.val h, ptSc_ne w.1 w.2.1 b.val hb⟩

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PointUniformity
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma
  Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.PointUniformity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minor

variable {D : D7}

theorem lead_sign (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    leadMinorK (ZhatOM Z) l hl * D.host.conj (leadMinorK (ZhatOM Z) l hl) =
      leadMinorK Z l hl * D.host.conj (leadMinorK Z l hl) := by
  have e : ∀ W : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      ((ZhatOM W).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
        (∏ j : Fin l, ((-1 : D.host.E) ^ (D.R.rS - (Fin.castLE hl j).val))) *
          (W.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
    intro W
    rw [← Matrix.det_mul_row]
    rfl
  simp only [leadMinorK]
  rw [e Z, Finset.prod_pow_eq_pow_sum]
  rcases neg_one_pow_eq_or D.host.E (∑ j : Fin l, (D.R.rS - (Fin.castLE hl j).val)) with h | h <;>
    rw [h] <;> simp

theorem gglob_of_cell {T T' : ℕ} (F : LFlag (D.sp.Y 0) D.R.rS (T : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T' : D.host.E))
    (p : Point D.host.E (D.R.rS + 1)) (hc : IsInCell (ZhatOM (ZhatL F F')) p) :
    Gglob D T T' p = Gval F F' := by
  obtain ⟨L, U, hL, hU, hZ⟩ := hc
  have hinv : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      leadMinorK (ZhatOM (ZhatL F F')) l hl = leadMinorK (ptMat p) l hl := by
    intro l hl
    rw [leadMinorK_eq, leadMinorK_eq, hZ]
    exact Formalism.HermitianLatticeCounting.Final.ExpansionTerms.leadingMinorUnipotentInvariant _ _ _ _ _ _ ⟨fun i => (hL i i).2 rfl, fun i j h => (hL i j).1 h⟩
      ⟨fun i => (hU i i).2 rfl, fun i j h => (hU i j).1 h⟩
  unfold Gglob
  rw [← hinv, ← hinv, lead_sign, lead_sign]
  unfold Gval Gflag Dl
  clear hinv hZ hL hU L U
  simp only [Formalism.MainNotions.S.Inh.tie_star]
  have hE : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1), leadMinorE (Zhat F.fl F'.fl) l = leadMinorK (ZhatL F F') l hl := by
    intro l hl
    unfold leadMinorE leadMinorK
    rw [dite_eq_left hl]
  rw [hE _ le_rfl, hE _ (Nat.le_succ _)]

theorem det_isIntegral {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ i j, IsIntegral ℤ (M i j)) :
    IsIntegral ℤ M.det := by
  have key : M.det ∈ integralClosure ℤ D.host.E := by
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ (fun σ _ => ?_)
    rw [Units.smul_def]
    refine Subalgebra.zsmul_mem _ ?_ _
    exact Subalgebra.prod_mem _ (fun i _ => (mem_integralClosure_iff ..).2 (hM _ _))
  exact (mem_integralClosure_iff ..).1 key

end Minor

theorem rowPt_of {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hG : t.toTerm.G ≠ 0) (hv : (Y.tO u u').vec t ≠ 0) :
    Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm) := by
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.TermOp.Vanish.avgCore
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Pf.chiTrivialC_outright
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' t.toTerm hG hrel
  obtain ⟨F2, ⟨hP2, -⟩, hG2, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam :=
    Formalism.L2.SG.NGCut.PtPf.frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2
  have hF2 : ∀ b, frame F2 b ∈ t.toTerm.lam := Formalism.L2.SG.NGCut.PtPf.frame_mem _ hP2.1.1 hP2.2.2.2
  have hZint : ∀ i j, IsIntegral ℤ (ZhatOM (ZhatL (lf D (X.Fu u)) F2) i j) :=
    Formalism.L2.SG.NGCut.PtPf.zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF2
  have hGg : Gglob D (D.mem u).A.T (D.mem u').A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm) = Gval (lf D (X.Fu u)) F2 :=
    gglob_of_cell (lf D (X.Fu u)) F2 _ hcell
  have hTu := tie_Tu_pos D u
  refine ⟨⟨⟨ZhatOM (ZhatL (lf D (X.Fu u)) F2), hZint, hcell⟩, by rw [hGg]; exact hG2, ?_⟩, fun v => ?_⟩
  ·
    obtain ⟨L, U, hL, hU, hZ⟩ := hcell
    have hlm : ∀ l (hl : l ≤ D.R.rS + 1), IsIntegral ℤ (leadMinorK (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) l hl) := by
      intro l hl
      have e : leadMinorK (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) l hl =
          leadMinorK (ZhatOM (ZhatL (lf D (X.Fu u)) F2)) l hl := by
        rw [leadMinorK_eq, leadMinorK_eq]
        exact Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_cell _ _ ⟨L, U, hL, hU, hZ⟩ l
      rw [e]
      exact det_isIntegral _ fun i j => hZint _ _
    have hconj : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (D.host.conj x) := fun x hx => by
      rw [← Formalism.MainNotions.S.Inh.tie_star]
      exact hx.map (starRingEnd D.host.E).toIntAlgHom
    unfold Gglob
    have hn : ∀ n : ℕ, IsIntegral ℤ (n : D.host.E) := fun n => by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (n : ℤ)))
    exact ((hlm _ _).mul (hconj _ (hlm _ _))).sub (((hn _).mul (hn _)).mul ((hlm _ _).mul (hconj _ (hlm _ _))))
  ·
    have hpos := (b_G_pos (p_starConj D) hTu (lf D (X.Fu u)) F2 rfl hP2.1.2 hG2
      (p_posX D _ hTu (lf D (X.Fu u))) (plEmb D v)).1
    have hpos2 : 0 < ((plEmb D v) (Gglob D (D.mem u).A.T (D.mem u').A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm))).re := by
      calc (0 : ℝ) < ((plEmb D v) (Gval (lf D (X.Fu u)) F2)).re := hpos
        _ = _ := by rw [hGg]
    rw [plEmb_Gglob, Complex.ofReal_re] at hpos2
    rw [GPoint_loc]
    have hc : 0 < ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 := by
      have := Finset.prod_pos (s := Finset.univ) (fun (i : Fin D.R.rS) _ => alf_pos D i)
      positivity
    exact mul_pos hc hpos2

theorem ptUnif' : Formalism.L2.SG.Pf.BDat.PtUnif := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ t ht hv => rowPt_of Y u u' t ?_ hv⟩
  intro h0
  apply ht.1
  simp [Full.tO, tOf, Gt, GTerm.G, h0]

theorem ptUnifG : Formalism.L2.SG.Pf.BDat.PtUnifG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ t ht hv => rowPt_of Y u u t ?_ hv⟩
  intro h0
  apply ht.1
  simp [Full.tO, tOf, Gt, GTerm.G, h0]

end Formalism.L2.SG.PointUniformity

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RelPtR
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open Matrix

namespace Formalism.L2.SG.Pf.RelPtR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem rv_crd_fvec (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    rv X.B.I v (X.crd ((X.Fu u).fvec a)) = Formalism.L2.SG.RealObj.frm X u 1 v a := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · rw [FlagG.fvec, Fin.snoc_last, X.flagZVector u, Fin.snoc_last]
    rfl
  · rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e u, Fin.snoc_castSucc]
    rfl

theorem zhatP_eq (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) *
        Formalism.L2.SG.RealObj.ZX X u u' 1 (Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ) a b := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hA : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ)
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) a b =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a)
        (uMat ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ)) *ᵥ
          (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) b)) := by
    unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm Formalism.L2.SG.Pf.JointAmplitudePoints.gamP Formalism.L2.SG.RealObj.trG hJ
    rw [← hH, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT]
    congr 1
    simp only [Matrix.mulVec_mulVec]
    congr 1
    rw [show (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ *
        (C.Qi τ * uMat ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ)) * C.Q τ) =
      (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) *
        uMat ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ)) * C.Q τ by
        simp only [Matrix.mul_assoc], hQQi]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hA, Formalism.L2.SG.Pf.LTL.Q_fvec C u τ a, Formalism.L2.SG.Pf.LTL.Q_fvec C u' τ b, Matrix.mulVec_smul,
    Formalism.L2.SG.Pf.LTL.hJ_smul_real, rv_crd_fvec, rv_crd_fvec]
  rfl

theorem alf_eq (D : D7) (a : Fin (D.R.rS + 1)) : Formalism.MainNotions.BesselShellMomentBounds.alf D a = rhoF D a := by
  unfold Formalism.MainNotions.BesselShellMomentBounds.alf rhoF
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  ring

theorem ptMat_ptLoc (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) (a b : Fin (D.R.rS + 1)) :
    ptMat (ptLoc D τ w) a b = ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (ptMat w a b) := by
  have h := Formalism.MainNotions.BesselShellMomentBounds.ptEntry_loc D τ w.1 0 a b
  simp only [Nat.zero_add] at h
  change ptEntry (locBlocksFrom D (rhoReal D) τ 0 w.1) a b = _
  rw [h, alf_eq D a, alf_eq D b]
  rfl

variable (u u' : D.what₂.Word)

theorem zhatO_gamP (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g)
    (τ : D.what₂.Tau) :
    ZhatO D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) =
      ptMat (ptLoc D τ w) := by
  have hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w (Formalism.L2.SG.RealObj.gamW X u u' w) := by
    unfold Formalism.L2.SG.RealObj.gamW
    rw [dite_eq_left hw]
    exact hw.choose_spec
  ext a b
  have h1 := congrFun (congrFun (hrep (vOf X τ)) a) b
  unfold Formalism.L2.SG.RealObj.ZhatO Formalism.L2.SG.RealObj.ptC at h1
  simp only [Matrix.map_apply] at h1
  rw [X.φ_eq, X.ιE.apply_symm_apply, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h1
  unfold ZhatO
  rw [zhatP_eq C u u' w τ a b, ptMat_ptLoc τ w a b, ← h1]
  ring

theorem normSq_dmin (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (g : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) (l : Fin (D.R.rS + 2)) :
    Complex.normSq (Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' g l) =
      Complex.normSq (((ZhatO D.R.k D.R.rS z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
        (Fin.castLE (Nat.le_of_lt_succ l.isLt))).det) := by
  unfold Formalism.QuantumDeterminants.Dmin
  have hM : (ZhatO D.R.k D.R.rS z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
      (Fin.castLE (Nat.le_of_lt_succ l.isLt)) =
      (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
        (Fin.castLE (Nat.le_of_lt_succ l.isLt)) *
      Matrix.diagonal (fun b : Fin l.val => (-1 : ℂ) ^ (D.R.rS - (Fin.castLE (Nat.le_of_lt_succ l.isLt) b).val)) := by
    ext i j
    simp [ZhatO, Matrix.mul_diagonal, mul_comm]
  rw [hM, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod]
  simp [Complex.normSq_neg]

theorem gf_gamP (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g)
    (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) =
      Gpt (((D.mem u).A.T : ℕ) : ℝ) (((D.mem u').A.T : ℕ) : ℝ) (ptLoc D τ w) := by
  unfold Formalism.QuantumDeterminants.Gf Gpt
  rw [normSq_dmin, normSq_dmin, zhatO_gamP C u u' w hw τ, Formalism.L2.SG.Pf.LTL.tz_zB C u τ,
    Formalism.L2.SG.Pf.LTL.tz_zB C u' τ]
  rfl

theorem relPtExPR_holds : Formalism.L2.SG.Pf.BDatR.RelPtExPR u u' C := by
  intro w hb hw τ
  refine ⟨Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _, ?_, ?_⟩
  · refine ⟨(1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ),
      fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => by subst h; exact Matrix.one_apply_eq i⟩,
      fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h).symm, fun h => by subst h; exact Matrix.one_apply_eq i⟩, ?_⟩
    rw [Matrix.one_mul, Matrix.mul_one, zhatO_gamP C u u' w hw τ]
  · rw [gf_gamP C u u' w hw τ]
    exact (hb.2 τ).ne'

end Formalism.L2.SG.Pf.RelPtR
end
end

