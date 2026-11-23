module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterEqLocalFactorAtTypePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevChiAt

section Gen
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eq_comp (s : SplitPlace L) :
    s.proj = (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)).toRingHom.comp
      (compAt L s.v) := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem locM_eq_one (s : SplitPlace L) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (κ : GAf L n)
    (hκ : TrivOutside {v} κ) (hne : s.v ≠ v) : NX.locM s κ = 1 := by
  have h := hκ s.v (by simpa using hne)
  have e : NX.locM s κ = ((κ.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v)).map
      (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)).toRingHom := by
    rw [Matrix.map_map, ← RingHom.coe_comp, ← proj_eq_comp]
    rfl
  rw [e, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end Gen

variable {D : D7}

section Red
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem intLift_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    NX.intLift v (1 : v.adicCompletion (maximalRealSubfield L)) = 1 := by
  unfold NX.intLift
  split_ifs with h
  · rfl
  · exact absurd (v.adicCompletionIntegers (maximalRealSubfield L)).one_mem h

theorem intLift_zero (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    NX.intLift v (0 : v.adicCompletion (maximalRealSubfield L)) = 0 := by
  unfold NX.intLift
  split_ifs with h
  · rfl
  · rfl

theorem redMat_topR_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {R : Type} [CommRing R]
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) {n r : ℕ} (h : r ≤ n) :
    NX.redMat v red (NX.topR h (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))) = 1 := by
  ext a c
  simp only [NX.redMat, NX.topR, Matrix.submatrix_apply]
  by_cases hac : a = c
  · subst hac; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, intLift_one, map_one]
  · rw [Matrix.one_apply_ne (fun e => hac (Fin.castLE_injective _ e)), Matrix.one_apply_ne hac, intLift_zero, map_zero]

theorem detT_one {R : Type} [CommRing R] (n r : ℕ) : NX.detT r (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold NX.detT
  have : (1 : Matrix (Fin n) (Fin n) R).submatrix (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) = 1 := by
    ext a c
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

end Red

theorem gVal_one (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) :
    NX.gVal D i k b kv s red τ 1 = 1 := by
  classical
  have hgl : NX.glOf (1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 := by
    apply Units.ext
    rw [NX.glOf_val _ (by simp)]
    rfl
  have hpsi : NX.psiUTot D i b (1 : G0g D.nd) = 1 := by
    unfold NX.psiUTot
    rw [dite_eq_left (Subgroup.one_mem _)]
    have : (⟨1, Subgroup.one_mem _⟩ : D.nexp.U) = 1 := rfl
    rw [this, map_one]; rfl
  unfold NX.gVal
  erw [redMat_topR_one, hgl, Pi.mulSingle_one, hpsi, detT_one, intLift_one, map_one red, map_one, one_mul]
  rw [dite_eq_left isUnit_one]
  have : (isUnit_one : IsUnit (1 : ZMod (D.host.g kv.1))).unit = 1 := Units.ext rfl
  rw [this, map_one]
  exact map_one _

theorem loc_one_eq {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) :
    NX.locM s (1 : GAf L n) = 1 := by
  simp [NX.locM]

theorem chi_eq_at : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ (h : κ ∈ M.J), TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      ((M.χ ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) =
        NX.gVal D i k b kv0 (M.sp (NX.pG D kv0)) (M.redG kv0) (τ kv0) (NX.locM (M.sp (NX.pG D kv0)) κ) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M kv0 hkv hQ hD κ h hκ
  have hG : ∀ kv, kv ≠ kv0 → NX.locM (M.sp (NX.pG D kv)) κ = 1 := fun kv hne => locM_eq_one _ κ hκ (hkv kv hne)
  have hQl : ∀ P ∈ M.QP, NX.locM (M.sp P) κ = 1 := fun P hP => locM_eq_one _ κ hκ (hQ P hP)
  have hDl : ∀ P ∈ M.DP, NX.locM (M.sp P) κ = 1 := fun P hP => locM_eq_one _ κ hκ (hD P hP)
  have h1 := M.chi_eq 1 M.J.one_mem
  have e1 : (⟨1, M.J.one_mem⟩ : M.J) = 1 := rfl
  rw [e1, map_one, Units.val_one] at h1
  simp only [loc_one_eq, gVal_one, Finset.prod_const_one, one_mul] at h1
  rw [M.chi_eq κ h, Fintype.prod_eq_single kv0 (fun kv hne => by rw [hG kv hne, gVal_one]), mul_assoc]
  conv_rhs => rw [← mul_one (NX.gVal D i k b kv0 (M.sp (NX.pG D kv0)) (M.redG kv0) (τ kv0) (NX.locM (M.sp (NX.pG D kv0)) κ))]
  congr 1
  rw [h1]
  congr 1
  · exact Finset.prod_congr rfl fun P hP => by rw [hQl P hP]
  · exact Finset.prod_congr rfl fun P hP => by rw [hDl P hP]

end GlobalTheory.LevChiAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParahoricOfScalarActionOnRamifiedParahoricFor
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ParaRigid

theorem det_mem_of {K : Type} [Field K] (O : Subring K) {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (hM : ∀ i j, M i j ∈ O) : M.det ∈ O := by
  have e : M = (Matrix.of fun i j => (⟨M i j, hM i j⟩ : O)).map O.subtype := by ext i j; rfl
  have h := RingHom.map_det O.subtype (Matrix.of fun i j => (⟨M i j, hM i j⟩ : O))
  rw [RingHom.mapMatrix_apply] at h
  rw [e, ← h]
  exact SetLike.coe_mem _

theorem inv_entry_mem {K : Type} [Field K] (O : Subring K) {m : ℕ} (x : GL (Fin m) K)
    (h1 : ∀ i j, x.1 i j ∈ O) (hd : (x.1.det)⁻¹ ∈ O) : ∀ i j, (x⁻¹).1 i j ∈ O := by
  intro i j
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine O.mul_mem ?_ (det_mem_of O _ ?_)
  · rw [Ring.inverse_eq_inv']; exact hd
  · intro k l
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    · exact h1 k l

theorem mem_GLint_of {K : Type} [Field K] (O : Subring K) {m : ℕ} (x : GL (Fin m) K)
    (h1 : ∀ i j, x.1 i j ∈ O) (hd : (x.1.det)⁻¹ ∈ O) : x ∈ Formalism.UG.GLint (Fin m) O :=
  GlobalTheory.HeckeScalarSph.mem_GLint_iff.2 ⟨h1, inv_entry_mem O x h1 hd⟩

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

variable {K : Type} [Field K] {m : ℕ}

def colVecAt (j : Fin m) (t : K) : Matrix (Fin m) Unit K := Matrix.of fun i _ => if i = j then t else 0

def rowVecAt (K : Type) [Field K] (i : Fin m) : Matrix Unit (Fin m) K := Matrix.of fun _ j => if j = i then 1 else 0

def Gmat (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) : Matrix (Fin m) (Fin m) K :=
  1 + (h * colVecAt j0 t) * rowVecAt K i0

def Pmat (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) : Matrix (Fin m) (Fin m) K :=
  1 + colVecAt j0 t * (rowVecAt K i0 * h)

theorem det_G (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) :
    (Gmat h i0 j0 t).det = 1 + h i0 j0 * t := by
  rw [Gmat, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem det_P (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) :
    (Pmat h i0 j0 t).det = 1 + h i0 j0 * t := by
  rw [Pmat, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem G_apply (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (i j : Fin m) :
    Gmat h i0 j0 t i j = (1 : Matrix (Fin m) (Fin m) K) i j + if j = i0 then h i j0 * t else 0 := by
  simp [Gmat, colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem P_apply (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (i j : Fin m) :
    Pmat h i0 j0 t i j = (1 : Matrix (Fin m) (Fin m) K) i j + if i = j0 then t * h i0 j else 0 := by
  simp [Pmat, colVecAt, rowVecAt, Matrix.mul_apply]
  done

theorem conj_G (h h' : Matrix (Fin m) (Fin m) K) (hh : h' * h = 1) (i0 j0 : Fin m) (t : K) :
    h' * Gmat h i0 j0 t * h = Pmat h i0 j0 t := by
  simp only [Gmat, Pmat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hh, Matrix.one_mul]

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

variable {K : Type} [Field K] {m : ℕ}

theorem detDD_G (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (r : ℕ) (hi0 : r ≤ i0.val) :
    (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Gmat h i0 j0 t a.1 b.1).det = 1 + h i0 j0 * t := by
  have e : (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Gmat h i0 j0 t a.1 b.1) =
      1 + ((Matrix.of fun a (_ : Unit) => h a.1 j0 * t : Matrix {x : Fin m // r ≤ x.val} Unit K) *
        (Matrix.of fun (_ : Unit) b => if b = ⟨i0, hi0⟩ then 1 else 0 : Matrix Unit {x : Fin m // r ≤ x.val} K)) := by
    ext a b
    simp [G_apply, Matrix.one_apply, Matrix.mul_apply, Subtype.ext_iff]
  rw [e, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [Matrix.mul_apply]

theorem detDD_P (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (r : ℕ) (hj0 : j0.val < r) :
    (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Pmat h i0 j0 t a.1 b.1).det = 1 := by
  have e : (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Pmat h i0 j0 t a.1 b.1) = 1 := by
    ext a b
    have ha : (a.1 : Fin m) ≠ j0 := fun e => by have := a.2; rw [e] at this; omega
    simp [P_apply, Matrix.one_apply, Subtype.ext_iff, ha]
  rw [e, Matrix.det_one]

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

theorem mem_para_of_eig : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (a : s.v.adicCompletion (maximalRealSubfield L)), F ≠ 0 → Valued.v a = 1 → (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s r (s.loc n κ))) → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = 1 → χ ⟨κ, h⟩ = 1) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = a → χ ⟨κ, h⟩ ≠ 1) → ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  intro L _ _ _ n r s V _ _ F J χ a hF ha hJ hEig h1 ha' κ hκU hκT hc
  obtain ⟨c, hc⟩ := hc
  classical
  set O := (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring with hO
  have hOv : ∀ x, x ∈ O ↔ Valued.v x ≤ 1 := fun x => by
    rw [hO, ValuationSubring.mem_toSubring, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hint := (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκT).2 hκU
  refine ⟨hint, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, j0, hi0, hj0, hv⟩ := hcon
  set h := s.loc n κ with hh
  have hent : ∀ i j, Valued.v (h.val i j) ≤ 1 := fun i j =>
    (hOv _).1 ((GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hint).1 i j)
  have hv1 : Valued.v (h.val i0 j0) = 1 := le_antisymm (hent i0 j0) hv
  have hne : h.val i0 j0 ≠ 0 := by
    intro e; rw [e, map_zero] at hv1; exact zero_ne_one hv1
  have ha0 : a ≠ 0 := by
    intro e; rw [e, map_zero] at ha; exact zero_ne_one ha
  set t := (a - 1) / h.val i0 j0 with ht
  have htv : Valued.v t ≤ 1 := by
    rw [ht, map_div₀, hv1, div_one]
    refine (Valuation.map_sub _ _ _).trans (max_le ha.le (by rw [map_one]))
  have hth : 1 + h.val i0 j0 * t = a := by rw [ht]; field_simp; ring
  have hdinv : a⁻¹ ∈ O := by rw [hOv, map_inv₀, ha, inv_one]
  have hone : ∀ i j, Valued.v ((1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) ≤ 1 := by
    intro i j
    rw [Matrix.one_apply]; split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  have hGint : ∀ i j, Gmat h.val i0 j0 t i j ∈ O := by
    intro i j
    rw [hOv, G_apply]
    refine (Valuation.map_add _ _ _).trans (max_le (hone i j) ?_)
    split_ifs
    · rw [map_mul]; exact mul_le_one' (hent _ _) htv
    · rw [map_zero]; exact zero_le'
  have hPint : ∀ i j, Pmat h.val i0 j0 t i j ∈ O := by
    intro i j
    rw [hOv, P_apply]
    refine (Valuation.map_add _ _ _).trans (max_le (hone i j) ?_)
    split_ifs
    · rw [map_mul]; exact mul_le_one' htv (hent _ _)
    · rw [map_zero]; exact zero_le'
  have hdG : (Gmat h.val i0 j0 t).det = a := by rw [det_G, hth]
  have hdP : (Pmat h.val i0 j0 t).det = a := by rw [det_P, hth]
  let Gg := Matrix.GeneralLinearGroup.mkOfDetNeZero (Gmat h.val i0 j0 t) (by rw [hdG]; exact ha0)
  have hGg : Gg.val = Gmat h.val i0 j0 t := rfl
  obtain ⟨g, ⟨hgT, hgl⟩, -⟩ := (_root_.GlobalTheory.SplitAdelic.main L n s).2.2 Gg
  set p := κ⁻¹ * g * κ with hp
  have hpT : TrivOutside {s.v} p :=
    GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv hκT) hgT) hκT
  have hinv : (h⁻¹).val * h.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpl : (s.loc n p).val = Pmat h.val i0 j0 t := by
    rw [hp, map_mul, map_mul, map_inv, hgl, ← hh, Units.val_mul, Units.val_mul, hGg]
    exact conj_G h.val (h⁻¹).val hinv i0 j0 t
  have hgl' : (s.loc n g).val = Gmat h.val i0 j0 t := by rw [hgl]; exact hGg
  have hgP : NG.ParaRT s r (s.loc n g) := by
    refine ⟨mem_GLint_of O _ (fun i j => by rw [hgl']; exact hGint i j) (by rw [hgl', hdG]; exact hdinv), ?_⟩
    intro i j hi hj
    have hji : j ≠ i0 := fun e => by rw [e] at hj; omega
    have hij : i ≠ j := fun e => by rw [e] at hi; omega
    rw [hgl', G_apply, if_neg hji, Matrix.one_apply_ne hij, add_zero, map_zero]
    exact zero_lt_one
  have hpP : NG.ParaRT s r (s.loc n p) := by
    refine ⟨mem_GLint_of O _ (fun i j => by rw [hpl]; exact hPint i j) (by rw [hpl, hdP]; exact hdinv), ?_⟩
    intro i j hi hj
    have hij0 : i ≠ j0 := fun e => by rw [e] at hi; omega
    have hij : i ≠ j := fun e => by rw [e] at hi; omega
    rw [hpl, P_apply, if_neg hij0, Matrix.one_apply_ne hij, add_zero, map_zero]
    exact zero_lt_one
  have hgJ : g ∈ J := (hJ g hgT).2 hgP
  have hpJ : p ∈ J := (hJ p hpT).2 hpP
  have hχg : χ ⟨g, hgJ⟩ ≠ 1 := ha' g hgJ hgT (by unfold NG.detDD; simp only [hgl']; rw [detDD_G _ _ _ _ r hi0, hth])
  have hχp : χ ⟨p, hpJ⟩ = 1 := h1 p hpJ hpT (by unfold NG.detDD; simp only [hpl]; rw [detDD_P _ _ _ _ r hj0])
  have eg := hEig ⟨g, hgJ⟩
  have ep := hEig ⟨p, hpJ⟩
  rw [hχp] at ep
  have hkp : κ * p = g * κ := by rw [hp]; group
  obtain ⟨x0, hx0⟩ : ∃ x, F x ≠ 0 := by
    by_contra hn; push_neg at hn; exact hF (funext hn)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx0
    have := hc (x0 * κ⁻¹)
    rwa [inv_mul_cancel_right, zero_smul] at this
  have key : ∀ x, c • ((χ ⟨g, hgJ⟩ : ℂˣ) : ℂ) • F x = c • F x := by
    intro x
    have e1 := hc (x * g)
    have e2 := ep (x * κ)
    rw [eg x] at e1
    rw [mul_assoc, hkp, ← mul_assoc, e1, hc x] at e2
    simpa using e2
  apply hχg
  have k0 := key x0
  rw [smul_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at k0
  rcases k0 with k0 | k0
  · apply Units.ext
    have : c * (((χ ⟨g, hgJ⟩ : ℂˣ) : ℂ) - 1) = 0 := by rw [mul_sub, mul_one]; exact k0
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hc0
    · simpa [sub_eq_zero] using h'
  · exact absurd k0 hx0

end GlobalTheory.ParaRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormFieldSquareClass
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem nfSq_of_fieldDat : GlobalTheory.NormSum.IntSt → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.TorEx → GlobalTheory.SqTop.BotSmall → NFSq := by
  intro hI hFD hTE hBS
  obtain ⟨CF0, h⟩ := GlobalTheory.SqTop.SqField.gBig_and hFD (GlobalTheory.SqTop.SqField.gBig_and hTE hBS)
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨x₀, fun D large₂ he hx hR T L μ₀ hμ G => ?_⟩
  obtain ⟨⟨_, _, _, _, hΛ⟩, hT, hQ, -, hB⟩ := h C0 le_rfl D large₂ he hx hR T L μ₀ hμ G
  exact GlobalTheory.SqTop.SqField.sqIn_of G μ₀ hI hΛ
    (fun i j s h1 h2 c => let ⟨x, a, b, _, d⟩ := hT i j s h1 h2 c; ⟨x, a, b, d⟩) hQ hB

end GlobalTheory.Mem.LiteralAutomorphy

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHeckeOfSideRead
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ValQ

theorem tameVal_eq_locK (hGAR : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (i : D.ntw.Tw) (k : ℕ)
    (e : NX.Kk D i k →+* ℂ) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (χ : HChar D.host.E)
    (hR : ReadsHecke e ψ χ) (hopen : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)))
    (hord : ∀ σ, ∃ N : ℕ, ψ σ ^ (D.ntw.l i ^ N) = 1) (P' : PlE D.host)
    (hl : ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal) (a : 𝓞 D.host.E) (y : D.host.Eˣ)
    (ha : a ∉ P'.asIdeal) (hy : (y : D.host.E) = (a : D.host.E)) :
    e (NX.ofOk D i k (NX.tameVal ψ P' 1 a).1) = ((χ.locK P' y : ℂˣ) : ℂ) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨art, hart, hH⟩ := hR
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver D.nd.Om P'
  obtain ⟨hq2, hq1⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P'
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ0 : 𝓞 D.host.E, ϖ0 ∈ P'.asIdeal ∧ ϖ0 ∉ P'.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P'.asIdeal) P'.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E))
    (show 0 < normV P' - 1 by omega)
  have hxu : IsUnitAt P' (atFin P' y) := by
    show Valued.v (((y : D.host.E) : P'.adicCompletion D.host.E)) = 1
    rw [hy, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 ha
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art hart
    P' A hA ϖ hϖ1 hϖ2 π hπ (atFin P' y) a hxu (by simp [atFin, hy])
  have hTR : NX.TameRep P' 1 σ a := ⟨A, hA, hσI, ϖ, π, hϖ1, hϖ2, hπ, by simpa using hσval⟩
  have hI : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' → ∀ σ ∈ Ine (F := D.host.E) A,
      ∃ N : ℕ, ψ σ ^ (D.ntw.l i ^ N) = 1 := fun _ _ σ _ => hord σ
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep ψ P' 1 (D.ntw.l i) hopen hl hI σ a ha hTR]
  have h1 := hH _ σ hσart.symm
  exact (congrArg (fun z : ℂˣ => (z : ℂ)) h1).symm

end GlobalTheory.LevCmp.ValQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBaseStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_at_reference_tuple_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → z.R.toRealDat.ExAt → RSide z Wt' R' → IdemSame z Xg → LiftAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  first | exact @GlobalTheory.Mem.R3.Rw.LiftExt.liftAt_of_rSide | exact GlobalTheory.Mem.R3.Rw.LiftExt.liftAt_of_rSide | (intros; apply GlobalTheory.Mem.R3.Rw.LiftExt.liftAt_of_rSide <;> assumption)
end

