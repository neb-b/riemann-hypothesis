module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0782
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OmegaQEqGaussMulFlatTransform
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatForm

open GlobalTheory.FlatConj

theorem gaussGL_inv {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ) :
    gaussGL ψ⁻¹ ξ⁻¹ r = (starRingEnd ℂ) (gaussGL ψ ξ r) := by
  unfold gaussGL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, AddChar.inv_apply, AddChar.map_neg_eq_conj]
  congr 1
  set u := Matrix.GeneralLinearGroup.det x
  have h1 : ((ξ u : ℂˣ) : ℂ) ^ Fintype.card kˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  have h2 : ‖((ξ u : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 Fintype.card_ne_zero
  rw [MonoidHom.inv_apply, inv_inv, Units.val_inv_eq_inv_val, map_inv₀, ← Complex.inv_eq_conj h2, inv_inv]

theorem gaussGL_mul_inv {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) :
    gaussGL ψ ξ r * gaussGL ψ⁻¹ ξ⁻¹ r = (Fintype.card k : ℂ) ^ (r ^ 2) := by
  obtain ⟨hnorm, -⟩ := _root_.GlobalTheory.complexMatrixGaussSum_norm_integral_galois k ψ ξ r hψ hξ (gaussGL ψ ξ r) rfl
  rw [gaussGL_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  push_cast
  rfl

theorem gaussGL_ne_zero {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) : gaussGL ψ ξ r ≠ 0 := fun h => by
  have := gaussGL_mul_inv ψ ξ r hψ hξ
  rw [h, zero_mul] at this
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) this.symm

theorem fourier_flat (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r t : ℕ) (hψ : ψ.IsPrimitive)
    (hξ : ξ ≠ 1) (u : Matrix (Fin (r + t)) (Fin r) k) :
    (∑ y : Matrix (Fin r) (Fin (r + t)) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
      ψ (Matrix.trace (y * u))) = ((Fintype.card k : ℂ) ^ ((r + t) * r) * (gaussGL ψ ξ r)⁻¹) *
      (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  have hψ' : (ψ⁻¹).IsPrimitive := addChar_inv_isPrimitive_of_isPrimitive ψ hψ
  have hξ' : ξ⁻¹ ≠ 1 := inv_ne_one.mpr hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'
  have hmul := gaussGL_mul_inv ψ ξ r hψ hξ
  have hne := gaussGL_ne_zero ψ ξ r hψ hξ
  set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hC : q ^ ((r + t) * r) * (gaussGL ψ ξ r)⁻¹ = q ^ (r * t) * G := by
    have hG' : gaussGL ψ⁻¹ ξ⁻¹ r = G := rfl
    rw [hG'] at hmul
    rw [show (r + t) * r = r * t + r ^ 2 by ring, pow_add, ← hmul]
    field_simp
  rw [hC]
  set u₁ := u.submatrix (Fin.castAdd t) id
  set u₂ := u.submatrix (Fin.natAdd r) id
  have hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k,
      ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) *
        ψ (trace (p.2 * u₂)) =
      (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (Matrix.trace (squareAndRectColumnsEquivWideMatrix p * u)) := by
    intro p
    have e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1 :=
      congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    have e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2 :=
      congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    rw [mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]
  rw [← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]
  rw [show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k,
      (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) *
        ψ (trace ((x, y).2 * u₂))) =
      (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (trace (x * u₁))) * ∑ y : Matrix (Fin r) (Fin t) k, ψ (trace (y * u₂)) by
    rw [Finset.sum_mul_sum]]
  rw [sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]
  by_cases hu2 : u₂ = 0
  swap
  · rw [if_neg hu2, mul_zero, dite_eq_right (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]
  rw [if_pos hu2]
  by_cases hdet : IsUnit u₁.det
  swap
  · have h0 : u₁.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    rw [hsing u₁ h0, zero_mul, dite_eq_right, mul_zero]
    rintro ⟨-, h⟩
    rw [topLeftBlock_eq_submatrix_castAdd] at h
    exact hdet h
  have hh : LowZero r u ∧ IsUnit (topL r u).det := ⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩
  rw [dif_pos hh]
  set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero
  have ha := hinv a
  simp only [Matrix.one_mul] at ha
  have hau : (a : Matrix (Fin r) (Fin r) k) = u₁ := rfl
  rw [hau] at ha
  rw [ha, ← hG]
  have hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a := Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])
  rw [hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]
  ring

theorem gaussP_ne_zero {E : Type} [Field E] [NumberField E] (PP : Pl E) (ψ : AddChar (kP PP) ℂ) (ξ : (kP PP)ˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) : gaussP PP ψ ξ r ≠ 0 :=
  @gaussGL_ne_zero (kP PP) (resField PP) (resFintype PP) ψ ξ r hψ hξ

theorem omegaQ_eq_gauss_mul_flat_transform (D : D7) [inst : ∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n : ℕ) (hrn : r ≤ n)
    (hQ : ∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1) (ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaQ Q r ξ (-1) ub = (∏ PP ∈ Q, ((Nat.card (kP PP) : ℂ) ^ (n * r) * (gaussP PP (ψP PP) (ξ PP) r)⁻¹))⁻¹ *
      ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)),
        omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) *
          ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  obtain rfl : inst = fun PP => resFintype PP := Subsingleton.elim _ _
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => resFintype PP
  let fl : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin (r + t)) (kP PP) → ℂ := fun PP y =>
    if h : IsUnit (topL r y).det then ((ξ PP h.unit : ℂˣ) : ℂ) else 0
  let fq : ∀ PP : Pl D.host.E, Matrix (Fin (r + t)) (Fin r) (kP PP) → ℂ := fun PP u =>
    if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  let C : Pl D.host.E → ℂ := fun PP => (Nat.card (kP PP) : ℂ) ^ ((r + t) * r) * (gaussP PP (ψP PP) (ξ PP) r)⁻¹
  have hC0 : ∀ PP : ↥Q, C PP ≠ 0 := fun PP =>
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
      (inv_ne_zero (gaussP_ne_zero _ _ _ _ (hQ _ PP.2).1 (hQ _ PP.2).2))
  have hCe : ∀ (PP : ↥Q) (u : Matrix (Fin (r + t)) (Fin r) (kP PP.1)),
      (∑ y : Matrix (Fin r) (Fin (r + t)) (kP PP.1), fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * u))) = C PP * fq PP.1 u := by
    intro PP u
    have := @fourier_flat (kP PP.1) (resField PP.1) (resFintype PP.1) (ψP PP.1) (ξ PP.1) r t (hQ _ PP.2).1 (hQ _ PP.2).2 u
    rw [← Nat.card_eq_fintype_card] at this
    exact this
  have hq : omegaQ Q r ξ (-1) ub = ∏ PP : ↥Q, fq PP.1 (ub PP.1) := by
    rw [← Finset.attach_eq_univ]
    unfold omegaQ
    convert GlobalTheory.FlatFourierQ.dite_prod' Q (fun PP => LowZero r (ub PP) ∧ IsUnit (topL r (ub PP)).det)
      (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
  have hf : ∀ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin (r + t)) (kP PP.1)),
      omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) = ∏ PP : ↥Q, fl PP.1 (-(y PP)) := by
    intro y
    have e0 : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin (r + t)) (kP PP),
        omegaFlat Q r ξ Y = ∏ PP ∈ Q.attach, fl PP.1 (Y PP.1) := by
      intro Y
      unfold omegaFlat
      convert GlobalTheory.FlatFourierQ.dite_prod' Q (fun PP => IsUnit (topL r (Y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
    rw [e0, Finset.attach_eq_univ]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [dif_pos PP.2, Subtype.coe_eta]
  have hprod : (∏ PP ∈ Q, C PP) = ∏ PP : ↥Q, C PP := (Finset.prod_coe_sort Q C).symm
  show _ = (∏ PP ∈ Q, C PP)⁻¹ * _
  simp only [hf, ← Finset.prod_mul_distrib]
  have hs := Finset.prod_univ_sum (t := fun (PP : ↥Q) => (Finset.univ : Finset (Matrix (Fin r) (Fin (r + t)) (kP PP.1))))
    (f := fun (PP : ↥Q) (y : Matrix (Fin r) (Fin (r + t)) (kP PP.1)) => fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * ub PP.1)))
  rw [Fintype.piFinset_univ] at hs
  rw [← hs]
  simp only [hCe]
  rw [hprod, Finset.prod_mul_distrib (f := fun PP : ↥Q => C PP) (g := fun PP : ↥Q => fq PP.1 (ub PP.1)), hq, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun PP _ => hC0 PP), one_mul]

end GlobalTheory.FlatForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceTwistTrivialOnCongruentUnits
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open GlobalTheory.ExportSeries

namespace GlobalTheory.OnePlaceCong

def locU {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) : Rˣ where
  val := 1 - g + g * x
  inv := 1 - g + g * (x⁻¹ : Rˣ)
  val_inv := by
    have h := x.mul_inv
    linear_combination (-((x : R) + (x⁻¹ : Rˣ) - 2)) * hg + g * g * h
  inv_val := by
    have h := x.inv_mul
    linear_combination (-((x : R) + (x⁻¹ : Rˣ) - 2)) * hg + g * g * h

theorem coe_locU {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) :
    ((locU g hg x : Rˣ) : R) = 1 - g + g * x := rfl

theorem locU_inv {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) :
    (locU g hg x)⁻¹ = locU g hg x⁻¹ := rfl

variable {D : D7}

theorem finPart_locU_mem {g : AE D} (hg : g * g = g) {z : (AE D)ˣ} (hz : finPart D (z : AE D) ∈ intAE D) :
    finPart D ((locU g hg z : (AE D)ˣ) : AE D) ∈ intAE D := by
  have h1 : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1)
  have hfg : finPart D g ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hg])
  rw [coe_locU, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul]
  exact add_mem (sub_mem h1 hfg) (GlobalTheory.HeckeConj.mul_mem_intAE D hfg hz)

theorem res_locU_eq_one {A : Type} [CommGroup A] {PP : Pl D.host.E} {χ : (AE D)ˣ →* A} {c : (kP PP)ˣ →* A}
    (hχ : IsResAt χ PP c) (hI : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) (N : ℕ)
    (hN : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (x : (AE D)ˣ) (hx : finPart D (x : AE D) ∈ intAE D)
    (y : Af D.host.F ⊗[D.host.F] D.host.E) (hy : y ∈ intAE D) (hxy : finPart D (x : AE D) - 1 = N • y) :
    χ (locU (idemAt PP) hI.1.1 x) = 1 := by
  have he : idemAt PP * idemAt PP = idemAt PP := hI.1.1
  have hfa := finPart_locU_mem he hx
  have hxa := GlobalTheory.IdemRes.toEAf_mem_of_finPart hfa
  obtain ⟨hE, hres⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP hI
  obtain ⟨w, rfl⟩ := GlobalTheory.SplitDualLat.finPart_surjective (D := D) y
  have hX := GlobalTheory.IdemRes.toEAf_mem_of_finPart hx
  have hW := GlobalTheory.IdemRes.toEAf_mem_of_finPart hy
  have key0 : Formalism.IndefR.Datum.toEAf D ((x : AE D) - 1 - N • w) = 0 := by
    change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D _) = 0
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul, hxy, sub_self, map_zero]
  have key : Formalism.IndefR.Datum.toEAf D (x : AE D) = 1 + N • Formalism.IndefR.Datum.toEAf D w := by
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul] at key0
    linear_combination key0
  have ha : (⟨Formalism.IndefR.Datum.toEAf D (locU (idemAt PP) he x : AE D), hxa⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      1 - ⟨_, hE⟩ + ⟨_, hE⟩ * (1 + N • ⟨_, hW⟩) := by
    apply Subtype.ext
    change Formalism.IndefR.Datum.toEAf D (1 - idemAt PP + idemAt PP * (x : AE D)) =
      1 - Formalism.IndefR.Datum.toEAf D (idemAt PP) + Formalism.IndefR.Datum.toEAf D (idemAt PP) *
        (1 + N • Formalism.IndefR.Datum.toEAf D w)
    rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, key]
  have hN0 : ((N : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hN
  refine (hχ _ ?_ hxa 1 ?_).trans (map_one c)
  · change (1 - idemAt PP) * (1 - idemAt PP + idemAt PP * (x : AE D)) = 1 - idemAt PP
    linear_combination (-((x : AE D) - 1)) * he
  · rw [ha, map_add (f := _), map_sub, map_one, map_mul, hres, map_add (f := _), map_one, map_nsmul, nsmul_eq_mul, hN0]
    simp

theorem chi_eq_one_of_cong : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := by
  intro D A _ PP χ κ ht N hN x hx hxy
  obtain ⟨y, hy, hxy⟩ := hxy
  have hPP : PP ∈ ({PP} : Finset (Pl D.host.E)) := Finset.mem_singleton_self PP
  have hsp : SplitSet ({PP} : Finset (Pl D.host.E)) := ht.split
  have hI := hsp.isIdemAt hPP
  have he : idemAt PP * idemAt PP = idemAt PP := hI.1.1
  have h0 : idemAt PP * cA D (idemAt PP) = 0 := hsp.mul_conj hPP hPP
  have hc : cA D (idemAt PP) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← RingHom.map_mul, he]
  have hg : (1 - idemAt PP - cA D (idemAt PP)) * (1 - idemAt PP - cA D (idemAt PP)) =
      1 - idemAt PP - cA D (idemAt PP) := by
    linear_combination he + hc + 2 * h0
  have hres := ht.res PP hPP

  have hx_eq : x = locU (idemAt PP) he x * locU (cA D (idemAt PP)) hc x *
      locU (1 - idemAt PP - cA D (idemAt PP)) hg x := by
    apply Units.ext
    simp only [Units.val_mul, coe_locU]
    linear_combination ((x : AE D) - 1) ^ 2 * he + ((x : AE D) - 1) ^ 2 * hc +
      (((x : AE D) - 1) ^ 2 - (1 - idemAt PP - cA D (idemAt PP)) * ((x : AE D) - 1) ^ 3) * h0

  have hA : χ (locU (idemAt PP) he x) = 1 := res_locU_eq_one hres hI N hN x hx.2.1 y hy hxy

  have hB : χ (locU (cA D (idemAt PP)) hc x) = 1 := by
    have hcb : Units.map (cA D).toMonoidHom (locU (cA D (idemAt PP)) hc x) =
        locU (idemAt PP) he (Units.map (cA D).toMonoidHom x) := by
      apply Units.ext
      change cA D (1 - cA D (idemAt PP) + cA D (idemAt PP) * (x : AE D)) = 1 - idemAt PP + idemAt PP * cA D (x : AE D)
      rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, Formalism.L2.Theta.cA_cA]
    have h1 : χ (locU (idemAt PP) he (Units.map (cA D).toMonoidHom x)) = 1 := by
      refine res_locU_eq_one hres hI N hN _ ?_ (sigR (Af D.host.F) D.sp.cm.sig y)
        (GlobalTheory.SplitDualLat.sigR_mem_intAE hy) ?_
      · change finPart D (cA D (x : AE D)) ∈ intAE D
        rw [GlobalTheory.SplitDualLat.finPart_cA]
        exact GlobalTheory.SplitDualLat.sigR_mem_intAE hx.2.1
      · change finPart D (cA D (x : AE D)) - 1 = _
        rw [GlobalTheory.SplitDualLat.finPart_cA, ← RingHom.map_one (sigR (Af D.host.F) D.sp.cm.sig), ← RingHom.map_sub, hxy,
          map_nsmul]
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      intro x
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add (f := _), hσ, add_comm]
    set b := locU (cA D (idemAt PP)) hc x with hb
    have hz : sigR (AF D.host.F) D.sp.cm.sig ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) =
        ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) := by
      change cA D ((b : AE D) * cA D (b : AE D)) = (b : AE D) * cA D (b : AE D)
      rw [RingHom.map_mul, Formalism.L2.Theta.cA_cA, mul_comm]
    obtain ⟨a, ha⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr _ hz
    have hr : χ (idF D a) = 1 := ht.real a
    have ha' : idF D a = b * Units.map (cA D).toMonoidHom b := ha
    rw [ha', map_mul, hcb, h1, mul_one] at hr
    exact hr

  have hC : χ (locU (1 - idemAt PP - cA D (idemAt PP)) hg x) = 1 := by
    have hi0 : infPart D (idemAt PP) = 0 := SpecGood.infPart_eq_zero_of_isIdemAt D PP _ hI
    have hi1 : infPart D (cA D (idemAt PP)) = 0 := by
      rw [GlobalTheory.PlaceIdem.infPart_cA, hi0, RingHom.map_zero]
    have hidem : idem ({PP} : Finset (Pl D.host.E)) = idemAt PP := Finset.sum_singleton _ _
    refine ht.unram _ ?_ (finPart_locU_mem hg hx.2.1) ?_ ?_
    · rw [coe_locU, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_sub,
        RingHom.map_one, hi0, hi1, hx.1]
      ring
    · rw [locU_inv]
      exact finPart_locU_mem hg hx.2.2
    · change (idem ({PP} : Finset (Pl D.host.E)) + cA D (idem ({PP} : Finset (Pl D.host.E)))) *
        (1 - (1 - idemAt PP - cA D (idemAt PP)) + (1 - idemAt PP - cA D (idemAt PP)) * (x : AE D)) = _
      rw [hidem]
      linear_combination (-((x : AE D) - 1)) * he + (-((x : AE D) - 1)) * hc + (-2 * ((x : AE D) - 1)) * h0
  rw [hx_eq, map_mul, map_mul, hA, hB, hC, mul_one, mul_one]

end GlobalTheory.OnePlaceCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealComponentEqConjInverseRationalMatrix
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.ArchRatComp

theorem compAt_mt_eq_map_inv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (γ a : GA D V) (γ' : GL (Fin V.rank) D.host.E),
    γ ∈ GQ V → GlobalTheory.Member.IsRat V γ γ' → a ∈ GinfC V → γ * a ∈ GfC V → ∀ τ : D.what₂.Tau, ∃ σ : D.host.E →+* ℂ,
      Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) = ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map σ := by
  intro D θ _ V γ a γ' _ hrat _ hfc τ
  refine ⟨(θ τ).comp ((infPart D).comp (incA D)), ?_⟩
  have h1 : infHom V (γ * a) = 1 := hfc
  have h2 : infHom V a = (infHom V γ)⁻¹ := by
    rw [map_mul] at h1; exact eq_inv_of_mul_eq_one_right h1
  have h3 : infHom V γ = Formalism.UG.bc ((infPart D).comp (incA D)) γ' := by
    show (Formalism.UG.bc _) (matHom V γ) = _
    rw [hrat]
    ext i j
    rfl
  have h4 : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) = ((infHom V a).val).map (θ τ) := rfl
  rw [h4, h2, h3, ← map_inv]
  ext i j
  rfl

end GlobalTheory.ArchRatComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointActsOnThetaFockVacuaByDetPower
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.RealVacPow

open scoped ComplexOrder

theorem vacuum_det_power : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (p : ℕ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) p) →
    ∃ k : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f →
      (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f) →
      om (a, 1) f = (∏ τ, (Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)).det ^ k τ) • f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP p BW hB
  have hP1 := hP.1
  obtain ⟨η, hη⟩ := hP1.eta
  choose b hb using hP1.expW
  have hsW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ) := hP.2.2.2.2.2.2.2.1
  choose q hq1 hq using fun τ => GlobalTheory.OneMapRef.RealMove.detPlus_one (n := V.rank) (sW τ) (hsW τ).1
  refine ⟨fun τ => -(b τ) - (q τ : ℤ), fun a ha f hf hv => ?_⟩
  have hθ : IsInfFam θ := hP1.inf
  have hψ := hP1.weil.std
  have hgV : ∀ τ, gramAt D V τ = 1 := fun τ => by
    unfold gramAt; rw [hP1.std]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hS : ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun τ => by
    rw [hgV]; exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hdetV : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => by rw [hgV]; simp
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ V hdetV a ha
  have mt1 : Formalism.L2.Theta.mt W 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have hy : IsDetRoot W 1 1 := by
    unfold IsDetRoot
    have : ((matHom W 1).1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) = 1 := mt1
    rw [this, Matrix.det_one, one_mul, Units.val_one, map_one]
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := fun τ => by
    rw [mt1]; exact Matrix.map_one _ (by simp) (by simp)
  rw [GlobalTheory.WeilVacChar.vacuum_character D ψ hψ V W θ hθ χV χW om η hη hP1.weil (fun _ => 1) sW hS hsW a ha 1 (one_mem _)
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, Matrix.one_mul, Matrix.mul_one]) x 1 hx hy f hf hv]
  congr 1
  have hexp : ∀ τ, HasInfExp D (χW * (η ^ W.rank)⁻¹) τ ((b τ : ℤ) : ℚ) := fun τ => by
    have := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hb τ) (hη.2.2.2 τ) W.rank
    rwa [add_sub_cancel_right] at this
  have hνx := hxv _ b hexp
  have hinv : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)).det * (compAt θ τ (Formalism.L2.Theta.mt V a)).det = 1 := fun τ => by
    rw [GlobalTheory.OneMapRef.RealMove.det_compAt, GlobalTheory.OneMapRef.RealMove.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    have : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
      unfold Formalism.L2.Theta.mt; rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [this, Matrix.det_one, map_one, map_one]
  have hd0 : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V a)).det ≠ 0 := fun τ h => by
    have := hinv τ; rw [h, mul_zero] at this; exact zero_ne_one this
  have hdp : ∀ τ, GlobalTheory.WeilParts.detPlus 1 (sW τ) (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt W 1)) =
      ((compAt θ τ (Formalism.L2.Theta.mt V a)).det)⁻¹ ^ q τ := fun τ => by
    rw [one, (hq τ _ 1 (by rw [Matrix.one_mul, Matrix.mul_one])).1]
    have e : (1 / 2 : ℂ) • (1 + sW τ) * 1 + (1 / 2 : ℂ) • (1 - sW τ) = 1 := by rw [Matrix.mul_one]; module
    rw [e, Matrix.det_one, one_pow, one_mul, eq_inv_of_mul_eq_one_left (hinv τ)]
  rw [map_one, mul_one, Circle.coe_inv, hνx, Finset.prod_congr rfl fun τ _ => hdp τ, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [zpow_sub₀ (hd0 τ), _root_.zpow_neg, zpow_natCast, inv_pow, div_eq_mul_inv]

end GlobalTheory.RealVacPow

end
end

