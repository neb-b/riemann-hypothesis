module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbVal
section
noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbCut

open MeasureTheory Formalism.MainNotions.S Formalism.L2.SG.Pf.LocOrbSumPf
open Classical

section Cast

variable {K : Type} [CommRing K]

theorem sLow_cast {n n' : ℕ} (h : n' = n) (A : Matrix (Fin n) (Fin n) K) :
    Formalism.DoubleCosetMeasures.sLow (A.submatrix (finCongr h) (finCongr h)) = Formalism.DoubleCosetMeasures.sLow A := by
  subst h
  rfl

theorem sUp_cast {n n' : ℕ} (h : n' = n) (A : Matrix (Fin n) (Fin n) K) :
    Formalism.DoubleCosetMeasures.sUp (A.submatrix (finCongr h) (finCongr h)) = Formalism.DoubleCosetMeasures.sUp A := by
  subst h
  rfl

theorem lowUni_cast {n n' : ℕ} (h : n' = n) {A : Matrix (Fin n) (Fin n) K} (hA : Formalism.DoubleCosetMeasures.IsLowUni A) :
    Formalism.DoubleCosetMeasures.IsLowUni (A.submatrix (finCongr h) (finCongr h)) := by
  subst h
  exact hA

theorem upUni_cast {n n' : ℕ} (h : n' = n) {A : Matrix (Fin n) (Fin n) K} (hA : Formalism.DoubleCosetMeasures.IsUpUni A) :
    Formalism.DoubleCosetMeasures.IsUpUni (A.submatrix (finCongr h) (finCongr h)) := by
  subst h
  exact hA

theorem sLow_one {n : ℕ} : Formalism.DoubleCosetMeasures.sLow (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [Formalism.DoubleCosetMeasures.sLow, Matrix.one_apply, Fin.ext_iff]

theorem sUp_one {n : ℕ} : Formalism.DoubleCosetMeasures.sUp (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [Formalism.DoubleCosetMeasures.sUp, Matrix.one_apply, Fin.ext_iff]

theorem sLow_mem (R : Subring K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ R) :
    Formalism.DoubleCosetMeasures.sLow A ∈ R := by
  unfold Formalism.DoubleCosetMeasures.sLow
  refine Subring.sum_mem R (fun j _ => ?_)
  split_ifs
  · exact hA _ _
  · exact R.zero_mem

theorem sUp_mem (R : Subring K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ R) :
    Formalism.DoubleCosetMeasures.sUp A ∈ R := by
  unfold Formalism.DoubleCosetMeasures.sUp
  refine Subring.sum_mem R (fun j _ => ?_)
  split_ifs
  · exact hA _ _
  · exact R.zero_mem

end Cast

section Val

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [IsTopologicalRing E]

theorem uLow_lowUni {n : ℕ} (x : Loc.IL n → E) : Formalism.DoubleCosetMeasures.IsLowUni (Loc.uLow x) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp only [Loc.uLow]
    rw [if_neg (ne_of_lt h'), dite_eq_right (not_lt.mpr h'.le)]
  · simp [Loc.uLow]

theorem uUp_upUni {n : ℕ} (w : Loc.Pt E n) (y : Loc.IN w → E) : Formalism.DoubleCosetMeasures.IsUpUni (Loc.uUp w y) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h' : j < i := hij
    simp only [Loc.uUp]
    rw [if_neg (ne_of_gt h'), dite_eq_right (fun h => absurd h.1 (not_lt.mpr h'.le))]
  · simp [Loc.uUp]

def rI {m : ℕ} (a : Loc.Pt E (m + 1)) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E :=
  B.submatrix (finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a)) (finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a))

theorem rI_mul {m : ℕ} (a : Loc.Pt E (m + 1)) (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    rI a (A * B) = rI a A * rI a B := by
  unfold rI
  rw [Matrix.submatrix_mul_equiv]

theorem rI_mat {m : ℕ} (a : Loc.Pt E (m + 1)) :
    rI a a.mat = Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
  unfold rI
  rw [Formalism.MainNotions.LocalModelPeriodLattices.mat_eq]
  ext i j
  simp

theorem rI_zQ {m : ℕ} (R : Subring E) (a : Loc.Pt E (m + 1)) (q : Formalism.FourierDecayAlt.A5.Cos R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) :
    rI a (zQ R a q) = Formalism.FourierDecayAlt.A5.orbZ (Formalism.MainNotions.LocalModelPeriodLattices.tr a) (Formalism.FourierDecayAlt.A5.rep R q) := by
  unfold rI zQ
  ext i j
  simp

theorem lowUni_rI {m : ℕ} (a : Loc.Pt E (m + 1)) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) E}
    (hA : Formalism.DoubleCosetMeasures.IsLowUni A) : Formalism.DoubleCosetMeasures.IsLowUni (rI a A) := lowUni_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) hA

theorem upUni_rI {m : ℕ} (a : Loc.Pt E (m + 1)) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) E}
    (hA : Formalism.DoubleCosetMeasures.IsUpUni A) : Formalism.DoubleCosetMeasures.IsUpUni (rI a A) := upUni_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) hA

theorem sLow_rI {m : ℕ} (a : Loc.Pt E (m + 1)) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Formalism.DoubleCosetMeasures.sLow (rI a A) = Formalism.DoubleCosetMeasures.sLow A := sLow_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) A

theorem sUp_rI {m : ℕ} (a : Loc.Pt E (m + 1)) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Formalism.DoubleCosetMeasures.sUp (rI a A) = Formalism.DoubleCosetMeasures.sUp A := sUp_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) A

theorem phase_eq (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1))
    (q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) (xy : (Loc.IL (m + 1) → E) × (Loc.IN a → E))
    (l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hq : zQ M.R a q = l * zAt a xy * ρ) :
    M.psiR (phQ M.R a q) = M.psiR (Loc.simpleLow (Loc.uLow xy.1) + Loc.simpleUp (Loc.uUp a xy.2)) := by
  have hψ : ∀ x ∈ M.R, M.psiR x = 1 := fun r hr => by
    simpa using (Formalism.MainNotions.LocalModelPeriodLattices.selfDual_of_core M hOK 1).2 M.R.one_mem r hr
  have hLo : Formalism.DoubleCosetMeasures.IsLowUni (rI a l * rI a (Loc.uLow xy.1)) :=
    Formalism.DoubleCosetMeasures.isLowUni_mul E (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))
  have hUp : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy.2) * rI a ρ) :=
    Formalism.DoubleCosetMeasures.isUpUni_mul E (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))
  have hv : Formalism.DoubleCosetMeasures.IsLowUni (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := (Formalism.FourierDecayAlt.A5.rep M.R q).1.2.1
  have hu : Formalism.DoubleCosetMeasures.IsUpUni (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := (Formalism.FourierDecayAlt.A5.rep M.R q).2.2
  have hvPu : (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) =
      (rI a l * rI a (Loc.uLow xy.1)) * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
        (rI a (Loc.uUp a xy.2) * rI a ρ) := by
    have h := congrArg (rI a) hq
    rw [rI_zQ] at h
    unfold zAt at h
    rw [rI_mul, rI_mul, rI_mul, rI_mul, rI_mat] at h
    unfold Formalism.FourierDecayAlt.A5.orbZ at h
    rw [h]
    simp only [Matrix.mul_assoc]
  have hLd : IsUnit (rI a l * rI a (Loc.uLow xy.1)).det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det E hLo]; exact isUnit_one
  have hUd : IsUnit (rI a (Loc.uUp a xy.2) * rI a ρ).det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det E hUp]; exact isUnit_one
  have hfix : ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
      ((((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) =
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
    calc _ = (rI a l * rI a (Loc.uLow xy.1))⁻¹ * ((((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a l * rI a (Loc.uLow xy.1))) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          ((rI a (Loc.uUp a xy.2) * rI a ρ) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) := by
          rw [hvPu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hLd, Matrix.mul_nonsing_inv _ hUd, Matrix.one_mul, Matrix.mul_one]
  have h0 := Formalism.DoubleCosetMeasures.Final.phaseWellDef E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 _ _
    (Formalism.DoubleCosetMeasures.isLowUni_mul E (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv) (Formalism.DoubleCosetMeasures.isUpUni_mul E hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)) hfix
  have sa := Formalism.DoubleCosetMeasures.Final.simpleAdd E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum
  rw [(sa _ _).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv, (sa _ _).2 hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)] at h0
  have hLi := (sa (rI a l * rI a (Loc.uLow xy.1))⁻¹ (rI a l * rI a (Loc.uLow xy.1))).1
    (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hLo
  rw [Matrix.nonsing_inv_mul _ hLd, sLow_one] at hLi
  have hUi := (sa (rI a (Loc.uUp a xy.2) * rI a ρ) (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹).2
    hUp (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)
  rw [Matrix.mul_nonsing_inv _ hUd, sUp_one] at hUi
  rw [(sa _ _).1 (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))] at hLi
  rw [(sa _ _).2 (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))] at hUi
  have hph : phQ M.R a q = Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) +
      (Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy.2))) := by
    unfold phQ
    linear_combination h0 + hLi + hUi
  have h1 : Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) ∈ M.R :=
    add_mem (by rw [sLow_rI]; exact sLow_mem M.R _ hl.2.2) (by rw [sUp_rI]; exact sUp_mem M.R _ hρ.2.2)
  rw [hph, AddChar.map_add_eq_mul, hψ _ h1, one_mul]
  rw [sLow_rI, sUp_rI, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq]

theorem nIso_orb (M : Loc.Model F E) {n : ℕ} {Z Z' : Matrix (Fin (n + 1)) (Fin (n + 1)) E}
    (l ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hZ : Z' = l * Z * ρ) (h1 : ∀ i j, Z' i j ∈ M.R) (h2 : IsUnit Z'.det) (h1' : ∀ i j, Z i j ∈ M.R)
    (h2' : IsUnit Z.det) (Z0 : M.Mat (n + 1)) :
    M.nIso (Formalism.MainNotions.LocalOrbitGerms.Cls.toMat M Z' h1 h2) Z0 = M.nIso (Formalism.MainNotions.LocalOrbitGerms.Cls.toMat M Z h1' h2') Z0 := by
  subst hZ
  unfold Loc.Model.nIso
  rw [Nat.card_congr (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv M _ Z0), Nat.card_congr (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv M _ Z0),
    Formalism.MainNotions.LocalOrbitGerms.Cls.toMat_map, Formalism.MainNotions.LocalOrbitGerms.Cls.toMat_map]
  exact Formalism.DoubleCosetMeasures.Final.isoInv E M.R (n + 1) l ρ Z (lowUni_of M hl) (upUni_of M hρ) hl.2.2 hρ.2.2 _ _ _

theorem val (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : IntegrandConstantOnOrbit M a c := by
  intro q xy hI hmem
  obtain ⟨l, ρ, hl, hρ, hq⟩ := hmem
  have hIq : ∀ i j, zQ M.R a q i j ∈ M.R := int_of_mem M hI ⟨l, ρ, hl, hρ, hq⟩
  have hdq : IsUnit (zQ M.R a q).det := Formalism.MainNotions.LocalOrbitGerms.Cls.isUnit_det_sub a _
  have hI' : ∀ i j, (Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2) i j ∈ M.R := hI
  have hdz : IsUnit (Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.L2.SG.Pf.LocModel.uLow_det, Formalism.L2.SG.Pf.LocModel.uUp_det, one_mul,
      mul_one, Formalism.MainNotions.LocalModelPeriodLattices.det_eq]
    exact Formalism.FourierDecayAlt.P.A5x6.pt_det_isUnit _
  rw [Formalism.MainNotions.LocalOrbitGerms.Cls.bbIntegrand_eq]
  unfold valQ Formalism.MainNotions.LocalOrbitGerms.Cls.GG
  rw [dite_eq_left ⟨hIq, hdq⟩, dite_eq_left ⟨hI', hdz⟩, phase_eq M hOK a q xy l ρ hl hρ hq,
    nIso_orb M l ρ hl hρ hq hIq hdq hI' hdz]
  rfl

end Val

end Formalism.L2.SG.Pf.LocOrbCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MkWEqOfSubMem
section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CorrProof

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem Dl_succ {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dite_eq_left le_rfl]
  congr 1

theorem mkW_eq_of_sub_mem {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))} (h : (x : V) - y ∈ H.X f) : H.mkW f x = H.mkW f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using h

theorem corrIso_holds (M : Model F E) (r n : ℕ) : CorrIso M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂
  obtain ⟨hg₁, hF₂, hF₂', hI, hz, hz'⟩ := hyp
  have hT1 := hg₁.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT1.2.1.2.1, hT1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT1.2.2.1.2.1, hT1.2.2.1.2.2.1⟩
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  obtain ⟨hIs, -, hW0c, hom', -, hκ⟩ := hI
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hκ
    have hN₁ : IsUnit (H.normE (H.Dl t₁.f t₁.f' (r + 1))) := hD₁.mul (hD₁.map M.L.cj)
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  have hU₁ := isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ hG₁
  have hU₂ := isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂ hG₂
  have hXU : ∀ g g' : Fin (r + 1) → V, H.X g ≤ Submodule.span E (Set.range (Sum.elim g g')) :=
    fun g g' => Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Sum.inl j.castSucc, rfl⟩)
  have huniq : ∀ (a b : V) (ha : a ∈ H.W0 f₂ f₂') (hb : b ∈ H.W0 f₂ f₂'),
      H.mkW f₂ ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H ha⟩ = H.mkW f₂ ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩ → a = b := by
    intro a b ha hb hab
    have h1 := sub_mem_X_of_mkW_eq H hab
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hU₂.disjoint) _ (hXU f₂ f₂' h1) (Submodule.sub_mem _ ha hb))
  have hex : ∀ w : ↥(H.W0 t₁.f t₁.f'), ∃ w₂ : ↥(H.W0 f₂ f₂'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ ∧
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW f₂' ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H w₂.2⟩ := by
    intro w
    obtain ⟨w₂, hw₂, s1, s2⟩ := hW0c w w.2
    refine ⟨⟨w₂, hw₂⟩, ?_, ?_⟩
    · have := s1 ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H hw₂⟩ rfl rfl
      simpa using this
    · have := s2 ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H hw₂⟩ rfl rfl
      simpa using this
  choose ψf hψf using hex
  have hψadd : ∀ a b, ψf (a + b) = ψf a + ψf b := by
    intro a b
    apply Subtype.ext
    apply huniq _ _ (ψf (a + b)).2 (ψf a + ψf b).2
    rw [← (hψf (a + b)).1]
    have e : (⟨((a + b : ↥(H.W0 t₁.f t₁.f')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (a + b).2⟩ : ↥(H.perp (H.X t₁.f))) =
        ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ + ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ := Subtype.ext rfl
    have e2 : (⟨((ψf a + ψf b : ↥(H.W0 f₂ f₂')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (ψf a + ψf b).2⟩ : ↥(H.perp (H.X f₂))) =
        ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩ + ⟨ψf b, mem_perp_isotropicSpan_of_mem_framePerp H (ψf b).2⟩ := Subtype.ext rfl
    rw [e, e2, map_add (f := _), map_add (f := _), map_add (f := _), (hψf a).1, (hψf b).1]
  have hψsmul : ∀ (c : E) a, ψf (c • a) = c • ψf a := by
    intro c a
    apply Subtype.ext
    apply huniq _ _ (ψf (c • a)).2 (c • ψf a).2
    rw [← (hψf (c • a)).1]
    have e : (⟨((c • a : ↥(H.W0 t₁.f t₁.f')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (c • a).2⟩ : ↥(H.perp (H.X t₁.f))) =
        c • ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ := Subtype.ext rfl
    have e2 : (⟨((c • ψf a : ↥(H.W0 f₂ f₂')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (c • ψf a).2⟩ : ↥(H.perp (H.X f₂))) =
        c • ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩ := Subtype.ext rfl
    rw [e, e2, map_smul, map_smul, map_smul, (hψf a).1]
  let ψL : ↥(H.W0 t₁.f t₁.f') →ₗ[E] ↥(H.W0 f₂ f₂') :=
    { toFun := ψf, map_add' := hψadd, map_smul' := hψsmul }
  have hinj : Function.Injective ψL := by
    intro a b hab
    have hab' : ψf a = ψf b := hab
    have e : H.mkW t₁.f ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ = H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ :=
      φ.injective (by rw [(hψf a).1, (hψf b).1, hab'])
    have h1 := sub_mem_X_of_mkW_eq H e
    exact Subtype.ext (sub_eq_zero.1 ((Submodule.disjoint_def.1 hU₁.disjoint) _ (hXU t₁.f t₁.f' h1)
      (Submodule.sub_mem _ a.2 b.2)))
  have hsurj : Function.Surjective ψL := by
    intro w₂
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ.symm (H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩))
    have hy' : φ (H.mkW t₁.f y) = H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ := by
      have : H.mkW t₁.f y = φ.symm (H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩) := hy
      rw [this, LinearEquiv.apply_symm_apply]
    have hyU : (y : V) ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')) ⊔ H.W0 t₁.f t₁.f' := by
      rw [hU₁.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hyU
    have hup : u ∈ H.perp (H.X t₁.f) := by
      have : u = (y : V) - w := by rw [← huw]; abel
      rw [this]
      exact Submodule.sub_mem _ y.2 (mem_perp_isotropicSpan_of_mem_framePerp H hw)
    have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
    obtain ⟨x, hx, β, γ, hxe⟩ := decomp_U_perpX H hF₁ hZ₁ hu hup
    refine ⟨⟨w, hw⟩, ?_⟩
    set D₂ := H.Dl f₂ f₂' (r + 1)
    set D₁ := H.Dl t₁.f t₁.f' (r + 1)
    let zP₁ : ↥(H.perp (H.X t₁.f)) := ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩
    let oP₁ : ↥(H.perp (H.X t₁.f)) := ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩
    let zP₂ : ↥(H.perp (H.X f₂)) := ⟨f₂ (Fin.last r), z_mem_perpX H hF₂⟩
    let oP₂ : ↥(H.perp (H.X f₂)) := ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩
    let wP : ↥(H.perp (H.X t₁.f)) := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩
    let vP : ↥(H.perp (H.X f₂)) := ⟨ψf ⟨w, hw⟩, mem_perp_isotropicSpan_of_mem_framePerp H (ψf ⟨w, hw⟩).2⟩
    have hq₁ : H.mkW t₁.f y = H.mkW t₁.f (β • zP₁ + γ • oP₁ + wP) := by
      apply mkW_eq_of_sub_mem
      show (y : V) - (β • t₁.f (Fin.last r) + γ • H.om' t₁.f t₁.f' + w) ∈ H.X t₁.f
      rw [← huw, hxe]
      convert hx using 1
      abel
    have hz1 : φ (H.mkW t₁.f zP₁) = H.mkW f₂ zP₂ := by
      have := hz zP₁ zP₂ rfl rfl
      simpa using this
    have ho0 : D₂ • φ (H.mkW t₁.f oP₁) = D₁ • H.mkW f₂ oP₂ := by
      have := hom' oP₁ oP₂ rfl rfl
      simpa using this
    have ho1 : φ (H.mkW t₁.f oP₁) = (Ring.inverse D₂ * D₁) • H.mkW f₂ oP₂ := by
      rw [mul_smul, ← ho0, smul_smul, Ring.inverse_mul_cancel _ hD₂, one_smul]
    have hw1 : φ (H.mkW t₁.f wP) = H.mkW f₂ vP := (hψf ⟨w, hw⟩).1
    have hq₂ : H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ =
        H.mkW f₂ (β • zP₂ + (γ * (Ring.inverse D₂ * D₁)) • oP₂ + vP) := by
      rw [← hy', hq₁]
      simp only [map_add (f := _), map_smul, hz1, ho1, hw1, smul_smul]
    have hd := sub_mem_X_of_mkW_eq H hq₂
    have hU2mem : (w₂ : V) - (ψf ⟨w, hw⟩ : V) ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')) := by
      have e : (w₂ : V) - (ψf ⟨w, hw⟩ : V) =
          ((w₂ : V) - ((β • zP₂ + (γ * (Ring.inverse D₂ * D₁)) • oP₂ + vP : ↥(H.perp (H.X f₂))) : V)) +
            (β • f₂ (Fin.last r) + (γ * (Ring.inverse D₂ * D₁)) • H.om' f₂ f₂') := by
        simp only [Submodule.coe_add, Submodule.coe_smul, zP₂, oP₂, vP]
        abel
      rw [e]
      exact Submodule.add_mem _ (hXU f₂ f₂' hd) (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
        (Submodule.smul_mem _ _ (om'_mem_U H f₂ f₂')))
    have h0 := (Submodule.disjoint_def.1 hU₂.disjoint) _ hU2mem (Submodule.sub_mem _ w₂.2 (ψf ⟨w, hw⟩).2)
    exact Subtype.ext (sub_eq_zero.1 h0).symm
  refine ⟨LinearEquiv.ofBijective ψL ⟨hinj, hsurj⟩, fun a b => ?_, fun n₁ n₂ => ?_⟩
  · show H.h ((ψf a : ↥(H.W0 f₂ f₂')) : V) ((ψf b : ↥(H.W0 f₂ f₂')) : V) = H.h a b
    exact hIs ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩
      ⟨ψf b, mem_perp_isotropicSpan_of_mem_framePerp H (ψf b).2⟩ (hψf a).1 (hψf b).1
  · constructor
    · rintro ⟨h₁, h₂, c1, -⟩
      refine ⟨h₁, ?_⟩
      show ((ψf ⟨n₁, h₁⟩ : ↥(H.W0 f₂ f₂')) : V) = n₂
      exact huniq _ _ (ψf ⟨n₁, h₁⟩).2 h₂ ((hψf ⟨n₁, h₁⟩).1.symm.trans c1)
    · rintro ⟨h₁, rfl⟩
      exact ⟨h₁, (ψf ⟨n₁, h₁⟩).2, (hψf ⟨n₁, h₁⟩).1, (hψf ⟨n₁, h₁⟩).2⟩

end CorrProof

end Formalism.L2.SG.LsDatumA
end
end

