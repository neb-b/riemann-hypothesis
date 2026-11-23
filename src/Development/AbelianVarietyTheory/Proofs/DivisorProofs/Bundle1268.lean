module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHomConjInverseTransposeAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocHomV

open GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem one_sub_mul_eq_zero (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) (t : L) :
    (1 - ι 1) * ι t = 0 := by
  rw [sub_mul, one_mul, ← hmul, one_mul, sub_self]

theorem idem (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) :
    (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
  rw [mul_sub, mul_one, one_sub_mul_eq_zero ι hmul, sub_zero]

theorem map_mul_map (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) L) : X.map ι * Y.map ι = (X * Y).map ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, map_sum, hmul]

theorem smul_map_eq_zero (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) L) : (1 - ι 1) • X.map ι = 0 := by
  ext i j
  simp [smul_eq_mul, one_sub_mul_eq_zero ι hmul]

def Am {n : ℕ} (P g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  (P : Matrix (Fin n) (Fin n) L) * ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
    ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

def Mg (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n : ℕ} (P g : GL (Fin n) L) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (Am P g).map ι

theorem Am_mul {n : ℕ} (P g g' : GL (Fin n) L) : Am P g * Am P g' = Am P (g * g') := by
  unfold Am
  calc _ = (P : Matrix (Fin n) (Fin n) L) * ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
        (((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L)) *
        ((g'⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Units.inv_mul, Matrix.mul_one, mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]

theorem Am_one {n : ℕ} (P : GL (Fin n) L) : Am P 1 = 1 := by
  simp [Am]

theorem Mg_mul (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ} (P g g' : GL (Fin n) L) :
    Mg ι P g * Mg ι P g' = Mg ι P (g * g') := by
  unfold Mg
  rw [add_mul, mul_add, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul, smul_smul,
    idem ι hmul, smul_map_eq_zero ι hmul, Matrix.mul_smul, Matrix.mul_one, smul_map_eq_zero ι hmul,
    map_mul_map ι hmul, Am_mul, add_zero, zero_add]

theorem Mg_one (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n : ℕ} (P : GL (Fin n) L) : Mg ι P 1 = 1 := by
  unfold Mg
  rw [Am_one]
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

def Phi (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ} (P : GL (Fin n) L) :
    GL (Fin n) L →* GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun g := ⟨Mg ι P g, Mg ι P g⁻¹, by rw [Mg_mul ι hmul, mul_inv_cancel, Mg_one],
    by rw [Mg_mul ι hmul, inv_mul_cancel, Mg_one]⟩
  map_one' := Units.ext (Mg_one ι P)
  map_mul' g g' := Units.ext (Mg_mul ι hmul P g g').symm

theorem key (σL : L →+* L) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n : ℕ} (P JS g : GL (Fin n) L) (J : Matrix (Fin n) (Fin n) E)
    (hJ : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = gram σL ι P J)
    (hg : Formalism.UG.cT σL (g : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * g = JS) :
    (Am P g)ᵀ * tJ ι J * (Am P g).map σL = tJ ι J := by
  have hpp : ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul P
  have hpp' : (P : Matrix (Fin n) (Fin n) L) * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv P
  have hσp' : (P : Matrix (Fin n) (Fin n) L).map σL * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL = 1 := by
    rw [← Matrix.map_mul, hpp', Matrix.map_one _ (map_zero σL) (map_one σL)]
  have hKK : (JS : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv JS
  have hKK' : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul JS
  have hgg : ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul g
  have huu : (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ * ((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σL) (map_one σL),
      Matrix.transpose_one]
  have hT : tJ ι J = ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL := by
    rw [hJ, gram]
    calc tJ ι J = (((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * (P : Matrix (Fin n) (Fin n) L)ᵀ) * tJ ι J *
        ((P : Matrix (Fin n) (Fin n) L).map σL * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL) := by
          rw [← Matrix.transpose_mul, hpp', Matrix.transpose_one, Matrix.one_mul, hσp', Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hKi : ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ = ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    have hg' : ((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ * (JS : Matrix (Fin n) (Fin n) L) * g = JS := hg
    calc _ = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ *
          ((JS : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
            rw [hKK, Matrix.mul_one]
      _ = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ *
          (((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ * (JS : Matrix (Fin n) (Fin n) L) * g *
            ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by rw [hg']
      _ = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ * ((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ) *
          (JS : Matrix (Fin n) (Fin n) L) * g * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by
            rw [huu, Matrix.mul_one, Matrix.mul_assoc ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), hKK',
              Matrix.mul_one, hgg, Matrix.one_mul]
  calc (Am P g)ᵀ * tJ ι J * (Am P g).map σL
      = ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
        (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((P : Matrix (Fin n) (Fin n) L)ᵀ * tJ ι J * (P : Matrix (Fin n) (Fin n) L).map σL) *
          (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ) *
        ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL := by
          simp only [Am, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map,
            Matrix.mul_assoc]
    _ = tJ ι J := by rw [← gram, ← hJ, hKi, ← hT]

theorem mem (σ : E →ₐ[F] E) (v : Pl (F := F)) (σL : L →+* L) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (hsupp : ∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (hσ : ∀ x, ι (σL x) = cA σ (ι x)) {n : ℕ} (P JS g : GL (Fin n) L) (J : Matrix (Fin n) (Fin n) E)
    (hJ : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = gram σL ι P J)
    (hg : Formalism.UG.cT σL (g : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * g = JS) :
    (Mg ι P g)ᵀ * incM F J * (Mg ι P g).map (cA σ) = incM F J := by
  have hce : cA σ (ι 1) = ι 1 := by rw [← hσ, map_one]
  have hMT : (Mg ι P g)ᵀ = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (Am P g)ᵀ.map ι := by
    simp [Mg, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_map]
  have hMc : (Mg ι P g).map (cA σ) =
      (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + ((Am P g).map σL).map ι := by
    ext i j
    by_cases h : i = j <;> simp [Mg, h, Matrix.one_apply, ← hσ, hce]
  have hsplit : incM F J = (1 - ι 1) • incM F J + (tJ ι J).map ι := by
    ext i j
    have hex : ∃ x, ι x = ι 1 * inclR (F := F) (AF F) (J i j) := (hsupp _).1 (fun u hu => by
      rw [← smul_mul_assoc, (hsupp (ι 1)).2 ⟨1, rfl⟩ u hu, zero_mul])
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, incM, tJ]
    rw [pre_spec ι hex]
    ring
  have h1 : (Am P g)ᵀ.map ι * incM F J = ((Am P g)ᵀ * tJ ι J).map ι := by
    calc (Am P g)ᵀ.map ι * incM F J = (Am P g)ᵀ.map ι * ((1 - ι 1) • incM F J + (tJ ι J).map ι) := by
          rw [← hsplit]
      _ = ((1 - ι 1) • (Am P g)ᵀ.map ι) * incM F J + (Am P g)ᵀ.map ι * (tJ ι J).map ι := by
          rw [Matrix.mul_add, Matrix.mul_smul, ← Matrix.smul_mul]
      _ = _ := by rw [smul_map_eq_zero ι hmul, Matrix.zero_mul, zero_add, map_mul_map ι hmul]
  have hL : (Mg ι P g)ᵀ * incM F J = (1 - ι 1) • incM F J + ((Am P g)ᵀ * tJ ι J).map ι := by
    rw [hMT, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, h1]
  have e1 : ((1 - ι 1) • incM F J) * ((1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) = (1 - ι 1) • incM F J := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, idem ι hmul]
  have e2 : ((1 - ι 1) • incM F J) * ((Am P g).map σL).map ι = 0 := by
    rw [Matrix.smul_mul, ← Matrix.mul_smul, smul_map_eq_zero ι hmul, Matrix.mul_zero]
  have e3 : ((Am P g)ᵀ * tJ ι J).map ι * ((1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) = 0 := by
    rw [Matrix.mul_smul, Matrix.mul_one, smul_map_eq_zero ι hmul]
  rw [hL, hMc, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, map_mul_map ι hmul,
    key σL ι P JS g J hJ hg, add_zero, zero_add, ← hsplit]

theorem exists_homV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] (σL : L →+* L)
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      ∀ (P JS : GL (Fin n) L), ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι P X.J →
      ∃ iV : Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L) →* UA σ X.J, ∀ g,
        mat (iV g) = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι := by
  intro F E _ _ _ _ _ σ v n X L _ σL ι hsupp hmul hσ P JS hJ
  exact ⟨((Phi ι hmul P).comp (Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L)).subtype).codRestrict
    (UG (cA σ) (incM F X.J)) (fun g => mem σ v σL ι hsupp hmul hσ P JS g.1 X.J hJ g.2), fun g => rfl⟩

end GlobalTheory.InertLocHomV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHomFrameConjugationAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame.HomW

section Idem

variable {R L : Type} [CommRing R] [Field L] {n : ℕ} (ι : L →+ R) (hm : ∀ x y, ι (x * y) = ι x * ι y)
include hm

theorem map_mul_map (X Y : Matrix (Fin n) (Fin n) L) : X.map ι * Y.map ι = (X * Y).map ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hm]

theorem e_mul (t : L) : ι 1 * ι t = ι t := by rw [← hm, one_mul]

theorem f_mul (t : L) : (1 - ι 1) * ι t = 0 := by rw [sub_mul, one_mul, e_mul ι hm, sub_self]

theorem ff : (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
  have := e_mul ι hm 1
  linear_combination this

theorem f_smul_map (X : Matrix (Fin n) (Fin n) L) : (1 - ι 1) • X.map ι = 0 := by
  ext i j
  simp [Matrix.smul_apply, f_mul ι hm]

theorem f_smul_mul_map (Y : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin n) L) :
    (1 - ι 1) • (Y * X.map ι) = 0 := by
  rw [← Matrix.mul_smul, f_smul_map ι hm, Matrix.mul_zero]

theorem f_smul_map_mul (Y : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin n) L) :
    (1 - ι 1) • (X.map ι * Y) = 0 := by
  rw [← Matrix.smul_mul, f_smul_map ι hm, Matrix.zero_mul]

theorem map_one' : (1 : Matrix (Fin n) (Fin n) L).map ι = ι 1 • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

def Mm (K : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) R := (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) R) + K.map ι

omit hm in
theorem Mm_def (K : Matrix (Fin n) (Fin n) L) : Mm ι K = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) R) + K.map ι := rfl

theorem Mm_mul (K K' : Matrix (Fin n) (Fin n) L) : Mm ι K * Mm ι K' = Mm ι (K * K') := by
  simp only [Mm_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, ff ι hm,
    Matrix.one_mul, Matrix.mul_one, f_smul_map ι hm, map_mul_map ι hm, add_zero, zero_add]

theorem Mm_one : Mm ι (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  rw [Mm_def, map_one' ι hm, ← add_smul, sub_add_cancel, one_smul]

theorem sandwich (Y : Matrix (Fin n) (Fin n) R) (K1 K2 K3 : Matrix (Fin n) (Fin n) L) :
    Mm ι K1 * ((1 - ι 1) • Y + K2.map ι) * Mm ι K3 = (1 - ι 1) • Y + (K1 * K2 * K3).map ι := by
  simp only [Mm_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, ff ι hm,
    Matrix.one_mul, Matrix.mul_one, f_smul_map ι hm, map_mul_map ι hm, f_smul_mul_map ι hm, f_smul_map_mul ι hm,
    add_zero, zero_add]

def toGL : GL (Fin n) L →* GL (Fin n) R where
  toFun g := ⟨Mm ι (g : Matrix (Fin n) (Fin n) L), Mm ι ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L),
    by rw [Mm_mul ι hm, Units.mul_inv, Mm_one ι hm], by rw [Mm_mul ι hm, Units.inv_mul, Mm_one ι hm]⟩
  map_one' := Units.ext (by show Mm ι ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1; rw [Units.val_one, Mm_one ι hm])
  map_mul' g g' := Units.ext (by
    show Mm ι ((g * g' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Mm ι (g : Matrix (Fin n) (Fin n) L) * Mm ι (g' : Matrix (Fin n) (Fin n) L)
    rw [Units.val_mul, Mm_mul ι hm])

omit hm in
theorem Mm_transpose (K : Matrix (Fin n) (Fin n) L) : (Mm ι K)ᵀ = Mm ι Kᵀ := by
  simp only [Mm_def, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_map]

end Idem

section Core

variable {L : Type} [Field L] {n : ℕ}

theorem unit_core (σL : L →+* L) (δ : L) (hδ : δ ≠ 0) (T : Matrix (Fin n) (Fin n) L) (P : GL (Fin n) L)
    (JT h : Matrix (Fin n) (Fin n) L)
    (hJT : JT = -δ⁻¹ • ((P : Matrix (Fin n) (Fin n) L)ᵀ * T * (P : Matrix (Fin n) (Fin n) L).map σL)ᵀ)
    (hh : (h.map σL)ᵀ * JT * h = JT) :
    ((P : Matrix (Fin n) (Fin n) L) * h * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))ᵀ * T *
      ((P : Matrix (Fin n) (Fin n) L) * h * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map σL = T := by
  set Pm : Matrix (Fin n) (Fin n) L := (P : Matrix (Fin n) (Fin n) L)
  set Pi : Matrix (Fin n) (Fin n) L := ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  set G := Pmᵀ * T * Pm.map σL with hGdef
  have hPP : Pm * Pi = 1 := Units.mul_inv P
  have h1 : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have h2 : Pm.map σL * Pi.map σL = 1 := by rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σL) (map_one σL)]
  have hGt : (h.map σL)ᵀ * Gᵀ * h = Gᵀ := by
    rw [hJT, Matrix.mul_smul, Matrix.smul_mul] at hh
    have := congrArg (fun M : Matrix (Fin n) (Fin n) L => (-δ) • M) hh
    simpa only [smul_smul, neg_mul_neg, mul_inv_cancel₀ hδ, one_smul] using this
  have hG : hᵀ * G * h.map σL = G := by
    have := congrArg Matrix.transpose hGt
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at this
    exact this
  calc (Pm * h * Pi)ᵀ * T * (Pm * h * Pi).map σL
      = Piᵀ * (hᵀ * (Pmᵀ * T * Pm.map σL) * h.map σL) * Pi.map σL := by
        simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    _ = Piᵀ * (Pmᵀ * T * Pm.map σL) * Pi.map σL := by rw [← hGdef, hG]
    _ = (Piᵀ * Pmᵀ) * T * (Pm.map σL * Pi.map σL) := by simp only [Matrix.mul_assoc]
    _ = T := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end Core

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L] {n : ℕ}

theorem e_smul_incM (v : Pl (F := F)) (ι : L →+ AE F E) (hAt : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
    (J : Matrix (Fin n) (Fin n) E) : ι 1 • incM F J = (tJ ι J).map ι := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, incM, tJ, smul_eq_mul]
  rw [pre_spec]
  apply (hAt _).1
  intro u hu
  have h1 : u • ι 1 = 0 := (hAt (ι 1)).2 ⟨1, rfl⟩ u hu
  rw [← smul_mul_assoc, h1, zero_mul]

theorem incM_split (v : Pl (F := F)) (ι : L →+ AE F E) (hAt : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
    (J : Matrix (Fin n) (Fin n) E) : incM F J = (1 - ι 1) • incM F J + (tJ ι J).map ι := by
  rw [← e_smul_incM v ι hAt, ← add_smul, sub_add_cancel, one_smul]

theorem Mm_cA (σ : E →ₐ[F] E) (σL : L →+* L) (ι : L →+ AE F E) (hσ : ∀ x, ι (σL x) = cA σ (ι x))
    (K : Matrix (Fin n) (Fin n) L) : (Mm ι K).map (cA σ) = Mm ι (K.map σL) := by
  have he : cA σ (ι 1) = ι 1 := by rw [← hσ, map_one]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Mm_def, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_sub, he, hσ]
  · simp [Mm_def, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, hσ]

end Adelic

theorem homW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] (σL : L →+* L) (δ : L)
    (ι : L →+ AE F E), δ ≠ 0 → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      ∀ (P JT : GL (Fin n) L), (JT : Matrix (Fin n) (Fin n) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι P X.J)ᵀ →
      ∃ iW : Formalism.UG.UJ σL (JT : Matrix (Fin n) (Fin n) L) →* UA σ X.J, ∀ h,
        mat (iW h) = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) +
          ((P : Matrix (Fin n) (Fin n) L) * ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι := by
  intro F E _ _ _ _ _ σ v n X L _ σL δ ι hδ hAt hm hσ P JT hJT
  let φ : Formalism.UG.UJ σL (JT : Matrix (Fin n) (Fin n) L) →* GL (Fin n) L :=
    (MulAut.conj P).toMonoidHom.comp (Subgroup.subtype _)
  have hφ : ∀ h, ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (P : Matrix (Fin n) (Fin n) L) *
      ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro h
    simp [φ, MulAut.conj_apply, Units.val_mul]
  have hmem : ∀ h, (toGL ι hm).comp φ h ∈ UG (cA σ) (incM F X.J) := by
    intro h
    have hh : (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ * (JT : Matrix (Fin n) (Fin n) L) *
        ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n) (Fin n) L) := h.2
    show (Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))ᵀ * incM F X.J *
      (Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map (cA σ) = incM F X.J
    rw [Mm_transpose, Mm_cA σ σL ι hσ]
    conv_lhs => rw [incM_split v ι hAt X.J]
    rw [sandwich ι hm, hφ, unit_core σL δ hδ (tJ ι X.J) P JT _ hJT hh, ← incM_split v ι hAt X.J]
  refine ⟨((toGL ι hm).comp φ).codRestrict _ hmem, fun h => ?_⟩
  show Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = _
  rw [hφ, Mm_def]

end GlobalTheory.InertLocFrame.HomW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalEigenIntertwiners
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isContRep_sub_cptRep (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W)
    [FiniteDimensional ℂ W] : GlobalTheory.Published.AutFin.IsContRep (GlobalTheory.PRep.sub (cptRep E a) W hW) := by
  first
  | exact @_root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub
  | exact _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub
  | (apply _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub ..)

theorem finiteDimensional_capEigen_maps : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W), FiniteDimensional ℂ W → ∀ (c : (E →+* ℂ) → ℂ → ℂ) (N : Submodule ℂ (W →ₗ[ℂ] Sm E a)), N ≤ maps L W hW → (∀ T ∈ N, ∀ τ u, cap τ u ∘ₗ T = c τ u • T) → FiniteDimensional ℂ N := by
  intro hHC E _ _ _ a L hL W hW hWf c N hN hcap
  haveI := hWf
  have hF := hHC E a L hL W (GlobalTheory.PRep.sub (cptRep E a) W hW) (isContRep_sub_cptRep W hW) c
  haveI := hF
  have hmem : ∀ T ∈ N, ∀ w, T w ∈ GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c := by
    intro T hT w
    have hm : (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
        ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧
          ∀ k ∈ L, finRep E a k (T w) = T w := hN hT
    obtain ⟨heq, hall⟩ := hm
    obtain ⟨htame, hleft, hfix⟩ := hall w
    have hZ : ∀ z ∈ Zalg E a, ∃ s : ℂ, z ∘ₗ T = s • T := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact ⟨c τ u, hcap T hT τ u⟩
      | algebraMap r => exact ⟨r, LinearMap.ext fun v => by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨s + t, by rw [LinearMap.add_comp, hs, ht, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨t * s, by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ht, LinearMap.comp_smul, hs, smul_smul]⟩
    refine ⟨⟨hleft, ?_, ?_, ?_, ?_⟩, hfix, GlobalTheory.Published.AutFinGL.type_of_map _ T heq w, fun τ u => ?_⟩
    · exact isOpen_stab_of_mem_nhds (finRep E a) (T w)
        (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
    · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, heq k w⟩
    · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {T w}) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs⟩ := hZ z hz
      have e : z (T w) = s • T w := LinearMap.congr_fun hs w
      show z (T w) ∈ _
      rw [e]
      exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
    · exact growth_of_tame htame
    · exact LinearMap.congr_fun (hcap T hT τ u) w
  let Φ : N →ₗ[ℂ] (W →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c)) :=
    { toFun := fun T => LinearMap.codRestrict _ T.1 fun w => Submodule.subset_span (hmem T.1 T.2 w)
      map_add' := fun T T' => LinearMap.ext fun w => rfl
      map_smul' := fun r T => LinearMap.ext fun w => rfl }
  have hinj : Function.Injective Φ := fun T T' h =>
    Subtype.ext (LinearMap.ext fun w => congrArg Subtype.val (LinearMap.congr_fun h w))
  exact Module.Finite.of_injective Φ hinj

end GlobalTheory.AutGrowth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumPiTensorHeisenbergFactorwiseSignature
section
noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD

namespace GlobalTheory.FockVacD

theorem sumPl_heisOp_vacuum_dep {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))
        (fun w => heisOp (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))
        (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [GlobalTheory.FockVac.atPl_tprod, GlobalTheory.FockVac.atPl_tprod, GlobalTheory.FockVac.heisOp_one,
    MultilinearMap.map_update_smul]
  rfl

end GlobalTheory.FockVacD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsPolynomialGrowthStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_sections_polynomial_growth : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ C * (m + 1) ^ d := by
  first | exact @GlobalTheory.exists_hdim_twist_lbPow_zero_le | exact GlobalTheory.exists_hdim_twist_lbPow_zero_le | (intros; apply GlobalTheory.exists_hdim_twist_lbPow_zero_le <;> assumption)
end

