module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1757

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharIndicatorMulIntegralFrame
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.CharMul

variable {D : D7}

theorem det_int {n : ℕ} {N : Matrix (Fin n) (Fin n) (EAf D)} (h : IsIntM N) :
    N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => h (σ i) i) _

theorem ring_mul {R : Type} [CommRing R] {ε : R} (h : ε * ε = ε) (a b : R) :
    (1 - ε + ε * a) * (1 - ε + ε * b) = 1 - ε + ε * (a * b) := by
  linear_combination (1 - a - b + a * b) * h

theorem det_mul' {R : Type} [CommRing R] {k : ℕ} (A B : Matrix (Fin k) (Fin k) R) :
    (HMul.hMul A B).det = A.det * B.det :=
  Matrix.det_mul A B

theorem det_gl {R : Type} [CommRing R] {k : ℕ} (β : GL (Fin k) R) : β.val.det * (β⁻¹).val.det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

theorem isUnitDet_mul {e : AE D} (he : e * e = e) {k : ℕ} {A B C : Matrix (Fin k) (Fin k) (EAf D)}
    (h : C.det = A.det * B.det) {x y : (AE D)ˣ} (hx : IsUnitDet e A x) (hy : IsUnitDet e B y) :
    IsUnitDet e C (x * y) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hx1, hy1, one_mul]
  · rw [Units.val_mul, map_mul, hx2, hy2, h]
    exact ring_mul (by rw [← map_mul, he]) _ _
  · rw [mul_inv_rev, Units.val_mul, map_mul]
    exact Subring.mul_mem _ hy3 hx3

private lemma eq_lr_take_drop_of_map_fst_eq_replicate {D : D7} : ∃ Ψ : AE D ≃+* (TensorProduct D.host.F D.host.E (Ainf D.host.F)) × EAf D,
    ∀ z, infPart D z = Algebra.TensorProduct.comm D.host.F D.host.E (Ainf D.host.F) (Ψ z).1 ∧
      toEAf D z = (Ψ z).2 := by
  refine ⟨((Algebra.TensorProduct.comm D.host.F (AF D.host.F) D.host.E).trans
    (Algebra.TensorProduct.prodRight D.host.F D.host.F D.host.E (Ainf D.host.F) (Af D.host.F))).toRingEquiv,
    fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact ⟨rfl, rfl⟩
  | add z z' h1 h2 =>
    constructor
    · simp only [map_add (f := _), Prod.fst_add, h1.1, h2.1]
    · simp only [map_add (f := _), Prod.snd_add, h1.2, h2.2]

private lemma units_eq_of_res_eq_of_le_iSup {D : D7} {z z' : AE D} (hi : infPart D z = infPart D z') (ht : toEAf D z = toEAf D z') :
    z = z' := by
  obtain ⟨Ψ, hΨ⟩ := eq_lr_take_drop_of_map_fst_eq_replicate (D := D)
  apply Ψ.injective
  refine Prod.ext ((Algebra.TensorProduct.comm D.host.F D.host.E (Ainf D.host.F)).injective ?_) ?_
  · rw [← (hΨ z).1, ← (hΨ z').1, hi]
  · rw [← (hΨ z).2, ← (hΨ z').2, ht]

private lemma exists_unit_infPart_one_toEAf_eq {D : D7} {u w : EAf D} (huw : u * w = 1) :
    ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ toEAf D (x : AE D) = u ∧ toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = w := by
  obtain ⟨Ψ, hΨ⟩ := eq_lr_take_drop_of_map_fst_eq_replicate (D := D)
  have hwu : w * u = 1 := by rw [mul_comm, huw]
  refine ⟨⟨Ψ.symm (1, u), Ψ.symm (1, w), ?_, ?_⟩, ?_, ?_, ?_⟩
  · apply Ψ.injective
    simp [huw]
  · apply Ψ.injective
    simp [hwu]
  · show infPart D (Ψ.symm (1, u)) = 1
    rw [(hΨ _).1, RingEquiv.apply_symm_apply, map_one]
  · show toEAf D (Ψ.symm (1, u)) = u
    rw [(hΨ _).2, RingEquiv.apply_symm_apply]
  · show toEAf D (Ψ.symm (1, w)) = w
    rw [(hΨ _).2, RingEquiv.apply_symm_apply]

theorem exists_isUnitDet {e : AE D} (he : e * e = e) (hE : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (EAf D)} {v : EAf D} (hv : v ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : A.det * v = 1) : ∃ x, IsUnitDet e A x := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, he]
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_unit_infPart_one_toEAf_eq (u := 1 - toEAf D e + toEAf D e * A.det)
    (w := 1 - toEAf D e + toEAf D e * v) (by rw [ring_mul hε, h, mul_one, sub_add_cancel])
  refine ⟨x, hx1, hx2, ?_⟩
  rw [hx3]
  exact Subring.add_mem _ (Subring.sub_mem _ (Subring.one_mem _) hE) (Subring.mul_mem _ hE hv)

private lemma isUnitDet_unique' {D : D7} {e : AE D} {k : ℕ} {M : Matrix (Fin k) (Fin k) (EAf D)} {x x' : (AE D)ˣ}
    (hx : IsUnitDet e M x) (hx' : IsUnitDet e M x') : x = x' :=
  Units.ext (units_eq_of_res_eq_of_le_iSup (hx.1.trans hx'.1.symm) (hx.2.1.trans hx'.2.1.symm))

private lemma unitChar_eq_inv_of_isUnitDet {D : D7} (ν : (AE D)ˣ →* Circle) {e : AE D} {k : ℕ} {M : Matrix (Fin k) (Fin k) (EAf D)}
    {x : (AE D)ˣ} (hx : IsUnitDet e M x) : unitChar ν e M = (((ν x)⁻¹ : Circle) : ℂ) := by
  have hex : ∃ x, IsUnitDet e M x := ⟨x, hx⟩
  unfold unitChar
  rw [dite_eq_left hex, isUnitDet_unique' hex.choose_spec hx]

theorem unitChar_mul : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D), e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
  ∀ {k : ℕ} (N : Matrix (Fin k) (Fin k) (EAf D)) (β : GL (Fin k) (EAf D)), IsIntM β.val → IsIntM (β⁻¹).val →
  unitChar ν e (HMul.hMul N β.val) = unitChar ν e N * unitChar ν e β.val := by
  intro D ν e he hE k N β hβ hβ'
  obtain ⟨y, hy⟩ := exists_isUnitDet he hE (det_int hβ') (det_gl β)
  obtain ⟨y', hy'⟩ := exists_isUnitDet he hE (det_int hβ) (by rw [mul_comm]; exact det_gl β)
  by_cases hN : ∃ x, IsUnitDet e N x
  · obtain ⟨x, hx⟩ := hN
    rw [unitChar_eq_inv_of_isUnitDet ν (isUnitDet_mul he (det_mul' N β.val) hx hy), unitChar_eq_inv_of_isUnitDet ν hx, unitChar_eq_inv_of_isUnitDet ν hy,
      map_mul, mul_inv, Circle.coe_mul]
  · have hNβ : ¬ ∃ x, IsUnitDet e (HMul.hMul N β.val) x := by
      rintro ⟨z, hz⟩
      exact hN ⟨_, isUnitDet_mul he (by rw [det_mul', mul_assoc, det_gl, mul_one]) hz hy'⟩
    unfold unitChar
    rw [dite_eq_right hN, dite_eq_right hNβ, zero_mul]

end GlobalTheory.StdRead.CharMul

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentModIdealModConjIdeal
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipConjIdeal

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_sub_left (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (x - y) z = ReciprocityTheory.ChartRestriction.G.FD.herm G x z - ReciprocityTheory.ChartRestriction.G.FD.herm G y z := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.herm, sub_mul, Finset.sum_sub_distrib]

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (a : E) (x z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (a • x) z = a * ReciprocityTheory.ChartRestriction.G.FD.herm G x z := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (a : E) (x z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G x (a • z) = ReciprocityTheory.ChartRestriction.G.FD.cc a * ReciprocityTheory.ChartRestriction.G.FD.herm G x z := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem herm_adjoint_pow (G : Matrix (Fin r) (Fin r) E) (β : GL (Fin r) E)
    (hU : ∀ v w, ReciprocityTheory.ChartRestriction.G.FD.herm G ((β : Matrix (Fin r) (Fin r) E) *ᵥ v)
      ((β : Matrix (Fin r) (Fin r) E) *ᵥ w) = ReciprocityTheory.ChartRestriction.G.FD.herm G v w) (k : ℕ) (x y : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G ((((β : Matrix (Fin r) (Fin r) E) - 1) ^ k) *ᵥ x) y =
      ReciprocityTheory.ChartRestriction.G.FD.herm G x (((((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) - 1) ^ k) *ᵥ y) := by
  have step : ∀ x z : Fin r → E, ReciprocityTheory.ChartRestriction.G.FD.herm G (((β : Matrix (Fin r) (Fin r) E) - 1) *ᵥ x) z =
      ReciprocityTheory.ChartRestriction.G.FD.herm G x ((((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) - 1) *ᵥ z) := by
    intro x z
    have hz : (β : Matrix (Fin r) (Fin r) E) *ᵥ (((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ z) = z := by
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, herm_sub_left]
    conv_lhs => rw [← hz, hU]
    simp [ReciprocityTheory.ChartRestriction.G.FD.herm, Finset.sum_sub_distrib, mul_sub, ReciprocityTheory.ChartRestriction.G.FD.cc]
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ih, step, mulVec_mulVec, ← pow_succ']

end GlobalTheory.UnipConjIdeal

namespace GlobalTheory.UnipConjIdeal

open Matrix

theorem pow_sub_one_mem_conj_ideal_smul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (β : GL (Fin r) E),
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v) (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) =
      herm X.Gm v w) →
    (∀ v, v ∈ X.L' ↔ Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v ∈ X.L') →
    ∀ P : Ideal (𝓞 E), (∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • X.L') →
    ∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈
      P.map ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E ≃+* 𝓞 E) : 𝓞 E →+* 𝓞 E) • X.L' := by
  intro E _ _ _ r X β hU hL P hP v hv
  have hsm : ∀ (p : 𝓞 E) (w : Fin r → E), p • w = (p : E) • w := fun p w => (algebraMap_smul E p w).symm
  set βm : Matrix (Fin r) (Fin r) E := (β : Matrix (Fin r) (Fin r) E) with hβm
  set βi : Matrix (Fin r) (Fin r) E := ((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hβi
  have h1 : βi * βm = 1 := Units.inv_mul β
  have h2 : βm * βi = 1 := Units.mul_inv β

  have hinv : ∀ w ∈ X.L', βi *ᵥ w ∈ X.L' := by
    intro w hw
    refine (hL _).mpr ?_
    rw [mulVec_mulVec, h2, one_mulVec]; exact hw
  have hBpow : ∀ k : ℕ, ∀ w ∈ X.L', ((-βi) ^ k) *ᵥ w ∈ X.L' := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ', ← mulVec_mulVec, neg_mulVec]
      exact X.L'.neg_mem (hinv _ (ih w hw))

  have hfac : βi - 1 = (-βi) * (βm - 1) := by
    rw [neg_mul, mul_sub, h1, mul_one]; abel
  have hcomm : Commute (-βi) (βm - 1) := by
    unfold Commute SemiconjBy
    rw [neg_mul, mul_neg, mul_sub, sub_mul, h1, h2, mul_one, one_mul]
  have hadjpow : (βi - 1) ^ r = (-βi) ^ r * (βm - 1) ^ r := by
    rw [hfac, hcomm.mul_pow]
  by_cases hP0 : P = ⊥
  · subst hP0
    have h0 := hP v hv
    rw [Submodule.bot_smul, Submodule.mem_bot] at h0
    rw [h0]; exact zero_mem _
  obtain ⟨c, hcP, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨P', hPP'⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr hcP)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc0

  have hi : ∀ w ∈ P • X.L', ∀ p' ∈ P', ((c : E)⁻¹ * p') • w ∈ X.L' := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro p hp l hl p' hp'
      have hm : p * p' ∈ Ideal.span {c} := by rw [hPP']; exact Ideal.mul_mem_mul hp hp'
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
      have : ((c : E)⁻¹ * p') • (p • l) = t • l := by
        rw [hsm, hsm, smul_smul]
        congr 1
        have : (p : E) * p' = t * c := by exact_mod_cast ht.symm
        field_simp
        linear_combination this
      rw [this]; exact X.L'.smul_mem t hl
    · intro x y hx hy p' hp'
      rw [smul_add]; exact X.L'.add_mem (hx p' hp') (hy p' hp')

  have hii : ∀ z ∈ X.L', ∀ p' ∈ P', ((c : E)⁻¹ * p') • (((βi - 1) ^ r) *ᵥ z) ∈ X.L' := by
    intro z hz p' hp'
    rw [hadjpow, ← mulVec_mulVec, ← mulVec_smul]
    exact hBpow r _ (hi _ (hP z hz) p' hp')

  set σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv with hσdef
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = ReciprocityTheory.ChartRestriction.G.FD.cc (x : E) := fun x => rfl
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc (ReciprocityTheory.ChartRestriction.G.FD.cc x) = x := by
    intro x; simp [ReciprocityTheory.ChartRestriction.G.FD.cc]

  have hiii : ∀ p' ∈ P', ((σ c : E)⁻¹ * (σ p' : E)) • (((βm - 1) ^ r) *ᵥ v) ∈ X.L' := by
    intro p' hp'
    refine X.L'_dual _ fun z hz => ?_
    rw [herm_smul_left, herm_adjoint_pow X.Gm β hU r v z]
    have : (σ c : E)⁻¹ * (σ p' : E) = ReciprocityTheory.ChartRestriction.G.FD.cc ((c : E)⁻¹ * p') := by
      rw [hσ, hσ, ReciprocityTheory.ChartRestriction.G.FD.cc, ReciprocityTheory.ChartRestriction.G.FD.cc, ReciprocityTheory.ChartRestriction.G.FD.cc, map_mul, map_inv₀]
    rw [this, ← herm_smul_right]
    exact X.L'_int v hv _ (hii z hz p' hp')

  have hmul : P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) = Ideal.span {σ c} := by
    rw [← Ideal.map_mul, ← hPP', Ideal.map_span, Set.image_singleton]; rfl
  have hd : σ c ∈ P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) := by
    rw [hmul]; exact Ideal.mem_span_singleton_self _
  have hσc : (σ c : E) ≠ 0 := by
    intro h; apply hcE
    have := congrArg ReciprocityTheory.ChartRestriction.G.FD.cc h
    rw [hσ, hcc] at this
    simpa [ReciprocityTheory.ChartRestriction.G.FD.cc] using this
  have key : ∀ u, u ∈ P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) →
      ((σ c : E)⁻¹ * u) • (((βm - 1) ^ r) *ᵥ v) ∈ P.map (σ : 𝓞 E →+* 𝓞 E) • X.L' := by
    intro u hu
    refine Submodule.mul_induction_on hu ?_ ?_
    · intro q hq q' hq'
      obtain ⟨p', hp', rfl⟩ := (Ideal.mem_map_of_equiv σ q').mp hq'
      have : ((σ c : E)⁻¹ * ((q * σ p' : 𝓞 E) : E)) • (((βm - 1) ^ r) *ᵥ v) =
          q • (((σ c : E)⁻¹ * (σ p' : E)) • (((βm - 1) ^ r) *ᵥ v)) := by
        rw [hsm, smul_smul]; congr 1; push_cast; ring
      rw [this]
      exact Submodule.smul_mem_smul hq (hiii p' hp')
    · intro x y hx hy
      rw [show ((x + y : 𝓞 E) : E) = (x : E) + y by push_cast; rfl, mul_add, add_smul]
      exact Submodule.add_mem _ hx hy
  have := key _ hd
  rwa [inv_mul_cancel₀ hσc, one_smul] at this

end GlobalTheory.UnipConjIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairMovesPhasedHeisenbergTranslate
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedTr
variable {D : D7}

theorem heisO_add_eq (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ u : WO S T) (F : WO S T → ℂ) :
    heisO ψ S T (w₀ + u) F = ψ (-symplOH S T w₀ u) • heisO ψ S T w₀ (heisO ψ S T u F) := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.IndefR.Fin.symplOH_add_right, Formalism.IndefR.Fin.symplOH_add_left, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, add_assoc]
  have h1 : ψ (-symplOH S T w₀ u) * ψ (symplOH S T w₀ u) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (-(ψ (symplOH S T w w₀) * ψ (symplOH S T w u) * F (w + (w₀ + u)))) * h1

theorem closeTo_of_mul {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {k m : ℕ} {g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)}
    {g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)} {z z' : Matrix (Fin N') (Fin N) D.host.E}
    (h : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc (k * m) g g' z z') : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc m g g' z z' := by
  intro i j
  obtain ⟨t, ht, e⟩ := h i j
  refine ⟨(k : Formalism.MainNotions.StandardLatticesGL3.AE D) * t, ?_, ?_⟩
  · have : (k : Formalism.MainNotions.StandardLatticesGL3.AE D) * t = k • t := by rw [nsmul_eq_mul]
    rw [this]; exact AddSubgroup.nsmul_mem _ ht k
  · rw [e]; push_cast; ring

theorem moved_translate : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • om (g, h) (heisO ψ S T (finPt hS hT r z) f₀) =
      Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') • heisO ψ S T (finPt hS hT r z') (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset χS χT om hom x y g h hg hh f₀ hf₀ z
  have hF := hom.om_pres (g, h) f₀ hf₀
  obtain ⟨n₁, hn₁, H₁⟩ := _root_.GlobalTheory.LevelTr.level_translate ψ θ S T hS hT cc δ r hset x y g h hg hh _ hF z
  obtain ⟨n₂, hn₂, H₂⟩ := _root_.GlobalTheory.MovedTrChar.psi_sympl_moved_eq_one ψ θ S T hS hT cc δ r hset x y g h hg hh z
  obtain ⟨n₃, hn₃, H₃⟩ := _root_.GlobalTheory.PhaseMove.phase_eq cc δ hset.crv x y z
  refine ⟨n₁ * n₂ * n₃, by positivity, fun z' hz' => ?_⟩
  have c1 : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n₁ (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' :=
    closeTo_of_mul (k := n₂ * n₃) (by rwa [show n₂ * n₃ * n₁ = n₁ * n₂ * n₃ by ring])
  have c2 : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n₂ (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' :=
    closeTo_of_mul (k := n₁ * n₃) (by rwa [show n₁ * n₃ * n₂ = n₁ * n₂ * n₃ by ring])
  have c3 : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n₃ (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' :=
    closeTo_of_mul (k := n₁ * n₂) (by rwa [show n₁ * n₂ * n₃ = n₁ * n₂ * n₃ by ring])
  rw [hom.om_heis g h _ f₀ hf₀, H₃ z' c3]
  have e : actO S T g h (finPt hS hT r z) =
      finPt hS hT r z' + (actO S T g h (finPt hS hT r z) - finPt hS hT r z') := by abel
  have hψ : ψ (-symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) = 1 := by
    have h2 := H₂ z' c2
    have h0 : ψ (-symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) *
        ψ (symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rwa [h2, mul_one] at h0
  rw [e, heisO_add_eq, H₁ z' c1, hψ, one_smul]

end GlobalTheory.MovedTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∃ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ GlobalTheory.WeilM.SB _ ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ (S φ) := by
  first | exact @GlobalTheory.WeilLocality.locality | exact GlobalTheory.WeilLocality.locality | (intros; apply GlobalTheory.WeilLocality.locality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVWStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityW.locality | exact GlobalTheory.WeilLocalityW.locality | (intros; apply GlobalTheory.WeilLocalityW.locality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

namespace GlobalTheory.HSApp

end GlobalTheory.HSApp
end
end

