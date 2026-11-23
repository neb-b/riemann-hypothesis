module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetInertPlaceLatticeLength
section
noncomputable section

namespace GlobalTheory.InertLatLength

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open GlobalTheory.LFun (toCompl latAt IsFrameAt)
open GlobalTheory.LFun.InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

def intMap (h : w.under (𝓞 F) = v) : intLoc F E v →+* w.adicCompletionIntegers E :=
  ((toCompl h).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E) fun y => toCompl_mem h y.2

theorem intMap_surjective (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    Function.Surjective (intMap h) := by
  intro z
  obtain ⟨y, hy⟩ := (toCompl_bijective hw h).2 (z : w.adicCompletion E)
  have hy' : y ∈ intLoc F E v := (mem_intLoc_iff hw h y).2 (by rw [hy]; exact z.2)
  exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩

def coord (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y : Fin n → Fv F v ⊗[F] E) :
    Fin n → w.adicCompletion E :=
  (a⁻¹).1 *ᵥ (toCompl h ∘ y)

theorem mulVec_coord (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y : Fin n → Fv F v ⊗[F] E) :
    a.1 *ᵥ coord h a y = toCompl h ∘ y := by
  rw [coord, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_latLoc_iff_coord {L : Submodule (𝓞 E) (Fin n → E)} (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) {a : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a)
    (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ ∀ i, coord h a y i ∈ w.adicCompletionIntegers E := by
  rw [mem_latLoc_iff hw h, ← mulVec_coord h a y]
  exact (ha _).symm

theorem coord_injective (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (a : GL (Fin n) (w.adicCompletion E)) : Function.Injective (coord h a) := by
  intro y y' e
  have e' : toCompl h ∘ y = toCompl h ∘ y' := by rw [← mulVec_coord, ← mulVec_coord, e]
  exact funext fun i => (toCompl_bijective hw h).1 (congrFun e' i)

theorem coord_add (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y y' : Fin n → Fv F v ⊗[F] E) :
    coord h a (y + y') = coord h a y + coord h a y' := by
  simp only [coord, ← Matrix.mulVec_add]
  congr 1
  funext i
  simp [map_add (f := _)]

theorem coord_smul (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (c : Fv F v ⊗[F] E)
    (y : Fin n → Fv F v ⊗[F] E) :
    coord h a (fun i => c * y i) = toCompl h c • coord h a y := by
  simp only [coord, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_mul]

theorem coord_mulVec (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (α : GL (Fin n) (Fv F v ⊗[F] E))
    (y : Fin n → Fv F v ⊗[F] E) :
    coord h a (α.1 *ᵥ y) = (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 *ᵥ coord h a y := by
  rw [coord, comp_mulVec, ← mulVec_coord h a y, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Units.val_mul, Units.val_mul]

theorem exists_coord_eq (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (a : GL (Fin n) (w.adicCompletion E)) (z : Fin n → w.adicCompletion E) : ∃ y, coord h a y = z := by
  obtain ⟨y, hy⟩ := (toCompl_bijective hw h).2.comp_left (a.1 *ᵥ z)
  refine ⟨y, ?_⟩
  rw [coord, show toCompl h ∘ y = a.1 *ᵥ z from hy, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

section Main

variable {L : Submodule (𝓞 E) (Fin n → E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {a : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a)

def phi : latLoc F L v →ₛₗ[intMap h] (Fin n → w.adicCompletionIntegers E) where
  toFun y i := ⟨coord h a y i, (mem_latLoc_iff_coord hw h ha y).1 y.2 i⟩
  map_add' y y' := funext fun i => Subtype.ext (congrFun (coord_add h a y y') i)
  map_smul' r y := funext fun i => Subtype.ext (congrFun (coord_smul h a r.1 y.1) i)

theorem coe_phi (y : latLoc F L v) (i : Fin n) : (phi hw h ha y i : w.adicCompletion E) = coord h a y i := rfl

include hw ha in
theorem phi_surjective : Function.Surjective (phi hw h ha) := by
  intro z
  obtain ⟨y, hy⟩ := exists_coord_eq hw h a (fun i => (z i : w.adicCompletion E))
  have hm : y ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha y).2 fun i => by rw [hy]; exact (z i).2
  exact ⟨⟨y, hm⟩, funext fun i => Subtype.ext (congrFun hy i)⟩

variable {M : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)} {α : GL (Fin n) (Fv F v ⊗[F] E)}

include hw ha in
theorem integral_entries (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) (i j : Fin n) :
    (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨y, hy⟩ := exists_coord_eq hw h a (Pi.single j 1)
  have hm : y ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha y).2 fun k => by
    rw [hy]
    by_cases e : k = j
    · subst e; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne e]; exact zero_mem _
  have h1 := (mem_latLoc_iff_coord hw h ha _).1 (hM ((hα _).2 ⟨y, hm, rfl⟩)) i
  rw [coord_mulVec, hy, Matrix.mulVec_single_one] at h1
  exact h1

def intMat (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) :
    Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) :=
  Matrix.of fun i j => ⟨_, integral_entries hw h ha hM hα i j⟩

variable (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x)

theorem coe_intMat_mulVec (z : Fin n → w.adicCompletionIntegers E) (i : Fin n) :
    ((intMat hw h ha hM hα *ᵥ z) i : w.adicCompletion E) =
      ((a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 *ᵥ fun j => (z j : w.adicCompletion E)) i := by
  have := RingHom.map_mulVec (w.adicCompletionIntegers E).subtype (intMat hw h ha hM hα) z i
  exact this

theorem submoduleOf_eq :
    M.submoduleOf (latLoc F L v) = (LinearMap.range (intMat hw h ha hM hα).mulVecLin).comap (phi hw h ha) := by
  ext y
  change y.1 ∈ M ↔ _
  rw [hα, Submodule.mem_comap, LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨phi hw h ha ⟨x, hx⟩, funext fun i => Subtype.ext ?_⟩
    rw [Matrix.mulVecLin_apply, coe_intMat_mulVec, coe_phi, e, coord_mulVec]
    rfl
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := exists_coord_eq hw h a (fun i => (z i : w.adicCompletion E))
    have hm : x ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha x).2 fun i => by rw [hx]; exact (z i).2
    refine ⟨x, hm, coord_injective hw h a (funext fun i => ?_)⟩
    rw [coord_mulVec, hx, ← coe_intMat_mulVec hw h ha hM hα, ← coe_phi hw h ha y]
    exact congrArg (fun t => ((t i : w.adicCompletionIntegers E) : w.adicCompletion E)) hz.symm

def quotMap : (latLoc F L v ⧸ M.submoduleOf (latLoc F L v)) →ₛₗ[intMap h]
    ((Fin n → w.adicCompletionIntegers E) ⧸ LinearMap.range (intMat hw h ha hM hα).mulVecLin) :=
  (M.submoduleOf (latLoc F L v)).mapQ _ (phi hw h ha) (submoduleOf_eq hw h ha hM hα).le

theorem quotMap_bijective : Function.Bijective (quotMap hw h ha hM hα) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq => ?_, fun q => ?_⟩
  · induction q using Submodule.Quotient.induction_on with
    | H y =>
      rw [quotMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero, submoduleOf_eq hw h ha hM hα]
      exact hq
  · induction q using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨y, rfl⟩ := phi_surjective hw h ha z
      exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem length_eq_addVal :
    Module.length (intLoc F E v) (latLoc F L v ⧸ M.submoduleOf (latLoc F L v)) =
      IsDiscreteValuationRing.addVal _ (intMat hw h ha hM hα).det := by
  haveI : RingHomSurjective (intMap h) := ⟨intMap_surjective hw h⟩
  rw [← GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det, Module.length, Module.length, WithBot.unbot_inj]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective (quotMap hw h ha hM hα) (quotMap_bijective hw h ha hM hα))

theorem coe_det_intMat :
    ((intMat hw h ha hM hα).det : w.adicCompletion E) = toCompl h (Matrix.GeneralLinearGroup.det α).1 := by
  have h1 := RingHom.map_det (w.adicCompletionIntegers E).subtype (intMat hw h ha hM hα)
  have h2 : (w.adicCompletionIntegers E).subtype.mapMatrix (intMat hw h ha hM hα) =
      (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 := Matrix.ext fun i j => rfl
  have h3 : Matrix.GeneralLinearGroup.det (a⁻¹ * Formalism.UG.bc (toCompl h) α * a) =
      Matrix.GeneralLinearGroup.det (Formalism.UG.bc (toCompl h) α) := by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  change (w.adicCompletionIntegers E).subtype _ = _
  rw [h1, h2]
  have h4 := congrArg Units.val h3
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply] at h4
  rw [h4, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Main

theorem ordL_eq_addVal {d : w.adicCompletionIntegers E} (hd : d ≠ 0) :
    ∃ m : ℕ, IsDiscreteValuationRing.addVal _ d = m ∧ Formalism.UG.ordL (d : w.adicCompletion E) = m := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hϖ' : Valued.v ϖ = WithZero.exp (-1) := hϖ
  have hle : ϖ ∈ w.adicCompletionIntegers E := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  let π : w.adicCompletionIntegers E := ⟨ϖ, hle⟩
  have hπ := GlobalTheory.DegreeOneUniformiser.irreducible_of_valued w π hϖ'
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
  refine ⟨m, IsDiscreteValuationRing.addVal_def d u hπ m hu, ?_⟩
  have hc : (d : w.adicCompletion E) = ((u : w.adicCompletionIntegers E) : w.adicCompletion E) * ϖ ^ m := by
    rw [hu, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hv : Valued.v (d : w.adicCompletion E) = WithZero.exp (-(m : ℤ)) := by
    rw [hc, map_mul, map_pow, hϖ', HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit,
      one_mul, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hne : Valued.v (d : w.adicCompletion E) ≠ 0 := by rw [hv]; exact WithZero.exp_ne_zero
  have hz : WithZero.unzero hne = Multiplicative.ofAdd (-(m : ℤ)) :=
    WithZero.coe_inj.1 (by rw [WithZero.coe_unzero, hv]; rfl)
  rw [Formalism.UG.ordL, dite_eq_right hne, hz]
  simp

theorem main_of_abs (habs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v), Formalism.UG.IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ,
    (absEv F E v x : ℝ) = (Formalism.UG.qV F v : ℝ) ^ (-(2 * Formalism.UG.ordL (toCompl h x.1)))) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ L _ v P hP g α hα
  have hw : Formalism.UG.IsInertAt F E v P := hP
  have h : P.under (𝓞 F) = v := (under_eq_iff hw P).2 rfl
  obtain ⟨a, ha⟩ := exists_isFrameAt hw (Submodule.IsLattice.fg E L) (Submodule.IsFullLattice.span_eq_top (A := E) (M := L))
  have hM : latLoc F L v ⊓ latMoved σ J L v g ≤ latLoc F L v := inf_le_left
  have hα' : ∀ y, y ∈ latLoc F L v ⊓ latMoved σ J L v g ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x := fun y => hα y
  have hlen := length_eq_addVal hw h ha hM hα'
  have hdet := coe_det_intMat hw h ha hM hα'
  have hd0 : (intMat hw h ha hM hα').det ≠ 0 := by
    intro e
    rw [e, ZeroMemClass.coe_zero] at hdet
    exact ((Matrix.GeneralLinearGroup.det α).isUnit.map (toCompl h)).ne_zero hdet.symm
  obtain ⟨m, hm1, hm2⟩ := ordL_eq_addVal hd0
  refine ⟨m, hlen.trans hm1, ?_⟩
  have e1 := habs F E σ hσ v P h hw (Matrix.GeneralLinearGroup.det α)
  rw [← hdet, hm2] at e1
  have hq := absNorm_eq hσ.2.2.1 hw
  apply NNReal.eq
  rw [e1, NNReal.coe_zpow, hq, Formalism.UG.qV]
  push_cast
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem absEv_det_eq_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) :=
  main_of_abs GlobalTheory.AbsInert.absEv_inert

end GlobalTheory.InertLatLength
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSymmetricElementaryDivisorsUnitary
section
noncomputable section

open Formalism.UG Formalism.IndefR.Mult GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.InertThetaCompare

namespace GlobalTheory.LFun.UnitaryDiv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q n : ℕ}

theorem exists_cartan (hU : IsUnramInv ϖ σ q) (g : GL (Fin n) L) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ GLint (Fin n) (intL L), ∃ k₂ ∈ GLint (Fin n) (intL L),
      (g : Matrix (Fin n) (Fin n) L) = (k₁ : Matrix (Fin n) (Fin n) L) *
        Matrix.diagonal (fun i => ϖ ^ a i) * (k₂ : Matrix (Fin n) (Fin n) L) := by
  have hnt := P.fSatake_nontriv hU
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hA : IsDiscreteValuationRing A := Valuation.valuationSubring_isDiscreteValuationRing _
  have : IsPrincipalIdealRing (intL L) := inferInstanceAs (IsPrincipalIdealRing A)
  obtain ⟨c, hc0, hg, -⟩ := P.glint_exists_denom (n := Fin n) A g
  refine P.cartan_decomp_gen (intL L) Valued.v (fun _ => Iff.rfl) ϖ (unif_ne_zero hU) (fun x hx => ?_) g c hc0 hg
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  rw [hϖ, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log hx']

theorem good_of_mem (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h1 : d.length = n) (h2 : d.Pairwise fun a b => b ≤ a)
    {g : GL (Fin n) L} (hg : g ∈ GU σ n) {k₁ k₂ : GL (Fin n) L} (h₁ : k₁ ∈ GLint (Fin n) (intL L))
    (h₂ : k₂ ∈ GLint (Fin n) (intL L))
    (e : g.1 = k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * k₂.1) : Good n d := by
  have hπ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨π', hπ', a, ha, b, hb, e'⟩ := GlobalTheory.DualDivU.hasDiv_dualLab _ σ n d _ hU.2.1 h1 hg
    ⟨ϖ, hπ, k₁, h₁, k₂, h₂, e⟩
  have l1 : (dualLab d).length = n := by simpa [dualLab] using h1
  have l2 : (dualLab d).Pairwise fun a b => b ≤ a := by
    rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact h2.imp fun h => neg_le_neg h
  rw [e] at e'
  have ent := fun {x} (hx : x ∈ GLint (Fin n) (intL L)) => GlobalTheory.DualDivU.entry_mem _ hx
  refine ⟨h1, h2, eq_of_getD l1 h1 (congrFun (eq_of_tails fun k => le_antisymm ?_ ?_))⟩
  · refine tail_le hπ' hπ (anti_getD l1 l2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (inv_mem h₁) ha)) (ent (mul_mem hb (inv_mem h₂))) ?_ k
    calc _ = (k₁⁻¹).1 * (k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * k₂.1) * (k₂⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [e']; simp only [Units.val_mul, Matrix.mul_assoc]
  · refine tail_le hπ hπ' (anti_getD h1 h2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (inv_mem ha) h₁)) (ent (mul_mem h₂ (inv_mem hb))) ?_ k
    calc _ = (a⁻¹).1 * (a.1 * Matrix.diagonal (fun i : Fin n => π' ^ (dualLab d).getD i.1 0) * b.1) * (b⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← e']; simp only [Units.val_mul, Matrix.mul_assoc]

theorem exists_good_div : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ d : List ℤ, GlobalTheory.InertThetaCompare.Good n d ∧
      ∃ a ∈ GLint (Fin n) (intL L), ∃ b ∈ GLint (Fin n) (intL L),
        ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) *
          Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * (b : Matrix (Fin n) (Fin n) L) := by
  intro L _ _ ϖ σ q n hU g
  obtain ⟨a, ha, k₁, h₁, k₂, h₂, e⟩ := exists_cartan hU (g : GL (Fin n) L)
  have hd : ∀ i : Fin n, (List.ofFn a).getD i.1 0 = a i := fun i => by simp [List.getD_eq_getElem?_getD]
  have e' : ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ (List.ofFn a).getD i.1 0) * k₂.1 := by
    simp only [hd]; exact e
  exact ⟨List.ofFn a, good_of_mem hU List.length_ofFn
    (List.pairwise_ofFn.2 fun i j hij => ha hij.le) g.2 h₁ h₂ e', k₁, h₁, k₂, h₂, e'⟩

end GlobalTheory.LFun.UnitaryDiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlDetEqOneOfMemUnip
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

theorem gl_det_eq_one_of_mem_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular (M := (g : Matrix (Fin r) (Fin r) κ))
    (fun i j h => unip_lower hg h)]
  simp [unip_diag hg]

theorem chi_eq_one_of_mem_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (h : R.IsGrp F) :
    ∀ i, ∀ u ∈ F.P0, (R.FW i).chi u = 1 := by
  intro i u hu
  obtain ⟨ψ, -, h0, -⟩ := h.levels
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : R.eG u ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simpa using hu
  rw [h1] at h2
  apply Units.ext
  apply D.what₂.embLL.injective
  rw [h.chiW i u, Units.val_one, map_one]
  refine Finset.prod_eq_one fun PP _ => ?_
  rw [gl_det_eq_one_of_mem_unip (h2 PP (Set.mem_univ _)), map_one, Units.val_one]

end GlobalTheory.TraceIncl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodFormsCoordinateMapMemOfLiftsMem
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open Formalism.IndefR.Mult Formalism.IndefR.Cx
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

theorem mem_of_mem_span_image {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] [AddCommGroup H]
    [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    (hj : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent ℂ fun k => j (b k))
    (N : Submodule K V) {z : V} (hz : j z ∈ Submodule.span ℂ (j '' (N : Set V))) : z ∈ N := by
  by_contra hn
  let b : Fin (Module.finrank K N) → V := fun k => (Module.finBasis K N k : V)
  have hb : LinearIndependent K b := (Module.finBasis K N).linearIndependent.map' N.subtype N.ker_subtype
  have hs : Submodule.span K (Set.range b) ≤ N := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (Module.finBasis K N k).2)
  have h1 := hj _ (Fin.cons z b) (linearIndependent_finCons.2 ⟨hb, fun h => hn (hs h)⟩)
  have h2 : (fun k => j ((Fin.cons z b : Fin (Module.finrank K N + 1) → V) k)) =
      (Fin.cons (j z) (fun k => j (b k)) : Fin (Module.finrank K N + 1) → H) := by
    funext k
    refine Fin.cases rfl (fun _ => rfl) k
  rw [h2, linearIndependent_finCons] at h1
  refine h1.2 (Submodule.span_le.2 ?_ hz)
  rintro _ ⟨x, hx, rfl⟩
  have h3 := congrArg (fun z : N => (z : V)) ((Module.finBasis K N).sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h3, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem exists_lvlE_eq {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ)
    (y : Fin (S.BaseDimension r X P ψ) → K) : ∃ x, (S.lvlE r P ψ).mulVecLin x = (S.V0E r X P ψ).mulVecLin y := by
  obtain ⟨u, hu⟩ := (image_idempotent_spec K _ (S.gaMat r (goodAt X P ψ))).2.le ⟨y, rfl⟩
  have h : S.gaMat r (goodAt X P ψ) = S.gaMat r (lvlIdem P ψ) * S.gaMat r (idemOf X) := by
    rw [← (group_action_matrix_hom K S G r).2, (idempotent_central K G X hX).2]
    rfl
  refine (image_idempotent_spec K _ (S.gaMat r (lvlIdem P ψ))).2.ge ⟨(S.gaMat r (idemOf X)).mulVec u, ?_⟩
  refine Eq.trans ?_ hu
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]

theorem goodFormsCoordinateMap_apply {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {Am : Formalism.L2.Indef.DefAmb Bs}
    (X : CxData Am) (b : Bool) (j : Bs.J) (c : Fin (X.dW b j) → ℂ) :
    X.w0C b j c = ∑ k, c k • X.eW b j (X.bW b j Bs.v0 k) := by
  show X.eW b j (∑ k, c k • X.bW b j Bs.v0 k) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul _ _ _

theorem goodFormsCoordinateMap_mem_of_lifts_mem {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {Am : Formalism.L2.Indef.DefAmb Bs}
    (X : CxData Am) {fc : Formalism.L2.Indef.DefSub Am → Formalism.L2.Indef.DefFace Bs} (cr : Crd Am fc) (b : Bool) (h5 : X.H5 cr b)
    (j : Bs.J) (t : Bs.Tup) (N : Submodule ℂ (X.W j)) (h : ∀ y, X.θ' j t (X.jL j t (cr.toL X.zs b j t y)) ∈ N)
    (c : Fin (X.dW b j) → ℂ) : X.w0C b j c ∈ N := by
  obtain ⟨d, hd⟩ := (h5 j t).2.ge ⟨c, rfl⟩
  rw [← hd]
  show ∑ k, d k • X.θ' j t (X.jL j t (cr.toL X.zs b j t (Pi.single k 1))) ∈ N
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h _)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem e_j_eOp (hU : R.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : Fin (R.nW i) → D.what₂.LL) :
    (R.HW i σ).e ((R.FW i).j σ ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y)) =
      postOn _ (R.eWf i σ) ((R.HW i σ).e ((R.FW i).j σ y)) := by
  have htw : ∀ g, (R.HW i σ).e ((R.FW i).j σ (GlobalTheory.LevelForms.twRep (R.FW i) g y)) =
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e ((R.FW i).j σ y)) := by
    intro g
    rw [GlobalTheory.LevelForms.twRep_apply, map_smulₛₗ, map_smul, (hU i σ).2.2, smul_smul, ← map_mul, Units.inv_mul, map_one,
      one_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.LevelForms.eOp_eq_sum, map_sum, map_sum]
  simp only [map_smulₛₗ, map_smul, htw]
  refine MultilinearMap.ext fun v => ?_
  simp only [RealDat.eWf, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply, postOn_apply, RingHom.id_apply]
  all_goals rfl

theorem exists_w0C_eq (i : Fin D.R.m) {w : (R.HW i (sg0 D A)).H} (h1 : w ∈ R.WS F false i (sg0 D A)) :
    ∃ c, Tw.out (s := twAt D.what₂.embLL A.v0) ((R.toCx F).w0C false i c) = w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 h1
  have hs : ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F) false)).ne'
  let c' : Fin ((R.toCx F).dW false i) → ℂ :=
    fun k => cj (twAt D.what₂.embLL A.v0) (c k * ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ)⁻¹)
  have e1 := goodFormsCoordinateMap_apply (R.toCx F) false i c'
  refine ⟨c', (congrArg (Tw.out (s := twAt D.what₂.embLL A.v0)) e1).trans (Eq.trans ?_ hc)⟩
  show ∑ k, cj (twAt D.what₂.embLL A.v0) (c' k) • (((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) •
    R.bC F false i (sg0 D A) k) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cj_cj, smul_smul, inv_mul_cancel_right₀ hs]

theorem exists_srcForm_eq (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (t : T0)
    (Z : Submodule D.what₂.LL (A.fam.L i t).S.Forms) (y : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) Z) → D.what₂.LL) :
    ∃ x, srcForm A i t F.P0 F.ψ0⁻¹ x = (A.fam.L i t).toF (A.fam.lvlA F.P0 F.ψ0) Z y := by
  obtain ⟨x, hx⟩ := exists_lvlE_eq (A.MtCSD i t) (A.leftGroupActionLift i t) A.X hX F.P0 F.ψ0⁻¹
    (((A.fam.L i t).zE (A.fam.lvlA F.P0 F.ψ0) Z).mulVecLin y)
  exact ⟨x, congrArg (fun u => (A.MtCSD i t).basis.equivFun.symm u) hx⟩

theorem out_lift_toL (i : Fin D.R.m) (t : T0)
    (y : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t)) → D.what₂.LL) :
    (R.toCx F).θ' i t ((R.toCx F).jL i t (F.cr.toL (R.toCx F).zs false i t y)) =
      Tw.mk (twAt D.what₂.embLL A.v0) (R.thG i t (jVx R i t
        ((A.fam.L i t).toF (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) y))) := rfl

theorem j_eOp_of_adForm (hW : R.models_HW) (hG : R.thP_thG) (hU : R.LUnif) (i : Fin D.R.m) (t : T0) (ph : ℂ)
    (y : Fin (R.nW i) → D.what₂.LL) (u : (R.HV i t).H) (h0 : adForm R i y = ph • R.thF i t u) :
    (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y) = ph • R.thG i t u := by
  have h1 := e_j_eOp R hU i (sg0 D A) y
  unfold adForm at h0
  rw [h0, LinearMap.map_smul, ← hG i t u, ← LinearMap.map_smul] at h1
  exact (hW i _).1 h1

end GlobalTheory.TraceIncl
end
end

