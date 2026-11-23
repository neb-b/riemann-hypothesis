module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilTransport

theorem conj_nhds : ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] [Algebra.IsAlgebraic E Ω] (E' Ω' : Type)
    [Field E'] [Field Ω'] [Algebra E' Ω'] (φ : Ω ≃+* Ω') (U' : Set (G E' Ω')), U' ∈ nhds (1 : G E' Ω') →
    ∃ U : Set (G E Ω), IsOpen U ∧ (1 : G E Ω) ∈ U ∧
      ∀ σ ∈ U, ∀ σ' : G E' Ω', (∀ z, φ (σ z) = σ' (φ z)) → σ' ∈ U' := by
  intro E Ω _ _ _ _ E' Ω' _ _ _ φ U' hU'
  obtain ⟨L', hL'fin, hL'⟩ := (krullTopology_mem_nhds_one_iff E' Ω' U').mp hU'
  let b := Module.finBasis E' L'
  let S : Set Ω := Set.range fun i => φ.symm (b i : Ω')
  let L : IntermediateField E Ω := IntermediateField.adjoin E S
  haveI : Finite S := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional E L := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen, L.fixingSubgroup.one_mem, ?_⟩
  intro σ hσ σ' hrel
  apply hL'
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  have hb : ∀ i, σ' (b i : Ω') = b i := by
    intro i
    have h1 : φ.symm (b i : Ω') ∈ L := IntermediateField.subset_adjoin E S ⟨i, rfl⟩
    have h2 := (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ _ h1
    have h3 := hrel (φ.symm (b i : Ω'))
    rw [h2, RingEquiv.apply_symm_apply] at h3
    exact h3.symm
  intro x hx
  have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hb]

section Transfer

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω']
  {A' : ValuationSubring Ω'} {φ : Ω ≃+* Ω'}

def conj (φ : Ω ≃+* Ω') (σ : Ω ≃+* Ω) : Ω' ≃+* Ω' := (φ.symm.trans σ).trans φ

@[simp] theorem conj_apply (φ : Ω ≃+* Ω') (σ : Ω ≃+* Ω) (y : Ω') : conj φ σ y = φ (σ (φ.symm y)) := rfl

def conjAlg (φ : Ω ≃+* Ω') (σ : G E Ω)
    (hσ : ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y) : G E' Ω' :=
  AlgEquiv.ofRingEquiv hσ

@[simp] theorem conjAlg_apply (φ : Ω ≃+* Ω') (σ : G E Ω)
    (hσ : ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y) (y : Ω') :
    conjAlg φ σ hσ y = φ (σ (φ.symm y)) := rfl

theorem val_le_one_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (z : Ω) :
    A'.valuation (φ z) ≤ 1 ↔ A.valuation z ≤ 1 := by
  rw [A'.valuation_le_one_iff, A.valuation_le_one_iff, hm]

theorem val_lt_one_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (z : Ω) :
    A'.valuation (φ z) < 1 ↔ A.valuation z < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ φ.injective]

omit [NumberField E'] in
theorem mem_Dec_iff' {K F : Type} [Field K] [Field F] [NumberField F] [Algebra F K] (B : ValuationSubring K)
    (τ : G F K) : τ ∈ Dec (F := F) B ↔ ∀ x, τ x ∈ B ↔ x ∈ B := by
  refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => mem_Dec.mpr ?_⟩
  ext x
  have := h ((τ⁻¹ : G F K) x)
  rw [mul_inv_apply] at this
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  exact this.symm

theorem mem_Dec_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) {σ : G E Ω} {σ' : G E' Ω'}
    (hrel : ∀ z, φ (σ z) = σ' (φ z)) : σ' ∈ Dec (F := E') A' ↔ σ ∈ Dec (F := E) A := by
  rw [mem_Dec_iff', mem_Dec_iff']
  constructor
  · intro h x; rw [← hm, hrel, h, hm]
  · intro h x; obtain ⟨z, rfl⟩ := φ.surjective x; rw [← hrel, hm, hm, h]

theorem actsAs_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) {σ : G E Ω} {σ' : G E' Ω'}
    (hrel : ∀ z, φ (σ z) = σ' (φ z)) (q a b : ℕ) : ActsAs A' q σ' a b ↔ ActsAs A q σ a b := by
  unfold ActsAs
  rw [mem_Dec_iff hm hrel]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h x hx
    have := h (φ x) ((val_le_one_iff hm x).mpr hx)
    rwa [← hrel, ← map_pow φ, ← map_pow φ, ← map_sub φ, val_lt_one_iff hm] at this
  · intro h x hx
    obtain ⟨z, rfl⟩ := φ.surjective x
    rw [val_le_one_iff hm] at hx
    rw [← hrel, ← map_pow φ, ← map_pow φ, ← map_sub φ, val_lt_one_iff hm]
    exact h z hx

end Transfer

section Smooth

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem smooth_comp (φ : Ω ≃+* Ω') (e : Weil h →* Weil h')
    (he : ∀ (σ : Weil h) z, φ ((σ : G E Ω) z) = (e σ : G E' Ω') (φ z)) (hdeg : ∀ σ, deg (e σ) = deg σ)
    {M : Type} [Monoid M] (f : Weil h' →* M) (hf : IsSmooth f) : IsSmooth (f.comp e) := by
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  obtain ⟨O', hO', hpre⟩ := isOpen_induced_iff.mp hf
  have h1 : (1 : G E' Ω') ∈ O' := by
    have : (1 : Ine (F := E') A') ∈ Subtype.val ⁻¹' O' := by rw [hpre]; simp
    exact this
  obtain ⟨U, hU, hU1, hUO⟩ := conj_nhds E Ω E' Ω' φ O' (hO'.mem_nhds h1)
  refine IsSmooth.of_open (U := Subtype.val ⁻¹' U) (hU.preimage continuous_subtype_val) hU1 ?_
  intro τ hτ
  have hmem : ((e (ineIncl h τ) : Weil h') : G E' Ω') ∈ Ine (F := E') A' := by
    rw [← deg_eq_zero_iff, hdeg, deg_ineIncl]
  have hO : (⟨_, hmem⟩ : Ine (F := E') A') ∈ Subtype.val ⁻¹' O' := hUO τ hτ _ (he (ineIncl h τ))
  rw [hpre] at hO
  have e1 : ineIncl h' ⟨_, hmem⟩ = e (ineIncl h τ) := Subtype.ext rfl
  rw [Set.mem_setOf_eq, e1] at hO
  exact hO

end Smooth

open GlobalTheory.LocLanglands in
theorem weil_equiv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∃ c : Weil h ≃* Weil h', (∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ') ∧ (∀ σ, deg (c σ) = deg σ) ∧ normV w' = normV w ∧ ∀ (M : Type) [Monoid M] (f : Weil h' →* M), GlobalTheory.WeilDeligne.IsSmooth f ↔ GlobalTheory.WeilDeligne.IsSmooth (f.comp c.toMonoidHom) := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP
  haveI : CharZero Ω' := (RingHom.charZero_iff (algebraMap E' Ω').injective).mp inferInstance
  haveI : Algebra.IsAlgebraic E' Ω' := IsAlgClosure.isAlgebraic
  have fixE : ∀ σ : G E Ω, σ ∈ Dec (F := E) A →
      ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y := by
    intro σ hσ y
    refine _root_.GlobalTheory.FixApprox.fix_of_approx Ω' A' (conj φ σ.toRingEquiv) ?_ _ ?_ ?_
    · intro z
      rw [conj_apply, hP.mem, AlgEquiv.coe_ringEquiv, apply_mem_iff_of_mem_Dec hσ]
      conv_rhs => rw [← φ.apply_symm_apply z]
      rw [hP.mem]
    · exact (IsIntegral.map (algebraMap E' Ω').toRatAlgHom
        (Algebra.IsIntegral.isIntegral (R := ℚ) y)).isAlgebraic
    · intro δ hδ
      obtain ⟨x, hx⟩ := _root_.GlobalTheory.approx_of_completion_equiv E w E' Ω' A' w' h' j i hP.cont hP.loc y δ hδ
      refine ⟨algebraMap E' Ω' (j x), ?_, hx⟩
      rw [conj_apply, ← hP.ext, RingEquiv.symm_apply_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  have fixE' : ∀ σ' : G E' Ω', ∀ x : E,
      conj φ.symm σ'.toRingEquiv (algebraMap E Ω x) = algebraMap E Ω x := by
    intro σ' x
    rw [conj_apply, RingEquiv.symm_symm, hP.ext, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, ← hP.ext,
      RingEquiv.symm_apply_apply]
  have hrelC : ∀ (σ : G E Ω) (hσ : ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y) z,
      φ (σ z) = conjAlg φ σ hσ (φ z) := by
    intro σ hσ z; rw [conjAlg_apply, RingEquiv.symm_apply_apply]
  have hrelC' : ∀ (σ' : G E' Ω') z, φ (conjAlg φ.symm σ' (fixE' σ') z) = σ' (φ z) := by
    intro σ' z; rw [conjAlg_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
  have q_eq : normV w' = normV w := by
    apply le_antisymm
    · obtain ⟨σ, hσ⟩ := exists_isFrob h
      have hrel := hrelC σ (fixE σ hσ.1)
      refine _root_.GlobalTheory.NormLeFrob.normV_le_of_isFrob E' Ω' A' w' h' (normV w) (one_lt_normV w) (conjAlg φ σ (fixE σ hσ.1)) ?_
      rw [← actsAs_one_iff, actsAs_iff hP.mem hrel, actsAs_one_iff]; exact hσ
    · obtain ⟨τ', hτ'⟩ := exists_isFrob h'
      have hrel := hrelC' τ'
      refine _root_.GlobalTheory.NormLeFrob.normV_le_of_isFrob E Ω A w h (normV w') (one_lt_normV w') (conjAlg φ.symm τ' (fixE' τ')) ?_
      rw [← actsAs_one_iff, ← actsAs_iff hP.mem hrel, actsAs_one_iff]; exact hτ'
  have memW : ∀ σ : Weil h, conjAlg φ (σ : G E Ω) (fixE σ (Weil_le_Dec h σ.2)) ∈ Weil h' := by
    intro σ
    obtain ⟨a, b, hab⟩ := σ.2
    refine ⟨a, b, ?_⟩
    rw [q_eq, actsAs_iff hP.mem (hrelC _ _)]; exact hab
  have memW' : ∀ σ' : Weil h', conjAlg φ.symm (σ' : G E' Ω') (fixE' σ') ∈ Weil h := by
    intro σ'
    obtain ⟨a, b, hab⟩ := σ'.2
    refine ⟨a, b, ?_⟩
    rw [← q_eq, ← actsAs_iff hP.mem (hrelC' _)]; exact hab
  let c : Weil h ≃* Weil h' :=
    { toFun := fun σ => ⟨_, memW σ⟩
      invFun := fun σ' => ⟨_, memW' σ'⟩
      left_inv := fun σ => by ext z; simp
      right_inv := fun σ' => by ext z; simp
      map_mul' := fun σ τ => by ext z; simp }
  have hc : ∀ σ y, ((c σ : Weil h') : G E' Ω') y = φ ((σ : G E Ω) (φ.symm y)) := fun _ _ => rfl
  have hcs : ∀ σ' y, ((c.symm σ' : Weil h) : G E Ω) y = φ.symm ((σ' : G E' Ω') (φ y)) := fun _ _ => rfl
  have hrel : ∀ (σ : Weil h) z, φ ((σ : G E Ω) z) = ((c σ : Weil h') : G E' Ω') (φ z) := by
    intro σ z; rw [hc, RingEquiv.symm_apply_apply]
  have hdeg : ∀ σ, deg (c σ) = deg σ := by
    intro σ
    obtain ⟨a, b, hab⟩ := σ.2
    rw [deg_eq hab, deg_eq (σ := c σ) (a := a) (b := b) (by rw [q_eq, actsAs_iff hP.mem (hrel σ)]; exact hab)]
  refine ⟨c, ?_, hdeg, q_eq, ?_⟩
  · intro σ σ'
    constructor
    · intro hr
      ext y
      obtain ⟨z, rfl⟩ := φ.surjective y
      rw [← hrel]
      exact hr z
    · rintro rfl z
      exact hrel σ z
  · intro M _ f
    constructor
    · exact smooth_comp φ c.toMonoidHom hrel hdeg f
    · intro hf
      have hrel' : ∀ (σ' : Weil h') z, φ.symm ((σ' : G E' Ω') z) = ((c.symm σ' : Weil h) : G E Ω) (φ.symm z) := by
        intro σ' z; rw [hcs, RingEquiv.apply_symm_apply]
      have hdeg' : ∀ σ', deg (c.symm σ') = deg σ' := by
        intro σ'; rw [← hdeg, MulEquiv.apply_symm_apply]
      have := smooth_comp φ.symm c.symm.toMonoidHom hrel' hdeg' (f.comp c.toMonoidHom) hf
      convert this using 1
      ext σ'
      simp

end GlobalTheory.WeilTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

variable {D : D7}

abbrev OI (v : FinPl D) : Type := v.adicCompletionIntegers D.host.F

def InvForm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u, IsHalf e u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f

def InPow {v : FinPl D} (ϖ : OI v) (N : ℕ) {m n : Type} (x : Matrix m n (Fv D.host.F v)) : Prop :=
  ∀ i j, ∃ o : OI v, x i j = algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N * o)

def Bdd {v : FinPl D} (ϖ : OI v) (N : ℕ) {m n : Type} (x : Matrix m n (Fv D.host.F v)) : Prop :=
  ∀ i j, ∃ o : OI v, algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N) * x i j = algebraMap (OI v) (Fv D.host.F v) o

def comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  c.sum fun u z => z • heisO ψ S T u f

def RelOff (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D)) (p f : WO S T → ℂ) : Prop :=
  ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) → comb ψ S T c p = 0 → comb ψ S T c f = 0

def CoEig (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (p f : WO S T → ℂ) (u : WO S T) : Prop :=
  ∃ c : ℂ, heisO ψ S T u p = c • p ∧ heisO ψ S T u f = c • f

def Shape (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (A : Set (WO S T)) (x₀ : WO S T) (f : WO S T → ℂ) : Prop :=
  (∀ z ∈ A, heisO ψ S T z f = f) ∧
    ∀ y, IsHalf e y → (∀ z ∈ A, ψ (symplO S T z y) = 1) → heisO ψ S T y f = ψ (symplO S T x₀ y) • f

def halfPow {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) (ϖ : OI v) (N : ℕ) : Set (WO S T) :=
  {z | IsHalf (cA D e) z ∧ InPow ϖ N (adjCo φ S T BS BT z)}

def rowIx {n r t : ℕ} (h : r + t = n) : Fin r ⊕ Fin t ≃ Fin n := finSumFinEquiv.trans (finCongr h)

def co {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) {r t : ℕ} (hS : r + t = S.rank) (hT : r = T.rank) (x : WO S T) :
    Matrix (Fin r ⊕ Fin t) (Fin r) (Fv D.host.F v) :=
  (adjCo φ S T BS BT x).submatrix (rowIx hS) (finCongr hT)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rank_V (i : Fin D.R.m) : D.R.r + D.R.t = (Vc D i).rank := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm

theorem rank_weight_component_eq (i : Fin D.R.m) : D.R.r = (Wc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm

def coR (R : RealDat D A Ks) (i : Fin D.R.m) {v : FinPl D} (φ : SplitProj D v) (x : WO (Vc D i) (Wc D i)) :
    Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) :=
  co φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (rank_V i) (rank_weight_component_eq i) x

def ActAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) {v : FinPl D} (φ : SplitProj D v) (e : AE D)
    (red : OI v →+* kP PP) : Prop :=
  ∀ h : GL (Fin (Vc D i).rank) (OI v), ∃ κ : GA D (Vc D i), Formalism.L2.Theta.SuppAt e (Vc D i) κ ∧ κ ∈ GfC (Vc D i) ∧
    finE (Vc D i) κ ∈ Formalism.L2.DIV.St (R.βV i) ∧
    grpCo φ (Vc D i) (frCo φ (R.βV i)) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h ∧
    redFn (R.βV i) PP (finE (Vc D i) κ) = Matrix.GeneralLinearGroup.map red h ∧
    (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) ∧
    ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      ℓ (R.ωP i t (κ, 1) f) = ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map red h)) : ℂˣ) : ℂ) * ℓ f

theorem placeIdem_eq {v : FinPl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (AE D) ε = idem D (.inl v) := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', e', h1', h2'⟩ := ((GlobalTheory.PlaceTensor.idem_spec D).2.2.2.1 v).2.2
  have : α = α' := by
    apply Subtype.ext
    funext w
    by_cases hw : w = v
    · subst hw; exact h1.trans h1'.symm
    · exact (h2 w hw).trans (h2' w hw).symm
  rw [this, ← e']
  rfl

theorem suppIn_of_suppAt {v : FinPl D} {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) {Sb : Finset (FinPl D)}
    (hv : v ∈ Sb) {V : HSp D} {g : GA D V} (hg : Formalism.L2.Theta.SuppAt e V g) : SuppIn Sb V g := by
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  have hg' : ∀ i j, idem D (.inl v) * (Formalism.L2.Theta.mt V g - 1) i j = (Formalism.L2.Theta.mt V g - 1) i j := fun i j => by
    rw [← he.2.1]; exact hg i j
  refine ⟨Matrix.ext fun i j => ?_, fun w hw ε hε i j => ?_⟩
  · rw [Matrix.map_apply, ← hg', map_mul, (h4 v).1, zero_mul]; rfl
  · rw [placeIdem_eq hε, ← hg', ← mul_assoc, h2 _ _ (fun h => hw (by rw [Sum.inl.inj h]; exact hv)), zero_mul]

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardModuleProperties
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.LocGL.IrrProdL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_eq_of_isL {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {𝔪 : Multiset (Segment k)} (h : IsL 𝔪 π) : (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, ⟨Δ, ⟨rfl, -⟩, hΔ⟩, -⟩ := h
  rw [← hd, Multiset.map_map]
  exact Finset.sum_congr rfl fun i _ => (hΔ i).deg_eq

theorem isL_add [CharZero k] (H : GlobalTheory.Published.LanglandsMultisegments) {𝔪 𝔫 : Multiset (Segment k)} (x t y : IrrGL (k := k))
    (hx : IsL 𝔪 x.rep) (ht : IsL 𝔫 t.rep) (hy : IsL (𝔪 + 𝔫) y.rep)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (x.1 + t.1)) k) V)
    (hπ : π.IsIrreducible) (φ : π.Equiv (prod₂ x.rep t.rep)) : IsL (𝔪 + 𝔫) π := by
  have e : y.1 = x.1 + t.1 := by
    rw [← deg_eq_of_isL hy, ← deg_eq_of_isL hx, ← deg_eq_of_isL ht, Multiset.map_add (f := _), Multiset.sum_add]
  obtain ⟨n, c⟩ := y
  dsimp only at e
  subst e
  have hd : ∑ a, (![x, t] a).1 = x.1 + t.1 := Fin.sum_univ_two _
  have hs := (H k).2 𝔪 𝔫 ![x, t] ⟨x.1 + t.1, c⟩ hd hx ht hy
  obtain ⟨ψ⟩ := nonempty_prod₂_equiv_prodIrr_pair x t hd
  let χ := φ.trans ψ
  have hs' := hs.trans (IsSubquotient.of_surjective χ.toIntertwiningMap χ.toLinearEquiv.surjective)
  obtain ⟨ω⟩ := IsSubquotient.nonempty_equiv hs' hy.irr_smooth.1 hπ
  exact hy.of_equiv ω.symm

theorem isL_sum_of_isIrreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π := by
  intro k _ _ _ _ _ H P hP h
  induction h with
  | zero =>
    rintro N x hd 𝔪 - - V _ _ π hπ ⟨φ⟩
    refine ⟨0, x, hd, ⟨Fin.elim0, ⟨by simp, fun i => i.elim0⟩, fun i => i.elim0⟩, ?_⟩
    exact (isCosocle_self hπ).of_equiv (.refl _) φ
  | succ h ih =>
    rintro N x hd 𝔪 hL hm V _ _ π hπ ⟨φ⟩
    have e : N = (x 0).1 + ∑ i : Fin h, (x i.succ).1 := hd.symm.trans (Fin.sum_univ_succ _)
    subst e
    obtain ⟨ψ⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ (fun a => (x a).1) hd fun a => (x a).rep
    let τ := prodIrr (fun i : Fin h => x i.succ) rfl
    have hτs : IsSmooth τ := isSmooth_prodIrr _ _
    have χ : π.Equiv (prod₂ (x 0).rep τ) := φ.trans ψ.symm
    have hτi : τ.IsIrreducible := GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ k _ _ _ _ _ (x 0).rep τ π
      (x 0).2.rep.smooth (x 0).2.rep.irr hτs hπ ⟨χ⟩
    have hτ : IsL (∑ i : Fin h, 𝔪 i.succ) τ :=
      ih _ (fun i => x i.succ) rfl (fun i => 𝔪 i.succ) (fun i => hL _) (fun i => hm _) _ τ hτi ⟨.refl _⟩
    obtain ⟨y, hy⟩ := hP (∑ j, 𝔪 j) fun Δ hΔ => by
      obtain ⟨j, -, hj⟩ := Multiset.mem_sum.1 hΔ
      exact hm j Δ hj
    rw [Fin.sum_univ_succ] at hy ⊢
    exact isL_add H (x 0) (IrrGL.of τ hτs hτi) y (hL 0) (hτ.of_equiv (IrrGL.equivOf τ hτs hτi)) hy π hπ
      (χ.trans (prod₂Equiv (.refl _) (IrrGL.equivOf τ hτs hτi)))

end GlobalTheory.LocGL.IrrProdL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGLStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supercuspidalSupport_unique_GL : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (s t : Multiset (IrrGL (k := k))), HasSupport x.rep s → HasSupport x.rep t → s = t := by
  first | exact @GlobalTheory.LocGL.SupportUnique.hasSupport_unique | exact GlobalTheory.LocGL.SupportUnique.hasSupport_unique | (intros; apply GlobalTheory.LocGL.SupportUnique.hasSupport_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
section
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT

namespace GlobalTheory.SphSupport

theorem toral_of_isSpherical (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k))
    (hs : IsSpherical x.rep) :
    ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, ∃ (χ : kˣ →* ℂˣ) (hχ : IsUnram χ), y = IrrGL.ofChar χ
      (isSmoothChar_of_isUnram hχ) := by
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i =>
    isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have H : IsCuspSupport x.rep (fun _ : Fin x.1 => 1) fun a => detRep (Fin 1) (unrChar k (α a)) :=
    ⟨x.2.rep.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k x.1 fun i => unrChar k (α i))⟩
  refine ⟨_, hasSupport_of_isCuspSupport H, ?_⟩
  intro y hy
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), rfl⟩

theorem toral_and_good_of_isSpherical : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)),
      IsSpherical x.rep → Toral x ∧ Good x := by
  intro hBZ k _ _ _ _ x hs
  obtain ⟨s, hsup, hs1⟩ := toral_of_isSpherical hBZ k x hs
  have h1 : ∀ y ∈ s, y.1 = 1 := fun y hy => by
    obtain ⟨χ, -, rfl⟩ := hs1 y hy
    rfl
  exact ⟨⟨s, hsup, h1⟩, ⟨s, hsup, fun y hy => Or.inl (h1 y hy)⟩⟩

end GlobalTheory.SphSupport
end

