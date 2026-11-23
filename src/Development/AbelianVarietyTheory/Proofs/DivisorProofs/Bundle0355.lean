module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlocksParabolicInductionFiniteLength
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.BZBridge

section Transport

variable {H G V : Type} [Group H] [Group G] [TopologicalSpace H] [TopologicalSpace G]
  [AddCommGroup V] [Module ℂ V]

def subrepCompEquiv (π : Representation ℂ G V) (Φ : H ≃* G) :
    Subrepresentation (π.comp Φ.toMonoidHom : Representation ℂ H V) ≃o Subrepresentation π where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (Φ.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (Φ g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp (π : Representation ℂ G V) (Φ : H ≃* G) (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp Φ.toMonoidHom : Representation ℂ H V) := by
  have := h
  exact (subrepCompEquiv π Φ).isSimpleOrder

theorem isSmooth_comp (π : Representation ℂ G V) (Φ : H ≃ₜ* G) (h : IsSmooth π) :
    IsSmooth (π.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H V) := by
  intro v
  exact (h v).preimage (map_continuous Φ)

theorem isAdmissible_of_comp (π : Representation ℂ G V) (Φ : H ≃ₜ* G) (hs : IsSmooth π)
    (h : IsAdmissible (π.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H V)) : IsAdmissible π := by
  refine ⟨hs, fun K hKo hKc => ?_⟩

  set K' : Subgroup H := K.comap Φ.toMulEquiv.toMonoidHom with hK'
  have hset : (K' : Set H) = Φ.symm '' (K : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨Φ x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      show Φ (Φ.symm y) ∈ K
      simpa using hy
  have hK'o : IsOpen (K' : Set H) := hKo.preimage (map_continuous Φ)
  have hK'c : IsCompact (K' : Set H) := by
    rw [hset]
    exact hKc.image (map_continuous Φ.symm)
  have := h.2 K' hK'o hK'c
  refine Submodule.finiteDimensional_of_le (S₂ := fixed (π.comp Φ.toMulEquiv.toMonoidHom) K') ?_
  intro v hv
  simp only [fixed, eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq] at hv ⊢
  intro x
  have h1 := hv ⟨Φ x, x.2⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
  exact h1

end Transport

def glReindex (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ε : ι ≃ κ) : GL ι K ≃ₜ* GL κ K where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv K K ε).toMulEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩

theorem irreducibleAdmissible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : IrreducibleAdmissible k := by
  intro n _ _ V _ _ π hs hi
  let Φ := glReindex k (Fintype.equivFin n).symm
  exact isAdmissible_of_comp π Φ hs
    (hA k (Fintype.card n) V _ (isSmooth_comp π Φ hs) (isIrreducible_comp π Φ.toMulEquiv hi))

end GlobalTheory.BZBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

open Polynomial

theorem isAlgClosed_fractionRing_of_AIC : ∀ (A : Type) [CommRing A] [IsDomain A], AIC A → IsAlgClosed (FractionRing A) := by
  first
  | exact @_root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing
  | exact _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing
  | (apply _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitFiniteSubextensionRingCocone
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem ringCocone_isColimit (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] :
    Nonempty (IsColimit (ringCocone K Ω)) := by
  haveI : ReflectsColimitsOfShape (FinSub K Ω) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change Ω at x
    have hx : _root_.IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    haveI := IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin K {x}, inferInstance⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨⟨i.1 ⊔ j.1, by haveI := i.2; haveI := j.2; infer_instance⟩,
      homOfLE (le_sup_left (a := i.1)), homOfLE (le_sup_right (b := j.1)), ?_⟩
    apply Subtype.ext
    exact h

end GlobalTheory.SepCech
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjOfIsConjGlFieldExtensionInclusionStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (n : ℕ) (γ γ' : GL (Fin n) F), IsConj (incl F F' n γ) (incl F F' n γ') → IsConj γ γ' := by
  first | (exact @GlobalTheory.Shin.isConj_of_isConj_incl) | (exact GlobalTheory.Shin.isConj_of_isConj_incl) | (intros; apply GlobalTheory.Shin.isConj_of_isConj_incl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDoublingJetOfOrderTwoFirstOrder
section
open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

theorem firstOrder_isJet : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → GlobalTheory.Nef.PathJet.IsJet π ε m β δ 2 (fun f => PowerSeries.C (β (ε f)) + PowerSeries.C (δ f) * PowerSeries.X) := by
  intro A B R _ _ _ π ε m β δ hεπ hmπ hεm hm2 hδ hδπ
  have hεπ' : ∀ b, ε (π b) = b := fun b => by rw [← RingHom.comp_apply, hεπ, RingHom.id_apply]
  have hεm' : ∀ f, ε (m f) = ε f := fun f => by rw [← RingHom.comp_apply, hεm]
  have hδ1 : δ 1 = 0 := by
    have h := hδ 1 1
    simp only [mul_one, map_one, one_mul] at h
    have : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have hdm : ∀ f, δ (m f) = 2 * δ f :=
    deriv_comp_m π ε m β δ hεπ hmπ hm2 hδ hδπ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro f g
    refine ⟨C (-(δ f * δ g)), ?_⟩
    beta_reduce
    rw [hδ, map_mul, map_mul]
    simp only [map_add (f := _), map_mul, map_neg]
    ring
  · intro f g
    simp [map_add (f := _)]
    exact ⟨0, by ring⟩
  · simp [hδ1]
  · intro b
    simp [hεπ', hδπ]
  · intro f
    refine ⟨0, ?_⟩
    beta_reduce
    rw [hεm', hdm]
    have hrC : ∀ x : R, rescale (2 : R) (C x) = C x := by
      intro x; ext n; rw [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]
    simp only [map_add (f := _), map_mul, rescale_X, hrC]
    ring
  · intro f
    simp
  · intro f
    simp [coeff_C, coeff_C_mul, coeff_X]

end GlobalTheory.Nef.PathJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCohomologyEquivalenceIffElementwise
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCEqv

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'),
    Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  intro R _ F E E' f
  obtain ⟨-, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  constructor
  · intro hf
    refine ⟨fun n z hz => ?_, fun n c hc ⟨y, hy⟩ => ?_⟩
    · obtain ⟨x, hx⟩ := (hf n).2 (cl E n z hz)
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, heq] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨c, y, hc, hy⟩
    · obtain ⟨h, hp⟩ := hpull E E' f n c hc
      have h0 : cl E n (((HC R F).map f.op).f n c) h = 0 := (hzero E n _ h).2 ⟨y, hy⟩
      rw [← hp] at h0
      have : cl E' n c hc = 0 := (hf n).1 (h0.trans (map_zero _).symm)
      obtain ⟨b, hb⟩ := (hzero E' n c hc).1 this
      exact ⟨b, hb.symm⟩
  · rintro ⟨hS, hI⟩ n
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, hzero] at hx
      obtain ⟨b, hb⟩ := hI n c hc hx
      exact (hzero E' n c hc).2 ⟨b, hb.symm⟩
    · intro x
      obtain ⟨z, hz, rfl⟩ := hsurj E n x
      obtain ⟨c, y, hc, hcy⟩ := hS n z hz
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      refine ⟨cl E' n c hc, ?_⟩
      rw [hp, heq]
      exact ⟨y, hcy⟩

end GlobalTheory.EtC.HCEqv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayOfIsUnitModStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B), IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) → IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  first | (exact @GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod) | (exact GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod) | (intros; apply GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleAlgebraOfStrictlyHenselianEtaleStalkAfStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIndEtaleAlgebra_of_strictlyHenselianEtaleStalk_affine : ∀ (A : Type) [CommRing A] (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A)), IsStalk O s → ∃ _ : Algebra A O, SH O ∧ IndEt A O ∧ s = Spec.map (CommRingCat.ofHom (algebraMap A O)) := by
  first | (exact @GlobalTheory.EtC.isStalk_affine) | (exact GlobalTheory.EtC.isStalk_affine) | (intros; apply GlobalTheory.EtC.isStalk_affine  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitFiniteSubextensionSpecArrowCone
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem isLimit_leftFunc_arrCone (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (hc : IsColimit (ringCocone K Ω)) :
    Nonempty (IsLimit (Arrow.leftFunc.mapCone (arrCone K Ω))) :=
  ⟨isLimitOfPreserves (Scheme.Spec ⋙ yoneda) hc.op⟩

end GlobalTheory.SepCech
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecSingle
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

namespace GlobalTheory.CechOne

theorem isLimit_cone_one (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (0 + 1) => GlobalTheory.CechOne.fB A B)
      (GlobalTheory.CechOne.fB A B) (fun _ => 𝟙 _) (fun _ => Category.id_comp _))) := by
  refine ⟨WidePullbackCone.IsLimit.mk _ (fun t => t.π 0) ?_ ?_ ?_⟩
  · intro t
    rw [WidePullbackCone.mk_base]
    exact t.condition 0
  · intro t i
    rw [WidePullbackCone.mk_π]
    exact (Category.comp_id (t.π 0)).trans (congrArg t.π (Fin.fin_one_eq_zero i).symm)
  · intro t m _ hπ
    have := hπ 0
    rw [WidePullbackCone.mk_π] at this
    exact (Category.comp_id m).symm.trans this

end GlobalTheory.CechOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecTensorSquare
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section
namespace GlobalTheory.CechOne

theorem isLimit_widePullback_tensor (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (1 + 1) => GlobalTheory.CechOne.fB A B)
      (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) (GlobalTheory.CechOne.y1 A B) (GlobalTheory.CechOne.hy1 A B))) := by
  have H := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B B)
  have e0 : y1 A B 0 = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := rfl
  have e1 : y1 A B 1 = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) := rfl
  refine ⟨WidePullbackCone.IsLimit.mk _ (fun t => H.lift (t.π 0) (t.π 1) ?_) ?_ ?_ ?_⟩
  · exact (t.condition 0).trans (t.condition 1).symm
  · intro t
    change _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) = _
    rw [← hy1 A B 0, ← Category.assoc, e0, H.lift_fst]
    exact t.condition 0
  · intro t i
    fin_cases i
    · exact H.lift_fst _ _ _
    · exact H.lift_snd _ _ _
  · intro t m _ hm
    apply H.hom_ext
    · rw [H.lift_fst, ← hm 0]; rfl
    · rw [H.lift_snd, ← hm 1]; rfl

end GlobalTheory.CechOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafBiprodStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod : ∀ (R : Type) [CommRing R] (M N : Shv R), FlatS M → FlatS N → FlatS (M ⊞ N) := by
  first | (exact @GlobalTheory.EtC.flatS_biprod) | (exact GlobalTheory.EtC.flatS_biprod) | (intros; apply GlobalTheory.EtC.flatS_biprod  <;> assumption)
end

