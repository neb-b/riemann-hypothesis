module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.CompletionDVR
public import Formalism.LocalToGlobal.ProjectiveLattices.GenSectB
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ComplPf
section
namespace Formalism.L2.Pj

open IsLocalRing

theorem complSt_holds : ComplSt := by
  intro W _ _ _ _
  haveI : CharZero (AdicCompletion (maximalIdeal W) W) :=
    charZero_of_injective_algebraMap (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr W)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hl : IsLocalHom (algebraMap W (AdicCompletion (maximalIdeal W) W)) := inferInstance
  exact ⟨⟨AdicCompletion (maximalIdeal W) W⟩, algebraMap W (AdicCompletion (maximalIdeal W) W), hl, ϖ, hϖ,
    GlobalTheory.irreducible_algebraMap_adicCompletion_of_dvr hϖ⟩

end Formalism.L2.Pj
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.GenSectC
section
noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial
open scoped TensorProduct

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem psi_kt (x : Fin m → Ω) (j₀ : Fin m) (q : KT K D m) :
    psi x j₀ (ktToΩ K Ω D m q) = aeval (gs x j₀) q := by
  show aeval (gs x j₀) (MvPolynomial.map (algebraMap K Ω) q) = aeval (gs x j₀) q
  rw [MvPolynomial.aeval_map_algebraMap]

theorem algKTR_apply (q : KT K D m) :
    algebraMap (KTf K D m) (RS K Ω D m) (algebraMap (KT K D m) (KTf K D m) q) =
      algebraMap (ΩT Ω D m) (RS K Ω D m) (ktToΩ K Ω D m q) := by
  exact IsLocalization.map_eq _ _

def Phi (x : Fin m → Ω) (j₀ : Fin m) (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) :
    RS K Ω D m →+* FractionRing (CT Ω D j₀) :=
  IsLocalization.lift (M := KTS K Ω D m)
    (g := (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp (psi x j₀).toRingHom) (by
      rintro ⟨s, hs⟩
      obtain ⟨q, hq, rfl⟩ := hs
      refine isUnit_iff_ne_zero.mpr ?_
      show algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ (ktToΩ K Ω D m q)) ≠ 0
      rw [psi_kt]
      exact fun h => hinj q (nonZeroDivisors.ne_zero hq)
        ((IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))) (h.trans (map_zero _).symm)))

theorem Phi_algebraMap (x : Fin m → Ω) (j₀ : Fin m) (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0)
    (a : ΩT Ω D m) :
    Phi x j₀ hinj (algebraMap (ΩT Ω D m) (RS K Ω D m) a) =
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) :=
  IsLocalization.lift_eq _ _

theorem Phi_mk'_spec (x : Fin m → Ω) (j₀ : Fin m)
    (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) (a : ΩT Ω D m) (y : KTS K Ω D m)
    (v : FractionRing (CT Ω D j₀)) :
    Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) a y) = v ↔
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) =
        algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) * v :=
  IsLocalization.lift_mk'_spec _ _ _ _

theorem ker_Phi (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) :
    Is (K := K) x = RingHom.ker (Phi x j₀ hinj) := by
  apply le_antisymm
  · rw [Is, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, Phi_algebraMap, psi_sec x j₀ hx₀ i, map_zero]
  · intro r hr
    rw [RingHom.mem_ker] at hr
    obtain ⟨⟨a, y⟩, rfl⟩ := IsLocalization.mk'_surjective (KTS K Ω D m) r
    dsimp only at hr ⊢
    rw [Phi_mk'_spec, mul_zero, ← map_zero (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))),
      (IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))).eq_iff,
      psi_eq_zero_iff x j₀ hx₀] at hr
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    apply Ideal.mul_mem_right
    have hle : Ideal.map (algebraMap (ΩT Ω D m) (RS K Ω D m)) (Ideal.span (Set.range (sec x))) ≤
        Is (K := K) x := by
      rw [Ideal.map_span, Is]
      apply Ideal.span_mono
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    exact hle (Ideal.mem_map_of_mem _ hr)

theorem quotient_generic_section_field [CharZero K] (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra (KTf K D m) E), FiniteDimensional (KTf K D m) E ∧
      Nonempty ((RS K Ω D m ⧸ Is (K := K) x) ≃ₐ[KTf K D m] E) := by
  classical
  have halg := halg_of x j₀ htr hbig
  have hind := gs_indep x j₀ hx₀ htr halg
  have hal := gs_alg x j₀ hx₀ htr halg
  have hI : Function.Injective (aeval (gs x j₀) : KT K D m →ₐ[K] CT Ω D j₀) := hind
  have hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0 := fun q hq h =>
    hq (hI (h.trans (map_zero _).symm))
  let χ : KT K D m →+* FractionRing (CT Ω D j₀) :=
    (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp
      (aeval (gs x j₀) : KT K D m →ₐ[K] CT Ω D j₀).toRingHom
  have hχ : Function.Injective χ :=
    (IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp hI
  let baseAlgebra : Algebra (KT K D m) (FractionRing (CT Ω D j₀)) := χ.toAlgebra
  let baseModule : Module (KT K D m) (FractionRing (CT Ω D j₀)) :=
    @Algebra.toModule _ _ _ _ baseAlgebra
  let baseSMul : SMul (KT K D m) (FractionRing (CT Ω D j₀)) := baseAlgebra.toSMul
  let fractionAlgebra : Algebra (KTf K D m) (FractionRing (CT Ω D j₀)) :=
    (IsFractionRing.lift hχ).toAlgebra
  have tower : IsScalarTower (KT K D m) (KTf K D m) (FractionRing (CT Ω D j₀)) :=
    IsScalarTower.of_algebraMap_eq (S := KTf K D m) (A := FractionRing (CT Ω D j₀))
      fun q => (IsFractionRing.lift_algebraMap (K := KTf K D m) hχ q).symm
  have key : ∀ r : KTf K D m, Phi x j₀ hinj (algebraMap (KTf K D m) (RS K Ω D m) r) =
      IsFractionRing.lift hχ r := by
    have h : (Phi x j₀ hinj).comp (algebraMap (KTf K D m) (RS K Ω D m)) = IsFractionRing.lift hχ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (KT K D m)) (RingHom.ext fun q => ?_)
      simp only [RingHom.comp_apply]
      rw [algKTR_apply, Phi_algebraMap, psi_kt, IsFractionRing.lift_algebraMap]
      rfl
    exact fun r => RingHom.congr_fun h r
  let ΦK : RS K Ω D m →ₐ[KTf K D m] FractionRing (CT Ω D j₀) :=
    { Phi x j₀ hinj with commutes' := key }
  have hint : ∀ c : CT Ω D j₀,
      IsIntegral (KTf K D m) (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c) := by
    intro c
    haveI := hal
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin K (Set.range (gs (D := D) x j₀))) c
    let e := hind.aevalEquiv
    have hKT : IsAlgebraic (KT K D m) (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c) := by
      refine ⟨p.map (e.symm : Algebra.adjoin K (Set.range (gs (D := D) x j₀)) →+* KT K D m), ?_, ?_⟩
      · exact (Polynomial.map_ne_zero_iff e.symm.injective).2 hp0
      · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        have hcomp : (algebraMap (KT K D m) (FractionRing (CT Ω D j₀))).comp
              (e.symm : Algebra.adjoin K (Set.range (gs (D := D) x j₀)) →+* KT K D m) =
            (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp
              (algebraMap (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀)) := by
          refine RingHom.ext fun a => ?_
          simp only [RingHom.comp_apply]
          show algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (aeval (gs x j₀) (e.symm a)) = _
          rw [← hind.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
        rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hp, map_zero]
    exact (hKT.extendScalars (IsFractionRing.injective (KT K D m) (KTf K D m))).isIntegral
  obtain ⟨t, ht⟩ := hfg
  let G : Set (FractionRing (CT Ω D j₀)) :=
    Set.range (fun v => algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (X v)) ∪
      (fun ω => algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C ω)) '' (t : Set Ω)
  haveI : Finite G := ((Set.finite_range _).union (t.finite_toSet.image _)).to_subtype
  let E' := IntermediateField.adjoin (KTf K D m) G
  haveI hfd : FiniteDimensional (KTf K D m) E' := IntermediateField.finiteDimensional_adjoin (by
    rintro _ (⟨v, rfl⟩ | ⟨ω, _, rfl⟩) <;> exact hint _)
  have hK : ∀ k : K, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))
      (MvPolynomial.C (algebraMap K Ω k)) ∈ E' := by
    intro k
    have e1 : algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C (algebraMap K Ω k)) =
        algebraMap (KTf K D m) (FractionRing (CT Ω D j₀))
          (algebraMap (KT K D m) (KTf K D m) (MvPolynomial.C k)) := by
      rw [← IsScalarTower.algebraMap_apply]
      show _ = algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (aeval (gs x j₀) (MvPolynomial.C k))
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply]
    rw [e1]
    exact E'.algebraMap_mem _
  have hΩ : ∀ ω : Ω, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C ω) ∈ E' := by
    let θ : Ω →+* FractionRing (CT Ω D j₀) :=
      (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp MvPolynomial.C
    let Si : IntermediateField K Ω := Subfield.toIntermediateField (E'.toSubfield.comap θ) (fun k => hK k)
    have hle : IntermediateField.adjoin K (t : Set Ω) ≤ Si := by
      rw [IntermediateField.adjoin_le_iff]
      intro ω hω
      exact IntermediateField.subset_adjoin (KTf K D m) G (Or.inr ⟨ω, hω, rfl⟩)
    intro ω
    have hω : ω ∈ IntermediateField.adjoin K (t : Set Ω) := by
      rw [ht]
      exact IntermediateField.mem_top
    exact hle hω
  have hmemC : ∀ c : CT Ω D j₀, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c ∈ E' := by
    intro c
    apply MvPolynomial.induction_on c
    · intro ω
      exact hΩ ω
    · intro p q hp hq
      rw [map_add (f := _)]
      exact add_mem hp hq
    · intro p v hp
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin (KTf K D m) G (Or.inl ⟨v, rfl⟩))
  have hrange : ∀ r : RS K Ω D m, Phi x j₀ hinj r ∈ E' := by
    intro r
    obtain ⟨⟨a, y⟩, rfl⟩ := IsLocalization.mk'_surjective (KTS K Ω D m) r
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, Phi_algebraMap]
    refine mul_mem (hmemC _) ?_
    have hy : algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) ≠ 0 := by
      obtain ⟨q, hq, hqy⟩ := y.2
      rw [← hqy, psi_kt]
      intro h
      exact hinj q (nonZeroDivisors.ne_zero hq)
        ((IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))) (h.trans (map_zero _).symm))
    have h1 : Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) (1 : ΩT Ω D m) y) =
        (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y))⁻¹ := by
      rw [Phi_mk'_spec, map_one, map_one, mul_inv_cancel₀ hy]
    rw [h1]
    exact inv_mem (hmemC _)
  let S := ΦK.range
  let L : S →ₗ[KTf K D m] E' :=
    { toFun := fun s => ⟨s.1, by
        obtain ⟨r, hr⟩ := (AlgHom.mem_range ΦK).1 s.2
        rw [← hr]
        exact hrange r⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional (KTf K D m) S :=
    FiniteDimensional.of_injective L (by
      intro a b h
      have h' := congrArg (fun e : E' => (e : FractionRing (CT Ω D j₀))) h
      exact Subtype.ext h')
  have hSf : IsField S := IsField.of_isDomain_of_finite (KTf K D m) S
  let E := S.toIntermediateField' hSf
  let g : RS K Ω D m →ₐ[KTf K D m] E :=
    { toFun := fun r => ⟨ΦK r, ΦK.mem_range_self r⟩
      map_one' := Subtype.ext (map_one ΦK)
      map_mul' := fun a b => Subtype.ext (map_mul ΦK a b)
      map_zero' := Subtype.ext (map_zero ΦK)
      map_add' := fun a b => Subtype.ext (map_add ΦK a b)
      commutes' := fun r => Subtype.ext (ΦK.commutes r) }
  have hg : Function.Surjective g := by
    rintro ⟨v, hv⟩
    obtain ⟨r, rfl⟩ := (AlgHom.mem_range ΦK).1 (show v ∈ S from hv)
    exact ⟨r, rfl⟩
  have hker : RingHom.ker g = Is (K := K) x := by
    rw [ker_Phi x j₀ hx₀ hinj]
    ext r
    simp only [RingHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  refine ⟨E, inferInstance, inferInstance, ?_, ⟨(Ideal.quotientEquivAlgOfEq (KTf K D m) hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg)⟩⟩
  exact FiniteDimensional.of_injective
    ({ toFun := fun e => (⟨e.1, e.2⟩ : S), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      E →ₗ[KTf K D m] S)
    (by
      intro a b h
      have h' := congrArg (fun e : S => (e : FractionRing (CT Ω D j₀))) h
      exact Subtype.ext h')

end Formalism.L2.Pj.GenSect
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.HeckeStabSet
section
noncomputable section

namespace Formalism.L2.Pj

section Hecke

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable (hkIdx : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], pts Ω → Type)
variable (quotR : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω), hkIdx Ω y → pts Ω → Prop)

def hkTerm (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) (H : hkIdx Ω y) : Ω :=
  open Classical in
  if h : ∃ z : pts Ω, quotR Ω y H z then evalAt pts mapR f h.choose else 0

def hkVal (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) : Ω :=
  ∑ᶠ H : hkIdx Ω y, hkTerm pts mapR hkIdx quotR f y H

def HkFin : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω), Finite (hkIdx Ω y)

theorem hkTerm_add (f g : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω)
    (H : hkIdx Ω y) :
    hkTerm pts mapR hkIdx quotR (f + g) y H = hkTerm pts mapR hkIdx quotR f y H + hkTerm pts mapR hkIdx quotR g y H := by
  unfold hkTerm
  split_ifs with h
  · exact evalAt_add _ _ _ _ _
  · exact (add_zero 0).symm

theorem hkTerm_smul (c : K) (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω)
    (H : hkIdx Ω y) :
    hkTerm pts mapR hkIdx quotR (c • f) y H = algebraMap K Ω c * hkTerm pts mapR hkIdx quotR f y H := by
  unfold hkTerm
  split_ifs with h
  · exact evalAt_smul _ _ _ _ _
  · exact (mul_zero _).symm

theorem hkVal_add (hF : HkFin pts hkIdx) (f g : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (y : pts Ω) :
    hkVal pts mapR hkIdx quotR (f + g) y = hkVal pts mapR hkIdx quotR f y + hkVal pts mapR hkIdx quotR g y := by
  haveI := hF Ω y
  unfold hkVal
  simp_rw [hkTerm_add]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

theorem hkVal_smul (c : K) (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) :
    hkVal pts mapR hkIdx quotR (c • f) y = algebraMap K Ω c * hkVal pts mapR hkIdx quotR f y := by
  unfold hkVal
  simp_rw [hkTerm_smul]
  exact (mul_finsum (fun H => hkTerm pts mapR hkIdx quotR f y H) (algebraMap K Ω c)).symm

def HkRel (c : K) (f g : Rules pts) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω),
    evalAt pts mapR g y = algebraMap K Ω c * hkVal pts mapR hkIdx quotR f y

def HkTotal : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) (H : hkIdx Ω y), ∃ z, quotR Ω y H z

def HkFun : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) (H : hkIdx Ω y) (z z' : pts Ω),
    quotR Ω y H z → quotR Ω y H z' → mapR (AlgHom.id K Ω) z z'

def PtsDetect [Fintype ι] (e : ι → ℕ) : Prop :=
  ∀ g ∈ secW pts mapR borR e, (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω),
    evalAt pts mapR g y = 0) → g = 0

def HkEx [Fintype ι] (e : ι → ℕ) (c : K) : Prop :=
  ∀ f ∈ secW pts mapR borR e, ∃ g ∈ secW pts mapR borR e, HkRel pts mapR hkIdx quotR c f g

variable {pts mapR borR hkIdx quotR}

theorem hkRel_unique [Fintype ι] {e : ι → ℕ} (hD : PtsDetect pts mapR borR e) {c : K} {f g g' : Rules pts}
    (hg : g ∈ secW pts mapR borR e) (hg' : g' ∈ secW pts mapR borR e)
    (h : HkRel pts mapR hkIdx quotR c f g) (h' : HkRel pts mapR hkIdx quotR c f g') : g = g' := by
  have hz : g - g' = 0 := by
    refine hD _ (Submodule.sub_mem _ hg hg') ?_
    intro Ω _ _ _ y
    rw [sub_eq_add_neg, ← neg_one_smul K g', evalAt_add, evalAt_smul, h Ω y, h' Ω y]
    simp
  exact sub_eq_zero.1 hz

theorem hkRel_add (hF : HkFin pts hkIdx) {c : K} {f f' g g' : Rules pts} (h : HkRel pts mapR hkIdx quotR c f g)
    (h' : HkRel pts mapR hkIdx quotR c f' g') : HkRel pts mapR hkIdx quotR c (f + f') (g + g') := by
  intro Ω _ _ _ y
  rw [evalAt_add, h Ω y, h' Ω y, hkVal_add _ _ _ _ hF, mul_add]

theorem hkRel_smul {c : K} (a : K) {f g : Rules pts} (h : HkRel pts mapR hkIdx quotR c f g) :
    HkRel pts mapR hkIdx quotR c (a • f) (a • g) := by
  intro Ω _ _ _ y
  rw [evalAt_smul, h Ω y, hkVal_smul, mul_left_comm]

def hkOp [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) : secW pts mapR borR e →ₗ[K] secW pts mapR borR e where
  toFun f := ⟨(hE f.1 f.2).choose, (hE f.1 f.2).choose_spec.1⟩
  map_add' f f' := by
    apply Subtype.ext
    exact hkRel_unique hD (hE _ (f + f').2).choose_spec.1
      (Submodule.add_mem _ (hE f.1 f.2).choose_spec.1 (hE f'.1 f'.2).choose_spec.1)
      (hE _ (f + f').2).choose_spec.2 (hkRel_add hF (hE f.1 f.2).choose_spec.2 (hE f'.1 f'.2).choose_spec.2)
  map_smul' a f := by
    apply Subtype.ext
    exact hkRel_unique hD (hE _ (a • f).2).choose_spec.1
      (Submodule.smul_mem _ a (hE f.1 f.2).choose_spec.1)
      (hE _ (a • f).2).choose_spec.2 (hkRel_smul a (hE f.1 f.2).choose_spec.2)

theorem hkOp_spec [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) (f : secW pts mapR borR e) :
    HkRel pts mapR hkIdx quotR c f (hkOp hE hD hF f) := (hE f.1 f.2).choose_spec.2

def HeckeStabW [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) (W : Submodule K (secW pts mapR borR e)) : Prop :=
  ∀ f ∈ W, hkOp hE hD hF f ∈ W

end Hecke

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

abbrev FDSec (X : Comp → Data E r) : Type := ∀ c, Frame (X c).Ψ r → ℂ

abbrev FPt (X : Comp → Data E r) : Type := Σ c, ((X c).dom : Set (Frame (X c).Ψ r))

def IsHolCusp (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : Prop :=
  ∀ c, P c ∈ (X c).SS (la c)

def supE (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ENNReal :=
  ⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)

def supN (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ℝ := (supE X la P).toReal

theorem pnorm_fac_nonneg (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    0 ≤ ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

theorem pnorm_smul (X : Data E r) (la : Wt X.Ψ r) (a : ℂ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (a • P) x = ‖a‖ * X.pnorm la P x := by
  simp only [Data.pnorm, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

def holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) : Submodule ℂ (FDSec X) :=
  Submodule.span ℂ {P | IsHolCusp X la P}

theorem holCusp_mem_holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X}
    (h : IsHolCusp X la P) : P ∈ holSub X la :=
  Submodule.subset_span h

end Formalism.L2.PjFree
end
end

