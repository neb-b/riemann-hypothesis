module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable

@[expose] public section

-- bundled from Formalism.WachLatticeTwists.CupProductVanishing.H2MapInjective
section
open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

def StatNatInvFG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O],
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ ε : GK p K →* Oˣ, IsCyc p K ε →
    Nonempty (NatInv ε (fun M _ _ _ => IsFGTop O M))

def H2MapInjective : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ε : Γ →* Oˣ),
    Nonempty (NatInv ε (fun M _ _ _ => IsFGTop O M)) →
    ∀ (Y R : Type) [AddCommGroup Y] [Module O Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
      [ContinuousConstSMul O Y] [AddCommGroup R] [Module O R] [TopologicalSpace R]
      [IsTopologicalAddGroup R] [ContinuousConstSMul O R], IsFGTop O Y → IsFGTop O R →
    ∀ i : Y →ₗ[O] R, Continuous i → Function.Injective i →
    ∀ z ∈ characterColumnKernelPairSetVariant (twRep ε Y), Continuous (fun q : Γ × Γ => z q.1 q.2) →
      (∃ f : Γ → R, Continuous f ∧ ∀ g h, i (z g h) = ((ε g : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c : Γ → Y, Continuous c ∧ ∀ g h, z g h = ((ε g : Oˣ) : O) • c h - c (g * h) + c g

def CupClause : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw] (ε : G →* Oˣ),
    IsFGTop O A → Nonempty (NatInv (ε.comp Dw.subtype) (fun M _ _ _ => IsFGTop O M)) →
    ∀ z ∈ characterColumnKernelPairSetVariant (twRep (ε.comp Dw.subtype) (Ymod r χ E)), Continuous (fun q : Dw × Dw => z q.1 q.2) →
      (∃ f : Dw → A, Continuous f ∧ ∀ g h, ((z g h : Ymod r χ E) : A) =
        ((ε (g : G) : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c : Dw → Ymod r χ E, Continuous c ∧ ∀ g h, z g h = ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g

def CupClauseGK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw] (ε : G →* Oˣ),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ e : Dw ≃ₜ* GK p K,
    IsCyc p K ((ε.comp Dw.subtype).comp e.symm.toMulEquiv.toMonoidHom) → IsFGTop O A →
    ∀ z ∈ characterColumnKernelPairSetVariant (twRep (ε.comp Dw.subtype) (Ymod r χ E)), Continuous (fun q : Dw × Dw => z q.1 q.2) →
      (∃ f : Dw → A, Continuous f ∧ ∀ g h, ((z g h : Ymod r χ E) : A) =
        ((ε (g : G) : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c : Dw → Ymod r χ E, Continuous c ∧ ∀ g h, z g h = ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g

end Formalism.RepresentationBoundsCohomology.T2
end
end

-- bundled from Formalism.WachLatticeTwists.CupProductVanishing.StatVhEInChi
section
open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

def StatVhE : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
      [Module.Finite ℤ_[l] O], (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M], Nonempty (M ≃ₗ[O] KO O) →
    ∀ (ρ : Representation O (G E Ω) M), (∀ g m, ρ g m = m) →
    ∀ S : Submodule O (H1z ρ),
      (∀ x ∈ S, ∃ z : coZ1s ρ, Submodule.mkQ _ z = x ∧ IsLocallyConstant (z : G E Ω → M)) →
      (∀ v, S ≤ unrH1 ρ (Ine (F := E) (Av v))) →
      Module.length O S ≤ Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (classNumber E) : ℕ∞)

def StatVhEInChi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
      [Module.Finite ℤ_[l] O], (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (A T' : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
      (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M],
      Nonempty (M ≃ₗ[O] KO O) →
    ∀ (r : G E Ω →* A) (χ : G E Ω →* T'ˣ), (∀ g (m : M), uElt r χ g • m = m) →
    ∀ (D : ℕ → Subgroup (G E Ω)) (places : Finset ℕ)
      (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
      (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
      (Vo VS : Type) (Io : Vo → Subgroup (G E Ω)) (IS : VS → Subgroup (G E Ω)),
      (∀ x ∈ HcG, ∃ z : coZ1s (uRep O (M := M) r χ), Submodule.mkQ _ z = x ∧
        IsLocallyConstant (z : G E Ω → M)) →
      (∀ v, (∃ a, Ine (F := E) (Av v) ≤ Io a) ∨ (∃ a, Ine (F := E) (Av v) ≤ IS a) ∨
        ∃ w ∈ places, ∃ I : Subgroup (D w), F w ≤ unrH1 (resRep (uRep O (M := M) r χ) (D w)) I ∧
          Ine (F := E) (Av v) ≤ I.map (D w).subtype) →
      Module.length O ↥((HcG ⊓ (⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
          ⨅ v, unrH1 (uRep O (M := M) r χ) (IS v)) ⊓
        ⨅ w ∈ places, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤
      Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (classNumber E) : ℕ∞)

end Formalism.RepresentationBoundsCohomology.T2
end
end

-- bundled from Formalism.WachLatticeTwists.CupProductVanishing.Statement
section
open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

section Defs

variable {O G VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT']

def pairF (D : LatData O G VT VT') : H1 D.ρT →ₗ[O] H1 D.ρT' →ₗ[O] FractionRing O :=
  (cupProductH1H1 D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT D.eqT D.contT').compr₂ D.invF

def withInv (D : LatData O G VT VT') (inv : H2 (twist D.ε (KO O)) →ₗ[O] KO O)
    (invF : H2 (twist D.ε (FractionRing O)) →ₗ[O] FractionRing O) : LatData O G VT VT' :=
  { D with inv := inv, invF := invF }

end Defs

end Formalism.RepresentationBoundsCohomology.T2
end
end

