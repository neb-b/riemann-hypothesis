module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.KeepsGap
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem conj_into {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A B : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F)))
    (hB : IsPlaceOver B w) :
    ∃ g : G F Ω, (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hmem : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hval : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hmem, ← hmem, map_eq_zero_iff _ g.injective]
  have hdec : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  refine ⟨g, hdec, fun s hs => ⟨hdec s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hval]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hmem y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem flag_at_place {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    (w : HeightOneSpectrum (𝓞 K)) {A B : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F)))
    (hB : IsPlaceOver B w) {κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ} (hκ : FlagAt M m r A κ) :
    ∃ κ' : Fin n → ↥(Dec (F := K) B) →* (Qbar l)ˣ, FlagAt M m (r.comp (res F Ω K)) B κ' := by
  obtain ⟨χ, hχ, ⟨P, hP⟩, hI⟩ := hκ
  obtain ⟨g, hD, hIn⟩ := conj_into w hA hB
  let d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A) :=
    (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _
      fun s => hD s s.2
  have hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
  have hcyc : ∀ (ψ : G F Ω →* (Qbar l)ˣ) (s : G K Ω), ψ (g * res F Ω K s * g⁻¹) = ψ (res F Ω K s) := fun ψ s => by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hrep : ∀ s : G K Ω, P * r g * r (res F Ω K s) * (P * r g)⁻¹ = P * r (g * res F Ω K s * g⁻¹) * P⁻¹ := fun s => by
    rw [map_mul, map_mul, map_inv]
    group
  refine ⟨fun i => (κ i).comp d, fun i => (χ i).comp (res F Ω K), fun i s hs => hχ i _ hs, ⟨P * r g, fun s => ?_⟩,
    fun i s hs => ?_⟩
  · rw [MonoidHom.comp_apply, hrep]
    exact hP (d s)
  · have h := hI i (d s) (hIn s hs)
    rw [hd, hcyc, hcyc] at h
    exact h

end

theorem UpperTheory.V.Z.Keep.keepsGap :
    ∀ (F L Ω : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), 1 ≤ M → (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ κ, Af.FlagAt M m r A κ) → (∀ i j, m i ≠ m j + 1) → Z.Win.Keeps r L := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ l _ n M m r hM hflag hgap w hw _ B hB
  have hlow : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal := by
    change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal
    rwa [map_natCast]
  obtain ⟨A, hA, κ, hκ⟩ := hflag _ hlow
  obtain ⟨κ', hκ'⟩ := flag_at_place w hA hB hκ
  have hfl : IsFlagOn _ _ κ' := hκ'.choose_spec.2.1
  exact ⟨κ', hfl, Lev.unlGap L Ω l n M hM m _ w hw B hB _ hκ' hgap⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

def LocL (T : Tower D) : Prop :=
  ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → (∃ g ∈ Ine (F := T.F) A, Raw.bar D.om (resQ T.F g) ≠ 1) ∨
      ∃ g ∈ Dec (F := T.F) A, Raw.bar D.om (resQ T.F g) = 1 ∧ T.rb wPs g = 1 ∧ T.rb wAl g ≠ 1

structure OrdAt (T : Tower D) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (A : ValuationSubring Ω)
    (κ : Fin 4 → ↥(Dec (F := T.F) A) →* (PadicAlgCl l)ˣ) : Prop where
  flag : Af.IsFlagOn (r.toHomUnits.comp (resQ T.F)) (Dec (F := T.F) A) κ
  red : ∀ i s, ‖(κ i s : PadicAlgCl l) - ((chi D T.pr i (resQ T.F s) : c.Oˣ) : c.O)‖ < 1
  wts : ∃ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) ∧ ∀ i (s : ↥(Dec (F := T.F) A)), (s : G T.F Ω) ∈ U ⊓ Ine (F := T.F) A →
    κ i s ^ 2 = cycBar T.F Ω l s ^ (2 * (D.wts4 i : ℤ))

end

def FlagF : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), ∀ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l),
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r →
    ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ κ, OrdAt T r A κ

def InfCyc : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
    A.valuation (l : Ω) < 1 → ∀ U : Subgroup (G F Ω), IsOpen (U : Set (G F Ω)) →
      ∃ s ∈ U ⊓ Ine (F := F) A, ¬ IsOfFinOrder (cycBar F Ω l s)

def UnlF : Prop :=
  InfCyc → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → T.Ok → LocL T → ∀ (r : G ℚ Ω →* M4 (PadicAlgCl l)) (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
    ∀ κ, OrdAt T r A κ → ∀ i j, κ i ≠ κ j * (cycBar T.F Ω l).comp (Dec (F := T.F) A).subtype

def UnlL : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → T.Ok → ∀ r : G ℚ Ω →* M4 (PadicAlgCl l),
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ κ, OrdAt T r A κ ∧
      ∀ i j, κ i ≠ κ j * (cycBar T.F Ω l).comp (Dec (F := T.F) A).subtype) →
    ∀ w : HeightOneSpectrum (𝓞 T.L), ((l : ℕ) : 𝓞 T.L) ∈ w.asIdeal → Unl1 (r.toHomUnits.comp (resQ T.L)) w

def UpTri : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (M M' B : Matrix (Fin n) (Fin n) k) (d : Fin n → k), Function.Injective d →
    (∀ i j, j < i → M i j = 0) → (∀ i j, j < i → M' i j = 0) → (∀ i, M i i = d i) → (∀ i, M' i i = d i) →
    B * M = M' * B → ∀ i j, j < i → B i j = 0

def FlagQ : Prop :=
  InfCyc → UpTri → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → ∀ r : G ℚ Ω →* M4 (PadicAlgCl l),
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ κ, OrdAt T r A κ) → Flagged r.toHomUnits

def IneOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G ℚ Ω →* GL (Fin n) (PadicAlgCl l))
    (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ H →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, g ∈ H → r g = 1) → IneAb r

def IneQ : Prop :=
  IneOf → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l),
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → IneAb r.toHomUnits

def PtLaws : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → T.Ok → LocL T → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l),
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r →
    IneAb r.toHomUnits ∧ Flagged r.toHomUnits ∧
      ∀ w : HeightOneSpectrum (𝓞 T.L), ((l : ℕ) : 𝓞 T.L) ∈ w.asIdeal → Unl1 (r.toHomUnits.comp (resQ T.L)) w

theorem ptLaws_of (h1 : FlagF) (h2 : InfCyc) (h3 : UnlF) (h4 : UnlL) (h5 : UpTri) (h6 : FlagQ) (h7 : IneOf) (h8 : IneQ) : PtLaws := by
  intro Ω _ _ _ l _ c D T hD ho hL c' h X y hw r hr
  have f := h1 D T c' h X y hw r hr
  exact ⟨h8 h7 D T hD c' h X y hw r hr, h6 h2 h5 D T hD r f, h4 D T hD ho r fun A hA =>
    (f A hA).imp fun κ hκ => ⟨hκ, h3 h2 D T hD ho hL r A hA κ hκ⟩⟩

end UpperTheory.V.Keep
end
end

