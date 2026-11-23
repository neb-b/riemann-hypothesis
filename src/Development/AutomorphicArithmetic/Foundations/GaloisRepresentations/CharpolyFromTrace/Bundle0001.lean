module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.UnlinkedOfType
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.SplInv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.GoodLiftAlt
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

def TypeRel (s : Level) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin (c + 1) → ℕ) (hd : ∑ b, d b = a) (θ : Fin (c + 1) → (𝓀[w.adicCompletion E])ˣ →* ℂˣ),
      (∀ b, 0 < d b) → HasTypeVec σ.ρ (stdBlocks d hd) θ →
    ∀ art : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h art →
    ∀ η : Fin (c + 1) → (w.adicCompletion E)ˣ →* ℂˣ, (∀ b, IsTameLift (η b) (θ b)) →
      TrSum r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun i s => ι.symm (η (blockOf d hd i) (art (ineIncl h s)))) ∧
      ∀ b₀, Kills r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun s => ι.symm (η b₀ (art (ineIncl h s))))
        fun b s => ι.symm (η (b₀.succAbove b) (art (ineIncl h s)))

def GoodLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ w : HeightOneSpectrum (𝓞 E),
    ∃ (X : UnramifiedFromSplittingCriterion.Fld E Ω) (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
      InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧ InScope .good l P χ' ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ g ∈ Dec (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → IsSplitAt w') ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

def AllLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ →
    ∀ S : Set (HeightOneSpectrum (𝓞 E)), (∀ u ∉ S, ∃ B, (CG.mk π).HasSat u B) → ∀ X : UnramifiedFromSplittingCriterion.Fld E Ω, UnramifiedFromSplittingCriterion.Tower S X →
    ∃ (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
      InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧ InScope .all l P χ' ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

end UpperTheory.Gal.NearKilling
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.IneNorm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

section
variable {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω]

private theorem res_mem_Ine_iff (A : ValuationSubring Ω) (σ : G M Ω) :
    (AlgEquiv.restrictScalarsHom E σ : G E Ω) ∈ Ine (F := E) A ↔ σ ∈ Ine (F := M) A := (Iff.rfl)

end

theorem UpperTheory.Gal.NearKilling.ineNorm :
    IneNorm := by
  intro E M Ω _ _ _ _ _ _ _ _ _ _ _ A v w _ h h' hfix art art' ha ha'
  have hl : ∀ s : Ine (F := E) A, ∃ t : G M Ω, AlgEquiv.restrictScalarsHom E t = (s : G E Ω) := by
    intro s
    exact ⟨{ (s : G E Ω) with commutes' := fun x => hfix s s.2 x }, by ext x; rfl⟩
  have hr : ∀ t : Ine (F := M) A, (AlgEquiv.restrictScalarsHom E (t : G M Ω) : G E Ω) ∈ Ine (F := E) A :=
    fun t => (res_mem_Ine_iff (E := E) (M := M) A (t : G M Ω)).2 t.2
  obtain ⟨r, hrv⟩ : ∃ r : Ine (F := M) A →* Ine (F := E) A,
      ∀ t, (r t : G E Ω) = AlgEquiv.restrictScalarsHom E (t : G M Ω) :=
    ⟨MonoidHom.codRestrict ((AlgEquiv.restrictScalarsHom E).comp (Ine (F := M) A).subtype)
      (Ine (F := E) A) hr, fun t => rfl⟩
  have hbij : Function.Bijective r := by
    constructor
    · intro a b hab
      apply Subtype.ext
      ext x
      have hab' := congrArg Subtype.val hab
      rw [hrv, hrv] at hab'
      exact DFunLike.congr_fun hab' x
    · intro s
      obtain ⟨t, ht⟩ := hl s
      have htm : t ∈ Ine (F := M) A := (res_mem_Ine_iff (E := E) (M := M) A t).1 (ht ▸ s.2)
      exact ⟨⟨t, htm⟩, Subtype.ext ((hrv _).trans ht)⟩
  obtain ⟨e, he⟩ : ∃ e : Ine (F := E) A ≃* Ine (F := M) A, ∀ s, r (e s) = s :=
    ⟨(MulEquiv.ofBijective r hbij).symm, fun s => (MulEquiv.ofBijective r hbij).apply_symm_apply s⟩
  have key : ∀ s, (AlgEquiv.restrictScalarsHom E ((e s : Ine (F := M) A) : G M Ω) : G E Ω) = s := by
    intro s
    rw [← hrv, he]
  refine ⟨e, key, fun s => ?_⟩
  exact GlobalTheory.ArtinNormU.localArtin_normU E M Ω A v w h h' art art' ha ha' _ _
    (fun z => (DFunLike.congr_fun (key s) z).symm)
end

