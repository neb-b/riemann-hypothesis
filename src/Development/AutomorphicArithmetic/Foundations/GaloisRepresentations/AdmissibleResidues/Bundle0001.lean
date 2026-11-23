module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.GalN.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def NoLink (x : GL (Fin n) (Qbar l)) (Q : ℕ) : Prop :=
  ∀ α β : Qbar l, (x : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot α → (x : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot β →
    ∀ k : ℕ, 1 ≤ k → α ^ k ≠ ((Q : Qbar l) * β) ^ k

def UnlinkAt (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) : Prop :=
  ∃ (s : G F Ω) (j : ℕ), 1 ≤ j ∧ IsFrob A (normV w ^ j) s ∧ NoLink (r s) (normV w ^ j)

def Unlinked (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    (r '' (Ine (F := F) A : Set (G F Ω))).Finite → UnlinkAt r w A

def Wit [IsCMField F] (_ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := Unlinked r


omit [NumberField F] in
def WitQ (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

def AutPol [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ AttC ι r π

def AutCsd0 [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π


omit [NumberField F] in
def IsAutomorphicOverImagQuad (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  Continuous r → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      ∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ AttC ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) π

def IsAutCsdN [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  AutCsd0 ι r ∧ (Continuous r → Wit ι r)


section Conv
variable {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}


end Conv

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealDefs
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure AwR (x y : WD h) : Prop where
  pol : ∀ g : ↥(Weil h), x.charPol g = y.charPol g
  n0 : y.mono0 → x = y

theorem AwR.of_eq {x y : WD h} (e : x = y) : AwR x y := ⟨fun _ => by rw [e], fun _ => e⟩

theorem AwR.eq_unr {x y : WD h} (k : AwR x y) (hy : y.unr) : x = y := k.n0 (WD.unr_mono0 _ hy)

def RatioW (x : WD h) : Prop :=
  ∀ φ : ↥(Weil h), deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖
end Local

section Real
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

structure IsGalRU (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ)
    (HT : (F →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 F)) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → AwR (wdOf h hl ι r) (rc (algNorm σ))
  ratio : ∀ (w : HeightOneSpectrum (𝓞 F)) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0 →
      RatioW (wdOf h hl ι r)
  weights : ∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z
  weights_sym : ∀ τ : F →+* Qbar l, HT τ = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw),
      IsdRAt P Bw (r.comp (Dec (F := F) A).subtype) ∧
      (∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw (r.comp (Dec (F := F) A).subtype) τ (HT τ)) ∧
      (∀ σ, π.IsLocComp w σ → GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin a)) ≠ ⊥ →
        GlobalTheory.SmGL.IsSpherical σ.ρ → ∀ rc, IsRec h rc →
          (∀ g : ↥(Weil h), (wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype)).charPol g = (rc (algNorm σ)).charPol g) ∧
          ((rc (algNorm σ)).mono0 → (wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype)).mono0)) ∧
      ∀ σ, π.IsLocComp w σ → GlobalTheory.SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := F) A).subtype)
end Real

def ExRN : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
    ∃ (r : G F Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ), IsGalRU π ι r wt HT ∧ AttR ι r π ∧
      ∀ r' : G F Ω →* GL (Fin n) (Qbar l), Continuous r' → AttR ι r' π → IsGalRU π ι r' wt HT

end UpperTheory.GalN.V
end
end

