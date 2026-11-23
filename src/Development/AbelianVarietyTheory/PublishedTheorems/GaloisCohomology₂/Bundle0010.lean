module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

namespace GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def DepthZeroInertia : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (t : G E Ω), t ∈ Ine (F := E) A →
    Formalism.L2.NT.TameCoupled A κ t L.gen →
    ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))), (cls σ).IsCusp →
    ∀ (τ : FDRep ℂ (Gn g n)) (P : (ZMod g)[X]), IsCuspOf L P τ.character →
    GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
    (rc (cls σ)).inePol t = GlobalTheory.SerSys.TameGen.liftPoly L.teich P

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def DepthZeroWild : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))), (cls σ).IsCusp →
    (∃ v : σ.V, v ≠ 0 ∧ ∀ κ : GL (Fin n) (w.adicCompletion E),
      (∀ a b, Valued.v (((κ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) - 1) a b) < 1) → σ.ρ κ v = v) →
    ∀ t ∈ Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (t y / y - 1) < 1) →
    (rc (cls σ)).inePol t = (X - 1) ^ n

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalOfCusp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def algNorm {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    IrrGL (k := w.adicCompletion E) :=
  (IrrGL.of σ.ρ σ.smooth σ.irred).nu (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)


omit [NumberField E] in
def IsSstAt (P : LocPrime l) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (r : ↥Gw →* GL (Fin a) (Om l)) : Prop :=
  ∃ LL' r', IsModel Bw r LL' r' ∧ IsSst P (Bw.repE LL' r')

variable [IsAlgClosure E Ω] [IsCMField E]

def IsLAdicCharOf (ι : Qbar l ≃+* ℂ) (χ : HChar (maximalRealSubfield E))
    (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ) : Prop :=
  Continuous μ ∧ ∃ (art : Ideles (maximalRealSubfield E) →* Gab (maximalRealSubfield E) Ω)
    (n : (maximalRealSubfield E →+* ℂ) → ℤ), IsGlobalArtin art ∧ IsAlgPos χ n ∧ IsLAdicOf art ι χ n μ

structure IsAttachedAbove (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where

  deRham : IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)

  jumps : ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  iwahori : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      ∀ rc, IsRec h rc → wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

structure IsGalRepOf (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where

  cont : Continuous r

  ss : IsSSRep r

  pol : ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ ∧ ∀ c : Ω ≃+* Ω, IsCMConjOm E Ω c →
    IsConjDual c r (cycBar E Ω l ^ (1 - (a : ℤ)) * μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)))

  away : ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι r (rc (algNorm σ))

  pure : ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    ∃ x : WD h, IsWDOf ι r x ∧ (x.lpTw ((wt : ℝ) / 2)).tempered

  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z

  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)

  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), IsAttachedAbove π ι r HT P h Bw hj

end GlobalTheory.GalOfCusp

namespace GlobalTheory.Published

open GlobalTheory.GalOfCusp

def GaloisRepOfPolarizedCuspidal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → IsPolarized π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), IsGalRepOf π χ ι r wt HT

end GlobalTheory.Published

namespace GlobalTheory.GalOfCusp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem rec_algNorm {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    rc (algNorm σ) = (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2) := by
  obtain ⟨_, _, _, -, H⟩ := H
  exact H.nu_eq _ _

variable [IsCMField E] {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}

theorem IsGalRepOf.wdOf_eq (H : IsGalRepOf π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) :
    wdOf h hl ι r = (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2) :=
  ((H.away w hl A h rc hrc σ hσ).wdOf_eq hl).trans (rec_algNorm hrc σ)

end GlobalTheory.GalOfCusp
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.Published

def GenericUnlinkedGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsGeneric π →
    ∃ (h : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N),
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) ∧ (∀ i, IsLSeg (Δ i) (x i).rep) ∧ Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.UnitaryDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSquareIntegrable (δ : IrrGL (k := k)) : Prop :=
  0 < δ.1 ∧ IsUnitarisable δ.rep ∧
    letI : MeasurableSpace (GL (Fin δ.1) k ⧸ Subgroup.center (GL (Fin δ.1) k)) := borel _
    ∃ μ : Measure (GL (Fin δ.1) k ⧸ Subgroup.center (GL (Fin δ.1) k)), μ.IsHaarMeasure ∧
      ∀ v, ∀ ℓ ∈ smoothPart δ.rep.dual, ∫⁻ q, ‖ℓ (δ.rep q.out v)‖ₑ ^ 2 ∂μ < ⊤

def IsUnitarySpeh (x : IrrGL (k := k)) : Prop := ∃ (δ : IrrGL (k := k)) (m : ℕ), IsSquareIntegrable δ ∧ 1 ≤ m ∧ IsSpeh δ m x.rep

end GlobalTheory.UnitaryDual

namespace GlobalTheory.Published

open GlobalTheory.UnitaryDual

def UnitaryDualGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π →
    ∃ (u : List (IrrGL (k := k))) (τ : List (IrrGL (k := k) × ℝ)), (∀ x ∈ u, IsUnitarySpeh x) ∧
      (∀ p ∈ τ, IsUnitarySpeh p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
      ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), List.ofFn x = GenericUnitary.factors u τ ∧
        Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.Published

def LanglandsMultisegments : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    (∀ (𝔪 𝔫 : Multiset (Segment k)) (x : IrrGL (k := k)), IsL 𝔪 x.rep → IsL 𝔫 x.rep → 𝔪 = 𝔫) ∧
    ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1),
      IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd)

end GlobalTheory.Published

end
end

