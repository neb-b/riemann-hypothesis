module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Down2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescWeak
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0762
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

open UpperTheory.V.Published

structure HypothesesH : Prop extends toClassicalTheorems : Hypotheses₂ where
  descU : Z.Desc.DescWeak
  cyc : Z.Bc.CycC
  cyc2 : Z.Bc.Desc2
  quat : DefQuatExists
  ssR : CuspSemisimpleReal

def AutBridge : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)),
    (∀ [IsTotallyReal F], IsAut ι r ↔ IsAutR ι r) ∧
    (∀ [_root_.NumberField.IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π) ∧
    ∀ [IsCMField F], IsAutCsd ι r → IsAut ι r

def Twi : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (κ : G F Ω →* (Qbar l)ˣ), IsAut ι r → IsAlgChar ι κ → IsAut ι (tw r κ)

def AlgOfCyc : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    (∀ κ : G F Ω →* (Qbar l)ˣ, Continuous κ →
      (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
        ∃ (a : ℤ) (k : ℕ), 0 < k ∧ ∀ s ∈ Ine (F := F) A, (κ s * cycBar F Ω l s ^ (-a)) ^ k = 1) → IsAlgChar ι κ) ∧
    (∀ κ κ' : G F Ω →* (Qbar l)ˣ, IsAlgChar ι κ → IsAlgChar ι κ' → IsAlgChar ι (κ * κ') ∧ IsAlgChar ι κ⁻¹) ∧
    ∀ (M : Type) [Field M] [NumberField M] [Algebra F M] [Algebra M Ω] [IsScalarTower F M Ω] [IsAlgClosure M Ω]
      (κ : G F Ω →* (Qbar l)ˣ), IsAlgChar ι κ → IsAlgChar ι (κ.comp (resG F M Ω))

def SelfDualC : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n), AttC ι r π →
    ∀ (χ : HChar (maximalRealSubfield F)) (μ : G (maximalRealSubfield F) Ω →* (Qbar l)ˣ), IsLAdicCharOf ι χ μ →
    ∀ (c : G (maximalRealSubfield F) Ω) (P : GL (Fin n) (Qbar l)), IsConjEl c →
      IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * μ.comp (resG (maximalRealSubfield F) F Ω)) P →
      GlobalTheory.ContraPair.DualIsConjBy π (compNorm F χ)

def SelfDualR : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n), AttR ι r π →
    ∀ (θ : G F Ω →* (Qbar l)ˣ) (χ : HChar F), DualTw r θ → IsCharOf ι χ (θ * cycBar F Ω l ^ ((n : ℤ) - 1)) →
      π.IsSelfDualBy χ ∧ ((∀ c c' : G F Ω, IsConjEl c → IsConjEl c' → θ c = θ c') → π.Polarized χ)

def CsdOf : Prop :=
  ∀ (F₀ F Ω : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω]
    [Algebra F Ω] [IsScalarTower F₀ F Ω] [IsAlgClosure F Ω], IsTotallyReal F₀ → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ),
    1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (c : G F₀ Ω) (P : GL (Fin n) (Qbar l)), IsConjEl c → IsAut ι r →
      IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ))) P → IsAutCsd ι r

def ExC : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub F n) (χ : HChar (maximalRealSubfield F)), (CG.mk π).IsRegAlg →
    (∀ v v' : InfinitePlace (maximalRealSubfield F), χ.locInf v (-1) = χ.locInf v' (-1)) →
    GlobalTheory.ContraPair.DualIsConjBy π (compNorm F χ) →
    ∃ (χ' : HChar (maximalRealSubfield F)) (r : G F Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ),
      compNorm F χ' = compNorm F χ ∧ IsGalRepOf π χ' ι r wt HT ∧ AttC ι r π ∧
      ∀ r' : G F Ω →* GL (Fin n) (Qbar l), Continuous r' → AttC ι r' π → IsGalRepOf π χ' ι r' wt HT

def ExR : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
    ∃ (r : G F Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ), IsGalRepOfR π ι r wt HT ∧ AttR ι r π ∧
      ∀ r' : G F Ω →* GL (Fin n) (Qbar l), Continuous r' → AttR ι r' π → IsGalRepOfR π ι r' wt HT

def SolDescent : Prop :=
  ∀ (F₀ F M Ω : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Field M] [NumberField M] [Field Ω]
    [Algebra F₀ F] [Algebra F M] [Algebra F₀ Ω] [Algebra F Ω] [Algebra M Ω] [IsScalarTower F₀ F Ω] [IsScalarTower F M Ω]
    [IsAlgClosure F₀ Ω] [IsAlgClosure F Ω] [IsAlgClosure M Ω] [IsGalois F M] [IsCMField F], IsSolvable (M ≃ₐ[F] M) → IsPlusOf F₀ F →
    (IsTotallyReal M ∨ IsCMField M) → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (μ : G F₀ Ω →* (Qbar l)ˣ), Continuous r → IsIrr (r.comp (resG F M Ω)) →
      IsAlgChar ι μ → (∀ c c' : G F₀ Ω, IsConjEl c → IsConjEl c' → μ c = μ c') →
      (∃ (c : G F₀ Ω) (P : GL (Fin n) (Qbar l)), IsConjEl c ∧ IsPairing c r (μ.comp (resG F₀ F Ω)) P) →
      (IsAut ι r ↔ IsAut ι (r.comp (resG F M Ω)))

section Ver

variable {F L Ω : Type} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]
  {C : Type} [CommGroup C]

def VerEq (κ : G L Ω →* C) (ν : G F Ω →* C) : Prop :=
  ∀ g : G F Ω, g ∉ (resG F L Ω).range →
    (∀ s s' : G L Ω, resG F L Ω s' = g * resG F L Ω s * g⁻¹ → κ s * κ s' = ν (resG F L Ω s)) ∧
    ∀ t : G L Ω, resG F L Ω t = g * g → κ t = ν g

end Ver

section Compat

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def LocGlob (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F))
    (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc →
    (((l : ℕ) : 𝓞 F) ∉ w.asIdeal → Lev.WO ι r (rc (algNorm σ))) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) ∧
        Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) (rc (algNorm σ))

def HasHT (r : G F Ω →* GL (Fin n) (Qbar l)) (HT : (F →+* Qbar l) → Multiset ℤ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
      IsdRAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) ∧
      ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) τ (HT τ)

end Compat

def CompatCsd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n), Continuous r →
    (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → AttC ι r π → ∀ w σ, π.IsLocComp w σ → LocGlob ι r w σ

def CompatReal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime],
    l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (χ : HChar F),
    Continuous r → π.IsRegAlg → π.Polarized χ → AttR ι r π → ∀ w σ, π.IsLocComp w σ → LocGlob ι r w σ

def GalUnitary : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
      ∃ (r : G E Ω →* GL (Fin n) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ), Continuous r ∧ IsSSRep r ∧
        (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → IsUnramU σ w →
          ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, r s = 1) ∧
        HasHT r HT ∧
        (∀ (τ : E →+* Qbar l) lam, HasWeightAt σ (ι.toRingHom.comp τ) lam →
          (HT τ).map (fun k : ℤ => (k : ℂ)) = (infOfWeight lam).map fun z => ((n : ℂ) - 1) / 2 - z) ∧
        (∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)),
          IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → LocGlob ι r w τ) ∧
        (∀ c : G (maximalRealSubfield E) Ω, IsConjEl c → ∃ P, IsPairing c r (cycBar E Ω l ^ (1 - (n : ℤ))) P) ∧
        (IsIrr r → ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π ∧
          ∀ φ lam, HasWeightAt σ φ lam → π.HasInfChar φ (infOfWeight lam))

end UpperTheory.V.Af
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Rep

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}

theorem RepIso.symm' (h : RepIso r r') : RepIso r' r := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, fun s => by rw [hg]; group⟩

theorem IsDiagOn.of_iso {H : Subgroup Γ} {χ : Fin n → Γ →* kˣ} (hd : IsDiagOn r H χ) (h : RepIso r r') :
    IsDiagOn r' H χ := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨a, ha⟩ := hd
  refine ⟨a * g⁻¹, fun s hs => ?_⟩
  rw [← ha s hs, hg]
  congr 1
  group

theorem IsFlagOn.of_iso {H : Subgroup Γ} {κ : Fin n → ↥H →* kˣ} (hd : IsFlagOn r H κ) (h : RepIso r r') :
    IsFlagOn r' H κ := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨a, ha⟩ := hd
  refine ⟨a * g⁻¹, fun s => ?_⟩
  have e : a * g⁻¹ * r' s * (a * g⁻¹)⁻¹ = a * r s * a⁻¹ := by rw [hg]; group
  rw [e]
  exact ha s

end Rep

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {r r' : G F Ω →* GL (Fin n) (Qbar l)}

theorem FrobEig.of_iso {ι : Qbar l ≃+* ℂ} {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂ} (H : FrobEig ι r w B)
    (h : RepIso r r') : FrobEig ι r' w B := by
  obtain ⟨g, hg⟩ := h
  intro A hA
  obtain ⟨h1, h2⟩ := H A hA
  refine ⟨fun s hs => by rw [hg, h1 s hs, mul_one, mul_inv_cancel], fun σ hσ => ?_⟩
  rw [← h2 σ hσ, hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem PotCrysAt.of_iso {A : ValuationSubring Ω} (H : PotCrysAt r A) (h : RepIso r r') : PotCrysAt r' A := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨O, i1, i2, i3, Bw, hj, hp⟩ := H
  exact ⟨O, i1, i2, i3, Bw, hj, (GlobalTheory.T.padicHodgeProperties_conj_invariant l (Loc.PP l) F Ω O _ Bw n _ _ g fun s => hg s).2.2.1 hp⟩

theorem LevelAt.of_iso {M : ℕ} {m : Fin n → ℤ} (H : LevelAt l M m r) (h : RepIso r r') : LevelAt l M m r' := fun w hw => by
  obtain ⟨A, hA, χ, κ, h1, h2, h3, h4⟩ := H w hw
  exact ⟨A, hA, χ, κ, h1, h2.of_iso h, h3, h4.imp id fun h5 => h5.of_iso h⟩

theorem continuous_of_iso (H : Continuous r) (h : RepIso r r') : Continuous r' := by
  obtain ⟨g, hg⟩ := h
  have e : (r' : G F Ω → GL (Fin n) (Qbar l)) = fun s => g * r s * g⁻¹ := funext hg
  rw [e]
  exact (continuous_const.mul H).mul continuous_const


variable (F l) in
theorem eventually_not_mem : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    simpa using (Fact.out : l.Prime).ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simpa [Ideal.dvd_span_singleton] using hw

variable [IsAlgClosure F Ω]

theorem Hypotheses₂.exists_rec (P : Hypotheses₂) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) :
    ∃ rc : IrrGL (k := w.adicCompletion F) → WD h, IsRec h rc := by
  have L := P.litN.loc
  obtain ⟨rc, hrc⟩ := L.llc F Ω A w h
  exact ⟨rc, GlobalTheory.T.rec_of_rec_literal L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz F Ω A w h rc hrc⟩

theorem exists_bridge {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[l] O) (_ : TopologicalSpace O)
      (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw := by
  obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l F Ω w A hw h
  obtain ⟨Bw, hBj, -⟩ := hLL L0 le_rfl
  exact ⟨_, _, _, _, Bw, fun x => by rw [hBj]; exact hj x⟩

end UpperTheory.V.Af

end
end

