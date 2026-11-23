module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.Gu

section Defs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]


variable (Ω) in
abbrev Par (w : HeightOneSpectrum (𝓞 E)) : Type 1 :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (IrrGL (k := w.adicCompletion E) → WD h) → WD h

abbrev cl {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : IrrGL (k := w.adicCompletion E) :=
  IrrGL.of σ.ρ σ.smooth σ.irred

def ParAt {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (p : Par Ω w) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    (((l : ℕ) : 𝓞 E) ∉ w.asIdeal → Lev.WO ι r (p A h rc)) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := E) A).subtype) ∧
        Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (p A h rc)

theorem locGlob_iff {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) : LocGlob ι r w σ ↔ ParAt ι r w fun _ _ rc => rc (algNorm σ) := Iff.rfl

theorem ParAt.congr {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 E)} {p p' : Par Ω w}
    (H : ParAt ι r w p) (e : ∀ A h rc, IsRec h rc → p A h rc = p' A h rc) : ParAt ι r w p' :=
  fun A h rc hrc => e A h rc hrc ▸ H A h rc hrc

structure Compat {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (p : ∀ w : HeightOneSpectrum (𝓞 E), Par Ω w)
    (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  ht : HasHT r HT
  par : ∀ w, ParAt ι r w (p w)

def ex (n d k : ℕ) : ℤ := (d : ℤ) - 2 * k - n

def totPar (n : ℕ) {c : ℕ} {a : Fin c → ℕ} (d : Fin c → ℕ) {w : HeightOneSpectrum (𝓞 E)}
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) : Par Ω w := fun _ _ rc =>
  sumList (List.ofFn fun i => sumList (List.ofFn fun k : Fin (d i) => (rc (cl (ρ i))).lpTw ((ex n (d i) k : ℝ) / 2)))

def satTot (w : HeightOneSpectrum (𝓞 E)) {c : ℕ} (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ) : Multiset ℂˣ :=
  ∑ i, ∑ k : Fin (d i), (S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))

end Defs

def SumAway : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a b : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (r' : G E Ω →* GL (Fin b) (Qbar l)), Continuous r → Continuous r' →
    ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (x x' : WD h),
      IsWDOf ι r x → IsWDOf ι r' x' → IsWDOf ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (x.lpSum x')

def SumHT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (a b : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (r' : G E Ω →* GL (Fin b) (Qbar l)), Continuous r → Continuous r' →
    ∀ HT HT', HasHT r HT → HasHT r' HT' → HasHT (Formalism.MainNotions.SumRepresentations.At.sumRep r r') fun τ => HT τ + HT' τ

def SumTwo : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a b : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (r' : G E Ω →* GL (Fin b) (Qbar l)) p p' HT HT',
    Compat ι r p HT → Compat ι r' p' HT' →
      Compat ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (fun w A h rc => (p w A h rc).lpSum (p' w A h rc)) fun τ => HT τ + HT' τ

def SumRed : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a b : ℕ) (r : Γ →* GL (Fin a) k) (r' : Γ →* GL (Fin b) k), 1 ≤ a → 1 ≤ b →
    ¬ IsIrr (Formalism.MainNotions.SumRepresentations.At.sumRep r r')

def SumFam : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (c : ℕ), 1 ≤ c → ∀ (N : Fin c → ℕ), (∀ i, 1 ≤ N i) → ∀ (n : ℕ), ∑ i, N i = n →
    ∀ (r : ∀ i, G E Ω →* GL (Fin (N i)) (Qbar l)) (p : Fin c → ∀ w : HeightOneSpectrum (𝓞 E), Par Ω w)
      (HT : Fin c → (E →+* Qbar l) → Multiset ℤ), (∀ i, Compat ι (r i) (p i) (HT i)) →
      ∃ R : G E Ω →* GL (Fin n) (Qbar l),
        Compat ι R (fun w A h rc => sumList (List.ofFn fun i => p i w A h rc)) (fun τ => ∑ i, HT i τ) ∧
        (IsIrr R → c = 1 ∧ ∀ i, IsIrr (r i))

def Eta : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (f : ℤ), ∃ (ξ : HChar E) (m : (E →+* ℂ) → ℤ), ξ.IsAlg m ∧
    compNorm E (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2) * ξ)) = 1

def TwistLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (P : CuspSub E a) (t : ℝ) (w : HeightOneSpectrum (𝓞 E))
    (ρ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w ρ →
      ∃ σ, (P.twist (GlobalTheory.HeckeGal.Model.absPow E t)).IsLocComp w σ ∧ cl σ = (cl ρ).nu (t : ℂ)

def CompatPol : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (P : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ξ : HChar E) (m : (E →+* ℂ) → ℤ),
    (CG.mk P).IsRegAlg → IsPolarized P χ → ξ.IsAlg m → GlobalTheory.ContraPair.DualIsConj (P.twist ξ) →
    ∀ σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin a) (w.adicCompletion E)), (∀ w, P.IsLocComp w (σ w)) →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ),
        Compat ι r (fun w _ _ rc => rc (algNorm (σ w))) HT ∧
        ∀ τ : E →+* Qbar l, (HT τ).map (fun k : ℤ => (k : ℂ)) =
          ((CG.mk P).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z

def Half : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (P : CuspSub E a), P.IsCsd →
    ∀ (ρ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin a) (w.adicCompletion E))), (∀ w, P.IsLocComp w (ρ w)) →
    ∀ (m : (E →+* ℂ) → Multiset ℂ), (∀ τ, P.HasInfChar τ (m τ)) → ∀ e : ℤ,
      (∀ τ, (m τ).Nodup ∧ ∀ z ∈ m τ, ∃ j : ℤ, z + (e : ℂ) / 2 = j) →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ),
        Compat ι r (fun w _ _ rc => (rc (cl (ρ w))).lpTw ((e : ℝ) / 2)) HT ∧
        ∀ τ : E →+* Qbar l, (HT τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map fun z => -(z + (e : ℂ) / 2)

def Strings : Prop :=
  ∀ (n c : ℕ) (d : Fin c → ℕ) (m : Fin c → Multiset ℂ) (lam : DomWeight n),
    ∑ i, GlobalTheory.DefiniteBC.spehInf (d i) (m i) = infOfWeight lam →
    (∀ i (k : Fin (d i)), (m i).Nodup ∧ ∀ z ∈ m i, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j) ∧
      ∑ i, ∑ k : Fin (d i), (m i).map (fun z => -(z + (ex n (d i) k : ℂ) / 2)) =
        (infOfWeight lam).map fun z => ((n : ℂ) - 1) / 2 - z

def CompUnique : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (ρ₁ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ₂ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₁ →
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₂ → Nonempty (ρ₁.Equiv ρ₂)

def RecTot : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (n c : ℕ) (a d : Fin c → ℕ) (hn : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (w : HeightOneSpectrum (𝓞 E))
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (σ : ∀ i, SmIrr (GL (Fin (d i * a i)) (w.adicCompletion E))),
    (∀ i, 1 ≤ a i ∧ 1 ≤ d i) → (∀ i, (P i).IsLocComp w (ρ i)) →
    (∀ i, GlobalTheory.SmGL.IsUnitarisable (ρ i).ρ ∧ GlobalTheory.SmGL.IsUnitarisable (σ i).ρ ∧ IsSpeh (cl (ρ i)) (d i) (σ i).ρ) →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), Nonempty (τ.ρ.Equiv (locProd hn w σ)) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
      totPar n d ρ A h rc = rc (algNorm τ)

def FrobTot : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n c : ℕ) (a d : Fin c → ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ), (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) →
      ParAt ι r w (totPar n d ρ) → FrobEig ι r w (algSat n (normV w) (satTot w d S))

def PolOfFrob : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → IsSSRep r →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : Multiset ℂˣ,
      FrobEig ι r w (algSat n (normV w) (B.map (·⁻¹))) ∧ FrobEig ι r (Bc.cPl w) (algSat n (normV (Bc.cPl w)) B)) →
    ∀ c : G (maximalRealSubfield E) Ω, IsConjEl c → ∃ P, IsPairing c r (cycBar E Ω l ^ (1 - (n : ℤ))) P

def SatLink : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (P : CuspSub E a),
    (∀ (w : HeightOneSpectrum (𝓞 E)) (ρ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w ρ →
      ∀ B, (CG.mk P).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w ρ.ρ B) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B

def SatConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    (∀ (a : ℕ) (P : CuspSub E a), P.IsCsd → ∀ B, (CG.mk P).HasSat (Bc.cPl w) B → (CG.mk P).HasSat w (B.map (·⁻¹))) ∧
    ∀ (c : ℕ) (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ),
      satTot w d (fun i => (S i).map (·⁻¹)) = (satTot (Bc.cPl w) d S).map (·⁻¹)

def IrrCase : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ (c : ℕ) (a d : Fin c → ℕ) (hn : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
      (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (m : Fin c → (E →+* ℂ) → Multiset ℂ),
      GlobalTheory.BcSpeh.Parts π a d hn P ρ m → c = 1 → (∀ i, d i = 1) → ∀ r : G E Ω →* GL (Fin n) (Qbar l), IsSSRep r →
      (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ S : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧
        FrobEig ι r w (algSat n (normV w) (satTot w d S))) →
      ∃ Q : CuspSub E n, (CG.mk Q).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj Q ∧ AttC ι r Q ∧
        ∀ φ lam, HasWeightAt π φ lam → Q.HasInfChar φ (infOfWeight lam)

end UpperTheory.V.Af.Gu
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open TensorProduct Module GlobalTheory.CoeffExt
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.ExLib

theorem eventually_sat (hS : SatLoc) {F : Type} [Field F] [NumberField F] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Af F)) V) (hρ : GlobalTheory.PRep.IsSmooth ρ) (h : ∀ w, ∃ σ, LocIsotypic ρ w σ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine .of_forall fun w => ?_
    obtain ⟨σ, hσ, -⟩ := h w
    exact absurd hσ (not_nontrivial V)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hU⟩ := GlobalFixedVectors.exists_KAway_subset (M := 1) ((hρ v).mem_nhds (by simp))
  filter_upwards [S.eventually_cofinite_notMem] with w hw
  obtain ⟨σ, hi⟩ := h w
  obtain ⟨h1, h2⟩ := hS F n w σ
  have hK : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GL (Fin n) (w.adicCompletion F))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F w)
  have h0 : ((1 : ℕ) : 𝓞 F) ∉ w.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  obtain ⟨B, hB⟩ := h1 (hasFixed_of_sum σ.ρ σ.smooth (ρ.comp (locGL F n w)) _ hK hi.2
    ⟨v, hv, fun u hu => hU (GlobalFixedVectors.mem_KAway.2 ⟨locGL_mem_KLev n w h0 hu, fun x hx =>
      pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _⟩)⟩)
  exact ⟨B, (h2 _ _ hi B).2 hB⟩

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  {V' : Type} [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
  [Module ↥L'.1 V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[↥L.1] (ι → V)}

theorem isSst_iff : IsSst P ρ ↔ finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] ↥(K0 K) * finrank ℚ_[l] V := by
  have := L.2
  rw [IsSst, ← finrank_mul_finrank ℚ_[l] ↥L.1 V, ← finrank_mul_finrank ℚ_[l] ↥L.1 ↥(Dst P ρ), mul_left_comm]
  exact (Nat.mul_right_inj finrank_pos.ne').symm

private theorem finrank_fun' {k M ι : Type} [Field k] [AddCommGroup M] [Module k M] [Fintype ι] :
    finrank k (ι → M) = Fintype.card ι * finrank k M := by
  rw [finrank, rank_fun, Cardinal.toNat_mul, Cardinal.toNat_natCast, finrank]

theorem isSst_of_coord (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (h : IsSst P ρ) : IsSst P ρ' := by
  have hm : ∀ x : V' ⊗[ℚ_[l]] Bst P, x ∈ Dst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dst P ρ := fun x => by
    simp only [mem_Dst]
    refine ⟨fun hx i g => by rw [← GlobalTheory.PstExt.tensCoord_stRep P hE, hx g], fun hx g => ?_⟩
    exact (tensCoord E (Bst P)).injective (funext fun i => by rw [GlobalTheory.PstExt.tensCoord_stRep P hE, hx i g])
  let e : ↥(Dst P ρ') ≃ₗ[ℚ_[l]] (ι → ↥(Dst P ρ)) :=
    { toFun := fun x i => ⟨tensCoord E (Bst P) x.1 i, (hm _).1 x.2 i⟩
      invFun := fun y => ⟨(tensCoord E (Bst P)).symm fun i => (y i).1, (hm _).2 fun i => by
        rw [LinearEquiv.apply_symm_apply]; exact (y i).2⟩
      map_add' := fun x y => funext fun i => Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
      map_smul' := fun c x => funext fun i =>
        Subtype.ext (congrFun (((tensCoord E (Bst P)).restrictScalars ℚ_[l]).map_smul c x.1) i)
      left_inv := fun x => Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
      right_inv := fun y => funext fun i =>
        Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i) }
  rw [isSst_iff] at h ⊢
  rw [e.finrank_eq, (E.restrictScalars ℚ_[l]).finrank_eq, finrank_fun', finrank_fun', h, mul_left_comm]

end Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {m : ℕ}

theorem isSst_enlarge {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1)
    (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1) (h : IsSst P (Bw.repE L₁ r₁)) :
    IsSst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isSst_of_coord P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

theorem isSstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsSstAt P Bw r) : IsSstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  refine ⟨L₂, r₂, hm, isSst_of_coord P (ι := Unit) (E := e.symm.trans (LinearEquiv.funUnique Unit _ _).symm)
    (fun g x _ => ?_) (isSst_enlarge P Bw hL r₁ hp)⟩
  change e.symm _ = Bw.repE L₂ _ g (e.symm x)
  rw [e.symm_apply_eq, he, e.apply_symm_apply]

theorem isPstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsPstAt P Bw r) : IsPstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  exact ⟨L₂, r₂, hm, GlobalTheory.PstConj.isPst_congr P e he (GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hp)⟩

theorem wdAt_conj [NumberField E] [IsAlgClosure E Ω] (ι : Om l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
    {r r' : ↥(Dec (F := E) A) →* GL (Fin m) (Om l)} (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) :
    wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  by_cases hr : IsPstAt P Bw r
  · exact GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj r r' p hc hr (isPstAt_conj P Bw p hc hr)
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, wdAt_of_not_isPstAt ι Bw h hj fun hr' =>
      hr (isPstAt_conj P Bw p⁻¹ (fun g => by rw [hc]; group) hr')]

theorem isConjDual_of_iso {k : Type} [Field k] {c : Ω ≃+* Ω} {r r' : G E Ω →* GL (Fin m) k} {μ : G E Ω →* kˣ}
    (H : IsConjDual c r μ) (h : RepIso r r') : IsConjDual c r' μ := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨Q, hQ⟩ := H
  let t : GL (Fin m) k := ⟨(g : Matrix (Fin m) (Fin m) k)ᵀ, ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)ᵀ,
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩
  have ht : (t : Matrix (Fin m) (Fin m) k) = (g : Matrix (Fin m) (Fin m) k)ᵀ := rfl
  have ht' : ((t⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)ᵀ := rfl
  refine ⟨g * Q * t, fun s s' hs => ?_⟩
  rw [hg s', hg s⁻¹]
  simp only [Units.val_mul, mul_inv_rev, hQ s s' hs, Matrix.transpose_mul, ← ht, ← ht', Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem isGalRepOf_of_iso [NumberField E] [IsAlgClosure E Ω] [IsCMField E] {π : CuspSub E m}
    {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r r' : G E Ω →* GL (Fin m) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : IsGalRepOf π χ ι r wt HT) (hs : IsSSRep r') (h : RepIso r r') :
    IsGalRepOf π χ ι r' wt HT := by
  obtain ⟨μ, h1, h2⟩ := H.pol
  have hc := continuous_of_iso H.cont h
  have h3 := fun c hc => isConjDual_of_iso (h2 c hc) h
  obtain ⟨g, hg⟩ := h
  have hg' : ∀ s, g * r s = r' s * g := fun s => by rw [hg, inv_mul_cancel_right]
  refine ⟨hc, hs, ⟨μ, h1, h3⟩, fun w hw A h rc hrc σ hσ => (H.away w hw A h rc hrc σ hσ).of_conj hw g fun s => hg' _,
    fun w hw A h => (H.pure w hw A h).imp fun x hx => ⟨hx.1.of_conj hw g fun s => hg' _, hx.2⟩, H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj => ?_⟩
  have Ha := H.above P AI T w A h O Bw hj
  have e : ∀ s : ↥(Dec (F := E) A), r'.comp (Dec (F := E) A).subtype s = g * r.comp (Dec (F := E) A).subtype s * g⁻¹ :=
    fun s => hg s
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l P E Ω O _ Bw m _ _ g e
  exact ⟨c1 Ha.deRham, fun τ L τ' hτ => c4 _ _ (Ha.jumps τ L τ' hτ), fun σ hσ hf =>
    ⟨isSstAt_conj P Bw g e (Ha.iwahori σ hσ hf).1, fun rc hrc =>
      (wdAt_conj P ι Bw h hj g e).trans ((Ha.iwahori σ hσ hf).2 rc hrc)⟩, fun σ hσ hf => c2 (Ha.crys σ hσ hf)⟩

end UpperTheory.V.Af.ExLib

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.JumpsOpen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af

theorem UpperTheory.V.Af.jumpsOpen {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (A : ValuationSubring Ω)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ)
    (H : Subgroup (G F Ω)) (hH : IsOpen (H : Set (G F Ω))) (hfl : IsFlagOn r (Dec (F := F) A) κ)
    (hI : ∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ H ⊓ Ine (F := F) A → κ i s = cycBar F Ω l s ^ m i)
    (τ : F →+* Qbar l) (J : Multiset ℤ) (hJ : IsJumpsAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) τ J) :
    J = Finset.univ.val.map fun i => -m i := by
  have char_mult (K L : FinExt l) (κ : ↥(GK K) →* (↥L.1)ˣ) (hκ : Continuous fun g => (κ g : ↥L.1)) (w : ℤ)
      (hw : Loc.HasWeight (GK K).subtype κ w) (hd : IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ))
      (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (a : ℤ) : multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ a = if a = -w then 1 else 0 := by
    have := L.2
    have := K.2
    have : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
    obtain ⟨T⟩ := Loc.tiedP l
    have hφ : Topology.IsOpenEmbedding (GK K).subtype :=
      (IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal
    have h := (Loc.charFil (GK K).subtype hφ κ hκ w hw).2
    have hF : ∀ i, Loc.FilT ↥L.1 ↥L.1 i = FilV ((Loc.PP l).PD K) (LL := ↥L.1) (V := ↥L.1) i := fun i => by
      have : (((Loc.PP l).PD (Loc.botExt l)).Fil i).restrictScalars ℚ_[l] =
          (((Loc.PP l).PD K).Fil i).restrictScalars ℚ_[l] := SetLike.coe_injective ((Loc.PP l).PD_Fil _ _ i)
      unfold Loc.FilT FilV
      rw [this]
    have hD : Loc.Ddr (GK K).subtype (Loc.chRep κ) = DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := by
      unfold Loc.Ddr DdR
      refine iInf_congr fun g => ?_
      have h2 : actVdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) g = Loc.actD (GK K).subtype (Loc.chRep κ) g := by
        unfold actVdR Loc.actD
        congr 1
        exact LinearMap.ext fun z => (Loc.PP l).PD_actdR K g z
      rw [h2]
    simp only [Loc.FilD, hF, hD] at h
    have hr := (((GlobalTheory.Per.Components.components_finrank l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep κ)).1 τ).2.2 hd).trans
      (Module.finrank_self _)
    have hle : DdRE ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ ≤ DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := inf_le_left
    set_option synthInstance.maxHeartbeats 200000 in
    have h1 : ∀ i, i ≤ -w → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 1 := fun i hi => by
      rw [FildR, inf_eq_left.2 (hle.trans (inf_eq_left.1 ((h i).1 hi))), hr]
    set_option synthInstance.maxHeartbeats 200000 in
    have h0 : ∀ i, -w < i → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 0 := fun i hi => by
      rw [FildR, le_bot_iff.1 ((inf_le_inf_right _ hle).trans ((h i).2 hi).le), finrank_bot]
    unfold multV
    rcases lt_trichotomy a (-w) with ha | ha | ha
    · rw [h1 a ha.le, h1 (a + 1) ha, ite_eq_right ha.ne]; simp
    · rw [h1 a ha.le, h0 (a + 1) (by omega), ite_eq_left ha]; simp
    · rw [h0 a ha, h0 (a + 1) (by omega), ite_eq_right ha.ne']; simp

  have flag_mult (K L : FinExt l) (n : ℕ) : ∀ (ρ : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1))
      (M : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1) (κ : Fin n → ↥(GK K) →* (↥L.1)ˣ),
      (∀ g x, ρ g x = (M g).mulVec x) → (∀ g i j, j < i → M g i j = 0) → (∀ g i, M g i i = κ i g) →
      IsDR ((Loc.PP l).PD K) ρ → (∀ i, IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i))) ∧
        ∀ τ a, multV ((Loc.PP l).PD K) ρ τ a = ∑ i, multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i)) τ a := by
    obtain ⟨T⟩ := Loc.tiedP l
    induction n with
    | zero =>
      intro ρ M κ _ _ _ _
      refine ⟨fun i => i.elim0, fun τ a => ?_⟩
      have : Subsingleton (TensorProduct ℚ_[l] (Fin 0 → ↥L.1) (Loc.PP l).R.BdR) := inferInstance
      simp [multV, Module.finrank_zero_of_subsingleton]
    | succ n ih =>
      intro ρ M κ hρ hM hκ hd
      let ι : ↥L.1 →ₗ[↥L.1] (Fin (n + 1) → ↥L.1) := LinearMap.single _ (fun _ => ↥L.1) 0
      let π : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1) := LinearMap.funLeft _ _ Fin.succ
      let M' : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1 := fun g => (M g).submatrix Fin.succ Fin.succ
      have hπ : ∀ g x, π (ρ g x) = (M' g).mulVec (π x) := fun g x => by
        funext i
        simp [π, M', hρ, LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
          hM g i.succ 0 (Fin.succ_pos i)]
      have hs : Function.Surjective π := LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
      let ρ' : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1) :=
        { toFun := fun g => Matrix.toLin' (M' g)
          map_one' := LinearMap.ext fun y => by
            obtain ⟨x, rfl⟩ := hs y
            rw [Matrix.toLin'_apply, ← hπ, map_one]; rfl
          map_mul' := fun g h => LinearMap.ext fun y => by
            obtain ⟨x, rfl⟩ := hs y
            rw [mul_apply_eq_comp, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← hπ, ← hπ, ← hπ,
              map_mul]; rfl }
      obtain ⟨d0, d2, hm⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep (κ 0)) _ ρ _ ρ' ι π
        (fun g x => by
          funext i
          rw [hρ]
          refine Fin.cases ?_ (fun i => ?_) i
          · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hκ]
          · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hM g i.succ 0 (Fin.succ_pos i)])
        hπ (fun x y h => by simpa [ι] using congrFun h 0) hs
        (by
          ext x
          simp only [LinearMap.mem_range, LinearMap.mem_ker]
          constructor
          · rintro ⟨y, rfl⟩
            funext i
            simp [ι, π, LinearMap.funLeft_apply]
          · intro h
            refine ⟨x 0, funext fun i => Fin.cases ?_ (fun i => ?_) i⟩
            · simp [ι]
            · simpa [ι, π, LinearMap.funLeft_apply] using (congrFun h i).symm) hd
      obtain ⟨e1, e2⟩ := ih ρ' M' (fun i => κ i.succ) (fun g x => rfl)
        (fun g i j h => hM g _ _ (Fin.succ_lt_succ_iff.2 h)) (fun g i => hκ g _) d2
      refine ⟨fun i => Fin.cases d0 e1 i, fun τ a => ?_⟩
      rw [(hm τ a).2.1, Fin.sum_univ_succ, e2]
  obtain ⟨g, hg⟩ := hfl
  obtain ⟨L, r', hL, hd, τ', -, hc⟩ := (GlobalTheory.ConjLocal.local_conj l (Loc.PP l) F Ω O _ Bw n _
    ((MulAut.conj g).toMonoidHom.comp (r.comp (Dec (F := F) A).subtype)) g (fun _ => rfl)).2.2.2 τ J hJ
  have he : ∀ s i j, ((r' s i j : ↥L.1) : Om l) = (g * r s * g⁻¹ : GL (Fin n) (Om l)) i j := fun s i j =>
    congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin n) (Om l) => (f s).val i j) hL.2
  have hκ : ∀ s i, ((r' s i i : ↥L.1) : Om l) = κ i s := fun s i => (he s i i).trans ((hg s).2 i)
  let κ' : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ := fun i => MonoidHom.toHomUnits
    { toFun := fun s => r' (Bw.e.symm s) i i
      map_one' := by simp
      map_mul' := fun s t => Subtype.ext (by
        rw [IntermediateField.coe_mul, hκ, hκ, hκ, map_mul, map_mul, Units.val_mul]) }
  have hκ' : ∀ i s, ((κ' i s : ↥L.1) : Om l) = κ i (Bw.e.symm s) := fun i s => hκ _ _
  obtain ⟨d, hm⟩ := flag_mult Bw.Kw L n (Bw.repE L r') (fun s => (r' (Bw.e.symm s)).val) κ' (fun _ _ => rfl)
    (fun s i j h => Subtype.ext ((he _ i j).trans ((hg _).1 i j h))) (fun _ _ => rfl)
    (by rw [IsDR, Module.finrank_fin_fun]; exact hd)
  let U : Subgroup ↥(GK Bw.Kw) := H.comap ((Dec (F := F) A).subtype.comp Bw.e.symm.toMonoidHom)
  have hU : IsOpen (U : Set ↥(GK Bw.Kw)) := hH.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  have hcm : ∀ (s : ↥(GK Bw.Kw)) x, (s : GQ l) (Bw.j x) = Bw.j ((Bw.e.symm s : G F Ω) x) := fun s x => by
    rw [← Bw.e_comm, MulEquiv.apply_symm_apply]
  have key : ∀ i a, multV ((Loc.PP l).PD Bw.Kw) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ' i)) τ' a = if a = -m i then 1 else 0 := fun i a => by
    refine char_mult Bw.Kw L (κ' i) (continuous_induced_rng.2 ?_) (m i) ⟨U, hU, fun s hs hq => ?_⟩ (d i) τ' a
    · have h1 : Continuous fun s : ↥(GK Bw.Kw) => g * r (Bw.e.symm s) * g⁻¹ :=
        (continuous_const.mul (hr.comp (continuous_subtype_val.comp Bw.e_symm_cont))).mul continuous_const
      exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (he _ i i).symm
    · have hine : (Bw.e.symm s : G F Ω) ∈ Ine (F := F) A := by
        refine ⟨(Bw.e.symm s).2, fun x hx => ?_⟩
        rw [hj.valuation_lt_one_iff, map_sub, ← hcm]
        exact ((Loc.iqBasic l).2.2.1 _).1 hq _ ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
      have h2 := (GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (Loc.PP l) Bw.j _ _ (hcm s)).symm.trans ((Loc.cycFacts l l).2.2 s)
      refine Units.ext (Subtype.ext ?_)
      rw [hκ', hI i (Bw.e.symm s) ⟨hs, hine⟩, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
      refine Eq.trans ?_ (map_zpow₀ (algebraMap ↥L.1 (Om l)) _ _).symm
      congr 1
      exact congrArg (algebraMap ℚ_[l] (Om l)) h2
  ext a
  have h := hc a
  rw [LocBridge.multE, hm] at h
  simp only [key] at h
  rw [Multiset.count_map, ← Nat.cast_inj (R := ℤ), h]
  simp [Finset.card_def]
end

