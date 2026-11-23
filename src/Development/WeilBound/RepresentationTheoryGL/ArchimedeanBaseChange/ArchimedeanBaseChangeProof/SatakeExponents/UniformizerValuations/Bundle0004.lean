module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsolateRepresentationAtCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0278
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataFinite
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.One

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def RunOut (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (HeightOneSpectrum (𝓞 E))) (D : Pre E n) : Prop :=
  Base π D ∧ (∀ w ∈ S, IsSplitAt w → D.SplitAt π w) ∧ ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w

def RunOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S T : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ D : Pre E n, RunOut π S T D

def Pre.Agree (D D' : Pre E n) : Prop :=
  (∃ e : Fin D.c ≃ Fin D'.c, ∀ i w, D.cls i w = D'.cls (e i) w) ∧ ∀ τ, ∑ i, D.m i τ = ∑ i, D'.m i τ

def DataFinite : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ (k : ℕ) (L : Fin k → Pre E n), ∀ (T : Finset (HeightOneSpectrum (𝓞 E))) (D : Pre E n), RunOut π S T D →
      ∃ j, D.Agree (L j)

def RunAgree : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (HeightOneSpectrum (𝓞 E))) (D D' : Pre E n), D.Agree D' → RunOut π S T D → RunOut π S T D'

theorem runFin_of (h1 : RunOne) (h2 : DataFinite) (h3 : RunAgree) : RunFin := by
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨k, L, hL⟩ := h2 E hE n hn π hπ S hS
  classical

  let good : Fin k → Prop := fun j => ∃ T D, RunOut π S T D ∧ D.Agree (L j)
  have hg : ∀ j, good j → RunOut π S ∅ (L j) := fun j ⟨T, D, hD, hA⟩ =>
    let h := h3 E n π S T D (L j) hA hD
    ⟨h.1, h.2.1, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  let idx := {j : Fin k // good j}
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin idx
  refine ⟨m, fun i => L (e.symm i).1, fun i => ⟨(hg _ (e.symm i).2).1, (hg _ (e.symm i).2).2.1⟩, fun T => ?_⟩
  obtain ⟨D, hD⟩ := h1 E hE n hn π hπ S T hS
  obtain ⟨j, hj⟩ := hL T D hD
  refine ⟨e ⟨j, T, D, hD, hj⟩, ?_⟩
  show ∀ w ∈ T, IsUnramU π w → ¬IsSplitAt w → InertAt π (L (e.symm (e ⟨j, T, D, hD, hj⟩)).1) w
  rw [Equiv.symm_apply_apply]
  exact (h3 E n π S T D (L j) hj hD).2.2

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocFinal
section
namespace PositivityTheory.Rg.BcN.F2.Final

open PositivityTheory.Rg.BcN.F2

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]

theorem hkAlg : HkAlg F ι := _root_.GlobalTheory.CompanionTheory.HeckeAlg.hk_alg F ι
theorem prodFinLen : ProdFinLen F ι := _root_.GlobalTheory.CompanionTheory.ProdLen.prodFinLen F ι
theorem subOfNonNil' : SubOfNonNil' F ι :=
  GlobalTheory.T.subquotient_of_non_nilpotent_variant F ι

end PositivityTheory.Rg.BcN.F2.Final
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PLemD
section
theorem PositivityTheory.Rg.BcB.F.LemDd.lemD : PositivityTheory.Rg.BcB.F.LemDd.LemD :=
  PositivityTheory.Rg.BcB.F.LemDd.lemD_of PositivityTheory.Rg.BcB.F.LemDd.InfUniq_holds PositivityTheory.Rg.BcB.F.LemDd.Tw.InfParts_holds
    PositivityTheory.Rg.BcB.SpectralAccumulation.InfTreeP.infTree_holds
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def parts (P : Pre E n) : List (Σ M : ℕ, Submodule ℂ (Sm E M)) := List.ofFn fun i => ⟨P.N i, P.V i⟩

def twPart (χ : HChar E) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) : Σ M : ℕ, Submodule ℂ (Sm E M) :=
  ⟨x.1, x.2.map (mulChi x.1 χ).toLinearMap⟩

def IsJoin (χ₁ χ₂ : HChar E) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n) : Prop :=
  parts D = (parts Pa).map (twPart χ₁) ++ (parts Pb).map (twPart χ₂)

def embW (a : ℕ) (w : Pl E) : GLw a w →* GA E a := (finGL E a).comp (locGL E a w)

def embT (a : ℕ) (w : Pl E) : GLw a w →* GA E a := (thetaGL a (conjAd E)).comp (embW a w)

def pairRt (a b : ℕ) (w : Pl E) : Representation ℂ (GLw a w × GLw b w) (H E a b → ℂ) :=
  (rightReg ℂ (H E a b) ℂ).comp ((embW a w).prodMap (embW b w))

def pairRtT (a b : ℕ) (w : Pl E) : Representation ℂ (GLw a w × GLw b w) (H E a b → ℂ) :=
  (rightReg ℂ (H E a b) ℂ).comp ((embT a w).prodMap (embT b w))

def IsSat2 {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E) (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : V)
    (Ba Bb : Multiset ℂˣ) : Prop :=
  x ∈ fixed ρ (K2 a b w) ∧ Ba.card = a ∧ Bb.card = b ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ i ≤ a, ∀ j ≤ b,
    heckeVec ρ (K2 a b w) (fun g => Tj ℂ a (Ov E w) ϖ i g.1 * Tj ℂ b (Ov E w) ϖ j g.2) x =
      (satEig (qV E w) a Ba i * satEig (qV E w) b Bb j) • x

def ctT (h : a + b = n) (w : Pl E) (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E) (k : ℕ) :
    GLw a w × GLw b w → ℂ :=
  ctMu h w ν fun u : UL n w => Tj ℂ n (Ov E w) ϖ k u.1

def JoinEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (μ : HChar E) (e : InfinitePlace E → ℤ)
  (Pa : Pre E a) (Pb : Pre E b), IsMu μ e → a + b = n → ∃ D : Pre E n, IsJoin (μ ^ b) (μ ^ a) Pa Pb D

def JoinInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (χ₁ χ₂ : HChar E)
  (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), IsJoin χ₁ χ₂ Pa Pb D → ∀ τ,
  ∑ i, D.m i τ = (∑ i, Pa.m i τ).map (· + expo χ₁ τ) + (∑ i, Pb.m i τ).map (· + expo χ₂ τ)

def JoinSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (χ₁ χ₂ : HChar E)
  (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n) (w : Pl E) (Ba Bb : Multiset ℂˣ), IsJoin χ₁ χ₂ Pa Pb D →
  χ₁.UnrAt w → χ₂.UnrAt w → Pa.Sat w Ba → Pb.Sat w Bb →
  D.Sat w (Ba.map (· * χ₁.val w) + Bb.map (· * χ₂.val w))

def TreeInf : Prop := InfTree → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : Pre E N)
  (τ : E →+* ℂ) (m : Multiset ℂ), t.Good → t.Untw → TreeParts t P → t.space ≠ ⊥ → HasInfCharGL t.space τ m →
  ∑ i, P.m i τ = m

def WeightJoin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n a b : ℕ) (μ : HChar E)
  (e : InfinitePlace E → ℤ) (π : Submodule ℂ (UA E n → ℂ)) (lam : InfinitePlace E → DomWeight n)
  (n₁ n₂ : (E →+* ℂ) → Multiset ℂ), 1 ≤ n → IsMu μ e → IsAutRepU π → (∀ v, HasWeightAt π v.embedding (lam v)) →
  RealSym n₁ → RealSym n₂ →
  (∀ v, (n₁ v.embedding).map (· + (b : ℂ) * (e v : ℂ) / 2) + (n₂ v.embedding).map (· + (a : ℂ) * (e v : ℂ) / 2) =
    infOfWeight (lam v)) →
  ∀ τ lam', HasWeightAt π τ lam' →
    (n₁ τ).map (· + expo (μ ^ b) τ) + (n₂ τ).map (· + expo (μ ^ a) τ) = infOfWeight lam'

def TreeSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : Pre E N) (w : Pl E),
  t.Good → t.Untw → TreeParts t P →
  (∃ φ ∈ t.space, φ ≠ 0 ∧ ∀ k ∈ KGL w (n := N), finRep E N (locGL E N w k) φ = φ) →
  ∃ B, P.Sat w B ∧ ∀ φ ∈ t.space, φ ≠ 0 → (∀ k ∈ KGL w (n := N), finRep E N (locGL E N w k) φ = φ) →
    IsSatVecGL w ((finRep E N).comp (locGL E N w)) φ B

def PairSat : Prop := TreeSat → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (s₁ : Tr E a) (s₂ : Tr E b)
  (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (G : H E a b → ℂ), s₁.Good → s₂.Good → s₁.Untw → s₂.Untw → TreeParts s₁ Pa →
  TreeParts s₂ Pb → G ∈ pairSpace s₁.space s₂.space → G ≠ 0 → G ∈ fixed (pairRt a b w) (K2 a b w) →
  ∃ Ba Bb, Pa.Sat w Ba ∧ Pb.Sat w Bb ∧ IsSat2 w (pairRt a b w) G Ba Bb

def ThetaSat2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w u : Pl E) (G : H E a b → ℂ)
  (Ba Bb : Multiset ℂˣ), IsSplitAt w → ConjPl w u → IsSat2 u (pairRt a b u) G Ba Bb →
  IsSat2 w (pairRtT a b w) G (Ba.map (·⁻¹)) (Bb.map (·⁻¹))

def CtSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
  (ν : (w.adicCompletion E)ˣ →* ℂˣ) (c : ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : V) (Ba Bb : Multiset ℂˣ), IsSplitAt w →
  ν = GlobalTheory.SmGL.unrChar (w.adicCompletion E) c → IsSat2 w ρ x Ba Bb → ∀ ϖ, IsUnifV E w ϖ → ∀ k ≤ n,
    heckeVec ρ (K2 a b w) (ctT h w ν ϖ k) x =
      satEig (qV E w) n (Ba.map (· * c ^ b) + Bb.map (· * c ^ a)) k • x

def MuLoc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (μ : HChar E)
  (e : InfinitePlace E → ℤ) (w : Pl E), IsMu μ e → μ.UnrAt w →
  μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (μ.val w) ∧ (∀ k : ℕ, (μ ^ k).UnrAt w ∧ (μ ^ k).val w = μ.val w ^ k) ∧
    ∀ u, IsSplitAt w → ConjPl w u → μ.UnrAt u ∧ μ.val u = (μ.val w)⁻¹

def SatAtU (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E) (B : Multiset ℂˣ) : Prop :=
  ∃ σ : SmIrr (GLw n w), IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ HasSatGL w σ.ρ B

def SatSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (D : Pre E n) (w : Pl E) (B : Multiset ℂˣ), SatAtU π w B → D.Sat w B → D.SplitAt π w

def SatConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (w u : Pl E) (B : Multiset ℂˣ), IsAutRepU π → IsSplitAt w → ConjPl w u → SatAtU π w B → SatAtU π u (B.map (·⁻¹))

def ReadSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n a b : ℕ) (h : a + b = n)
  (μ : HChar E) (e : InfinitePlace E → ℤ) (π : Submodule ℂ (UA E n → ℂ)) (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a)
  (Pb : Pre E b) (D : Pre E n) (G : H E a b → ℂ) (w : Pl E) (B : Multiset ℂˣ) (ϖ : w.adicCompletion E),
  IsMu μ e → IsAutRepU π → s₁.Good → s₂.Good → s₁.Untw → s₂.Untw → TreeParts s₁ Pa → TreeParts s₂ Pb →
  IsJoin (μ ^ b) (μ ^ a) Pa Pb D → G ∈ pairSpace s₁.space s₂.space → G ≠ 0 → IsSplitAt w → μ.UnrAt w → SatAtU π w B →
  IsUnifV E w ϖ →
  (G ∈ fixed (pairRt a b w) (K2 a b w) →
    (∀ k ≤ n, heckeVec (pairRt a b w) (K2 a b w) (ctT h w (μ.loc w) ϖ k) G = satEig (qV E w) n B k • G) →
    D.Sat w B ∧ D.SplitAt π w) ∧
  ∀ u, ConjPl w u → G ∈ fixed (pairRt a b u) (K2 a b u) →
    (∀ k ≤ n, heckeVec (pairRtT a b w) (K2 a b w) (ctT h w (μ.loc w) ϖ k) G = satEig (qV E w) n B k • G) →
    D.Sat u (B.map (·⁻¹)) ∧ D.SplitAt π u

theorem readSplit_of (h1 : TreeSat) (h2 : PairSat) (h3 : ThetaSat2) (h4 : CtSat) (h5 : MuLoc) (h6 : JoinSat)
    (h7 : SatSplit) (h8 : SatConj) : ReadSplit := by
  intro E _ _ _ hE n a b h μ e π s₁ s₂ Pa Pb D G w B ϖ hμ hπ g₁ g₂ u₁ u₂ t₁ t₂ hJ hG h0 hw hun hB hϖ
  obtain ⟨m1, m2, m3⟩ := h5 E hE μ e w hμ hun
  have hq : qV E w ≠ 0 := qV_ne_zero w
  have hc : B.card = n := by
    obtain ⟨σ, -, hs⟩ := hB
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs.1
    exact (hs.2 x hx hx0).2.2.1
  have key : ∀ (ρ : Representation ℂ (GLw a w × GLw b w) (H E a b → ℂ)) (Ba Bb : Multiset ℂˣ), IsSat2 w ρ G Ba Bb →
      (∀ k ≤ n, heckeVec ρ (K2 a b w) (ctT h w (μ.loc w) ϖ k) G = satEig (qV E w) n B k • G) →
      Ba.map (· * μ.val w ^ b) + Bb.map (· * μ.val w ^ a) = B := fun ρ Ba Bb hs he =>
    eq_of_satEig_eq hq (by simp [hs.2.1, hs.2.2.1, h]) hc fun k hk =>
      smul_left_injective ℂ h0 ((h4 E n a b h w _ _ _ ρ G Ba Bb hw m1 hs ϖ hϖ k hk).symm.trans (he k hk))
  refine ⟨fun hf he => ?_, fun u hu hf he => ?_⟩
  · obtain ⟨Ba, Bb, sa, sb, hs⟩ := h2 h1 E a b s₁ s₂ Pa Pb w G g₁ g₂ u₁ u₂ t₁ t₂ hG h0 hf
    have hD := h6 E n a b _ _ Pa Pb D w Ba Bb hJ (m2 b).1 (m2 a).1 sa sb
    rw [(m2 b).2, (m2 a).2, key _ Ba Bb hs he] at hD
    exact ⟨hD, h7 E n π D w B hB hD⟩
  · obtain ⟨Ba, Bb, sa, sb, hs⟩ := h2 h1 E a b s₁ s₂ Pa Pb u G g₁ g₂ u₁ u₂ t₁ t₂ hG h0 hf
    obtain ⟨hu1, hu2⟩ := m3 u hw hu
    obtain ⟨-, n2, -⟩ := h5 E hE μ e u hμ hu1
    have hD := h6 E n a b _ _ Pa Pb D u Ba Bb hJ (n2 b).1 (n2 a).1 sa sb
    have e1 := key _ _ _ (h3 E a b w u G Ba Bb hw hu hs) he
    have e2 : Ba.map (· * (μ ^ b).val u) + Bb.map (· * (μ ^ a).val u) = B.map (·⁻¹) := by
      rw [(n2 b).2, (n2 a).2, hu2, ← e1]
      simp [Multiset.map_map, mul_comm]
    rw [e2] at hD
    exact ⟨hD, h7 E n π D u _ (h8 E n π w u B hπ hw hu hB) hD⟩

end PositivityTheory.Rg.BcB.F.RS

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SatIndepOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.LemB

def CjEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
  ∀ s : w.adicCompletion E →+* w.adicCompletion E,
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w

def BcWeyl : Prop := ∀ (n : ℕ) (α α' : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.WeylConjU α α' →
  GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α'

end PositivityTheory.Rg.BcB.F.LemB

end
end

