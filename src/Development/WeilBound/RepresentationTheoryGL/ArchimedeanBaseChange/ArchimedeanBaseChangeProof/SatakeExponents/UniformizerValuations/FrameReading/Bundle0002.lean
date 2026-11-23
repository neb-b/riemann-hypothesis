module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GammaZetaNablaCancel
section
noncomputable section

open NumberField

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

open PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation

def GelfInj : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℂ), (∀ m, GlobalTheory.Dec.gelfVal x m = GlobalTheory.Dec.gelfVal y m) →
    Finset.univ.val.map x = Finset.univ.val.map y

def RegDom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → Formalism.BasicNotions.DomWeight n),
    RealSym (mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w)) ∧ ∀ τ, GapM (mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w) τ)

def Reg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → Formalism.BasicNotions.DomWeight n)
    (χ : InfinitePlace E → PositivityTheory.RgBcC.Inf n),
    (∀ v s m, GlobalTheory.Dec.gelfVal (χ v s) m = GlobalTheory.Dec.gelfVal (PositivityTheory.RgBcC.infOf (l v).w s) m) →
      RealSym (mOf χ) ∧ ∀ τ, GapM (mOf χ τ)

end PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b N : ℕ}

abbrev prodAt (P : Pre E n) (w : Pl E) := lp P w

abbrev pairAt (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) := GlobalTheory.SmGL.extTensor (prodAt Pa w) (prodAt Pb w)

structure Ctx (μ : HChar E) (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n) : Prop where
  g₁ : s₁.Good
  g₂ : s₂.Good
  u₁ : s₁.Untw
  u₂ : s₂.Untw
  t₁ : TreeParts s₁ Pa
  t₂ : TreeParts s₂ Pb
  join : IsJoin (μ ^ b) (μ ^ a) Pa Pb D

def JoinType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μ : HChar E)
  (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))), KTypes E Ω →
  ∃ W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ), (∀ N, FiniteDimensional ℂ (W N)) ∧
    ∀ (a b : ℕ), a + b = n → ∀ (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
      s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ Ω M, HasType K' W' V) →
      s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ Ω M, HasType K' W' V) → ∀ i, HasKType (W (D.N i)) (D.V i)

def ReadLev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (μ : HChar E)
  (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  ∀ (w : Pl E) (K : Subgroup (GLw n w)) (L : Subgroup (GLw a w × GLw b w)) (G : H E a b → ℂ),
  IsOpen (K : Set (GLw n w)) → IsCompact (K : Set (GLw n w)) → IsOpen (L : Set (GLw a w × GLw b w)) →
  (∀ m X, blk h w m X ∈ K → m ∈ L ∧ μ.loc w (GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1) →
  G ∈ pairSpace s₁.space s₂.space → G ≠ 0 → G ∈ fixed (pairRt a b w) L → GlobalTheory.LGrp.IsSpherical (prodAt D w) K

def actP (w : Pl E) (u : GLw a w × GLw b w → ℂ) (G : H E a b → ℂ) : H E a b → ℂ :=
  fun z => hint (K2 a b w) fun m => u m * pairRt a b w m G z

def phiMu (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : GLw n w → ℂ) (x y : GLw n w)
    (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * phi3 h w f x y m

def matS (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : GLw n w → ℂ) (X : Finset (GLw n w))
    (G : X → H E a b → ℂ) : X → H E a b → ℂ := fun x => ∑ y : X, actP w (phiMu h w μ f x y) (G y)

def ReadS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (μ : HChar E)
  (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  ∀ (w : Pl E) (K' : Subgroup (GLw n w)) (X : Finset (GLw n w)) (L : Subgroup (GLw a w × GLw b w)) (e : GLw n w → ℂ)
    (P : SmIrr (GLw n w)) (m : ℕ) (G : X → H E a b → ℂ), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) →
    (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) →
    (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → IsOpen (L : Set (GLw a w × GLw b w)) → IsHk K' e →
    (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0) →
    Module.finrank ℂ (fixed (prodAt D w) K') < m →
    (∀ x, G x ∈ pairSpace s₁.space s₂.space ∧ G x ∈ fixed (pairRt a b w) L) → (matS h w (μ.loc w) e X)^[m] G ≠ 0 →
    GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w)

def hkG {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) (v : V) : V :=
  ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v

def dl (w : Pl E) (x : Fin N → ℤ) : ℂ := qh w ^ (∑ i : Fin N, ((N : ℤ) - 1 - 2 * (i : ℕ)) * x i)

def Gap (x : Fin N → ℤ) : Prop := ∀ i j, i < j → x j + 1 ≤ x i

abbrev I2 (a b : ℕ) (w : Pl E) : Subgroup (GLw a w × GLw b w) := (iwGL a w).prod (iwGL b w)

def dc2 (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) (m : GLw a w × GLw b w) : ℂ :=
  dcos a w (tdiag ϖ x) m.1 * dcos b w (tdiag ϖ y) m.2

def ev2 (w : Pl E) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) : ℂ :=
  dl w x * pw ξa x * (dl w y * pw ξb y)

def JEig (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) : Prop :=
  ∃ v ∈ fixed (pairAt Pa Pb w) (I2 a b w), v ≠ 0 ∧
    ∀ x y, Gap x → Gap y → hkG (pairAt Pa Pb w) (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v

def ReadT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (μ : HChar E)
  (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  ∀ (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (J : Type) [Fintype J] (c : J → ℂ) (x : J → Fin a → ℤ) (y : J → Fin b → ℤ) (m : ℕ)
    (G : H E a b → ℂ), ordL (ϖ : w.adicCompletion E) = 1 → (∀ j, Gap (x j) ∧ Gap (y j)) →
    Module.finrank ℂ (fixed (pairAt Pa Pb w) (I2 a b w)) ≤ m →
    G ∈ pairSpace s₁.space s₂.space → G ∈ fixed (pairRt a b w) (I2 a b w) →
    (actP w fun g => ∑ j, c j * dc2 w ϖ (x j) (y j) g)^[m] G ≠ 0 →
    ∃ ξa ξb, JEig Pa Pb w ϖ ξa ξb ∧ ∑ j, c j * ev2 w ξa ξb (x j) (y j) ≠ 0

def JEigFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
  (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 →
  ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa' : Pre E a) (Pb' : Pre E b), PreEquiv Pa Pa' → PreEquiv Pb Pb' →
    Module.finrank ℂ (fixed (pairAt Pa' Pb' w) (I2 a b w)) ≤ m ∧ ∀ ξa ξb, JEig Pa' Pb' w ϖ ξa ξb → (ξa, ξb) ∈ Z

def ExpRead : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
  (ϖ : (w.adicCompletion E)ˣ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ordL (ϖ : w.adicCompletion E) = 1 →
  N3.Mono ξa → N3.Mono ξb → JEig Pa Pb w ϖ ξa ξb →
    Pa.Sat w (Finset.univ.val.map ξa) ∧ Pb.Sat w (Finset.univ.val.map ξb)

def RReadLev : Prop := RS.ReadMod → JoinMod → ReadLev
def RReadS : Prop := RS.ReadMod → JoinMod → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) → ReadS
def RReadT : Prop := RS.ReadMod → ReadT
def RExpRead : Prop := N3.N3 → ExpRead

theorem tout_of {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {K : ∀ w : Pl E, Subgroup (GLw n w)}
    {W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)} {D : Pre E n}
    (wt : ∀ τ lam, HasWeightAt π τ lam → ∑ i, D.m i τ = infOfWeight lam)
    (good : ∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w)
    (atS : ∀ w ∈ S, IsSplitAt w → ∃ P : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w) ∧
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ)
    (atT : ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w)
    (lev : ∀ w, GlobalTheory.LGrp.IsSpherical (prodAt D w) (K w)) (kt : ∀ i, HasKType (W (D.N i)) (D.V i)) : TOut π S T K W D :=
  ⟨⟨wt, Set.Finite.subset (eventually_cofinite.1 good) fun _ hw hx => hw.2 (hx hw.1)⟩, atS, atT, lev, kt⟩

end PositivityTheory.Rg.BcB.F.Tail

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimPhi
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev chComm {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb)
    (hg : ∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op))
    (hX : ∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) (hXs : IsSelfAdjoint X) : CommRing (ChAlg g X) := by
  haveI : IsMulCommutative (ChAlg g X) := StarAlgebra.isMulCommutative_adjoin ℂ
    (s := gOps g ∪ {X})
    (by
      rintro u (⟨x, rfl⟩ | rfl)
      · exact ⟨((hg x x).2).symm⟩
      · exact ⟨by
          rw [hXs.star_eq]
          rfl⟩)
    (by
      rintro u (⟨x, rfl⟩ | rfl) v (⟨y, rfl⟩ | rfl) _
      · exact (hg x y).1
      · exact ((hX x).1).symm
      · exact (hX y).1
      · rfl)
    (by
      rintro u (⟨x, rfl⟩ | rfl) v (⟨y, rfl⟩ | rfl) _
      · exact (hg x y).2
      · rw [hXs.star_eq]
        exact ((hX x).1).symm
      · exact (hX y).2
      · contradiction)
  exact { (inferInstance : Ring (ChAlg g X)) with mul_comm := mul_comm' }

def genO {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) : Option Γ → (B.Hb →L[ℂ] B.Hb) :=
  fun o => o.elim X fun x => (g x).op

theorem range_genO {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) :
    Set.range (genO g X) = gOps g ∪ {X} := by
  ext z
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inr rfl
    | some x => exact Or.inl ⟨x, rfl⟩
  · rintro (⟨x, rfl⟩ | rfl)
    · exact ⟨some x, rfl⟩
    · exact ⟨none, rfl⟩

def letter {B : Block E} {Γ : Type} (g : Γ → BGen B) (tX : PT B) : Option Γ × Bool → BGen B
  | (none, false) => Sum.inr tX
  | (none, true) => Sum.inr tX.adj
  | (some x, false) => g x
  | (some x, true) => (g x).adj

theorem letter_ok (hO : BlockOperatorsProductAdjoint) (hW : BlockWordOperators) {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (tX t₀ : PT B) (hg : ∀ x, (g x).Ok) (htX : tX.Ok) (hX : X = tX.op) (h₀ : t₀.Ok)
    (p : Option Γ × Bool) :
    (letter g tX p).Ok ∧ (letter g tX p).op = if p.2 then star (genO g X p.1) else genO g X p.1 := by
  have hadj := (hW E B [] t₀ 0 (by simp) h₀ le_rfl (by simp)).2.2.2.2.1
  obtain ⟨o, s⟩ := p
  cases o with
  | none =>
    cases s with
    | false => exact ⟨htX, hX.symm⟩
    | true =>
      have := hO E B tX tX htX htX
      refine ⟨this.2.2.2.2.1, ?_⟩
      show tX.adj.op = star X
      rw [this.2.2.2.2.2.1, hX, ContinuousLinearMap.star_eq_adjoint]
  | some x =>
    cases s with
    | false => exact ⟨hg x, rfl⟩
    | true =>
      refine ⟨(hadj (g x) (hg x)).1, ?_⟩
      show (g x).adj.op = star (g x).op
      rw [(hadj (g x) (hg x)).2, ContinuousLinearMap.star_eq_adjoint]

theorem phiEx (hO : BlockOperatorsProductAdjoint) (hW : BlockWordOperators) (hS : BlockLinearCombinations) (hA : AdjWords) {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (tX t₀ : PT B) (hg : ∀ x, (g x).Ok) (htX : tX.Ok) (hX : X = tX.op) (h₀ : t₀.Ok)
    (y : ChAlg g X) : ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ ((y : B.Hb →L[ℂ] B.Hb) * t₀.op) := by
  have hy : (y : B.Hb →L[ℂ] B.Hb) ∈ StarAlgebra.adjoin ℂ (Set.range (genO g X)) := by
    rw [range_genO]; exact y.2
  obtain ⟨J, hJ, c, w, L, -, hyw, -⟩ := hA (B.Hb →L[ℂ] B.Hb) (Option Γ) (genO g X) _ hy
  have hl := letter_ok hO hW g X tX t₀ hg htX hX h₀

  let bw : J → List (BGen B) := fun j => (w j).map (letter g tX)
  have bok : ∀ j, ∀ b ∈ bw j, b.Ok := fun j b hb => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hb
    exact (hl p).1
  have bop : ∀ j, ((bw j).map BGen.op).prod = wdVal (genO g X) (w j) := fun j => by
    simp only [bw, wdVal, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    exact (hl p).2
  let R : J → ℝ := fun j => ((bw j).map fun b => Sum.elim (fun _ => (0 : ℝ)) (fun s => |s.T| + |s.r + B.c|) b).sum
  have hR0 : ∀ j, 0 ≤ R j := fun j => by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
    rcases b with _ | s
    · exact le_rfl
    · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hRs : ∀ j, ∀ s, Sum.inr s ∈ bw j → s.T ≤ R j ∧ s.r + B.c ≤ R j := fun j s hs => by
    have hle : |s.T| + |s.r + B.c| ≤ R j := by
      have := List.single_le_sum (l := (bw j).map fun b => Sum.elim (fun _ => (0 : ℝ)) (fun s => |s.T| + |s.r + B.c|) b)
        (fun z hz => by
          obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
          rcases b with _ | s
          · exact le_rfl
          · exact add_nonneg (abs_nonneg _) (abs_nonneg _))
        _ (List.mem_map.2 ⟨Sum.inr s, hs, rfl⟩)
      exact this
    exact ⟨(le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans hle),
      (le_abs_self _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans hle)⟩
  have hwd := fun j => hW E B (bw j) t₀ (R j) (bok j) h₀ (hR0 j) (hRs j)
  have hsum := hS E B.a B.b B.D B.I J Finset.univ (fun j => c j * BGen.sc (bw j)) (fun j => (BGen.wd (bw j) t₀).Φ)
    (fun j => (BGen.wd (bw j) t₀).op) (fun j _ => by
      have := hO E B _ _ (hwd j).1 (hwd j).1
      exact ⟨this.1, this.2.1⟩)
  refine ⟨_, hsum.1, ?_⟩
  convert hsum.2 using 1
  rw [hyw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, ← bop, (hwd j).2.1, smul_smul]

end PositivityTheory.Rg.BcB.F.Rd

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbDefs
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

def genE {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (y : Γ) : ChAlg g X :=
  ⟨(g y).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨y, rfl⟩)⟩

def XE {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) : ChAlg g X :=
  ⟨X, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩

def ConvMulSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type)
  [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)), IsTestM Φ₁ → IsTestM Φ₂ → ∀ f : ι → H E a b → ℂ,
  (∀ i, Continuous (f i)) →
  PositivityTheory.Rg.BcB.E.conv D.μ (mulM D.μ Φ₁ Φ₂) f = PositivityTheory.Rg.BcB.E.conv D.μ Φ₁ (PositivityTheory.Rg.BcB.E.conv D.μ Φ₂ f)

def FinSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E)
  (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E))),
  IsOpen (K₁ : Set (GL (Fin B.a) (Af E))) → IsCompact (K₁ : Set (GL (Fin B.a) (Af E))) →
  IsOpen (K₂ : Set (GL (Fin B.b) (Af E))) → IsCompact (K₂ : Set (GL (Fin B.b) (Af E))) →
  ∀ (cK : ℂ) (ψ₀ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)),
  cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1 →
  (∀ x y h, ψ₀ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0) →
  (∀ (A : Type) (f : A × B.κ → H E B.a B.b → ℂ), (∀ i, ∀ u ∈ K₁.prod K₂, ∀ x, f i (x * finH u) = f i x) →
    convF B.ν ψ₀ f = f ∧ ∀ ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ → convF B.ν (mulF B.ν ψ ψ₀) f = convF B.ν ψ f) ∧
  ∀ ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ →
    ∀ x y, ∀ u ∈ K₁.prod K₂, ∀ h, mulF B.ν ψ ψ₀ x y (h * u) = mulF B.ν ψ ψ₀ x y h

def RealiseSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (Γ : Type) [Countable Γ]
  (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ),
  (∀ x, (g x).Ok) → tX.Ok → X = tX.op → g a₀ = Sum.inr t₀ →
  (∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op)) →
  (∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) → IsSelfAdjoint X →
  (∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) → χ (genE g X a₀) ≠ 0 →
  ∃ (M : ℕ) (s : ℕ → ChAlg g X → ℂ) (f : ℕ → B.I → H E B.a B.b → ℂ),
    (∀ y, Tendsto (fun k => s k (genE g X y)) atTop (𝓝 (χ (genE g X y)))) ∧
    Tendsto (fun k => s k (XE g X)) atTop (𝓝 (χ (XE g X))) ∧
    ∀ k, s k (genE g X a₀) ≠ 0 ∧ (∀ i, Continuous (f k i)) ∧ f k ≠ 0 ∧ LeftInv (f k) ∧ WL2 B.D M (f k) ∧
      PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ (f k) = s k (genE g X a₀) • f k ∧
      (∀ y (t : PT B), g y = Sum.inr t → PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ t.Φ t₀.Φ) (f k) =
        (s k (genE g X y) * s k (genE g X a₀)) • f k) ∧
      PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ tX.Φ t₀.Φ) (f k) = (s k (XE g X) * s k (genE g X a₀)) • f k

end PositivityTheory.Rg.BcB.F.Rd.B

end
end

