module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.GaloisCohomology.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AutomorphicSideWildInertia
section
noncomputable section

namespace Formalism.MainNotions.AutomorphicSideWildInertia

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

def ResidualIrreducibleGood (D : D7) : Prop := ResidualIrreducibleRankR D


end Formalism.MainNotions.AutomorphicSideWildInertia
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
section
noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingBounds

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachLatticeFreeLocal D.loc HW D.locA F

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2L D.loc HW D.locA F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p3L D.loc HW D.locA F Cm

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p4L D.loc HW D.locA F Cm

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p5L D.loc HW D.locA F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p6L D.loc HW D.locA F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p7L D.loc HW D.locA F

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p8L D.loc HW D.locA F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p9L D.loc HW D.locA F

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachCharacterisationLocal D.loc HW D.locA F

def adm11 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.gammaSemisimpleLocal D.loc HW D.locA F

def adm12 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2aL D.loc HW D.locA F

def adm13 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2bL D.loc HW D.locA F

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2cL D.loc HW D.locA F

def adm15 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2dL D.loc HW D.locA F

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachLengthLocal D.loc HW D.locA F

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem invariant_cocycle_le_gamma_cocycle (W : LocWach PD LL O v n) (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) :
    W.wachCocyclesDelta T ≤ W.divisibleCocycles T := by
  have e := W.gamK_eq_one h1 h2
  intro x hx
  unfold Formalism.BasicNotions.LocWach.wachCocyclesDelta Formalism.BasicNotions.herrZ1Δ at hx
  have hx1 := (Submodule.mem_inf.mp hx).1
  rw [e] at hx1
  exact hx1

def coreResK (W : LocWach PD LL O v n) : Prop :=
  ∀ (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) (w : ↥(W.wachCocyclesDelta T)),
    Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (W.clK T w) =
      W.cl T ⟨(w : W.DD T × W.DD T), invariant_cocycle_le_gamma_cocycle W h1 h2 T w.2⟩


variable (PD LL O) in
def coreJumps : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → IsCrys PD T₀.ρ → IsCrys PD T₁.ρ → IsCrys PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      IsJumpV PD T₁.ρ τ a ↔ IsJumpV PD T₀.ρ τ a ∨ IsJumpV PD T₂.ρ τ a

end Local

def adm17 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreExt ((HW l).W K s LL h)

def adm18 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreExtΔ ((HW l).W K s LL h)

def adm19 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreDss ((HW l).W K s LL h)

def adm20 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (_hKK : K'.1 ≤ K.1) (hle : GK K ≤ GK K')
    (LL : FinExt l),
    Formalism.MainNotions.LiftingTheory.coreCor ((D.loc l).PD K) ((D.loc l).PD K') ↥LL.1 ↥(OL LL) (Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _)
      (Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1)

def adm21 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ (s = 1 → l ≠ 2 → ((HW l).W K s LL h).ClKNat)

theorem resK_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) : coreResK ((HW l).W K s LL h) := by
  intro h1 h2 T w
  exact ((F l).E K s LL h).tie.clK_res (((HW l).W K s LL h).gamK_eq_one h1 h2) T w _ rfl

def adm22 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), FontaineLe ((D.loc l).PD K) ↥LL.1

def adm23 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), coreJumps ((D.loc l).PD K) ↥LL.1 ↥(OL LL)

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  adm1 D HW F ∧ adm2 D HW F ∧ adm3 D HW F Cm ∧ ArchimedeanSignatureMatching D HW F Cm ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F ∧ adm8 D HW F ∧
    adm9 D HW F ∧ adm10 D HW F ∧ adm11 D HW F ∧ adm12 D HW F ∧ adm13 D HW F ∧ adm14 D HW F ∧ adm15 D HW F ∧ adm16 D HW F ∧
    adm17 D HW F ∧ adm18 D HW F ∧ adm19 D HW F ∧ adm20 D HW F ∧ adm21 D HW F ∧ adm22 D HW F ∧ adm23 D HW F

def Conclusion1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F ∧ Formalism.MainNotions.LiftingTheory.WachKillsCaseB D HW F ∧ Formalism.MainNotions.LiftingTheory.WachKillsCaseA D HW F

def Conclusion2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK

def aux₃ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Conclusion1 D HW F ∧ Conclusion2 D HW F CA CB CK

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ) : Prop := admitted D HW F Cm → aux₃ D HW F CA CB CK

end Formalism.MainNotions.CrystallineLiftingBounds
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
section
noncomputable section

open Classical

namespace Formalism.MainNotions.TruncatedSeriesCountingBounds

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def JumpsAt {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (i : ZMod n) (Sset : Set ℤ) : Prop :=
  ∀ τ, Formalism.MainNotions.LiftingTheory.Over W τ i → JumpsInV PD T.ρ τ Sset

def lowCount {PD : PeriodData G Qp K₀ K B BdR} [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (i : ZMod n) (η : ℕ) : ℤ :=
  ∑ τ ∈ Finset.univ.filter (fun τ => Formalism.MainNotions.LiftingTheory.Over W τ i),
    ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD T.ρ τ a

def ColLeR (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (x : ℝ) : Prop :=
  ∃ mm k : ℕ, F.col PD = mm ∧ lenOl PD (O := O) = k ∧ (mm : ℝ) ≤ x * k

def Thick (b η : ℕ) (size : ZMod n → ℕ) (i : ZMod n) : Prop := b ≤ size i ∧ size i ≤ b + η

def HidaSetting (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (T₁ T₂ : LocLat G Qp LL O)
    (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool) (size Mi hi : ZMod n → ℕ) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W ∧ Formalism.MainNotions.LiftingTheory.Sur W F ∧
  (∀ i, η < size i) ∧
  (∀ i, JumpsAt W T₁ i (if up i then
      Set.Icc (size i : ℤ) ((size i : ℤ) + S) ∪ Set.Icc (-(η : ℤ)) η
    else Set.Icc (-(size i : ℤ) - S) (-(size i : ℤ)) ∪ Set.Icc (-(η : ℤ)) η)) ∧
  (∀ i, lowCount W T₂ i η ≤ m) ∧
  (∀ i, ¬ Thick b η size i → size i ≤ w) ∧
  Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi

def eLift {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n) (T₁ : LocLat G Qp LL O)
    (Mi hi : ZMod n → ℕ) : ℕ :=
  Formalism.MainNotions.LiftingTheory.ePA PD.p (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi)
    (Formalism.MainNotions.LiftingTheory.jumpSet W T₁ (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi))

def hB (b w S η : ℕ) (size : ZMod n → ℕ) : ℕ :=
  if ∃ i, Thick b η size i then b + η + S else w + S

def Band (l b S η : ℕ) (size : ZMod n → ℕ) (lg C : ℝ) : Prop :=
  ∃ i, ¬ Thick b η size i ∧ (Thick b η size (i + 1) ∨ Thick b η size (i - 1)) ∧
    |(l : ℝ) * size i - b| ≤ C * ((l : ℝ) * η + (l : ℝ) * S + (b : ℝ) / l + size i + (l : ℝ) * lg)

def ThmB (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (C : ℝ) : Prop :=
  11 ≤ PD.p →
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool)
    (size Mi hi : ZMod n → ℕ),
    HidaSetting PD W T₁ T₂ F b w S η m up size Mi hi →
    20 * w ≤ b → 20 * η ≤ b → 20 * S ≤ b →
    (∃ i, ¬ Thick b η size i) →
    let l : ℕ := PD.p
    let h : ℕ := hB b w S η size
    let lg : ℝ := Real.logb l (2 * (h : ℝ))
    let band : ℝ := if Band l b S η size lg C then 1 else 0
    let r : ℝ := finrank LL T₂.V
    let e' : ℝ := eLift W T₁ Mi hi
    ((∀ i, up (i + 1) ≠ up i ∧
        ¬ (Thick b η size i ∧ Thick b η size (i + 1) ∧ Thick b η size (i + 2))) →
      ColLeR PD F (C * ((n : ℝ) + 1) * r * ((h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + η) / l + S + 1 + lg +
        η * band) + C * n * m * e')) ∧
    (∀ R : ℕ, 1 ≤ R → (∀ i, up i = up 0) → (∀ i, ¬ ∀ t : ℕ, t < R → Thick b η size (i + t)) →
      ColLeR PD F (C * ((n : ℝ) + 1) * r * ((h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + η) / l +
        (R : ℝ) ^ 2 * (S + 1 + lg) + η * band) + C * n * m * (R : ℝ) ^ 2 * e'))

def Clusters (j : ℕ) (thick : ZMod n → Prop) : Prop :=
  ∀ t, thick t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (t - k)) ∨
    (∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ thick (t - d) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ thick (t - k))

end Core

def crisMap {Qp : Type} [Field Qp] (B : Type) [CommRing B] [Algebra Qp B] {LL : Type} [Field LL]
    [Algebra Qp LL] {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') :
    TensorProduct Qp V B →ₗ[LL] TensorProduct Qp V' B :=
  TensorProduct.AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)

section Lit

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {Bc BdR : Type} [CommRing Bc] [CommRing BdR] [Algebra Qp Bc] [Algebra K₀ Bc] [IsScalarTower Qp K₀ Bc]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

def DcrisExactStrict [TopologicalSpace G] (PD : PeriodData G Qp K₀ K Bc BdR) (LL : Type) [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] : Prop :=
  Function.Bijective (algebraMap K₀ K) →
  ∀ (V₀ V₁ V₂ : Type) [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [FiniteDimensional LL V₀] [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁]
    [IsScalarTower Qp LL V₁] [FiniteDimensional LL V₁] [AddCommGroup V₂] [Module LL V₂]
    [Module Qp V₂] [IsScalarTower Qp LL V₂] [FiniteDimensional LL V₂]
    (ρ₀ : Representation LL G V₀) (ρ₁ : Representation LL G V₁) (ρ₂ : Representation LL G V₂)
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂)
    [TopologicalSpace V₀] [IsModuleTopology LL V₀] [TopologicalSpace V₁] [IsModuleTopology LL V₁]
    [TopologicalSpace V₂] [IsModuleTopology LL V₂],
    (∀ x, Continuous fun g => ρ₀ g x) → (∀ x, Continuous fun g => ρ₁ g x) →
    (∀ x, Continuous fun g => ρ₂ g x) →
    (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) →
    Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π →
    IsCrys PD ρ₀ → IsCrys PD ρ₁ → IsCrys PD ρ₂ →
    (∀ y ∈ Dcris PD ρ₀, crisMap Bc ι y = 0 → y = 0) ∧
    (∀ x ∈ Dcris PD ρ₁, crisMap Bc π x = 0 → ∃ y ∈ Dcris PD ρ₀, crisMap Bc ι y = x) ∧
    (Dcris PD ρ₁).map (crisMap Bc π) = Dcris PD ρ₂ ∧
    (∀ a : ℤ, (FilCris PD ρ₁ a).map (crisMap Bc π) = FilCris PD ρ₂ a) ∧
    (∀ (a : ℤ), ∀ y ∈ Dcris PD ρ₀, crisMap Bc ι y ∈ FilCris PD ρ₁ a → y ∈ FilCris PD ρ₀ a)

def DdREqDcris [TopologicalSpace G] (PD : PeriodData G Qp K₀ K Bc BdR) (LL : Type) [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] : Prop :=
  Function.Bijective (algebraMap K₀ K) →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V) [TopologicalSpace V] [IsModuleTopology LL V],
    (∀ x, Continuous fun g => ρ g x) → IsCrys PD ρ →
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ ∧
    ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD ρ τ) ∧
      finrank LL ↥(DdRE PD ρ τ) = finrank LL V ∧
      ∀ a : ℤ, FildR PD ρ τ a =
        (FilCris PD ρ a ⊓ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map
          (ιV PD (LL := LL) (V := V))

end Lit

section Theory

def TheoremBLocal (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), K.1 ≤ MaximalUnramifiedExtension l →
    ∀ [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
      ThmB ((LT l).PD K) ((HW l).W K 1 LL hG) C

def BlochKatoDimensionLocal (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    BlochKatoDim ((LT l).PD K) ↥LL.1

def DcrisExactStrictLocal (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), DcrisExactStrict ((LT l).PD K) ↥LL.1

def DdREqDcrisAll (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), DdREqDcris ((LT l).PD K) ↥LL.1

end Theory

def Conclusion1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := TheoremBLocal D.loc D.locA HW F C

def adm8 (D : D7) : Prop := BlochKatoDimensionLocal D.loc

def adm9 (D : D7) : Prop := DcrisExactStrictLocal D.loc

def adm15 (D : D7) : Prop := DdREqDcrisAll D.loc

end Formalism.MainNotions.TruncatedSeriesCountingBounds
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
section
noncomputable section

namespace Formalism.MainNotions.IdempotentChoiceDepthZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Obj51

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))

def IsOrthogonalIdempotentDecomposition (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (S : IdempotentChoiceData N i) : Prop :=

  (InR N i r S.eB ∧ InR N i r S.e1 ∧ S.eB * S.eB = S.eB ∧ S.e1 * S.e1 = S.e1 ∧
    S.eB * S.e1 = 0 ∧ S.e1 * S.eB = 0 ∧
    (∀ x, ((S.eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((S.e1 x).map (toK N i)).rank = 1)) ∧

  (∀ g u, S.e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
      ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧
  (∀ a, InR' N r S a → ∀ u, S.e (((a S.π').map (toK N i)).mulVec u) =
      (((S.ψρ a).map (toK N i)).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i (S.ψχ c a) * (S.e u).2 c)) ∧
  (∀ A : Matrix (Fin R.r) (Fin R.r) (N.O i), ∃ a, InR' N r S a ∧ S.ψρ a = A) ∧

  (∃ w ∈ placesOver H.E (N.l i), S.g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) S.g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) =
    N.l i - 1 ∧

  (InR N i r S.X0 ∧ S.eB * S.X0 = S.X0 ∧ S.X0 * S.eB = S.X0 ∧
    ∀ u, S.e (((S.X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) S.g0 : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧

  ((∀ f ∈ N.T i, (fun x' => f (S.p x')) ∈ S.T') ∧ (∀ c ∈ Finset.Icc 1 R.t, S.rr c ∈ S.T') ∧
    S.T' = Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f (S.p x')) '' (N.T i : Set _) ∪
      (fun c => S.rr c) '' (Finset.Icc 1 R.t : Set ℕ)) ∧
    (∃ b : Fin R.t.factorial → S.X' → N.O i, (∀ k, b k ∈ S.T') ∧
      ∀ f ∈ S.T', ∃! cf : Fin R.t.factorial → N.T i,
        f = ∑ k, ((fun x' => (cf k : N.X i → N.O i) (S.p x')) : S.X' → N.O i) * b k) ∧
    (∀ x, Nat.card {x' // S.p x' = x} = R.t.factorial)) ∧

  (∀ x', ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) =
    Matrix.det ((Polynomial.X : Polynomial (N.O i)) • (S.eB (S.p x')).map (Polynomial.C (R := N.O i)) -
      (S.X0 (S.p x')).map (Polynomial.C (R := N.O i)) + 1 -
      (S.eB (S.p x')).map (Polynomial.C (R := N.O i)))) ∧

  (S.p S.π' = π ∧ ∀ c ∈ Finset.Icc 1 R.t,
    S.rr c S.π' = ((chiU N i c S.g0 : (N.O i)ˣ) : N.O i)) ∧

  ((∀ x', ((Eel N S x').map (toK N i)).rank = 1) ∧
    (∀ x', Eel N S x' * Eel N S x' = del51 N S x' • Eel N S x') ∧
    (∀ u, S.e (((Eel N S S.π').map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => if (c : ℕ) = 0 then toK N i (del51 N S S.π') * (S.e u).2 c else 0)) ∧
    IsUnit (del51 N S S.π')) ∧

  CharpolyCoeffsInSubalgebra N i S.T' (fun x' => rO N i r (S.p x'))

end Obj51

end Formalism.MainNotions.IdempotentChoiceDepthZero
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LatticeVariant
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.LatticeVariant

open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

abbrev LamO (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Type :=
  AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)

def ConjCl (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def DelOn (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Prop :=
  ∀ (P : PlE D.host) (hP : P ∈ Q) (A' : ValuationSubring N.Om), IsPlaceOver A' P →
    ∃ σ ∈ Ine (F := D.host.E) A', Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = 1

variable {Y}

variable (Y)

variable (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)






end Formalism.MainNotions.LatticeVariant

end
end

