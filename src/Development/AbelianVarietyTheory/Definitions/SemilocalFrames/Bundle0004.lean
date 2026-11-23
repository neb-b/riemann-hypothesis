module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmStarOfIsCMUnram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
section
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def ipow (𝔡 : Ideal (𝓞 K)) (n : ℤ) : Submodule (𝓞 K) K :=
  (((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

def line (A : Submodule (𝓞 K) K) (v : V) : Submodule (𝓞 K) V :=
  A.map ((LinearMap.toSpanSingleton K V v).restrictScalars (𝓞 K))

def GenBy (A B : Submodule (𝓞 K) V) (e : ℕ) : Prop :=
  ∃ t : Finset V, t.card ≤ e ∧ A = B ⊔ Submodule.span (𝓞 K) (t : Set V)

def cf (K : Type) [Field K] [NumberField K] : ℝ := 1 + Real.logb 2 (Module.finrank ℚ K)

def HasOrtho (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → GlobalTheory.Mass.PD k →
    (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ Formalism.HermitianLatticesTheory.IsUnimodular k L) →
    ∃ I : Submodule (𝓞 K) W, Formalism.HermitianLatticesTheory.IsOrthoLattice k I (Module.finrank K W)

structure NF (H : HermSpace K V) (r : ℕ) where
  F : FlagD H r
  F' : FlagD H r
  j : ℕ
  j_le : j ≤ r
  c : K
  c_norm : c * star c = 1
  T : ℕ
  hT : F.T = T
  hT' : F'.T = T
  same : ∀ a : Fin (r + 1), j ≤ a.val → F'.e a = c • F.e a
  w : Formalism.MainNotions.S.Loc.Pt K j
  sgn : Fin j → ℤˣ
  pair : ∀ a b : Fin j, H.B (F.e (Fin.castLE (j_le.trans (Nat.le_succ r)) a))
    (F'.e (Fin.castLE (j_le.trans (Nat.le_succ r)) b)) = w.mat a b * ((sgn b : ℤ) : K)
  ist : Fin r → V
  ist_e : ∀ a b : Fin r, j ≤ b.val → H.B (F.e a.castSucc) (ist b) = if a = b then 1 else 0
  ist_e' : ∀ a b : Fin r, a.val < j → j ≤ b.val → H.B (F'.e a.castSucc) (ist b) = 0
  normalForm_dual_orthogonal_last : ∀ b : Fin r, j ≤ b.val → H.B F.z (ist b) = 0
  ist_iso : ∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (ist a) (ist b) = 0
  posdef : ∀ σ : K →+* ℂ, F.PosDefAt σ
  𝔡 : Ideal (𝓞 K)
  𝔡_ne : 𝔡 ≠ ⊥
  𝔡_star : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)

namespace NF

variable {H : HermSpace K V} {r : ℕ} (N : NF H r)

def aa (a : Fin r) : Submodule (𝓞 K) K := ipow N.𝔡 (-((r : ℤ) - a.val))

def Ist : Submodule K V := Submodule.span K (N.ist '' {b | N.j ≤ b.val})

def Wt : Submodule K V := perp H (V0 N.F N.F' ⊔ N.Ist)

def Wn : Submodule K V := perp H (N.F.X ⊔ N.F'.X ⊔ N.Ist)

def Pi : Submodule K V := perp H N.Wt

def P0 : Submodule (𝓞 K) V :=
  (⨆ a : Fin r, line (N.aa a) (N.F.e a.castSucc)) ⊔
    (⨆ a : Fin r, ⨆ _ : a.val < N.j, line (N.aa a) (N.F'.e a.castSucc)) ⊔ line 1 N.F.z ⊔
    ⨆ a : Fin r, ⨆ _ : N.j ≤ a.val, line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)

def Ref (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V := N.P0 ⊔ (L ⊓ rs (𝓞 K) N.Wn)

def nD (l : ℕ) : ℝ :=
  if h : l ≤ r + 1 then |((Algebra.norm ℚ (Dl N.F N.F' l h) : ℚ) : ℝ)| *
    (Ideal.absNorm N.𝔡 : ℝ) ^ (-(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a))) else 0

def Del : ℝ := N.nD N.j

def Db : ℝ := ∏ l ∈ (Finset.Icc 1 N.j).filter (fun l => N.nD l ≠ 0), N.nD l

def NT : ℝ := (N.T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K

def R : Subgroup (V ≃ₗ[K] V) := Subgroup.closure {s | N.F.InN (s : V →ₗ[K] V) ∧ N.F'.InN (s : V →ₗ[K] V)}

def fixing (_ : NF H r) (S : Submodule K V) : Subgroup (V ≃ₗ[K] V) := fixingSubgroup (V ≃ₗ[K] V) (S : Set V)

def R1 : Subgroup (V ≃ₗ[K] V) := N.R ⊓ N.fixing (V0 N.F N.F')

def ZI : Subgroup (V ≃ₗ[K] V) := N.R1 ⊓ N.fixing N.Wt

def Rs : Subgroup (V ≃ₗ[K] V) := N.R ⊓ N.fixing N.Wt

def Gam (Λ : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) := N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ

def IsTerm (g : ℕ) (Λ : Submodule (𝓞 K) V) : Prop :=
  IsFramed N.F N.F' Λ N.aa ∧ IsAdm N.F N.F' Λ (g : 𝓞 K)

def gI (g : ℕ) (Λ : Submodule (𝓞 K) V) : ℕ := idx (flagPairDefinitePartLattice N.F N.F' Λ) (latLa N.F N.F' Λ (g : 𝓞 K))

def iI (g : ℕ) (Λ : Submodule (𝓞 K) V) : ℕ := idx (latLa N.F N.F' Λ (g : 𝓞 K)) (latTh N.F N.F' Λ)

def bI (Λ : Submodule (𝓞 K) V) : ℕ := bOne N.F N.F' Λ N.j

def om (Λ : Submodule (𝓞 K) V) : ℝ := GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ)

def omSum (Q : Submodule (𝓞 K) V → Prop) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient N.R (Submodule (𝓞 K) V), if Q o.out then ENNReal.ofReal (N.om o.out) else 0

def SameDat (g : ℕ) (Λ₀ Λ : Submodule (𝓞 K) V) : Prop :=
  latL N.F N.F' Λ = latL N.F N.F' Λ₀ ∧ latL N.F' N.F Λ = latL N.F' N.F Λ₀ ∧
    iotaGraph N.F N.F' Λ (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)

def Split (Λ : Submodule (𝓞 K) V) : Prop :=
  latTh N.F N.F' Λ = (Λ ⊓ rs (𝓞 K) N.Wt) ⊔ rs (𝓞 K) (II N.F N.F')

def Near (𝔠 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V) : Prop :=
  𝔠 • N.P0 ≤ Λ ⊓ rs (𝓞 K) N.Pi ∧ 𝔠 • (Λ ⊓ rs (𝓞 K) N.Pi) ≤ N.P0

end NF

def IsDat (H : HermSpace K V) (g : ℕ) (L₀ : Submodule (𝓞 K) V) (j x : ℕ)
    (d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) : Prop :=
  GlobalTheory.Mass.IsIntLat H.B.flip d.1 ∧ GlobalTheory.Mass.discN H.B.flip d.1 = GlobalTheory.Mass.discN H.B.flip L₀ ∧
    IsModIso H (g : 𝓞 K) d.1 L₀ d.2 ∧ idx L₀ (fixLat d.2) = x ∧ GenBy L₀ (fixLat d.2) j

def Trip (H : HermSpace K V) (g : ℕ) (L₀ : Submodule (𝓞 K) V) (j x x' : ℕ) :
    Set ((Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V)) :=
  {p | IsDat H g L₀ j x p.1 ∧ IsDat H g L₀ j x' p.2.1 ∧ p.2.2 ∈ isomGrp H ∧ imLat p.2.2 p.2.1.1 = p.1.1 ∧
    ∀ y y' : V, (y, y') ∈ p.2.1.2 ↔ (p.2.2 y, y') ∈ p.1.2}

def fixSp (η : V ≃ₗ[K] V) : Submodule K V := LinearMap.ker ((η : V →ₗ[K] V) - LinearMap.id)

end GlobalTheory.DegCnt
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre
section
noncomputable section

namespace GlobalTheory.SA

open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat

def ofHSpace {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) : HermSpace E S.V where
  B := S.hT.flip
  herm x y := S.herm.eq y x
  nondeg x h := S.nondeg.2 x h

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}

def xPlus (F : FlagD H r) : Submodule K V := F.X ⊔ Submodule.span K {F.z}

abbrev latX (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := Λ ⊓ rs R F.X

def IsComp (F F' : FlagD H r) (u : V) (a a' : K) : Prop := u - a • F.z - a' • F'.z ∈ F.X ⊔ F'.X

def redLat (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := (Λ ⊓ rs R (perp H F.X)) ⊔ rs R F.X

def IsPairMap (F F' F'' : FlagD H r) (Λ : Submodule R V) (g : R) (β : V ≃ₗ[K] V) : Prop :=
  F'.X.map (β : V →ₗ[K] V) = F''.X ∧ (perp H F'.X).map (β : V →ₗ[K] V) = perp H F''.X ∧
  (∀ x ∈ perp H F'.X, ∀ y ∈ perp H F'.X, H.B (β x) (β y) = H.B x y) ∧
  imLat β (redLat F' Λ) = redLat F'' Λ ∧ β F'.z - F''.z ∈ F''.X ∧
  ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), ∀ l'' ∈ Λ ⊓ rs R (perp H F''.X), β l' - l'' ∈ F''.X →
    l'' - l' ∈ latX F Λ ⊔ smulLat g Λ

def fixSp (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : Submodule K V where
  carrier := {x | x ∈ wSp F F' ∧ ∃ x'' ∈ wSp F F'', x - x'' ∈ F.X ∧ β x - x'' ∈ F''.X}
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, a, ha, h1, h2⟩ ⟨hy, b, hb, h3, h4⟩
    refine ⟨add_mem hx hy, a + b, add_mem ha hb, ?_, ?_⟩
    · rw [add_sub_add_comm]; exact add_mem h1 h3
    · rw [map_add (f := _), add_sub_add_comm]; exact add_mem h2 h4
  smul_mem' := by
    rintro c x ⟨hx, a, ha, h1, h2⟩
    refine ⟨Submodule.smul_mem _ c hx, c • a, Submodule.smul_mem _ c ha, ?_, ?_⟩
    · rw [← smul_sub]; exact Submodule.smul_mem _ c h1
    · rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ c h2

theorem perp_anti {S S' : Submodule K V} (h : S ≤ S') : perp H S' ≤ perp H S := fun y hy =>
  (mem_perp_iff H S y).2 fun x hx => (mem_perp_iff H S' y).1 hy x (h hx)

theorem perp_sup (S S' : Submodule K V) : perp H (S ⊔ S') = perp H S ⊓ perp H S' := by
  refine le_antisymm (le_inf (perp_anti le_sup_left) (perp_anti le_sup_right)) fun y hy => ?_
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _), (mem_perp_iff H _ y).1 hy.1 a ha, (mem_perp_iff H _ y).1 hy.2 b hb, add_zero]

theorem mem_perp_span (s : Set V) (y : V) :
    y ∈ perp H (Submodule.span K s) ↔ ∀ x ∈ s, H.B y x = 0 := by
  rw [mem_perp_iff]
  refine ⟨fun h x hx => h x (Submodule.subset_span hx), fun h x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, ha, smul_zero]

theorem X_eq_span (F : FlagD H r) :
    F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
  rw [FlagD.X, FlagD.Xa, ← Set.image_univ]
  congr 2
  ext b
  simp

theorem xPlus_eq_span (F : FlagD H r) : xPlus F = Submodule.span K (Set.range F.e) := by
  rw [xPlus, X_eq_span, ← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Fin.exists_fin_succ', FlagD.z, eq_comm]

theorem mem_perp_xPlus (F : FlagD H r) (y : V) :
    y ∈ perp H (xPlus F) ↔ y ∈ perp H F.X ∧ H.B y F.z = 0 := by
  rw [xPlus, perp_sup, Submodule.mem_inf, mem_perp_span]
  simp



theorem xPlus_sup (F F' : FlagD H r) : xPlus F ⊔ xPlus F' = V0 F F' := by
  rw [xPlus, xPlus, V0, Submodule.span_insert, sup_sup_sup_comm]

theorem wSp_eq (F F' : FlagD H r) : wSp F F' = perp H (xPlus F) ⊓ perp H (xPlus F') := by
  rw [wSp, ← xPlus_sup, perp_sup]

section Pair

variable {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} {β : V ≃ₗ[K] V}

end Pair

namespace FlagExample

open NumberField Formalism.BasicNotions.Examples₂

variable (E : Type) [Field E] [NumberField E] [StarRing E]

variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)

end FlagExample

end GlobalTheory.SA

end
end

