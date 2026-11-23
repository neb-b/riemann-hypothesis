module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DPairOneIrr
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

def MoveDefInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel →
    ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ),
      0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
      markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ

namespace MoveEx

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example

end MoveEx

end GlobalTheory.LKDef
end
end

-- bundled from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MarkWeightedFixedPointEqDefinitePairOdd
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights

variable {p : ℕ} [Fact p.Prime]

def eigL (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : Fin G.n → ℂ) : ℂ :=
  if h : FixL G v β y z then h.choose else 0

def cxSumAtM (G : HTGroup p) (v : InfinitePlace G.F) (c : Polynomial G.F → ℂ → ℂ) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : Pts G v β x t hx Kf K',
    ((Nat.card (Stab G v β x t hx Kf K' (Quot.out q)) : ℕ) : ℂ)⁻¹ *
      ∑ᶠ y : grp G β, if FixL G v β y (Quot.out q).2.1 then
        f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) *
          f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) *
          c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (eigL G v β y (Quot.out q).2.1) else 0

def cxSumM (G : HTGroup p) (v : InfinitePlace G.F) (c : Polynomial G.F → ℂ → ℂ) (P : Form G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  cxSumAtM G v c P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec Kf f K' f'

def cxTotalM (G : HTGroup p) (v : InfinitePlace G.F) (c : Polynomial G.F → ℂ → ℂ) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : FCls G, cxSumM G v c (Quot.out q) Kf f K' f'

def markSumC (G : HTGroup p) (c : Polynomial G.F → ℂ → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if h : ∃ μ, (Quot.out q).Mark μ then
    c (Quot.out q).pol h.choose * (Quot.out q).term Kf f 1 K' f' else 0

def rootSum (G : HTGroup p) (v : InfinitePlace G.F) (c : Polynomial G.F → ℂ → ℂ) (P : Polynomial G.F) : ℂ :=
  (((P.map v.embedding).roots).map (c P)).sum

def CxCountRegMark : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 →
    ∀ (c : Polynomial G.F → ℂ → ℂ) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      cxTotalM G v c L.K.toSubgroup f K' f' = markSumC G c L.K.toSubgroup f K' f'

def MarkWeightedFixedPointEqDefinitePairOdd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 →
    ∀ (c : Polynomial G.F → ℂ → ℂ) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
    (∀ P : Pair G, (∃ μ, P.Mark μ) → ¬ Irreducible P.pol → P.term L.K.toSubgroup f 1 K' f' = 0) →
      cxTotalM G v c L.K.toSubgroup f K' f' = dSumIrr G (rootSum G v c) L.K.toSubgroup f 1 K' f'

end GlobalTheory.RootSumWeights
end
end

-- bundled from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

namespace HeckeTraceForms

variable {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V]

def forms (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) : Submodule ℂ (H → V) where
  carrier := {φ | (∀ γ g, φ (ι γ * g) = ξ γ (φ g)) ∧ ∀ k ∈ K, ∀ g, φ (g * k) = φ g}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun γ g => by simp [ha1, hb1], fun k hk g => by simp [ha2 k hk, hb2 k hk]⟩
  zero_mem' := ⟨fun γ g => by simp, fun k hk g => by simp⟩
  smul_mem' := by
    rintro c a ⟨h1, h2⟩
    exact ⟨fun γ g => by simp [h1], fun k hk g => by simp [h2 k hk]⟩

def IsHecke (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (T : forms ι K ξ →ₗ[ℂ] forms ι K ξ) : Prop :=
  ∀ φ g, (T φ : H → V) g = ∑ᶠ h : H ⧸ K, F h.out • (φ : H → V) (g * h.out)

def heckeTrace (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ) : ℂ :=
  if h : ∃ T, IsHecke ι K ξ F T then LinearMap.trace ℂ (forms ι K ξ) h.choose else 0

theorem heckeTrace_zero (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) :
    heckeTrace ι K ξ (fun _ => 0) = 0 := by
  have h0 : IsHecke ι K ξ (fun _ => 0) 0 := fun φ g => by simp
  have h : ∃ T, IsHecke ι K ξ (fun _ => 0) T := ⟨0, h0⟩
  have hT : h.choose = 0 := by
    apply LinearMap.ext; intro φ; apply Subtype.ext; funext g
    rw [h.choose_spec φ g]; simp
  rw [heckeTrace, dite_eq_left h, hT, map_zero]

end HeckeTraceForms

variable {p : ℕ} [Fact p.Prime]

structure DForm (G : HTGroup p) where

  β : G.Cˣ
  sym : sh G β = β
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t

  posR : ∀ v : InfinitePlace G.F, ∀ x : Fin G.n → ℂ, x ≠ 0 →
    (sigPosH (G.gram_herm v) = 1 → 0 < (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re < 0)

namespace DForm

variable {G : HTGroup p}

def Rel (P Q : DForm G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y)

def ofDPair (P : DPair G) : DForm G := ⟨P.β, P.sym, P.trivAf, P.posR⟩

def embAt (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t) :
    GlobalTheory.LKCx.grp G B.β →* G.GAf × Gr G 1 :=
  (GlobalTheory.LKCx.toAfF G B.β x t hx).prod (GlobalTheory.LKCx.toP1 G B.β)

def emb (B : DForm G) : GlobalTheory.LKCx.grp G B.β →* G.GAf × Gr G 1 :=
  B.embAt B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec

def trace (B : DForm G) {V : Type} [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  HeckeTraceForms.heckeTrace B.emb (Kf.prod K') (ξ.comp (GlobalTheory.LKCx.grp G B.β).subtype) (fun h => f h.1 * f' h.2)

end DForm

def DFCls (G : HTGroup p) : Type := Quot (DForm.Rel (G := G))

def dTrace (G : HTGroup p) {V : Type} [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : DFCls G, (Quot.out q).trace ξ Kf f K' f'

def RegIrr (G : HTGroup p) (x : G.C) : Prop :=
  (minpoly G.F x).natDegree = G.n ∧ (minpoly G.F x).Separable ∧ Irreducible (minpoly G.F x)

def TraceDefinitePairsEqAutomorphicTrace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
      (wt : Polynomial G.F → ℂ),
      (∀ (B : DForm G) (y : GlobalTheory.LKCx.grp G B.β), (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n →
        (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable →
        LinearMap.trace ℂ V (ξ y.1) = wt (minpoly G.F ((y.1.1 : G.Cˣ) : G.C))) →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      (∀ (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t)
          (y : GlobalTheory.LKCx.grp G B.β), ¬ RegIrr G ((y.1.1 : G.Cˣ) : G.C) →
        GlobalTheory.LKCount.orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.embAt x t hx y)
          (fun h => f h.1 * f' h.2) = 0) →
      dSumIrr G wt L.K.toSubgroup f 1 K' f' = dTrace G ξ L.K.toSubgroup f K' f'

namespace HeckeTraceExample

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example GlobalTheory.LKDef.Example

theorem indicator_bi {H : Type} [Group H] (K : Subgroup H) :
    ∀ k ∈ K, ∀ k' ∈ K, ∀ g, Set.indicator (K : Set H) (1 : H → ℂ) (k * g * k') = Set.indicator (K : Set H) 1 g := by
  intro k hk k' hk' g
  have : k * g * k' ∈ K ↔ g ∈ K := by
    rw [K.mul_mem_cancel_right hk', K.mul_mem_cancel_left hk]
  by_cases hg : g ∈ K
  · simp [Set.indicator_apply, hg, this.2 hg]
  · have h2 : k * g * k' ∉ K := fun h => hg (this.1 h)
    simp [Set.indicator_apply, hg, h2]

end HeckeTraceExample

end GlobalTheory.LKDef
end
end

