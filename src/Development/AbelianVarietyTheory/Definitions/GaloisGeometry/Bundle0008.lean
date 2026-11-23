module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
section
noncomputable section

namespace GlobalTheory.HTW.LJ

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual NumberField IsDedekindDomain

variable {D : D7}

section Sets

variable (D)

def c0 : ℚ := ((D.R.t : ℚ) - 1) / 2

def sz (j : ℕ) (ρ : D.what₂.Tau) : ℚ :=
  if h : j - 1 < D.R.m then (D.hc ρ).e ⟨j - 1, h⟩ else 0

def cloudJ (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  {q | ∃ a : Fin (D.R.k - 1), q = sz D j ρ + (D.hc ρ).v a + c0 D}

def lowJ (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  {q | ∃ a : Fin D.R.m, q = sz D j ρ - (D.hc ρ).b a + c0 D}

def blockJ : Set ℚ := {q | ∃ c : ℕ, c < D.R.t ∧ q = c}

def Jp (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := cloudJ D j ρ ∪ lowJ D j ρ ∪ blockJ D

def refl (q : ℚ) : ℚ := ((D.R.t : ℚ) - 1) - q

def reflS (S : Set ℚ) : Set ℚ := {q | refl D q ∈ S}

def Jm (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := reflS D (Jp D j ρ)

def JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := if up then Jp D j ρ else Jm D j ρ

def cloudT (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  if up then cloudJ D j ρ else reflS D (cloudJ D j ρ)

def lowT (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  if up then lowJ D j ρ else reflS D (lowJ D j ρ)

def JW (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := cloudT D up j ρ ∪ lowT D up j ρ

def dualS (S : Set ℚ) : Set ℚ := {q | -q - 1 ∈ S}

end Sets

section Emb

variable (D)

def PlaceOf (ρ : D.what₂.Tau) (g : D.R.GG) : Prop :=
  ((D.eTau ρ : D.R.Psi) : D.R.GG) = g ∨
    ((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc = g

def TypeU (ep : Bool) (g : D.R.GG) : Prop := (g ∈ D.R.Psi ↔ ep = true)

def ReadAt (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i)) (g : D.R.GG)
    (ρ : D.what₂.Tau) : Prop :=
  (D.naut.iotaQC i).toRingHom.comp τ₀ = D.host.emb g ∧ PlaceOf D ρ g

variable {D}

def gEmb {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) :
    D.host.E →+* Qbar (D.nd.l i) :=
  (C.LL.1.val.toRingHom).comp (τ.toRingHom.comp (Br.cEw D.nbr i w hw))

end Emb

section Stmt

variable (D)


open Classical in
def hodgeTateJumpsAtModulesForSign (ep : Bool) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1),
      ∃ (g : D.R.GG) (ρ : D.what₂.Tau), ReadAt D i (gEmb C τ) g ρ ∧
        (∀ (x : D.nd.X i) (a : ℤ),
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a ↔
            (a : ℚ) ∈ JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
            (if (a : ℚ) ∈ JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ then 1 else 0) ∧
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a ↔
            (a : ℚ) ∈ dualS (JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ)) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
            (if (a : ℚ) ∈ dualS (JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ) then 1 else 0)) ∧
        ∀ (ρπ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), π ∈ D.nd.Z i →
          TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρπ π → ∀ a : ℤ,
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a ↔
            (a : ℚ) ∈ JW D (decide (TypeU D ep g)) (D.nd.j i) ρ) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a =
            (if (a : ℚ) ∈ JW D (decide (TypeU D ep g)) (D.nd.j i) ρ then 1 else 0) ∧
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a ↔
            (a : ℚ) ∈ dualS (JW D (decide (TypeU D ep g)) (D.nd.j i) ρ)) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a =
            (if (a : ℚ) ∈ dualS (JW D (decide (TypeU D ep g)) (D.nd.j i) ρ) then 1 else 0)

def ConclusionJa : Prop := ∃ ep : Bool, hodgeTateJumpsAtModulesForSign D ep

end Stmt

end GlobalTheory.HTW.LJ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JumpWindow
section
noncomputable section

namespace GlobalTheory.BlockWindow

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain

def JointTB (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ) : Prop :=
  D.nd.l i ≠ 2 ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.inert D.nbr i w hw = IK (D.nbr i w hw).Kw ∧ (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 ∧
    ∀ (CL : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ CL.1) (hs : Good (D.nbr i w hw).Kw 1 CL)
      (Y : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥CL.1 ↥(OL CL)),
      IsCrys (Br.PD D.loc D.nbr i w hw) Y.ρ →
      (∀ τ, JumpsInV (Br.PD D.loc D.nbr i w hw) Y.ρ τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ a}) →
      (∀ a ∈ LocalSituation.Jset (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) Y,
        -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
      ∀ e < D.R.t,
        LocalSituation.cTBY (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) Y M0 h0 e ≤ cB

def JumpWindow (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (h₁ : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (CL : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ CL.1) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥CL.1),
    ∃ U : Finset ℤ, U.card ≤ D.R.nV ∧ (∀ u ∈ U, -(h₁ : ℤ) ≤ u ∧ u + 1 ≤ h₁) ∧
      ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw)
        (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ a → a ∈ U

theorem JointTB.mono {D : D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc}
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {π : D.nd.X i} {M0 h0 cB cB' : ℕ} (hle : cB ≤ cB')
    (h : JointTB D HW F i r π M0 h0 cB) : JointTB D HW F i r π M0 h0 cB' := by
  refine ⟨h.1, fun w hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2 w hw
  refine ⟨h1, h2, fun CL hL hs Y hc hY => ?_⟩
  obtain ⟨k1, k2⟩ := h3 CL hL hs Y hc hY
  exact ⟨k1, fun e he => (k2 e he).trans hle⟩

end GlobalTheory.BlockWindow

end
end

