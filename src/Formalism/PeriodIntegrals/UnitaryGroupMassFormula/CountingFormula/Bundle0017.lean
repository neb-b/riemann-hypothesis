module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowers
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical ValuativeRel

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def pbLat {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    (x : ι → V) (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) V :=
  Submodule.span (𝓞 K) {v | ∃ i, ∃ c ∈ (𝔞 i : Submodule (𝓞 K) K), v = c • x i}

def gram {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (x : ι → V) : Matrix ι ι K :=
  Matrix.of fun i j => h (x i) (x j)

def NMPseudo : Prop :=
  ∀ (K F V ι : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x : ι → V)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → Module.finrank F K = 2 → h.IsSymm →
    (∀ i, ∀ a ∈ (𝔞 i : Submodule (𝓞 K) K), star a ∈ (𝔞 i : Submodule (𝓞 K) K)) → (∀ i, 𝔞 i ≠ 0) →
    LinearIndependent K x → Submodule.span K (Set.range x) = X → (gram h x).det ≠ 0 →
    Formalism.HermitianLatticesTheory.IsIntegralLat h (pbLat x 𝔞) →
    nM F h X (pbLat x 𝔞) ^ 2 =
      (FractionalIdeal.absNorm ((∏ i, 𝔞 i ^ 2) *
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) : ℝ)

def flagDifferenceVectors (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim F0.fvec fun b => ((gS D : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)

def differentIdealPowers (D : Formalism.BasicNotions.D7) : Fin (D.R.rS + 1) → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (fun a : Fin D.R.rS => ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))) 1

def MMPseudo : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z →
        ZhatL (lf D F0) F' = Z → Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') →
        MMof D F0 F' = pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D))

def DetGa : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T T' : D.host.E), star T = T → star T' = T' → ∀ Z : MatZ D,
    (Ga T T' Z).det = (-1) ^ (D.R.rS + 1) * GZ T T' Z

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.MassConstUniqueOne
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

section Local

variable (K F : Type) [Field K] [Field F] [NumberField F] [Algebra F K]

def vT (T : ℕ) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((T : ℕ) : 𝓞 F)}))

end Local

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Const

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem massConst_unique_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {c c' : ℝ}
    (hc : MassConst K F 1 c) (hc' : MassConst K F 1 c') : c = c' := by
  have ho := stdLat_isOrtho K 1
  have hs := stdForm_isSymm K 1
  have e := hc _ (stdForm K 1) (stdLat K 1) hs (isTotPosDef_of_ortho hK hs ho) (finrank_of_ortho ho)
    (isFullLattice_of_ortho ho) (isIntegralLat_of_ortho ho)
  have e' := hc' _ (stdForm K 1) (stdLat K 1) hs (isTotPosDef_of_ortho hK hs ho) (finrank_of_ortho ho)
    (isFullLattice_of_ortho ho) (isIntegralLat_of_ortho ho)
  rw [lamG_eq_one_of_ortho hK hF hs ho, mul_one] at e e'
  rw [← e, ← e']

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem massConst_cMass (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) (hm : 1 ≤ m) :
    MassConst K F m (cMass K F m) := by
  obtain ⟨c₁, hc₁, hall⟩ := massConst_all hermRepUnram liStat hK hF
  have h1 : MassConst K F 1 c₁ := by
    have := hall 1 le_rfl
    rwa [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty, mul_one] at this
  have hex : ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := ⟨c₁, hc₁, h1⟩
  have hone : cOne K F = c₁ := by
    unfold cOne
    rw [dite_eq_left hex]
    exact massConst_unique_one hK hF hex.choose_spec.2 h1
  unfold cMass
  rw [hone]
  exact hall m hm

end Const


end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

