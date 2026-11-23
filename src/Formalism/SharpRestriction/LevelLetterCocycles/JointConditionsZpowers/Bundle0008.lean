module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.TwentyWordsLeB
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrystallineLatticeOfJumpPoints
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

variable {D : D7}

section Pts

variable (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL)

variable {HW i r w hw Cx hG}

end Pts

theorem zeta_of_good {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l} (h : Good K 1 LL) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  haveI : NeZero (l : Om l) := ⟨by exact_mod_cast hl.ne'⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic l (Om l)) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hl).ne')
  have hp : IsPrimitiveRoot z l := Polynomial.isRoot_cyclotomic_iff.mp hz
  have hmem : z ∈ Ks K 1 := by
    unfold Formalism.BasicNotions.Loc.Ks
    exact (le_sup_right (a := K0 K)) (IntermediateField.subset_adjoin _ _ (by simpa using hp.pow_eq_one))
  exact ⟨⟨z, h.2.2.2 (Ks K 1).val ⟨z, hmem⟩⟩, IsPrimitiveRoot.coe_submonoidClass_iff.mp hp⟩

section Pts2

variable {L : SizeData₂ D} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}

end Pts2

theorem epsU_eq (i : D.nd.Loc) : epsU D.nd i = chiU D.nd i 1 * (chiU D.nd i 2)⁻¹ := by
  have ht : 2 ≤ D.R.t := by
    have := D.R.rank_add_five_le
    omega
  unfold epsU chiU Formalism.MainNotions.N.Glob.epsO
  rw [D.nd.chi_def i 2 (by norm_num) ht, show (-(((2 : ℕ) : ℤ) - 1)) = -1 by norm_num, zpow_neg_one,
    mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]

theorem rDuO_cont (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x : D.nd.X i) : Continuous fun g => rDuO D.nd i r x g := by
  have hinv : Continuous fun g : GE D.nd => g⁻¹ := continuous_inv
  have hχ : ∀ c, Continuous fun g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) :=
    fun c => D.nd.chi_cont i c
  have hc : Continuous fun g => (((chiU D.nd i 1 * epsU D.nd i) g : (D.nd.O i)ˣ) : D.nd.O i) := by
    rw [epsU_eq]
    have e : ∀ g, (((chiU D.nd i 1 * (chiU D.nd i 1 * (chiU D.nd i 2)⁻¹)) g : (D.nd.O i)ˣ) : D.nd.O i) =
        (chiU D.nd i 1 g : D.nd.O i) * ((chiU D.nd i 1 g : D.nd.O i) * (chiU D.nd i 2 g⁻¹ : D.nd.O i)) := by
      intro g
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_inv]
    simp only [e]
    exact (hχ 1).mul ((hχ 1).mul ((hχ 2).comp hinv))
  show Continuous fun g => (((chiU D.nd i 1 * epsU D.nd i) g : (D.nd.O i)ˣ) : D.nd.O i) •
    (rO D.nd i r x g⁻¹).transpose
  exact hc.smul ((hr x).comp hinv).matrix_transpose

section Cond

variable (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

variable {L HW i r ρ π}

variable (L HW i r ρ π)

attribute [local instance] nLet_neZero

variable {L HW i r ρ π}

end Cond

end Formalism.MainNotions.N

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LocalErrorBoundPlaces
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

open Classical

variable {D : D7}

section Exp

variable (L : SizeData₂ D)

def hN : ℕ := ⌊Formalism.MainNotions.TwistedPlaces.hB L⌋₊

def eA (CA : ℝ) (l : ℕ) : ℕ :=
  ⌈CA * (1 + ((hN L + hN L : ℕ) : ℝ) / (l : ℝ) + (1 + Real.logb l (((hN L + hN L : ℕ) : ℝ) + 1)))⌉₊

end Exp

section RowA

def lenA (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (e' : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  if lam ∈ dc.col then (2 * (locDeg D.host.E lam : ℚ) * D.R.m + 1) * e' else 0

variable (L : SizeData₂ D) (tb : Formalism.MainNotions.TwistedPlaces.Tab L)
  (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

end RowA

section Star

variable (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)

def localErrorBoundPlaces (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) : ℚ :=
  (∑ u ∈ dc.col, ((locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * D.nd.vdel i + 2 * D.nd.vdel i + Br.h0W i u ρ π +
      (D.R.r : ℚ) * (c0 u : ℚ))) +
    (D.R.t : ℚ) * (∑ w ∈ dc.row, ((locDeg D.host.E w : ℚ) + 2) * (cB : ℚ)) +
    4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i +
    (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col

end Star

end Formalism.MainNotions.N

end
end

