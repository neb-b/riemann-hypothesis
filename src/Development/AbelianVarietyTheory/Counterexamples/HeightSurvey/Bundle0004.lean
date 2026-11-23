module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsGoodFamily
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.S Matrix

namespace GlobalTheory.DefiniteCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jm_const (n : ℕ) (s : Bool) :
    Formalism.REAL.Jm (fun _ : Fin n => s) = (if s then (1 : ℂ) else -1) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [Formalism.REAL.Jm, h, Matrix.one_apply]

theorem kset_const (n : ℕ) (s : Bool) : Formalism.REAL.Kset (fun _ : Fin n => s) = UJset (fun _ : Fin n => s) := by
  ext g
  simp only [Formalism.REAL.Kset, UJset, Formalism.REAL.inUJ, jm_const, Set.mem_setOf_eq, Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  cases s <;> simp

theorem lowK_const (n : ℕ) (s : Bool) (lam : Fin n → ℝ) (a : Fin n) :
    Formalism.QuantumDeterminants.lowK (fun _ : Fin n => s) lam a = lam a - (((n : ℝ) - 1) / 2 - (a : ℕ)) := by
  have h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext b; simp
  have h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext b; simp
  have h3 : (a : ℕ) + 1 ≤ n := a.2
  simp only [Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Pi.sub_apply, Pi.add_apply, ne_eq, not_true_eq_false,
    and_false, and_true, Finset.filter_false, Finset.card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio]
  rw [show n - 1 - (a : ℕ) = n - ((a : ℕ) + 1) by omega, Nat.cast_sub h3]
  push_cast; ring

theorem isDS_const_top {n : ℕ} {s : Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsDS (fun _ => s) lam σ) :
    IsKTypeOf (fun _ => s) σ (Formalism.QuantumDeterminants.lowK (fun _ => s) lam) ⊤ := by
  obtain ⟨_, _, _, hirr, _, ⟨S, hS⟩, _⟩ := h
  have hfd := hS.1
  rcases hirr S S.closed_of_finiteDimensional (fun g hg v hv => hS.2.1 g (by rwa [kset_const]) v hv) with h0 | h1
  · obtain ⟨v, hv, hv0, _⟩ := hS.2.2.2.1
    exact absurd (by simpa [h0] using hv) hv0
  · rwa [h1] at hS

end GlobalTheory.DefiniteCheck

end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.MatchingNotVacuous
section
noncomputable section

namespace GlobalTheory.ThetaFrameCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem genFibre_tied (T : CDVR) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c) (hz : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt)
    (G : SAB H (Sp T.V)) (m : SABMap G Y.t yt) :
    ∃ (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _))
      (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (m' : SABMap t' Y.oF.t z),
      m1.φ = m'.φ ≫ Y.m0.toSABMap.φ ∧ m2.φ ≫ m.φ = m'.φ ≫ Y.m.φ := by
  obtain ⟨PP', cub, sym, adj, prim, m2, -⟩ :=
    sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap (algebraMap T.V T.Fr)) G
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ Y.t G _ yt (spMap (algebraMap T.V T.Fr)) m m2
  have cancel : ∀ (t' : SAB H (Sp T.Fr)) (p : Sp T.Fr ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' Y.oF.t z, n.φ = m'.φ ≫ Y.m.φ := by
    intro t' p hp n; subst hp
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n
  obtain ⟨m', hm'⟩ := cancel _ _ hz.symm n
  obtain ⟨m1, h1⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ (pullback.fst _ _) z Y.m0.toSABMap m'
  exact ⟨_, m1, m2, m', h1, hn.symm.trans hm'⟩

variable {Xo}

end GlobalTheory.ThetaFrameCheck
end
end

