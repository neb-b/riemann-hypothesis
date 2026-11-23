module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0011
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0036
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0037
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseJacobsonPowers.SfrMulMemJHfr

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.BallQuot
section
noncomputable section

namespace PI.PoleLengthCount

theorem pole_ballQuot : BallQuot := ball_quotient_length

end PI.PoleLengthCount
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFrom
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

theorem ball_product_length : PiBallFrom := by
  intro hPi hBQ D B P j X ka wL wF G la Q S CRm T e c hOk k

  have hC : Q.InCurve := hOk.2.1
  haveI : FiniteDimensional (Kp X la G.N) (OsK X la G.w) := hC.1
  haveI : IsReduced (OsK X la G.w) := hC.2.1
  haveI : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  have hU := isUnif_of_curve Q hC

  have hle : ballO (unifO X la G.N) Q.e Q.c ≤
      ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ)) := by
    intro v hv
    exact ball_mono hU hC.2.2 (fun ζ => by dsimp only; omega) hv

  have h1 := hPi (Op X la G.N) (SectionSheafQuotient X la G.w wF) (Mon (WeightFamilies.dimY D j) k)
    (ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ)))
    (ballO (unifO X la G.N) Q.e Q.c) hle
  have h2 := hBQ (Op X la G.N) (Kp X la G.N) (OsK X la G.w) (unifO X la G.N)
    (unifO_irreducible X la G.N) (finite_As_of_curve Q hC) (SectionSheafQuotient X la G.w wF) Q.e hC.2.2 Q.c (Q.mm S T e)
  refine h1.trans ?_
  rw [h2, Fintype.card_coe, Nat.cast_mul]

end PI.PoleLengthCount
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiLenHolds
section
noncomputable section

namespace PI.PoleLengthCount

open Module

theorem piLen_holds : PiLen := by
  intro R M ι _ _ _ _ P Q _
  classical
  set PP := Submodule.pi Set.univ fun _ : ι => P
  set QQ := Submodule.pi Set.univ fun _ : ι => Q
  let q : Submodule R ↥P := Q.comap P.subtype
  let g : ι → (↥PP →ₗ[R] ↥P) := fun i =>
    ((LinearMap.proj i).comp PP.subtype).codRestrict P (fun x => x.2 i (Set.mem_univ i))
  let f : ↥PP →ₗ[R] (ι → ↥P ⧸ q) := LinearMap.pi fun i => q.mkQ.comp (g i)
  have hker : QQ.comap PP.subtype = LinearMap.ker f := by
    ext x
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, f, QQ,
      Submodule.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      funext i
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      exact h i
    · intro h i
      have := congrFun h i
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero] at this
      exact this
  have hsurj : Function.Surjective f := by
    intro y
    choose p hp using fun i => Submodule.Quotient.mk_surjective q (y i)
    refine ⟨⟨fun i => (p i : M), fun i _ => (p i).2⟩, ?_⟩
    funext i
    simp only [f, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← hp i]
    rfl
  have e1 := (Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective f hsurj)
  rw [e1.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]

end PI.PoleLengthCount
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Vanish
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem mem_pow_smul_top_iff {N : ℕ} (la : HeightOneSpectrum (𝓞 B.KO)) (w : Fin N → B.Cusp j wL)
    {u : WeightFamilies.Wt D j} {a : ℕ} {x : ↥(HK X la w u)} :
    x ∈ Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) ↔ (x : Lw X la w) ∈ JHfr X la w u a := by
  rw [mem_Jid_pow_smul_top X la w, mem_JHfr X la w]

theorem hasse_preserves_kernel (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : HKPres G la := fun β x hx =>
  (mem_HK X la G.w).2 (hasse_presentation X la G.w wF β x ((mem_HK X la G.w).1 hx))

theorem leading_coeff_eq_zero_of_jet {N : ℕ} (la : HeightOneSpectrum (𝓞 B.KO)) (w : Fin N → B.Cusp j wL)
    {u : WeightFamilies.Wt D j} (x : ↥(HK X la w u)) (hx : (x : Lw X la w) ∈ JHfr X la w u 1) : toA0K X la w u x = 0 := by
  rw [reduction_eq_zero_iff_mem_ideal_smul, ← pow_one (Jid X la w), mem_pow_smul_top_iff la w]
  exact hx

theorem vanishingOnQuadric (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Vanish G la := by
  intro k β x hx hβ
  unfold rD
  split_ifs with h
  · refine leading_coeff_eq_zero_of_jet la G.w _ ?_
    have h1 := hasse_jid_power X la G.w wF β k _ ((mem_pow_smul_top_iff la G.w).1 hx)
    exact PI.HJP.JHfr_anti X la G.w wF (by omega) h1
  · rfl

end PI.PoleLengthCount
end
end

