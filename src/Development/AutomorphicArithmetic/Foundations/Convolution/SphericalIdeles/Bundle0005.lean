module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftAll
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.DescAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SameSat
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormUnr
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SmoEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Imports
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.T GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual
open UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS

theorem UpperTheory.ConvolutionTheory.Sph.down :
    UpperTheory.ConvolutionTheory.Sph.Down := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hW v hv ⟨w, hwv, B', hB'⟩
  let μE : Measure (normOneGL (K := E) (n := n)) := Measure.haar
  let μF : Measure (normOneGL (K := F) (n := n)) := Measure.haar
  have hnorm := Sph.norm F E σ hσ hp n hn μE μF π P hW
  obtain ⟨s, χ, χ', V, V', θ, hχ, hχ', hV, hV', hθ, hst, hW', -, hOff⟩ := hnorm
  obtain ⟨-, htw⟩ := powTwist F E
  obtain ⟨hi, -, h1⟩ := htw s χ χ' hχ hχ'
  obtain ⟨hback, -⟩ := h1 n hn
  obtain ⟨-, hAtE, hcl, -⟩ := carryLift F E σ hσ hp n hn μE μF
  have hsat : ∃ B, (Cusp.cx (P.twist χ')).sat w B := by
    have := satake_twist_holds E n (CG.mk P) χ' w B' (Sph.powSat E χ' s hχ' w).1 hB'
    rw [CG.twist_mk] at this
    exact ⟨_, this⟩
  obtain ⟨B₁, hB₁⟩ := hsat
  have hS1 : SSat μE V' w (B₁.map fun b : ℂˣ => (b : ℂ)) := (Dp.sSatIff E n μE _ V' hV' w _).2 ⟨B₁, rfl, hB₁⟩
  have hsph : ∀ u : Pl E, u.under (𝓞 F) = v → ∃ B, SSat μE V' u B := fun u hu =>
    Dp.sSatEx E n μE V' hV'.summand u (Sph.sphConj F E σ hσ hp n hn μE θ hθ V' hst w u (hwv.trans hu.symm) hS1.2.1)
  choose! b hb using hsph
  obtain ⟨Λ, t, S, hS, hAt⟩ := hAtE V' hV'.summand
  let t₁ : Pl E → Multiset ℂ := fun u => if u.under (𝓞 F) = v then b u else t u
  let S₀ : Set (Pl E) := S \ {u | u.under (𝓞 F) = v}
  have hS₀ : S₀.Finite := hS.subset Set.diff_subset
  have hAt₁ : At μE S₀ V' Λ t₁ := by
    refine ⟨hAt.1, fun u hu => ?_⟩
    by_cases h : u.under (𝓞 F) = v
    · simp only [t₁, if_pos h]
      exact hb u h
    · simp only [t₁, if_neg h]
      exact hAt.2 u fun h' => hu ⟨h', h⟩
  have hAE₁ : AtAE μE V' Λ t₁ := ⟨S₀, hS₀, hAt₁⟩
  obtain ⟨V₀, Λ₀, t₀, hV₀, hAt₀, hΛ, ht, hv₀, -⟩ := Sph.descAt ci Sph.gm F E σ hσ hp n hn μE μF θ hθ V' Λ t₁ S₀
    hV'.summand hst hS₀ hAt₁ (hOff _ _ hAE₁) v hv (fun u hu h => h.2 hu)
  obtain ⟨π₀, hπ₀, -⟩ := Dp.exCusp F n μF V₀ hV₀
  have hl := hcl π₀ _ V₀ V' Λ₀ t₀ Λ t₁ hπ₀ hV' hAt₀ hAE₁ hΛ ht
  obtain ⟨η, hη, hiso⟩ := (R.fibre_holds F E hp n hn (.cx π₀) (.cx (P.twist χ')) hl.1).2 (.cx (π.twist χ)) hW'
  have he : π₀.twist η = π.twist χ := (Dp.isoEq F n _ _).1 hiso
  obtain ⟨B₀, -, hB₀⟩ := (Dp.sSatIff F n μF π₀ V₀ hπ₀ v _).1 hv₀
  have hηu : η.UnrAt v := by
    rcases hη with rfl | hη
    · intro x _
      rfl
    · exact Sph.normUnr F E η hη v hv
  have h2 := satake_twist_holds F n (CG.mk π₀) η v B₀ hηu hB₀
  rw [CG.twist_mk, he] at h2
  have h3 := satake_twist_holds F n (CG.mk (π.twist χ)) χ⁻¹ v _ (Sph.powSat F χ⁻¹ (-s) hi v).1 h2
  rw [CG.twist_mk, hback] at h3
  exact ⟨_, h3⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.TwoLeAbsNorm
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.T GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual
open UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS

private theorem same_sat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex F] [IsGalois F E] {n : ℕ} (hp : (Module.finrank F E).Prime) (π : CuspSub F n)
    {sat sat' : Pl E → Multiset ℂˣ → Prop}
    (H : WeakBC (CG.mk π).HasSat sat) (H' : WeakBC (CG.mk π).HasSat sat') :
    ∀ᶠ w : Pl E in cofinite, ∃ B, sat w B ∧ sat' w B := by
  have hN := (places F E hp).2.2.2.2.1
  filter_upwards [H, H'] with w a b
  have hn : normV w = normV (w.under (𝓞 F)) ^ resDeg F w := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hN w
  obtain ⟨B, hB, hB'⟩ := a _ hn
  obtain ⟨C, hC, hC'⟩ := b _ hn
  obtain rfl := hB.unique hC
  exact ⟨_, hB', hC'⟩

private theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (v : Pl K) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have a := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have b := Ideal.absNorm_eq_one_iff.not.2 v.isPrime.ne_top
  omega

theorem UpperTheory.ConvolutionTheory.Sph.up :
    UpperTheory.ConvolutionTheory.Sph.Up := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hW v hv B hB w hw f hf
  let μE : Measure (normOneGL (K := E) (n := n)) := Measure.haar
  let μF : Measure (normOneGL (K := F) (n := n)) := Measure.haar
  have hnorm := Sph.norm F E σ hσ hp n hn μE μF π P hW
  obtain ⟨s, χ, χ', V, V', θ, hχ, hχ', hV, -, hθ, -, hW', hOff, -⟩ := hnorm
  obtain ⟨c1, -, c3, -⟩ := carryLift F E σ hσ hp n hn μE μF
  obtain ⟨Λ, t, S, hS, hAt⟩ := c1 V hV.summand
  have hN := (places F E hp).2.2.2.2.1

  have hBv : (CG.mk (π.twist χ)).HasSat v (B.map (· * χ.val v)) := by
    have := satake_twist_holds F n (CG.mk π) χ v B (Sph.powSat F χ s hχ v).1 hB
    rwa [CG.twist_mk] at this
  have hSv : SSat μF V v ((B.map (· * χ.val v)).map fun b : ℂˣ => (b : ℂ)) :=
    (Dp.sSatIff F n μF (π.twist χ) V hV v _).2 ⟨_, rfl, hBv⟩

  let t₁ : Pl F → Multiset ℂ := Function.update t v ((B.map (· * χ.val v)).map fun b : ℂˣ => (b : ℂ))
  have hAt₁ : At μF (S \ {v}) V Λ t₁ := by
    refine ⟨hAt.1, fun u hu => ?_⟩
    by_cases e : u = v
    · subst e
      simpa [t₁] using hSv
    · have hu' : u ∉ S := fun h => hu ⟨h, e⟩
      simpa [t₁, Function.update_of_ne e] using hAt.2 u hu'
  have hfin : (S \ {v}).Finite := hS.diff
  have hAE₁ : AtAE μF V Λ t₁ := ⟨_, hfin, hAt₁⟩
  obtain ⟨V'', hV'', hAE'', hup⟩ := Sph.liftAt ci Sph.gm F E σ hσ hp n hn μE μF θ hθ V Λ t₁ (S \ {v})
    hV.summand hfin hAt₁ (hOff Λ t₁ hAE₁) v (by simp) hv

  obtain ⟨P', hP', -⟩ := Dp.exCusp E n μE V'' hV''
  have hl := c3 _ P' V V'' Λ t₁ _ _ hV hP' hAE₁ hAE'' rfl (Filter.Eventually.of_forall fun _ => rfl)
  have e : P' = P.twist χ' := Sph.smoEq E n hn P' (P.twist χ') (same_sat hp (π.twist χ) hl.1 hW')
  rw [e] at hP'

  obtain ⟨B', hB'e, hB'⟩ := (Dp.sSatIff E n μE (P.twist χ') V'' hP' w _).1 (hup w hw)
  have h1 := hN w
  rw [hw] at h1
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hf
  have hg : f = resDeg F w := Nat.pow_right_injective (two_le_absNorm v) (hf'.symm.trans h1)
  have hB'' : B' = B.map fun b => (b * χ.val v) ^ f := by
    refine Multiset.map_injective Units.val_injective ?_
    rw [← hB'e, bcSat, hw, ← hg]
    simp [t₁, Multiset.map_map]
  subst hB''

  obtain ⟨-, hinv, h3⟩ := (powTwist F E).2 s χ χ' hχ hχ'
  have htt := (h3 n hn).2.1 P
  have hval : χ'.val w = χ.val v ^ f := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, (Sph.powSat F χ s hχ _).2, (Sph.powSat E χ' s hχ' w).2, hf', Nat.cast_pow,
      ← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]
  have hfin' := satake_twist_holds E n (CG.mk (P.twist χ')) χ'⁻¹ w _ (Sph.powSat E χ'⁻¹ (-s) hinv w).1 hB'
  rw [CG.twist_mk, htt] at hfin'
  change (CG.mk P).HasSat w _
  convert hfin' using 1
  simp [Multiset.map_map, hval, mul_pow, HChar.val_inv]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStableAlt
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

private theorem weak_same {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (hp : (Module.finrank F E).Prime) (π : CuspSub F n)
    {sat sat' : Pl E → Multiset ℂˣ → Prop} (H : WeakBC (CG.mk π).HasSat sat) (H' : WeakBC (CG.mk π).HasSat sat') :
    ∀ᶠ w : Pl E in cofinite, ∃ B, sat w B ∧ sat' w B := by
  have hN := (places F E hp).2.2.2.2.1
  filter_upwards [H, H'] with w a b
  have hw : normV w = normV (w.under (𝓞 F)) ^ resDeg F w := by
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hN w
  obtain ⟨B, hB, hB'⟩ := a _ hw
  obtain ⟨C, hC, hC'⟩ := b _ hw
  obtain rfl := hB.unique hC
  exact ⟨_, hB', hC'⟩

theorem UpperTheory.ConvolutionTheory.Sph.weakStable :
    UpperTheory.ConvolutionTheory.Sph.WeakStable := by
  intro K M _ _ _ _ _ _ _ _ hp n hn π P hW
  refine ⟨?_, fun v => ?_, fun w => ?_⟩
  · haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
    haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos
    haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
    obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
    let μE : Measure (normOneGL (K := M) (n := n)) := Measure.haar
    let μF : Measure (normOneGL (K := K) (n := n)) := Measure.haar
    obtain ⟨s, χ, χ', V, V', θ', hχ, hχ', hV, hV', hθ', hst', hW', hOff, hOff'⟩ :=
      UpperTheory.ConvolutionTheory.Sph.norm K M σ hσ hp n hn μE μF π P hW
    obtain ⟨-, htw⟩ := powTwist K M
    obtain ⟨hi, hi', h1⟩ := htw s χ χ' hχ hχ'
    obtain ⟨-, hback, -⟩ := h1 n hn
    obtain ⟨-, -, h2⟩ := htw (-s) χ⁻¹ χ'⁻¹ hi hi'
    obtain ⟨-, -, -, hCj, -⟩ := h2 n hn
    obtain ⟨c1, -, c3, -, -, θ, hθ, c6⟩ := carryLift K M σ hσ hp n hn μE μF
    obtain ⟨Λ, t, hAt⟩ := c1 V hV.summand
    obtain ⟨V₂, hV₂, hst, hAt₂⟩ :=
      coreLift ci Sph.gm K M σ hσ hp n hn μE μF θ hθ V Λ t hV.summand hAt (hOff Λ t hAt)
    obtain ⟨P₂, hP₂, -⟩ := Dp.exCusp M n μE V₂ hV₂
    have hl := c3 _ P₂ V V₂ Λ t _ _ hV hP₂ hAt hAt₂ rfl (Filter.Eventually.of_forall fun _ => rfl)
    have e : P₂ = P.twist χ' := Sph.smoEq M n hn P₂ (P.twist χ') (weak_same hp (π.twist χ) hl.1 hW')
    rw [e] at hP₂
    intro g
    have h := hCj (P.twist χ') _ ((c6 _ V₂ hP₂).2 hst g)
    rwa [hback] at h
  · exact (LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL K n π v).imp fun _ h => h.1
  · exact (LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL M n P w).imp fun _ h => h.1
end

