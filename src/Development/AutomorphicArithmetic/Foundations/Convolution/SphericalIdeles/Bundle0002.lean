module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0003
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsoluteCharacterNorms.UnitExponentHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormRam
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.ConvolutionTheory.Sph

private theorem one_of_ramified {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (hp : (Module.finrank K M).Prime) (w : HeightOneSpectrum (𝓞 M))
    (hram : ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    w.asIdeal.inertiaDeg (𝓞 K) = 1 ∧ ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard = 1 := by
  have := w.isPrime
  haveI : Module.Finite K M := Module.finite_of_finrank_pos hp.pos
  have k := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (w.asIdeal.under (𝓞 K)) (𝓞 M) Gal(M/K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(M/K), Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(M/K),
    IsGalois.card_aut_eq_finrank] at k
  have he : w.asIdeal.ramificationIdx (𝓞 K) ≠ 1 := fun h => hram (Ideal.ramificationIdx_eq_one_iff.1 h)
  have hd : w.asIdeal.ramificationIdx (𝓞 K) ∣ Module.finrank K M :=
    ⟨((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K), by rw [← k]; ring⟩
  have hel := (Nat.dvd_prime hp).1 hd |>.resolve_left he
  rw [hel] at k
  have h1 : ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
    calc Module.finrank K M * (((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K))
        = ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * (Module.finrank K M * w.asIdeal.inertiaDeg (𝓞 K)) := by ring
      _ = Module.finrank K M * 1 := by rw [k, mul_one]
  exact ⟨Nat.eq_one_of_mul_eq_one_left h1, Nat.eq_one_of_mul_eq_one_right h1⟩

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
theorem UpperTheory.ConvolutionTheory.Sph.normRam :
    UpperTheory.ConvolutionTheory.Sph.NormRam := by
  intro K M _ _ _ _ _ _ hp w hram
  obtain ⟨hf, hg⟩ := one_of_ramified hp w hram
  refine ⟨?_, fun w' hw' => ?_, fun η hη hu => ?_⟩
  · have h := GlobalTheory.QuadNormChar.normV_under (K := K) w
    rwa [hf, pow_one] at h
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hg
    have h1 : w.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 M) := ⟨w.isPrime, ⟨rfl⟩⟩
    have h2 : w'.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 M) :=
      ⟨w'.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal hw'.symm⟩⟩
    rw [ha] at h1 h2
    exact HeightOneSpectrum.ext (h2.trans h1.symm)
  · let Ω := AlgebraicClosure M
    haveI : Module.Finite K M := Module.finite_of_finrank_pos hp.pos
    haveI : Algebra.IsAlgebraic M Ω := IsAlgClosure.isAlgebraic
    haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
    obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
    have hAv : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      exact hA (algebraMap (𝓞 K) (𝓞 M) x)
    have hmove : ∃ s ∈ Ine (F := K) A, ¬ UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes M s := by
      by_contra hfix
      push_neg at hfix
      obtain ⟨hlo, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 K)) w hAv hA hfix
      exact hram (Ideal.ramificationIdx_eq_one_iff.1 he)
    exact UpperTheory.Gal.UnramifiedFromSplittingCriterion.normRam K M Ω hp η hη A _ hAv hmove hu
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConjAlt
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1

namespace UpperTheory.ConvolutionTheory.Sph

open scoped Fin.NatCast Fin.CommRing in
private theorem round_cycle {m : ℕ} {P : Fin (m + 1) → Prop} (h : ∀ i, P (i + 1) → P i) (j k : Fin (m + 1)) (hj : P j) :
    P k := by
  have key : ∀ (t : ℕ) (i : Fin (m + 1)), P (i + (t : Fin (m + 1))) → P i := by
    intro t
    induction t with
    | zero => intro i hi; simpa using hi
    | succ t ih =>
      intro i hi
      refine ih i (h _ ?_)
      rw [Nat.cast_succ, ← add_assoc] at hi
      exact hi
  refine key (j - k).val k ?_
  rw [Fin.cast_val_eq_self]
  simpa using hj

private theorem mem_fixL {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    {w : Pl K} {J : Subgroup (GL (Fin n) (w.adicCompletion K))} {f : LL μ} :
    f ∈ fixL μ w J ↔ ∀ g ∈ J, rhoL μ w g f = f := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
  constructor
  · intro h g hg
    exact h _ ⟨g, hg, rfl⟩
  · rintro h _ ⟨g, hg, rfl⟩
    exact h g hg

private theorem fix_step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    {σ : E ≃ₐ[F] E} (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) {m n : ℕ} {μ : Measure (normOneGL (K := E) (n := n))} [μ.IsHaarMeasure]
    {θ : Twist μ} (hθ : IsGalTwist σ θ) (p : Pl F) (hs : GM.Split E p) (D : Split (incFin E p) (galFin σ p) m)
    (e : Fin (m + 1) ≃ PlacesOver E p)
    (he : ∀ (b : CompletionsOver E p) i, completionMap p (e i).1 (D.e b i) = b (e i))
    {V : Submodule ℂ (LL μ)} (hV : V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V) (i : Fin (m + 1))
    (h : V ⊓ fixL μ (e (i + 1)).1 (GLnLocal.integralGL ((e (i + 1)).1.adicCompletion E) n) ≠ ⊥) :
    V ⊓ fixL μ (e i).1 (GLnLocal.integralGL ((e i).1.adicCompletion E) n) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨hxV, hxf⟩ := Submodule.mem_inf.1 hx
  have hxf' := mem_fixL.1 hxf
  refine (Submodule.ne_bot_iff _).2 ⟨θ.U x, Submodule.mem_inf.2 ⟨?_, mem_fixL.2 fun k hk => ?_⟩, fun h0 => hx0 ?_⟩
  · rw [← hV]
    exact Submodule.mem_map_of_mem hxV
  · obtain ⟨⟨ε, hε⟩, hint, -⟩ := splitLoc F E p (e i) (hs _) n
    obtain ⟨-, hint', -⟩ := splitLoc F E p (e (i + 1)) (hs _) n
    obtain ⟨g, rfl⟩ : ∃ g, mapGL n (completionMap p (e i).1) g = k := by
      obtain ⟨g, hg⟩ := ε.surjective k
      exact ⟨g, (hε g).symm.trans hg⟩
    have hg := (hint g).1 hk
    have h2 := (twistPerm F E σ hσ m n μ θ hθ).2.1 p D e he i g x
    rw [hxf' _ ((hint' g).2 hg)] at h2
    exact h2.symm
  · have := (Dp.twUnitary E n μ θ).1 x
    rw [h0, norm_zero] at this
    exact norm_eq_zero.1 this.symm

end UpperTheory.ConvolutionTheory.Sph

theorem UpperTheory.ConvolutionTheory.Sph.sphConj :
    UpperTheory.ConvolutionTheory.Sph.SphConj := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ θ hθ V hV w w' hww h
  let u : PlacesOver E (w.under (𝓞 F)) := ⟨w, inferInstance⟩
  have hl : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := by
    rw [hww]
    infer_instance
  let u' : PlacesOver E (w.under (𝓞 F)) := ⟨w', hl⟩
  by_cases hs : GM.Split E (w.under (𝓞 F))
  · obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 := ⟨Module.finrank F E - 1, by have := hp.pos; omega⟩
    obtain ⟨D, e, -, he⟩ := finSplit F E σ hσ m hm _ u hs
    have hstep := fun i => fix_step hσ hθ _ hs D e he hV i
    let Q : PlacesOver E (w.under (𝓞 F)) → Prop := fun a =>
      V ⊓ fixL μ a.1 (GLnLocal.integralGL (a.1.adicCompletion E) n) ≠ ⊥
    obtain ⟨j, hj⟩ := e.surjective u
    obtain ⟨k, hk⟩ := e.surjective u'
    have hQ : Q (e k) := round_cycle (P := fun i => Q (e i)) hstep j k (by
      change Q (e j)
      rw [hj]
      exact h)
    rw [hk] at hQ
    exact hQ
  · have := (T.places F E hp).2.2.2.1 _ hs u u'
    have hw : w' = w := congrArg Subtype.val this
    subst hw
    exact h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Unlinked
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.CBC

theorem UpperTheory.ConvolutionTheory.Sph.unlinked :
    UpperTheory.ConvolutionTheory.Sph.Unlinked := by
  intro K _ _ _ n hn π v B hB a ha b hb hab
  have hB' : (CG.mk π).HasSat v B := hB
  obtain ⟨ν, hν, h⟩ := PositivityTheory.RgJS.unit_exponent_holds K
  obtain ⟨π₀, t, hu, he⟩ := h n (CG.mk π) hn
  have hχ : ((ν t)⁻¹).UnrAt v := fun x hx => by
    change ((ν t).loc v x)⁻¹ = 1
    rw [(hν t).1 v x hx, inv_one]
  have e0 : (CG.mk π).twist (ν t)⁻¹ = π₀ := by
    rw [he, ← CG.twist_mul, mul_inv_cancel, CG.twist_one]
  have hS : π₀.HasSat v (B.map (· * ((ν t)⁻¹).val v)) :=
    e0 ▸ PositivityTheory.RgJS.satake_twist_holds K n (CG.mk π) (ν t)⁻¹ v B hχ hB'
  have hJ := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound K n π₀ hu v _ hS
  have h1 := (hJ _ (Multiset.mem_map_of_mem _ ha)).2
  have h2 := (hJ _ (Multiset.mem_map_of_mem _ hb)).1
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < Ideal.absNorm v.asIdeal := by linarith
  simp only [Units.val_mul, norm_mul] at h1 h2
  have ha' : ‖(a : ℂ)‖ = (Ideal.absNorm v.asIdeal : ℝ) * ‖(b : ℂ)‖ := by
    rw [hab, norm_mul]
    simp
  rw [ha', mul_assoc] at h1
  have h3 : (Ideal.absNorm v.asIdeal : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one (Ideal.absNorm v.asIdeal : ℝ)]
    rw [← Real.rpow_add hq0]
    norm_num
  have h4 := mul_lt_mul_of_pos_left h2 hq0
  rw [h3] at h4
  exact absurd h1 (not_lt.2 h4.le)
end

