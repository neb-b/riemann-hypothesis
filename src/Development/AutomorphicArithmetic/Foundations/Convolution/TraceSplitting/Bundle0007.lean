module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FamParts
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Cbcc
section
open NumberField in
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

open NumberField in
theorem UpperTheory.ConvolutionTheory.T.cbcc :
    UpperTheory.ConvolutionTheory.T.Places → UpperTheory.ConvolutionTheory.T.LiftStep → UpperTheory.ConvolutionTheory.T.LiftAll → UpperTheory.ConvolutionTheory.T.DescStep → UpperTheory.ConvolutionTheory.T.SplitStrong → UpperTheory.V.Z.Bc.CBCc := by
  intro hPl hLS hLA hDS hSS K M _ _ _ _ _ _ hp hK n hn
  haveI := hK
  haveI hM : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  refine ⟨fun π => ?_, fun P hP => ?_, fun π P _ hw => UpperTheory.ConvolutionTheory.R.fibre_holds K M hp n hn π P hw⟩
  · rcases π with @⟨_, π⟩ | @⟨hR, π⟩
    swap
    · exact (not_both K hR hK).elim
    rcases hLS K M σ hσ hp n hn (fun m hm _ => hLA K M σ hσ hp m hm) π with ⟨ι, _, m, Q, hm, h2, hw⟩ | ⟨P, ⟨h1, h2⟩, h3⟩
    · obtain ⟨η, hη, e⟩ := UpperTheory.ConvolutionTheory.R.twoParts_holds K M hp n _ ι m Q hn hm h2 hw
      exact Or.inl ⟨η, hη, Quotient.exact e⟩
    · exact Or.inr ⟨.cx P, h1, fun τ m h => (h2 τ m).1 h, hSS K M σ hσ hp n hn π P h3 h1⟩
  · rcases P with @⟨_, P⟩ | @⟨hR, P⟩
    swap
    · exact (not_both M hR hM).elim
    obtain ⟨hinf, -, hne, -⟩ := hPl K M hp
    obtain ⟨v, hv⟩ := hinf.nonempty
    obtain ⟨w⟩ := hne v
    obtain ⟨π, ⟨h1, h2⟩, -⟩ := hDS K M σ hσ hp n hn P hP v w hv
    exact ⟨.cx π, h1, fun τ m h => (h2 τ m).2 h, hSS K M σ hσ hp n hn π P hP h1⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.DescStep
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.T Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.CBC

private theorem occ_basic {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) :
    (∃ σ, Occurs μ V w σ) ∧ (∀ σ σ', Occurs μ V w σ → Occurs μ V w σ' → Nonempty (σ.ρ.Equiv σ'.ρ)) := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  have h := occursBasics K n μ V w Measure.haar hV
  exact ⟨h.1, h.2.1⟩

private theorem loc_iff {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (μ : Measure (normOneGL (K := E) (n := n)))
    [μ.IsHaarMeasure] (π : CuspSub E n) (V : Submodule ℂ (LL μ)) (h : Dp.Carries μ π V) (w : Pl E) (σ : SmIrr (Gw n w)) :
    (Cusp.cx π).locComp w σ ↔ Occurs μ V w σ :=
  (Dp.locIff E n μ π V h w σ).trans (occursIff E n μ V h.summand w σ).symm

private theorem locIso_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {v : Pl F} (w : PlacesOver E v) {τ τ₁ : SmIrr (Gw n v)} {τ' τ₁' : SmIrr (Gw n w.1)} (a : τ₁.ρ.Equiv τ.ρ)
    (b : τ'.ρ.Equiv τ₁'.ρ) (h : LocIso w τ τ') : LocIso w τ₁ τ₁' := by
  obtain ⟨e, he⟩ := h
  refine ⟨a.toLinearEquiv.trans (e.trans b.toLinearEquiv), fun g x => ?_⟩
  have ha : a.toLinearEquiv (τ₁.ρ g x) = τ.ρ g (a.toLinearEquiv x) :=
    Representation.IntertwiningMap.isIntertwining _ _ a.toIntertwiningMap g x
  have hb : ∀ g y, b.toLinearEquiv (τ'.ρ g y) = τ₁'.ρ g (b.toLinearEquiv y) := fun g y =>
    Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap g y
  simp only [LinearEquiv.trans_apply]
  rw [ha, he, hb]

theorem UpperTheory.ConvolutionTheory.T.descStep :
    UpperTheory.ConvolutionTheory.T.CoreDesc → UpperTheory.ConvolutionTheory.T.LiftAll → UpperTheory.ConvolutionTheory.T.DescStep := by
  intro hD hL F E _ _ _ _ _ _ _ _ σ hσ hp n hn P hP v w hv
  let μE : Measure (normOneGL (K := E) (n := n)) := Measure.haar
  let μF : Measure (normOneGL (K := F) (n := n)) := Measure.haar
  obtain ⟨χ', hχ', V, hV⟩ := Dp.exTwist E n μE P hn
  obtain ⟨s, hs'⟩ := hχ'
  obtain ⟨hex, htw⟩ := powTwist F E
  obtain ⟨χ, hs⟩ := (hex s).1
  obtain ⟨hi, hi', h1⟩ := htw s χ χ' hs hs'
  obtain ⟨-, hPP, -, hconj, -⟩ := h1 n hn
  obtain ⟨-, -, h2⟩ := htw (-s) χ⁻¹ χ'⁻¹ hi hi'
  obtain ⟨-, -, hlift, -, hloc⟩ := h2 n hn
  obtain ⟨-, hAt, hcl, -, hnp, θ, hθ, hst⟩ := carryLift F E σ hσ hp n hn μE μF
  obtain ⟨Λ, t, hΛ⟩ := hAt V hV.summand
  have hstab := (hst _ V hV).1 fun g => hconj P _ (hP g)
  have hoff : OffAll F n Λ t := by
    by_contra hc
    exact hnp _ V Λ t hV hΛ (famParts F E σ hσ hp n hn (fun m hm _ => hL F E σ hσ hp m hm) Λ t hc)
  obtain ⟨⟨τ', hτ'⟩, huE⟩ := occ_basic μE V hV.summand w.1
  obtain ⟨V₀, Λ₀, t₀, hV₀, hAt₀, hΛ₀, ht₀, τ, hτ, hiso⟩ :=
    hD F E σ hσ hp n hn μE μF θ hθ V Λ t hV.summand hstab hΛ hoff v w hv τ' hτ'
  obtain ⟨π, hπ, -⟩ := Dp.exCusp F n μF V₀ hV₀
  obtain ⟨-, huF⟩ := occ_basic μF V₀ hV₀ v
  have hl := hlift π _ (hcl π _ V₀ V Λ₀ t₀ Λ t hπ hV hAt₀ hΛ hΛ₀ ht₀)
  have hl2 := hloc π (P.twist χ') v w (hv w) fun τ₁ τ₁' h₁ h₁' => by
    obtain ⟨a⟩ := huF τ₁ τ ((loc_iff μF π V₀ hπ v τ₁).1 h₁) hτ
    obtain ⟨b⟩ := huE τ' τ₁' hτ' ((loc_iff μE _ V hV w.1 τ₁').1 h₁')
    exact locIso_congr w a b hiso
  rw [hPP] at hl hl2
  exact ⟨π.twist χ⁻¹, hl, hl2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep
section
open MeasureTheory NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T

private theorem pow_loc {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]
  exact h _

private theorem pow_val {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) : χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = (normV v : ℂ) ^ (-s) := by
  refine ⟨fun x hx => Units.ext ?_, ?_⟩
  · have hx' : Valued.v (x : v.adicCompletion K) = 1 := hx
    rw [pow_loc h, FinitePlace.norm_def, hx']
    simp
  · have hx' : Valued.v ((atFin v (unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
      unif_spec v
    refine (pow_loc h v (atFin v (unif v))).trans ?_
    rw [FinitePlace.norm_def, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    have e' : normV v = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    rw [WithZero.log_exp, e', zpow_neg_one, NNReal.coe_inv, Complex.ofReal_inv, NNReal.coe_natCast, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]

private theorem bc_twist {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [_root_.NumberField.IsTotallyComplex K]
    [_root_.NumberField.IsTotallyComplex M] {ν : HChar K} {ν' : HChar M} {z : ℂ} (hν : IsPow ν z) (hν' : IsPow ν' z) {n : ℕ} (π : CG K n)
    {ι : Type} [Fintype ι] {m : ι → ℕ} (P : ∀ i, CG M (m i)) (h : WeakBC π.HasSat (R.sumSat P)) :
    WeakBC (π.twist ν).HasSat (R.sumSat fun i => (P i).twist ν') := by
  refine Filter.Eventually.mono h fun w hw f hf => ?_
  obtain ⟨B, hB, B', hB', e⟩ := hw f hf
  have hv : ν'.val w = ν.val (w.under (𝓞 K)) ^ f := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, (pow_val hν _).2, (pow_val hν' _).2, hf, Nat.cast_pow, ← Complex.cpow_nat_mul,
      Complex.natCast_cpow_natCast_mul]
  refine ⟨_, satake_twist_holds K n π ν _ B (pow_val hν _).1 hB, fun i => (B' i).map (· * ν'.val w),
    fun i => satake_twist_holds M _ (P i) ν' w _ (pow_val hν' _).1 (hB' i), ?_⟩
  refine Eq.trans ?_ (map_sum (Multiset.mapAddMonoidHom (· * ν'.val w)) B' Finset.univ)
  rw [← e]
  simp [Multiset.map_map, hv, mul_pow]

theorem UpperTheory.ConvolutionTheory.T.liftStep :
    UpperTheory.ConvolutionTheory.T.CoreLift → UpperTheory.ConvolutionTheory.T.LiftStep := by
  intro hC F E _ _ _ _ _ _ _ _ σ hσ hp n hn hlow π
  let μF : Measure (normOneGL (K := F) (n := n)) := Measure.haar
  let μE : Measure (normOneGL (K := E) (n := n)) := Measure.haar
  have htw : ∃ χ : HChar F, (∃ s : ℂ, IsPow χ s) ∧
      ∃ V, Dp.Carries μF (π.twist χ) V := Dp.exTwist F n μF π hn
  obtain ⟨χ, ⟨s, hχ⟩, V, hV⟩ := htw
  obtain ⟨hex, hpw⟩ := powTwist F E
  obtain ⟨χ', hχ'⟩ := (hex s).2
  obtain ⟨hi, hi', hrest⟩ := hpw s χ χ' hχ hχ'
  have hback := (hrest n hn).1 π
  obtain ⟨-, -, hrest'⟩ := hpw (-s) χ⁻¹ χ'⁻¹ hi hi'
  obtain ⟨-, -, hL, hCj, -⟩ := hrest' n hn
  obtain ⟨c1, -, c3, c4, -, θ, hθ, c6⟩ := carryLift F E σ hσ hp n hn μE μF
  obtain ⟨Λ, t, hAt⟩ := c1 V hV.summand
  by_cases hO : OffAll F n (bcInf (K := E) Λ) (bcSat t)
  · obtain ⟨V', hV', hst, hAt'⟩ := hC F E σ hσ hp n hn μE μF θ hθ V Λ t hV.summand hAt hO
    obtain ⟨P, hP, -⟩ := Dp.exCusp E n μE V' hV'
    have h1 := hL _ _ (c3 _ P V V' Λ t _ _ hV hP hAt hAt' rfl (Filter.Eventually.of_forall fun _ => rfl))
    rw [hback] at h1
    exact Or.inr ⟨_, h1, fun g => hCj _ _ ((c6 P V' hP).2 hst g)⟩
  · obtain ⟨ι, _, m, Q, hm, hι, hW⟩ := c4 _ V Λ t hV hAt (famParts F E σ hσ hp n hn hlow _ _ hO)
    refine Or.inl ⟨ι, inferInstance, m, fun i => (Q i).twist χ'⁻¹, hm, hι, ?_⟩
    have h1 := bc_twist hi hi' _ Q hW
    have e : (CG.mk (π.twist χ)).twist χ⁻¹ = CG.mk π := congrArg CG.mk hback
    rwa [e] at h1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplitAlt
section
noncomputable section

open scoped GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC UpperTheory.ConvolutionTheory.T

namespace UpperTheory.ConvolutionTheory.T.Ncs

private theorem loc_one_of {L : Type} [Field L] [NumberField L] (ψ : HChar L) (w : HeightOneSpectrum (𝓞 L))
    (hu : ψ.UnrAt w) (hv : ψ.val w = 1) (x : (w.adicCompletion L)ˣ) : ψ.loc w x = 1 := by
  refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.loc w) (fun y hy => ?_) x
  have h2 := unif_spec w
  have h3 := hu (y * (atFin w (unif w))⁻¹) (by
    unfold IsUnitAt
    unfold IsUnifAt at hy h2
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3.trans hv

private theorem norm_surj {A B : Type} [Field A] [Field B] [Algebra A B] (hs : Function.Surjective (algebraMap A B))
    (x : Aˣ) : ∃ y : Bˣ, GroundTheory.LocalField.normUnits A B y = x := by
  have hfr : Module.finrank A B = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap A B) ⟨(algebraMap A B).injective, hs⟩).finrank_eq
    simpa using this.symm
  refine ⟨Units.map (algebraMap A B).toMonoidHom x, Units.ext ?_⟩
  rw [GroundTheory.LocalField.coe_normUnits]
  change Algebra.norm A (algebraMap A B x) = x
  rw [Algebra.norm_algebraMap, hfr, pow_one]

private theorem loc_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (η : HChar F) (hη : IsNormChar E η) (v : HeightOneSpectrum (𝓞 F)) (hs : GM.Split E v)
    (x : (v.adicCompletion F)ˣ) : η.loc v x = 1 := by
  let ψ : HChar E := ⟨η.1.comp (GroundTheory.Global.ideleNorm F E), η.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg η.1 (GroundTheory.Global.ideleNorm_diagonal (K := F) k)).trans (η.2.2 _)⟩
  have hψ : ∀ x, ψ.1 x = η.1 (GroundTheory.Global.ideleNorm F E x) := fun _ => rfl
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ψ.UnrAt w ∧ ψ.val w = 1 := by
    filter_upwards [hη.2.2, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))] with w h1 h2
    have hf := GlobalTheory.ArtinTransport.normV_eq_pow (E := F) (E' := E) (v := w.under (𝓞 F)) (w := w) rfl
    obtain ⟨a, b⟩ := GlobalTheory.NormValGen.unrAt_val_of_comp_norm F E η ψ hψ w _ hf h2
    exact ⟨a, b.trans (h1 _ hf)⟩
  have h1 : ψ.1 = 1 := GlobalTheory.FrobDense.eq_one_of_away ψ.1 ψ.2.1 ψ.2.2 (Filter.eventually_cofinite.1 hev).toFinset
    fun w hw y => by
      have := not_not.1 (fun h => hw ((Set.Finite.mem_toFinset _).2 h))
      exact loc_one_of ψ w this.1 this.2 y
  obtain ⟨⟨w, hw⟩⟩ := GroundTheory.Global.nonempty_placesOver E v
  obtain rfl : GroundTheory.Global.AdeleBaseChange.below F w = v := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w v).2 hw
  haveI := hw
  have hsurj := hs ⟨w, hw⟩
  obtain ⟨y, hn⟩ := norm_surj (A := (GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (B := w.adicCompletion E) hsurj x
  have h2 := GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w y
  rw [hn] at h2
  have h3 : η.1 (GroundTheory.Global.ideleNorm F E (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)) = 1 := by
    rw [← hψ, h1]; rfl
  rw [h2] at h3
  exact h3

private theorem twist_inter {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] {n : ℕ} (π : CuspSub F n) (η : HChar F)
    (v : HeightOneSpectrum (𝓞 F)) (h : ∀ x, η.loc v x = 1) (g : GL (Fin n) (v.adicCompletion F)) (φ : π.V) :
    (π.twist η).locRep v g (π.toTwist η φ) = π.toTwist η (π.locRep v g φ) := by
  have hd : CuspSub.locDet n η v g = 1 := h _
  rw [CuspSub.locRep_eq, CuspSub.op_toTwist, ← CuspSub.locRep_eq]
  simp only [opAdd, zero_smul, add_zero]
  have e : opMul η (Op.fin (locGL F n v g)) = 1 := (CuspSub.chiDet_locGL η v g).trans hd
  rw [e, Units.val_one, one_smul]

end UpperTheory.ConvolutionTheory.T.Ncs

open UpperTheory.ConvolutionTheory.T.Ncs in
theorem UpperTheory.ConvolutionTheory.T.normCharSplit :
    UpperTheory.ConvolutionTheory.T.NormCharSplit := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n _ η hη v hs π τ
  have hl := loc_eq_one η hη v hs
  change (π.twist η).IsLocComp v τ ↔ π.IsLocComp v τ
  constructor
  · rintro ⟨f, h0, hf⟩
    refine ⟨(π.toTwist η).symm.toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun x => (π.toTwist η).symm.injective ?_),
      fun g x => (π.toTwist η).injective ?_⟩
    · simpa only [LinearMap.comp_apply, LinearMap.zero_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_zero] using LinearMap.congr_fun h x
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← twist_inter π η v hl, LinearEquiv.apply_symm_apply, hf]
  · rintro ⟨f, h0, hf⟩
    refine ⟨(π.toTwist η).toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun x => (π.toTwist η).injective ?_),
      fun g x => ?_⟩
    · simpa only [LinearMap.comp_apply, LinearMap.zero_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_zero] using LinearMap.congr_fun h x
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [twist_inter π η v hl, hf]
end
end

