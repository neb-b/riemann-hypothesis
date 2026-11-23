module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0532
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0585
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0588
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0587
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0590
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInjectiveOfSubsingleton
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

noncomputable section

namespace GlobalTheory.CompanionTheory.SubEmb

theorem exists_injective_of_subsingleton {G V Y : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y] [Nontrivial Y] (π : Representation ℂ G V) (τ : Representation ℂ G Y)
    (hi : π.IsIrreducible) : ∃ φ : π.IntertwiningMap τ, Function.Injective φ := by
  classical
  haveI := hi
  haveI : Nontrivial V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : Y)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  let φ : π.IntertwiningMap τ :=
    { toFun := fun u => f u • w
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun c a => by simp [mul_smul]
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]
        exact LinearMap.ext fun _ => rfl }
  refine ⟨φ, (Representation.IsIrreducible.injective_or_eq_zero φ).resolve_right fun h => ?_⟩
  have h1 : f v • w = 0 := congrArg (fun ψ : π.IntertwiningMap τ => ψ v) h
  exact (smul_ne_zero hf hw) h1

theorem zero_case {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin 0) k) V) (hi : π.IsIrreducible)
    (x : Fin 0 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = 0) :
    ∃ φ : π.IntertwiningMap (prodIrr x hd), Function.Injective φ := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  have hirr : (prodIrr x hd).IsIrreducible := GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr
  exact exists_injective_of_subsingleton π _ hi

theorem succ_case
    (hstage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t), Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b c : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W')
    (hb : 0 < b) (hρs : IsSmooth ρ) (hρi : ρ.IsIrreducible) (hρc : IsCuspidal ρ)
    (x' : Fin c → IrrGL (k := k)) (hd' : ∑ i, (x' i).1 = a) (hcusp : ∀ i, (x' i).IsCusp)
    (f : σ.IntertwiningMap (prodIrr x' hd')) (hf : Function.Injective f) :
    ∃ (c' : ℕ) (x : Fin c' → IrrGL (k := k)) (hd : ∑ i, (x i).1 = a + b), (∀ i, (x i).IsCusp) ∧
      ∃ Φ : (prod₂ σ ρ).IntertwiningMap (prodIrr x hd), Function.Injective Φ := by
  have hF0 := GlobalTheory.CompanionTheory.ProdInj.prod₂_map_injective k a b _ _ W' σ _ ρ f hf
  obtain ⟨F, hF⟩ := hF0
  let y : Fin 1 → IrrGL (k := k) := fun _ => IrrGL.of ρ hρs hρi
  have hy : ∑ i, (y i).1 = b := by simp [y, IrrGL.of]
  have hy' : ∑ i : Fin 1, (IrrGL.of ρ hρs hρi).1 = (IrrGL.of ρ hρs hρi).1 := by simp
  have e₁0 := nonempty_equiv_prodIrr_one (IrrGL.of ρ hρs hρi) hy'
  obtain ⟨e₁⟩ := e₁0
  have e₂ : ρ.Equiv (prodIrr y hy) := (IrrGL.equivOf ρ hρs hρi).trans e₁
  have hd : ∑ i, (Fin.append x' y i).1 = a + b := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hd', hy]
  have e₃0 := hstage k c 1 a b x' y hd' hy hd
  obtain ⟨e₃⟩ := e₃0
  refine ⟨c + 1, Fin.append x' y, hd, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hcusp i
    · rw [Fin.append_right]; exact IrrGL.isCusp_of.2 ⟨hb, hρc⟩
  · let E := (prod₂Equiv (Representation.Equiv.refl _) e₂).trans e₃
    refine ⟨E.toIntertwiningMap.comp F, ?_⟩
    exact E.toLinearEquiv.injective.comp hF

theorem subEmbedding_of_stage
    (hstage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t), Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h))) :
    Ysupp.SubEmbedding := by
  intro k _ _ _ _ N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ π hs hi
    by_cases hN0 : N = 0
    · subst hN0
      exact ⟨0, Fin.elim0, by simp, fun a => a.elim0, zero_case π hi _ _⟩
    · have hN : 0 < N := Nat.pos_of_ne_zero hN0
      have h0 := GlobalTheory.JacFactor.exists_map_jac₂ k N V π hs hi hN
      obtain ⟨a, b, h, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩ := h0
      subst h
      have h1 := GlobalTheory.CompanionTheory.Frob.exists_injective_of_jac₂ k a b V W W' π σ ρ hs hi φ hφ
      obtain ⟨ψ, hψ⟩ := h1
      have h2 := ih a (by omega) W σ hσs hσi
      obtain ⟨c, x', hd', hcusp, f, hf⟩ := h2
      have h3 := succ_case hstage σ ρ hb hρs hρi hρc x' hd' hcusp f hf
      obtain ⟨c', x, hd, hx, Φ, hΦ⟩ := h3
      exact ⟨c', x, hd, hx, Φ.comp ψ, hΦ.comp hψ⟩

end GlobalTheory.CompanionTheory.SubEmb
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialChineseRemainder
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.EllCRT

private theorem monic_of_mem_normalizedFactors' {K : Type} [Field K] {P q : K[X]}
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors P) : q.Monic := by
  have hq0 : q ≠ 0 := (UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq).ne_zero
  rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
  exact Polynomial.monic_normalize hq0

private theorem span_sup_span_eq_unit_ideal_of_ne_normalizedFactors {K : Type} [Field K] {P p q : K[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors P)
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors P) (hpq : p ≠ q) :
    Ideal.span {p} ⊔ Ideal.span {q} = ⊤ := by
  have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hqi : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
  have hcop : IsCoprime p q := by
    rw [Irreducible.coprime_iff_not_dvd hpi]
    intro hd
    exact hpq (Polynomial.eq_of_monic_of_associated (monic_of_mem_normalizedFactors' hp)
      (monic_of_mem_normalizedFactors' hq) (hpi.associated_of_dvd hqi hd))
  exact (Ideal.sup_eq_top_iff_isCoprime p q).mpr hcop

theorem exists_congr_monic_factors {K : Type} [Field K] {P : K[X]} (hP : P ≠ 0) (t : K[X] → K[X]) :
    ∃ m : K[X], ∀ f : K[X], f.Monic → Irreducible f → f ∣ P → f ∣ m - t f := by
  classical
  let S : Finset K[X] := (UniqueFactorizationMonoid.normalizedFactors P).toFinset
  have hcop : Pairwise (Function.onFun IsCoprime (fun i : S => Ideal.span {(i : K[X])})) := by
    intro i j hij
    show IsCoprime (Ideal.span {(i : K[X])}) (Ideal.span {(j : K[X])})
    exact Ideal.isCoprime_iff_sup_eq.mpr (span_sup_span_eq_unit_ideal_of_ne_normalizedFactors (Multiset.mem_toFinset.mp i.2)
      (Multiset.mem_toFinset.mp j.2) (fun h => hij (Subtype.ext h)))
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun i : S => t i)
  refine ⟨r, fun f hfm hfi hfP => ?_⟩
  obtain ⟨q, hq, hfq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hP hfi hfP
  have hfeq : f = q := Polynomial.eq_of_monic_of_associated hfm (monic_of_mem_normalizedFactors' hq) hfq
  subst hfeq
  have h := hr ⟨f, Multiset.mem_toFinset.mpr hq⟩
  exact Ideal.mem_span_singleton.mp h

private theorem adjoinRoot_exists_mk_eq {R : Type} [CommRing R] {f : R[X]} (x : AdjoinRoot f) :
    ∃ p : R[X], AdjoinRoot.mk f p = x :=
  AdjoinRoot.mk_surjective x

private theorem adjoinRoot_mk_eq_of_selfRecip_val_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    (g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q) {r r' : ℕ} (Q : SelfRecip E r)
    (Q' : SelfRecip E r') (hQ : Q'.1 = Q.1) (l : E[X])
    (hl : (AdjoinRoot.mk Q'.1 l : Fld Q') = g r' Q') :
    (AdjoinRoot.mk Q.1 l : Fld Q) = g r Q := by
  have h1 : Q'.1.natDegree = r' := Q'.2.2.2.1
  have h2 : Q.1.natDegree = r := Q.2.2.2.1
  rw [hQ] at h1
  have hrr : r' = r := h1.symm.trans h2
  subst hrr
  obtain rfl : Q' = Q := Subtype.ext hQ
  exact hl

private theorem exists_polynomial_lift_adjoinRoot_selfRecip {E : Type} [Field E] [NumberField E] [IsCMField E]
    (g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q) :
    ∃ t : E[X] → E[X], ∀ (r : ℕ) (Q : SelfRecip E r),
      (AdjoinRoot.mk Q.1 (t Q.1) : Fld Q) = g r Q := by
  classical
  refine ⟨fun f => if h : ∃ Q' : SelfRecip E f.natDegree, Q'.1 = f then
      (adjoinRoot_exists_mk_eq (f := h.choose.1) (g f.natDegree h.choose)).choose else 0, ?_⟩
  intro r Q
  have hex : ∃ Q' : SelfRecip E Q.1.natDegree, Q'.1 = Q.1 :=
    ⟨⟨Q.1, by rw [Q.2.2.2.1]; exact Q.2⟩, rfl⟩
  dsimp only
  rw [dite_eq_left hex]
  exact adjoinRoot_mk_eq_of_selfRecip_val_eq g Q hex.choose hex.choose_spec _
    (adjoinRoot_exists_mk_eq (f := hex.choose.1) (g Q.1.natDegree hex.choose)).choose_spec

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E),
    γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X],
      ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly →
        (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := by
  intro E _ _ _ n γ₀ _ g
  obtain ⟨t, ht⟩ := exists_polynomial_lift_adjoinRoot_selfRecip g
  obtain ⟨m, hm⟩ := exists_congr_monic_factors (Matrix.charpoly_monic γ₀.val).ne_zero t
  refine ⟨m, fun r Q hQ => ?_⟩
  rw [← ht r Q]
  exact AdjoinRoot.mk_eq_mk.mpr (hm Q.1 Q.2.1 Q.2.2.1 hQ)

end GlobalTheory.CompanionTheory.EllCRT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLocalOrbitalIntegralBounded
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec

set_option maxHeartbeats 1000000 in
theorem finite_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
    ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    ∃ (C : ℝ) (t : F), t ≠ 0 ∧ ∀ c : hermE σ n,
      ‖starLoc (Af F) σ J (psiFin F ψ) μ Q (hermIn (Af F) σ n c)‖ ≤
        C * (delta (t • c).1 : ℝ) ^ (-((M : ℝ) / 2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ hψ μ hμ Q hQ
  classical
  obtain ⟨hA1, hA2, hA3, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  haveI : LocallyCompactSpace (Af F) := hA1
  haveI : SecondCountableTopology (Af F) := hA2
  haveI : T2Space (Af F) := hA3
  obtain ⟨hT1, hT2, hT3, hT4, -, -, -, hT8, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := hT1
  haveI : SecondCountableTopology (Af F ⊗[F] E) := hT3
  haveI : T2Space (Af F ⊗[F] E) := hT4
  haveI : BorelSpace (Fin n → Fin M → Af F ⊗[F] E) := hT8 n M
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (Module.Basis (Fin d) F E) :=
    ⟨_, ⟨Module.finBasis F E⟩⟩
  obtain ⟨N, hN, hNU⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_small F E σ hCM d b n M _ (invariant_mem_nhds hQ.1 hQ.2)
  obtain ⟨hLo, hLc⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_isOpen_isCompact F E σ hCM d b n M N hN
  set L := latN b n M N with hL
  obtain ⟨s, hs⟩ := eq_sum_cosets hQ.2 L hLo (fun x l hl => hNU hl x)
  obtain ⟨D, hD, hDc⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.traceDual_clear_by_integer F
  obtain ⟨t₁, ht₁, htest⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest.rat_test F E σ hCM d b ψ hψ N hN D hD hDc
  obtain ⟨s₂, hs₂, hrat⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem.ratTuple_mem_latN F E d b M J n N hN
  have hs₂F : ((s₂ : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hs₂.ne'
  refine ⟨(∑ a ∈ s, ‖Q a‖) * (μ (L : Set _)).toReal, t₁ * (s₂ : F), mul_ne_zero ht₁ hs₂F, fun c => ?_⟩
  set t : F := t₁ * (s₂ : F) with ht
  set bc := hermIn (Af F) σ n c with hbc
  obtain ⟨hp1, hp2, hp3⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.phaseB_pairB_props F E σ hCM M J n ψ hψ bc
  obtain ⟨hq1, hq2⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd.pairB_add F E σ M J n ψ bc
  set q := phaseB σ J (psiFin F ψ) bc with hq
  set B := pairB σ J (psiFin F ψ) bc with hB
  set S : Set (Fin n → Fin M → Af F ⊗[F] E) := {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1} with hS
  have hLfin : μ (L : Set _) ≠ ⊤ := hLc.measure_lt_top.ne
  have hSL : S ⊆ L := fun y hy => hy.1
  have hSfin : μ S ≠ ⊤ := ne_top_of_le_ne_top hLfin (measure_mono hSL)

  have hbd : ‖starLoc (Af F) σ J (psiFin F ψ) μ Q bc‖ ≤
      (∑ a ∈ s, ‖Q a‖) * √((μ (L : Set _)).toReal * (μ S).toReal) := by
    have hw := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.weyl_sq_compact_open _ μ L hLc hLo q B hp1 hp2 (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd.phaseB_add F E σ hCM M J hJ n ψ hψ bc) hq1 hq2
    exact _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound.twisted_integral_finite_coset_combination_bound _ μ L hLc hLo q hp1 hp2 _ hw Q s hs

  have hSm : MeasurableSet S := by
    have e : S = (L : Set _) ∩ ⋂ l ∈ L, (B l) ⁻¹' {1} := by
      ext y
      simp [hS]
    have hcl : IsClosed S := by
      rw [e]
      have hLcl : IsClosed (L : Set (Fin n → Fin M → Af F ⊗[F] E)) := hLc.isClosed
      exact hLcl.inter (isClosed_biInter fun l _ => isClosed_singleton.preimage (hp3 l))
    exact hcl.measurableSet

  have hdiff : ∀ u ∈ S, ∀ v ∈ S, ∀ l ∈ L, B l (v - u) = 1 := by
    intro u hu v hv l hl
    have h := hq2 l u (v - u)
    rw [add_sub_cancel, hv.2 l hl, hu.2 l hl, one_mul] at h
    exact h.symm
  set c' : Matrix (Fin n) (Fin n) E := ((t • c).1).map σ with hc'
  have hδ : delta c' = delta (t • c).1 := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map F E σ n _
  have hδ0 : delta c' ≠ 0 := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin.delta_pos_index E n c'
  haveI hfin : Finite ((Fin n → 𝓞 E) ⧸ Kc c') := Nat.finite_of_card_ne_zero hδ0
  haveI := Fintype.ofFinite ((Fin n → 𝓞 E) ⧸ Kc c')

  have hcount : ((delta c' ^ M : ℕ) : ℝ≥0∞) * μ S ≤ μ (L : Set _) := by
    have h := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Count.card_mul_measure_le_of_disjoint_translates _ μ L S hSm hSL (Fin M → (Fin n → 𝓞 E) ⧸ Kc c')
      (fun φ => ratTuple J s₂ fun i => (φ i).out) (fun φ => hrat _) ?_
    · have hc : Fintype.card (Fin M → (Fin n → 𝓞 E) ⧸ Kc c') = delta c' ^ M := by
        rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]
        rfl
      rwa [hc] at h
    · intro φ φ' u v hu hv huv
      funext i₀
      have hρ : ratTuple (F := F) J s₂ (fun i => (φ i).out - (φ' i).out) = ratTuple J s₂ (fun i => (φ i).out) - ratTuple J s₂ (fun i => (φ' i).out) := by
        funext a j
        simp only [ratTuple, Pi.sub_apply, map_sub]
        rw [show (fun i => algebraMap (𝓞 E) E ((φ i).out a) - algebraMap (𝓞 E) E ((φ' i).out a)) =
          (fun i => algebraMap (𝓞 E) E ((φ i).out a)) - (fun i => algebraMap (𝓞 E) E ((φ' i).out a)) from rfl,
          Matrix.mulVec_sub]
        simp [mul_sub]
      have hmem : ∀ l ∈ L, B l (ratTuple J s₂ fun i => (φ i).out - (φ' i).out) = 1 := by
        intro l hl
        have : ratTuple (F := F) J s₂ (fun i => (φ i).out - (φ' i).out) = v - u := by
          rw [hρ, sub_eq_sub_iff_add_eq_add, add_comm v]
          exact huv
        rw [this]
        exact hdiff u hu v hv l hl
      have hK : (φ i₀).out - (φ' i₀).out ∈ Kc c' := by
        intro c₀
        have hx := htest ((s₂ : E) * ∑ a, c.1 a c₀ *
          algebraMap (𝓞 E) E (((φ i₀).out - (φ' i₀).out) a)) (fun x hx => by
            have h1 := hmem (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (by
              intro a i
              by_cases h : a = c₀ ∧ i = i₀
              · simpa [h] using hx
              · simp only [h, if_false]
                exact (latN b n M N).zero_mem a i)
            rw [hB, hbc, _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle.pair_single F E σ M J hJ n (psiFin F ψ) c c₀ i₀ x s₂ _] at h1
            exact h1)
        obtain ⟨o, ho⟩ := hx
        refine ⟨o, ?_⟩
        rw [ho]
        simp only [Matrix.mulVec, dotProduct, hc', Matrix.map_apply, Finset.smul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        have h3 : σ (c.1 c₀ a) = c.1 a c₀ := c.2 a c₀
        rw [show σ ((t • c).1 c₀ a) = t • c.1 a c₀ from by
          show σ (t • c.1 c₀ a) = _
          rw [Algebra.smul_def, map_mul, AlgHom.commutes, h3, ← Algebra.smul_def]]
        simp only [ht, Algebra.smul_def, map_mul, map_natCast]
        ring
      have h5 : (QuotientAddGroup.mk (φ' i₀).out : (Fin n → 𝓞 E) ⧸ Kc c') = QuotientAddGroup.mk (φ i₀).out :=
        QuotientAddGroup.eq.2 (by rw [neg_add_eq_sub]; exact hK)
      rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h5
      exact h5.symm

  have hδpos : (0 : ℝ) < (delta c' : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hδ0)
  have hreal : (delta c' : ℝ) ^ M * (μ S).toReal ≤ (μ (L : Set _)).toReal := by
    have h := ENNReal.toReal_mono hLfin hcount
    rw [ENNReal.toReal_mul] at h
    simpa using h
  rw [← hδ]
  set A := (μ (L : Set _)).toReal with hA
  set Sr := (μ S).toReal with hSr
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ Sr := ENNReal.toReal_nonneg
  set w : ℝ := (delta c' : ℝ) ^ (-((M : ℝ) / 2)) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hδpos.le _
  have hw2 : w ^ 2 * (delta c' : ℝ) ^ M = 1 := by
    rw [hw, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hδpos.le, ← Real.rpow_natCast _ M, ← Real.rpow_add hδpos]
    have : -((M : ℝ) / 2) * ((2 : ℕ) : ℝ) + (M : ℝ) = 0 := by push_cast; ring
    rw [this, Real.rpow_zero]
  have hsq : √(A * Sr) ≤ A * w := by
    refine Real.sqrt_le_iff.2 ⟨mul_nonneg hA0 hw0, ?_⟩
    have h1 : Sr = w ^ 2 * ((delta c' : ℝ) ^ M * Sr) := by rw [← mul_assoc, hw2, one_mul]
    have h2 : Sr ≤ w ^ 2 * A := by
      rw [h1]
      exact mul_le_mul_of_nonneg_left hreal (sq_nonneg _)
    calc A * Sr ≤ A * (w ^ 2 * A) := mul_le_mul_of_nonneg_left h2 hA0
      _ = (A * w) ^ 2 := by ring
  calc _ ≤ (∑ a ∈ s, ‖Q a‖) * √(A * Sr) := hbd
    _ ≤ (∑ a ∈ s, ‖Q a‖) * (A * w) :=
        mul_le_mul_of_nonneg_left hsq (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteNonsplitSignPlaces
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section
namespace GlobalTheory.CompanionTheory.FinSign

theorem ordL_eq_zero_of_v_eq_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L}
    (h : Valued.v x = 1) : ordL x = 0 := by
  unfold ordL
  rw [dite_eq_right (by rw [h]; exact one_ne_zero)]
  simp [h]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := by
  intro E _ _ _ hU n γ₀ H₀ _ _ hpos P₁
  obtain ⟨hd0, -⟩ := gramOn_det_totallyPositive_of_posDef H₀ hpos
    (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))
  refine (GlobalTheory.QNorm.finite_valuation_ne_one E (Units.mk0 _ hd0)).subset ?_
  rintro w ⟨hw, hs⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0]
  intro h1
  apply hs
  unfold sgnOn
  have hv : Valued.v (algebraMap E (w.adicCompletion E)
      (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H₀
        (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))).det) = 1 :=
    (w.valuedAdicCompletion_eq_valuation' _).trans h1
  rw [aeval_map_mat, _root_.GlobalTheory.UnitaryClasses.BaseChangeSign.main E hU w hw n H₀ (aeval γ₀.val P₁), ordL_eq_zero_of_v_eq_one hv]
  simp

end GlobalTheory.CompanionTheory.FinSign
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormOne
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.HodgeFormUnit

theorem gForm_one {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) :
    CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0 = oneOm K (Sec q ⊤) := by
  apply Subtype.ext
  simp [CrystallineSemistableComparison.Onto.form, oneOm]

theorem e_oneH {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0) (h : CrystallineSemistableComparison.Om.L2.IsOmT q 0 e) :
    e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  let Λ : CrystallineSemistableComparison.Om.L2.LiftsT q :=
    { v := fun T g => Function.surjInv Ideal.Quotient.mk_surjective
        (CrystallineSemistableComparison.Pb.ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (CrystallineSemistableComparison.Om.L2.inTop q T) g)
      hv := fun T g => Function.surjInv_eq _ _ }
  obtain ⟨f, hf, hc, hz⟩ := h 1 Fin.elim0 Λ
  have hf' : f = (CrystallineSemistableComparison.Pb.toSq (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (0 : ℕ)) (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (((0 : ℕ) : ℤ) + 1))
      fun T => T.pdPow_zero).pullC 0 (fun s => (1 : (CrystallineSemistableComparison.Pb.thA (CrystallineSemistableComparison.smFun X q)).obj (s.obj (Fin.last 0)))) := by
    funext s
    apply Subtype.ext
    refine (hz s).trans ?_
    have hv : (Λ.form 1 Fin.elim0 s : (s.obj (Fin.last 0)).B) = Λ.v _ 1 := by
      simp [CrystallineSemistableComparison.Om.L2.LiftsT.form]
    have hJ : Λ.v (s.obj (Fin.last 0)) 1 - 1 ∈ (s.obj (Fin.last 0)).J :=
      Ideal.Quotient.eq.1 ((Λ.hv _ 1).trans ((map_one _).trans (map_one _).symm))
    refine Ideal.Quotient.eq.2 ?_
    change Λ.form 1 Fin.elim0 s - 1 ∈ (s.obj (Fin.last 0)).pdPow 1
    rw [hv]
    exact (s.obj (Fin.last 0)).J_le_pdPow_one hJ
  have h1 : CrystallineSemistableComparison.HT.oneH q = e.symm (CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0) := by
    refine Eq.trans ?_ hc.symm
    exact congrArg Submodule.Quotient.mk (Subtype.ext hf'.symm)
  rw [h1, LinearEquiv.apply_symm_apply, gForm_one]

end GlobalTheory.CompanionTheory.HodgeFormUnit
end

