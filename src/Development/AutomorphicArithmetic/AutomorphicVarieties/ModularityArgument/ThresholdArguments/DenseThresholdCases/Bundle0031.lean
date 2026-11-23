module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.RecSph
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.LinkTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwoRuns
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrSeedPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PsiCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.CcEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DownQuadS
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol UpperTheory.V.Z.Bc
private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)
private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem isoOfFrobOne (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r)
    (hr' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r')
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) : RepIso r r' := by
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, hd, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv hd
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩
private theorem normV_one {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) (h : w.asIdeal.inertiaDeg ℤ = 1) : normV w = normV (w.under (𝓞 K)) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [Ideal.inertiaDeg_tower (R := ℤ) (w.under (𝓞 K)).asIdeal w.asIdeal] at h
  rw [normV_under (K := K) w, Nat.eq_one_of_mul_eq_one_left h, pow_one]
theorem UpperTheory.V.Z.Bc.automorphic_rank_two_of_automorphic_restrict_of_finite_det :
    ∀ (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : DescS) (hG : GapTwo) (hR : ExRTwo) (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra ℚ Ω]
      [Algebra M Ω] [IsScalarTower ℚ M Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure M Ω] (hp : Module.finrank ℚ M = 2) (hM : IsCMField M)
      (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hr : Continuous r)
      (hirr : IsIrr (r.comp (resG ℚ M Ω))) (hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (r s) ^ N = 1), IsAut ι (r.comp (resG ℚ M Ω)) → IsAut ι r := by
  intro H cyc hG hR M Ω _ _ _ _ _ _ _ _ hp hM l _ ι r hr hirr hfin
  haveI : Algebra.IsQuadraticExtension ℚ M := ⟨hp⟩
  have hK : IsTotallyReal ℚ := inferInstance
  have hdown := cyc M hp inferInstance
  have hss : IsSSRep (r.comp (resG ℚ M Ω)) := (Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirr
  have hirr' : IsIrr r := (Bc.irrBasic.1 _ _ _ 2 r).1 _ hirr
  have hcont := continuous_restrictScalarsHom ℚ M Ω
  rintro ⟨sat', inf', hc', hreg', hatt'⟩
  have hgap : Gap2 inf' := by
    rcases hc' with ⟨_, P, rfl, rfl⟩ | ⟨hR', -⟩
    · refine hG M Ω l ι _ P ((GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_) hatt' (hfin.imp fun N h => ⟨h.1, fun s => h.2 _⟩)
      obtain ⟨m, hm, h⟩ := hreg' τ
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) hm]
      exact h
    · exact (not_both M hR' inferInstance).elim
  obtain ⟨sat, inf, hc, hbc, hinf⟩ := hdown sat' inf' hc' hreg' hgap (UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic UpperTheory.frobenius_conj_of_galois_conjugate_places UpperTheory.hecke_eigenvalue_basic_properties ℚ M Ω l ι 2 r sat' hatt')
  have hreg : RegInf 2 inf := fun τ => by
    obtain ⟨m, hm, h⟩ := hreg' (ComplexEmbedding.lift M τ)
    have := hinf _ m hm
    rw [ComplexEmbedding.lift_comp_algebraMap] at this
    exact ⟨m, this, h⟩
  obtain ⟨r₁, hr₁, hatt₁⟩ := (show ∃ r₁ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous r₁ ∧ AttachedSys ι r₁ sat by
    rcases hc with ⟨hC, -⟩ | ⟨hR', π, rfl, rfl⟩
    · exact (not_both ℚ hK hC).elim
    · obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt H.toClassicalTheorems ℚ π
      refine hR ℚ Ω l ι π ω (fun v => ?_) ⟨fun v v' => by rw [Subsingleton.elim v v'], _root_.UpperTheory.V.Sd.Wc.polGL2_alt H.toClassicalTheorems ℚ π ω hω⟩
      have := hreg v.embedding
      simpa only [InfinitePlace.mk_embedding] using this)
  have hN := (UpperTheory.galois_representation_image_spec ℚ M Ω).1
  have hss₁ := UpperTheory.semisimpleModule_restriction_to_normal_subgroup _ _ _ 2 r₁ (resG ℚ M Ω) hN hatt₁.1
  have hiso : RepIso (r₁.comp (resG ℚ M Ω)) (r.comp (resG ℚ M Ω)) := by
    refine isoOfFrobOne M Ω l ι 2 _ _ (hr₁.comp hcont) (hr.comp hcont) hss₁ hss ?_
    filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under ℚ M).eventually hatt₁.2, hatt'.2]
      with w h1 ⟨B₁, hB₁, h₁⟩ ⟨B', hB', h'⟩ hd
    have hn := normV_one (K := ℚ) w hd
    obtain ⟨B, hB, hP⟩ := h1 hn
    obtain rfl := cusp_unique hc _ _ _ hB hB₁
    obtain rfl := cusp_unique hc' _ _ _ hP hB'
    have h3 := (UpperTheory.frobenius_power_compatibility ℚ M Ω l ι w 1 (by rw [pow_one]; exact hn)).1 2 r₁ _ h₁
    simp only [pow_one, Multiset.map_id'] at h3
    rw [← hn] at h3
    exact ⟨_, h3, h'⟩
  obtain ⟨δ, hδ, hiso'⟩ := UpperTheory.schur_extension _ _ _ 2 r r₁ (resG ℚ M Ω) hN hirr hiso
  have hF := UpperTheory.finiteCharacter_of_algebraic_cyclotomic (_root_.UpperTheory.V.Af.algOfCyc_s H)
  obtain ⟨sat₂, inf₂, hc₂, hreg₂, hatt₂⟩ := _root_.UpperTheory.V.Af.twist_invariance_automorphic H ℚ Ω l ι 2 r₁ δ ⟨sat, inf, hc, hreg, hatt₁⟩
    (hF.1 ℚ Ω l ι δ (hF.2 ℚ M Ω l δ hδ))
  exact ⟨sat₂, inf₂, hc₂, hreg₂, (Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirr',
    hatt₂.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso hiso'⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfRoot
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af
open UpperTheory.V UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem exists_unr {ξ : kˣ →* ℂˣ} (h : IsUnram ξ) : ∃ a : ℂˣ, ξ = unrChar k a := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  exact ⟨_, eq_unrChar h hϖ⟩
private theorem unr_eq {a b : ℂˣ} (h : (a : ℂ) = (resCard k : ℂ) * b) : unrChar k b = unrChar k a * absPow k 1 := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  have hU : IsUnram (unrChar k a * absPow k 1) := fun u hu => by
    rw [MonoidHom.mul_apply, isUnram_unrChar k a u hu, isUnram_absPow k 1 u hu, one_mul]
  rw [eq_unrChar hU hϖ]
  congr 1
  refine Units.ext ?_
  simp only [MonoidHom.mul_apply, Units.val_mul]
  rw [unrChar_uniformizer k a hϖ, val_absPow, Complex.cpow_one, h]
  have hn : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one hϖ]; simp
  have hq : (resCard k : ℂ) ≠ 0 := by
    have : (1 : ℝ) < resCard k := by exact_mod_cast one_lt_resCard (k := k)
    exact_mod_cast (by positivity : (resCard k : ℝ) ≠ 0)
  rw [hn]
  push_cast
  field_simp
end Loc
section WD
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem unr_of_level {n : ℕ} {x : WD h} (hL : IsLevelWD 1 n x) : x.unr := by
  obtain ⟨χ, b, hχ, e, hN, hb⟩ := hL
  have h1 : ((1 : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    rw [Nat.cast_one]
    exact fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  rw [← e, WD.unr_mk]
  refine ⟨hN, fun s => ?_⟩
  rw [hb s]
  simp [fun i => hχ i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char E Ω w A h 1 h1 s s.2), Module.End.one_eq_id]
private theorem eq_one_of_root {x : WD h} (hu : x.unr) (t : Ine (F := E) A) {z : ℂ}
    (hz : (x.charPol (ineIncl h t)).IsRoot z) : z = 1 := by
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.unr_mk] at hu
  rw [WD.charPol_mk, hu.2 t, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hz
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have h3 := hv.apply_eq_smul
  exact smul_left_injective ℂ hv.2 (by simpa using h3.symm)
end WD
end UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity
open UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity in
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.recSph_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → RecSph := by
  intro _ E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ hP hlev
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hxu : (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).unr := by
    have h0 := unr_of_level hlev
    rwa [algNorm, L.nu, WD.unr_tw] at h0
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hun : ∀ i, IsUnram (ξ i) := fun i u hu1 => by
    obtain ⟨g, rfl⟩ := ha.surj u
    have h0 : deg g = 0 := by
      have h1 := ha.ord_eq g
      rw [ord_eq_zero_iff.2 hu1] at h1
      omega
    have hr : ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol (ineIncl h ⟨g, deg_eq_zero_iff.1 h0⟩)).IsRoot
        ((ξ i (a g) : ℂˣ) : ℂ) := by
      rw [charPol_of_chars L _ ξ hξ hs]
      refine IsRoot.dvd ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      simp only [eval_sub, eval_X, eval_C, IsRoot.def]
      exact sub_self _
    exact Units.ext (eq_one_of_root hxu _ hr)
  choose α hα using fun i => exists_unr (hun i)
  obtain rfl : ξ = fun i => GlobalTheory.SmGL.unrChar _ (α i) := funext hα
  have hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars _ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  obtain ⟨-, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds _ n σ.V σ.ρ _ hξ).1 hs'
  have hN : (resCard (w.adicCompletion E) : ℂ) = (Ideal.absNorm w.asIdeal : ℂ) := by
    have := GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm E w
    exact_mod_cast this
  have hne : ∀ i j, (α i : ℂ) ≠ (Ideal.absNorm w.asIdeal : ℂ) * α j := fun i j e => by
    have hm : ∀ l, IrrGL.ofChar (GlobalTheory.SmGL.unrChar _ (α l)) (hξ l) ∈ GlobalTheory.RoadU.chars _ hξ := fun l =>
      Multiset.mem_map_of_mem (fun i => IrrGL.ofChar (GlobalTheory.SmGL.unrChar _ (α i)) (hξ i)) (Finset.mem_univ l)
    refine hu _ (hm j) _ (hm i) ?_
    simp only [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    exact unr_eq (by rw [hN]; exact e)
  have hsph := UpperTheory.ConvolutionTheory.Sph.unlSph E n w σ α hne hq
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsph
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hv
  exact ⟨v, hv0, GlobalTheory.LGrp.mem_fixed.1 hv⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IrrOfTw
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness
private theorem irr_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (φ : Γ →* kˣ)
    (h : IsIrr (tw r φ)) : IsIrr r := by
  obtain ⟨hne, -, hmin⟩ := h
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun U _ hU => hmin U le_top fun s v hv => ?_⟩
  have e : (tw r φ s : Matrix (Fin n) (Fin n) k).mulVec v =
      (φ s : k) • (r s : Matrix (Fin n) (Fin n) k).mulVec v := by
    rw [tw_val, Matrix.smul_mulVec]
  rw [e]
  exact U.smul_mem _ (hU s v hv)
private theorem comp_tw {Γ Δ k : Type} [Group Γ] [Group Δ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (φ : Γ →* kˣ)
    (f : Δ →* Γ) : (tw r φ).comp f = tw (r.comp f) (φ.comp f) := by
  refine MonoidHom.ext fun s => Units.ext ?_
  simp only [MonoidHom.comp_apply, tw_val]
private theorem open_ker {K Ω C : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω]
    [Algebra ℚ K] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] [Group C] {M : ℕ} (hM : 1 ≤ M) {φ : G ℚ Ω →* C}
    (hφ : KillsMu M φ) :
    IsOpen ((φ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)).ker : Set (G K Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := K) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ _ fun ζ hζ => hs ζ hζ
end UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness
open UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness in
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.twWit_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Z.Win.AIsoTwAlt → TwWit := by
  intro P hI l _ Ω _ _ _ ι n W M φ hM hφ hW K _ _ _ _ _ _ hK hirr
  haveI : Algebra.IsAlgebraic ℚ K := inferInstance
  haveI : IsAlgClosure K Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, (IsAlgClosure.isAlgebraic (R := ℚ) (K := Ω)).tower_top K⟩
  rw [comp_tw] at hirr ⊢
  have hW' := hW K hK (irr_of_tw _ _ hirr)
  have hs := (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results P K Ω l ι).1 0 (φ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))
    (open_ker hM hφ)
  rw [zpow_zero, one_mul] at hs
  obtain ⟨hc, art, χ, a, h⟩ := hs
  exact (hI P K Ω l ι n _ hW').2 _ ⟨χ, hc, art, a, h⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkTwo
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
theorem UpperTheory.Gal.projectedFormsSystemPart.exists_two_links_same_kappa_not_dvd_of_fit_deep :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O → ∃ K K' : Link T c' h, K'.κ = K.κ ∧ ¬ K'.s.p ∣ K.s.p := by
  intro hU Ω _ _ _ l _ c D T hF hD
  have hC : Ctx2 D ∨ Ctx3 D := hF.2.imp And.left And.left
  have hG : D.Good := hC.elim And.left And.left
  have hO := hF.1
  have hPre : Nonempty (Pre T) := by
    obtain ⟨η, N, m, hN, hK, hm, hη, hcc, hun, hv⟩ := etaEx hC
    obtain ⟨κ₀, m', h1, h2, h3, h4, h5⟩ := Tw.kap0 Ω l hG.l_odd T.K T.degK
      (hO.split 2 hG.two_mem) η N m hN hK hm hη hcc (fun A => by
        by_cases hA : Raw.Away D.S A
        · exact Or.inl (hun A hA)
        · simp only [Raw.Away, not_forall, not_not] at hA
          obtain ⟨p, hp, hA⟩ := hA
          exact Or.inr (hO.split p hp A hA))
    obtain ⟨γ, g1, g2, g3, g4⟩ := halfEx hG
    have hl := hG.pl_over l Fact.out
    obtain ⟨t, β, c₁, b1, b2, b3, b4, b5, b6, b7, U, hU, b8⟩ :=
      Tw.bt0 Ω l hG.l_odd T.K T.degK (D.pl l) hl (hO.split l hG.l_mem _ hl)
    exact ⟨{ κ₀ := κ₀, γ := γ, β := β, t := t, κ₀_open := h1, κ₀_ord := ⟨m', h2, h3⟩,
             κ₀_conj := fun σ hσ s s' e hs => by rw [h4 σ hσ s s' e]; exact hv _ hs
             κ₀_unr := fun A hA => h5 A (hun A hA), γ_cont := g1, γ_red := g2, γ_sq := g3, γ_ker := g4,
             β_cont := b3, t_cont := b1, β_t := b2, β_red := fun s => (b4 s).2,
             conj := fun σ hσ s s' e => ⟨b6 σ hσ s s' e, b5 σ hσ s s' e⟩, t_unr := b7,
             cyc := betaCyc Ω l T.K T.degK (D.pl l) hl β b6 U hU b8 }⟩
  obtain ⟨P⟩ := hPre
  obtain ⟨k1, k2, k3⟩ := kapCont P
  obtain ⟨u1, u2, u3⟩ := kapUnr P hG
  let Q : QCh T :=
    { κ := P.κ, β := P.βL, t := P.tL, κ_cont := k1, β_cont := k2, t_cont := k3, β_t := fun _ hg => P.β_t hg,
      β_red := fun _ => P.β_red _, conj := kapConj P hD, t_unr := u1, unr := u2, tame := u3, mu := kapMu P hG,
      cyc := kapCyc P hG }
  obtain ⟨c₁, -, hL, hκ, hβ, -⟩ := Pr.coefEx l c T.L Ω Q.κ Q.β Q.κ_cont Q.β_cont
  refine ⟨c₁, fun c' h h₁ => ?_⟩
  obtain ⟨κ, a1, a2, -⟩ := liftO c' Q.κ Q.κ_cont fun g => h₁ (hκ g)
  obtain ⟨β, b1, b2, b3⟩ := liftO c' Q.β Q.β_cont fun g => h₁ (hβ g)
  obtain ⟨X⟩ := ochOf Q c' h κ β a1 b1 a2 b2 fun g => b3 g (Q.β_red g)
  have key : ∀ Y : SetD T, ∃ K : Link T c' h, K.κ = X.κ ∧ K.s = Y.s := fun Y => by
    obtain ⟨V, hV⟩ := hU.lev l T.L Ω Y.s Y.s.S Y.fin subset_rfl Y.s.split
    obtain ⟨r, r1, r2, r3⟩ := residEx X Y V hG hO hV
    obtain ⟨σ, hσ, hc⟩ := Y.cc
    obtain ⟨g₀, -, hg₀⟩ := Y.om0
    exact ⟨{ s := Y.s, V := V, hV := hV, noMu := noMu hG T.L g₀ hg₀, large := fun τ x => h₁ (hL τ x), e := Y.e, hA := Y.hA,
             κ := X.κ, β := X.β, t := X.t, κ_cont := X.κ_cont, β_cont := X.β_cont, t_cont := X.t_cont, β_t := X.β_t,
             β_red := X.β_red, conj := fun g g' e => X.conj σ hσ g g' (hc g g' e), t_unr := X.t_unr,
             unr := fun A v hA hv g hg =>
               ⟨X.unr A (Y.away A v hA hv) hg, (((barFacts hG).2.2 A (Y.away A v hA hv) _ ⟨hg.1, hg.2⟩)).2⟩
             tame := X.tame
             mu := fun v g hg => by
               obtain ⟨a, ha⟩ := (prFacts l T.L Ω Y.s V).2.2.2 v g hg
               exact X.mu g a ha
             cyc := X.cyc, r := r, chib := fun i g => by rw [r1]; rfl
             psib := r2, th := r3, v0 := v0ok X Y V hG r r1 }, rfl, rfl⟩
  obtain ⟨Y, -⟩ := UpperTheory.Gal.projectedFormsSystemPart.setAv T hG hO 1 one_ne_zero
  obtain ⟨Y', hY⟩ := UpperTheory.Gal.projectedFormsSystemPart.setAv T hG hO Y.s.p Y.s.p_prime.ne_zero
  obtain ⟨K, k1, k2⟩ := key Y
  obtain ⟨K', k3, k4⟩ := key Y'
  exact ⟨K, K', k3.trans k1.symm, by rw [k2, k4]; exact hY⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedEndE
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
theorem UpperTheory.Gal.projectedFormsSystemPart.linked_endomorphism_dense :
    GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.W.LocCFTAll → _root_.UpperTheory.V.W.ModUAlt → UpperTheory.V.W.LevEx → UpperTheory.V.W.LamEx → UpperTheory.V.W.ProModularRingExists → _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense → _root_.UpperTheory.V.Sd.Seed2Alt → UpperTheory.V.Sd.Twist → UpperTheory.V.Sd.AlgCyc → UpperTheory.V.Sd.AlgRes → _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt := by
  intro hA _ hMod hLev hLam hB0 hS3 hS2 hTw hCyc hRes Ω _ _ _ l _ ι c _ N _ e ψ he hev η σ g₁ B M hM hram L _ _ _ _ Φ C₀ k hB hok hbig hseed
  obtain ⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩ := hseed
  haveI : IsAlgClosure L Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed ℚ
      isAlgebraic := haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
        Algebra.IsAlgebraic.tower_top (K := ℚ) L }
  have hM0 : M ≠ 0 := by
    rintro rfl
    obtain ⟨hσ, hc⟩ := k.c
    have h1 : σ ∈ η.ker := k.split ⊤ (by rw [← ValuationSubring.mem_nonunits_iff, Nat.cast_zero]; exact zero_mem _) ⟨by
      refine mem_Dec.2 (eq_top_iff.2 fun x _ => ?_)
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact ValuationSubring.mem_top _, hσ⟩
    have h2 := k.del ⟨σ, hσ⟩
    rw [hc, hok.del_c] at h2
    have h3 : η σ = 1 := h1
    rw [h3] at h2
    exact absurd h2 (by decide)
  have H : UpperTheory.V.Pr.LinkHyp c N e η σ B M := ⟨he, hM, hM0, hram, hB, hD.cc⟩
  have hv : Nonempty Φ.V := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hbig.1
    simp [UpperTheory.V.Fr.Frame.d] at this
  obtain ⟨v⟩ := hv
  have hker : η.ker = galOf ℚ K Ω := by
    rw [← hD.η_ker]
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]
    exact_mod_cast Iff.rfl
  haveI := hD.imag
  obtain ⟨κ, hκ⟩ := hTw K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc
  obtain ⟨hk3, hk2⟩ := UpperTheory.V.Pr.kaOf hCyc hRes Ω l ι c N e ψ η σ g₁ B M H L Φ k
  obtain ⟨ka, hk2, hka⟩ := hk2 K hker κ hκ
  obtain ⟨c₁, hle, hL, hv3, hv2, f, hf⟩ := UpperTheory.V.Pr.coefEx l c L Ω _ _ hk3.alg.1 hk2.alg.1
  haveI := UpperTheory.V.Pr.coefIs l c₁
  obtain ⟨m₃, hm₃, -, r₃, -, s₃⟩ := hS3 K L Ω l ι σ N' w χ' η' θ j hD hne M hM0
    (by rw [mul_comm]; exact (Nat.mul_dvd_mul_left l hev.two_dvd).trans hM)
    (UpperTheory.V.Z.Sym.Pl.linkUnr Ω l _ η _ σ g₁ B M L Φ k) (UpperTheory.V.Z.Sym.Pl.chiUnr Ω l c N e ψ χ' j hord hcong M hM L) 2
  obtain ⟨m₂, hm₂, -, r₂, -, -, -, s₂⟩ := hS2 K L Ω l ι σ N' w χ' η' θ j hD κ ka hκ hka 2
  obtain ⟨hfin, a₃, a₂⟩ := _root_.UpperTheory.Gal.projectedFormsSystemPart.twoRuns_alt hA hMod hLam ι H v hL hk2 hk3
    (UpperTheory.Gal.projectedFormsSystemPart.cRealAv hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl) hok hbig hle hf hk2 hv2)
    (UpperTheory.Gal.projectedFormsSystemPart.cRealAv hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl) hok hbig hle hf hk3 hv3)
    (fun R₂ => _root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hk2 χ' j hord hcong m₂ hm₂ _ (by
      convert s₂ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]))
    (fun R₃ => _root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hk3 χ' j hord hcong m₃ hm₃ _ (by
      convert s₃ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]))
  exact ⟨UpperTheory.V.Pr.finPtDown l c c₁ f hle hf Φ 3 hfin, a₃, ka, hk2.alg, a₂⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PmAutO
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.Gal.projectedFormsSystemPart.pmAutO_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
          Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.Gal.projectedFormsSystemPart.AutOffN K.s.v0 ι (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)) := by
  intro U Ω _ _ _ l _ c D T hF _ c' h K X B Λ ι J₀ hM φ hφ J hJ y hy hW r hr hc hm hi
  have hG : D.Good := hF.2.elim (fun a => a.1.1) (fun a => a.1.1)
  let x : B.Pt := (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)).comp φ
  have hx : ∀ b, x b = y (algebraMap X.B X.A (φ b)) := fun _ => rfl
  have hJx : J₀ ≤ RingHom.ker x := fun b hb => hy _ (hJ ▸ Ideal.mem_map_of_mem φ hb)
  have hrL : (X.P.map (y : X.A →+* PadicAlgCl l)).r.comp (resLe T.F_le) = r.comp (resQ T.L) := by
    rw [← hr]; rfl
  have hcL : Continuous (r.comp (resQ T.L)) := hc.comp (Af.continuous_restrictScalarsHom _ _ _)
  have hanti : StrictAnti fun i => (D.wts4 i : ℤ) := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp [Raw.wts4] <;> omega
  obtain ⟨w, hw⟩ := auArith U.pr.toClassicalTheorems.litN.aut.art D T c' h K X B φ hφ y x hx
    (auPsiCont D T c' h K X B 0 φ hφ y x hx (hrL ▸ hcL)) _ hanti hW
  have hrep := auRep D T c' h K X B 0 φ hφ y x hx
  rw [hrL, pow_zero, mul_one] at hrep
  obtain ⟨hi1, hi2⟩ := auIrr _ (r.comp (resQ T.L)) hi fun g =>
    ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.end2oN K.v0 hM.end2 x w _ hJx hw hrep (hi2 _)
end
end

