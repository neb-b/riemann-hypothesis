module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPerfectFieldExtensionFormallySmoothPartialLifts
section
set_option maxSynthPendingDepth 1

open Polynomial IntermediateField

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]

def IsGoodPartialLift (p : ℕ) (N : Ideal B) (u : K →ₐ[F] B ⧸ N) (ψ : K →+* B)
    (σ : Σ L : IntermediateField F K, L →ₐ[F] B) : Prop :=
  (∀ z : K, ∃ h : z ^ p ∈ σ.1, σ.2 ⟨z ^ p, h⟩ = ψ z) ∧ ∀ y : σ.1, Ideal.Quotient.mk N (σ.2 y) = u y

def PartialLiftLE (σ τ : Σ L : IntermediateField F K, L →ₐ[F] B) : Prop :=
  ∃ h : σ.1 ≤ τ.1, ∀ y : σ.1, τ.2 (IntermediateField.inclusion h y) = σ.2 y

theorem PartialLiftLE.trans {a b d : Σ L : IntermediateField F K, L →ₐ[F] B} (h₁ : PartialLiftLE a b)
    (h₂ : PartialLiftLE b d) : PartialLiftLE a d := by
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  exact ⟨h₁.trans h₂, fun y => by rw [← h₁' y, ← h₂' (IntermediateField.inclusion h₁ y)]; rfl⟩

theorem exists_isGoodPartialLift_upperBound {p : ℕ} {N : Ideal B} {u : K →ₐ[F] B ⧸ N} {ψ : K →+* B}
    (c : Set {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ})
    (hc : IsChain (fun a b => PartialLiftLE a.1 b.1) c) (hne : c.Nonempty) :
    ∃ ub : {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ},
      ∀ a ∈ c, PartialLiftLE a.1 ub.1 := by
  obtain ⟨i₀, hi₀⟩ := hne
  have : Nonempty c := ⟨⟨i₀, hi₀⟩⟩
  let t : c → IntermediateField F K := fun i => i.1.1.1
  have dir : Directed (· ≤ ·) t := by
    intro i j
    by_cases hij : i = j
    · exact ⟨i, le_rfl, hij ▸ le_rfl⟩
    rcases hc i.2 j.2 (fun h => hij (Subtype.ext h)) with h | h
    · exact ⟨j, h.1, le_rfl⟩
    · exact ⟨i, le_rfl, h.1⟩
  have dir' : Directed (· ≤ ·) (fun i => (t i).toSubalgebra) := dir.mono_comp _ (fun _ _ h => h)
  let f : ∀ i, (t i).toSubalgebra →ₐ[F] B := fun i => i.1.1.2
  have hf : ∀ (i j : c) (h : (t i).toSubalgebra ≤ (t j).toSubalgebra),
      f i = (f j).comp (Subalgebra.inclusion h) := by
    intro i j h
    ext y
    by_cases hij : i = j
    · subst hij; rfl
    rcases hc i.2 j.2 (fun h => hij (Subtype.ext h)) with ⟨h', h''⟩ | ⟨h', h''⟩
    · exact (h'' y).symm
    · exact h'' (Subalgebra.inclusion h y)
  have hT : (iSup t).toSubalgebra ≤ ⨆ i, (t i).toSubalgebra :=
    (IntermediateField.toSubalgebra_iSup_of_directed dir).le
  let φ : ↥(iSup t) →ₐ[F] B := Subalgebra.iSupLift _ dir' f hf _ hT
  have hφ : ∀ (i : c) (y : K) (hy : y ∈ t i), φ ⟨y, (le_iSup t i) hy⟩ = i.1.1.2 ⟨y, hy⟩ :=
    fun i y hy => Subalgebra.iSupLift_mk _ (i := i) ⟨y, hy⟩ _
  refine ⟨⟨⟨iSup t, φ⟩, ⟨fun z => ?_, fun y => ?_⟩⟩,
    fun a ha => ⟨le_iSup t ⟨a, ha⟩, fun y => hφ ⟨a, ha⟩ y.1 y.2⟩⟩
  · obtain ⟨h, h'⟩ := (i₀.2).1 z
    exact ⟨le_iSup t ⟨i₀, hi₀⟩ h, (hφ ⟨i₀, hi₀⟩ _ h).trans h'⟩
  · have hy : (y : K) ∈ ⋃ i, (t i : Set K) := by
      rw [← IntermediateField.coe_iSup_of_directed dir]; exact y.2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    rw [show y = ⟨y, (le_iSup t i) hi⟩ from rfl, hφ i y hi]
    exact i.1.2.2 ⟨y, hi⟩

theorem exists_isGoodPartialLift_frobenius [PerfectField F] (p : ℕ) [hp : Fact p.Prime] [CharP F p]
    {N : Ideal B} (hpB : (p : B) = 0) (hN : N ^ 2 = ⊥) (u : K →ₐ[F] B ⧸ N) :
    ∃ σ, IsGoodPartialLift p N u ((sqZeroFrobeniusLift N hp.out hpB hN).comp u.toRingHom) σ := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  set P := sqZeroFrobeniusLift N hp.out hpB hN
  set ψ : K →+* B := P.comp u.toRingHom
  let L₀ : IntermediateField F K :=
    { (frobenius K p).fieldRange with
      algebraMap_mem' := fun a => ⟨algebraMap F K ((frobeniusEquiv F p).symm a), by
        rw [frobenius_def, ← map_pow]; congr 1; exact (frobeniusEquiv F p).apply_symm_apply a⟩ }
  let e := (frobenius K p).rangeRestrictFieldEquiv
  have he : ∀ (y : (frobenius K p).fieldRange) (z : K), (y : K) = z ^ p → e.symm y = z :=
    fun y z h => e.symm_apply_eq.mpr (Subtype.ext (h.trans (frobenius_def p z).symm))
  let φ₀ : L₀ →ₐ[F] B :=
    { ψ.comp (e.symm.toRingHom : (frobenius K p).fieldRange →+* K) with
      commutes' := fun a => by
        obtain ⟨b, rfl⟩ := (frobeniusEquiv F p).surjective a
        have hb : algebraMap F L₀ (frobeniusEquiv F p b) =
            ⟨algebraMap F K b ^ p, ⟨algebraMap F K b, by rw [frobenius_def]⟩⟩ := by
          apply Subtype.ext
          show algebraMap F K (frobeniusEquiv F p b) = _
          rw [frobeniusEquiv_def, map_pow]
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
        rw [hb]
        show ψ (e.symm _) = _
        rw [he _ (algebraMap F K b) rfl]
        simp [ψ, P, ← Ideal.Quotient.mk_algebraMap, sqZeroFrobeniusLift_mk, frobenius_def] }
  refine ⟨⟨L₀, φ₀⟩, fun z => ⟨⟨z, by rw [frobenius_def]⟩, congrArg ψ (he _ z rfl)⟩, fun y => ?_⟩
  obtain ⟨z, hz⟩ := y.2
  have hy : y = ⟨z ^ p, ⟨z, by rw [frobenius_def]⟩⟩ := Subtype.ext (hz.symm.trans (frobenius_def p z))
  subst hy
  show Ideal.Quotient.mk N (ψ (e.symm _)) = _
  rw [he _ z rfl]
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u z)
  simp [ψ, P, ← hc, sqZeroFrobeniusLift_mk]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormRemainder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

def PrimitiveFormRemainder.analyticSubring (d : ℕ) (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {g | AnalyticAt ℂ g y₀}
  mul_mem' ha hb := ha.mul hb
  one_mem' := analyticAt_const
  add_mem' ha hb := ha.add hb
  zero_mem' := analyticAt_const
  neg_mem' ha := ha.neg

theorem PrimitiveFormRemainder.proof (hSWD : SeparateWeierstrassDivision.Statement) :
    PrimitiveFormRemainder.Statement := by
  classical
  intro σ _ w d A ℓ N δ q n c f hδ hq hc hW hf
  obtain ⟨v, r, -, hr, hev⟩ := hSWD σ d (A w) w n c (fun x => f x.2) hc hW
    (hf.comp (analyticAt_snd (p := (A w, w))))
  set S := PrimitiveFormRemainder.analyticSubring d (A w)

  let s : ((i : σ) → Fin (n i)) → ℕ := fun α => ∑ i, (α i : ℕ)
  let M : ℕ := ∑ i, n i
  have hsM : ∀ α, s α ≤ M := fun α => Finset.sum_le_sum fun i _ => (α i).isLt.le
  let Q : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i => ∑ j, C (q i j) * X ^ (j : ℕ)
  let R : Polynomial ((Fin d → ℂ) → ℂ) :=
    ∑ α, C (r α * δ ^ (M - s α)) * ∏ i, Q i ^ (α i : ℕ)
  refine ⟨M, R, ?_, ?_⟩
  ·
    have hC : ∀ g : (Fin d → ℂ) → ℂ, AnalyticAt ℂ g (A w) → C g ∈ lifts S.subtype := fun g hg =>
      C_mem_lifts S.subtype ⟨g, hg⟩
    have hR : R ∈ lifts S.subtype := by
      refine Subsemiring.sum_mem _ fun α _ => Subsemiring.mul_mem _ (hC _ ((hr α).mul (hδ.pow _)))
        (Subsemiring.prod_mem _ fun i _ => Subsemiring.pow_mem _ ?_ _)
      exact Subsemiring.sum_mem _ fun j _ =>
        Subsemiring.mul_mem _ (hC _ (hq i j)) (X_pow_mem_lifts _ _)
    intro k
    obtain ⟨g, hg⟩ := (lifts_iff_coeff_lifts R).1 hR k
    rw [← hg]
    exact g.2
  ·
    have hcont : Continuous fun z : σ → ℂ => (A z, z) := A.continuous.prodMk continuous_id
    filter_upwards [(hcont.tendsto w).eventually hev] with z hz hWz hqz
    have hf' : f z = ∑ α, r α (A z) * ∏ i, z i ^ (α i : ℕ) := by
      rw [hz]; simp [hWz]
    have hQ : ∀ i, (Q i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z) = δ (A z) * z i := by
      intro i
      simp [Q, eval₂_finsetSum, hqz i]
    simp only [R, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_finsetProd, eval₂_pow, hQ, hf', Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [Pi.evalRingHom_apply, Pi.mul_apply, Pi.pow_apply, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [← pow_mul_pow_sub (δ (A z)) (hsM α)]
    ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjDimSpread
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open CategoryTheory

variable {R : Type} [CommRing R]

noncomputable def ProjDimSpread.localizedModuleEquiv (M : ModuleCat.{0} R) (S : Submonoid R) :
    M.localizedModule S ≃ₗ[Localization S] LocalizedModule S M :=
  LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S (M.localizedModuleMkLinearMap S)
      (LocalizedModule.mkLinearMap S M))

theorem ProjDimSpread.hasProjectiveDimensionLE_zero_iff (M : ModuleCat.{0} R) (S : Submonoid R) :
    HasProjectiveDimensionLE (M.localizedModule S) 0 ↔
      Module.Projective (Localization S) (LocalizedModule S M) := by
  rw [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
    ← IsProjective.iff_projective]
  exact ⟨fun _ ↦ Module.Projective.of_equiv (localizedModuleEquiv M S),
    fun _ ↦ Module.Projective.of_equiv (localizedModuleEquiv M S).symm⟩

theorem ProjDimSpread.spread_zero [IsNoetherianRing R] (P : Ideal R) [P.IsPrime]
    (M : ModuleCat.{0} R) [Module.Finite R M]
    (h : HasProjectiveDimensionLE (M.localizedModule P.primeCompl) 0) :
    ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
      HasProjectiveDimensionLE (M.localizedModule Q.primeCompl) 0 := by
  rw [hasProjectiveDimensionLE_zero_iff] at h
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have : Module.Flat (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.Flat.of_projective
  have hfree : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  have hP : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ Module.freeLocus R M :=
    Module.mem_freeLocus.mpr hfree
  obtain ⟨_, ⟨g, rfl⟩, hPg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hP
      Module.isOpen_freeLocus
  refine ⟨g, (PrimeSpectrum.mem_basicOpen g _).mp hPg, fun Q _ hQ ↦ ?_⟩
  have : Module.Free (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M) :=
    Module.mem_freeLocus.mp (hsub ((PrimeSpectrum.mem_basicOpen g ⟨Q, inferInstance⟩).mpr hQ))
  exact (hasProjectiveDimensionLE_zero_iff M Q.primeCompl).mpr Module.Projective.of_free

theorem ProjDimSpread.spread [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (n : ℕ) :
    ∀ (M : ModuleCat.{0} R) [Module.Finite R M],
      HasProjectiveDimensionLE (M.localizedModule P.primeCompl) n →
      ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
        HasProjectiveDimensionLE (M.localizedModule Q.primeCompl) n := by
  induction n with
  | zero => exact fun M _ h ↦ spread_zero P M h
  | succ n ih =>
    intro M _ h
    rcases Module.exists_finite_presentation R M with ⟨F, _, _, _, _, f, surjf⟩
    let S := f.shortComplexKer
    have S_exact := LinearMap.shortExact_shortComplexKer surjf
    have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
    have Sp_exact (T : Submonoid R) : (S.map (ModuleCat.localizedModuleFunctor T)).ShortExact :=
      S_exact.map_of_exact (ModuleCat.localizedModuleFunctor T)
    have projp (T : Submonoid R) : Projective (S.map (ModuleCat.localizedModuleFunctor T)).X₂ :=
      (ModuleCat.localizedModuleFunctor.{0} T).projective_obj_of_projective proj
    have hK : HasProjectiveDimensionLE
        ((ModuleCat.of R (LinearMap.ker f)).localizedModule P.primeCompl) n :=
      ((Sp_exact P.primeCompl).hasProjectiveDimensionLT_X₃_iff n (projp _)).mp h
    obtain ⟨g, hg, hQ⟩ := ih (ModuleCat.of R (LinearMap.ker f)) hK
    exact ⟨g, hg, fun Q _ hgQ ↦
      ((Sp_exact Q.primeCompl).hasProjectiveDimensionLT_X₃_iff n (projp _)).mpr (hQ Q hgQ)⟩

noncomputable def ProjDimSpread.quotientEquiv (I Q : Ideal R) [Q.IsPrime] :
    (ModuleCat.of R (R ⧸ I)).localizedModule Q.primeCompl ≃ₗ[Localization.AtPrime Q]
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) :=
  ((ProjDimSpread.localizedModuleEquiv (ModuleCat.of R (R ⧸ I)) Q.primeCompl).trans
    (LinearEquiv.extendScalarsOfIsLocalization Q.primeCompl (Localization.AtPrime Q)
      (IsLocalizedModule.linearEquiv Q.primeCompl (LocalizedModule.mkLinearMap Q.primeCompl (R ⧸ I))
        (I.toLocalizedQuotient' (Localization.AtPrime Q) Q.primeCompl
          (Algebra.linearMap R (Localization.AtPrime Q)))))).trans
    (Submodule.quotEquivOfEq _ _
      (Ideal.localized'_eq_map (Localization.AtPrime Q) Q.primeCompl I))

theorem ProjDimSpread.proof : ProjDimSpread.Statement := by
  intro R _ _ I P _ ℓ h
  have e : ∀ (Q : Ideal R) [Q.IsPrime], (ModuleCat.of R (R ⧸ I)).localizedModule Q.primeCompl ≅
      ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) :=
    fun Q _ ↦ (ProjDimSpread.quotientEquiv I Q).toModuleIso
  have hP : HasProjectiveDimensionLE
      ((ModuleCat.of R (R ⧸ I)).localizedModule P.primeCompl) ℓ :=
    hasProjectiveDimensionLT_of_iso (e P).symm (ℓ + 1)
  obtain ⟨g, hg, hQ⟩ := ProjDimSpread.spread P ℓ (ModuleCat.of R (R ⧸ I)) hP
  refine ⟨g, hg, fun Q _ hgQ ↦ ?_⟩
  have := hQ Q hgQ
  exact hasProjectiveDimensionLT_of_iso (e Q) (ℓ + 1)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem subset_closure_nonvanishing_of_open {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hDc : IsPreconnected D) (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hδ : AnalyticOnNhd ℂ δ D) (hne : ∃ y ∈ D, δ y ≠ 0) :
    Y ⊆ closure {x | x ∈ Y ∧ δ (A x) ≠ 0} := by
  obtain ⟨y₁, hy₁D, hy₁⟩ := hne
  intro x hx
  rw [mem_closure_iff_nhds]
  intro V hV
  by_contra hempty
  have hzero : δ =ᶠ[𝓝 (A x)] 0 := by
    filter_upwards [hopen x hx V hV] with y hy
    obtain ⟨x', ⟨hx'Y, hx'V⟩, rfl⟩ := hy
    by_contra h0
    exact hempty ⟨x', hx'V, hx'Y, h0⟩
  exact hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hmaps hx) hzero hy₁D)

theorem ProperOpenProjectionCover.proof (hbranch : ProperOpenProjectionBranchLocus.Statement)
    (hcount : UnbranchedProperCountConstant.Statement) : ProperOpenProjectionCover.Statement := by
  intro σ _ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨δ, hδ, hne, hsec⟩ := hbranch σ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨N, hN⟩ := hcount σ (X ∩ B) d A D δ hD hDc hmaps hprop hδ (fun x hx hx0 => by
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hsec x hx hx0
    exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hXV⟩)
  exact ⟨δ, N, hδ, hne, hN, hsec, subset_closure_nonvanishing_of_open hDc hmaps hopen hδ hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionLocalUnbranched
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

theorem exists_forall_ne_zero_of_isOpen {E ι : Type} [TopologicalSpace E] (s : Finset ι)
    (G : ι → E → ℂ) (U : Set E) (hc : ∀ i ∈ s, ContinuousOn (G i) U)
    (hne : ∀ i ∈ s, ∀ W : Set E, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, G i t ≠ 0) :
    ∀ W : Set E, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, ∀ i ∈ s, G i t ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rintro W - - ⟨t, ht⟩
    exact ⟨t, ht, by simp⟩
  | insert a s ha ih =>
    intro W hWo hWU hW
    obtain ⟨t₀, ht₀W, ht₀⟩ := hne a (Finset.mem_insert_self a s) W hWo hWU hW
    have hW'o : IsOpen (W ∩ G a ⁻¹' {0}ᶜ) :=
      ((hc a (Finset.mem_insert_self a s)).mono hWU).isOpen_inter_preimage hWo isOpen_compl_singleton
    obtain ⟨t, ⟨htW, hta⟩, hts⟩ := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      (fun i hi => hne i (Finset.mem_insert_of_mem hi)) _ hW'o (Set.inter_subset_left.trans hWU)
      ⟨t₀, ht₀W, ht₀⟩
    refine ⟨t, htW, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hta
    · exact hts i hi

theorem ProperOpenProjectionLocalUnbranched.proof (hFin : CompactHolomorphicFibreFinite.Statement)
    (hLoc : IsolatedFibreLocalUnbranched.Statement) : ProperOpenProjectionLocalUnbranched.Statement := by
  classical
  intro σ _ X B k f d A D hB hf hXB hD hAD hprop hopen y₀ hy₀
  have zerosX : ∀ z, z ∈ X ∩ B → ∀ i, f i z = 0 := fun z hz => by
    rw [hXB] at hz
    exact hz.2
  have memX : ∀ z, z ∈ B → (∀ i, f i z = 0) → z ∈ X ∩ B := fun z hz h0 => by
    rw [hXB]
    exact ⟨hz, h0⟩

  set F := {x | x ∈ X ∩ B ∧ A x = y₀} with hF
  have hFc : IsCompact F := by
    have := hprop {y₀} (Set.singleton_subset_iff.2 hy₀) isCompact_singleton
    simpa only [Set.mem_singleton_iff] using this

  set n := Fintype.card σ
  let L : (σ → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n => ℂ) (Fintype.equivFin σ)
  set U₀ : Set (Fin n → ℂ) := L.symm ⁻¹' B with hU₀
  set Φ : (Fin n → ℂ) → Fin (k + d) → ℂ :=
    fun v => Fin.append (fun i => f i (L.symm v)) (A (L.symm v)) with hΦ
  set yv : Fin (k + d) → ℂ := Fin.append (0 : Fin k → ℂ) y₀ with hyv
  have hU₀o : IsOpen U₀ := hB.preimage L.symm.continuous
  have hΦd : DifferentiableOn ℂ Φ U₀ := by
    refine differentiableOn_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [hΦ, Fin.append_left]
      exact (hf i).differentiableOn.comp L.symm.differentiable.differentiableOn (fun v hv => hv)
    · simp only [hΦ, Fin.append_right]
      exact ((differentiable_apply (𝕜 := ℂ) j).comp
        (A.differentiable.comp L.symm.differentiable)).differentiableOn
  have hfib : {v | v ∈ U₀ ∧ Φ v = yv} = L.symm ⁻¹' F := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hU₀, hF, hΦ, hyv]
    constructor
    · rintro ⟨hv, he⟩
      refine ⟨memX _ hv fun i => ?_, ?_⟩
      · simpa using congrFun he (Fin.castAdd d i)
      · funext j
        simpa using congrFun he (Fin.natAdd k j)
    · rintro ⟨hv, hA⟩
      refine ⟨hv.2, funext fun j => ?_⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [zerosX _ hv i]
      · simp [hA]
  have hfibc : IsCompact {v | v ∈ U₀ ∧ Φ v = yv} := by
    rw [hfib, ← L.image_eq_preimage_symm]
    exact hFc.image L.continuous
  have hFfin : F.Finite := by
    have h1 := (hFin n (k + d) U₀ Φ yv hU₀o hΦd hfibc).image L.symm
    rwa [hfib, Set.image_preimage_eq _ L.symm.surjective] at h1

  have hloc : ∀ x ∈ F, ∃ (M : Set (σ → ℂ)) (g : (Fin d → ℂ) → ℂ), IsOpen M ∧ x ∈ M ∧
      AnalyticAt ℂ g y₀ ∧ (¬ ∀ᶠ t in 𝓝 y₀, g t = 0) ∧
      ∀ z ∈ X ∩ B ∩ M, g (A z) ≠ 0 →
        ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O := by
    intro x hx
    have hiso : ∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ B ∩ W, A x' = A x → x' = x := by
      refine ⟨(F \ {x})ᶜ, hFfin.sdiff.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl, ?_⟩
      rintro x' ⟨hx'XB, hx'W⟩ hx'A
      by_contra hne
      exact hx'W ⟨⟨hx'XB, hx'A.trans hx.2⟩, hne⟩
    obtain ⟨M, g, hM, hg, hg0, hsec⟩ := hLoc σ X B k f d A hB hf hXB hopen x hx.1 hiso
    rw [hx.2] at hg hg0
    exact ⟨interior M, g, isOpen_interior, mem_interior_iff_mem_nhds.2 hM, hg, hg0,
      fun z hz => hsec z ⟨hz.1, interior_subset hz.2⟩⟩
  choose! M g hMo hxM hga hgne hsec using hloc
  set s := hFfin.toFinset with hs
  have hsF : ∀ x, x ∈ s ↔ x ∈ F := fun x => hFfin.mem_toFinset

  obtain ⟨r₀, hr₀, hr₀D⟩ := nhds_basis_closedBall.mem_iff.1 (hD.mem_nhds hy₀)
  set Mall := ⋃ x ∈ F, M x with hMall
  have hMallo : IsOpen Mall := isOpen_biUnion fun x hx => hMo x hx
  set C := {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ r₀} \ Mall with hC
  have hCc : IsCompact C := (hprop _ hr₀D (isCompact_closedBall y₀ r₀)).diff hMallo
  have hAC : y₀ ∉ A '' C := by
    rintro ⟨c, ⟨⟨hcXB, -⟩, hcM⟩, hcA⟩
    exact hcM (Set.mem_biUnion (show c ∈ F from ⟨hcXB, hcA⟩) (hxM c ⟨hcXB, hcA⟩))
  have hev : ∀ᶠ t in 𝓝 y₀, t ∈ ball y₀ r₀ ∧ t ∉ A '' C ∧ ∀ x ∈ s, AnalyticAt ℂ (g x) t := by
    refine (show ∀ᶠ t in 𝓝 y₀, t ∈ ball y₀ r₀ from ball_mem_nhds y₀ hr₀).and
      ((show ∀ᶠ t in 𝓝 y₀, t ∉ A '' C from
        ((hCc.image A.continuous).isClosed.isOpen_compl).mem_nhds hAC).and ?_)
    exact (Filter.eventually_all_finset s).2 fun x hx => (hga x ((hsF x).1 hx)).eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hgan : ∀ x ∈ s, AnalyticOnNhd ℂ (g x) (ball y₀ r) := fun x hx t ht => (hball t ht).2.2 x hx
  refine ⟨ball y₀ r, fun t => ∏ x ∈ s, g x t, isOpen_ball, mem_ball_self hr, ?_,
    Finset.analyticOnNhd_fun_prod s hgan, ?_, ?_⟩
  · intro t ht
    exact hr₀D (ball_subset_closedBall (hball t ht).1)
  · intro W hWo hWU hW
    have hne : ∀ x ∈ s, ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ ball y₀ r → W.Nonempty →
        ∃ t ∈ W, g x t ≠ 0 := by
      intro x hx W hWo hWU hW
      by_contra hcon
      push Not at hcon
      obtain ⟨t, htW⟩ := hW
      have hzt : g x =ᶠ[𝓝 t] 0 := by
        filter_upwards [hWo.mem_nhds htW] with u hu using hcon u hu
      have hEq := (hgan x hx).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball y₀ r).isPreconnected (hWU htW) hzt
      exact hgne x ((hsF x).1 hx) (by
        filter_upwards [ball_mem_nhds y₀ hr] with u hu using hEq hu)
    obtain ⟨t, htW, ht⟩ := exists_forall_ne_zero_of_isOpen s g (ball y₀ r)
      (fun x hx => (hgan x hx).continuousOn) hne W hWo hWU hW
    exact ⟨t, htW, Finset.prod_ne_zero_iff.2 ht⟩
  · intro y hyU hgy x' hx'XB hx'A
    have hx'M : x' ∈ Mall := by
      by_contra hn
      refine (hball y hyU).2.1 ⟨x', ⟨⟨hx'XB, ?_⟩, hn⟩, hx'A⟩
      rw [hx'A]
      exact ball_subset_closedBall (hball y hyU).1
    obtain ⟨x, hxF, hx'x⟩ := Set.mem_iUnion₂.1 hx'M
    have hgx : g x (A x') ≠ 0 := by
      rw [hx'A]
      exact Finset.prod_ne_zero_iff.1 hgy x ((hsF x).2 hxF)
    exact hsec x hxF x' ⟨hx'XB, hx'x⟩ hgx

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreGermIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteFibreGermIntegral.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x → (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (a j) (A x)) ∧
        ∀ᶠ z in 𝓝 x, z ∈ X → g z ^ N + ∑ j, a j (A z) * g z ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

