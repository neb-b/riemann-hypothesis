module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildInertiaKilledByAdditiveLocallyConstantStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInertiaRestrictionCocyclesLe
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.Quad

theorem length_torsionBy_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : O) :
    Module.length O (Submodule.torsionBy O (KOG O 1) a) ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  rcases eq_or_ne a 0 with rfl | ha
  · have e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O := Submodule.quotEquivOfEqBot _ (by simp)
    rw [e.length_eq]
    have : Module.length O O = ⊤ := by
      by_contra h
      have h2 := (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).2
      have : IsArtinianRing O := h2
      exact IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)
    rw [this]; exact le_top
  · have ha' : algebraMap O (FractionRing O) a ≠ 0 := by
      simpa using ha
    let x : KOG O 1 := Submodule.Quotient.mk fun _ => (algebraMap O (FractionRing O) a)⁻¹
    have hx : a • x = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨fun _ => 1, ?_⟩
      funext j
      simp [Algebra.smul_def, mul_inv_cancel₀ ha']
    let x' : Submodule.torsionBy O (KOG O 1) a := ⟨x, hx⟩
    let f : O →ₗ[O] Submodule.torsionBy O (KOG O 1) a := LinearMap.toSpanSingleton O _ x'
    have hf : Ideal.span {a} ≤ LinearMap.ker f := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Subtype.ext hx
    refine Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_
    rintro ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨b, hb⟩ := hy
      refine ⟨Submodule.Quotient.mk (b 0), Subtype.ext ?_⟩
      change b 0 • x = Submodule.Quotient.mk y
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      have h0 : algebraMap O (FractionRing O) (b 0) = algebraMap O (FractionRing O) a * y 0 := by
        simpa [Algebra.smul_def] using congrFun hb 0
      simp only [Pi.smul_apply, Algebra.smul_def, h0]
      field_simp

theorem eq_zero_of_tameGen {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {γ : G E Ω} (hγ : TameGenAt A γ) {M : Type} [AddCommGroup M] (f : G E Ω → M)
    (hf : IsLocallyConstant f) (hadd : ∀ a ∈ Ine (F := E) A, ∀ b ∈ Ine (F := E) A, f (a * b) = f a + f b)
    (hw : ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → f σ = 0) (h0 : f γ = 0)
    (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) : f σ = 0 := by
  have h1 : f 1 = 0 := by simpa using hadd 1 (one_mem _) 1 (one_mem _)
  let K : Subgroup (G E Ω) :=
    { carrier := {g | g ∈ Ine (F := E) A ∧ f g = 0}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨one_mem _, h1⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have := hadd a ha.1 a⁻¹ (inv_mem ha.1)
        rw [mul_inv_cancel, h1, ha.2, zero_add] at this
        exact this.symm⟩ }
  refine closure_minimal (t := {g | f g = 0}) ?_ (hf.isClosed_fiber 0) (hγ.2 hσ)
  intro g hg
  refine ((Subgroup.closure_le K).2 ?_ hg).2
  rintro g (rfl | hg)
  · exact ⟨hγ.1, h0⟩
  · exact ⟨GlobalTheory.TameCharUnique.mem_Ine_of_wild hg, hw g hg⟩

theorem psiChi_group {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}
    (hS : GoodCongruenceObjects D.nd r ρ π S) (c : Fin D.R.t) (g : GE D.nd) :
    S.ψχ c (fun x' => rO D.nd i r (S.p x') g) = ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g :=
    ⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩
  have a1 := h1 g (S.e.symm (0, fun _ => 1))
  have a2 := h2 _ hg (S.e.symm (0, fun _ => 1))
  simp only [hp] at a2
  have a3 := congrFun (congrArg Prod.snd (a2.symm.trans a1)) c
  simp only [LinearEquiv.apply_symm_apply, mul_one] at a3
  exact IsFractionRing.injective _ _ a3

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  intro D i r ρ π Xs S hr hS hπ v hv hq c
  have hl := D.nd.SQ_l i v hv
  have hchi : ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chiU D.nd i ((c : ℕ) + 1) γ = chiU D.nd i 1 γ :=
    fun γ hγ => (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v hl γ hγ).2 _ (by omega) c.2
  have hγ0 := D.nd.locNd_chebotarevPlace_mem i v
  have htor : ∀ f ∈ cocChi i r S Xs c, (D.nd.zeta i v - 1) • f (D.nd.gam0 i v) = 0 := by
    intro f hf
    have := Check.cocW_quad i r S Xs _ hq hf _ hγ0
    rw [Check.matKO_smul_one, psiChi_group hS, hchi _ hγ0] at this
    rw [sub_smul, one_smul, sub_eq_zero]
    exact this
  have hdet : ∀ f ∈ cocChi i r S Xs c, f (D.nd.gam0 i v) = 0 →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f σ = 0 := by
    intro f hf h0
    obtain ⟨hc, hz⟩ := (_root_.GlobalTheory.Cut.Coc.main D i r ρ π Xs S hr hS hπ).2 c hf
    have : DiscreteTopology (KOG (D.nd.O i) 1) := ⟨rfl⟩
    have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 hc
    have hadd : ∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
        f (a * b) = f a + f b := by
      intro a ha b _
      have e : chiRatO D.nd i ((c : ℕ) + 1) a = (1 : D.nd.O i) • 1 := by
        change (((chiU D.nd i ((c : ℕ) + 1) a * (chiU D.nd i 1 a)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
          (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) = _
        rw [hchi a ha, mul_inv_cancel, Units.val_one]
      rw [hz, Check.WKG_eq_matKO, e, Check.matKO_smul_one, one_smul]
    exact eq_zero_of_tameGen (D.nd.restN_tameGenerator_generates i v hv) f hlc hadd (GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant D i v hl f hlc hadd) h0
  refine le_trans ?_ (length_torsionBy_le (D.nd.zeta i v - 1))
  refine Module.length_le_of_injective
    (LinearMap.restrict (LinearMap.proj (⟨D.nd.gam0 i v, hγ0⟩ : Ine (F := D.host.E) (D.nd.plOm.1 v))) ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact htor f hf
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, f, hf, rfl⟩ h0
    refine Subtype.ext (funext fun σ => ?_)
    exact hdet f hf (congrArg Subtype.val h0) σ.1 σ.2

end GlobalTheory.Cut.Quad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieSkewAdjointMatrix
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory.LieSkew

open GlobalTheory.ExpDeriv

theorem inner_integral_identity : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc hc0 f f' hf hf' hcf' hd H t
  exact _root_.GlobalTheory.AutomorphicL2Unitary.inner_R_sub_eq_intervalIntegral Γ μ c hc hc0 hf hf' hcf' hd H t (GlobalTheory.T.integrable_conj_mul_translate_path' Γ μ c hc hf' hcf' H t)

theorem hasDerivAt_inner_R : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ H : L2 Γ μ, HasDerivAt (fun t => inner ℂ H (R Γ μ (c t) hf.toL2)) (inner ℂ H hf'.toL2) 0 := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc hc0 f f' hf hf' hcf' hd H
  have hk : Continuous fun s => inner ℂ H (R Γ μ (c s) hf'.toL2) :=
    continuous_const.inner ((continuous_R hf'.toL2).comp hc)
  have e : (fun t => inner ℂ H (R Γ μ (c t) hf.toL2)) =
      fun t => inner ℂ H hf.toL2 + ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
    funext t
    rw [← inner_integral_identity Γ μ c hc hc0 hf hf' hcf' hd H t, add_sub_cancel]
  rw [e]
  have := ((hk.integral_hasStrictDerivAt 0 0).hasDerivAt).const_add (inner ℂ H hf.toL2)
  simpa [hc0] using this

theorem inner_lie_eq_neg_inner_lie {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (μ : Measure (GA E N))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)
    (hW : _root_.GlobalTheory.CuspRep.IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (X : Lie E N) (φ ψ : W) :
    inner ℂ (toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩) (toL2ₗ μ W h ψ) =
      - inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩) := by
  set c : ℝ → GA E N := fun t => infGL E N (expGL X t) with hcdef
  have hc : Continuous c := by
    have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Matrix.of X) := by
      open scoped Matrix.Norms.Operator in
      exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    have hinv : ∀ t, (expGL X t)⁻¹ = expGL X (-t) := fun t =>
      (eq_inv_of_mul_eq_one_right (by rw [← expGL_add, add_neg_cancel, expGL_zero])).symm
    have he : Continuous (expGL X) := Units.continuous_iff.2 ⟨hv, by
      simp only [hinv, expGL_val]
      exact hv.comp continuous_neg⟩
    exact GlobalTheory.CuspQuot.continuous_infGL.comp he
  have hc0 : c 0 = 1 := by simp only [c, expGL_zero, map_one]
  have hcinv : ∀ t, c (-t) = (c t)⁻¹ := fun t => by
    simp only [c, ← map_inv]
    congr 1
    refine (eq_inv_of_mul_eq_one_right ?_)
    rw [← expGL_add, add_neg_cancel, expGL_zero]
  have hcont : ∀ θ ∈ W, Continuous (θ : GA E N → ℂ) := fun θ hθ =>
    ContAut.continuous_of_isOpen_stab E N θ (hA θ hθ).level
  set F := toL2ₗ μ W h φ
  set Ψ := toL2ₗ μ W h ψ
  set F' := toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩
  set Ψ' := toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩
  have dF := hasDerivAt_inner_R (latticeGL E N) μ c hc hc0 (h φ φ.2) (h _ (hW (.lie X) φ.1 φ.2))
    (hcont _ (hW (.lie X) φ.1 φ.2)) (fun x t => hasDerivAt_along X φ.1 x t) Ψ
  have dΨ := hasDerivAt_inner_R (latticeGL E N) μ c hc hc0 (h ψ ψ.2) (h _ (hW (.lie X) ψ.1 ψ.2))
    (hcont _ (hW (.lie X) ψ.1 ψ.2)) (fun x t => hasDerivAt_along X ψ.1 x t) F
  have d1 : HasDerivAt (fun t => inner ℂ (R (latticeGL E N) μ (c t) F) Ψ) (inner ℂ F' Ψ) 0 := by
    have := dF.star
    simp only [← starRingEnd_apply, inner_conj_symm] at this
    exact this
  have d2 : HasDerivAt (fun t => inner ℂ F (R (latticeGL E N) μ (c (-t)) Ψ)) (-inner ℂ F Ψ') 0 := by
    have h0 : HasDerivAt (fun t => inner ℂ F (R (latticeGL E N) μ (c t) Ψ)) (inner ℂ F Ψ') (-0) := by
      rw [neg_zero]; exact dΨ
    have := h0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simpa [Function.comp_def] using this
  have e : (fun t => inner ℂ (R (latticeGL E N) μ (c t) F) Ψ) =
      fun t => inner ℂ F (R (latticeGL E N) μ (c (-t)) Ψ) := by
    funext t
    let U : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
      ⟨(R (latticeGL E N) μ (c t)).toLinearMap, fun v => norm_R _ v⟩
    have hU : ∀ v, U v = R (latticeGL E N) μ (c t) v := fun _ => rfl
    have hΨ : R (latticeGL E N) μ (c t) (R (latticeGL E N) μ (c t)⁻¹ Ψ) = Ψ := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    calc inner ℂ (R (latticeGL E N) μ (c t) F) Ψ
        = inner ℂ (U F) (U (R (latticeGL E N) μ (c t)⁻¹ Ψ)) := by rw [hU, hU, hΨ]
      _ = inner ℂ F (R (latticeGL E N) μ (c t)⁻¹ Ψ) := U.inner_map_map _ _
      _ = _ := by rw [hcinv]
  rw [e] at d1
  exact d1.unique d2

theorem lie_skew : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hW : _root_.GlobalTheory.CuspRep.IsStable W), (∀ φ ∈ W, IsAutForm φ) → ∀ (X : Matrix (Fin N) (Fin N) (Cinf E)) (φ ψ : W), inner ℂ (toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩) (toL2ₗ μ W h ψ) = - inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩) := by
  intro E _ _ _ N μ _ _ W h hW hA X φ ψ
  exact inner_lie_eq_neg_inner_lie μ W h hW hA X φ ψ

end GlobalTheory.LieSkew
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.LFun

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem invT_val_eq (g : GA E a) : (invT a (Ad E) g).val = (g.valᵀ)⁻¹ := by
  change (g⁻¹).valᵀ = _
  rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv]

theorem invT_scalar {R : Type} [CommRing R] (z : Rˣ) :
    invT a R (GeneralLinearGroup.scalar (Fin a) z) = GeneralLinearGroup.scalar (Fin a) z⁻¹ := by
  apply Units.ext
  change ((GeneralLinearGroup.scalar (Fin a) z)⁻¹).valᵀ = _
  rw [← map_inv]
  ext i j
  by_cases h : i = j
  · subst h; simp [GeneralLinearGroup.scalar]
  · simp [GeneralLinearGroup.scalar, h, Ne.symm h]

namespace CuspSub

variable (π : CuspSub E a)

def contra : CuspSub E a := UpperTheory.V.TC.dual π

variable {π} {π' : CuspSub E a}

theorem HasCentral.contra {ω : HChar E} (h : π.HasCentral ω) : π.contra.HasCentral ω⁻¹ := by
  rintro z _ ⟨ψ, hψ, rfl⟩
  change rt E a _ (UpperTheory.V.TC.dualFn E a ψ) = _ • UpperTheory.V.TC.dualFn E a ψ
  rw [UpperTheory.V.TC.rt_dualFn, invT_scalar, h z⁻¹ ψ hψ, map_smul]
  congr 1
  simp

theorem IsUnitary.contra (h : π.IsUnitary) : π.contra.IsUnitary := by
  obtain ⟨ω, h1, h2⟩ := h
  exact ⟨ω⁻¹, h1.inv, h2.contra⟩

end CuspSub

namespace CG

end CG

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
  GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.ConjLocal

section DdR

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem finrank_DdR_congr : finrank LL ↥(DdR PD ρ) = finrank LL ↥(DdR PD ρ') := by
  let E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have hD : DdR PD ρ = (DdR PD ρ').comap (E : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR) := by
    ext x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  rw [hD]
  exact (E.ofSubmodule' (DdR PD ρ')).finrank_eq

end DdR

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {a : ℕ}

theorem exists_ext_entries (L₁ : FinExt l) (A : GL (Fin a) (Om l)) :
    ∃ L₂ : FinExt l, L₁.1 ≤ L₂.1 ∧ (∀ i j, (A : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L₂.1) ∧
      ∀ i j, ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L₂.1 := by
  let f : Bool × Fin a × Fin a → Om l := fun p => if p.1 then (A : Matrix (Fin a) (Fin a) (Om l)) p.2.1 p.2.2
    else ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) p.2.1 p.2.2
  have hfin : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨supExt L₁ ⟨_, hfin⟩, le_sup_left, fun i j => ?_, fun i j => ?_⟩
  · exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (Set.range f) ≤ L₁.1 ⊔ _)
      (IntermediateField.subset_adjoin _ _ ⟨(true, i, j), rfl⟩)
  · exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (Set.range f) ≤ L₁.1 ⊔ _)
      (IntermediateField.subset_adjoin _ _ ⟨(false, i, j), rfl⟩)

theorem repE_apply (L : FinExt l) (r : ↥Gw →* GL (Fin a) ↥L.1) (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L r g x = ((r (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1).mulVec x := by
  simp [LocBridge.repE, Matrix.toLinAlgEquiv'_apply]


variable {Bw} in
theorem exists_conj_model {r r' : ↥Gw →* GL (Fin a) (Om l)} (A : GL (Fin a) (Om l))
    (hc : ∀ g, r' g = A * r g * A⁻¹) {L₁ : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L₁.1}
    (h₁ : IsModel Bw r L₁ r₁) :
    ∃ (L₂ : FinExt l) (hL : L₁.1 ≤ L₂.1) (r₂ : ↥Gw →* GL (Fin a) ↥L₂.1), IsModel Bw r' L₂ r₂ ∧
      ∃ e : (Fin a → ↥L₂.1) ≃ₗ[↥L₂.1] (Fin a → ↥L₂.1), ∀ g x,
        e (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x) =
          Bw.repE L₂ r₂ g (e x) := by
  obtain ⟨L₂, hL, hA, hB⟩ := exists_ext_entries L₁ A
  let A₂ : Matrix (Fin a) (Fin a) ↥L₂.1 := fun i j => ⟨_, hA i j⟩
  let B₂ : Matrix (Fin a) (Fin a) ↥L₂.1 := fun i j => ⟨_, hB i j⟩
  let f : ↥L₂.1 →+* Om l := algebraMap ↥L₂.1 (Om l)
  have fA : f.mapMatrix A₂ = (A : Matrix (Fin a) (Fin a) (Om l)) := rfl
  have fB : f.mapMatrix B₂ = ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := rfl
  have inj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L₂.1 → Matrix (Fin a) (Fin a) (Om l)) :=
    Matrix.map_injective Subtype.val_injective
  have h1 : A₂ * B₂ = 1 := inj (by rw [map_mul, map_one, fA, fB, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : B₂ * A₂ = 1 := inj (by rw [map_mul, map_one, fA, fB, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  let U : GL (Fin a) ↥L₂.1 := ⟨A₂, B₂, h1, h2⟩
  refine ⟨L₂, hL, (MulAut.conj U).toMonoidHom.comp
    (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁), ?_, ?_⟩
  · refine ⟨h₁.1.trans hL, ?_⟩
    ext g i j
    rw [hc g, ← h₁.2]
    change (f.mapMatrix (A₂ * ((IntermediateField.inclusion hL).toRingHom.mapMatrix
        ((r₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1)) * B₂)) i j =
      ((A : Matrix (Fin a) (Fin a) (Om l)) * (algebraMap ↥L₁.1 (Om l)).mapMatrix
        ((r₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1) *
        ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) i j
    rw [map_mul, map_mul, fA, fB]
    rfl
  · refine ⟨Formalism.MainNotions.N.K.Norm.matEquiv A₂ B₂ h1 h2, fun g x => ?_⟩
    rw [Formalism.MainNotions.N.K.Norm.matEquiv_apply, Formalism.MainNotions.N.K.Norm.matEquiv_apply, repE_apply, repE_apply]
    change A₂.mulVec (Matrix.mulVec _ x) = Matrix.mulVec (A₂ * _ * B₂) (A₂.mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem local_conj : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Gw : Subgroup (Ω ≃ₐ[E] Ω))
    (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r r' : ↥Gw →* GL (Fin a) (Om l)) (A : GL (Fin a) (Om l)),
    (∀ g, r' g = A * r g * A⁻¹) → (IsdRAt P Bw r → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw r') ∧
      (IsPotCrysAt P Bw r → IsPotCrysAt P Bw r') ∧
      ∀ (τ : E →+* Om l) (J : Multiset ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw r' τ J := by
  intro l _ P E Ω _ _ _ _ O _ _ _ Gw Bw a r r' A hc
  have dR : ∀ {L₁ L₂ : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L₁.1} (hL : L₁.1 ≤ L₂.1)
      (r₂ : ↥Gw →* GL (Fin a) ↥L₂.1) (e : (Fin a → ↥L₂.1) ≃ₗ[↥L₂.1] (Fin a → ↥L₂.1)),
      (∀ g x, e (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x) =
          Bw.repE L₂ r₂ g (e x)) → Bw.IsdRE P L₁ r₁ → Bw.IsdRE P L₂ r₂ := by
    intro L₁ L₂ r₁ hL r₂ e he hd
    have h := (local_ext P Bw hL r₁).2.1.2 hd
    unfold LocBridge.IsdRE at h ⊢
    rw [← finrank_DdR_congr (P.PD Bw.Kw) e he, h]
  refine ⟨fun ⟨L₁, r₁, h₁, hd⟩ => ?_, fun ⟨L₁, r₁, h₁, hd⟩ => ?_, fun ⟨L₁, r₁, h₁, hd⟩ => ?_,
    fun τ J ⟨L₁, r₁, h₁, hd, τ₁, hτ, hJ⟩ => ?_⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    exact ⟨L₂, r₂, hm, dR hL r₂ e he hd⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    exact ⟨L₂, r₂, hm, Formalism.MainNotions.N.K.Norm.isCrys_congr (P.PD Bw.Kw) e he ((local_ext P Bw hL r₁).1.2 hd)⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    obtain ⟨K', hK, hcr⟩ := (local_ext P Bw hL r₁).2.2.1.2 hd
    exact ⟨L₂, r₂, hm, K', hK, Formalism.MainNotions.N.K.Norm.isCrys_congr (P.PD K') e (fun g x => he _ x) hcr⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    refine ⟨L₂, r₂, hm, dR hL r₂ e he hd, (IntermediateField.inclusion hL).comp τ₁, fun x => hτ x, fun n => ?_⟩
    rw [hJ n, ← (local_ext P Bw hL r₁).2.2.2 τ₁ n]
    exact Formalism.MainNotions.N.K.Norm.multV_congr (P.PD Bw.Kw) e he _ n

end GlobalTheory.ConjLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApply
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem schurSquareMatrixToBlocks_blockDiagonal_one {R : Type} [CommRing R] (m r : ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    blk (GroundTheory.Automorphic.FourierWhittaker.blockMat (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      Matrix.fromBlocks h 0 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blk, eqv, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, Matrix.one_apply, Fin.ext_iff]
  all_goals
    have hi := i.isLt
    have hj := j.isLt
    try intro
    split_ifs <;> first | rfl | (exfalso; omega) | omega

theorem schurF_blockGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ)
    (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (h : GA E (m + 1)) :
    schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      β h * b₁ 1 * (χ 0 : ℂ) := by
  classical
  have hb := schurSquareMatrixToBlocks_blockDiagonal_one (R := Ad E) m r (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))
  have hD : Dof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 1 := by
    rw [Dof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₂]
  have hA : Aof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = h := by
    rw [Aof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₁]
  have hB : Bof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Bof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₂]
  have hC : Cof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Cof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₁]
  have hmk : mkGL (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) = h :=
    Units.ext (coe_mkGL (Matrix.isUnits_det_units h))
  have hmk1 : mkGL (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) = 1 :=
    Units.ext (by rw [coe_mkGL (by simp)]; rfl)
  have hpsi : psi (0 : Ad E) = 1 := by
    simp [psi]
  have hchi : chiF (m := m) (r := r) χ 0 = (χ 0 : ℂ) := by
    have h0 : (fun i j => pInf E ((0 : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) i j)) = 0 := by
      funext i j; simp
    rw [chiF, h0]
    simp [zero_mem]
  rw [schurF, if_pos (by rw [hD]; simp), Xof, Scof, Yof, hA, hB, hC, hD]
  simp only [inv_one, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, sub_zero, Matrix.zero_apply]
  rw [hpsi, hmk, hmk1, hchi, one_mul]

end GlobalTheory.SchurExt
end

