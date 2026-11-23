module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0308
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureSimilitude
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SimTheta

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mem_UJ_smul_iff (s : A →+* A) (J : Matrix n n A) (c d : A) (hdc : d * c = 1) (u : GL n A) :
    u ∈ UJ s (c • J) ↔ u ∈ UJ s J := by
  have hscale : cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) =
      c • (cT s (u : Matrix n n A) * J * (u : Matrix n n A)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · intro h
    have h' : cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) = c • J := h
    rw [hscale] at h'
    change cT s (u : Matrix n n A) * J * (u : Matrix n n A) = J
    have h2 := congrArg (fun B : Matrix n n A => d • B) h'
    simpa only [smul_smul, hdc, one_smul] using h2
  · intro h
    have h' : cT s (u : Matrix n n A) * J * (u : Matrix n n A) = J := h
    change cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) = c • J
    rw [hscale, h']

theorem conj_mem (s : A →+* A) (J : Matrix n n A) (G : GL n A) (c d : A) (hdc : d * c = 1)
    (hG : cT s (G : Matrix n n A) * J * (G : Matrix n n A) = c • J) (u : GL n A) (hu : u ∈ UJ s J) :
    G * u * G⁻¹ ∈ UJ s J := by
  refine GlobalTheory.CompanionTheory.SW.HIsom.conj_mem_UJ s J G u ?_
  rw [hG]
  exact (mem_UJ_smul_iff s J c d hdc u).2 hu

theorem conj_inv_mem (s : A →+* A) (J : Matrix n n A) (G : GL n A) (c d : A) (hdc : d * c = 1)
    (hG : cT s (G : Matrix n n A) * J * (G : Matrix n n A) = c • J) (u : GL n A) (hu : u ∈ UJ s J) :
    G⁻¹ * u * G ∈ UJ s J := by
  have h := GlobalTheory.CompanionTheory.SW.HIsom.conj_inv_mem_UJ s J G u hu
  rw [hG] at h
  exact (mem_UJ_smul_iff s J c d hdc _).1 h

end Generic

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem JR_smul (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (c : E)
    (J : Matrix (Fin M) (Fin M) E) :
    JR (F := F) R (c • J) = inclR (F := F) R c • JR (F := F) R J := by
  ext i j
  simp [JR, Matrix.map_apply]

theorem gramE_smul (σ : E →ₐ[F] E) {M n : ℕ} (c : E) (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) : gramE σ (c • J) X = c • gramE σ J X := by
  ext a b
  simp only [gramE, hE, hform, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def gramEquiv (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E) (c : E)
    (hc : c ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = c • J)
    (T : Matrix (Fin n) (Fin n) E) :
    {X : Fin n → Fin M → E | gramE σ J X = T} ≃ {X : Fin n → Fin M → E | gramE σ J X = c • T} where
  toFun X := ⟨SWIsom.ratAct (g : Matrix (Fin M) (Fin M) E) X.1, by
    have := X.2
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [SWIsom.gramE_ratAct, hg, gramE_smul, this]⟩
  invFun Y := ⟨SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1, by
    have hY := Y.2
    simp only [Set.mem_setOf_eq] at hY ⊢
    have h1 : gramE σ J (SWIsom.ratAct (g : Matrix (Fin M) (Fin M) E)
        (SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1)) =
        c • gramE σ J (SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1) := by
      rw [SWIsom.gramE_ratAct, hg, gramE_smul]
    rw [SWIsom.ratAct_mul, Units.mul_inv, SWIsom.ratAct_one, hY] at h1
    exact (smul_right_injective _ hc h1).symm⟩
  left_inv X := by
    apply Subtype.ext
    change SWIsom.ratAct _ (SWIsom.ratAct _ X.1) = X.1
    rw [SWIsom.ratAct_mul, Units.inv_mul, SWIsom.ratAct_one]
  right_inv Y := by
    apply Subtype.ext
    change SWIsom.ratAct _ (SWIsom.ratAct _ Y.1) = Y.1
    rw [SWIsom.ratAct_mul, Units.mul_inv, SWIsom.ratAct_one]

end Alg

theorem unitaryConj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E)
    (l : F) (hl : l ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) =
      (algebraMap F E l) • J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    ∃ e : HA R σ J ≃ₜ* HA R σ J,
      (∀ u, HA.mat R σ J (e u) = bc (inclR R) g * HA.mat R σ J u * (bc (inclR R) g)⁻¹) ∧
      ∀ u, HA.mat R σ J (e u) ∈ HFin R σ J ↔ HA.mat R σ J u ∈ HFin R σ J := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.HIsom.isTopologicalRing_tens F E R
  set G : GL (Fin M) (R ⊗[F] E) := bc (inclR R) g with hG
  have hdcE : algebraMap F E l⁻¹ * algebraMap F E l = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hl, map_one]
  have hdcR : inclR (F := F) R (algebraMap F E l⁻¹) * inclR (F := F) R (algebraMap F E l) = 1 := by
    rw [← map_mul, hdcE, map_one]
  have hGR : cT (sigR R σ) (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = inclR (F := F) R (algebraMap F E l) • JR R J := by
    rw [← GlobalTheory.CompanionTheory.SW.HIsom.JR_conj R σ J g, hg, JR_smul]
  have h₁ : ∀ u ∈ HR R σ J, G * u * G⁻¹ ∈ HR R σ J := fun u hu =>
    conj_mem (sigR R σ) (JR R J) G _ _ hdcR hGR u hu
  have h₂ : ∀ u ∈ HR R σ J, G⁻¹ * u * G ∈ HR R σ J := fun u hu =>
    conj_inv_mem (sigR R σ) (JR R J) G _ _ hdcR hGR u hu
  refine ⟨GlobalTheory.CompanionTheory.SW.HIsom.conjHomeo _ _ G h₁ h₂, fun u => rfl, fun u => ?_⟩
  change G * HA.mat R σ J u * G⁻¹ ∈ HFin R σ J ↔ _
  constructor
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g⁻¹ * w * g, conj_inv_mem (σ : E →+* E) J g _ _ hdcE hg w hw, ?_⟩
    have : bc (inclR R) w = G * HA.mat R σ J u * G⁻¹ := hwu
    simp only [map_mul, map_inv, this, ← hG]
    group
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g * w * g⁻¹, conj_mem (σ : E →+* E) J g _ _ hdcE hg w hw, ?_⟩
    have : bc (inclR R) w = HA.mat R σ J u := hwu
    simp only [map_mul, map_inv, this, ← hG]

section Theta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem theta_map (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (g : GL (Fin M) E) (c : E) (hc : c ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = c • J)
    [LocallyCompactSpace (AF F)] [SecondCountableTopology (AF F)] [T2Space (AF F)]
    (He : HA (AF F) σ J ≃ᵐ HA (AF F) σ J)
    (hmat : ∀ u, HA.mat (AF F) σ J (He u) =
      bc (inclR (AF F)) g * HA.mat (AF F) σ J u * (bc (inclR (AF F)) g)⁻¹)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (T : Matrix (Fin n) (Fin n) E) :
    (thetaMeas σ J (μ.map He.symm) (He ⁻¹' 𝓕) {X | gramE σ J X = T}).map
        (actTup (AF F) (bc (inclR (AF F)) g)) =
      thetaMeas σ J μ 𝓕 {X | gramE σ J X = c • T} := by
  obtain ⟨tg, -, -, -, bs, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM M J hJ (AF F)
  haveI := tg
  haveI := bs
  haveI : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)).2.2.2.2.2.2.2.1 n M
  set G : GL (Fin M) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
  have hmG := SWIsom.measurable_actTup (n := n) σ hCM (AF F) G
  have hmf : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ Y := fun Y =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have hmass : (μ.map He.symm) (He ⁻¹' 𝓕) = μ 𝓕 := by
    rw [He.symm.map_apply]
    congr 1
    ext x
    simp
  have hrest : ((μ.map He.symm).restrict (He ⁻¹' 𝓕)).map He = μ.restrict 𝓕 := by
    rw [← He.restrict_map, Measure.map_map He.measurable He.symm.measurable]
    simp
  unfold thetaMeas
  rw [Measure.map_smul, hmass] <;> try exact hmG.aemeasurable
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Measure.map_sum hmG.aemeasurable, ← SWIsom.sum_reindex (gramEquiv σ J g c hc hg T)]
  congr 1
  funext X
  rw [Measure.map_map hmG (hmf _)]
  have hcomp : (actTup (AF F) G ∘ fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) =
      (fun h => actW (AF F) σ J h⁻¹
        (ratTup (AF F) ((gramEquiv σ J g c hc hg T X : _) : Fin n → Fin M → E))) ∘ He := by
    funext h
    have := SWIsom.act_conj (AF F) σ G He hmat h (ratTup (AF F) (X : Fin n → Fin M → E))
    simp only [Function.comp]
    rw [this, ← SWIsom.ratTup_ratAct]
    rfl
  rw [hcomp, ← Measure.map_map (hmf _) He.measurable, hrest]

end Theta

theorem theta_simil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (γ : GL (Fin M) E) (l : F), l ≠ 0 → cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J → ∃ (μ' : Measure (HA (AF F) σ J)) (𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ' ∧ IsFDH F E σ M J μ' 𝓕' ∧ ∀ (n : ℕ) (T T' : Matrix (Fin n) (Fin n) E), T' = (algebraMap F E l) • T → (thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T}).map (actTup (AF F) (bc (inclR (AF F)) γ)) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T'} := by
  intro F E _ _ _ _ _ σ hCM M J hJ μ 𝓕 hμ h𝓕 γ l hl hγ
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨e, hmat, hrat⟩ := unitaryConj F E σ hCM M J γ l hl hγ (AF F)
  obtain ⟨tg, -, -, -, bs, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM M J hJ (AF F)
  haveI := tg
  haveI := bs
  haveI : μ.IsHaarMeasure := hμ
  let He := e.toHomeomorph.toMeasurableEquiv
  have hμ' : IsHaarH F E σ M J (μ.map He.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  have hmm : (μ.map He.symm).map He = μ := by
    rw [Measure.map_map He.measurable He.symm.measurable]
    simp
  have hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ :=
    (MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving
  have h𝓕' : IsFDH F E σ M J (μ.map He.symm) (He ⁻¹' 𝓕) :=
    SWIsom.isFD_pull σ e.toMulEquiv hrat hq h𝓕
  have hc : algebraMap F E l ≠ 0 := by
    simpa using hl
  refine ⟨_, _, hμ', h𝓕', ?_⟩
  intro n T T' hT'
  subst hT'
  exact theta_map σ hCM J hJ γ _ hc hγ He hmat μ 𝓕 T

end GlobalTheory.CompanionTheory.SW.SimTheta
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedGradedGenerationGlobalSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

lemma restrictTop_top_self {X : Scheme.{0}} (r : Γ(X, ⊤)) : restrictTop (⊤ : X.Opens) r = r := by
  change (X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom r = r
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]
  rfl

lemma twist_map_comp_app {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {F G K : X.Modules}
    (φ : F ⟶ G) (ψ : G ⟶ K) (V : X.Opens) (s : Γ(GlobalTheory.twist F L, V)) :
    (GlobalTheory.Twist.map L (φ ≫ ψ)).app V s = (GlobalTheory.Twist.map L ψ).app V ((GlobalTheory.Twist.map L φ).app V s) := by
  rw [GlobalTheory.Twist.map_comp]
  rfl

lemma smul_mem_twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (e : ℕ) {a : A} (ha : a ∈ I)
    {m : Γ(GlobalTheory.twistZ P H n, ⊤)} (hm : m ∈ twPow I H n P e) :
    toFunctions (X := X) (A := A) ⊤ a • m ∈ twPow I H n P (e + 1) := by
  have hm' : m ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ e) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) := hm
  change _ ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))
  have hmem : toFunctions (X := X) (A := A) ⊤ a ∈ Ideal.map (toFunctions (X := X) (A := A) ⊤) I :=
    Ideal.mem_map_of_mem _ ha
  rw [pow_succ', Ideal.map_mul, mul_smul]
  exact Submodule.smul_mem_smul hmem hm'

theorem lifts_succ : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), (∀ i, g i ∈ I) → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (n : ℤ) (e : ℕ), Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) = ⊤ → Lifts I H hS n e → Lifts I H hS n (e + 1) := by
  intro A _ _ I X _ H P S hS k g hg hr n e hspan hL y
  have hy : y ∈ Submodule.span Γ(X, ⊤) (⋃ i, Set.range
      ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) := by
    rw [hspan]; trivial
  have hsub : ∀ m : ℕ, ∀ a b : Γ(GlobalTheory.twistZ P H n, ⊤), a ∈ twPow I H n P m → b ∈ twPow I H n P m →
      a + b ∈ twPow I H n P m := fun m a b ha hb =>
    Submodule.add_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ha hb
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, y', rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨c', rfl, hc'⟩ := hL y'
    refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (mulLvl (hr i) e)).app ⊤ c', ?_, ?_⟩
    · rw [← twist_map_comp_app, ← twist_map_comp_app, grπ_grT]
    · rw [← twist_map_comp_app, mulLvl_arrow, twist_map_comp_app, twist_smulHom_app,
        restrictTop_top_self]
      exact smul_mem_twPow I H n P e (hg i) hc'
  | zero =>
    refine ⟨0, map_zero _, ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))
  | add x y _ _ hx hy =>
    obtain ⟨c₁, rfl, h₁⟩ := hx
    obtain ⟨c₂, rfl, h₂⟩ := hy
    refine ⟨c₁ + c₂, map_add _ _ _, ?_⟩
    rw [map_add (f := _)]
    exact hsub _ _ _ h₁ h₂
  | smul a x _ hx =>
    obtain ⟨c, rfl, h⟩ := hx
    refine ⟨a • c, Scheme.Modules.Hom.app_smul _ _ _, ?_⟩
    rw [Scheme.Modules.Hom.app_smul]
    exact Submodule.smul_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) a h

end GlobalTheory.CompanionTheory.GE.Step
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsFiniteGenerators
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.TwLim

theorem twSecs_sub_mem {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    (S : Subobject P) {x y : Γ(GlobalTheory.twistZ P H n, ⊤)} (hx : x ∈ twSecs H n S)
    (hy : y ∈ twSecs H n S) : x - y ∈ twSecs H n S := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, map_sub _ a b⟩

theorem twSecs_mono {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    {S T : Subobject P} (h : S ≤ T) : twSecs H n S ⊆ twSecs H n T := by
  rintro _ ⟨a, rfl⟩
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (Subobject.ofLE S T h)).app ⊤ a, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← GlobalTheory.Twist.map_comp,
    Subobject.ofLE_arrow]

theorem zero_mem_twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ) : (0 : Γ(GlobalTheory.twistZ P H n, ⊤)) ∈ twPow I H n P m :=
  Submodule.zero_mem _

end GlobalTheory.CompanionTheory.GE.TwLim

namespace GlobalTheory.CompanionTheory.GE.TwLim

theorem twPow_sub_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ), twPow I H n P m ⊆ twSecs H n (powSub I P m) := _root_.GlobalTheory.CompanionTheory.GE.twPow_subset_twSecs

theorem twPow_complete : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := _root_.GlobalTheory.CompanionTheory.GE.exists_limit_twPow

theorem antitone_closedSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} {S : ℕ → Subobject P} (hS : ClosedSys I P S) :
    Antitone S :=
  antitone_nat_of_succ_le fun m => (hS.succ m).symm ▸ le_sup_left

theorem exists_compat_limit : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ n : ℤ, (∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1)) → ∃ W : Set Γ(GlobalTheory.twistZ P H n, ⊤), (∀ e, W ⊆ twSecs H n (S e)) ∧ ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W, x - b ∈ twPow I H n P (e + 1) := by
  intro A _ _ I hI X _ _ H hH P hP S hS n hstep
  refine ⟨⋂ e, twSecs H n (S e), fun e => Set.iInter_subset _ e, ?_⟩
  intro e x hx
  have hpow : ∀ m, twPow I H n P (m + 1) ⊆ twSecs H n (S m) := fun m =>
    (twPow_sub_twSecs I H hH hP n (m + 1)).trans (twSecs_mono H n (hS.pow_le m))
  let seq : ∀ k : ℕ, {y // y ∈ twSecs H n (S (e + k))} := fun k =>
    Nat.rec ⟨x, hx⟩ (fun k y => ⟨(hstep (e + k) y.1 y.2).choose, (hstep (e + k) y.1 y.2).choose_spec.1⟩) k
  have hseq : ∀ k, (seq k).1 - (seq (k + 1)).1 ∈ twPow I H n P (e + k + 1) := fun k =>
    (hstep (e + k) (seq k).1 (seq k).2).choose_spec.2
  have hcg : ∀ a b : ℕ, a = b → (seq a).1 = (seq b).1 := by rintro _ _ rfl; rfl
  have hs0 : (seq 0).1 = x := rfl
  let f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤) := fun j => (seq (j - (e + 1))).1
  have hf : ∀ j, f j - f (j + 1) ∈ twPow I H n P j := by
    intro j
    by_cases hj : j < e + 1
    · have h1 : f j = f (j + 1) := hcg _ _ (by omega)
      rw [h1, sub_self]
      exact zero_mem_twPow I H n P j
    · obtain ⟨k, rfl⟩ : ∃ k, j = e + 1 + k := ⟨j - (e + 1), by omega⟩
      have h1 : f (e + 1 + k) = (seq k).1 := hcg _ _ (by omega)
      have h2 : f (e + 1 + k + 1) = (seq (k + 1)).1 := hcg _ _ (by omega)
      rw [h1, h2]
      have := hseq k
      rwa [show e + k + 1 = e + 1 + k by omega] at this
  obtain ⟨L, hL⟩ := twPow_complete I hI H hH hP n f hf
  have hk : ∀ k, L ∈ twSecs H n (S (e + k)) := by
    intro k
    have h1 : f (e + k + 1) = (seq k).1 := hcg _ _ (by omega)
    have hd : (seq k).1 - L ∈ twSecs H n (S (e + k)) := h1 ▸ hpow (e + k) (hL (e + k + 1))
    have := twSecs_sub_mem H n _ (seq k).2 hd
    rwa [sub_sub_cancel] at this
  refine ⟨L, Set.mem_iInter.2 fun m => ?_, ?_⟩
  · rcases le_or_gt e m with hm | hm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact hk k
    · exact twSecs_mono H n (antitone_closedSys I hS hm.le) (by simpa using hk 0)
  · have h1 : f (e + 1) = x := (hcg (e + 1 - (e + 1)) 0 (by omega)).trans hs0
    simpa [h1] using hL (e + 1)

end GlobalTheory.CompanionTheory.GE.TwLim
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedVanishingSectionsSpan
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE

theorem span_range_twist_eq_top : ∀ {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X), L.IsLB →
    ∀ {k : ℕ} {P : Fin k → X.Modules} {Q K : X.Modules} (f : ∀ i, P i ⟶ Q) (ι : K ⟶ ⨁ P)
      (w : ι ≫ biproduct.desc f = 0), (ShortComplex.mk ι (biproduct.desc f) w).ShortExact →
      Subsingleton (GlobalTheory.coh (GlobalTheory.twist K L) 1) →
      Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map L (f i)).app ⊤)) = ⊤ := by
  intro X L hL k P Q K f ι w hS hK
  have hsurj := GlobalTheory.cohOn.app_surjective (GlobalTheory.Twist.shortExact_map hL hS) ⊤ hK
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  have hg : (ShortComplex.map (ShortComplex.mk ι (biproduct.desc f) w) (GlobalTheory.twistFunctor L)).g =
      ∑ i, GlobalTheory.Twist.map L (biproduct.π P i) ≫ GlobalTheory.Twist.map L (f i) := by
    show (GlobalTheory.twistFunctor L).map (biproduct.desc f) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [biproduct.desc_eq, Functor.map_sum]
    rfl
  let e : (GlobalTheory.twist (⨁ P) L ⟶ GlobalTheory.twist Q L) →+ Γ(GlobalTheory.twist Q L, ⊤) :=
    { toFun := fun φ => (φ.app ⊤) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have key : ((ShortComplex.map (ShortComplex.mk ι (biproduct.desc f) w) (GlobalTheory.twistFunctor L)).g.app ⊤) x =
      ∑ i, ((GlobalTheory.Twist.map L (f i)).app ⊤) (((GlobalTheory.Twist.map L (biproduct.π P i)).app ⊤) x) := by
    rw [hg]
    exact map_sum e _ _
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span (Set.mem_iUnion.2 ⟨i, ?_⟩)
  exact ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.GE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformSpanEventually
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Uniform

theorem span_range_eq_top_iff_surjective {X : Scheme.{0}} {k : ℕ} {A B : X.Modules}
    (T : Fin k → (A ⟶ B)) (U : X.Opens) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U)) = ⊤ ↔
      Function.Surjective ((biproduct.desc T).app U) := by
  have hι : ∀ i (z : Γ(A, U)),
      (biproduct.desc T).app U ((biproduct.ι (fun _ : Fin k => A) i).app U z) = (T i).app U z := by
    intro i z
    rw [← GlobalTheory.QCoh.appLinear_apply, ← GlobalTheory.QCoh.appLinear_apply, ← LinearMap.comp_apply,
      ← GlobalTheory.QCoh.appLinear_comp, biproduct.ι_desc, GlobalTheory.QCoh.appLinear_apply]
  constructor
  · intro h y
    have hy : y ∈ Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U)) := h ▸ Submodule.mem_top
    have hle : Submodule.span Γ(X, U) (⋃ i, Set.range ((T i).app U)) ≤
        LinearMap.range (GlobalTheory.QCoh.appLinear (biproduct.desc T) U) := by
      rw [Submodule.span_le]
      intro w hw
      obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.1 hw
      exact ⟨(biproduct.ι (fun _ : Fin k => A) i).app U z, by rw [GlobalTheory.QCoh.appLinear_apply, hι]⟩
    obtain ⟨x, hx⟩ := hle hy
    exact ⟨x, hx⟩
  · intro h
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := h y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [biproduct_app_eq_sum (fun _ : Fin k => A) U x, ← GlobalTheory.QCoh.appLinear_apply, map_sum]
    refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
      (Set.mem_iUnion.2 ⟨i, (biproduct.π (fun _ : Fin k => A) i).app U x, ?_⟩)
    rw [GlobalTheory.QCoh.appLinear_apply, hι]

theorem span_range_eq_top_uniform : ∀ {X : Scheme.{0}} [CompactSpace X] {k : ℕ}
    {K : ℕ → X.Modules} (T : Fin k → ∀ e, K e ⟶ K (e + 1)), (∀ e, (K e).IsQuasicoherent) →
    (∀ U : X.affineOpens, ∃ dU : ℕ, ∀ e, dU ≤ e →
      Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤) →
    ∃ d' : ℕ, ∀ e, d' ≤ e → ∀ U : X.affineOpens,
      Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤ := by
  intro X _ k K T hq hgen
  obtain ⟨ι, _, 𝒰, haff, hcov⟩ := GlobalTheory.QCoh.exists_finite_affine_cover_of_isCompact (X := X)
    (W := ⊤) (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  choose dU hdU using fun i => hgen ⟨𝒰 i, haff i⟩
  refine ⟨Finset.univ.sup dU, fun e he U => ?_⟩
  haveI := hq e
  haveI := hq (e + 1)
  have hepi : Epi (biproduct.desc fun i => T i e) := by
    rw [GlobalTheory.QCoh.epi_iff_affineCover 𝒰 hcov.symm haff]
    intro i
    exact (span_range_eq_top_iff_surjective (fun j => T j e) (𝒰 i)).1
      (hdU i e ((Finset.le_sup (f := dU) (Finset.mem_univ i)).trans he))
  exact (span_range_eq_top_iff_surjective (fun j => T j e) U).2
    (GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen _ U.2)

end GlobalTheory.CompanionTheory.GE.Uniform
end
end

