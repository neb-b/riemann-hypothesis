module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0639
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh

namespace GlobalTheory.DiscreteSpectrumCM

theorem isUnitarisable_of_injective {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (q : ρ.IntertwiningMap τ)
    (hq : Function.Injective q) (hu : IsUnitarisable τ) : IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := hu
  let B' : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ := (B.compl₂ q.toLinearMap).comp q.toLinearMap
  have hB : ∀ v w, B' v w = B (q v) (q w) := fun _ _ => rfl
  refine ⟨B', fun v w => by rw [hB, hB, h1], fun v hv => by
    rw [hB]; exact h2 _ fun e => hv (hq (e.trans (map_zero q).symm)), fun g v w => ?_⟩
  rw [hB, hB, ← h3 g (q v) (q w)]
  rw [q.isIntertwining _ _ g v, q.isIntertwining _ _ g w]

section Local

open GlobalTheory.PRep GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem injective_of_irreducible {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (hi : ρ.IsIrreducible)
    (q : ρ.IntertwiningMap τ) (h0 : q.toLinearMap ≠ 0) : Function.Injective q := by
  rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hi).2 (LinearMap.ker q.toLinearMap) (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    change q (ρ g v) = 0
    rw [q.isIntertwining _ _ g v]
    change τ g (q.toLinearMap v) = 0
    rw [hv, map_zero]) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

theorem isUnitarisable_of_isSpeh_one {a : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GL (Fin a) k) X} (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    {τ : Representation ℂ (GL (Fin a) k) Y} (h : IsSpeh (IrrGL.of ρ hs hi) 1 τ) (hu : IsUnitarisable τ) :
    IsUnitarisable ρ := by
  obtain ⟨hd, hτ, p, hp, -⟩ := h
  have key : ∀ y : Fin 1 → IrrGL (k := k), y = (fun _ => IrrGL.of ρ hs hi) → ∀ hd : ∑ i, (y i).1 = a,
      Nonempty ((IrrGL.of ρ hs hi).rep.Equiv (prodIrr y hd)) := by
    rintro _ rfl hd
    exact nonempty_equiv_prodIrr_one _ hd
  obtain ⟨e⟩ := key _ (funext fun _ => by simp [spehFactor]) hd
  let q : ρ.IntertwiningMap τ := p.comp (e.toIntertwiningMap.comp (IrrGL.equivOf ρ hs hi).toIntertwiningMap)
  have hq : Function.Surjective q :=
    hp.comp (e.toLinearEquiv.surjective.comp (IrrGL.equivOf ρ hs hi).toLinearEquiv.surjective)
  refine isUnitarisable_of_injective q (injective_of_irreducible hi q fun h0 => ?_) hu
  have : Nontrivial Y := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hτ).1
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨v, rfl⟩ := hq y
  exact hy (LinearMap.congr_fun h0 v)

end Local

section Speh

open GlobalTheory.PRep GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E]

theorem isSpehQuot_of_isSpeh {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a)
    (σ' : LocIrr w N) (hs : IsSpeh (IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ) : IsSpehQuot h σ σ' := by
  obtain ⟨hd, -, p, hp, -⟩ := hs
  let T : ∀ i : Fin d, (twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans
      ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  exact ⟨p.comp M.toIntertwiningMap, hp.comp M.toLinearEquiv.surjective⟩

end Speh

section Inf

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem hasInfCharGL_unique {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (h : HasInfCharGL V τ m) (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

end Inf

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  simp only [GlobalTheory.SphGal.spehInf, GlobalTheory.DefiniteBC.spehInf]
  rw [← List.sum_ofFn, ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
  rfl

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.DiscreteSpectrumCM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianGraphsSumEqMatrixCoeffIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem graph_term_of_termMove {D : D7} (hTM : TermMove D) {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)}
    {𝓗 : Set (GA D V)} {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) {γ : GA D W} (hγ : γ ∈ GQ W) {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hc : mt W γ = c.map (incA D)) {Y : Lag W} (hY : IsLagFrame W Y (1, c)) (g₁ g₂ : GA D W) :
    lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂) = thetaIP μ 𝓕 (om (1, g₁⁻¹ * γ⁻¹ * g₂) f₂) f₁ := by
  have hmul : ∀ p q (f : WO V W → ℂ), om p (om q f) = om (p * q) f := fun p q f => by rw [map_mul]; rfl
  have p₁ := hS.weil.om_pres (1, g₁) f₁ h₁
  have p₂ := hS.weil.om_pres (1, g₂) f₂ h₂
  obtain ⟨hfr, hg⟩ := hTM ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ _ p₁ p₂
  have e1 : om (1, g₁⁻¹) (om (1, γ⁻¹) (om (1, g₂) f₂)) = om (1, g₁⁻¹ * γ⁻¹ * g₂) f₂ := by
    rw [hmul, hmul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, one_mul, mul_assoc]
  have e2 : om (1, g₁⁻¹) (om (1, g₁) f₁) = f₁ := by
    rw [hmul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  rw [← hfr Y (1, c) hY, (hg γ hγ c hc).2,
    ← _root_.GlobalTheory.WeilPairing.thetaInner_weilRep D ψ V W χV χW om μ 𝓕 hS.weil hS.covol (1, g₁⁻¹) _ _ (hS.weil.om_pres (1, γ⁻¹) _ p₂) p₁, e1, e2]


open scoped GlobalTheory.GaugeEx in
theorem rallis_graphs : ∀ D : D7, EisAbs D → TermMove D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧ ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW := by
  intro D hEA hTM ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ ha₁ hc₁ ha₂ hc₂
  haveI := hS.haarW
  obtain ⟨e, he⟩ := _root_.GlobalTheory.RawLift.Graphs.graphs D W
  haveI : Countable (Lag W) := _root_.GlobalTheory.RawLift.lag_countable D W
  haveI : Countable (GQ W) := e.injective.countable
  choose c hc hcf using he
  let P : GA D W → ℂ := fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁
  have hT : ∀ (γ : GQ W) (p : GA D W × GA D W),
      lagTerm μ 𝓕 (fr (e γ).1) (om (1, p.1) f₁) (om (1, p.2) f₂) = P (p.1⁻¹ * (γ : GA D W)⁻¹ * p.2) :=
    fun γ p => graph_term_of_termMove hTM hS hf₁ hf₂ γ.2 (hc γ) (hcf γ) p.1 p.2
  have hPm : StronglyMeasurable P := by
    have h := _root_.GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hS.weil hS.covol f₁ f₂ hf₁ hf₂ (1, 1)
    have hcont : Continuous fun g : GA D W => ((1 : GA D W), g) := continuous_const.prodMk continuous_id
    convert h.comp_measurable hcont.measurable using 1
    funext g
    simp only [Function.comp_apply]
    rw [lagTerm_one_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : GQ W, ‖P (g₁⁻¹ * (γ : GA D W)⁻¹ * g₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ ∂νW ∂νW ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hEA ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ hf₁ hf₂ φ₁ φ₂ ha₁ hc₁ ha₂ hc₂) ?_
    refine lintegral_mono fun g₁ => lintegral_mono fun g₂ => ?_
    have hinj : Function.Injective fun γ : GQ W => (e γ).1 := Subtype.val_injective.comp e.injective
    refine le_trans (le_of_eq ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun Y => ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ))
    refine tsum_congr fun γ => ?_
    rw [← hT γ (g₁, g₂)]
  obtain ⟨hI, hE⟩ := GlobalTheory.T.unfold_tsum_integral_fundamentalDomain νW (GQ W) 𝓖 hS.fdW φ₁ φ₂ P ha₁.cont ha₂.cont ha₂.left hPm hfin
  refine ⟨hI, ?_⟩
  refine ((e.tsum_eq (fun Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥} =>
    ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW))).symm.trans ?_).trans hE
  refine tsum_congr fun γ => ?_
  congr 1
  funext p
  rw [hT γ p]

end GlobalTheory.RawLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianStabilizerNormalizesFrameUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCusp

open GlobalTheory.MixModel

variable {D : D7}

theorem mem_span_cols {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (v : Fin n → D.host.E) :
    v ∈ Submodule.span D.host.E (Set.range I.transpose) ↔ ∃ a, I *ᵥ a = v := by
  change v ∈ Submodule.span D.host.E (Set.range I.col) ↔ _
  rw [← Matrix.range_mulVecLin]; rfl

theorem exists_mul_eq_mul {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (M : Matrix (Fin n) (Fin n) D.host.E)
    (h : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      M *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose)) :
    ∃ A : Matrix (Fin s) (Fin s) D.host.E, M * I = I * A := by
  have h1 : ∀ j, ∃ b, I *ᵥ b = M *ᵥ I.transpose j := fun j =>
    (mem_span_cols I _).1 (h _ (Submodule.subset_span ⟨j, rfl⟩))
  choose f hf using h1
  refine ⟨Matrix.of fun i j => f j i, ?_⟩
  refine Matrix.ext fun k j => ?_
  have := congrFun (hf j) k
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at this
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simpa using this.symm

theorem frame_gram_mul {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (J c c' : Matrix (Fin n) (Fin n) D.host.E)
    (hc : c * c' = 1) (hu : cᴴ * J * c = J) : Iᴴ * J * c = (c' * I)ᴴ * J := by
  have h1 : (c * c')ᴴ = 1 := by rw [hc, Matrix.conjTranspose_one]
  calc Iᴴ * J * c = Iᴴ * (c * c')ᴴ * J * c := by rw [h1, Matrix.mul_one]
    _ = Iᴴ * c'ᴴ * (cᴴ * J * c) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (c' * I)ᴴ * J := by rw [hu, Matrix.conjTranspose_mul]

theorem mul_mul_mul_eq_zero {R : Type} [CommRing R] {n s : ℕ} (C C' m : Matrix (Fin n) (Fin n) R)
    (I : Matrix (Fin n) (Fin s) R) (A' : Matrix (Fin s) (Fin s) R) (h : C' * I = I * A') (h0 : m * I = 0) :
    C * m * C' * I = 0 := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.mul_assoc C, h0, Matrix.mul_zero, Matrix.zero_mul]

theorem mul_mul_mul_eq_zero' {R : Type} [CommRing R] {n s : ℕ} (C C' m : Matrix (Fin n) (Fin n) R)
    (K : Matrix (Fin s) (Fin n) R) (A' : Matrix (Fin s) (Fin s) R) (h : K * C = A' * K) (h0 : K * m = 0) :
    K * (C * m * C') = 0 := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_assoc A', h0, Matrix.mul_zero, Matrix.zero_mul]


set_option maxHeartbeats 2000000 in
theorem conj_mem_NI : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ γ : GQ W, GlobalTheory.RallisCusp.lagAct W γ Y = Y → ∀ n ∈ NI W I, (γ : GA D W) * n * (γ : GA D W)⁻¹ ∈ NI W I := by
  intro D W Y s I _ hS γ hY n hn
  set c := gqMat W γ with hc_def
  set c' := gqMat W γ⁻¹ with hc'_def
  have hcc' : c * c' = 1 := gqMat_mul_inv W γ
  have hc'c : c' * c = 1 := gqMat_inv_mul W γ
  have memS : ∀ v, v ∈ Submodule.span D.host.E (Set.range I.transpose) ↔ ((v, 0) : _ × _) ∈ Y.1 := by
    intro v; rw [hS, Submodule.mem_comap, LinearMap.inl_apply]
  have memY : ∀ y, y ∈ Y.1 ↔ (c' *ᵥ y.1, y.2) ∈ Y.1 := by
    intro y; conv_lhs => rw [← hY]
    exact mem_lagAct W γ Y y
  have hcS : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      c *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose) := by
    intro v hv
    rw [memS, memY]
    simpa [Matrix.mulVec_mulVec, hc'c] using (memS v).1 hv
  have hc'S : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      c' *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose) := by
    intro v hv
    rw [memS]
    exact (memY _).1 ((memS v).1 hv)
  obtain ⟨A, hA⟩ := exists_mul_eq_mul I c' hc'S
  obtain ⟨B, hB⟩ := exists_mul_eq_mul I c hcS
  have hIc : Iᴴ * W.gram * c = Aᴴ * (Iᴴ * W.gram) := by
    rw [frame_gram_mul I W.gram c c' hcc' (gqMat_unitary W γ), hA, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hIc' : Iᴴ * W.gram * c' = Bᴴ * (Iᴴ * W.gram) := by
    rw [frame_gram_mul I W.gram c' c hc'c (gqMat_unitary W γ⁻¹), hB, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hrat : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), M.map (incA D) = rat M := fun _ => rfl
  have hγ : mt W (γ : GA D W) = rat c := (rat_gqMat W γ).symm
  have hγ' : mt W ((γ : GA D W)⁻¹) = rat c' := (rat_gqMat W γ⁻¹).symm
  have hle : NI W I ≤ (NI W I).comap (MulAut.conj (γ : GA D W)).toMonoidHom := by
    unfold NI
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨h1, h2, h3⟩ := hg
    apply Subgroup.subset_closure
    have hm : (matHom W ((MulAut.conj (γ : GA D W)).toMonoidHom g)).1 - 1 = rat c * ((matHom W g).1 - 1) * rat c' := by
      change mt W ((γ : GA D W) * g * (γ : GA D W)⁻¹) - 1 = rat c * (mt W g - 1) * rat c'
      rw [mt_mul, mt_mul, hγ, hγ', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← rat_mul, hcc', rat_one]
    rw [cT_sig, hrat] at h2 h3
    rw [hrat] at h1
    have hA' : rat c' ⬝ rat I = rat I ⬝ rat A := by rw [← rat_mul, hA, rat_mul]
    have hIc2 : rat (Iᴴ * W.gram) ⬝ rat c = rat Aᴴ ⬝ rat (Iᴴ * W.gram) := by rw [← rat_mul, hIc, rat_mul]
    have hB' : rat c ⬝ rat I = rat I ⬝ rat B := by rw [← rat_mul, hB, rat_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm, hrat]
      exact mul_mul_mul_eq_zero (rat c) (rat c') _ (rat I) (rat A) hA' h1
    · rw [hm, cT_sig, hrat]
      exact mul_mul_mul_eq_zero' (rat c) (rat c') _ (rat (Iᴴ * W.gram)) (rat Aᴴ) hIc2 h2
    · intro x hx
      rw [cT_sig] at hx
      have hx' : (Iᴴ * W.gram) *ᵥ (c' *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hIc', ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      obtain ⟨a, ha⟩ := h3 (c' *ᵥ x) hx'
      refine ⟨rat B *ᵥ a, ?_⟩
      have hv : rat c' *ᵥ (fun i => incA D (x i)) = fun i => incA D ((c' *ᵥ x) i) := by
        funext i; exact (RingHom.map_mulVec (incA D) c' x i).symm
      rw [hm, hrat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, ha, Matrix.mulVec_mulVec, hB',
        Matrix.mulVec_mulVec]
  exact hle hn

end GlobalTheory.RallisCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterTeichmullerLabelOfGoodTypes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.CharLabTransport

theorem teich_inv {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (c : (ZMod g)ˣ) :
    L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((c⁻¹ : (ZMod g)ˣ) : ZMod g)) =
      (L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (c : ZMod g)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem charLab_of_value {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ)
    (t : (ZMod g)ˣ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 →
      L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (t : ZMod g)) = ((θ u : ℂˣ) : ℂ) ∨
      L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (t : ZMod g)) = (((θ u)⁻¹ : ℂˣ) : ℂ)) :
    ∃ c : ZMod g, GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp θ) c ∧
      (c = (t : ZMod g) ∨ c = ((t⁻¹ : (ZMod g)ˣ) : ZMod g)) := by
  by_cases hex : ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1
  · obtain ⟨u₀, hu₀⟩ := hex
    have huniq : ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 → u = u₀ := by
      intro u hu
      apply Units.ext
      exact (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (hu.trans hu₀.symm)
    rcases hε with rfl | rfl <;> rcases h u₀ hu₀ with hv | hv
    · refine ⟨_, ⟨t.ne_zero, fun u hu => ?_⟩, Or.inl rfl⟩
      rw [huniq u hu, hv]; simp
    · refine ⟨_, ⟨(t⁻¹).ne_zero, fun u hu => ?_⟩, Or.inr rfl⟩
      rw [huniq u hu, teich_inv, hv]; simp
    · refine ⟨_, ⟨(t⁻¹).ne_zero, fun u hu => ?_⟩, Or.inr rfl⟩
      rw [huniq u hu, teich_inv, hv]; simp
    · refine ⟨_, ⟨t.ne_zero, fun u hu => ?_⟩, Or.inl rfl⟩
      rw [huniq u hu, hv]; simp
  · exact ⟨_, ⟨t.ne_zero, fun u hu => (hex ⟨u, hu⟩).elim⟩, Or.inl rfl⟩

theorem charLab_of_goodTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R → ∀ (k : Fin 2) (v : D.nd.PlG k) (i : Fin D.R.m) (PP : Pl D.host.E),
    R.C.P.Div k PP → ∀ (iso : ZMod (D.host.g k) ≃+* kP PP) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∃ c : ZMod (D.host.g k),
        GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) PP).comp
          (Units.map (iso : ZMod (D.host.g k) →* kP PP)))) c ∧
        (c = ((D.nd.chiT k v i : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) ∨
          c = (((D.nd.chiT k v i)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hg k v i PP hdiv iso ε hε
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨L, -, hser, hchi⟩ := hg k
  refine ⟨L, hser, ?_⟩
  apply charLab_of_value L _ _ ε hε
  intro u hu
  have h1 : (((u : ZMod (D.host.g k)).val : ℕ) : ZMod (D.host.g k)) = u := ZMod.natCast_zmod_val _
  refine hchi v i PP hdiv (u : ZMod (D.host.g k)).val
    (Units.map (iso : ZMod (D.host.g k) →* kP PP) u) ?_ ?_
  · rw [← hu, ← map_natCast (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))), h1]
  · rw [← map_natCast iso, h1]; rfl

end GlobalTheory.CharLabTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoefficientNontrivialCosetsSummableBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lx_eq_of_rep_rel {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x y : LX R i v}
    (h : (rep x)⁻¹ * rep y ∈ levW R i) : x = y := by
  have : (Quotient.mk _ (Quotient.out x) : LX R i v) = Quotient.mk _ (Quotient.out y) := by
    apply Quotient.sound
    change ((QuotientGroup.leftRel (levW R i)).comap (Subtype.val : locSet R i v → GA D (Wc D i))) _ _
    rw [Setoid.comap_rel, QuotientGroup.leftRel_apply]
    exact h
  exact (Quotient.out_eq x).symm.trans (this.trans (Quotient.out_eq y))

theorem rep_notMem_levW {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x : LX R i v}
    (hx : x ≠ lx0 R i v) : rep x ∉ levW R i := fun h =>
  hx (lx_eq_of_rep_rel ((levW R i).mul_mem ((levW R i).inv_mem h) (trivial_level_coset_representative_mem_level R i v)))

theorem rep_suppF {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    SuppF (Wc D i) (fid D v) (rep x) := (Quotient.out x).2.2

theorem eq_one_of_suppF_zero {V : HSp D} {g : GA D V} (h : SuppF V 0 g) : g = 1 := by
  have e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V 1 := by
    have h1 : Formalism.L2.Theta.mt V 1 = 1 := rfl
    rw [h1, ← sub_eq_zero]
    ext a b
    have := h a b
    simpa [eq_comm] using this
  exact Subtype.ext (Units.ext e)

end

theorem acoef_small : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (Eu.LX R i v)), Eu.lx0 R i v ∉ C → ∑ x ∈ C, ‖Eu.acoef R i t μ 𝓕 v x‖ ≤ s v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hLS μ 𝓕 hμ
  obtain ⟨s, hs, hs1, hb⟩ := hLS μ 𝓕 hμ
  refine ⟨fun v => max (s v) 0, ?_, fun v => max_lt (hs1 v) one_pos, ?_⟩
  · refine Summable.of_nonneg_of_le (fun v => le_max_right _ _) (fun v => ?_) hs.abs
    exact max_le (le_abs_self _) (abs_nonneg _)
  · intro v C hC
    by_cases hex : ∃ f, IsFinIdem D v f
    · have hf : IsFinIdem D v (fid D v) := by
        unfold fid
        rw [dite_eq_left hex]
        exact hex.choose_spec
      have hinj : Function.Injective (rep : LX R i v → GA D (Wc D i)) := fun x y h =>
        lx_eq_of_rep_rel (by rw [h, inv_mul_cancel]; exact (levW R i).one_mem)
      have := hb v _ hf (C.image rep) ?_ ?_
      · rw [Finset.sum_image (fun x _ y _ h => hinj h)] at this
        exact this.trans (le_max_left _ _)
      · intro g hg
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        exact ⟨rep_suppF x, rep_notMem_levW fun e => hC (e ▸ hx)⟩
      · intro g hg g' hg' h
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hg'
        rw [lx_eq_of_rep_rel h]
    · have hf : fid D v = 0 := by
        unfold fid
        rw [dite_eq_right hex]
      have hC0 : C = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
        have h1 : rep x = 1 := eq_one_of_suppF_zero (hf ▸ rep_suppF x)
        exact rep_notMem_levW (fun e => hC (e ▸ hx)) (h1 ▸ (levW R i).one_mem)
      rw [hC0, Finset.sum_empty]
      exact le_max_right _ _

end GlobalTheory.RawLift.Eu

end
end

