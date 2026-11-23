module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactElementGaussianList
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesSmoothModerateGrowthDeriv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.PoinDer

variable {D : D7}

theorem termBound (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ) (hv : KDecay M v) (b : ∀ τ, M.H τ)
    (hb : ∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ :=
  _root_.GlobalTheory.PoinTerm.norm_coef_le D θ hθ V S M K v hv b hb

theorem sumBound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ →
    ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) →
    (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) →
    (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V,
    Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A :=
  _root_.GlobalTheory.poincare_sum_bound

theorem termDeriv (hHC : GlobalTheory.Published.HarishChandraModules) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ)
    (τ : D.what₂.Tau) (hb : b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (x : GA D V) :
    HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s))
      (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 :=
  _root_.GlobalTheory.TermDeriv.hasDerivAt_coef_oneP D hHC θ hθ V S M K v b τ hb X hX x

theorem onePDecay (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : GA D V) (t : ℝ), |t| < 1 →
      ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤ L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ :=
  _root_.GlobalTheory.OnePDecay.decay_oneP D θ hθ V τ X hX N

theorem finE_mul_oneP (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (x : GA D V) (t : ℝ) :
    Lev.finE V (x * oneP θ V τ X t) = Lev.finE V x := by
  have h : finHom V (oneP θ V τ X t) = 1 := GlobalTheory.PointAtPlaceHom.atTau_mem V τ _
  show (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) (x * oneP θ V τ X t) = (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) x
  rw [map_mul, MonoidHom.comp_apply (Formalism.UG.bc (Lev.swapAE D)) (finHom V) (oneP θ V τ X t), h, map_one, mul_one]

theorem poin_smooth_growth_deriv : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ UnifModGrowth V θ (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (w : M.H τ) = dRep (M.rep τ) X (a τ) → (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ' => Function.update a τ w τ') = Rder θ V τ X (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c a
  obtain ⟨C₀, A, hB⟩ := sumBound D θ hθ V Λ hΛ 𝔪 c
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK

  have hsum : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, ∀ g,
      Summable (fun γ : GQ V => ‖coef θ M K v b (c * (γ : GA D V) * g)‖) ∧
      ∑' γ : GQ V, ‖coef θ M K v b (c * (γ : GA D V) * g)‖ ≤ C * height V g ^ A := by
    intro b hb
    obtain ⟨C, hC0, hC⟩ := termBound θ hθ M K v hv b hb
    refine ⟨C * C₀, fun g => ?_⟩
    refine hB (fun x => ‖coef θ M K v b x‖) C (fun _ => norm_nonneg _) (fun x hx => ?_) hC g
    simp only [coef, if_neg hx, norm_zero]
  have grow : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ModGrowthExp V A (poin θ M K v c b) := by
    intro b hb
    obtain ⟨C, hC⟩ := hsum b hb
    exact ⟨C, fun g => (norm_tsum_le_tsum_norm (hC g).1).trans (hC g).2⟩

  have der : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∀ τ, ∀ X ∈ lieAt V τ, ∀ g,
      HasDerivAt (fun t : ℝ => poin θ M K v c b (g * oneP θ V τ X t))
        (poin θ M K v c (Function.update b τ (dRep (M.rep τ) X (b τ))) g) 0 := by
    intro b hb τ X hX g
    set b' := Function.update b τ (dRep (M.rep τ) X (b τ)) with hb'd
    have hb' : ∀ τ', b' τ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ' := by
      intro τ'
      by_cases h : τ' = τ
      · subst h
        rw [hb'd, Function.update_self]
        exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M τ' hX (hb τ')
      · rw [hb'd, Function.update_of_ne h]
        exact hb τ'
    obtain ⟨C', hC'0, hC'⟩ := termBound θ hθ M K v hv b' hb'
    obtain ⟨L, hL0, hL⟩ := onePDecay θ hθ V τ hX (2 * V.rank ^ 2 + 1)
    set u : GA D V → ℝ := fun x => if Lev.finE V x ∈ K then C' * L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ else 0
      with hu
    have hprod : ∀ x : GA D V, 0 ≤ ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x =>
      Finset.prod_nonneg fun τ' _ => inv_nonneg.2 (pow_nonneg (by unfold hsn; positivity) _)
    have hu0 : ∀ x, 0 ≤ u x := fun x => by
      simp only [hu]; split_ifs
      · exact mul_nonneg (mul_nonneg hC'0 hL0) (hprod x)
      · exact le_rfl
    have huK : ∀ x, Lev.finE V x ∉ K → u x = 0 := fun x hx => by simp only [hu, if_neg hx]
    have huC : ∀ x, u x ≤ (C' * L) * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x => by
      simp only [hu]; split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg hC'0 hL0) (hprod x)
    have hbd : ∀ (x : GA D V) (y : ℝ), y ∈ Set.Ioo (-1 : ℝ) 1 → ‖coef θ M K v b' (x * oneP θ V τ X y)‖ ≤ u x := by
      intro x y hy
      by_cases hx : Lev.finE V x ∈ K
      · have h1 := hC' (x * oneP θ V τ X y)
        have h2 := hL x y (abs_lt.2 ⟨hy.1, hy.2⟩)
        simp only [hu, if_pos hx]
        calc _ ≤ _ := h1
          _ ≤ C' * (L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) := mul_le_mul_of_nonneg_left h2 hC'0
          _ = _ := by ring
      · have : coef θ M K v b' (x * oneP θ V τ X y) = 0 := by
          simp only [coef, finE_mul_oneP, if_neg hx]
        rw [this, norm_zero]
        exact hu0 x
    have hS := (hB u (C' * L) hu0 huK huC g).1
    obtain ⟨Cb, hCb⟩ := hsum b hb
    have key := hasDerivAt_tsum_of_isPreconnected (g := fun (γ : GQ V) (s : ℝ) => coef θ M K v b (c * (γ : GA D V) * g * oneP θ V τ X s))
      (g' := fun (γ : GQ V) (s : ℝ) => coef θ M K v b' (c * (γ : GA D V) * g * oneP θ V τ X s)) (t := Set.Ioo (-1 : ℝ) 1)
      (y₀ := 0) (y := 0) hS isOpen_Ioo isPreconnected_Ioo
      (fun γ y _ => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun x => termDeriv hHC θ hθ M K v b τ (hb τ) hX x) _ y)
      (fun γ y hy => hbd _ y hy) (by norm_num)
      (by simpa [GlobalTheory.Mem.Lift.oneP_zero hθ] using (hCb g).1.of_norm) (by norm_num)
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
    refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [poin, mul_assoc]
  refine ⟨?_, ⟨A, fun l hl => ?_⟩, ?_⟩
  ·
    refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V
      {φ | ∃ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) ∧ φ = poin θ M K v c b} ?_ ?_ _ ⟨_, fun τ => (a τ).2, rfl⟩
    · rintro φ ⟨b, hb, rfl⟩
      exact (((_root_.GlobalTheory.PoinAut.poin_aut D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c).1 fun τ => ⟨b τ, hb τ⟩).1).cont
    · rintro φ ⟨b, hb, rfl⟩ τ X hX
      refine ⟨_, ⟨Function.update b τ (dRep (M.rep τ) X (b τ)), fun τ' => ?_, rfl⟩, der b hb τ X hX⟩
      by_cases h : τ' = τ
      · subst h
        rw [Function.update_self]
        exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M τ' hX (hb τ')
      · rw [Function.update_of_ne h]
        exact hb τ'
  ·
    have claim : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∃ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) ∧
          l.foldr (fun p f => Rder θ V p.1 p.2 f) (poin θ M K v c fun τ => a τ) = poin θ M K v c b := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨fun τ => a τ, fun τ => (a τ).2, rfl⟩
      | cons p l ih =>
        intro hl'
        obtain ⟨b, hb, e⟩ := ih fun q hq => hl' q (List.mem_cons_of_mem _ hq)
        have hX : p.2 ∈ lieAt V p.1 := hl' p List.mem_cons_self
        refine ⟨Function.update b p.1 (dRep (M.rep p.1) p.2 (b p.1)), fun τ' => ?_, ?_⟩
        · by_cases h : τ' = p.1
          · rw [h, Function.update_self]
            exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M p.1 hX (hb p.1)
          · rw [Function.update_of_ne h]
            exact hb τ'
        · rw [List.foldr_cons, e]
          funext g
          exact (der b hb p.1 p.2 hX g).deriv
    obtain ⟨b, hb, e⟩ := claim l hl
    rw [e]
    exact grow b hb
  ·
    intro τ X hX w hw
    funext g
    have e : (fun τ' => (Function.update a τ w τ' : M.H τ')) =
        Function.update (fun τ' => (a τ' : M.H τ')) τ (dRep (M.rep τ) X (a τ)) := by
      funext τ'
      by_cases h : τ' = τ
      · subst h
        simp [hw]
      · simp [Function.update_of_ne h]
    rw [e]
    exact ((der (fun τ' => a τ') (fun τ' => (a τ').2) τ X hX g).deriv).symm

end GlobalTheory.PoinDer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingInnerProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.KInvData

theorem hasDerivAt_linear {Z Q : Type} [NormedAddCommGroup Q] [NormedSpace ℂ Q] (U : Submodule ℂ (Z → ℂ))
    [FiniteDimensional ℂ U] (φ : (Z → ℂ) →ₗ[ℂ] Q) {u : ℝ → Z → ℂ} {u' : Z → ℂ} {t : ℝ} (hu : ∀ s, u s ∈ U) (hu' : u' ∈ U)
    (hd : ∀ z, HasDerivAt (fun s => u s z) (u' z) t) : HasDerivAt (fun s => φ (u s)) (φ u') t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h1 : Filter.Tendsto (slope u t) (nhdsWithin t {t}ᶜ) (nhds u') := by
    rw [tendsto_pi_nhds]
    intro z
    exact hasDerivAt_iff_tendsto_slope.1 (hd z)
  have hm : ∀ s, slope u t s ∈ U := fun s => U.smul_of_tower_mem _ (U.sub_mem (hu s) (hu t))
  have h2 : Filter.Tendsto (fun s => (⟨slope u t s, hm s⟩ : U)) (nhdsWithin t {t}ᶜ) (nhds ⟨u', hu'⟩) :=
    tendsto_subtype_rng.2 h1
  have h3 := ((φ ∘ₗ U.subtype).continuous_of_finiteDimensional.tendsto _).comp h2
  refine h3.congr fun s => ?_
  simp [slope, LinearMap.map_smul_of_tower]

theorem kapX_one {D : D7} (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : kapX X e hJ 1 = 1 := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X 1) = 1
  rw [map_one, map_one]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}
  {Pi : ModuleCat.{0} ℂ} {rf : GA D X → Module.End ℂ Pi}
  {rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi} {p : (WO W X → ℂ) →ₗ[ℂ] Pi}

theorem line_step (hθ : IsInfFam θ) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB)
    (hmap : IsCoinvMap θ ωA (algF ψ θ true A B) Pi rf rl p)
    {τ : D.what₂.Tau} {Y : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hY : Y ∈ lieAt W τ)
    (U : Submodule ℂ ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ)) [FiniteDimensional ℂ U]
    (hU : U ≤ algD Γ.M Bs.ψ Bs.emb)
    (hUt : ∀ t : ℝ, ∀ x ∈ U, om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y t), 1) x ∈ U)
    {ΦD : (Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ} (hΦD : ΦD ∈ U) {Φ Φ₁ : WO W X → ℂ}
    (h0 : IsDatum Γ.M ψ cA ΦD Φ)
    (h1 : IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y 1), 1) ΦD) Φ₁) : p Φ₁ = p Φ := by
  classical
  have huniq : ∀ {x : (Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ} {f g : WO W X → ℂ},
      IsDatum Γ.M ψ cA x f → IsDatum Γ.M ψ cA x g → f = g := fun hf hg =>
    GlobalTheory.SquareAgree.CoinvPass.isDatum_unique cA.surjective hf hg
  let G : Submodule ℂ (((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) × (WO W X → ℂ)) :=
    { carrier := {q | q.1 ∈ U ∧ IsDatum Γ.M ψ cA q.1 q.2}
      add_mem' := fun ha hb => ⟨U.add_mem ha.1 hb.1, GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ ha.2 hb.2⟩
      zero_mem' := ⟨U.zero_mem, GlobalTheory.SquareAgree.CoinvPass.isDatum_zero⟩
      smul_mem' := fun c _ ha => ⟨U.smul_mem c ha.1, GlobalTheory.SquareAgree.CoinvPass.isDatum_smul c ha.2⟩ }
  let fG : G →ₗ[ℂ] U := ((LinearMap.fst ℂ _ _).comp G.subtype).codRestrict U (fun q => q.2.1)
  have hfG : Function.Injective fG := by
    intro q q' hq
    have e1 : q.1.1 = q'.1.1 := congrArg Subtype.val hq
    have e2 : q.1.2 = q'.1.2 := huniq q.2.2 (e1 ▸ q'.2.2)
    exact Subtype.ext (Prod.ext e1 e2)
  haveI : FiniteDimensional ℂ G := Module.Finite.of_injective fG hfG
  let Uf : Submodule ℂ (WO W X → ℂ) := G.map (LinearMap.snd ℂ _ _)
  let Φt : ℝ → WO W X → ℂ := fun t => ωA (oneP θ W τ Y t, 1) Φ
  have hdat : ∀ t, IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y t), 1) ΦD) (Φt t) := by
    intro t
    have h := hO.weilA ΦD Φ h0 (oneP θ W τ Y t) 1
    rwa [kapX_one] at h
  have hmemU : ∀ t, Φt t ∈ Uf := fun t => ⟨(_, Φt t), ⟨hUt t ΦD hΦD, hdat t⟩, rfl⟩
  have halg : ∀ t, Φt t ∈ algF ψ θ true A B := by
    intro t
    obtain ⟨Φ', hΦ', hD'⟩ := hO.algA' _ (hU (hUt t ΦD hΦD))
    rwa [huniq hD' (hdat t)] at hΦ'
  have hshift : ∀ s t, ωA (oneP θ W τ Y s, 1) (Φt t) = Φt (s + t) := by
    intro s t
    simp only [Φt]
    rw [GlobalTheory.Mem.Lift.oneP_add hθ hY s t, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hzero : ∀ t, ∀ l : Module.Dual ℂ Pi, HasDerivAt (fun s => l (p (Φt s))) 0 t := by
    intro t l
    obtain ⟨Φ', hΦ', hder⟩ := hmap.stabM.2 τ Y hY (Φt t) (halg t)
    have hp := hmap.invl τ Y hY (Φt t) (halg t) Φ' hΦ' hder
    have hd : ∀ z, HasDerivAt (fun s => Φt s z) (Φ' z) t := by
      intro z
      have h := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hder z)
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show Φt s z = ωA (oneP θ W τ Y (s - t), 1) (Φt t) z
      rw [hshift, sub_add_cancel]
    have h := hasDerivAt_linear (Uf ⊔ Submodule.span ℂ {Φ'}) (l.comp p) (u := Φt)
      (fun s => Submodule.mem_sup_left (hmemU s)) (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) hd
    simpa [hp] using h
  have hconst : ∀ l : Module.Dual ℂ Pi, l (p (Φt 1)) = l (p (Φt 0)) := fun l =>
    is_const_of_deriv_eq_zero (fun t => (hzero t l).differentiableAt) (fun t => (hzero t l).deriv) 1 0
  have e1 : Φt 1 = Φ₁ := huniq (hdat 1) h1
  have e0 : Φt 0 = Φ := by
    simp only [Φt]
    rw [GlobalTheory.Mem.Lift.oneP_zero hθ, Prod.mk_one_one, map_one, Module.End.one_apply]
  rw [← e1, ← e0, ← sub_eq_zero]
  exact (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => by rw [map_sub, hconst l, sub_self]

end GlobalTheory.KInvData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftFiniteVectorEqTranslateLevelDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel


set_option maxHeartbeats 1000000 in
theorem thP_vec_eq_translate : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (hn : T.rank ≤ S.rank) (B : C.Bas), C.IsB B → ∀ ΛT : Lt D.host.E T.rank, IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ f₀ f, IsThPVecOf C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f → ∃ (Lv : SW.Level C.X) (M : ℕ) (f' : WO S T → ℂ) (k₀ : GA D S), IdemTwo Lv.w ∧ 0 < M ∧ (M : 𝓞 D.host.E) ∈ Lv.𝔪 ∧ C.IsBase Lv B f' ∧ k₀ ∈ GfC S ∧ f = om (k₀, 1) (C.uVec Lv hn f') ∧ C.IsTh (C.uVec Lv hn f') ∧ C.IsFock B (C.uVec Lv hn f') ∧ C.uVec Lv hn f' ≠ 0 ∧ ∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → Lev.finE T k ∈ Formalism.L2.DIV.St βT ∧ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1 := by
  intro D S T C om hom hn B hB ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg hodd f₀ f hf
  have hf0 : f ≠ 0 := _root_.GlobalTheory.ThPVecNe.thPVec_ne_zero D S T C hn B hB ΛT hsd βS βT hβS hβT Pg Q ξ f₀ f hf
  have hfc := hf
  obtain ⟨hvac, e, he, hθ⟩ := hf
  obtain ⟨Lv, k₀, Λ', L, hw2, hmP, hJ, hk₀, hmov, hfin, hA, hB', hC, hD, hE, hF⟩ :=
    _root_.GlobalTheory.LiftLevel.lift_level_datum D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg hodd e he
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hfT : f = Tm (thPDatum S T βS βT Pg Q ξ e) := hall Tm hTm
  obtain ⟨hSB, hTh, hFock, hLat⟩ := GlobalTheory.T.placeModel_indicator_theta_fock_latticeVacuum D S T C B hB ΛT hsd (Pg ∪ Q) e he f₀ hvac Tm hTm L hA hB' hC
  have hLat'' := hLat _ hD
  haveI := Fintype.ofFinite (LvCls C Lv)
  set f'' := Tm (indL L) with hf''
  have hee : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hhalf : ∀ w : WO S T, IsHalf (cA D e) (partAt (cA D e) w) := fun w i j => by
    simp only [partAt, Matrix.map_apply]
    rw [← mul_assoc, hee]
  set t : LvCls C Lv → WO S T := fun c =>
    partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))) with ht
  have hfsum : f = ∑ c : LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) •
      heisO C.ψ S T (t c) f'' := by
    rw [hfT]
    have hΦ : thPDatum S T βS βT Pg Q ξ e = ∑ c : LvCls C Lv,
        Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) • fun x => indL L (x + t c) := by
      funext x
      rw [hF x, finsum_eq_sum_of_fintype, Finset.sum_apply]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦ, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, hTm.trans _ hSB _ (hhalf _)]
  set f' := om (k₀⁻¹, 1) f'' with hf'
  have hinv : ∀ g : GA D S, ∀ x, om (g, 1) (om (g⁻¹, 1) x) = x := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one]
    exact congrArg (fun E : Module.End ℂ (WO S T → ℂ) => E x) om.map_one
  have hinv' : ∀ g : GA D S, ∀ x, om (g⁻¹, 1) (om (g, 1) x) = x := fun g x => by
    simpa using hinv g⁻¹ x
  have hom1 : om (k₀, 1) f' = f'' := hinv k₀ f''
  have hTh' : C.IsTh f' := hom.om_pres _ _ hTh
  have hu : om (k₀, 1) (C.uVec Lv hn f') = f := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfsum, Ctx.uVec, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul]
    congr 1
    rw [Ctx.rho, hom.om_heis _ _ _ _ hTh', hom1]
    obtain ⟨v, hv, hv1, hv2⟩ := hE _ (c.out).2
    have h2 : heisO C.ψ S T (2 • v) f'' = f'' := hLat''.1 v hv
    have h3 := GlobalTheory.FinTranslate.heisO_heisO S T C.ψ (t c) (2 • v) f''
    rw [h2, show C.ψ (symplOH S T (t c) (2 • v)) = 1 from hv2, one_smul] at h3
    calc heisO C.ψ S T (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))) f''
        = heisO C.ψ S T (t c + 2 • v) f'' := congrArg (fun w => heisO C.ψ S T w f'') hv1
      _ = heisO C.ψ S T (t c) f'' := h3.symm
  have hmt1 : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => by simp [Formalism.L2.Theta.mt]
  have hmvB : C.mvB 1 B = B := by
    funext τ
    simp [Ctx.mvB, hmt1, compAt]
  have hfmt1 : fmt T 1 = 1 := by simp [fmt, hmt1]
  have hmov1 : IsMov (fmt T 1) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) := by
    rw [hfmt1]
    intro u
    exact ⟨fun h => ⟨u, h, (Matrix.one_mulVec u).symm⟩, fun ⟨u₀, h, e⟩ => by rw [e, Matrix.one_mulVec]; exact h⟩
  have hne' : f' ≠ 0 := by
    intro h0
    apply hf0
    have : f'' = 0 := by rw [← hom1, h0, map_zero]
    rw [hfsum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [this]
    have : heisO C.ψ S T (t c) (0 : WO S T → ℂ) = 0 := by
      funext w
      simp [heisO]
    rw [this, smul_zero]
  have hFock' : C.IsFock B f' := by
    have := (((GlobalTheory.Ker.WeakMove.om_move D S T C om hom k₀⁻¹ 1 f'' hTh).2 B hB).1 hFock)
    rwa [hmvB] at this
  have hlat' : IsLatVac (heisO C.ψ S T) (hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ))) f' :=
    (GlobalTheory.TensLatMove.hatA_move D S T C k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hmov hmov1).2
      om hom f'' hTh hLat''
  have hbase : C.IsBase Lv B f' := ⟨hTh', hne', hFock', hlat'⟩
  have hu1 : C.IsTh (C.uVec Lv hn f') := GlobalTheory.Ker.KernelCompare.isTh_uVec C Lv hn hTh'
  have hfth : C.IsTh f := hu ▸ hom.om_pres _ _ hu1
  have hfF : C.IsFock B f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_thPVec C.ψ C.θ S T _ _ _ _ βS βT Pg Q ξ f₀ f hfc hfth τ
  have hu2 : C.IsFock B (C.uVec Lv hn f') := by
    have h := (((GlobalTheory.Ker.WeakMove.om_move D S T C om hom k₀⁻¹ 1 f hfth).2 B hB).1 hfF)
    rw [hmvB, ← hu, hinv'] at h
    exact h
  have hu3 : C.uVec Lv hn f' ≠ 0 := fun h0 => hf0 (by rw [← hu, h0, map_zero])
  refine ⟨Lv, Ideal.absNorm Lv.𝔪, f', k₀, hw2, ?_, Ideal.absNorm_mem Lv.𝔪, hbase, hk₀, hu.symm, hu1, hu2, hu3,
    _root_.GlobalTheory.LevKFrame.levK_frame D S T C Lv ΛT hsd hAA βT hβT Pg hmP hJ⟩
  exact Nat.pos_of_ne_zero fun h => Lv.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuaProductEqGaussianDatumSmallModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitVacua_product_eq_gaussianDatum_smallModel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M'.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumB (t := t) W e Γ (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) := by
  first | exact @GlobalTheory.SmallVac.vac_datumB | exact GlobalTheory.SmallVac.vac_datumB | (intros; apply GlobalTheory.SmallVac.vac_datumB <;> assumption)
end

