module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLMulIsPrimitiveFrameDiagonalLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open ValuativeRel

namespace GlobalTheory.PrimFrameExist

theorem exists_gl_mul_isPrimFrame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : ℕ) (C : Type) [Fintype C] [DecidableEq C] (d : C → kˣ) (X : Matrix (Fin a) C k), X.rank = a →
    ∃ g₀ : GL (Fin a) k, IsPrimFrame (diagLat d) (g₀.val * X) := by
  intro k _ _ _ _ a C _ _ d X hX
  classical
  set Λ : Submodule 𝒪[k] (C → k) := diagLat d with hΛdef
  set V : Submodule k (C → k) := Submodule.span k (Set.range X.row) with hVdef
  set M : Submodule 𝒪[k] (C → k) := V.restrictScalars 𝒪[k] ⊓ Λ with hMdef
  have hΛfg : Λ.FG := (isLattice_diagLat d).fg
  haveI : IsNoetherian 𝒪[k] Λ := isNoetherian_of_fg_of_noetherian Λ hΛfg
  haveI : IsNoetherian 𝒪[k] M := isNoetherian_of_le inf_le_right
  haveI : Module.IsTorsionFree 𝒪[k] k := inferInstance
  haveI : Module.IsTorsionFree 𝒪[k] (C → k) := Module.IsTorsionFree.trans_faithfulSMul 𝒪[k] k (C → k)
  haveI : Module.IsTorsionFree 𝒪[k] M := inferInstance
  haveI : Module.Free 𝒪[k] M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex 𝒪[k] M
  let b : Module.Basis ι 𝒪[k] M := Module.Free.chooseBasis 𝒪[k] M
  let v : ι → (C → k) := fun i => (b i : C → k)
  have hvV : ∀ i, v i ∈ V := fun i => (b i).2.1
  have hvΛ : ∀ i, v i ∈ Λ := fun i => (b i).2.2
  have hrepr : ∀ y (hy : y ∈ M), y = ∑ i, ((b.repr ⟨y, hy⟩ i : 𝒪[k]) : k) • v i := by
    intro y hy
    have h := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
  have hli : LinearIndependent k v := by
    rw [← LinearIndependent.iff_fractionRing (R := 𝒪[k]) (K := k)]
    exact b.linearIndependent.map' M.subtype M.ker_subtype
  have hclear : ∀ x : C → k, ∃ r : 𝒪[k], r ≠ 0 ∧ (r : k) • x ∈ Λ := by
    intro x
    obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k])
      (fun j => x j / (d j : k))
    refine ⟨r, nonZeroDivisors.coe_ne_zero r, ?_⟩
    rw [hΛdef, mem_diagLat]
    intro j
    obtain ⟨s, hs⟩ := hr j
    rw [Algebra.smul_def] at hs
    have h1 : valuation k (algebraMap 𝒪[k] k r * (x j / d j)) ≤ 1 := by
      rw [← hs]; exact (Valuation.mem_integer_iff _ _).1 s.2
    have e : ((r : 𝒪[k]) : k) • x = fun l => (algebraMap 𝒪[k] k r * (x l / d l)) * d l := by
      funext l; simp only [Pi.smul_apply, smul_eq_mul]; rw [mul_assoc, div_mul_cancel₀ _ (d l).ne_zero]; rfl
    rw [e, map_mul]
    exact mul_le_of_le_one_left' h1
  have hli' : X.rank = Fintype.card (Fin a) ↔ LinearIndependent k X.row := by
    rw [rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span, eq_comm]; rfl
  have hXli : LinearIndependent k X.row := hli'.1 (by simpa using hX)
  have hVle : V ≤ Submodule.span k (Set.range v) := by
    intro x hx
    obtain ⟨r, hr0, hr⟩ := hclear x
    have hrx : ((r : 𝒪[k]) : k) • x ∈ M := ⟨V.smul_mem _ hx, hr⟩
    have e := hrepr _ hrx
    have hr0' : ((r : 𝒪[k]) : k) ≠ 0 := fun h => hr0 (Subtype.ext h)
    have hx' : x = ((r : 𝒪[k]) : k)⁻¹ • (((r : 𝒪[k]) : k) • x) := (inv_smul_smul₀ hr0' x).symm
    rw [hx', e]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hspan : Submodule.span k (Set.range v) = V :=
    le_antisymm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hvV i)) hVle
  have hcard : Fintype.card ι = a := by
    rw [← finrank_span_eq_card hli, hspan, hVdef, finrank_span_eq_card hXli, Fintype.card_fin]
  let e : Fin a ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let Y : Matrix (Fin a) C k := Matrix.of fun i => v (e i)
  have hYV : ∀ i, Y.row i ∈ V := fun i => hvV (e i)
  choose g hg using fun i => (Submodule.mem_span_range_iff_exists_fun k).1 (hYV i)
  have hYg : (Matrix.of g) * X = Y := by
    ext i l
    have h := congrFun (hg i) l
    rw [Finset.sum_apply] at h
    rw [Matrix.mul_apply]
    exact (Finset.sum_congr rfl fun j _ => rfl).trans h
  have hYli : LinearIndependent k Y.row := hli.comp e e.injective
  have hgli : LinearIndependent k (Matrix.of g).row := by
    refine LinearIndependent.of_comp (Matrix.vecMulLinear X) ?_
    convert hYli using 1
    funext i
    rw [← hYg]
    try rfl
  have hu : IsUnit (Matrix.of g) := Matrix.linearIndependent_rows_iff_isUnit.1 hgli
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, hYg, isPrimFrame_iff]
  refine ⟨fun i => hvΛ (e i), fun c hc i => ?_⟩
  have hcV : c ᵥ* Y ∈ V := by
    rw [vecMul_eq_sum]; exact V.sum_mem fun i _ => V.smul_mem _ (hYV i)
  have hcM : c ᵥ* Y ∈ M := ⟨hcV, hc⟩
  have e1 := hrepr _ hcM
  have e2 : c ᵥ* Y = ∑ t, c (e.symm t) • v t := by
    rw [vecMul_eq_sum, ← e.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [e.symm_apply_apply]; rfl
  have h := Fintype.linearIndependent_iffₛ.1 hli (fun t => c (e.symm t))
    (fun t => ((b.repr ⟨_, hcM⟩ t : 𝒪[k]) : k)) (by rw [← e2, ← e1]) (e i)
  simp only [Equiv.symm_apply_apply] at h
  rw [h]
  exact (b.repr _ _).2

end GlobalTheory.PrimFrameExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenuineSplittingAdelicSchwartzPlaceSignatu
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.GenRepD

theorem rho_add' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) (φ₁ φ₂ : (κ → R) → ℂ) :
    d.rho ψ w (φ₁ + φ₂) = d.rho ψ w φ₁ + d.rho ψ w φ₂ := by
  funext x; simp [Darboux.rho, schr, mul_add]

theorem rho_smul' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) (c : ℂ) (φ : (κ → R) → ℂ) :
    d.rho ψ w (c • φ) = c • d.rho ψ w φ := by
  funext x; simp [Darboux.rho, schr]; ring

theorem rho_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) :
    d.rho ψ w 0 = 0 := by
  funext x; simp [Darboux.rho, schr]


open scoped Classical in
theorem genRepD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsByD τ C ω₀ Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c₀ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ρ, c₀, hR, hcont, hder⟩ := GlobalTheory.T.archimedeanSchwartz_genuineUnitaryRep_signatures F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ω₀, hω⟩ := _root_.GlobalTheory.SliceExt.exists_rep_pure F κ (UG (cA σ) JB) ρ
  have hgen : ∀ g, ∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ := by
    intro g φ hφ
    unfold schA at hφ ⊢
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      rw [hω]
      exact Submodule.subset_span ⟨ρ g f, h, hh, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hact1 : ∀ x : Matrix α β (AE F E), actB (cA σ) (1 : UG (cA σ) JB) x = x := fun x => by simp [actB]
  refine ⟨ω₀, c₀, fun g hg => ⟨hgen g, fun w φ hφ => ?_, fun μ hμ φ hφ =>
    GlobalTheory.T.weil_operator_unitary_adelic_L2 F κ (ρ g).toLinearMap (ω₀ g) (hω g) (hR g hg).2 μ hμ φ hφ⟩, fun l hl φ hφ => ?_, ?_⟩
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨u, H, hu, hsplit⟩ := GlobalTheory.T.heisenbergRho_split_archimedean_finite F E σ α β κ ψ JA JB d w
      obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor F E σ α β κ ψ JA JB d hψ u hu f
      have e1 : d.rho ψ w (pureA F f h) = pureA F f₁ (H h) := by
        have := hsplit 1 h1m f f₁ h (by simpa only [hact1] using hf₁)
        simpa only [hact1] using this
      rw [e1, hω, hω]
      exact (hsplit g hg (ρ g f) (ρ g f₁) h ((hR g hg).1 u hu f f₁ hf₁)).symm
    | zero => rw [rho_zero', map_zero, rho_zero']
    | add x y _ _ hx hy => rw [rho_add', map_add (f := _), map_add (f := _), hx, hy, rho_add']
    | smul c x _ hx => rw [rho_smul', map_smul, map_smul, hx, rho_smul']
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨T, hT⟩ := hl h hh
      have e : (fun g => l (ω₀ g (pureA F f h))) = fun g => T (ρ g f) := funext fun g => by rw [hω, hT]
      rw [e]
      exact hcont T f
    | zero => simp only [map_zero]; exact continuousOn_const
    | add x y _ _ hx hy => simp only [map_add (f := _)]; exact hx.add hy
    | smul c x _ hx => simp only [map_smul, smul_eq_mul]; exact continuousOn_const.mul hx
  · intro γ hγ Y hY T h hh l hl
    obtain ⟨L, hL⟩ := hl h hh
    show HasDerivAt (fun t : ℝ => l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) h))) _ 0
    have e : (fun t : ℝ => l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) h))) =
        (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T))) := by
      funext t
      exact (congrArg l (hω (γ (Multiplicative.ofAdd t)) (Φ T) h)).trans (hL _)
    rw [e, hL]
    exact hder γ hγ Y hY T L

end GlobalTheory.GenRepD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPlaceTranslateCombinationLatticeIndicaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodPlace_translateCombination_latticeIndicator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (hM' : Γ.M'.IsGood B.ψ) (hlt : a' < a)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) {H : Type} (κ : H → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J)
    (ν α : (Fv F B.v₁)ˣ →* ℂˣ) (hν : ∀ x, ‖(ν x : ℂ)‖ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) → ℂ))
    (hι : Γ.M'.IsLinBar B.ψ B.τ₁ 1 1 ι)
    (hact : ∀ g : GL (Fin a') (Fv F B.v₁), ∃ k : H, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F B.v₁) φ r →
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB _, om' (κ k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ r) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₁ r ∧
        ι φ₁ = omB ν α g 1 (ι φ))
    {m : ℕ} (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ)
    (φ₀ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ)
    (hSB : ∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) (h₀ : ∀ k, φ k B.v₁ = φ₀)
    (P : GL (Fin a') (Fv F B.v₁)) (Λ : Submodule 𝒪[Fv F B.v₁] (Fin (a + a') → Fv F B.v₁)) (c : ℂ)
    (hφ₀ : ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y)),
    ∃ z : H →₀ ℂ, zdeg z ≠ 0 ∧
      (z.sum fun k c => c • om' (κ k, 1) (∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k))) ∈ Γ.M'.So B.ψ B.τ₁ := by
  first | exact @GlobalTheory.CombAtGood.exists_comb_translates_mem_So | exact GlobalTheory.CombAtGood.exists_comb_translates_mem_So | (intros; apply GlobalTheory.CombAtGood.exists_comb_translates_mem_So <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

namespace GlobalTheory.FlatCM.GramExists

theorem exists_weilEq_entry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → p + q = 1 →
    HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ →
    Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ g : 𝓞 E, WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ ρ σ₁ A B p q hρ hpq hA f₁ f₂ h₁ h₂
  obtain ⟨A', B', f₁', f₂', p', q', hpq', hdet, h₁', h₂', hW⟩ := _root_.GlobalTheory.GramBaseChange.exists_complex_fibre E H K ρ σ₁ A B p q hρ hA f₁ f₂ h₁ h₂
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.CM.PureHom.exists_weilEq_smul_of_pure E H A' B' p' q' (hpq'.trans hpq) hdet f₁' f₂' h₁' h₂'
  exact ⟨g, hW g hg⟩

theorem exists_isGram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∃ gP gQ, IsGram X gP gQ := by
  intro E _ _ _ H K _ _ ρ σ₁ p q X
  have hP : ∀ a b : Fin p, ∃ g : 𝓞 E, WeilEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L
      ((X.A true).t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun a b =>
    exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP _ _ (X.lin (Sum.inl a)) (X.lin (Sum.inl b))
  have hQ : ∀ a b : Fin q, ∃ g : 𝓞 E, WeilEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L
      ((X.A false).t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun a b =>
    exists_weilEq_entry E H K ρ σ₁ (X.A false) X.B 0 1 X.ρ_sq rfl X.typeM _ _ (X.lin (Sum.inr a)) (X.lin (Sum.inr b))
  choose gP hgP using hP
  choose gQ hgQ using hQ
  exact ⟨Matrix.of gP, Matrix.of gQ, fun a b => hgP a b, fun a b => hgQ a b⟩

end GlobalTheory.FlatCM.GramExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRelationLinearHomsCmSignatureType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.PureHom

open PureTriple

theorem exists_prod_act_comp_eq_one_of_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (A B : PAT H (Sp ℂ)) (p q : ℕ), ρ ^ 2 = -(H.d : ℂ) →
    HasType H A.t.act ρ 1 0 → HasType H B.t.act ρ p q → ∀ (n : ℕ), p + q < n → ∀ ψ : Fin n → (A.t.G ⟶ B.t.G),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) →
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  intro E _ _ _ H ρ A B p q hρ hA hB n hn ψ hψ
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have hdA := hA ℂ (RingHom.id ℂ) Function.injective_id
  have hdB := hB ℂ (RingHom.id ℂ) Function.injective_id
  rw [hid] at hdA hdB
  simp only [RingHom.id_apply] at hdA hdB
  have hsq : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have key : ∀ (T : PAT H (Sp ℂ)) (a b : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ a) ∧
      (τ H.rt ≠ ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ b)) → ∃ a' b' : ℕ, a' + b' = a + b ∧
      ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ a') ∧
        (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ b') := by
    intro T a b hd
    by_cases h0 : ρ = H.rt0
    · exact ⟨a, b, rfl, h0 ▸ hd⟩
    · have h1 := (sq_eq_sq_iff_eq_or_eq_neg.1 (hρ.trans H.sqrt_neg_disc_sq.symm)).resolve_left h0
      have h2 : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ H.rt0 → τ H.rt = ρ := fun τ h =>
        ((sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq τ).trans H.sqrt_neg_disc_sq.symm)).resolve_left h).trans h1.symm
      exact ⟨b, a, add_comm b a, fun τ => ⟨fun h => (hd τ).2 fun h' => h0 (h'.symm.trans h),
        fun h => (hd τ).1 (h2 τ h)⟩⟩
  obtain ⟨pA, qA, hpqA, hdetA⟩ := key A 1 0 hdA
  obtain ⟨pB, qB, hpqB, hdetB⟩ := key B p q hdB
  obtain ⟨gA, tyA, htyA⟩ := AllClasses.exists_isTypeFn H pA qA
  obtain ⟨gB, tyB, htyB⟩ := AllClasses.exists_isTypeFn H pB qB
  obtain ⟨uA, HA, χA, -, hAH, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨uB, HB, χB, -, hBH, -⟩ := PureType.exists_isThetaUnif hT B.pol
  obtain ⟨DA, PeA, FA, hpA, hqA, hPA, hFA, -, hactA⟩ := exists_datum_period hT hL A htyA hdetA uA hAH
  obtain ⟨DB, PeB, FB, hpB, hqB, hPB, hFB, -, hactB⟩ := exists_datum_period hT hL B htyB hdetB uB hBH
  obtain ⟨-, -, -, -, -, hA2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ uA HA χA hAH
  obtain ⟨-, -, -, -, hB1, hB2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hBH
  choose Ψ hΨ hΨΛ using fun i => (HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    (ψ i) (hψ i).isMonHom).imp fun _ h => And.intro h.1 h.2.1
  let GA : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    FA.toLinearMap ∘ₗ diagMul tyA (s : E) ∘ₗ FA.symm.toLinearMap
  let GB : 𝓞 E → (Fin B.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ) := fun s =>
    FB.toLinearMap ∘ₗ diagMul tyB (s : E) ∘ₗ FB.symm.toLinearMap
  have hGA : ∀ s z, uA.ex (GA s z) = uA.ex z ≫ A.t.act.act s := fun s z => by
    have e := hactA s (FA.symm z)
    rw [FA.apply_symm_apply] at e
    exact e
  have hGB : ∀ s z, uB.ex (GB s z) = uB.ex z ≫ B.t.act.act s := fun s z => by
    have e := hactB s (FB.symm z)
    rw [FB.apply_symm_apply] at e
    exact e
  have hGPA : ∀ s a, GA s (FA (PeA a)) = FA (PeA (s • a)) := fun s a => by
    simp only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    ext i
    exact (hPA.1 s a i).symm
  have hGPB : ∀ s b, GB s (FB (PeB b)) = FB (PeB (s • b)) := fun s b => by
    simp only [GB, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    ext i
    exact (hPB.1 s b i).symm
  have hGAc : ∀ r s z, GA r (GA s z) = GA s (GA r z) := fun r s z => by
    simp only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    ext i
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hGBinj : ∀ r : 𝓞 E, r ≠ 0 → ∀ z, GB r z = 0 → z = 0 := fun r hr z hz => by
    have hr' : (r : E) ≠ 0 := by exact_mod_cast hr
    have e : diagMul tyB (r : E) (FB.symm z) = 0 := by
      have := congrArg FB.symm hz
      simpa [GB] using this
    have e' : FB.symm z = 0 := funext fun k => by
      have := congrFun e k
      simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left ((map_ne_zero (tyB k)).2 hr')
    simpa using congrArg FB e'
  have hcomm : ∀ i s z, Ψ i (GA s z) = GB s (Ψ i z) := by
    intro i s z
    haveI := (hψ i).isMonHom
    haveI := A.t.act.hom s
    have e := linear_lift_unique uA uB hA2 hB1 (A.t.act.act s ≫ ψ i) (F := Ψ i ∘ₗ GA s) (F' := GB s ∘ₗ Ψ i)
      (fun z => by rw [LinearMap.comp_apply, hΨ, hGA, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, hGB, hΨ, (hψ i).comm, Category.assoc])
    exact LinearMap.congr_fun e z
  have := DA.fin
  have := DA.proj
  have := DB.fin
  have := DB.proj
  have hrkA : Module.finrank (𝓞 E) DA.La = 1 := by rw [DA.rank, hpA, hqA, hpqA]
  haveI : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hrkA]; exact one_pos)
  obtain ⟨a, ha⟩ := exists_ne (0 : DA.La)
  have hb : ∀ i, ∃ b : DB.La, Ψ i (FA (PeA a)) = FB (PeB b) := fun i => by
    have hm : Ψ i (FA (PeA a)) ∈ uB.Λ := hΨΛ i _ ((hFA _).2 ⟨a, rfl⟩)
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 ((hFB (FB.symm _)).1 (by rwa [FB.apply_symm_apply]))
    exact ⟨b, by rw [hb, FB.apply_symm_apply]⟩
  choose b hb using hb
  have hrkB : Module.finrank (𝓞 E) DB.La = p + q := by rw [DB.rank, hpB, hqB, hpqB]
  have hni : ¬ LinearIndependent (𝓞 E) b := fun hi => by
    have := hi.fintype_card_le_finrank
    rw [Fintype.card_fin, hrkB] at this
    omega
  obtain ⟨x, hx, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hni
  refine ⟨x, fun h => hi₀ (by rw [h]; rfl), ?_⟩
  let Θ : (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ) := ∑ i, Ψ i ∘ₗ GA (x i)
  have hΘ : ∀ z, Θ z = ∑ i, Ψ i (GA (x i) z) := fun z => by
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply]
  have hΘa : Θ (FA (PeA a)) = 0 := by
    rw [hΘ]
    calc ∑ i, Ψ i (GA (x i) (FA (PeA a))) = ∑ i, FB (PeB (x i • b i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcomm, hb, hGPB]
      _ = 0 := by rw [← map_sum, ← map_sum, hx, map_zero, map_zero]
  have hΘc : ∀ s z, Θ (GA s z) = GB s (Θ z) := fun s z => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΘ, hΘ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGAc, hcomm]
  have hΘl : ∀ a', Θ (FA (PeA a')) = 0 := fun a' => by
    obtain ⟨r, s, hr, e⟩ := CMLat.exists_smul_eq_smul hrkA ha a'
    refine hGBinj r hr _ ?_
    rw [← hΘc, hGPA, e, ← hGPA, hΘc, hΘa, map_zero]
  have hΘ0 : Θ.restrictScalars ℝ = 0 := by
    refine LinearMap.ext_on uA.full fun z hz => ?_
    obtain ⟨a', ha'⟩ := AddMonoidHom.mem_range.1 ((hFA (FA.symm z)).1 (by rwa [FA.apply_symm_apply]))
    have ez : z = FA (PeA a') := by rw [ha', FA.apply_symm_apply]
    rw [ez]
    exact hΘl a'
  have hΘz : ∀ z, Θ z = 0 := fun z => LinearMap.congr_fun hΘ0 z
  have hs : Smooth A.t.G.hom := A.ab.smooth
  have hp : IsProper B.t.G.hom := B.ab.proper
  have hr : IsReduced A.t.G.left := isReduced_of_smooth_complex _ A.t.G.hom hs
  refine ComplexPoints.over_hom_ext_of_complexPoints fun y => ?_
  obtain ⟨z, rfl⟩ := uA.ex_onto y
  have hpr : ∀ s : Finset (Fin n), uA.ex z ≫ ∏ i ∈ s, (A.t.act.act (x i) ≫ ψ i) =
      uB.ex (∑ i ∈ s, Ψ i (GA (x i) z)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, comp_one]; exact ((uB.ker 0).2 uB.Λ.zero_mem).symm
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, comp_mul, ih, uB.ex_add, hΨ, hGA, Category.assoc]
  rw [hpr, ← hΘ, hΘz, comp_one]
  exact (uB.ker 0).2 uB.Λ.zero_mem

end GlobalTheory.CM.PureHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlaceStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_bijOn_schwartzBruhat_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    Set.BijOn (fun (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) => ∫ x, φ x * ψ (x ⬝ᵥ y) ∂μ)
      (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := by
  first | exact @GlobalTheory.FourierLocBij.fourier_bijOn | exact GlobalTheory.FourierLocBij.fourier_bijOn | (intros; apply GlobalTheory.FourierLocBij.fourier_bijOn <;> assumption)
end

