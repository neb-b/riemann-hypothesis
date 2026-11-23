module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.SchrIrred

open ValuativeRel

theorem norm_addChar_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) (x : k) : ‖ψ x‖ = 1 := by
  have hle : ∀ y : k, ‖ψ y‖ ≤ 1 := by
    intro y
    have hK : IsCompact ((fun u : k => y * u) '' (𝒪[k] : Set k)) :=
      (IsNonarchimedeanLocalField.isCompact_closedBall k 1).image (by fun_prop)
    obtain ⟨C, hC⟩ := (hK.image (continuous_norm.comp hψ)).isBounded.exists_norm_le
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    have hmem : ‖ψ (y * (n : k))‖ ∈ (fun z => ‖ψ z‖) '' ((fun u : k => y * u) '' (𝒪[k] : Set k)) :=
      ⟨y * n, ⟨n, natCast_mem _ n, rfl⟩, rfl⟩
    have h2 := hC _ hmem
    rw [Real.norm_of_nonneg (norm_nonneg _), mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at h2
    linarith
  have h1 : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by rw [← norm_mul, h1, norm_one]
  have a := hle x
  have b := hle (-x)
  nlinarith [norm_nonneg (ψ x), norm_nonneg (ψ (-x))]

def toCircle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) : AddChar k Circle where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (norm_addChar_eq_one ψ hψ x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (by show ψ (a + b) = ψ a * ψ b; exact AddChar.map_add_eq_mul ψ a b)

theorem coe_toCircle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) (x : k) : (toCircle ψ hψ x : ℂ) = ψ x := rfl

def colH (k : Type) [TopologicalSpace k] (κ : Type) : (κ → k) ≃ₜ Matrix κ Unit k where
  toFun x := Matrix.of fun i _ => x i
  invFun M i := M i ()
  left_inv _ := rfl
  right_inv M := by ext i j; cases j; rfl
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun _ => continuous_apply i
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    exact (continuous_apply () ).comp (continuous_apply i)

theorem sb_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {f : Y → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB Y) : f ∘ h ∈ GlobalTheory.WeilM.SB X :=
  ⟨hf.1.comp_continuous h.continuous, hf.2.comp_homeomorph h⟩

end GlobalTheory.SchrIrred

namespace GlobalTheory.SchrIrred

open ValuativeRel

theorem schr_irreducible_local (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] [Invertible (2 : k)] {κ : Type} [Fintype κ] (ψk : AddChar k ℂ) (hc : Continuous ψk) (h1 : ψk ≠ 1)
    (N : Submodule ℂ ((κ → k) → ℂ)) (hN : N ≤ GlobalTheory.WeilM.SB (κ → k))
    (hS : ∀ w, ∀ φ ∈ N, schr ψk w φ ∈ N) (φ₀ : (κ → k) → ℂ) (h0 : φ₀ ∈ N) (hne : φ₀ ≠ 0) :
    N = GlobalTheory.WeilM.SB (κ → k) := by
  classical
  let e := colH k κ
  let L : (Matrix κ Unit k → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) := LinearMap.funLeft ℂ ℂ e
  have hL : ∀ Φ, L Φ = Φ ∘ e := fun _ => rfl
  have hcirc : Continuous (toCircle ψk hc) := by
    have : Continuous (fun x => ((toCircle ψk hc x : Circle) : ℂ)) := hc
    exact continuous_induced_rng.2 this
  have hne1 : toCircle ψk hc ≠ 1 := by
    intro h
    apply h1
    ext x
    have := congrArg (fun χ : AddChar k Circle => ((χ x : Circle) : ℂ)) h
    simpa [coe_toCircle] using this
  have hW : N.comap L ≤ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) := by
    intro Φ hΦ
    have h := sb_comp e.symm (hN hΦ)
    have : (Φ ∘ e) ∘ e.symm = Φ := by funext M; simp
    rw [← this]
    exact h
  have hT : ∀ Φ ∈ N.comap L, ∀ x : Matrix κ Unit k, (fun t => Φ (t + x)) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) →
      (fun t => Φ (t + x)) ∈ N.comap L := by
    intro Φ hΦ x _
    rw [Submodule.mem_comap, hL] at hΦ ⊢
    have h := hS (e.symm x, 0) _ hΦ
    convert h using 1
    funext y
    have he : e (y + e.symm x) = e y + x := by ext i j; cases j; rfl
    simp [schr, he]
  have hM : ∀ Φ ∈ N.comap L, ∀ b : Matrix κ Unit k,
      (fun t => ((toCircle ψk hc (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) * Φ t) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) →
      (fun t => ((toCircle ψk hc (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) * Φ t) ∈ N.comap L := by
    intro Φ hΦ b _
    rw [Submodule.mem_comap, hL] at hΦ ⊢
    have h := hS (0, fun r => b r ()) _ hΦ
    convert h using 1
    funext y
    simp [schr, dotProduct, coe_toCircle, e, colH, mul_comm]
    change Φ (e y) * ψk (∑ r, b r () * y r) = ψk (∑ r, b r () * y r) * Φ (e y)
    exact mul_comm _ _
  have h0' : φ₀ ∘ e.symm ∈ N.comap L := by
    rw [Submodule.mem_comap, hL]
    have : (φ₀ ∘ e.symm) ∘ e = φ₀ := by funext y; simp
    rw [this]; exact h0
  have hne' : φ₀ ∘ e.symm ≠ 0 := by
    intro h
    apply hne
    funext y
    have := congrFun h (e y)
    simpa using this
  have hall := GlobalTheory.IrredSB.sb_irreducible k κ Unit (toCircle ψk hc) hcirc hne1 (N.comap L) hW hT hM _ h0' hne'
  refine le_antisymm hN fun φ hφ => ?_
  have hm : φ ∘ e.symm ∈ N.comap L := by
    rw [hall]
    exact sb_comp e.symm hφ
  rw [Submodule.mem_comap, hL] at hm
  have : (φ ∘ e.symm) ∘ e = φ := by funext y; simp
  rwa [this] at hm

end GlobalTheory.SchrIrred

namespace GlobalTheory.SchrIrred

theorem schr_irreducible : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ N : Submodule ℂ ((κ → Fv F v) → ℂ), N ≤ GlobalTheory.WeilM.SB (κ → Fv F v) → (∀ w, ∀ φ ∈ N, schr ψk w φ ∈ N) → ∀ φ₀ ∈ N, φ₀ ≠ 0 →
      N = GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ v κ _ ψk hc h1 N hN hS φ₀ h0 hne
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  exact schr_irreducible_local (Fv F v) ψk hc h1 N hN hS φ₀ h0 hne

end GlobalTheory.SchrIrred
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictedProductCharStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_restricted_product_char : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    ∀ (κ : Type) [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (y : κ → AF F),
    (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
    (∀ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) ∈ SB (κ → Fv F v)) ∧
    (∀ᶠ v in cofinite, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) = GlobalTheory.SympChange.indO v) ∧
    ∀ x, pure f φ x * ψ (x ⬝ᵥ y) = (f (fun i => evI F (x i)) * eInf (fun i => evI F (x i)) (fun i => evI F (y i))) *
      ∏ᶠ v, (φ v (fun i => evFin F v (x i)) *
        GlobalTheory.LatVac.psiAt ψ v ((fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i))) := by
  first | exact @GlobalTheory.WeylTwist.pure_mul_psi | exact GlobalTheory.WeylTwist.pure_mul_psi | (intros; apply GlobalTheory.WeylTwist.pure_mul_psi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawCharacterConductorAtRamifiedPlace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.StdPairConeChars

theorem condLE_mono {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {e m : ℕ} (hem : e ≤ m)
    {χ : (Fv F v)ˣ →* ℂˣ} (h : GlobalTheory.SplitFlip.CondLE (unifAt v) e χ) : GlobalTheory.SplitFlip.CondLE (unifAt v) m χ := by
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have h1 : ValuativeRel.valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) ≤ 1 := hϖ.mem
  intro x hx
  refine h x ⟨hx.1, hx.2.trans ?_⟩
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' h1 hem

theorem nu_cond_at_ram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : B.P, v.1 ∈ X.T →
      GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) ∧ 1 ≤ (condExp (chrW X.ν (B.τ v))) ∧
      chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) ∧
      (∃ m, GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.α (B.τ v)) ∧ GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.β (B.τ v))) ∧
      (∀ x, ‖(chrW X.α (B.τ v) x : ℂ)‖ = 1) ∧ ∀ x, ‖(chrW X.β (B.τ v) x : ℂ)‖ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hvT
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v.1) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v.1)).choose_spec
  have hα := hT.chars.heckeα.1
  have hβ := hT.chars.heckeβ.1
  have hν : Continuous X.ν := (show Continuous fun x => X.α x / X.β x from hα.div' hβ)
  have hne : {c | GlobalTheory.SplitFlip.CondLE (unifAt v.1) c (chrW X.ν (B.τ v))}.Nonempty :=
    GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.ν hν (B.τ v))
  have hmem : GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) := Nat.sInf_mem hne
  obtain ⟨eα, heα⟩ := GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.α hα (B.τ v))
  obtain ⟨eβ, heβ⟩ := GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.β hβ (B.τ v))
  have hram : ¬ UnrAt X.ν (splitPrime (B.τ v)) :=
    hT.chars.ram _ (by rw [splitPrime_under]; exact hvT)
  obtain ⟨x₀, hx₀, hx₀', hνx₀⟩ := GlobalTheory.StepFacNe.chrW_ram X.ν (B.τ v) hram
  have hx₀v : ValuativeRel.valuation (Fv F v.1) (x₀ : Fv F v.1) = 1 := by
    have h1 := (GlobalTheory.GaussNonvanish.val_le_one_iff v.1 _).2 hx₀
    have h2 := (GlobalTheory.GaussNonvanish.val_le_one_iff v.1 _).2 hx₀'
    have h3 : ValuativeRel.valuation (Fv F v.1) (x₀ : Fv F v.1) *
        ValuativeRel.valuation (Fv F v.1) ((x₀⁻¹ : (Fv F v.1)ˣ) : Fv F v.1) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ValuativeRel.ValueGroupWithZero (Fv F v.1)) = _ := h3.symm
      _ ≤ _ := mul_le_of_le_one_right' h2
  have hc1 : 1 ≤ condExp (chrW X.ν (B.τ v)) := by
    by_contra h
    have h0 : condExp (chrW X.ν (B.τ v)) = 0 := by omega
    have hm := hmem
    rw [h0] at hm
    refine hνx₀ (hm x₀ ⟨hx₀v, ?_⟩)
    rw [pow_zero, Units.val_one, map_one]
    exact ((ValuativeRel.valuation (Fv F v.1)).map_sub _ _).trans (by simp [hx₀v])
  have hdiv : chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) := by
    ext x
    simp [chrW, locChar, Chars.ν]
  refine ⟨hmem, hc1, hdiv, ⟨max eα eβ, condLE_mono (le_max_left _ _) heα, condLE_mono (le_max_right _ _) heβ⟩,
    fun x => ?_, fun x => ?_⟩
  · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW X.α (B.τ v) x
  · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW X.β (B.τ v) x

end GlobalTheory.StdPairConeChars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProduct
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
namespace GlobalTheory.ModulusCoord

theorem map_haar_eq_smul_of_coords : ∀ (Q L A C : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [T2Space L] [MeasurableSpace L] [BorelSpace L]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C] [LocallyCompactSpace C]
    [SecondCountableTopology C] [T2Space C] [MeasurableSpace C] [BorelSpace C]
    (Φ : L × (A × C) ≃ₜ Q),
    (∀ q' : Q, ∃ (l' : L) (f : L → A) (g : L × A → C), Continuous f ∧ Continuous g ∧
      ∀ l a c, Φ (l, (a, c)) * q' = Φ (l * l', (a + f l, c + g (l, a)))) →
    ∀ (α : Q →* Q) (sA : A →+ A) (sC : C →+ C) (kA kC : ℝ≥0), Continuous α → Continuous sA → Continuous sC →
    (∀ l a c, α (Φ (l, (a, c))) = Φ (l, (sA a, sC c))) →
    (∀ ν : Measure A, ν.IsAddHaarMeasure → ν.map sA = kA • ν) →
    (∀ ν : Measure C, ν.IsAddHaarMeasure → ν.map sC = kC • ν) →
    ∀ μ : Measure Q, μ.IsHaarMeasure → μ.map α = (kA * kC) • μ := by
  intro Q L A C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Φ hT α sA sC kA kC hα hsA hsC hαΦ hA hC μ hμ
  set ρ : Measure L := (Measure.haar : Measure L).inv with hρ
  set νA : Measure A := Measure.addHaar with hνA
  set νC : Measure C := Measure.addHaar with hνC
  set P : Measure (L × (A × C)) := ρ.prod (νA.prod νC) with hP
  have hΦm : Measurable Φ := Φ.continuous.measurable
  set ν₀ : Measure Q := P.map Φ with hν₀
  have hright : ν₀.IsMulRightInvariant := by
    constructor
    intro q'
    obtain ⟨l', f, g, hf, hg, hfg⟩ := hT q'
    let T : L × (A × C) → L × (A × C) :=
      fun p => (p.1 * l', (p.2.1 + f p.1, p.2.2 + g (p.1, p.2.1)))
    have hTΦ : (· * q') ∘ Φ = Φ ∘ T := by funext p; exact hfg p.1 p.2.1 p.2.2
    have hTmp : MeasurePreserving T P P := by
      refine MeasurePreserving.skew_product (μa := ρ) (μb := ρ) (μc := νA.prod νC) (μd := νA.prod νC)
        (f := fun l : L => l * l')
        (g := fun l (x : A × C) => (x.1 + f l, x.2 + g (l, x.1))) ?_ ?_ ?_
      · exact measurePreserving_mul_right ρ l'
      · exact (by fun_prop : Continuous fun p : L × (A × C) =>
          (p.2.1 + f p.1, p.2.2 + g (p.1, p.2.1))).measurable
      · filter_upwards with l
        exact (MeasurePreserving.skew_product (μa := νA) (μc := νC) (g := fun (a : A) (c : C) => c + g (l, a))
          (measurePreserving_add_right νA (f l))
          (by exact (by fun_prop : Continuous fun p : A × C => p.2 + g (l, p.1)).measurable)
          (ae_of_all _ fun a => map_add_right_eq_self νC (g (l, a)))).map_eq
    rw [hν₀, Measure.map_map (measurable_mul_const q') hΦm, hTΦ,
      ← Measure.map_map hΦm hTmp.measurable, hTmp.map_eq]
  have hfin : IsFiniteMeasureOnCompacts ν₀ := Measure.IsFiniteMeasureOnCompacts.map P Φ
  have hpos : ν₀.IsOpenPosMeasure := Φ.continuous.isOpenPosMeasure_map Φ.surjective
  haveI : ν₀.inv.IsHaarMeasure := by constructor
  have hα_map : ν₀.map α = (kA * kC) • ν₀ := by
    have hcomp : α ∘ Φ = Φ ∘ Prod.map id (Prod.map sA sC) := by
      funext p; exact hαΦ p.1 p.2.1 p.2.2
    rw [hν₀, Measure.map_map hα.measurable hΦm, hcomp,
      ← Measure.map_map hΦm (measurable_id.prodMap (hsA.measurable.prodMap hsC.measurable)), hP,
      ← Measure.map_prod_map _ _ measurable_id (hsA.measurable.prodMap hsC.measurable),
      ← Measure.map_prod_map _ _ hsA.measurable hsC.measurable, hA νA inferInstance,
      hC νC inferInstance, Measure.map_id, Measure.prod_smul_right, Measure.prod_smul_left,
      smul_smul, Measure.prod_smul_right, Measure.map_smul _ hΦm.aemeasurable, mul_comm]
  have hinv : (ν₀.inv).map α = (kA * kC) • ν₀.inv := by
    have hc : α ∘ (fun q => q⁻¹) = (fun q => q⁻¹) ∘ α := by funext q; simp [map_inv]
    rw [Measure.inv, Measure.map_map hα.measurable measurable_inv, hc,
      ← Measure.map_map measurable_inv hα.measurable, hα_map,
      Measure.map_smul _ measurable_inv.aemeasurable]
  rw [Measure.isMulLeftInvariant_eq_smul μ ν₀.inv, Measure.map_smul _ hα.measurable.aemeasurable,
    hinv, smul_smul, mul_comm, ← smul_smul]

end GlobalTheory.ModulusCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewGramInrInl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat.VacFix

theorem isHalf_of_mulG {D : D7} (S : HSp D) {n : ℕ} (ε : AE D) (x : Matrix (Fin n) (Fin S.rank) (AE D))
    (h : ∀ a b, ε * mulG S x a b = mulG S x a b) (a : Fin n) (b : Fin S.rank) : ε * x a b = x a b := by
  have h1 : ε • mulG S x = mulG S x := Matrix.ext h
  have h2 : divG S (ε • mulG S x) = ε • divG S (mulG S x) := Matrix.smul_mul _ _ _
  rw [h1, divG_mulG] at h2
  exact (congrFun (congrFun h2 a) b).symm

theorem hTens_eq_zero {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (hc : ∀ a, c (c a) = a)
    {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A)
    (h₁ : ∀ a b, JB (e (.inl a)) (e (.inr b)) = 0) (h₂ : ∀ a b, JB (e (.inr a)) (e (.inl b)) = 0)
    (ε : A) (hε : ε * c ε = 0) (x : Matrix (Fin n) (Fin d) A)
    (hl : ∀ a b, ε * x a (e (.inl b)) = x a (e (.inl b)))
    (hr : ∀ a b, ε * c (x a (e (.inr b))) = c (x a (e (.inr b)))) : hTens c JA JB x x = 0 := by
  unfold hTens
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun k _ =>
    Finset.sum_eq_zero fun l _ => ?_
  obtain ⟨b | b, rfl⟩ := e.surjective b <;> obtain ⟨l | l, rfl⟩ := e.surjective l
  · have u := congrArg c (hl k l)
    rw [map_mul] at u
    rw [← u, ← hl a b]
    linear_combination (x a (e (.inl b)) * JA a k * JB (e (.inl b)) (e (.inl l)) * c (x k (e (.inl l)))) * hε
  · rw [h₁, mul_zero, zero_mul]
  · rw [h₂, mul_zero, zero_mul]
  · have u := congrArg c (hr a b)
    rw [map_mul, hc] at u
    rw [← u, ← hr k l]
    linear_combination (x a (e (.inr b)) * JA a k * JB (e (.inr b)) (e (.inr l)) * c (x k (e (.inr l)))) * hε

theorem skewGram_inl_inr {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (a b) :
    skewGram A B e (e (.inl a)) (e (.inr b)) = 0 := by
  simp [skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

theorem skewGram_inr_inl {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (a b) :
    skewGram A B e (e (.inr a)) (e (.inl b)) = 0 := by
  simp [skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

theorem hTens_mixHalf {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) (ε : AE D)
    (hε : ε * cA D ε = 0) (γ : Pt G i j) (hγ : γ ∈ mixHalf e ε) :
    hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ = 0 := by
  refine hTens_eq_zero (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) GlobalTheory.DualPairCheck.cA_cA e _ _
    (fun a b => ?_) (fun a b => ?_) ε hε γ (fun a b => ?_) (fun a b => ?_)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (skewGram_inl_inr _ _ e a b))).trans (map_zero _)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (skewGram_inr_inl _ _ e a b))).trans (map_zero _)
  · exact isHalf_of_mulG (negSp (spW G i j)) ε (colV e γ)ᵀ hγ.1 b a
  · refine isHalf_of_mulG (spV₁ G i j) ε ((γ.submatrix id fun k => e (.inr k)).map (cA D)) (fun a b => ?_) a b
    exact neg_injective ((mul_neg _ _).symm.trans (hγ.2 a b))

theorem psi_double {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ)
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s') (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (θ : 𝓞 E)
    (γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hγ : γ ∈ latAtV X Y v) :
    B.ψ (⅟(2 : AF F) * symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (2 • γ) (2 • γ)) = 1 := by
  have h2 : (2 : ℕ) • γ = (2 : AF F) • γ := by rw [two_smul, two_smul]
  rw [h2, GlobalTheory.LatVac.symp_smul_smul, ← mul_assoc, ← mul_assoc, invOf_mul_self, one_mul]
  refine GlobalTheory.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 2 ?_ γ hγ γ hγ
  rw [map_ofNat]
  exact ofNat_mem _ 2

theorem vac_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    ∀ v : Pl D.host.F, (∀ u ∈ latPt e v, u ∈ latAtV Γ.V Γ.W v) →
      ∀ γ ∈ genPt e v, Acts (evFin D.host.F v) (Γ.M.co.rho W.ψ γ) (Γ.M.vac v) (Γ.M.vac v) := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT v hL γ hγ
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM.vac v
  have h1 := hθ γ (hL γ (genPt_subset e v hγ))
  have h2 : Bs.ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) = 1 := by
    rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨-, ε, hε, hγ⟩
    · exact psi_double _ Bs Γ.V Γ.W _ _ _ _ hT.base hT.geo.hV hT.geo.hW v θ γ' (hL γ' hγ')
    · unfold symp
      rw [hTens_mixHalf e Γ h.JWW ε hε.2.1 γ hγ, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one]
  rw [h2, one_smul, h.ψ] at h1
  exact h1

end GlobalTheory.BigDat.VacFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterAndTranslationCoordsSurjectivStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (bb : GL (Fin n) (Fv F v)) (cc : GL (Fin d) (Fv F v)) (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW (t.comp σ)) = 0 ∧ GlobalTheory.FlipMatch.coX t bb cc z = Z) ∧
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW t) = 0 ∧ GlobalTheory.FlipMatch.coY σ X W t bb cc z = Z) := by
  exact @GlobalTheory.FlipOnto.coX_coY_onto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingEquivariantStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_local_gl_embedding_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ g : GL (Fin a') (Fv F v),
      ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F)
          (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) = (chrW X.ν t (GlobalTheory.SplitFlip.gdet g) : ℂ) ^ 2 ∨
      ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F)
          (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) = (((chrW X.ν t (GlobalTheory.SplitFlip.gdet g))⁻¹ : ℂˣ) : ℂ) ^ 2 := by
  first | exact @GlobalTheory.SiegelValGood.siegel_factor_eq_sq | exact GlobalTheory.SiegelValGood.siegel_factor_eq_sq | (intros; apply GlobalTheory.SiegelValGood.siegel_factor_eq_sq <;> assumption)
end

